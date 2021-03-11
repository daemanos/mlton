(* Copyright (C) 2021 Daman Morris.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

functor DataflowTransform(P: DATAFLOW_PROBLEM): SSA_TRANSFORM =
struct

open P

(* Optimization fuel *)
val fuel: int ref = ref 0

(* Rolling back speculative rewrites *)
(* TODO real implementation *)
fun checkpoint () = ()
fun restart () = ()

structure Node = struct
   datatype t = Lb of (Var.t * Type.t) vector * Label.t
              | St of Statement.t
              | Tr of Transfer.t
end

structure Replace = struct
   (* invariants:
    * - if an Lb produced this, it is either a Graph with a suffix of NONE
    *   or a None
    * - if an St produced this, it is a Graph with both a suffix and a prefix,
    *   or a Statements, or a None
    * - if a Tr produced this, it is either a Graph with a prefix of NONE or
    *   a None
    *)
   datatype t = Graph of {suffix: suffix option,
                          blocks: Block.t list,
                          prefix: prefix option}
              | Statements of Statement.t vector
              | None
end

fun rewriteNode (rwLb, rwSt, rwTr) n f =
let
   fun doitLb al =
      case rwLb al f of
         NONE => Replace.None
       | SOME {blocks, prefix} =>
            Replace.Graph {suffix = NONE, blocks = blocks, prefix = SOME prefix}

   fun doitSt st =
      case rwSt st f of
        NONE => Replace.None
      | SOME (Statements sts) => Replace.Statements sts
      | SOME (Graph {suffix, blocks, prefix}) =>
           Replace.Graph {suffix = SOME suffix,
                          blocks = blocks,
                          prefix = SOME prefix}

   fun doitTr tr =
      case rwTr tr f of
         NONE => Replace.None
       | SOME {suffix, blocks} =>
            Replace.Graph {suffix = SOME suffix, blocks = blocks, prefix = NONE}
in
   case n of
      Node.Lb al => doitLb al
    | Node.St st => doitSt st
    | Node.Tr tr => doitTr tr
end

fun updLb rwLb (_,    rwSt, rwTr) = (rwLb, rwSt, rwTr)
fun updSt rwSt (rwLb, _,    rwTr) = (rwLb, rwSt, rwTr)
fun updTr rwTr (rwLb, rwSt, _   ) = (rwLb, rwSt, rwTr)

fun transform p =
let
   fun rewLoop r node f =
   let
      fun add rw' (rn, rw) = (rn, Then (rw, rw'))
      fun doit r sm no =
         case r of
            Doit rfs => (
               case rewriteNode rfs node f of
                  Replace.None => no
                | replace => sm (replace, Noop))
          | Then (rw1, rw2) => doit rw1 (sm o add rw2) (doit rw2 sm no)
          | Iter rw => doit rw (sm o add (Iter rw)) no
          | Noop => no
   in
      doit r SOME NONE
   end

   fun node n f =
      case rewLoop rewrite n f of
         SOME (rn, rewrite') => () (* TODO *)
       | NONE => () (* TODO *)
in
   p
end

end
