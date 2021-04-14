(* Copyright (C) 2021 Daman Morris.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

functor DataflowTree(S: SSA_TRANSFORM_STRUCTS): DATAFLOW_TREE =
struct

open S

(* helper constructor for lattice types *)
(* TODO probably put somewhere more relevant *)
datatype 'f Poset = Top
                  | Elt of 'f
                  | Bot

structure VarMapLattice = MapLattice (
struct
   type ord_key = Var.t
   fun compare (u, v) =
      if (Var.hash u) < (Var.hash v)
      then LESS
      else GREATER
end)

structure FactBase =
struct
   type 'a t = (Label.t * 'a) list

   val empty = []
   fun singleton la = [la]
   fun fromList las = las
   fun uniform (ls, a) = List.map (ls, fn l => (l, a))

   fun fromCases (cases, default, fact, do_con) =
   let
      val default_la =
         case default of
            SOME label => [(label, fact)]
          | _ => []
   in
      case cases of
         Cases.Con conLabels =>
            Vector.foldr
            (conLabels,
             default_la,
             fn ((con, label), acc) =>
                case do_con (con, label) of
                   SOME fact' => (label, fact') :: acc
                 | _ => (label, fact) :: acc)
       | Cases.Word (sz, wordLabels) =>
            List.append
            (Vector.toListMap (wordLabels, fn (_, label) => (label, fact)),
             default_la)
   end

   fun insert las la = la::las

   fun lookup las l =
      case las of
         ((l',a)::rest) =>
            if Label.equals (l,l') then SOME a
            else lookup rest l
       | [] => NONE

   fun isMember las l = isSome (lookup las l)

   fun deleteList ls las =
      List.keepAll
      (las,
       fn (l', _) => List.exists (ls, fn l => Label.equals (l', l)))

   fun foldi f b0 las = List.fold (las, b0, fn ((l, a), b) => f (l, a) b)
   fun fold f b0 las = List.fold (las, b0, fn ((_, a), b) => f a b)
end

type prefix = {args: (Var.t * Type.t) vector,
               label: Label.t,
               statements: Statement.t vector}

type suffix = {statements: Statement.t vector,
               transfer: Transfer.t}

type 'f rwLb = (Var.t * Type.t) vector * Label.t -> 'f ->
               {blocks: Block.t list, prefix: prefix} option

fun norwLb _ _ = NONE

type 'f rwTr = Transfer.t -> 'f ->
               {suffix: suffix, blocks: Block.t list} option

fun replaceTr tr =
   SOME {suffix = {statements = Vector.new0 (),
                   transfer = tr},
         blocks = []}

fun norwTr _ _ = NONE

datatype ReplaceSt = Statements of Statement.t vector
                   | Graph of {suffix: suffix,
                               blocks: Block.t list,
                               prefix: prefix}

type 'f rwSt = Statement.t -> 'f -> ReplaceSt option

fun norwSt _ _ = NONE

type 'f rw = ('f rwLb * 'f rwSt * 'f rwTr)

(* helper function to package rewrite functions *)
fun mkRw rwLb rwSt rwTr = (rwLb, rwSt, rwTr)

datatype 'f rewrite = Doit of 'f rw
                    | Then of ('f rewrite * 'f rewrite)
                    | Iter of 'f rewrite
                    | Noop

fun mkRewrite r = Doit r
fun thenRewrite r1 r2 = Then (r1, r2)
fun iterRewrite r = Iter r
fun deepRewrite r = Iter (Doit r)

type 'f transferLb = (Var.t * Type.t) vector * Label.t -> 'f -> 'f
type 'f transferSt = Statement.t -> 'f -> 'f
type 'f transferTr = Transfer.t -> 'f -> 'f FactBase.t

type 'f transfer = ('f transferLb * 'f transferSt * 'f transferTr)

fun mkTransfer lb st tr = (lb, st, tr)

end
