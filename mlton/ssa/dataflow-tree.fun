(* Copyright (C) 2021 Daman Morris.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

functor DataflowTree(S: SSA_TRANSFORM_STRUCTS): DATAFLOW_TREE =
struct

open S

structure FactBase =
struct
   type 'a t = (Label.t * 'a) list

   val empty = []
   fun fromList las = las

   fun insert las la = la::las

   fun lookup las l =
      case las of
         ((l',a)::rest) =>
            if Label.equals (l,l') then SOME a
            else lookup rest l
       | [] => NONE
end

type prefix = {args: (Var.t * Type.t) vector,
               label: Label.t,
               statements: Statement.t vector}

type suffix = {statements: Statement.t vector,
               transfer: Transfer.t}

type 'f rwLb = (Var.t * Type.t) vector * Label.t -> 'f ->
               {blocks: Block.t list, prefix: prefix option}

fun norwLb _ _ = {blocks = [], prefix = NONE}

type 'f rwTr = Transfer.t -> 'f ->
               {suffix: suffix option, blocks: Block.t list}

fun norwTr _ _ = {suffix = NONE, blocks = []}

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
