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

structure Node = struct
   datatype t = L of Label.t
              | S of Statement.t
              | T of Transfer.t
end

structure ReplaceBlock = struct
   datatype t = T of {label: Label.t option,
                      statements: Statement.t vector,
                      transfer: Transfer.t option}

   val empty = T {label=NONE, statements=Vector.new0 (), transfer=NONE}
   val noop = [empty]
end

type 'f rw = Node.t -> 'f -> ReplaceBlock.t list

datatype 'f rewrite = Doit of 'f rw
                    | Then of ('f rewrite * 'f rewrite)
                    | Iter of 'f rewrite
                    | Noop

type 'f transferLb = Label.t -> 'f -> 'f
type 'f transferSt = Statement.t -> 'f -> 'f
type 'f transferTr = Transfer.t -> 'f -> 'f FactBase.t

type 'f transfer = ('f transferLb * 'f transferSt * 'f transferTr)

fun mkTransfer lb st tr = (lb, st, tr)

end
