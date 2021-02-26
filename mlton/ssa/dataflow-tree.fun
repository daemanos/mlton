(* Copyright (C) 2021 Daman Morris.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

functor DataflowTree(S: SSA_TRANSFORM_STRUCTS): DATAFLOW_TREE =
struct

open S

datatype Shape = Open | Closed

structure FactBase =
struct
   type 'a t = (Label.t * 'a) list

   fun mkFactBase las = las

   fun insert las la = la::las

   fun lookup las l =
      case las of
         ((l',a)::rest) =>
            if Label.equals (l,l') then SOME a
            else lookup rest l
       | [] => NONE
end

(* FIXME dummy implementation *)

structure Fact = struct
   datatype 'a t = O of 'a
                 | C of 'a FactBase.t
end

structure Node = struct
   datatype t = S of Statement.t
              | T of Transfer.t

   fun shape _ = Closed
end

end
