(* Copyright (C) 2021 Daman Morris.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

signature DATAFLOW_TREE_STRUCTS =
   sig
      include RESTORE
   end

signature DATAFLOW_TREE =
   sig
      include DATAFLOW_TREE_STRUCTS

      datatype Shape = Open | Closed

      (* Fact definition *)
      structure FactBase : sig
         type 'a t

         val mkFactBase : (Label.t * 'a) list -> 'a t

         val insert : 'a t -> (Label.t * 'a) -> 'a t
         val lookup : 'a t -> Label.t -> 'a option
      end

      structure Fact : sig
         datatype 'a t = O of 'a
                       | C of 'a FactBase.t
      end

      structure Node : sig
         datatype t = S of Statement.t
                    | T of Transfer.t

         val shape : t -> Shape
      end

   end
