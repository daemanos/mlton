(* Copyright (C) 2021 Daman Morris.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

signature DATAFLOW_PROBLEM_STRUCTS =
   sig
      include RESTORE
   end

signature DATAFLOW_PROBLEM =
   sig
      include DATAFLOW_PROBLEM_STRUCTS

      type f
      type change = unit option

      (* Fact definition *)
      structure FactBase : sig
         type 'a t

         val mkLabelMap : (Label.t * 'a) list -> 'a t

         val insert : 'a t -> (Label.t * 'a) -> 'a t
         val lookup : 'a t -> Label.t -> 'a option
      end

      datatype 'a Fact = Open of 'a
                       | Closed of 'a FactBase.t

      (* Lattice definition *)
      val bot : f
      val join : f -> f -> (change * f)

      (* Transfers *)
      val transfer : unit DirectedGraph.Node.t -> f -> f Fact

      (* Rewrites *)
      val rewrite : unit DirectedGraph.Node.t -> f -> (unit DirectedGraph.t) option
   end
