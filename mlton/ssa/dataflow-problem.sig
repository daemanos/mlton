(* Copyright (C) 2021 Daman Morris.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

signature DATAFLOW_PROBLEM =
   sig
      include DATAFLOW_TREE

      (* Fact lattice definition *)
      structure Fact: DATAFLOW_LATTICE

      (* Transfers *)
      val transfer : Node.t -> Fact.t -> Fact.t outflow

      (* Rewrites *)
      val rewrite : Node.t -> Fact.t -> Block.t list
   end
