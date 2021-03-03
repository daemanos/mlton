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
      val transfer : Fact.t transfer

      (* Rewrites *)
      val rewrite : Fact.t rewrite
   end
