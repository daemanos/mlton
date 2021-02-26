(* Copyright (C) 2021 Daman Morris.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

signature DATAFLOW_PROBLEM =
   sig
      include DATAFLOW_TREE

      type f

      (* Lattice definition *)
      (* TODO separate into own functor/signature pair *)
      val bot : f
      val join : f -> f -> f option

      (* Transfers *)
      val transfer : Node.t -> f -> f Fact.t

      (* Rewrites *)
      val rewrite : Node.t -> f -> Block.t list
   end
