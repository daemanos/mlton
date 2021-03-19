(* Copyright (C) 2017,2019-2020 Matthew Fluet.
 * Copyright (C) 1999-2008 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

(* NOTE: copying copyright holders since I plan to base this on the original
 * implementation *)

functor ConstantPropagationDFP(S: SSA_TRANSFORM_STRUCTS): DATAFLOW_PROBLEM =
struct

structure T = DataflowTree (S)
open T

(* FIXME dummy implementation *)

structure Fact = struct
   datatype t = Top
              | Bot
              | Val of unit

   val top = Top
   val bot = Bot

   fun join _ = NONE
end

open Fact

val transfer =
let
   fun lb _ _ = Top
   fun st _ _ = Top
   fun tr _ _ = FactBase.empty
in
   mkTransfer lb st tr
end

val rewrite = Noop

end
