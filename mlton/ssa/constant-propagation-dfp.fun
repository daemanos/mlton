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

type f = unit

val bot = ()
fun join _ _ = NONE

fun transfer _ _ = Fact.O ()

fun rewrite _ _ = []

end
