(* Copyright (C) 2021 Daman Morris.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

signature DATAFLOW_LATTICE =
   sig
      type t

      val bot: t
      val top: t

      val join : t -> t -> t option
   end
