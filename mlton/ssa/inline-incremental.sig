(* Copyright (C) 2009 Matthew Fluet.
 * Copyright (C) 1999-2007 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

signature INLINE_INC_STRUCTS =
   sig
      include SHRINK
   end

signature INLINE_INC =
   sig
      include INLINE_INC_STRUCTS

      (* Parameters:
       * - sumCoeff (p_1 in paper) = sensitivity to call tree size
       * - sizeCoeff (p_2 in paper) = sensitivity to code size
       * - cutoffThresh (b_2 in paper) = threshold # of cutoff nodes to consider
       * - cutoffCoeff (b_1 in paper) = sensitivity to # of cutoff nodes
       * - decisionCoeff (t_1 in paper) = multiplicative coefficient of the
       *   decision threshold
       * - decisionDropoff (t_2 in paper) = exponential coefficient of the
       *   decision threshold
       * *)
      val inlineIncremental:
         Program.t * {sumCoeff: real,
                      sizeCoeff: real,
                      cutoffThresh: real,
                      cutoffCoeff: real,
                      decisionCoeff: real,
                      decisionDropoff: real,
                      expandCutoffFactor1: real,
                      expandCutoffFactor2: real} -> Program.t
   end
