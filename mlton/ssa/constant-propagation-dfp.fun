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

structure Lattice = VarMapLattice

structure ConstValue =
struct
   datatype t = Const of Const.t
                (* restricted to only enum-like (no args) for now *)
              | ConApp of {con: Con.t, args: t vector}

   fun equals (c1, c2) =
      case (c1, c2) of
         (Const c1', Const c2') => Const.equals (c1', c2')
       | (ConApp {con = con1, args = args1},
          ConApp {con = con2, args = args2}) =>
          Con.equals (con1, con2) andalso Vector.forall2 (args1, args2, equals)
       | _ => false

   fun join (old, new) =
      case (old, new) of
         (Elt oldConst, Elt newConst) =>
            if equals (oldConst, newConst)
            then NONE
            else SOME Top
       | _ => SOME Top

   fun fromExp exp =
      case exp of
         Exp.Const c => SOME (Const c)
       | Exp.ConApp {con, args} =>
            if Vector.isEmpty args
            then SOME (ConApp {con = con, args = Vector.new0 ()})
            else NONE
            (*let
               val args' =
                  Vector.keepAllMap
                  (args,
                   fn var =>
                      case Lattice.find (lat, var) of
                         SOME (Elt c) => SOME c
                       | _ => NONE)
            in
               if (Vector.size args') = (Vector.size args)
               then SOME (ConApp {con = con, args = args'})
               else NONE
            end*)
       | _ => NONE

   fun toExp const =
      case const of
         Const c => Exp.Const c
       | ConApp {con, ...} =>
            Exp.ConApp
            {con = con,
             args = Vector.new0 ()}
end

structure Fact = struct
   type fact = ConstValue.t Poset
   type t = fact Lattice.t

   val bot = Lattice.empty
   val join = Lattice.join ConstValue.join
end

(* For now mostly based on example in Hoopl paper *)
(* TODO maybe add additional MLton-specific details as necessary *)
local
   (* Analysis: variable equals a literal constant *)
   val varHasLit : Fact.t transfer =
   let
      fun lb _ f = f

      fun st s f =
         case Statement.var s of
            SOME var =>
               (case ConstValue.fromExp (Statement.exp s) of
                   SOME c => Lattice.insert (f, var, Elt c)
                 | _      => Lattice.insert (f, var, Top))
          | NONE => f

      fun tr t f =
         let open Transfer
         in
            case t of
               Goto {dst, ...} => FactBase.singleton (dst, f)
             | Case {test, cases, default} =>
                  FactBase.fromCases
                  (cases, default, f,
                   fn (con, _) =>
                      SOME
                      (Lattice.insert
                       (f, test,
                        Elt (ConstValue.ConApp
                             {con = con,
                              args = Vector.new0 ()}))))
             | _ => FactBase.empty
         end
   in
      mkTransfer lb st tr
   end

   val constProp : Fact.t rewrite =
   let
      val lb = norwLb

      fun st s f =
         case s of
            Statement.T {var = SOME var, ty, ...} =>
               (case Lattice.find (f, var) of
                   SOME (Elt c) =>
                     SOME
                     (Statements
                      (Vector.new1
                       (Statement.T
                        {var = SOME var,
                         ty = ty,
                         exp = ConstValue.toExp c})))
                 | _ => NONE)
          | _ => NONE

      val tr = norwTr
   in
      mkRewrite (lb, st, tr)
   end

   val simplify : Fact.t rewrite =
   let
      val lb = norwLb

      (* TODO more simplification *)
      val st = norwSt

      fun tr t f =
         case t of
            Transfer.Case {test, cases, default} =>
               (case Lattice.find (f, test) of
                   SOME (Elt (ConstValue.ConApp {con, ...})) =>
                     let
                        val Cases.Con cases = cases
                        val SOME (_, label) =
                           Vector.peek
                           (cases,
                            fn (con', _) => Con.equals (con, con'))
                     in
                        replaceTr
                        (Transfer.Goto
                         {dst = label,
                          args = Vector.new0 ()})
                     end
                 | _ => NONE)
          | _ => NONE
   in
      deepRewrite (lb, st, tr)
   end

in
   val transfer = varHasLit
   val rewrite = thenRewrite constProp simplify
end

end
