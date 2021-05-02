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
              | ConApp of {con: Con.t, args: t vector}

   fun equals (c1, c2) =
      case (c1, c2) of
         (Const c1', Const c2') => Const.equals (c1', c2')
       | (ConApp {con = con1, args = args1},
          ConApp {con = con2, args = args2}) =>
          Con.equals (con1, con2) andalso Vector.forall2 (args1, args2, equals)
       | _ => false

   fun join (old, new) = if equals (old, new) then NONE else SOME Top

   fun toStatements (const, var, ty) =
      case const of
         Const c => [Statement.T {var = SOME var, ty = ty, exp = Exp.Const c}]
       | ConApp {con, args} =>
            let
               fun introduceVar const =
                  case const of
                     Const c =>
                        let
                           val var = Var.newNoname ()
                           val ty = Type.ofConst c
                        in
                           (var, toStatements (const, var, ty))
                        end
                   | ConApp {con, args} =>
                        let
                           val (vars, stss) =
                              List.unzip (Vector.toListMap (args, introduceVar))
                           val var = Var.newNoname ()
                           val ty = conType con
                           val exp =
                              Exp.ConApp
                              {con = con,
                               args = Vector.fromList vars}
                           val st =
                              Statement.T
                              {var = SOME var,
                               ty = ty,
                               exp = exp}
                        in
                           (var, List.snoc (List.concat stss, st))
                        end

               val (vars, stss) =
                  List.unzip (Vector.toListMap (args, introduceVar))
               val exp = Exp.ConApp {con = con, args = Vector.fromList vars}
               val st = Statement.T {var = SOME var, ty = ty, exp = exp}
            in
               List.snoc (List.concat stss, st)
            end

   fun layout const =
      let
         val layoutArgs = Vector.layout layout
         open Layout
      in
         case const of
            Const c => Const.layout c
          | ConApp {con, args} =>
               seq [str "con ",
                    Con.layout con,
                    if Vector.isEmpty args
                    then empty
                    else seq [str " ", layoutArgs args]]
      end
end

structure Fact = struct
   type fact = ConstValue.t Poset
   type t = fact Lattice.t

   val bot = Lattice.empty
   val join = Lattice.join (joinPoset ConstValue.join)

   fun lookup (f, var) = Lattice.lookup (f, var) handle _ => Bot
   fun insert (f, var, const) =
      let
         val _ =
            Control.diagnostic
            (fn () =>
             let open Layout
             in
                seq [str "Adding ", Var.layout var, str " |-> ",
                     layoutPoset ConstValue.layout const]
             end)
      in
         Lattice.insert (f, var, const)
      end

      (*fun joinOrInsert (f, var, const) =
         case joinPoset ConstValue.join (lookup (f, var), const) of
            NONE => f
          | SOME const' => insert (f, var, const')*)

   fun findAll (f, vars) =
      Vector.keepAllMap
      (vars, fn var =>
       case Lattice.find (f, var) of
          SOME (Elt c) => SOME c
        | _ => NONE)

   val layout = Lattice.layout (layoutPoset ConstValue.layout)
end

(* For now mostly based on example in Hoopl paper *)
(* TODO maybe add additional MLton-specific details as necessary *)
local
   (* Analysis: variable equals a literal constant *)
   val varHasLit : Fact.t transfer =
   let
      fun lb (args, _) f =
         Vector.fold
         (args, f, fn ((arg, _), f) =>
          getOpt (Fact.join (f, Lattice.singleton (arg, Bot)), f))

      fun st s f =
         case Statement.var s of
            SOME var =>
               let
                  val constOrTop =
                     case Statement.exp s of
                        Exp.Const c => Elt (ConstValue.Const c)
                      | Exp.ConApp {con, args} =>
                           let
                              val args' = Fact.findAll (f, args)
                           in
                              if (Vector.size args') = (Vector.size args)
                              then Elt (ConstValue.ConApp
                                        {con = con, args = args'})
                              else Top
                           end
                      | _ => Top
               in
                  Fact.insert (f, var, constOrTop)
               end
          | NONE => f

      fun tr t f =
         let open Transfer
         in
            case t of
               Goto {dst, args} =>
                  let
                     val argVals =
                        Vector.map
                        (args, fn arg => Fact.lookup (f, arg))
                     val targetArgs = labelArgs dst
                     val f =
                        Vector.fold2
                        (targetArgs, argVals, f, fn ((arg, _), argVal, f) =>
                         Fact.insert (f, arg, argVal))
                  in
                     FactBase.singleton (dst, f)
                  end
             | Case {test, cases, default} =>
                  FactBase.fromCases
                  (cases, default, f,
                   fn (con, label) =>
                      let
                         val (args, _) = Vector.unzip (labelArgs label)
                         val args' = Fact.findAll (f, args)
                      in
                         if (Vector.size args) = (Vector.size args')
                         then
                            SOME
                            (Fact.insert
                             (f, test,
                              Elt (ConstValue.ConApp
                                   {con = con,
                                    args = args'})))
                         else
                            NONE
                      end)
             | Call {return, ...} =>
                  (* Note: this is a conservative approximation since there is
                   * no way to know whether this is an intraprocedural call
                   * or not; would need a way to expose the current Func.t to
                   * the dataflow problem *)
                  Return.foldLabel
                  (return, FactBase.empty, fn (label, fbase) =>
                   FactBase.insert fbase
                   (label,
                    Vector.fold (labelArgs label, f, fn ((arg, _), f) =>
                                 Fact.insert (f, arg, Top))))
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
            Statement.T {var = SOME var, ty, exp = Exp.Var var'} =>
               (case Lattice.find (f, var') of
                   SOME (Elt c) =>
                     let
                        val _ =
                           Control.diagnostic
                           (fn () =>
                            let open Layout
                            in
                               seq [str "Found ", Var.layout var', str " |-> ",
                                    ConstValue.layout c]
                            end)
                        val sts =
                           Vector.fromList
                           (ConstValue.toStatements (c, var, ty))
                     in SOME (Statements sts)
                     end
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
                        val cases =
                           case cases of
                              Cases.Con cases => cases
                            | _ => raise Fail "constantPropagationDFP_simplify"

                        val dst =
                           case Vector.peek
                                (cases, fn (con', _) =>
                                 Con.equals (con, con')) of
                              SOME (_, label) => SOME label
                            | _ => default
                     in
                        case dst of
                           SOME dst =>
                              replaceTr
                              (Transfer.Goto
                               {dst = dst,
                                args = Vector.new0 ()})
                         | _ => NONE
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
