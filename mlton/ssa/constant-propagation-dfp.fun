(* Copyright (C) 2021 Daman Morris.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

functor ConstantPropagationDFP(S: SSA_TRANSFORM_STRUCTS): DATAFLOW_PROBLEM =
struct

structure T = DataflowTree (S)
open T

structure Lattice = VarMapLattice

structure ConstValue =
struct
   datatype t = Const of Const.t
              | ConApp of {con: Con.t, args: t vector}
              | Tuple of t vector

   fun equals (c1, c2) =
      case (c1, c2) of
         (Const c1', Const c2') => Const.equals (c1', c2')
       | (ConApp {con = con1, args = args1},
          ConApp {con = con2, args = args2}) =>
          Con.equals (con1, con2) andalso Vector.forall2 (args1, args2, equals)
       | (Tuple cs1, Tuple cs2) =>
          (Vector.forall2 (cs1, cs2, equals) handle _ => false)
       | _ => false

   fun join (old, new) = if equals (old, new) then NONE else SOME Top

   fun typeOf const =
      case const of
         Const c => Type.ofConst c
       | ConApp {con, ...} => conType con
       | Tuple cs => Type.tuple (Vector.map (cs, typeOf))

   fun toStatements (const, var) =
      let
         fun introduceVars cs =
            List.unzip
            (Vector.toListMap (cs, fn c =>
             let
                val var = Var.newNoname ()
                val sts = toStatements (c, var)
             in
                (var, sts)
             end))

         val (stss, exp) =
            case const of
               Const c => ([], Exp.Const c)
             | ConApp {con, args} =>
                  let
                     val (vars, stss) = introduceVars args
                     val exp =
                        Exp.ConApp {con = con, args = Vector.fromList vars}
                  in
                     (stss, exp)
                  end
             | Tuple cs =>
                  let
                     val (vars, stss) = introduceVars cs
                     val exp = Exp.Tuple (Vector.fromList vars)
                  in
                     (stss, exp)
                  end
         val st = Statement.T {var = SOME var, ty = typeOf const, exp = exp}
      in
         List.snoc (List.concat stss, st)
      end

   fun layout const =
      let
         val layoutArgs = Vector.layout layout
         fun separateArgs (args, sep) =
            Layout.separate (Vector.toListMap (args, layout), sep)
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
          | Tuple cs => seq [str "(", seq (separateArgs (cs, ", ")), str ")"]
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

   fun findAll (f, vars) =
      Vector.keepAllMap
      (vars, fn var =>
       case Lattice.find (f, var) of
          SOME (Elt c) => SOME c
        | _ => NONE)

   val layout = Lattice.layout (layoutPoset ConstValue.layout)
end

local
   (* Analysis: variable equals a literal constant *)
   val varHasLit : Fact.t transfer =
   let
      fun lb _ f = f

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
                      | Exp.Tuple args =>
                           let
                              val args' = Fact.findAll (f, args)
                           in
                              if (Vector.size args') = (Vector.size args)
                              then Elt (ConstValue.Tuple args')
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
                   let
                      val f' =
                         Vector.fold
                         (labelArgs label, f, fn ((arg, _), f) =>
                          Fact.insert (f, arg, Top))
                   in
                     FactBase.insert (fbase, label, f')
                   end)
             | Runtime {return, ...} => FactBase.singleton (return, f)
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
            Statement.T {var = SOME var, exp = Exp.Var var', ...} =>
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
                           (ConstValue.toStatements (c, var))
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

      fun st s f =
         case s of
            Statement.T {var = SOME var, ty, exp = Exp.PrimApp {prim, args, ...}} =>
               let
                  val applyArgs =
                     Vector.toListMap
                     (args, fn arg =>
                      case Fact.lookup (f, arg) of
                         Elt (ConstValue.Const c) => Prim.ApplyArg.Const c
                       | Elt (ConstValue.ConApp {con, args}) =>
                            Prim.ApplyArg.Con
                            {con = con,
                             hasArg = Vector.isEmpty args}
                       | _ => Prim.ApplyArg.Var arg)
                  val exp' =
                     case Prim.apply (prim, applyArgs, Var.equals) of
                        Prim.ApplyResult.Const c => SOME (Exp.Const c)
                      | Prim.ApplyResult.Bool b =>
                           SOME (Exp.ConApp
                                 {con = Con.fromBool b,
                                  args = Vector.new0 ()})
                      | _ => NONE
               in
                  case exp' of
                     SOME exp' =>
                        replaceSt1
                        (Statement.T {var = SOME var, ty = ty, exp = exp'})
                   | NONE => NONE
               end
          | _ => NONE

      fun tr t f =
         case t of
            Transfer.Case {test, cases, default} =>
               (case Lattice.find (f, test) of
                   SOME (Elt (ConstValue.ConApp {con, args})) =>
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
                              let
                                 val (vars, stss) =
                                    Vector.foldr
                                    (args, ([], []), fn (arg, (vars, stss)) =>
                                     let
                                        val var = Var.newNoname ()
                                        val sts =
                                           ConstValue.toStatements (arg, var)
                                     in
                                        (var::vars, sts::stss)
                                     end)
                                 val sts = Vector.fromList (List.concat stss)
                                 val goto =
                                    Transfer.Goto
                                    {dst = dst,
                                     args = Vector.fromList vars}
                              in
                                 SOME
                                 {suffix = {statements = sts, transfer = goto},
                                  blocks = []}
                              end
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
