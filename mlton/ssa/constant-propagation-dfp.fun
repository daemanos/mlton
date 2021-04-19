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

   fun join (old, new) =
      case (old, new) of
         (Bot, _) => SOME new
       | (_, Bot) => SOME old
       | (Elt oldConst, Elt newConst) =>
            if equals (oldConst, newConst)
            then NONE
            else SOME Top
       | _ => SOME Top

   fun toExp (const, f) =
      case const of
         Const c => Exp.Const c
       | ConApp _ =>
            let
               val candidates =
                  Lattice.filter
                  (fn elt =>
                   case elt of
                      Elt const' => equals (const', const)
                    | _ => false) f
            in
               case Lattice.firsti candidates of
                  SOME (var, _) => Exp.Var var
                | _ => raise Fail "ConstValue.toExp"
            end

   fun toStatement (const, f, var, ty) =
      Statement.T {var = SOME var, ty = ty, exp = toExp (const, f)}

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
   val join = Lattice.join ConstValue.join

   fun findAll (f, vars) =
      Vector.keepAllMap
      (vars, fn var =>
       case Lattice.find (f, var) of
          SOME (Elt c) => SOME c
        | _ => NONE)

   fun layout f = Lattice.layout' (f, layoutPoset ConstValue.layout)
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
                  Lattice.insert (f, var, constOrTop)
               end
          | NONE => f

      fun tr t f =
         let open Transfer
         in
            case t of
               Goto {dst, ...} => FactBase.singleton (dst, f)
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
                            (Lattice.insert
                             (f, test,
                              Elt (ConstValue.ConApp
                                   {con = con,
                                    args = args'})))
                         else
                            NONE
                      end)
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
                     replaceSt1 (ConstValue.toStatement (c, f, var, ty))
                 | _ => NONE)
          | _ => NONE

      val tr = norwTr
   in
      mkRewrite (lb, st, tr)
   end

   val simplify : Fact.t rewrite =
   let
      fun lb (args, label) f =
         let
            val (args, statements) =
               Vector.mapAndFold
               (args, [], fn ((var, ty), sts) =>
                case Lattice.find (f, var) of
                   SOME (Elt c) =>
                   let
                      val arg' = (Var.new var, ty)
                      val st = ConstValue.toStatement (c, f, var, ty)
                   in
                      (arg', st::sts)
                   end
                 | _ => ((var, ty), sts))
            val prefix =
               {args = args,
                label = label,
                statements = Vector.fromListRev statements}
         in
            SOME {blocks = [], prefix = prefix}
         end

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
