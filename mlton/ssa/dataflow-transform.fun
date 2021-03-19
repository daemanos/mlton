(* Copyright (C) 2021 Daman Morris.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

functor DataflowTransform(P: DATAFLOW_PROBLEM): SSA_TRANSFORM =
struct

open P

(* Optimization fuel *)
val fuel: int ref = ref 0

(* Rolling back speculative rewrites *)
(* TODO real implementation *)
fun checkpoint () = ()
fun restart () = ()


(* wrap facts and fact bases in a single datatype so they can be used in
 * recursive functions below *)
datatype outfact = Cont of Fact.t
                 | Done of Fact.t FactBase.t

structure Node = struct
   datatype t = Lb of (Var.t * Type.t) vector * Label.t
              | St of Statement.t
              | Tr of Transfer.t

   fun continue (n, f) =
      case n of
         Lb al => Cont ((#1 transfer) al f)
       | St st => Cont ((#2 transfer) st f)
       | Tr tr => Done ((#3 transfer) tr f)

   fun entryLabels n =
      case n of
         Tr tr =>
            let open Transfer
            in case tr of
                  Bug => raise Fail "???" (* FIXME *)
                | Call {return, ...} => [] (* TODO propagate to other funcs? *)
                | Case {cases, ...} =>
                     Cases.fold (cases, [], fn (lb, lbs) => lb::lbs)
                | Goto {dst, ...} => [dst]
                | Runtime {return, ...} => [return]
                | _ => []
            end
       | _ => []

end

structure DBlock = struct
   datatype t = T of {entryFact: Fact.t,
                      args: (Var.t * Type.t) vector option,
                      label: Label.t option,
                      statements: Statement.t vector,
                      transfer: Transfer.t option}

   local
      fun make f (T r) = f r
   in
      val entryFact = make #entryFact
      val args = make #args
      val label = make #label
      val statements = make #statements
      val transfer = make #transfer
   end

   fun nodes (T {args, label, statements, transfer, ...}) =
      let
         val argsLabel =
            case (args, label) of
               (SOME args, SOME label) => [Node.Lb (args, label)]
             | _ => []
         val transfer =
            case transfer of
               NONE => []
             | SOME transfer => [Node.Tr transfer]
      in
         argsLabel @ (Vector.toListMap (statements, Node.St)) @ transfer
      end

   fun new (args, label, statements, transfer) entryFact =
      T {entryFact = entryFact,
         args = args,
         label = label,
         statements = statements,
         transfer = transfer}

   fun fromLabel (args, label) =
      new (SOME args, SOME label, Vector.new0 (), NONE)
   fun fromStatements statements = new (NONE, NONE, statements, NONE)
   fun fromTransfer transfer = new (NONE, NONE, Vector.new0 (), SOME transfer)

   fun fromNode n =
      case n of
         Node.Lb al => fromLabel al
       | Node.St st => fromStatements (Vector.new1 st)
       | Node.Tr tr => fromTransfer tr

   fun prefix ({args, label, statements}) =
      new (SOME args, SOME label, statements, NONE)
   fun suffix ({statements, transfer}) =
      new (NONE, NONE, statements, SOME transfer)

   datatype edge = Open | Closed

   fun shape (T {args, transfer, ...}) =
      case (args, transfer) of
         (NONE, NONE) => (Open, Open)
       | (SOME _, NONE) => (Closed, Open)
       | (NONE, SOME _) => (Open, Closed)
       | (SOME _, SOME _) => (Closed, Closed)

   fun merge c d =
      case (shape c, shape d) of
         ((_, Open), (Open, _)) =>
            let
               val T {args, label, ...} = c
               val T {transfer, ...} = d
               val statements = Vector.concat [statements c, statements d]
            in
               [new (args, label, statements, transfer) (entryFact c)]
            end
       | ((_, Closed), (Closed, _)) => [c, d]
       | _ => raise Fail "DBlock.merge"

   fun toBlock (T {args, label, statements, transfer, ...}) =
      case (args, label, statements, transfer) of
         (SOME args, SOME label, statements, SOME transfer) =>
            Block.T {args = args,
                     label = label,
                     statements = statements,
                     transfer = transfer}
       | _ => raise Fail "DBlock.toBlock"

   fun fromBlock (Block.T {args, label, statements, transfer}) =
      T {entryFact = Fact.bot,
         args = SOME args,
         label = SOME label,
         statements = statements,
         transfer = SOME transfer}
end

structure Graph = struct
   datatype t = Nil
              | Unit of DBlock.t
              | Many of DBlock.t option * DBlock.t list * DBlock.t option

   val empty = Nil

   fun singleton (n, f) = Unit (DBlock.fromNode n f)
   fun statements (sts, f) = Unit (DBlock.fromStatements sts f)

   fun closed blocks = Many (NONE, blocks, NONE)
   fun openL (left, blocks) = Many (SOME left, blocks, NONE)
   fun openR (blocks, right) = Many (NONE, blocks, SOME right)
   fun openLR (left, blocks, right) = Many (SOME left, blocks, SOME right)

   (* FIXME better error messages for failures *)
   (* failures can only happen if a Unit has been constructed incorrectly or
    * if splice is applied to incompatible arguments *)
   fun splice g1 g2 =
      case (g1, g2) of
         (_, Nil) => g1
       | (Nil, _) => g2
       | (Unit b1, Unit b2) =>
            (case DBlock.merge b1 b2 of
                [b] => Unit b
              | _ => raise Fail "Graph.splice")
       | (Unit b, Many (SOME left, body, right)) =>
            (case DBlock.merge b left of
                [left'] => Many (SOME left', body, right)
              | _ => raise Fail "Graph.splice")
       | (Many (left, body, SOME right), Unit b) =>
            (case DBlock.merge right b of
                [right'] => Many (left, body, SOME right')
              | _ => raise Fail "Graph.splice")
       | (Many (left, body1, SOME b1), Many (SOME b2, body2, right)) =>
            Many (left, body1 @ (DBlock.merge b1 b2) @ body2, right)
       | (Many (left, body1, NONE), Many (NONE, body2, right)) =>
            Many (left, body1 @ body2, right)
       | _ => raise Fail "Graph.splice"

end

fun rewriteNode (rwLb, rwSt, rwTr) n f =
let
   (* FIXME might need to rethink Fact.bot's below *)
   fun doitLb al =
      case rwLb al f of
         NONE => NONE
       | SOME {blocks, prefix} =>
            SOME (Graph.openR (List.map (blocks, DBlock.fromBlock),
                               DBlock.prefix prefix Fact.bot))

   fun doitSt st =
      case rwSt st f of
        NONE => NONE
      | SOME (Statements sts) => SOME (Graph.statements (sts, Fact.bot))
      | SOME (Graph {suffix, blocks, prefix}) =>
           SOME (Graph.openLR (DBlock.suffix suffix Fact.bot,
                               List.map (blocks, DBlock.fromBlock),
                               DBlock.prefix prefix Fact.bot))

   fun doitTr tr =
      case rwTr tr f of
         NONE => NONE
       | SOME {suffix, blocks} =>
            SOME (Graph.openL (DBlock.suffix suffix Fact.bot,
                               List.map (blocks, DBlock.fromBlock)))
in
   if !fuel > 0
   then
      (fuel := !fuel - 1;
       case n of
          Node.Lb al => doitLb al
        | Node.St st => doitSt st
        | Node.Tr tr => doitTr tr)
   else
      NONE
end

fun updLb rwLb (_,    rwSt, rwTr) = (rwLb, rwSt, rwTr)
fun updSt rwSt (rwLb, _,    rwTr) = (rwLb, rwSt, rwTr)
fun updTr rwTr (rwLb, rwSt, _   ) = (rwLb, rwSt, rwTr)

fun rewLoop r node f =
let
   fun add rw' (rn, rw) = (rn, Then (rw, rw'))
   fun doit r sm no =
      case r of
         Doit rfs => (
            case rewriteNode rfs node f of
               NONE => no
             | SOME replace => sm (replace, Noop))
       | Then (rw1, rw2) => doit rw1 (sm o add rw2) (doit rw2 sm no)
       | Iter rw => doit rw (sm o add (Iter rw)) no
       | Noop => no
in
   doit r SOME NONE
end

fun analyzeAndRewrite rewrite entries =
let
   fun node (n, f) =
   let val f =
      case f of
         Cont f => f
         (* can only happen if a Graph has been constructed incorrectly *)
       | _ => raise Fail "analyzeAndRewrite_node"
   in case rewLoop rewrite n f of
         SOME (g, rewrite') =>
            analyzeAndRewrite rewrite' (Node.entryLabels n) g (Cont f)
       | NONE => (Graph.singleton (n, f), Node.continue (n, f))
   end

   and block (b, f) =
   let
      val nodes = DBlock.nodes b
      fun cat (n, (g, f)) =
         let val (g', f') = node (n, f)
         in (Graph.splice g g', f')
         end
   in
      case f of
         Cont f => List.fold (nodes, (Graph.empty, Cont f), cat)
       | Done fb =>
            let val f =
               case DBlock.label b of
                  SOME label =>
                     (case FactBase.lookup fb label of
                         SOME f => f
                       | NONE => Fact.bot)
                | NONE => Fact.bot
            in List.fold (nodes, (Graph.empty, Cont f), cat)
            end
   end

   and body entries blockmap fbase0 = ()

   and graph g f =
      case g of
         Graph.Nil => (Graph.Nil, f)
       | Graph.Unit b => block (b, f)
       | Graph.Many (left, blocks, right) =>
            let
               val (g1, fb1) =
                  case left of
                     SOME b =>
                        (case block (b, f) of
                            (g, Done fb) => (g, Done fb)
                            (* can only happen if the left edge doesn't have a
                             * transfer *)
                          | _ => raise Fail "analyzeAndRewrite_graph")
                   | NONE => (Graph.Nil, Done FactBase.empty)

               val (g2, fb2) =
                  List.fold (blocks, (g1, fb1),
                             fn (b, (g, f)) =>
                                let val (g', f') = block (b, f)
                                in (Graph.splice g g', f')
                                end)

               val (g', f') =
                  case right of
                     SOME b =>
                        let val (g3, f') = block (b, fb2)
                        in (Graph.splice g2 g3, f')
                        end
                   | NONE => (g2, fb2)
            in
               (g', f')
            end
in
   graph
end


fun transform p = p

end
