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

(* wrap facts and fact bases in a single datatype so they can be used in
 * recursive functions below *)
structure AccumFact =
struct
   datatype t = Cont of Fact.t
              | Done of Fact.t FactBase.t

   fun valOf af =
      case af of
         Cont f => f
       | _ => raise Fail "AccumFact.valOf"
end

structure LabelSet = UnorderedSet (Label)

(* not sure why this is not available in scope from ssa-tree *)
local
   open Layout
in
   fun layoutFormals (xts: (Var.t * Type.t) vector) =
      Vector.layout (fn (x, t) =>
                     if !Control.showTypes
                        then mayAlign [seq [Var.layout x, str ":"],
                                       indent (Type.layout t, 2)]
                        else Var.layout x)
      xts
end

structure Node = struct
   datatype t = Lb of (Var.t * Type.t) vector * Label.t
              | St of Statement.t
              | Tr of Transfer.t

   fun continue (n, f) =
      case n of
         Lb al => AccumFact.Cont ((#1 transfer) al f)
       | St st => AccumFact.Cont ((#2 transfer) st f)
       | Tr tr => AccumFact.Done ((#3 transfer) tr f)

   fun entryLabels n =
      case n of
         Tr tr =>
            let
               val labels = ref []
               fun doit label = labels := (label :: !labels)
            in
               (Transfer.foreachLabel (tr, doit);
                !labels)
            end
       | _ => []

   fun layout n =
      let
         open Layout
         val (tag, obj) =
            case n of
               Lb (args, label) =>
                  (str "Lb",
                   seq [Label.layout label, str " ", layoutFormals args])
             | St statement => (str "St", Statement.layout statement)
             | Tr transfer => (str "Tr", Transfer.layout transfer)
      in
         compact (seq [tag, str "[", obj, str "]"])
      end
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
      val label = make #label
      val statements = make #statements
   end

   fun layout (T {entryFact, args, label, statements, transfer}) =
      let
         open Layout
         val labelArgsLayout =
            case (label, args) of
               (SOME label, SOME args) =>
                  seq [Label.layout label, str " ", layoutFormals args]
             | _ => empty
         val statementsLayout =
            align (Vector.toListMap (statements, Statement.layout))
         val transferLayout =
            case transfer of
               SOME transfer => Transfer.layout transfer
             | _ => empty
      in
         align [seq [str "dblock(", Fact.layout entryFact, str ") ",
                     labelArgsLayout],
                indent (align [statementsLayout, transferLayout], 2)]
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

   fun successors (T {transfer, ...}) =
      case transfer of
         SOME tr => Node.entryLabels (Node.Tr tr)
       | NONE => []

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

   fun fromBlock entryFact (Block.T {args, label, statements, transfer}) =
      T {entryFact = entryFact,
         args = SOME args,
         label = SOME label,
         statements = statements,
         transfer = SOME transfer}

   val fromBlockBot = fromBlock Fact.bot
end

structure Graph = struct
   datatype t = Nil
              | Unit of DBlock.t
              | Many of DBlock.t option * DBlock.t list * DBlock.t option

   val empty = Nil
   val emptyC = Many (NONE, [], NONE)

   fun singleton (n, f) = Unit (DBlock.fromNode n f)
   fun statements (sts, f) = Unit (DBlock.fromStatements sts f)

   fun closed blocks = Many (NONE, blocks, NONE)
   fun openL (left, blocks) = Many (SOME left, blocks, NONE)
   fun openR (blocks, right) = Many (NONE, blocks, SOME right)
   fun openLR (left, blocks, right) = Many (SOME left, blocks, SOME right)

   fun layout graph =
      let
         open Layout
      in
         case graph of
            Nil => str "graphNil"
          | Unit dblock => seq [str "graphUnit ", DBlock.layout dblock]
          | Many (left, blocks, right) =>
               let
                  val tag =
                     case (left, right) of
                        (NONE, NONE) => str "graphMany_CC"
                      | (SOME _, NONE) => str "graphMany_OC"
                      | (NONE, SOME _) => str "graphMany_CO"
                      | (SOME _, SOME _) => str "graphMany_OO"
                  val leftLayout =
                     case left of
                        SOME dblock => DBlock.layout dblock
                      | _ => empty
                  val rightLayout =
                     case right of
                        SOME dblock => DBlock.layout dblock
                      | _ => empty
                  val blocksLayout = List.map (blocks, DBlock.layout)
               in
                  align [tag,
                         indent (align [leftLayout,
                                        align blocksLayout,
                                        rightLayout],
                                 2)]
               end
      end

   val toString = Layout.toString o layout

   (*fun entryLabel g =
      case g of
         Many (NONE, b :: _, _) => DBlock.label b
       | _ => NONE

   fun successors g =
      case g of
         Many (_, body, NONE) =>
            (case List.rev body of
                b :: _ => DBlock.successors b
              | _ => [])
       | _ => []*)

   (* failures can only happen if a Unit has been constructed incorrectly or
    * if splice is applied to incompatible arguments *)
   fun splice g1 g2 =
      let
         fun fail msg =
         let
            val layout1 = layout g1
            val layout2 = layout g2
            open Layout
         in
            raise Fail (toString (align [str msg, layout1, layout2]))
         end
      in
         case (g1, g2) of
            (_, Nil) => g1
          | (Nil, _) => g2
          | (Unit b1, Unit b2) =>
               (case DBlock.merge b1 b2 of
                   [b] => Unit b
                 | _ => fail "Unit/unit splice: result not unary")
          | (Unit b, Many (SOME left, body, right)) =>
               (case DBlock.merge b left of
                   [left'] => Many (SOME left', body, right)
                 | _ => fail "Unit/many splice: left edge not unary")
          | (Many (left, body, SOME right), Unit b) =>
               (case DBlock.merge right b of
                   [right'] => Many (left, body, SOME right')
                 | _ => fail "Many/unit splice: right edge not unary")
          | (Many (left, body1, SOME b1), Many (SOME b2, body2, right)) =>
               Many (left, body1 @ (DBlock.merge b1 b2) @ body2, right)
          | (Many (left, body1, NONE), Many (NONE, body2, right)) =>
               Many (left, body1 @ body2, right)
          | _ => fail "Invalid splice shape"
      end
end

fun rewriteNode (rwLb, rwSt, rwTr) n f =
let
   (* FIXME might need to rethink Fact.bot's below *)
   fun doitLb al =
      case rwLb al f of
         NONE => NONE
       | SOME {blocks, prefix} =>
            let
               val {label, args, ...} = prefix
               val () = setLabelArgs (label, args)

               val blocks = List.map (blocks, DBlock.fromBlockBot)
               val prefix = DBlock.prefix prefix Fact.bot
            in
               SOME (Graph.openR (blocks, prefix))
            end

   fun doitSt st =
      case rwSt st f of
        NONE => NONE
      | SOME (Statements sts) => SOME (Graph.statements (sts, Fact.bot))
      | SOME (Graph {suffix, blocks, prefix}) =>
           let
              val {label, args, ...} = prefix
              val () = setLabelArgs (label, args)

              val suffix = DBlock.suffix suffix Fact.bot
              val blocks = List.map (blocks, DBlock.fromBlockBot)
              val prefix = DBlock.prefix prefix Fact.bot
           in
              SOME (Graph.openLR (suffix, blocks, prefix))
           end

   fun doitTr tr =
      case rwTr tr f of
         NONE => NONE
       | SOME {suffix, blocks} =>
            let
               val suffix = DBlock.suffix suffix Fact.bot
               val blocks = List.map (blocks, DBlock.fromBlockBot)
            in
               SOME (Graph.openL (suffix, blocks))
            end
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

fun transform (program: Program.t): Program.t =
   let
      val Program.T {datatypes, globals, functions, main} =
         eliminateDeadBlocks program

      val (_, transferSt, _) = transfer

      (* Accumulate facts from globals *)
      val fact0 =
         Vector.fold
         (globals, Fact.bot, fn (global, fact) => transferSt global fact)

      (* Accumulate maps from labels to their arguments, associated blocks,
       * and predecessor labels *)
      val {get = labelPreds: Label.t -> Label.t list,
           set = setLabelPreds, ...} =
         Property.getSet
         (Label.plist, Property.initConst [])
      val _ =
         List.foreach
         (functions, fn f =>
          let
             val {blocks, start, args, ...} = Function.dest f
             val _ = setLabelArgs (start, args)
          in
             Vector.foreach
             (blocks, fn Block.T {label, args, transfer, ...} =>
              (setLabelArgs (label, args);
               Transfer.foreachLabel
               (transfer, fn label' =>
                setLabelPreds (label, label' :: (labelPreds label)))))
          end)

      (* Main analysis + rewriting *)
      fun analyzeAndRewrite rewrite entries =
      let
         fun node (n: Node.t, af: AccumFact.t) : (Graph.t * AccumFact.t) =
         let val f = AccumFact.valOf af
         in
            case rewLoop rewrite n f of
               SOME (g, rewrite') =>
                  analyzeAndRewrite rewrite' (Node.entryLabels n) g (AccumFact.Cont f)
             | NONE => (Graph.singleton (n, f), Node.continue (n, f))
         end
         and block (b: DBlock.t, f: AccumFact.t): (Graph.t * AccumFact.t) =
            List.fold
            (DBlock.nodes b,
             (Graph.empty,
              AccumFact.Cont
              (case f of
                  AccumFact.Cont f => f
                | AccumFact.Done fb =>
                     (case DBlock.label b of
                         SOME label =>
                            (case FactBase.lookup fb label of
                                SOME f => f
                              | NONE => Fact.bot)
                       | NONE => Fact.bot))),
             fn (n, (g, f)) =>
                let val (g', f') = node (n, f)
                in (Graph.splice g g', f')
                end)
         and body (entries: Label.t list) blocks (fbase0: Fact.t FactBase.t)
            : Graph.t * AccumFact.t =
         let
            datatype ChangeFlag = Change | NoChange

            fun updateFact labels (label, fact') (cha, fbase) =
            let
               val fact = getOpt (FactBase.lookup fbase label, Fact.bot)
            in
               case Fact.join (fact, fact') of
                  NONE => (cha, fbase)
                | SOME fact'' =>
                     (if LabelSet.contains (labels, label)
                      then Change
                      else cha,
                      FactBase.insert fbase (label, fact''))
            end

            datatype TxFactBase
               = TxFB of {tfb_fbase: Fact.t FactBase.t,
                          tfb_rg: Graph.t,
                          tfb_cha: ChangeFlag,
                          tfb_labels: LabelSet.t}

            (* TODO put elsewhere *)
            datatype Direction = Fwd | Bwd

            fun fixpoint direction do_block blocks fbase0 =
            let
               val is_fwd =
                  case direction of
                     Fwd => true
                   | Bwd => false

               val tagged_blocks =
                  List.map
                  (blocks,
                   fn b =>
                      (* label is required to be present here *)
                      ((valOf (DBlock.label b), b),
                       if is_fwd
                       then [valOf (DBlock.label b)]
                       else DBlock.successors b))

               fun tx_block label block in_labels
                   (TxFB {tfb_fbase = fbase,
                          tfb_labels = labels,
                          tfb_rg = blocks,
                          tfb_cha = cha}) =
               let
                  val labels' = LabelSet.union (labels, LabelSet.fromList in_labels)
               in
                  if is_fwd andalso not (FactBase.isMember fbase label)
                  then
                     TxFB {tfb_fbase = fbase,
                           tfb_labels = labels',
                           tfb_rg = blocks,
                           tfb_cha = cha}
                  else
                     let
                        val (rg, out_facts) =
                           case do_block (block, fbase) of
                              (rg, AccumFact.Done out_facts) => (rg, out_facts)
                            | _ => raise Fail "analyzeAndRewrite_fixpoint [do_block]"

                        val (cha', fbase') =
                           FactBase.foldi
                           (updateFact labels)
                           (cha, fbase)
                           out_facts
                     in
                        TxFB {tfb_labels = labels',
                              tfb_rg = Graph.splice rg blocks,
                              tfb_fbase = fbase',
                              tfb_cha = cha'}
                     end
               end

               fun tx_blocks bs tx_fb =
                  case bs of
                     [] => tx_fb
                   | (((label, block), in_labels) :: bs) =>
                        tx_blocks bs (tx_block label block in_labels tx_fb)

               fun loop fbase =
                  let
                     val init_tx =
                        TxFB {tfb_fbase = fbase,
                              tfb_cha = NoChange,
                              tfb_rg = Graph.emptyC,
                              tfb_labels = LabelSet.empty}

                     val TxFB tx_fb = tx_blocks tagged_blocks init_tx
                  in
                     case #tfb_cha tx_fb of
                        NoChange => tx_fb
                      | Change => loop (#tfb_fbase tx_fb)
                  end

               val tx_fb = loop fbase0
            in
               (#tfb_rg tx_fb,
                AccumFact.Done
                (FactBase.deleteList
                 (List.map (tagged_blocks, #1 o #1))
                 (#tfb_fbase tx_fb)))
            end

            fun getFact (label, fb) =
               AccumFact.Cont
               (case FactBase.lookup fb label of
                   SOME fact => fact
                 | NONE => Fact.bot)

            fun blockLabelEquals label block =
               case DBlock.label block of
                    SOME label' => Label.equals (label, label')
                  | _ => false
         in
            (* TODO implement backward analysis *)
            fixpoint Fwd
            (fn (b, fb) => block (b, (getFact (valOf (DBlock.label b), fb))))
            (List.map
             (entries, fn label =>
              case List.peek (blocks, blockLabelEquals label) of
                 SOME block => block
               | NONE => raise Fail "fixpoint_blockNotFound"))
            fbase0
         end
         and graph (g: Graph.t) (f: AccumFact.t): Graph.t * AccumFact.t =
            case g of
               Graph.Nil => (Graph.Nil, f)
             | Graph.Unit b => block (b, f)
             | Graph.Many (left, blocks, right) =>
                  let
                     val (g', f') =
                        case left of
                           SOME b =>
                              (case block (b, f) of
                                  (g, AccumFact.Done fb) =>
                                    let
                                       val (g', f') =
                                          body (DBlock.successors b) blocks fb
                                    in
                                       (Graph.splice g g', f')
                                    end
                                  (* can only happen if the left edge doesn't have a
                                   * transfer *)
                                | _ => raise Fail "analyzeAndRewrite_graph")
                         | NONE =>
                              (case f of
                                  AccumFact.Done fb => body entries blocks fb
                                | _ => raise Fail "analyzeAndRewrite_graph")
                     val (g', f') =
                        case right of
                           SOME b =>
                              let val (g'', f'') = block (b, f')
                              in (Graph.splice g' g'', f'')
                              end
                         | NONE => (g', f')
                  in
                     (g', f')
                  end
      in
         graph
      end

      val functions =
         List.map
         (functions, fn f =>
          let
             (* TODO visit blocks in the right order (reverse postorder for
              * forward) *)
             val {args, blocks, mayInline, name, raises, returns, start} =
                Function.dest f
             val dblocks =
                Vector.toListMap
                (blocks, fn block => DBlock.fromBlock fact0 block)
             val body = Graph.closed dblocks
             val labels = Vector.toListMap (blocks, Block.label)
             val af0 = AccumFact.Done (FactBase.uniform (labels, fact0))
             val (body, _) = analyzeAndRewrite rewrite [start] body af0
             val dblocks =
                case body of
                   Graph.Many (NONE, dblocks, NONE) => dblocks
                 | _ => raise Fail "dataflowTransform_openOnExit"
             val blocks = Vector.fromListMap (dblocks, DBlock.toBlock)
          in
             Function.new
             {args = args,
              blocks = blocks,
              mayInline = mayInline,
              name = name,
              raises = raises,
              returns = returns,
              start = start}
          end)
      val program =
         Program.T
         {datatypes = datatypes,
          globals= globals,
          functions = functions,
          main = main}
   in
      program
   end

end
