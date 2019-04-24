(* Copyright (C) 2009 Matthew Fluet.
 * Copyright (C) 1999-2007 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

functor InlineIncremental (S: INLINE_INC_STRUCTS): INLINE_INC =
struct

open S
open Exp Transfer

structure Key: ORDER =
struct
   type t = real
   open Real
end

structure Queue = Heap(structure Key = Key)

structure Node =
struct
   datatype Kind = Expanded
                 | Cutoff
                 | Opaque
                 | Deleted

   datatype t = T of {kind: Kind,
                      ir: Block.t vector ref,
                      callsite: Block.t ref,
                      children: t list ref,
                      plist: PropertyList.t}

   fun kind (T {kind, ...}) = kind
   fun ir (T {ir, ...}) = ir
   fun callsite (T {callsite, ...}) = callsite
   fun children (T {children, ...}) = children
   fun plist (T {plist, ...}) = plist

   fun callsize (T {ir, ...})
      = Block.sizeV (!ir, {sizeExp = Exp.size, sizeTransfer = Transfer.size})

   fun callsizeAux (children, doit)
      = foldr (op +) 0 (map doit children)

   fun callsizeC (T {children, ...}) = callsizeAux (!children, callsize)

   fun callsizeB (T {children, ...}) =
      let
         fun doit child
            = case kind child of
                   Cutoff => callsize child
                 | _      => 0
      in
         callsizeAux (!children, doit)
      end

   fun cutoffCount (T {children, ...}) =
      let
         fun doit child
            = case kind child of
                   Cutoff => 1
                 | _      => 0
      in
         foldr (op +) 0 (map doit (!children))
      end

   (* TODO needs to determine the number of arguments whose type is more
    * concrete than the formal params *)
   fun concreteArgs (T {callsite, ir, ...}): real = 0.0

   (* TODO needs to determine the number of simple optimizations as a result
    * of deep inlining trials, yet to be implemented *)
   fun simpleOptimizations (node): real = 0.0

   fun localBenefit (node: t, frequency: real)
      = case kind node of
             Cutoff   => frequency * (1.0 + concreteArgs node)
           | Expanded => frequency * (1.0 + simpleOptimizations node)
           | _        => Error.bug "InlineIncremental.localBenefit: wrong node kind"

   fun foreach (node: t as T {children, ...}, f: t -> unit) =
      let
         fun doit (child as T {children = children', ...}) =
            (List.foreach (!children', doit); f child)
      in
         List.foreach (!children, doit)
      end

   fun layout (T {kind, children, ...}) =
      let
         open Layout
      in
         seq [str "node",
              paren (case kind of
                          Expanded => str "E"
                        | Cutoff   => str "C"
                        | Opaque   => str "G"
                        | Deleted  => str "D"),
             str " ",
             List.layout layout (!children)]
      end
end

fun inlineIncremental (program as Program.T {datatypes,
                                             globals,
                                             functions,
                                             main},
                       params as {sumCoeff,
                                  sizeCoeff,
                                  cutoffThresh,
                                  cutoffCoeff,
                                  decisionCoeff,
                                  decisionDropoff,
                                  expandCutoffFactor1,
                                  expandCutoffFactor2}) =
   let
      (* keep track of a node's front, i.e., the queue of nodes to be
         explored next for potential inlining *)
      val {get = front: Node.t -> Node.t Queue.t, set = setFront, ...}
         = Property.getSet
           (Node.plist,
            Property.initRaise ("InlineIncremental.front", Node.layout))
      (* keep track of whether a node is done expanding *)
      val {get = expansionDone: Node.t -> bool, set = setExpansionDone, ...}
         = Property.getSetOnce (Node.plist, Property.initConst false)
      (* keep track of the call frequency of nodes with respect to the root *)
      val {get = callFreq: Node.t -> real, set = setCallFreq, ...}
         = Property.getSetOnce (Node.plist, Property.initConst 0.0)

      (* TODO actually implement *)
      fun priority (node: Node.t): Key.t = 0.0

      fun initFront node =
         let
            val nodes = Node.children node
            val pairs = map (fn node => (priority node, node)) (!nodes)
         in
            setFront (node, Queue.new pairs)
         end

      fun descend (node: Node.t, expandCutoff: Node.t -> unit) =
         case Node.kind node of
              Expanded =>
              let
                 val myFront = front node
                 val (best, myFront') = Queue.deleteMin myFront
                 val new = descend (best, expandCutoff)
                 val myFront'' =
                    case new of
                         SOME newNode => if Queue.size (front newNode) > 0
                                         then Queue.insert
                                              (myFront',
                                               priority newNode,
                                               newNode)
                                         else myFront'
                       | NONE => myFront'
              in
                 (setFront (node, myFront'');
                  SOME node)
              end
            | Cutoff => (expandCutoff node; NONE)
            | _ => NONE

      fun expand (root: Node.t): unit =
         let
            val _ = Node.foreach (root, initFront)
            fun thresh () =
               let
                  val s_ir = Real.fromInt (Node.callsizeC root)
                  val exp = (s_ir - expandCutoffFactor1) / expandCutoffFactor2
               in
                  Real.exp exp
               end
            fun expandCutoff (node: Node.t) =
               let
                  val benefit = Node.localBenefit (node, callFreq node)
                  val size = Node.callsize node
                  val myThresh = thresh ()
               in
                  if (benefit / (Real.fromInt size)) >= myThresh
                  then expand node
                  else ()
               end
            fun doit () =
               if expansionDone root
               then ()
               else let val _ = descend (root, expandCutoff)
                    in doit ()
                    end
         in
            doit ()
         end

      fun inlineFunction function = function
   in
      Program.T
      {datatypes = datatypes,
       globals = globals,
       functions = map inlineFunction functions,
       main = inlineFunction main}
   end

end
