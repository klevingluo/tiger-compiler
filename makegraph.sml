signature MAKEGRAPH =
sig
    val instrs2graph: Assem.instr list -> Flow.flowgraph * Flow.Graph.node list
end

structure MakeGraph : MAKEGRAPH =
struct

  structure A = Assem

  fun instrs2graph(instrs) = 
    let
      val graph = ref (Graph.newGraph())
      val defs  = ref Graph.Table.empty
      val uses  = ref Graph.Table.empty
      val moves = ref Graph.Table.empty
      val labels : (Temp.label, Graph.node) HashTable.hash_table = 
        (HashTable.mkTable(fn t => HashString.hashString(Symbol.name (t)), 
                           op =)
        (42, Fail "not found"))

      fun addJump(A.OPER{assem, dst, src, jump}) = ()
        | addJump(A.LABEL{assem,lab}) = 
            (HashTable.insert(labels)(lab, Graph.newNode(!graph)))
        | addJump(A.MOVE{assem,dst,src}) = ()

      fun addNode(instr) = 
          case instr of
               A.OPER{assem, dst, src, jump} =>
                 let
                   val node = Graph.newNode(!graph)
                 in
                   (defs := Graph.Table.enter(!defs, node, dst);
                    uses := Graph.Table.enter(!uses, node, src);
                    moves := Graph.Table.enter(!moves, node, false);
                    (case jump of
                         SOME(jumps) => 
                            (map(fn jmp => 
                               Graph.mk_edge({from=node, 
                                              to=
                              (case HashTable.find(labels)(jmp) of
                                    SOME(node) => node
                                  | NONE => raise Fail 
                                       ("label "  ^ (Symbol.name jmp) ^ " not found"))}))
                               (jumps);
                             ())
                       | NONE =>());
                    node)
                 end
             | A.LABEL{assem, lab} => 
                 (case HashTable.find(labels)(lab) of
                      SOME(node) =>
                      (defs  := Graph.Table.enter(!defs, node, []);
                       uses  := Graph.Table.enter(!uses, node, []);
                       moves := Graph.Table.enter(!moves, node, false);
                       node)
                    | NONE => raise Fail "label not found")
             | A.MOVE{assem, dst, src} => 
                 let
                   val node = Graph.newNode(!graph)
                 in
                   (defs  := Graph.Table.enter(!defs, node, [dst]);
                    uses  := Graph.Table.enter(!uses, node, [src]);
                    moves := Graph.Table.enter(!moves, node, true);
                    node)
                 end

      fun linkNodes(first::second::rest) = 
             (Graph.mk_edge({from=first, to=second});
             linkNodes(second::rest))
        | linkNodes(first::rest) = ()
        | linkNodes([]) = ()

    in
      (map(addJump)(instrs);
       linkNodes(map(addNode)(instrs));
       (Flow.FGRAPH{control = !graph,
                    def     = !defs,
                    use     = !uses,
                    ismove  = !moves},
                    Graph.nodes(!graph)))
    end
end
