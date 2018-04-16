(* TODO: may not need this sig if we choose not to handle spills *)
signature REG_ALLOC =
sig
    structure Frame : FRAME
    type allocation = Frame.register Temp.Table.table
    val alloc : Assem.instr list * Frame.frame ->
                Assem.instr list * allocation
end

signature COLOR =
sig
    structure Frame : FRAME
    type allocation = Frame.register Temp.Table.table
    val color : {interference : Liveness.igraph,
                 initial : allocation,
                 spillCost : Graph.node -> int,
                 registers : Frame.register list}
                -> allocation * Temp.temp list
end

structure Color : COLOR =
struct
    structure Frame = MipsFrame

    type allocation = Frame.register Temp.Table.table

    structure G = Graph
    structure T = Temp
    structure S = IntListSet

    (* DATA STRUCTURES *)

    (* Work-lists, Sets, and Stacks *)
    (* TODO: these should be mutually disjoint, may aid debugging if we enforce
       that somehow *)
    val simplifyWorklist = ref S.empty
    val freezeWorklist = ref S.empty
    val spillWorklist = ref S.empty
    val spilledNodes = ref S.empty
    val coalescedNodes = ref S.empty
    val coloredNodes = ref S.empty
    val selectStack = ref S.empty

    (* Move sets *)
    (* TODO: according to the text these should be doubly linked lists *)
    val coalescedMoves = ref S.empty
    val constrainedMoves = ref S.empty
    val frozenMoves = ref S.empty
    val worklistMoves = ref S.empty
    val activeMoves = ref S.empty

    (* Other data structures *)
    (* TODO: most of these are probably better represented as functions,
       such as is degree() *)
    val adjSet = []
    val adjList = []
    val degree = []
    val moveList = []
    val alias = []
    val color = []

    (* color: {Liveness.igraph, allocation, Graph.node -> int, Frame.register list}
              -> allocation * Temp.temp list *)
    fun color({interference= Liveness.IGRAPH{graph, tnode, gtemp, moves},
               initial, spillCost, registers}) =
        let (* We have len(registers) colors to color with *)
            val k = List.length(registers)

            (* Determines whether the node is move related *)
            fun moveRelated(node) =
                List.exists (fn((n1, n2)) => node = n1 orelse node = n2) moves

            (* Maps the degree of all nodes to the number of adjacent nodes *)
            fun mapDegrees(node::nodes, map) =
                mapDegrees(nods, G.Table.enter(map, node, List.length(Graph.adj node)))
              | mapDegrees([], map) = map

            val degrees = ref mapDegrees(Graph.nodes(graph), G.Table.Empty)

            (* Retrieves the degree of a node *)
            fun getDegree(node) = valOf(G.Table.look(!degrees, node))

            (* Decrements the degree of a node, adding it to the appropriate
               worklist if moveRelated *)
            fun decrementDegree(node) =
                let val dNode = getDegree(node)
                in (degrees := G.Table.enter(!degrees, node, dNode - 1);
                    if dNode = k
                    then if moveRelated(node)
                         then freezeWorklist := S.add(!freezeWorklist, node)
                         else simplifyWorklist := S.add(!simplifyWorklist, node)
                    else ())
                end

            fun simplify() = ()

            fun coalesce() =
                raise Fail "graph is uncolorable without unsupported coalescing"

            fun freeze() = ()

            fun selectSpill() =
                raise Fail "graph is uncolorable without unsupported spilling"

            fun assignColors() = ()

            fun mainLoop() =
                (if not(S.isEmpty(!simplifyWorklist))
                 then simplify()
                 else if not(S.isEmpty(!worklistMoves))
                 then coalesce()
                 else if not(S.isEmpty(!frozenMoves))
                 then freeze()
                 else if not(S.isEmpty(!spillWorklist))
                 then selectSpill()
                 else ();
                 if S.isEmpty(!simplifyWorklist)
                    andalso S.isEmpty(!worklistMoves)
                    andalso S.isEmpty(!freezeWorklist)
                    andalso S.isEmpty(!spillWorklist)
                 then ()
                 else mainLoop())
        in (mainLoop();
            assignColors())
        end

end
