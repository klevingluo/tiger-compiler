signature LIVENESS =
sig
    datatype igraph =
             IGRAPH of {graph: Graph.graph,
                        tnode: Temp.temp -> Graph.node,
                        gtemp: Graph.node -> Temp.temp,
                        moves: (Graph.node * Graph.node) list}

    (*
       Takes a flow graph and returns two kinds of information:
       - interference graph
       - table mapping of each flow-graph node to the set of temps that are
         live-out at that node
    *)
    val interferenceGraph :
        Flow.flowgraph ->
        igraph * (Flow.Graph.node -> Temp.temp list)

    val show : igraph -> unit
end

structure Liveness : LIVENESS =
struct

    structure G = Graph
    structure T = Temp
    structure F = Flow
    structure S = IntListSet

    datatype igraph =
             IGRAPH of {graph: G.graph,
                        tnode: T.temp -> G.node,
                        gtemp: G.node -> T.temp,
                        moves: (G.node * G.node) list}

    (* type liveSet = unit T.Table.table * T.temp list *)
    type liveSet = S.set
    type liveMap = liveSet Flow.Graph.Table.table

    (* Helper for dealing with SOME and NONE retrieval of sets *)
    fun lookSet(t, e) =
        case G.Table.look(t, e)
         of SOME(s) => s
          | NONE => S.empty

    (* Helper for dealing with SOME and NONE retrieval of lists *)
    fun lookList(t, e) =
        case G.Table.look(t, e)
         of SOME(l) => l
          | NONE => []

    (* Helper for coercing a list to a set *)
    fun set(l) = S.addList(S.empty, l)

    (* interferenceGraph: Flow.flowgraph -> igraph * (Flow.Graph.node -> Temp.temp list) *)
    fun interferenceGraph(F.FGRAPH{control, def, use, ismove}) =
        let
            val igraph = G.newGraph()
            val fnodes = G.nodes(control)

            (* Initialize an empty mapping of nodes to an empty set *)
            fun initialize() =
                foldl (fn(node, table) => G.Table.enter(table, node, S.empty))
                      Graph.Table.empty
                      fnodes

            (* Iteratively compute liveness (algorithm 10.4) *)
            fun iterate(ins, outs) =
                let
                    (* Flag for whether or not any update was found *)
                    val updated = ref false

                    (* Helper for dealing with SOME and NONE retrieval of sets *)
                    fun lookSet(t, e) =
                        case G.Table.look(t, e)
                         of SOME(s) => s
                          | NONE => S.empty

                    (* Helper for dealing with SOME and NONE retrieval of lists *)
                    fun lookList(t, e) =
                        case G.Table.look(t, e)
                         of SOME(l) => l
                          | NONE => []

                    (* Helper for coercing a list to a set *)
                    fun set(l) = S.addList(S.empty, l)

                    (* Computes new livein and liveout for the specified node *)
                    fun reCompute(node, (ins, outs)) =
                        let
                            val oldIns = lookSet(ins, node)
                            val oldOuts = lookSet(outs, node)
                            val oldUse = set(lookList(use, node))
                            val oldDef = set(lookList(def, node))
                            val newIns = S.union(oldUse, S.difference(oldOuts, oldDef))
                            (* Computes the new liveout from the specified node's successors *)
                            fun succOuts(ins, node) =
                                foldl (fn(n, out) => S.union(lookSet(ins, n), out))
                                      S.empty
                                      (G.succ(node))
                            val newOuts = succOuts(ins, node)
                        in
                            if S.equal(oldIns, newIns) andalso S.equal(oldOuts, newOuts)
                            (* If there's nothing else to do for this node, continue *)
                            then (ins, outs)
                            (* Otherwise update our in & outs *)
                            else (updated := true;
                                  (G.Table.enter(ins, node, newIns),
                                   G.Table.enter(outs, node, newOuts)))
                        end

                    val (newIns, newOuts) = foldl reCompute (ins, outs) (List.rev fnodes)
                in
                    if !updated
                    then iterate(newIns, newOuts)
                    else (newIns, newOuts)
                end

            (* Run liveness iteration to generate our liveness maps *)
            val (liveIns, liveOuts) : (liveMap * liveMap) =
                iterate(initialize(), initialize())

            (* Aggregate our move edges *)
            fun aggregateMoves() =
                let
                    val moves = []
                    fun addMoves(moves, node::nodes) =
                        (case G.Table.look(ismove, node)
                          of SOME(ismove) =>
                             if ismove
                             then
                                 let val (to, from) = (lookList(def, node), lookList(use, node))
                                     (* move blocks only contain single tos and froms *)
                                     val (toNode, fromNode) = (List.hd(to), List.hd(from))
                                 in addMoves((toNode, fromNode)::moves, nodes)
                                 end
                             else addMoves(moves, nodes)
                           (* shouldn't hit this, but depends on impl of flow graph *)
                           | NONE => addMoves(moves, nodes))
                      | addMoves(moves, [])  = []
                in
                    addMoves(moves, fnodes)
                end

            (* Plot temps as nodes and map either representation to each other  *)
            fun plotTemps(temps) =
                let
                    val temps = []
                    val temp2node : G.node T.Table.table = T.Table.empty
                    val node2temp : T.temp F.Graph.Table.table = F.Graph.Table.empty
                    fun processLiveness(tnode, ntemp, temp::temps) =
                        (case T.Table.look(tnode, temp)
                          of SOME(node) => processLiveness(tnode, ntemp, temps)
                           | NONE =>
                             let val node = F.Graph.newNode(igraph)
                                 val tnode' = T.Table.enter(tnode, temp, node)
                                 val ntemp' = F.Graph.Table.enter(ntemp, node, temp)
                             in processLiveness(tnode', ntemp', temps)
                             end)
                      | processLiveness(tnode, ntemp, []) = (tnode, ntemp)
                in processLiveness(temp2node, node2temp, temps)
                end

            fun getTemps() =
                let
                    fun addTemps(temps, node::nodes) =
                        addTemps(S.addList(
                                      S.addList(temps,lookList(def, node)),
                                      lookList(use, node)),
                                 nodes)
                      | addTemps(temps, []) = temps
                in addTemps(S.empty, fnodes)
                end

            val (temp2node, node2temp) = plotTemps(getTemps())

            (* Generate the wrapper for the constructed mapping of temp->node *)
            fun gentnode(nodemap) =
                fn(t : T.temp) => (valOf(T.Table.look(nodemap, t)))

            (* Generate the wrapper for the constructed mapping of node->temp *)
            fun gengtemp(tempmap) =
                fn(n : G.node) => (valOf(F.Graph.Table.look(tempmap, n)))

            (* The table mapping of each flow-graph node to the set of temps that are
               live-out at that node *)
            val node2liveouts =
             fn(node : Flow.Graph.node) =>
                (S.listItems(valOf(F.Graph.Table.look(liveOuts, node))))

        in
            (IGRAPH{graph= igraph,
                    tnode= gentnode(temp2node),
                    gtemp= gengtemp(node2temp),
                    moves= aggregateMoves()},
             node2liveouts)
        end

    (* show: igraph -> unit *)
    fun show(igraph) = ()
end
