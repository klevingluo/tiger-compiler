(* TODO: may not need this sig if we choose not to handle spills *)

signature COLOR =
sig
    structure Frame : FRAME
    type allocation = Frame.register Temp.Table.table
    val color : {interference : Liveness.igraph,
                 initial : Graph.node list,
                 spillCost : Graph.node -> int,
                 node2live : Flow.Graph.node -> Temp.temp list,
                 registers : Frame.register list}
                -> unit
end

structure Color : COLOR =
struct
    structure Frame = MipsFrame

    type allocation = Frame.register Temp.Table.table

    structure G = Graph
    structure T = Temp
    structure S = RedBlackSetFn (struct
                      type ord_key = G.node
                      fun compare((_,n1), (_,n2)) = Int.compare(n1,n2)
                     end)

    (* maps from node to node *)
    structure Nodemap = RedBlackMapFn (struct
                          type ord_key = G.node
                          fun compare((_,n1), (_,n2)) = Int.compare(n1,n2)
                        end)

    structure NodeListMap = RedBlackMapFn (struct
                             type ord_key = G.node
                             fun compare((_,n1), (_,n2)) = Int.compare(n1,n2)
                           end)

    (* the cantor function maps pairs of integers to unique integers *)
    (* sets of ordered pairs of nodes *)
    structure M = RedBlackSetFn (struct
                      type ord_key = (G.node * G.node)
                      fun compare(((_, x1),(_,y1)), ((_, x2), (_,y2))) = 
                        let fun cantor(x,y) = (x + y) * (x + y + 1) div 2 + y
                        in Int.compare(cantor(x1,y1), cantor(x2,y2))
                        end
                     end)

    (* DATA STRUCTURES *)

    (* Work-lists, Sets, and Stacks *)
    (* TODO: these should be mutually disjoint, may aid debugging if we enforce
       that somehow *)
    val precolored       = ref S.empty (* machine registers, precolored *)
    val simplifyWorklist = ref S.empty (* low-degree, non-move-related nodes *)
    val freezeWorklist   = ref S.empty (* low-degree move-related nodes *)
    val spillWorklist    = ref S.empty (* high degree nodes *)
    val spilledNodes     = ref S.empty (* nodes marked for spilling this round *)
    val coalescedNodes   = ref S.empty (* nodes coalesced *)
    val coloredNodes     = ref S.empty (* nodes colored *)

    val selectStack      = ref [] : G.node list ref (* stack of removed temps *)

    (* Move sets *)
    val coalescedMoves   = ref M.empty (* coalesced moves *)
    val constrainedMoves = ref M.empty (* moves whose nodes interfere *)
    val frozenMoves      = ref M.empty (* moves that will not be coalesced *)
    val worklistMoves    = ref M.empty (* moves to coalesce *)
    val activeMoves      = ref M.empty (* moves not ready to coalesce *)

    (* Other data structures *)
    (* TODO: most of these are probably better represented as functions,
       such as is degree() *)

    val adjSet   = ref M.empty (* inteference edges u,v in graph, symmetr closed*)
    (* list of all nodes interfering with u*)
    val adjList  = ref NodeListMap.empty : S.set NodeListMap.map ref
    val degree   = ref M.empty (* degree of each node u *)
    val moveList = ref M.empty (* list of associated moves for each node*)
    val color    = ref M.empty (* the color of each node *)
    (* the alias of a coalesced move, that is, u -> v coalesced means alias(v) = u*)
    val alias    = ref Nodemap.empty : G.node Nodemap.map ref 

    (* color: {Liveness.igraph, allocation, Graph.node -> int, Frame.register list}
              -> allocation * Temp.temp list *)
    fun color({interference= Liveness.IGRAPH{graph, tnode, gtemp, moves},
              initial, 
              spillCost, 
              node2live,
              registers}) =
        let (* We have len(registers) colors to color with *)
            val k = List.length(registers)
            val graph = ref graph

            (* Maps the degree of all nodes to the number of adjacent nodes *)
            fun mapDegrees(node::nodes, map) =
                mapDegrees(nodes, G.Table.enter(map, node, List.length(G.adj node)))
              | mapDegrees([], map) = map

            val degrees = ref (mapDegrees(G.nodes(!graph), G.Table.empty))

            (* Determines whether the node is move related *)
            fun moveRelated(node) =
                List.exists (fn((n1, n2)) => G.eq(node, n1) orelse
                                             G.eq(node,n2)) 
                             moves 

            (* Retrieves the degree of a node *)
            and getDegree(node) = valOf(G.Table.look(!degrees, node))

            (* Decrements the degree of a node, adding it to the appropriate
               worklist if moveRelated *)
            and decrementDegree(node) =
                let val dNode = getDegree(node)
                in (degrees := G.Table.enter(!degrees, node, dNode - 1);
                     (* TODO: might be wrong  *)
                    if dNode < k
                    then (enableMoves(node::G.adj(node));
                          spillWorklist := S.delete(!spillWorklist, node);
                          if moveRelated(node)
                          then freezeWorklist := S.add(!freezeWorklist, node)
                          else simplifyWorklist := S.add(!simplifyWorklist,node))
                    else ())
                end

            and enableMoves(node::rest) =
              let
                fun processMove(move) =
                  if M.member(!activeMoves, move)
                  then (activeMoves := M.delete(!activeMoves, move);
                  worklistMoves := M.add(!worklistMoves, move))
                  else ()
                fun processMoves(moves) = map(fn mv => processMove(mv))(moves)
              in
                map(fn nd => (processMoves(nodeMoves(nd))))(G.nodes(!graph))
              end

            and nodeMoves(node : G.node) : (G.node * G.node) list= 
              List.filter(fn((n1, n2)) => G.eq(node, n1) orelse
                                          G.eq(node, n2)) 
                         (M.listItems(!activeMoves))

            and simplify() = (
              let
                fun simplifyNode(node) =
                  (simplifyWorklist := S.delete(!simplifyWorklist, node);
                   selectStack := node :: !selectStack;
                   app(decrementDegree)(G.adj(node)))
              in
                app(simplifyNode)(S.listItems(!simplifyWorklist))
              end
              )

            and removeNode(nd, graph) =
              (selectStack := nd:: !selectStack;
               let
                 val toEdges = G.pred(nd)
                 val fromEdges = G.succ(nd)
                 fun rmToEdges(graph) =
                   map(fn (pred) => G.rm_edge({from=pred, to=nd}))
                      (toEdges)
                 fun rmFromEdges(graph) =
                   map(fn (succ) => G.rm_edge({from=nd, to=succ}))
                      (fromEdges)
               in
                 rmFromEdges(rmToEdges(graph))
               end)

            and combine(u: G.node, v: G.node) =
              (if S.member(!freezeWorklist, v)
               then freezeWorklist := S.delete(!freezeWorklist, v)
               else spillWorklist := S.delete(!spillWorklist, v);
               coalescedNodes := S.add(!coalescedNodes, v);
               alias := Nodemap.insert(!alias, v, u);
               (* TODO: nodemoves u = nm u + nm v *)
               (map(fn t => (addEdge(t,u);
                             decrementDegree(t)))
                  (G.adj(v)));
               if (getDegree(u) >= k andalso S.member(!freezeWorklist, u))
               then (freezeWorklist := S.delete(!freezeWorklist, u);
                     spillWorklist := S.delete(!spillWorklist, u))
               else ())

            and getAlias(node: G.node) =
              (if S.member(!coalescedNodes, node)
               then getAlias(valOf(Nodemap.find(!alias, node)))
               else node)

            and conservative(nodes) =
              (let 
                 fun foldfunc(nd, acc) =
                   if getDegree(nd) > k 
                   then acc + 1 
                   else acc
                 val deg = foldr(foldfunc)(0)(nodes)
               in
                 deg < k
               end)

            and ok(t,r) =
              getDegree(t) < k orelse 
              S.member(!precolored, t) orelse
              M.member(!adjSet, (t,r))

            and addWorkList(u) =
              if (not (S.member(!precolored, u)) andalso
                  not (moveRelated(u)) andalso
                  getDegree(u) < k)
              then (freezeWorklist := S.delete(!freezeWorklist, u);
                    simplifyWorklist := S.add(!simplifyWorklist, u))
              else ()

            and coalesce() =
              let
                fun processMove((from, to)) =
                  let
                    val x = getAlias(from)
                    val y = getAlias(to)
                    val (u,v) = if S.member(!precolored, y)
                                then (y,x)
                                else (x,y)
                  in
                    (worklistMoves := M.delete(!worklistMoves, (x,y));
                     if (G.eq(u,v))
                     then (coalescedMoves := M.add(!coalescedMoves, (from, to));
                           addWorkList(u))
                     else if (S.member(!precolored, v) orelse 
                              M.member(!adjSet, (u,v)))
                     then (constrainedMoves := M.add(!constrainedMoves, (x,y));
                           addWorkList(u);
                           addWorkList(v))
                     else if (S.member(!precolored, u) andalso 
                              List.exists(fn (t) => ok(t,u))(G.adj(v)) orelse
                              not (S.member(!precolored, u)) andalso
                              conservative(List.revAppend(G.adj(u), G.adj(v))))
                     then (coalescedMoves := M.add(!coalescedMoves, (from, to));
                           combine(u,v);
                           addWorkList(u))
                     else activeMoves := M.add(!activeMoves, (x,y)))
                  end
              in
                app(processMove)(M.listItems(!worklistMoves))
              end

            and freeze() = 
              let
                fun processNode(u) = 
                  (freezeWorklist := S.delete(!freezeWorklist, u);
                   simplifyWorklist := S.add(!simplifyWorklist, u);
                   freezeMoves(u))
              in
                app(processNode)(S.listItems(!freezeWorklist))
              end

            and freezeMoves(u) =
              let
                val v = ref (getAlias(u))
                fun freezeMove((x,y)) = 
                  (if G.eq(getAlias(y), getAlias(u))
                   then v := getAlias(x)
                   else v := getAlias(y);
                   activeMoves := M.delete(!activeMoves, (x,y));
                   frozenMoves := M.add(!frozenMoves, (x,y));
                   if (List.length(nodeMoves(!v)) = 0 andalso getDegree(!v) < k)
                   then (freezeWorklist := S.delete(!freezeWorklist, !v);
                         simplifyWorklist := S.add(!simplifyWorklist, u))
                   else())
              in
                app(freezeMove)(nodeMoves(u))
              end

            and livenessAnalysis() = ()

            and build() = 
              let
                (* TODO: dummy shit, remove and replace later *)
                val program = []
                fun liveOut(a) = []
                val revProgram = List.rev(program)
                fun isMoveInstr(a) = false
                fun def(a) = []
                fun addMove(a) = 
                  (moveList := M.add(!moveList, a);
                   worklistMoves := M.add(!worklistMoves, a))
                fun procBlock(b) =
                  let
                    val live = ref(liveOut(b))
                    fun procInstr(a) =
                      (if isMoveInstr(a)
                       then (live := [] (* liveout - use i*);
                             app(addMove)([](* def i, use i *)))
                       else ();
                       live := !live (* + def I *);
                       app(fn des => app(
                           fn sec => addEdge(sec, des))(!live))
                          (def(a)))
                  in
                    app(procInstr)(program)
                  end
              in
                map(procBlock)(revProgram)
              end

            and addEdge(u : G.node,v : G.node) = 
              let
                fun incrementDegree(nd) = 
                  degrees := G.Table.enter(!degrees, 
                                           nd, 
                                           valOf(G.Table.look(!degrees, nd)) + 1);
                fun addAdjList(a,b) =
                      adjList := 
                        NodeListMap.insert(!adjList, 
                                           a,
                                           S.add(valOf(NodeListMap.find(!adjList, a)), b))
              in
                if (M.member(!adjSet, (u,v)) andalso (not (G.eq(u,v))))
                then adjSet := M.add(M.add(!adjSet, (u,v)), (v,u))
                else();
                if (not (S.member(!precolored, u)))
                then (incrementDegree(u);
                      addAdjList(u,v))
                else ();
                if (not (S.member(!precolored, v)))
                then (incrementDegree(v);
                      addAdjList(v,u))
                else ()
              end

            and selectSpill() =
                raise Fail "graph is uncolorable without unsupported spilling"

            and makeWorkList() =
              let
                fun sortNode(node) = 
                  if getDegree(node) >= k
                  then spillWorklist := S.add(!spillWorklist, node)
                  else if moveRelated(node)
                  then freezeWorklist := S.add(!freezeWorklist, node)
                  else simplifyWorklist := S.add(!simplifyWorklist, node)
              in
                map(sortNode)(initial)
              end

            and adjacent(n) =
              let 
                fun removeList(set, ndlist) =
                  foldr(fn (nd, acc) => S.delete(acc, nd))
                       (set)
                       (ndlist)
              in
                removeList(valOf(NodeListMap.find(!adjList, n)), 
                            List.revAppend(!selectStack,
                                           S.listItems(!coalescedNodes)))
              end

            and assignColors() = ()
            and rewriteProgram(spilledNodes) = ()

            (* simplifies, freezes, and coalseces nodes where possible *)
            and simplifyLoop() = (
                 if   not(S.isEmpty(!simplifyWorklist)) then simplify()
                 else if not(M.isEmpty(!worklistMoves)) then coalesce()
                 else if not(M.isEmpty(!frozenMoves))   then freeze()
                 else if not(S.isEmpty(!spillWorklist)) then selectSpill()
                 else ();
                 if S.isEmpty(!simplifyWorklist)
                    andalso M.isEmpty(!worklistMoves)
                    andalso S.isEmpty(!freezeWorklist)
                    andalso S.isEmpty(!spillWorklist)
                 then ()
                 else simplifyLoop()
              )

            and mainLoop() =
                (livenessAnalysis();
                 build();
                 makeWorkList();
                 simplifyLoop();
                 assignColors();
                 if not (S.isEmpty(!spilledNodes))
                 then (rewriteProgram(!spilledNodes);
                       mainLoop())
                 else ())
        in 
          mainLoop()
        end

end
