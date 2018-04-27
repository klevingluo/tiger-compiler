signature COLOR =
sig
    structure Frame : FRAME
    type allocation = Frame.register Temp.Table.table
    val color : {interference : Liveness.igraph,
                 initial : allocation,
                 spillCost : Graph.node -> int,
                 node2live : Flow.Graph.node -> Temp.temp list,
                 registers : Frame.register list}
                -> (allocation * Temp.temp list)
    val cleanSpills : unit -> unit
end

structure Color : COLOR =
struct

    structure Frame = MipsFrame
    structure Ttab= Temp.Table
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
    
    type move = G.node * G.node
    type allocation = Frame.register Ttab.table
    
    structure M = RedBlackSetFn (struct
                      type ord_key = move
                      fun compare(((_, x1),(_,y1)), ((_, x2), (_,y2))) = 
                        let fun cantor(x,y) = (x + y) * (x + y + 1) div 2 + y
                        in Int.compare(cantor(x1,y1), cantor(x2,y2))
                        end
                     end)

    (* DATA STRUCTURES *)
    val alloc = ref Ttab.empty : allocation ref

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
    val initialref       = ref S.empty 

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
    val degrees  = ref G.Table.empty : int G.Table.table ref (* degree of each node u *)
    val moveList = ref M.empty (* list of associated moves for each node*)
    val color    = ref M.empty (* the color of each node *)
    (* the alias of a coalesced move, that is, u -> v coalesced means alias(v) = u*)
    val alias    = ref Nodemap.empty : G.node Nodemap.map ref 

    fun cleanSpills() = 
      (spilledNodes   := S.empty;
       coloredNodes   := S.empty;
       coalescedNodes := S.empty)

    (* color: {Liveness.igraph, allocation, Graph.node -> int, Frame.register list}
              -> allocation * Temp.temp list *)
    fun color({interference= Liveness.IGRAPH{graph, tnode, gtemp, moves},
              initial, 
              spillCost, 
              node2live,
              registers}) =
        let (* We have len(registers) colors to color with *)
            val k = List.length(registers)

            (* Maps the degree of all nodes to the number of adjacent nodes *)
            fun mapDegrees(node::nodes, map) =
                mapDegrees(nodes, G.Table.enter(map, node, List.length(G.adj node)))
              | mapDegrees([], map) = map

            (* Determines whether the node is move related *)
            fun moveRelated(node) = not (List.null(nodeMoves(node)))

            (* Retrieves the degree of a node *)
            and getDegree(node) = valOf(G.Table.look(!degrees, node))

            (* Decrements the degree of a node, adding it to the appropriate
               worklist if moveRelated *)
            and decrementDegree(node) =
                let val dNode = getDegree(node)
                in (degrees := G.Table.enter(!degrees, node, dNode - 1);
                    if dNode = k
                    then (enableMoves(node::G.adj(node));
                          spillWorklist := S.delete(!spillWorklist, node);
                          if moveRelated(node)
                          then freezeWorklist := S.add(!freezeWorklist, node)
                          else simplifyWorklist := S.add(!simplifyWorklist,node))
                    else ())
                end

            and enableMoves(nodes) =
              let
                fun processMove(move) =
                  if M.member(!activeMoves, move)
                  then (activeMoves := M.delete(!activeMoves, move);
                        worklistMoves := M.add(!worklistMoves, move))
                  else ()
                fun processMoves(moves) = map(fn mv => processMove(mv))(moves)
              in
                map(fn nd => (processMoves(nodeMoves(nd))))(nodes)
              end

            and nodeMoves(node : G.node) : move list= 
              List.filter(fn move => M.member(!activeMoves, move) orelse
                                     M.member(!worklistMoves, move))
                         (M.listItems(!moveList))

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
               app(fn (x,y) => if G.eq(x,v)
                               then moveList := M.add(!moveList, (u,y))
                               else ())
                  (M.listItems(!moveList));
               enableMoves([v]);
               map(fn t => (addEdge(t,u);
                             decrementDegree(t)))
                  (G.adj(v));
               if (getDegree(u) >= k andalso S.member(!freezeWorklist, u))
               then (freezeWorklist := S.delete(!freezeWorklist, u);
                     spillWorklist := S.add(!spillWorklist, u))
               else ())

            and getAlias(node: G.node) =
              (if S.member(!coalescedNodes, node)
               then getAlias(valOf(Nodemap.find(!alias, node)))
               else node)

            and conservative(nodes) =
              (let 
                 fun foldfunc(nd, acc) =
                   if getDegree(nd) >= k 
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
                    (worklistMoves := M.delete(!worklistMoves, (from, to));
                     if (G.eq(u,v))
                     then (coalescedMoves := M.add(!coalescedMoves, (from, to));
                           addWorkList(u))
                     else if (S.member(!precolored, v) orelse 
                              M.member(!adjSet, (u,v)))
                     then (constrainedMoves := M.add(!constrainedMoves,(from,to));
                           addWorkList(u);
                           addWorkList(v))
                     else if (S.member(!precolored, u) andalso 
                              List.exists(fn (t) => ok(t,u))(G.adj(v)) orelse
                              not (S.member(!precolored, u)) andalso
                              conservative(List.revAppend(G.adj(u), G.adj(v))))
                     then (coalescedMoves := M.add(!coalescedMoves, (from, to));
                           combine(u,v);
                           addWorkList(u))
                     else activeMoves := M.add(!activeMoves, (from, to)))
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

            and build() = 
              let
                fun setDegree(nd) = 
                  degrees := G.Table.enter(!degrees, nd, 0);
                fun addEdges(nd) =
                  map(fn n2 => addEdge(nd, n2))(G.succ(nd))
                fun addajs(nd) =
                  adjList := NodeListMap.insert(!adjList, nd, S.empty)
              in
                (app(setDegree)(G.nodes(graph));
                 app(addajs)(G.nodes(graph));
                 map(addEdges)(G.nodes(graph)))
              end

            and addEdge(u : G.node, v : G.node) = 
              let
                fun incrementDegree(nd) = 
                  degrees := G.Table.enter(!degrees, 
                                           nd, 
                                           (case (G.Table.look(!degrees, nd)) of
                                                SOME(x) => x
                                              | NONE => raise Fail "degrees not found") + 1);
                fun addAdjList(a,b) =
                      adjList := 
                        NodeListMap.insert(!adjList, 
                                           a,
                                           S.add(
                             case(NodeListMap.find(!adjList, a)) of 
                                  SOME(x) => x
                                | NONE => raise Fail "error", b))
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

            and selectSpill() = ()

            and makeWorkList() =
              let
                fun sortNode(node) = 
                  if getDegree(node) >= k
                  then spillWorklist := S.add(!spillWorklist, node)
                  else if moveRelated(node)
                  then freezeWorklist := S.add(!freezeWorklist, node)
                  else simplifyWorklist := S.add(!simplifyWorklist, node)
              in
                 (alloc := initial;
                  map(fn nd => initialref := S.add(!initialref, nd))(G.nodes(graph));
                  app(sortNode)(S.listItems(!initialref)))
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

            and assignColors() = 
              let
                val ok = ref registers : Frame.register list ref
                fun ruleOutColor(ot: G.node) = 
                   ok := List.filter(fn (color) => 
                          not (S.member(S.union(!coloredNodes, !precolored), ot)
                                andalso valOf(Ttab.look(!alloc, gtemp(ot))) =
                                color))
                       (!ok)
                fun accfunc(nd) = 
                  (app(ruleOutColor)
                      (case NodeListMap.find(!adjList, nd) of 
                            SOME(x) => S.listItems(x)
                          | NONE => []);
                   if List.null(!ok)
                   then spilledNodes := S.add(!spilledNodes, nd)
                   else (coloredNodes := S.add(!coloredNodes, nd);
                         alloc := Ttab.enter(!alloc, gtemp(nd), hd(!ok))))
                fun colorCoalesce(nd) = 
                         alloc := Ttab.enter(!alloc, gtemp(nd),
                         valOf(Ttab.look(!alloc, gtemp(getAlias(nd)))))
              in
                (app(accfunc)(!selectStack);
                 app(colorCoalesce)(S.listItems(!coalescedNodes)))
              end

            (* simplifies, freezes, and coalesces nodes where possible *)
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

        in 
          (build();
           makeWorkList();
           simplifyLoop();
           assignColors();
           (!alloc, map(gtemp)(S.listItems(!spilledNodes))))
        end

end
