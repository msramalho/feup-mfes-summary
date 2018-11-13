sig Node {}
one sig Graph {
	edge: Node -> set Node
}

// domínio g.edge.Node
// contradomínio g.edge[Node]


fun addEdge [g: Graph, from, to: Node] : Graph {
	// como é função o que está cá dentro tem de ser um grafo
	// {} é um grafo em compreensão
	// return implícito porque tem algo do tipo Graph
	{g' : Graph | g'.edge = g.edge + from->to + to->from and
	 (from + to) in (g.edge.Node + g.edge[Node])}
}

pred addEdge [g, g': Graph, from, to: Node] {
	// predicate is true if every condition is true
	(from + to) in (g.edge.Node + g.edge[Node])
	// Aqui só retorna bool
	// Descreve a relação g - g'
	g'.edge = g.edge + from->to
}

// check if every pair is connected
// for all points in the domain and counterdomain of the Nodes
// check if a point can reach any different/disjoint other 
// by considering that the graph is undirected
pred connected [g: Graph] {
	all disj p1, p2: (g.edge.Node + g.edge[Node]) |
	 p2 in p1.^(g.edge + ~(g.edge)) 
}


fun removeNode [g: Graph, p: Node] : Graph {
	{g': Graph | g'.edge = g.edge - (p <: g.edge + g.edge :> p)}
}

pred isBiConnected [g: Graph] {
	all p: (g.edge.Node + g.edge[Node]) | connected[removeNode[g, p]]
}

// guarantee that the addEdge function preserves 
// the bicconective property of the grpaph
check {
	all g, g': Graph, p1, p2: Node |
	 isBiConnected[g] and addEdge[g, g', p1, p2] =>
	 isBiConnected[g']
}


run addEdge {} for 7
