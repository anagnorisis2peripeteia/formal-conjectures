import networkx as nx

def tree_number(G):
    max_tree = 0
    def dfs(current_tree, candidates):
        nonlocal max_tree
        if len(current_tree) > max_tree:
            max_tree = len(current_tree)
        for v in list(candidates):
            candidates.remove(v)
            if sum(1 for u in current_tree if G.has_edge(u, v)) == 1:
                dfs(current_tree | {v}, candidates | (set(G.neighbors(v)) - current_tree))
                
    import itertools
    for k in range(len(G), 0, -1):
        if k <= max_tree: break
        for sub in itertools.combinations(G.nodes(), k):
            H = G.subgraph(sub)
            if nx.is_connected(H) and H.number_of_edges() == k - 1:
                max_tree = max(max_tree, k)
                break
    return max_tree

def girth(G):
    try:
        cycles = nx.minimum_cycle_basis(G)
        if not cycles: return 0
        return min(len(c) for c in cycles)
    except:
        return 0

def check_144(G):
    if not nx.is_connected(G): return False
    g = girth(G)
    if g == 0: return False
    ecc = nx.eccentricity(G)
    rad = min(ecc.values())
    centers = [v for v, e in ecc.items() if e == rad]
    dist_dict = dict(nx.shortest_path_length(G))
    e_centers = max([min(dist_dict[v][c] for c in centers) for v in G.nodes()], default=0)
    
    rhs = g - 1 + e_centers
    t = tree_number(G)
    if t < rhs:
        print(f"Counterexample! tree={t}, girth={g}, ecc_centers={e_centers}, rhs={rhs}")
        print("Edges:", list(G.edges()))
        return True
    return False

# Create the specific graph the agent was thinking about
# Wait, let's use the script to test a few manual constructions
G = nx.Graph()
# Two cliques connected by a single edge
G.add_edges_from(nx.complete_graph(5).edges())
G.add_edges_from([(u+5, v+5) for u, v in nx.complete_graph(5).edges()])
G.add_edge(0, 5)
check_144(G)

# Two cliques connected by a path of length 2
G = nx.Graph()
G.add_edges_from(nx.complete_graph(5).edges())
G.add_edges_from([(u+6, v+6) for u, v in nx.complete_graph(5).edges()])
G.add_edge(0, 5)
G.add_edge(5, 6)
check_144(G)

