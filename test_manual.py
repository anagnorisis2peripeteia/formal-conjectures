import networkx as nx

def tree_number(G):
    max_tree = 0
    import itertools
    for k in range(len(G), 0, -1):
        if k <= max_tree: break
        for sub in itertools.combinations(G.nodes(), k):
            H = G.subgraph(sub)
            if nx.is_connected(H) and H.number_of_edges() == k - 1:
                max_tree = max(max_tree, k)
                break
    return max_tree

def check_144(G):
    if not nx.is_connected(G): return False
    try:
        cycles = nx.minimum_cycle_basis(G)
        if not cycles: return False
        g = min(len(c) for c in cycles)
    except:
        return False

    ecc = nx.eccentricity(G)
    rad = min(ecc.values())
    centers = [v for v, e in ecc.items() if e == rad]
    dist_dict = dict(nx.shortest_path_length(G))
    e_centers = max([min(dist_dict[v][c] for c in centers) for v in G.nodes()], default=0)
    
    rhs = g - 1 + e_centers
    t = tree_number(G)
    print(f"tree={t}, girth={g}, ecc_centers={e_centers}, rhs={rhs}")
    if t < rhs:
        print(f"Counterexample! n={len(G)} tree={t}, girth={g}, ecc_centers={e_centers}, rhs={rhs}")
        return True
    return False

G = nx.cycle_graph(5)
G.add_edge(0, 5)
G.add_edge(5, 6)
check_144(G)

