import networkx as nx

# Generate small graphs and test the conjecture
def get_girth(G):
    g = 1000000
    for u, v in G.edges():
        G.remove_edge(u, v)
        try:
            p = nx.shortest_path_length(G, u, v)
            g = min(g, p + 1)
        except nx.NetworkXNoPath:
            pass
        G.add_edge(u, v)
    if g == 1000000: return 0
    return g

def get_tree_max(G):
    # DP or simple recursion for max induced tree
    # Since n <= 10, we can just use itertools
    import itertools
    for k in range(len(G), 0, -1):
        for subset in itertools.combinations(G.nodes(), k):
            if nx.is_tree(G.subgraph(subset)):
                return k
    return 0

def get_ecc_centers(G):
    ecc = nx.eccentricity(G)
    min_ecc = min(ecc.values())
    centers = [v for v in G.nodes() if ecc[v] == min_ecc]
    max_dist = 0
    for v in G.nodes():
        max_dist = max(max_dist, min(nx.shortest_path_length(G, v, c) for c in centers))
    return max_dist

def check(G):
    if not nx.is_connected(G): return True
    t = get_tree_max(G)
    g = get_girth(G)
    e = get_ecc_centers(G)
    if t < g - 1 + e:
        print(f"Counterexample! n={len(G)} edges={list(G.edges())}")
        print(f"tree={t} girth={g} ecc={e}")
        return False
    return True

for n in range(3, 9):
    print(f"Checking n={n}")
    # generate all non-isomorphic connected graphs
    # Since we don't have nauty here easily, let's use Atlas for n<=7
    for G in nx.graph_atlas_g():
        if len(G) == n and nx.is_connected(G):
            if not check(G):
                exit(0)
print("No counterexamples up to n=7 in atlas.")
