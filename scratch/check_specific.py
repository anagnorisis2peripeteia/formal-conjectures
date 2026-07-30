import networkx as nx
import itertools

G = nx.Graph()
# A = 0, 1, 2, 3 where 0 is c, 1,2,3 are a's
# B = 4, 5, 6 where 4,5,6 are b's
G.add_edges_from([(0,4), (0,5), (0,6)])
G.add_edges_from([(1,5), (1,6)])
G.add_edges_from([(2,4), (2,6)])
G.add_edges_from([(3,4), (3,5)])

def get_tree_max(G):
    for k in range(len(G), 0, -1):
        for subset in itertools.combinations(G.nodes(), k):
            if nx.is_tree(G.subgraph(subset)):
                return k
    return 0

def check(G):
    t = get_tree_max(G)
    cycles = nx.cycle_basis(G)
    g = min(len(c) for c in cycles) if cycles else 0
    if g > 0:
        # let's be safe
        g = 1000
        for u, v in G.edges():
            G.remove_edge(u, v)
            try:
                g = min(g, nx.shortest_path_length(G, u, v) + 1)
            except: pass
            G.add_edge(u, v)
    ecc = nx.eccentricity(G)
    min_ecc = min(ecc.values())
    centers = [v for v in G.nodes() if ecc[v] == min_ecc]
    max_d = 0
    for v in G.nodes():
        max_d = max(max_d, min(nx.shortest_path_length(G, v, c) for c in centers))
    print(f"tree={t} girth={g} ecc(Centers)={max_d} centers={centers}")
    if t < g - 1 + max_d:
        print(f"Counterexample! n={len(G)}")
        return False
    return True

check(G)
