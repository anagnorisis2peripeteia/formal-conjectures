import networkx as nx
import itertools

def get_tree_max(G):
    max_t = 0
    for k in range(len(G), 0, -1):
        if k <= max_t: continue
        for subset in itertools.combinations(G.nodes(), k):
            if nx.is_tree(G.subgraph(subset)):
                max_t = k
                break
    return max_t

def check(G):
    t = get_tree_max(G)
    cycles = nx.cycle_basis(G)
    g = 0
    if cycles:
        g = min(len(c) for c in cycles) # Note: cycle_basis might not give shortest, but for bipartite it's usually 4 or 6.
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
    if t < g - 1 + max_d:
        print(f"Counterexample! n={len(G)}")
        print(f"tree={t} girth={g} ecc={max_d}")
        return False
    return True

# Bipartite with 1 dominating vertex
for k in range(3, 7):
    # A has k+1 vertices, B has k vertices
    for mask in range(1 << (k * k)):
        G = nx.Graph()
        G.add_nodes_from(range(2*k + 1))
        # 0 is c
        for i in range(k):
            G.add_edge(0, i + 1) # c to B
        
        valid = True
        for i in range(k):
            for j in range(k):
                if mask & (1 << (i*k + j)):
                    G.add_edge(i + 1, k + 1 + j)
        
        if nx.is_connected(G):
            # to make it fast, check if ecc(centers) is large enough to matter
            ecc = nx.eccentricity(G)
            if min(ecc.values()) < max(ecc.values()) - 1:
                if not check(G):
                    exit(0)
print("Done.")
