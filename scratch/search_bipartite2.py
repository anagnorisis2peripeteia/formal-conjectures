import networkx as nx
import itertools

def check(G):
    # Only bipartite graphs
    if not nx.is_bipartite(G): return True
    if max(dict(G.degree()).values()) > 3: return True
    
    ecc = nx.eccentricity(G)
    min_ecc = min(ecc.values())
    centers = [v for v in G.nodes() if ecc[v] == min_ecc]
    max_d = max(min(nx.shortest_path_length(G, v, c) for c in centers) for v in G.nodes())
    
    if max_d >= 2:
        cycles = nx.cycle_basis(G)
        g = 1000
        for u, v in G.edges():
            G.remove_edge(u, v)
            try:
                g = min(g, nx.shortest_path_length(G, u, v) + 1)
            except: pass
            G.add_edge(u, v)
        if g == 1000: g = 0
        
        # tree max
        t = 0
        for s in range(len(G), 0, -1):
            if s <= t: continue
            for sub in itertools.combinations(G.nodes(), s):
                if nx.is_tree(G.subgraph(sub)):
                    t = s
                    break
                    
        if t < g - 1 + max_d:
            print(f"COUNTEREXAMPLE: n={len(G)} g={g} ecc={max_d} tree={t}")
            print(G.edges())
            return False
    return True

for n in range(6, 12):
    # random search for cubic or subcubic bipartite graphs
    print(f"Testing n={n}")
    for _ in range(2000):
        # generate random bipartite
        n1 = n // 2
        n2 = n - n1
        G = nx.bipartite.random_graph(n1, n2, 0.4)
        if not nx.is_connected(G): continue
        if not check(G): exit(0)
print("Done")
