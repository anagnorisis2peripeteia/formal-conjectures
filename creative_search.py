import sys
import networkx as nx
import random
import math

def alpha(G):
    if len(G) == 0: return 0
    return max((len(c) for c in nx.find_cliques(nx.complement(G))), default=0)

def alpha_core_size(G):
    a = alpha(G)
    core = 0
    for v in G.nodes():
        H = G.copy()
        H.remove_node(v)
        if alpha(H) < a:
            core += 1
    return core

def max_dist_even(G):
    dist_paths = dict(nx.all_pairs_shortest_path_length(G))
    max_even = 0
    for v in G.nodes():
        even_count = sum(1 for u in G.nodes() if dist_paths.get(v, {}).get(u, -1) % 2 == 0)
        max_even = max(max_even, even_count)
    return max_even

def tree_number(G):
    import itertools
    max_tree = 0
    for k in range(len(G), 0, -1):
        if k <= max_tree: break
        for sub in itertools.combinations(G.nodes(), k):
            H = G.subgraph(sub)
            if nx.is_connected(H) and H.number_of_edges() == k - 1:
                max_tree = max(max_tree, k)
                break
    return max_tree

def check_108(G):
    if not nx.is_connected(G): return False
    a = alpha(G)
    mde = max_dist_even(G)
    ac = alpha_core_size(G)
    rhs = mde + 2 * (ac // 3)
    if a > rhs:
        print(f"Counterexample to 108: n={len(G)}, edges={G.number_of_edges()}")
        print(f"alpha={a}, max_dist_even={mde}, alpha_core={ac}")
        print("Edges:", list(G.edges()))
        return True
    return False

def check_random_graphs():
    for _ in range(500):
        n = random.randint(5, 20)
        # Random G_{n,p}
        p = random.uniform(0.1, 0.9)
        G = nx.erdos_renyi_graph(n, p)
        if check_108(G): return True
        
        # Random regular
        d = random.randint(1, n-1)
        if (n * d) % 2 == 0:
            G = nx.random_regular_graph(d, n)
            if check_108(G): return True
            
        # Random bipartite
        n1 = random.randint(1, n-1)
        n2 = n - n1
        p2 = random.uniform(0.1, 0.9)
        G = nx.bipartite.random_graph(n1, n2, p2)
        if check_108(G): return True

if __name__ == '__main__':
    print("Starting creative search for Conj 108...")
    if check_random_graphs():
        sys.exit(0)
    print("No counterexample found.")
