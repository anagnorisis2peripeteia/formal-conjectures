import sys
import networkx as nx
import random
import itertools

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
        for u in G.nodes():
            d = dist_paths.get(v, {}).get(u, -1)
            if d != -1 and d % 2 == 0:
                max_even = max(max_even, d)
    return max_even

def matching_number(G):
    return len(nx.max_weight_matching(G, maxcardinality=True))

def check_72(G):
    if not nx.is_connected(G): return False
    mn = matching_number(G)
    mde = max_dist_even(G)
    ac = alpha_core_size(G)
    if mn > mde + ac:
        print(f"Counterexample to 72: n={len(G)}, edges={G.number_of_edges()}")
        print(f"matching_number={mn}, max_dist_even={mde}, alpha_core={ac}")
        print("Edges:", list(G.edges()))
        return True
    return False

def check_random_graphs():
    for _ in range(5000):
        n = random.randint(5, 20)
        p = random.uniform(0.1, 0.9)
        G = nx.erdos_renyi_graph(n, p)
        if check_72(G): return True
        
        d = random.randint(1, n-1)
        if (n * d) % 2 == 0:
            G = nx.random_regular_graph(d, n)
            if check_72(G): return True
            
        n1 = random.randint(1, n-1)
        n2 = n - n1
        p2 = random.uniform(0.1, 0.9)
        G = nx.bipartite.random_graph(n1, n2, p2)
        if check_72(G): return True

    return False

if __name__ == '__main__':
    print("Starting creative search for Conj 72...")
    if check_random_graphs():
        sys.exit(0)
    print("No counterexample found.")
