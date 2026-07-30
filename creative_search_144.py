import sys
import networkx as nx
import random

def tree_number(G):
    # This might be slow for larger random graphs!
    # Instead of exact, we can just use a large number if we can't compute it. But we need exact to disprove.
    # Actually, a simple backtrack to find max tree.
    max_tree = 0
    def dfs(current_tree, candidates):
        nonlocal max_tree
        if len(current_tree) > max_tree:
            max_tree = len(current_tree)
        for v in list(candidates):
            candidates.remove(v)
            # v must have exactly one neighbor in current_tree to maintain tree property
            if sum(1 for u in current_tree if G.has_edge(u, v)) == 1:
                # also v cannot have edges to other vertices in current_tree
                dfs(current_tree | {v}, candidates | (set(G.neighbors(v)) - current_tree))
                
    # just an exact algorithm
    # Or just use the combinations one for n <= 15
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
    min_cycle = float('inf')
    for cycle in nx.cycle_basis(G):
        if len(cycle) < min_cycle:
            min_cycle = len(cycle)
    if min_cycle == float('inf'):
        return 0
    return min_cycle

def ecc_centers(G):
    if len(G) == 0: return 0
    ecc = nx.eccentricity(G)
    rad = nx.radius(G)
    centers = [v for v, e in ecc.items() if e == rad]
    dist_dict = dict(nx.shortest_path_length(G))
    max_dist = 0
    for v in G.nodes():
        min_dist = min(dist_dict[v][c] for c in centers)
        max_dist = max(max_dist, min_dist)
    return max_dist

def check_144(G):
    if not nx.is_connected(G): return False
    g = girth(G)
    if g == 0: return False
    e = ecc_centers(G)
    rhs = g - 1 + e
    t = tree_number(G)
    if t < rhs:
        print(f"Counterexample to 144 found!")
        print(f"tree={t}, girth={g}, ecc_centers={e}, rhs={rhs}")
        print("Edges:", list(G.edges()))
        return True
    return False

def check_random_graphs():
    for _ in range(500):
        n = random.randint(5, 12)
        p = random.uniform(0.1, 0.9)
        G = nx.erdos_renyi_graph(n, p)
        if check_144(G): return True
        
        d = random.randint(1, n-1)
        if (n * d) % 2 == 0:
            G = nx.random_regular_graph(d, n)
            if check_144(G): return True

if __name__ == '__main__':
    print("Starting creative search for Conj 144...")
    if check_random_graphs():
        sys.exit(0)
    print("No counterexample found.")
