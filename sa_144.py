import sys
import networkx as nx
import random
import math

def tree_number(G):
    import itertools
    max_tree = 0
    # Actually, we can just use the fact that an induced tree is an independent set in a certain graph? No.
    # Just exact combinations for n <= 15
    for k in range(len(G), 0, -1):
        if k <= max_tree: break
        for sub in itertools.combinations(G.nodes(), k):
            H = G.subgraph(sub)
            if nx.is_connected(H) and H.number_of_edges() == k - 1:
                return k # Since we iterate downwards, first found is max
    return 0

def girth(G):
    try:
        # A fast way to find girth is BFS from every node
        min_cycle = float('inf')
        for node in G:
            distances = {node: 0}
            parents = {node: None}
            queue = [node]
            for curr in queue:
                for neighbor in G[curr]:
                    if neighbor not in distances:
                        distances[neighbor] = distances[curr] + 1
                        parents[neighbor] = curr
                        queue.append(neighbor)
                    elif parents[curr] != neighbor:
                        # cycle found
                        cycle_len = distances[curr] + distances[neighbor] + 1
                        if cycle_len < min_cycle:
                            min_cycle = cycle_len
        return min_cycle if min_cycle != float('inf') else 0
    except Exception:
        return 0

def ecc_centers(G):
    if len(G) == 0: return 0
    try:
        ecc = nx.eccentricity(G)
        rad = nx.radius(G)
        centers = [v for v, e in ecc.items() if e == rad]
        dist_dict = dict(nx.shortest_path_length(G))
        max_dist = 0
        for v in G.nodes():
            min_dist = min(dist_dict[v][c] for c in centers)
            max_dist = max(max_dist, min_dist)
        return max_dist
    except Exception:
        return 0

def score(G):
    if not nx.is_connected(G): return 9999
    g = girth(G)
    if g == 0: return 9999
    e = ecc_centers(G)
    t = tree_number(G)
    return t - (g - 1 + e)

def hill_climbing(n):
    G = nx.erdos_renyi_graph(n, 0.3)
    while not nx.is_connected(G) or girth(G) == 0:
        G = nx.erdos_renyi_graph(n, 0.3)
    
    current_score = score(G)
    if current_score < 0:
        return G
    
    temp = 2.0
    for i in range(2000):
        # Mutate
        H = G.copy()
        edges = list(H.edges())
        non_edges = list(nx.non_edges(H))
        
        if random.random() < 0.5 and edges:
            H.remove_edge(*random.choice(edges))
        elif non_edges:
            H.add_edge(*random.choice(non_edges))
            
        new_score = score(H)
        
        if new_score < current_score or random.random() < math.exp((current_score - new_score) / temp):
            G = H
            current_score = new_score
            if current_score < 0:
                return G
        temp *= 0.99
    return None

if __name__ == '__main__':
    for n in range(5, 17):
        print(f"Annealing for n={n}")
        for _ in range(5):
            res = hill_climbing(n)
            if res:
                print(f"Found counterexample to 144: n={len(res)}")
                print("Edges:", list(res.edges()))
                t = tree_number(res)
                g = girth(res)
                e = ecc_centers(res)
                print(f"tree={t}, girth={g}, ecc_centers={e}")
                sys.exit(0)
    print("No counterexample found.")
