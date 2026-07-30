import networkx as nx
import itertools
import random
from collections import deque

def get_girth(G):
    # Shortest cycle length
    girth = float('inf')
    for n in G.nodes():
        # BFS to find shortest cycle containing n
        dist = {n: 0}
        parent = {n: None}
        q = deque([n])
        while q:
            u = q.popleft()
            for v in G.neighbors(u):
                if v not in dist:
                    dist[v] = dist[u] + 1
                    parent[v] = u
                    q.append(v)
                elif parent[u] != v:
                    girth = min(girth, dist[u] + dist[v] + 1)
    return girth if girth != float('inf') else 0

def is_induced_tree(G, nodes):
    subg = G.subgraph(nodes)
    return nx.is_tree(subg)

def max_induced_tree(G):
    # Find max induced tree by brute force or max clique in some other graph?
    # Actually, finding the maximum induced tree is NP-hard.
    # We can just use an ILP or branch and bound, or just brute force since n is small.
    max_tree = 0
    nodes = list(G.nodes())
    n = len(nodes)
    for r in range(n, 0, -1):
        for combo in itertools.combinations(nodes, r):
            if is_induced_tree(G, combo):
                return r
    return 0

def get_ecc_centers(G):
    # ecc of all nodes
    ecc = nx.eccentricity(G)
    radius = min(ecc.values())
    centers = [n for n in G.nodes() if ecc[n] == radius]
    
    # max distance to nearest center
    max_dist = 0
    # all pairs shortest paths
    apsp = dict(nx.all_pairs_shortest_path_length(G))
    for v in G.nodes():
        dist_to_center = min(apsp[v][c] for c in centers)
        max_dist = max(max_dist, dist_to_center)
    return max_dist

def check_graph(G):
    if not nx.is_connected(G):
        return True
    if nx.is_tree(G):
        return True # girth=0, ecc_centers = dist, tree = n
    
    g = get_girth(G)
    ec = get_ecc_centers(G)
    t = max_induced_tree(G)
    
    # tree(G) >= girth(G) - 1 + ecc(Centers)
    return t >= g - 1 + ec

# Generate graphs using nauty or just random graphs
def generate_graphs(n):
    # Using a simple generator for small n
    # For n=10, there are 11 million graphs, too many for brute force max_induced_tree in python.
    # Let's generate a bunch of random graphs.
    pass

if __name__ == "__main__":
    print("Testing random graphs...")
    count = 0
    for n in range(10, 16):
        print(f"Testing n={n}")
        for p in [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9]:
            for _ in range(200):
                G = nx.erdos_renyi_graph(n, p)
                if nx.is_connected(G):
                    if not check_graph(G):
                        print(f"Counterexample found! n={n}, p={p}")
                        print("Edges:", list(G.edges()))
                        g = get_girth(G)
                        ec = get_ecc_centers(G)
                        t = max_induced_tree(G)
                        print(f"tree={t}, girth={g}, ecc_centers={ec}")
                        exit(0)
    print("Done testing random graphs.")
