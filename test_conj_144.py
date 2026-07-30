import sys
import networkx as nx

def tree_number(G):
    # max induced tree size
    # check all subsets
    import itertools
    max_tree = 0
    # to be faster, maybe start from largest
    for k in range(len(G), 0, -1):
        if k <= max_tree: break
        for sub in itertools.combinations(G.nodes(), k):
            H = G.subgraph(sub)
            if nx.is_connected(H) and H.number_of_edges() == k - 1:
                max_tree = max(max_tree, k)
                break
    return max_tree

def girth(G):
    # length of shortest cycle
    min_cycle = float('inf')
    for cycle in nx.cycle_basis(G):
        if len(cycle) < min_cycle:
            min_cycle = len(cycle)
    if min_cycle == float('inf'):
        # wait, if tree, girth is usually defined as infinity, but what does graffiti say?
        return 0
    return min_cycle

def ecc_centers(G):
    if len(G) == 0: return 0
    ecc = nx.eccentricity(G)
    rad = nx.radius(G)
    centers = [v for v, e in ecc.items() if e == rad]
    # ecc of a set S is max_{v} min_{s in S} d(v,s)
    dist_dict = dict(nx.shortest_path_length(G))
    max_dist = 0
    for v in G.nodes():
        min_dist = min(dist_dict[v][c] for c in centers)
        max_dist = max(max_dist, min_dist)
    return max_dist

def check_144(n):
    import subprocess
    cmd = f"geng -c {n}"
    proc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    for line in proc.stdout:
        g6 = line.strip().decode()
        G = nx.from_graph6_bytes(g6.encode())
        
        # girth in graffiti is usually length of shortest cycle, if acyclic, what is it?
        # Let's just check graphs with a cycle
        g = girth(G)
        if g == 0: continue
        
        t = tree_number(G)
        e = ecc_centers(G)
        rhs = g - 1 + e
        if t < rhs:
            print(f"Counterexample to 144: {g6} (n={n})")
            print(f"tree={t}, girth={g}, ecc_centers={e}, rhs={rhs}")
            return True
    return False

if __name__ == '__main__':
    for n in range(3, 10):
        print(f"Checking n={n}...")
        if check_144(n):
            sys.exit(0)
    print("No counterexample to 144 found for n <= 9.")
