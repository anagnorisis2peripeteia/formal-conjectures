import sys
import subprocess
import networkx as nx

def tree_number(G):
    max_tree = 0
    import itertools
    for k in range(len(G), 0, -1):
        if k <= max_tree: break
        for sub in itertools.combinations(G.nodes(), k):
            H = G.subgraph(sub)
            if nx.is_connected(H) and H.number_of_edges() == k - 1:
                max_tree = max(max_tree, k)
                break
    return max_tree

def check_144(G):
    if not nx.is_connected(G): return False
    try:
        cycles = nx.minimum_cycle_basis(G)
        if not cycles: return False
        g = min(len(c) for c in cycles)
    except:
        return False

    ecc = nx.eccentricity(G)
    rad = min(ecc.values())
    centers = [v for v, e in ecc.items() if e == rad]
    dist_dict = dict(nx.shortest_path_length(G))
    e_centers = max([min(dist_dict[v][c] for c in centers) for v in G.nodes()], default=0)
    
    rhs = g - 1 + e_centers
    t = tree_number(G)
    if t < rhs:
        print(f"Counterexample! n={len(G)} tree={t}, girth={g}, ecc_centers={e_centers}, rhs={rhs}")
        print("Edges:", list(G.edges()))
        return True
    return False

for n in range(5, 10):
    print(f"Checking n={n}")
    cmd = f"geng -c {n}"
    try:
        output = subprocess.check_output(cmd, shell=True, text=True)
    except Exception as e:
        print("geng error", e)
        sys.exit(1)
    
    for line in output.splitlines():
        if line.strip():
            G = nx.from_graph6_bytes(line.strip().encode('ascii'))
            if check_144(G):
                print(f"Found on {line.strip()}")
                sys.exit(0)
