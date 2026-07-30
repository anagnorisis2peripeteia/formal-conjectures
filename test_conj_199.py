import sys
import networkx as nx
import math

def alpha(G):
    if len(G) == 0: return 0
    return max((len(c) for c in nx.find_cliques(nx.complement(G))), default=0)

def triangles_incident(G, v):
    # number of edges in the neighborhood of v
    neighbors = list(G.neighbors(v))
    if len(neighbors) < 2: return 0
    subG = G.subgraph(neighbors)
    return subG.number_of_edges()

def check_199(n):
    import subprocess
    cmd = f"geng -c {n}"
    proc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    for line in proc.stdout:
        g6 = line.strip().decode()
        G = nx.from_graph6_bytes(g6.encode())
        
        a = alpha(G)
        triangles = [triangles_incident(G, v) for v in G.nodes()]
        if not triangles:
            continue
        max_T = max(triangles)
        min_T = min(triangles)
        
        rhs = math.ceil(n / 2.0 + max_T / (1.0 + min_T))
        
        if a > rhs:
            print(f"Counterexample to 199: {g6} (n={n})")
            print(f"alpha={a}, max_T={max_T}, min_T={min_T}, rhs={rhs}")
            return True
    return False

if __name__ == '__main__':
    for n in range(3, 11):
        print(f"Checking n={n}...")
        if check_199(n):
            sys.exit(0)
    print("No counterexample to 199 found for n <= 10.")
