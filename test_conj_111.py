import sys
import networkx as nx
import math

def alpha(G):
    if len(G) == 0: return 0
    return max((len(c) for c in nx.find_cliques(nx.complement(G))), default=0)

def local_independence(G, v):
    neighbors = list(G.neighbors(v))
    if not neighbors: return 0
    subG = G.subgraph(neighbors)
    return alpha(subG)

def avg_l(G):
    return sum(local_independence(G, v) for v in G.nodes()) / len(G)

def check_111(n):
    import subprocess
    cmd = f"geng -c {n}"
    proc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    for line in proc.stdout:
        g6 = line.strip().decode()
        G = nx.from_graph6_bytes(g6.encode())
        
        comp = nx.complement(G)
        comp_degrees = dict(comp.degree())
        max_deg = max(comp_degrees.values())
        S = [v for v, d in comp_degrees.items() if d == max_deg]
        
        # N(S) in the complement
        N_S = set()
        for s in S:
            N_S.update(comp.neighbors(s))
        N_S.difference_update(S) # usually neighborhood does not include S itself, wait, graffiti N(S) usually means union of N(v), does it include S?
        # N(S) means {u | exists v in S with uv in E}. It might intersect S. Let's just use union of neighbors.
        N_S = set()
        for s in S:
            N_S.update(comp.neighbors(s))
        # size of N(S)
        ns_size = len(N_S)
        
        a = alpha(G)
        al = avg_l(G)
        rhs = math.ceil(1 + ns_size * (al - 1))
        
        if a > rhs:
            print(f"Counterexample to 111: {g6} (n={n})")
            print(f"alpha={a}, |N(S)|={ns_size}, avg_l={al}, rhs={rhs}")
            return True
    return False

if __name__ == '__main__':
    for n in range(3, 10):
        print(f"Checking n={n}...")
        if check_111(n):
            sys.exit(0)
    print("No counterexample to 111 found for n <= 9.")
