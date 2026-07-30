import sys
import networkx as nx

def residue(s):
    s = sorted(s, reverse=True)
    while s and s[0] > 0:
        d = s.pop(0)
        if d > len(s): return -1
        for i in range(d):
            if s[i] == 0: return -1
            s[i] -= 1
        s.sort(reverse=True)
    return len([x for x in s if x == 0])

def alpha(G):
    if len(G) == 0: return 0
    return max((len(c) for c in nx.find_cliques(nx.complement(G))), default=0)

def is_bipartite_subgraph(G, nodes):
    H = G.subgraph(nodes)
    return nx.is_bipartite(H)

def bipartite_number(G):
    # max induced bipartite subgraph size
    import itertools
    for k in range(len(G), 0, -1):
        for sub in itertools.combinations(G.nodes(), k):
            if is_bipartite_subgraph(G, sub):
                return k
    return 0

def check_109(n):
    import subprocess
    cmd = f"geng -c {n}"
    proc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    for line in proc.stdout:
        g6 = line.strip().decode()
        G = nx.from_graph6_bytes(g6.encode())
        a = alpha(G)
        seq = [d for n, d in G.degree()]
        res = residue(seq)
        if res == -1: continue # invalid sequence, shouldn't happen for graphs
        bg = bipartite_number(G)
        rhs = (res + 2*bg) // 3
        if a > rhs:
            print(f"Counterexample to 109: {g6} (n={n})")
            print(f"alpha={a}, res={res}, b={bg}, rhs={rhs}")
            return True
    return False

if __name__ == '__main__':
    for n in range(2, 9):
        print(f"Checking n={n}...")
        if check_109(n):
            sys.exit(0)
    print("No counterexample to 109 found for n <= 8.")
