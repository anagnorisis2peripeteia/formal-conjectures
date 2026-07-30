import sys
import networkx as nx

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
            if d != -1 and d % 2 == 0 and d > 0: # positive even distance
                max_even = max(max_even, d)
    return max_even

def check_108(n):
    import subprocess
    cmd = f"geng -c {n}"
    proc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    for line in proc.stdout:
        g6 = line.strip().decode()
        G = nx.from_graph6_bytes(g6.encode())
        a = alpha(G)
        mde = max_dist_even(G)
        ac = alpha_core_size(G)
        rhs = mde + 2 * (ac // 3)
        if a > rhs:
            print(f"Counterexample to 108: {g6} (n={n})")
            print(f"alpha={a}, max_dist_even={mde}, alpha_core={ac}")
            return True
    return False

if __name__ == '__main__':
    for n in range(2, 10):
        print(f"Checking n={n}...")
        if check_108(n):
            sys.exit(0)
    print("No counterexample to 108 found for n <= 9.")
