import sys
import networkx as nx

def path_number(G):
    # order of max induced path
    import itertools
    max_p = 0
    for k in range(len(G), 0, -1):
        if k <= max_p: break
        for sub in itertools.combinations(G.nodes(), k):
            H = G.subgraph(sub)
            if nx.is_connected(H):
                deg = [d for n, d in H.degree()]
                if deg.count(1) == 2 and deg.count(2) == k - 2:
                    max_p = max(max_p, k)
                    break
                elif k == 1 and deg.count(0) == 1:
                    max_p = max(max_p, k)
                    break
                elif k == 2 and deg.count(1) == 2:
                    max_p = max(max_p, k)
                    break
    return max_p

def path_cover_number(G):
    # Minimum number of vertex disjoint paths to cover G
    # For small graphs, we can use an exact approach.
    # Actually, a path cover is a set of paths. The size is len(G) - number of edges in the paths.
    # So we want to find a maximum set of vertex-disjoint edges that form a collection of paths.
    # This is equivalent to finding a maximum collection of paths in G.
    # This is exactly len(G) - max_edges_in_path_cover.
    
    # We can frame it as finding a subgraph of G with max degree 2 and no cycles, maximizing edges.
    max_edges = 0
    n = len(G)
    def solve(edge_idx, current_edges, current_deg):
        nonlocal max_edges
        if len(current_edges) > max_edges:
            # check if no cycles
            H = nx.Graph()
            H.add_nodes_from(G.nodes())
            H.add_edges_from(current_edges)
            try:
                nx.find_cycle(H)
            except nx.NetworkXNoCycle:
                max_edges = len(current_edges)
        
        if edge_idx >= len(edges):
            return
        
        # Try adding edges[edge_idx]
        u, v = edges[edge_idx]
        if current_deg[u] < 2 and current_deg[v] < 2:
            current_edges.append((u,v))
            current_deg[u] += 1
            current_deg[v] += 1
            
            # Check cycles
            H = nx.Graph()
            H.add_edges_from(current_edges)
            try:
                nx.find_cycle(H)
            except nx.NetworkXNoCycle:
                solve(edge_idx + 1, current_edges, current_deg)
                
            current_deg[u] -= 1
            current_deg[v] -= 1
            current_edges.pop()
            
        # Try not adding
        solve(edge_idx + 1, current_edges, current_deg)

    edges = list(G.edges())
    solve(0, [], {v:0 for v in G.nodes()})
    return n - max_edges

def check_137(n):
    import subprocess
    cmd = f"geng -c {n}"
    proc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    for line in proc.stdout:
        g6 = line.strip().decode()
        G = nx.from_graph6_bytes(g6.encode())
        
        p = path_number(G)
        comp = nx.complement(G)
        p_comp = path_cover_number(comp)
        
        rhs = 4.0 / p_comp if p_comp > 0 else float('inf')
        
        if p < rhs:
            print(f"Counterexample to 137: {g6} (n={n})")
            print(f"path(G)={p}, p(comp)={p_comp}, rhs={rhs}")
            return True
    return False

if __name__ == '__main__':
    for n in range(2, 9):
        print(f"Checking n={n}...")
        if check_137(n):
            sys.exit(0)
    print("No counterexample to 137 found for n <= 8.")
