import sys
import subprocess

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

def parse_graph6(g6_bytes):
    n = g6_bytes[0] - 63
    adj = {i: [] for i in range(n)}
    k = 1
    bit_idx = 0
    val = g6_bytes[k] - 63
    for j in range(1, n):
        for i in range(j):
            if (val & (1 << (5 - bit_idx))):
                adj[i].append(j)
                adj[j].append(i)
            bit_idx += 1
            if bit_idx == 6:
                k += 1
                if k < len(g6_bytes):
                    val = g6_bytes[k] - 63
                bit_idx = 0
    return n, adj

def L_s_is_le_6(n, adj):
    # Try all subsets L of size 7. If we find one where G-L is connected and all L have neighbors in G-L, then L_s >= 7.
    # Return True if NO such subset exists (i.e. L_s <= 6).
    
    # We can iterate subsets L of size 7:
    import itertools
    for L_tuple in itertools.combinations(range(n), 7):
        V_minus_L = [v for v in range(n) if v not in L_tuple]
        if not V_minus_L: continue
        
        start = V_minus_L[0]
        visited = set([start])
        queue = [start]
        while queue:
            curr = queue.pop(0)
            for neighbor in adj[curr]:
                if neighbor in V_minus_L and neighbor not in visited:
                    visited.add(neighbor)
                    queue.append(neighbor)
        
        if len(visited) == len(V_minus_L):
            valid = True
            for v in L_tuple:
                if not any(neighbor in V_minus_L for neighbor in adj[v]):
                    valid = False
                    break
            if valid:
                return False # L_s >= 7
    return True # L_s <= 6

for n_v in range(7, 12):
    print(f"Checking {n_v}")
    proc = subprocess.Popen(['geng', '-c', f'-D6', str(n_v)], stdout=subprocess.PIPE)
    for line in proc.stdout:
        line = line.strip()
        n, adj = parse_graph6(line)
        deg = [len(adj[i]) for i in range(n)]
        if residue(deg) == 2:
            if L_s_is_le_6(n, adj):
                print(f"FOUND! n={n_v} graph={line.decode('ascii')}")
                sys.exit(0)
    print(f"None found for {n_v}")
