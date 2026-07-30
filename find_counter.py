import sys
from collections import deque
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

def is_traceable(n, adj):
    def dfs(u, visited, count):
        if count == n:
            return True
        for v in adj[u]:
            if not (visited & (1 << v)):
                if dfs(v, visited | (1 << v), count + 1):
                    return True
        return False
    
    for start_node in range(n):
        if dfs(start_node, 1 << start_node, 1):
            return True
    return False

import time
start = time.time()
for n_v in range(7, 12):
    print(f"Checking {n_v}")
    proc = subprocess.Popen(['geng', '-c', f'-D6', str(n_v)], stdout=subprocess.PIPE)
    for line in proc.stdout:
        line = line.strip()
        n, adj = parse_graph6(line)
        deg = [len(adj[i]) for i in range(n)]
        if residue(deg) == 2:
            if not is_traceable(n, adj):
                print(f"FOUND NONTRACEABLE! {line.decode('ascii')}")
                # check leaves
                print(f"Degree sequence: {sorted(deg, reverse=True)}")
                # check if L_s <= 6 (wait, if it's nontraceable and L_s <= 6, it's a counterexample)
                sys.exit(0)
