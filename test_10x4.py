def is_traceable(n, adj):
    def dfs(u, visited, count):
        if count == n: return True
        for v in adj[u]:
            if not (visited & (1 << v)):
                if dfs(v, visited | (1 << v), count + 1): return True
        return False
    for start in range(n):
        if dfs(start, 1 << start, 1): return True
    return False

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
                if k < len(g6_bytes): val = g6_bytes[k] - 63
                bit_idx = 0
    return n, adj

import subprocess
proc = subprocess.Popen(['geng', '-c', '-q', '-d4', '-D4', '10'], stdout=subprocess.PIPE)
nontraceable = 0
total = 0
for line in proc.stdout:
    line = line.strip()
    _, adj = parse_graph6(line)
    total += 1
    if not is_traceable(10, adj):
        nontraceable += 1
print(f"Total 10x4: {total}, Nontraceable: {nontraceable}")
