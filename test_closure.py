def path_closure(n, adj):
    import copy
    current = copy.deepcopy(adj)
    while True:
        added = False
        deg = [len(current[i]) for i in range(n)]
        new_edges = []
        for i in range(n):
            for j in range(i+1, n):
                if j not in current[i] and deg[i] + deg[j] >= n - 1:
                    new_edges.append((i, j))
        if not new_edges:
            break
        for i, j in new_edges:
            if j not in current[i]:
                current[i].append(j)
                current[j].append(i)
                added = True
    return current

import sys
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

n, adj = parse_graph6(b"F?zV_")
closed = path_closure(n, adj)
is_complete = all(len(closed[i]) == n-1 for i in range(n))
print(f"Is complete: {is_complete}")
