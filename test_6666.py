import subprocess
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

proc = subprocess.Popen(['geng', '-c', '-q', '-d4', '-D6', '10'], stdout=subprocess.PIPE)
for line in proc.stdout:
    line = line.strip()
    _, adj = parse_graph6(line)
    deg = tuple(sorted([len(adj[i]) for i in range(10)], reverse=True))
    if deg == (6, 6, 6, 6, 4, 4, 4, 4, 4, 4):
        closed = path_closure(10, adj)
        is_complete = all(len(closed[i]) == 9 for i in range(10))
        if not is_complete:
            print(f"Non-closing graph: {line.decode('ascii')}")
