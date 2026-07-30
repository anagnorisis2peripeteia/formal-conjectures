import subprocess
import ast

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
                if k < len(g6_bytes):
                    val = g6_bytes[k] - 63
                bit_idx = 0
    return n, adj

fails = [
(7, (4, 4, 4, 4, 4, 1, 1)),
(7, (3, 3, 3, 3, 2, 2, 2)),
(8, (4, 4, 4, 4, 4, 2, 2, 2)),
(8, (5, 5, 4, 4, 3, 3, 3, 3)),
(8, (4, 4, 3, 3, 3, 3, 3, 3)),
(8, (3, 3, 3, 3, 3, 3, 3, 3)),
(8, (5, 4, 4, 4, 3, 3, 3, 2)),
(8, (5, 5, 5, 5, 3, 3, 3, 3)),
(8, (6, 4, 4, 4, 3, 3, 3, 3)),
(8, (4, 4, 4, 4, 3, 3, 2, 2)),
(8, (4, 4, 4, 4, 3, 3, 3, 3)),
(8, (4, 4, 4, 3, 3, 3, 3, 2)),
(8, (5, 5, 5, 5, 5, 5, 1, 1)),
(8, (5, 4, 4, 3, 3, 3, 3, 3)),
(9, (4, 4, 4, 4, 4, 3, 3, 3, 3)),
(9, (5, 5, 5, 5, 4, 3, 3, 3, 3)),
(9, (5, 5, 5, 5, 5, 5, 2, 2, 2)),
(9, (6, 6, 6, 6, 6, 6, 6, 1, 1)),
(10, (6, 6, 6, 6, 6, 4, 4, 4, 3, 3)),
(10, (6, 6, 6, 6, 5, 4, 4, 4, 4, 3)),
(10, (4, 4, 4, 4, 4, 4, 4, 4, 4, 4)),
(10, (6, 5, 5, 4, 4, 4, 4, 4, 4, 4)),
(10, (6, 6, 6, 5, 5, 4, 4, 4, 4, 4)),
(10, (6, 6, 6, 6, 4, 4, 4, 4, 4, 4)),
(10, (5, 5, 5, 5, 4, 4, 4, 4, 4, 4)),
(10, (6, 5, 5, 5, 4, 4, 4, 4, 4, 3)),
(10, (5, 5, 5, 4, 4, 4, 4, 4, 4, 3)),
(10, (5, 5, 4, 4, 4, 4, 4, 4, 4, 4)),
(10, (6, 5, 5, 5, 5, 4, 4, 4, 3, 3)),
(10, (5, 5, 5, 5, 4, 4, 4, 4, 3, 3)),
(10, (6, 5, 5, 5, 5, 4, 4, 4, 4, 4)),
(10, (6, 6, 5, 5, 5, 4, 4, 4, 4, 3)),
(10, (5, 5, 5, 5, 5, 5, 3, 3, 3, 3)),
(10, (6, 6, 6, 6, 6, 6, 6, 2, 2, 2)),
(10, (6, 6, 6, 6, 6, 4, 4, 4, 4, 2)),
(10, (6, 6, 5, 5, 4, 4, 4, 4, 4, 4)),
(10, (6, 6, 6, 6, 6, 4, 4, 4, 4, 4)),
(10, (5, 5, 5, 5, 5, 4, 4, 4, 4, 3)),
(10, (5, 5, 5, 5, 5, 4, 4, 3, 3, 3)),
(11, (5, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4)),
(11, (6, 6, 6, 6, 6, 4, 4, 4, 4, 4, 4)),
(11, (6, 6, 6, 6, 5, 5, 4, 4, 4, 4, 4)),
(11, (6, 6, 6, 6, 6, 5, 4, 4, 4, 4, 3)),
(11, (6, 6, 6, 6, 6, 6, 6, 3, 3, 3, 3)),
(12, (6, 6, 6, 6, 6, 6, 5, 5, 4, 4, 4, 4)),
(12, (6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5)),
(12, (6, 6, 6, 6, 6, 6, 6, 4, 4, 4, 4, 4)),
(12, (6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 4, 4)),
(12, (6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 4)),
(12, (6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 4, 4)),
(12, (6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 5, 5)),
(12, (6, 6, 6, 5, 5, 5, 5, 5, 5, 5, 5, 4)),
(12, (6, 6, 6, 6, 6, 5, 5, 5, 5, 4, 4, 4)),
(12, (6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 3)),
(12, (6, 6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5)),
(12, (5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5)),
(13, (6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5)),
(14, (6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6))
]

for n, seq in fails:
    # use geng -d to generate graphs with this exact sequence? No, we can just use -d and -D for max and min
    # geng doesn't do exact sequence easily, but we can just use the degree sequence to filter
    d_min, d_max = min(seq), max(seq)
    cmd = ['geng', '-c', '-q', f'-d{d_min}', f'-D{d_max}', str(n)]
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE)
    graphs = 0
    non_closing = 0
    for line in proc.stdout:
        line = line.strip()
        _, adj = parse_graph6(line)
        deg = sorted([len(adj[i]) for i in range(n)], reverse=True)
        if tuple(deg) == seq:
            graphs += 1
            closed = path_closure(n, adj)
            is_complete = all(len(closed[i]) == n-1 for i in range(n))
            if not is_complete:
                non_closing += 1
    if graphs > 0:
        print(f"n={n} seq={seq}: {graphs} graphs, {non_closing} non-closing")

