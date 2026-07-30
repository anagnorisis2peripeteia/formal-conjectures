import subprocess
import copy

def path_closure(n, adj):
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

seqs = [
(6, 6, 6, 6, 6, 6, 6, 6, 4, 4, 4, 4),
(6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 4),
(6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 4, 3),
(6, 6, 6, 6, 6, 6, 6, 5, 5, 4, 4, 4),
(6, 6, 6, 6, 6, 6, 6, 4, 4, 4, 4, 4),
(6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5),
(6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 3),
(6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 4, 4),
(6, 6, 6, 6, 6, 6, 5, 5, 4, 4, 4, 4),
(6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 4),
(6, 6, 6, 6, 6, 5, 5, 5, 5, 4, 4, 4),
(6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 5, 5),
(6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 4, 4),
(6, 6, 6, 5, 5, 5, 5, 5, 5, 5, 5, 4)
]

n = 12
cmd = ['geng', '-c', '-q', '-d3', '-D6', str(n)]
proc = subprocess.Popen(cmd, stdout=subprocess.PIPE)
stats = {s: {'graphs': 0, 'non_closing': 0} for s in seqs}
for line in proc.stdout:
    line = line.strip()
    _, adj = parse_graph6(line)
    deg = tuple(sorted([len(adj[i]) for i in range(n)], reverse=True))
    if deg in stats:
        stats[deg]['graphs'] += 1
        closed = path_closure(n, adj)
        if not all(len(closed[i]) == n-1 for i in range(n)):
            stats[deg]['non_closing'] += 1
            print(f"NON CLOSING {deg} : {line.decode('ascii')}")

for seq in seqs:
    print(f"seq={seq}: {stats[seq]['graphs']} graphs, {stats[seq]['non_closing']} non-closing")
