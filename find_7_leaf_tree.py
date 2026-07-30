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

n, adj = parse_graph6(b"I??F~z{~?")
print(adj)

def find_tree(u, visited, edges, leaves):
    if len(visited) == n:
        if leaves >= 7:
            print("Found tree edges:", edges)
            return True
        return False
    for v in adj[u]:
        if v not in visited:
            # We can explore from v. But we need to explore ALL trees.
            pass

# Since n=10, we can just use a randomized search or BFS
import networkx as nx
G = nx.Graph()
for u in adj:
    for v in adj[u]:
        G.add_edge(u, v)

for i in range(10000):
    import random
    tree_edges = []
    visited = set([0])
    current_nodes = [0]
    while len(visited) < n:
        u = random.choice(current_nodes)
        neighbors = [v for v in adj[u] if v not in visited]
        if neighbors:
            v = random.choice(neighbors)
            visited.add(v)
            current_nodes.append(v)
            tree_edges.append((u, v))
    
    T = nx.Graph()
    T.add_edges_from(tree_edges)
    leaves = [node for node in T.nodes() if T.degree(node) == 1]
    if len(leaves) >= 7:
        print("Found 7-leaf tree!")
        print("Edges:", tree_edges)
        break
