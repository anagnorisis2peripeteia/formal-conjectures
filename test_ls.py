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

n, adj = parse_graph6(b"I??F~z{~?")
print(f"n = {n}")

# We need to find L_s (maximum number of leaves in a spanning tree).
# To do this, we can just find the maximum size of an independent set in the graph?
# No, L_s is the maximum number of leaves.
# A set of vertices L can be the leaves of a spanning tree iff G - L is connected.
def L_s(n, adj):
    max_leaves = 0
    # Try all subsets L of size k
    for i in range(1, 1 << n):
        # check if G - L is connected
        L = i
        V_minus_L = [v for v in range(n) if not (L & (1 << v))]
        if not V_minus_L:
            continue
        
        # bfs on V_minus_L
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
            # check if every leaf has at least one neighbor in V_minus_L
            valid = True
            for v in range(n):
                if L & (1 << v):
                    if not any(neighbor in V_minus_L for neighbor in adj[v]):
                        valid = False
                        break
            if valid:
                leaves = bin(L).count('1')
                if leaves > max_leaves:
                    max_leaves = leaves
    return max_leaves

print(f"L_s = {L_s(n, adj)}")
