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

def generate_sequences(n, max_deg):
    def dfs(idx, current_sum, current_seq):
        if idx == n:
            if current_sum % 2 != 0: return
            if residue(current_seq) == 2:
                yield tuple(current_seq)
            return
        
        last = current_seq[-1] if current_seq else max_deg
        for d in range(min(max_deg, last), 0, -1):
            current_seq.append(d)
            yield from dfs(idx + 1, current_sum + d, current_seq)
            current_seq.pop()

    yield from dfs(0, 0, [])

import sys
for n in range(7, 15):
    for seq in set(generate_sequences(n, 6)):
        print(f"n={n}, seq={seq}")

