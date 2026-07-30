def check_chvatal(d):
    n = len(d)
    d = sorted(d)
    for k in range(1, (n+2)//2):
        if d[k-1] <= k - 1:
            if d[n-k-1] < n - k:
                return False
    return True

import ast
fails = []
with open('all_seqs.txt') as f:
    for line in f:
        parts = line.strip().split(', seq=')
        n = int(parts[0].split('=')[1])
        seq = ast.literal_eval(parts[1])
        if not check_chvatal(seq):
            fails.append((n, seq))

print(f"Total fails: {len(fails)}")
for n, seq in fails:
    print(f"{n}: {seq}")
