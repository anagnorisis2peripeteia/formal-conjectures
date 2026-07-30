def residueAux(s):
    if len(s) == 0: return 0
    d = s[0]
    rest = s[1:]
    for i in range(min(d, len(rest))):
        rest[i] -= 1
    rest.sort(reverse=True)
    while len(rest) > 0 and rest[-1] < 0:
        return -100 # Invalid
    return residueAux(rest) + (1 if d > len(rest) else 0)

def gen_seqs(n, max_len, min_d=1, max_d=None):
    if max_len == 0: return [[]]
    if max_d is None: max_d = n - 1
    res = []
    for d in range(min(n-1, max_d), min_d-1, -1):
        for sub in gen_seqs(n, max_len - 1, min_d, d):
            res.append([d] + sub)
    return res

for n in range(1, 13):
    for s in gen_seqs(n, n):
        if sum(s) % 2 != 0: continue
        if residueAux(list(s)) != 2: continue
        t = n // 2
        max_d = s[0] if s else 0
        min_d = s[-1] if s else 0
        if 2 * max_d < n - 1:
            print(f"n={n}, s={s}, maxD={max_d}, minD={min_d}")
