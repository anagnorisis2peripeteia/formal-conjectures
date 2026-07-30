from collections import deque

def hh_step(s):
    if not s: return []
    d = s[0]
    rest = s[1:]
    if d > len(rest): return [-1]
    res = [x - 1 for x in rest[:d]] + rest[d:]
    if any(x < 0 for x in res): return [-1]
    return sorted(res, reverse=True)

def residue(seq):
    s = list(seq)
    while s:
        if s[0] == 0: return len(s)
        s = hh_step(s)
        if s and s[0] < 0: return -1
    return 0

def build(seq):
    # just checking graphic property
    s = list(seq)
    while s:
        if s[0] == 0: return True
        s = hh_step(s)
        if s and s[0] < 0: return False
    return True

res = []

def rec(last, rem, p):
    if rem == 0:
        if sum(p) % 2 == 0 and build(p):
            if residue(p) == 2:
                res.append(tuple(p))
        return
    for v in range(last, -1, -1):
        p.append(v)
        rec(v, rem - 1, p)
        p.pop()

for n in range(1, 15):
    res = []
    rec(6, n, [])
    if res:
        print(f"n={n}:", set(res))
