def residueAux(s):
    if len(s) == 0: return 0
    if s[0] == 0: return len(s)
    d = s[0]
    rest = s[1:]
    for i in range(min(d, len(rest))):
        rest[i] -= 1
    rest.sort(reverse=True)
    while len(rest) > 0 and rest[-1] < 0:
        return -100 # Invalid
    return residueAux(rest)

def is_graphical(s):
    s = list(s)
    s.sort(reverse=True)
    while True:
        if len(s) == 0: return True
        if s[0] == 0: return all(x == 0 for x in s)
        d = s[0]
        s = s[1:]
        if len(s) < d: return False
        for i in range(d):
            s[i] -= 1
            if s[i] < 0: return False
        s.sort(reverse=True)

def gen_seqs(n, max_len, min_d=1, max_d=None):
    if max_len == 0: return [[]]
    if max_d is None: max_d = n - 1
    res = []
    for d in range(min(n-1, max_d), min_d-1, -1):
        for sub in gen_seqs(n, max_len - 1, min_d, d):
            res.append([d] + sub)
    return res

for n in range(1, 13):
    for s in gen_seqs(n, n, 1, min(n-1, 6)):
        if sum(s) % 2 != 0: continue
        if not is_graphical(s): continue
        if residueAux(list(s)) != 2: continue
        t = n // 2
        max_d = s[0] if s else 0
        min_d = s[-1] if s else 0
        
        # Check hypotheses
        is_reg_2 = (min_d == 2 and max_d == 2)
        is_reg_3_8 = (n == 8 and min_d == 3 and max_d == 3)
        is_reg_4_10 = (n == 10 and min_d == 4 and max_d == 4)
        is_5_12 = (n == 12 and min_d == 5 and max_d == 5)
        
        if is_reg_2 or is_reg_3_8 or is_reg_4_10 or is_5_12:
            continue
            
        hNotHalf = (2 * min_d < n - 1)
        if not hNotHalf: continue
        
        # Chvatal path condition
        asc = sorted(s)
        chvatal = True
        for k in range(1, n // 2 + 1): # k from 1 to n/2
            if asc[k-1] <= k:
                if asc[n-k-1] < n - k:
                    chvatal = False
                    break
        if chvatal: continue
        
        print(f"SURVIVOR n={n}, s={s}")

print("Done testing survivors")
