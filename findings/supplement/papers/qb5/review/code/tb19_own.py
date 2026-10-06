# Own enumeration of the n = 19 family: T = K_{4,6} (T_W saturated into T_U), B = K_{3,6} (B_U saturated into B_W),
# plus 10 cut edges T_U -- B_W with T_U cut degree <= 2 (total 10) and B_W cut degree in [1,3].
# Enumerates cut matrices up to row and column permutations by brute-force canonical forms.
import itertools, sys
cols = range(6)
pairs = [frozenset(p) for p in itertools.combinations(cols, 2)]
singles = [frozenset([c]) for c in cols]
def colsums(rows):
    s = [0]*6
    for r in rows:
        for c in r: s[c] += 1
    return s
cands = []
for P in itertools.combinations_with_replacement(range(15), 5):
    rows = [pairs[i] for i in P] + [frozenset()]
    cands.append(rows)
for P in itertools.combinations_with_replacement(range(15), 4):
    for S in itertools.combinations_with_replacement(range(6), 2):
        rows = [pairs[i] for i in P] + [singles[j] for j in S]
        cands.append(rows)
good = [r for r in cands if all(1 <= x <= 3 for x in colsums(r))]
perms = list(itertools.permutations(cols))
def canon(rows):
    best = None
    for p in perms:
        key = tuple(sorted(tuple(sorted(p[c] for c in r)) for r in rows))
        if best is None or key < best: best = key
    return best
classes = {}
for r in good:
    k = canon(r)
    classes.setdefault(k, r)
print("candidates", len(cands), "colsum-ok", len(good), "classes", len(classes), file=sys.stderr)
def g6(n, edges):
    bits = []
    adj = set((min(a,b), max(a,b)) for a, b in edges)
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if (i, j) in adj else 0)
    while len(bits) % 6: bits.append(0)
    out = chr(63 + n)
    for i in range(0, len(bits), 6):
        v = 0
        for b in bits[i:i+6]: v = 2*v + b
        out += chr(63 + v)
    return out
TW = range(0, 4); TU = range(4, 10); BU = range(10, 13); BW = range(13, 19)
for k in sorted(classes):
    edges = [(a, b) for a in TW for b in TU] + [(a, b) for a in BU for b in BW]
    for i, row in enumerate(k):
        for c in row: edges.append((TU[i], BW[c]))
    assert len(edges) == 52
    print(g6(19, edges))
