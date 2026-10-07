"""Tiny exact controls only. No pair search and no imported producer code."""
from pathlib import Path
from itertools import combinations, product
import ast
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = ROOT / 'openmath/Openmath/Proofs/BipartiteFive.lean'
text = SOURCE.read_text()
block = ast.literal_eval(re.search(r'def blockEdges\b.*?:=\s*(\[.*?\])', text, re.S).group(1))

def norm(a, b):
    return tuple(sorted((a, b)))

def links(name):
    section = re.search(r'def ' + name + r'\b.*?\ninstance', text, re.S).group(0)
    return ast.literal_eval('[' + re.search(r'\(\[(.*?)\]\s*:', section, re.S).group(1) + ']')

edges = {norm(a, b) for a, b in block}
for size, name in ((13, 'pair26'), (26, 'half52'), (52, 'graph')):
    edges = {norm(a + off, b + off) for off in (0, size) for a, b in edges} | {norm(a, b) for a, b in links(name)}
assert len(edges) == 260

def side(v):
    return int(((v % 13 in (3,4,5,7,9,11,12)) != ((v // 13) % 2 == 1)))

def degrees(vertices, edge_set):
    return {v: sum(v in e for e in edge_set) for v in vertices}

assert set(degrees(range(104), edges).values()) == {5}
assert all(side(a) != side(b) for a,b in edges)
P = {v for v in range(104) if side(v) == 0}
Q = set(range(104)) - P
assert len(P) == len(Q) == 52
U = {0,55}
V = set(range(104)) - U
HE = {e for e in edges if not (set(e) & U)}
assert len(HE) == 250
HP, HQ = P-U, Q-U
assert len(HP) == len(HQ) == 51
hd = degrees(V, HE)
assert set(hd.values()) == {4,5}
W = set(range(52)) - U
X, Y = HQ & W, HP & W
assert len(X) == 26 and len(Y) == 25
cut = sorted(e for e in HE if (e[0] in W) != (e[1] in W))
assert cut == [(25,90),(38,77)]
a = sum((u in X and v in HP-Y) or (v in X and u in HP-Y) for u,v in HE)
b = sum((u in HQ-X and v in Y) or (v in HQ-X and u in Y) for u,v in HE)
DX, DY = sum(5-hd[v] for v in X), sum(5-hd[v] for v in Y)
assert (a,b,DX,DY) == (1,1,5,0)
assert DX-DY == 5*(len(X)-len(Y))-a+b
# This one displayed Hall witness excludes every spanning q-factor q>=2.
assert a < 2*(len(X)-len(Y))
# A simple augmenting-path check supplies a perfect matching, proving max q=1.
adj = {u: sorted(v for v in HQ if norm(u,v) in HE) for u in HP}
match = {}
def augment(u, seen):
    for v in adj[u]:
        if v in seen:
            continue
        seen.add(v)
        if v not in match or augment(match[v], seen):
            match[v] = u
            return True
    return False
assert all(augment(u,set()) for u in sorted(HP))
matching = sorted(norm(u,v) for v,u in match.items())
assert len(matching) == 51 and set().union(*(set(e) for e in matching)) == V

C1 = [0,1,3,2,6,4,5,7,15,11,9,13,12,14,10,8,0]
C2 = [0,2,10,11,3,7,6,14,15,13,5,1,9,8,12,4,0]
def cycle_edges(c):
    assert c[0] == c[-1] and len(set(c[:-1])) == 16
    return {norm(a,b) for a,b in zip(c,c[1:])}
Q4E = {norm(v, v^(1<<i)) for v in range(16) for i in range(4)}
E1, E2 = cycle_edges(C1), cycle_edges(C2)
assert E1 | E2 == Q4E and not E1 & E2
qadj = {v: {w for w in range(16) if norm(v,w) in Q4E} for v in range(16)}
assert max(len(qadj[u] & qadj[v]) for u,v in combinations(range(16),2)) == 2
crossings = []
for i in range(4):
    cuti = {e for e in Q4E if ((e[0]>>i)&1) != ((e[1]>>i)&1)}
    assert len(cuti) == 8
    crossings.append([len(E1 & cuti),len(E2 & cuti)])
    assert sum(crossings[-1]) == 8

# Exact nine-state compatibility product bound for four red + four blue ports.
states = list(product(range(3),repeat=2))
best = 0
best_sets = None
for mask in range(1<<9):
    A = [s for i,s in enumerate(states) if mask>>i&1]
    B = [t for t in states if all(s[0] == t[0] or s[1] == t[1] for s in A)]
    if len(A)*len(B) > best:
        best, best_sets = len(A)*len(B), [A,B]
assert best == 9
out = {
    'scope': 'Finite edge, Hall, perfect-matching, Q4-cycle and nine-state checks. No Pair decision, no census, no Lean or project oracle.',
    'source': str(SOURCE.relative_to(ROOT)),
    'source_sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    'host': {'n':104,'e':260,'degree':5,'bipartition':[52,52]},
    'balanced_deletion': {
        'deleted':[0,55], 'n':102, 'e':250, 'bipartition':[51,51],
        'degree_counts': {str(d): sum(x==d for x in hd.values()) for d in sorted(set(hd.values()))},
        'cut_region':sorted(W), 'cut_edges':cut,
        'hall_left':sorted(X), 'hall_right':sorted(Y),
        't':len(X)-len(Y), 'a':a, 'b':b, 'D_X':DX, 'D_Y':DY,
        'max_spanning_regular_degree':1, 'perfect_matching':matching,
        'avoidance': 'Inherited on paper from the previously PASS-certified source graph, not newly oracle-checked.'
    },
    'Q4': {'cycles':[C1,C2], 'crossings_by_coordinate':crossings, 'max_pair_codegree':2, 'all_coordinate_boundaries':8},
    'nine_state_compatibility': {'max_cross_free_product':best,'attainment':best_sets}
}
(HERE/'CONTROL-CHECK.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({
    'status':'checks passed',
    'deleted':[0,55], 'degrees':out['balanced_deletion']['degree_counts'],
    'hall': {'X':len(X),'Y':len(Y),'a':a,'b':b,'D_X':DX,'D_Y':DY},
    'max_spanning_regular_degree':1, 'Q4_crossings':crossings,
    'nine_state_product_bound':best,
    'source_sha256':out['source_sha256']
},indent=2))
