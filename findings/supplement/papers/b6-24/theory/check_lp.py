"""Check the rigidity criterion (NOTES §3) on random balanced bipartite graphs with a 4-factor
(not necessarily sparse), n <= 16, every balanced T exhaustively:
   max_F |F ∩ E0(T)| <= 1   <=>   (A) |E0 - Ex| <= 1  or  (B) exists S with s(S) = 1, E0 - Ex ⊆ ∂_P(S).
Also checks max_F |F ∩ E0(T)| against brute-force enumeration of all 4-factors for n <= 12, and
the identity s(S) = e_H(S_Q, P-S) + e_F(S_P, Q-S) for random F and all S."""
import sys, itertools, random
sys.path.insert(0, '.')
from tools import *
seed = int(sys.argv[1]); a = int(sys.argv[2]); trials = int(sys.argv[3])
rng = random.Random(seed)
def all_four_factors(I):
    # brute force via SAT enumeration
    from pysat.solvers import Cadical153
    pool = IDPool(); var = {e: pool.id(e) for e in I.pq}
    S = Cadical153()
    for v in I.Y:
        lits = [var[e] for e in I.pq if v in e]
        for cl in CardEnc.equals(lits=lits, bound=4, vpool=pool, encoding=EncType.seqcounter).clauses:
            S.add_clause(cl)
    out = []
    while S.solve():
        m = set(l for l in S.get_model() if l > 0)
        F = frozenset(e for e in I.pq if var[e] in m)
        out.append(F)
        S.add_clause([-var[e] for e in F])
    S.delete()
    return out
nchk = 0; nrig = 0; mism = 0; ninst = 0
for t in range(trials):
    n = 2 * a
    Y = nx.Graph(); Y.add_nodes_from(range(n))
    h = a // 2   # two K_{h,h} blocks (h = 4 when a = 8)
    A = (list(range(0, h)), list(range(a, a + h))); B = (list(range(h, a)), list(range(a + h, 2 * a)))
    for (BP, BQ) in (A, B):
        for p in BP:
            for q in BQ:
                Y.add_edge(p, q)
    # optionally thin the blocks so they are not complete (keep degrees >= 4 after cross edges)
    p1, q1, p2, q2 = A[0][0], A[1][0], B[0][0], B[1][0]
    Y.remove_edge(p1, q1); Y.remove_edge(p2, q2)
    Y.add_edge(p1, q2); Y.add_edge(p2, q1)
    allpairs = [(p, a + q) for p in range(a) for q in range(a) if not Y.has_edge(p, a + q)]
    rng.shuffle(allpairs)
    extra = rng.randrange(1, 7)
    for (p, q) in allpairs:
        if extra == 0: break
        if Y.degree(p) < 6 and Y.degree(q) < 6:
            Y.add_edge(p, q); extra -= 1
    I = Inst(Y, set(range(a)))
    if I.four_factor() is None: continue
    ninst += 1
    Fs = all_four_factors(I) if n <= 16 else None
    # excluded edges
    Ex = set()
    for e in I.pq:
        cost = {f: (0 if f == e else 1) for f in I.pq}
        F = I.four_factor({f: (-1 if f == e else 0) for f in I.pq})
        if e not in F: Ex.add(e)
    if Fs is not None:
        allF = set().union(*Fs)
        assert Ex == set(I.pq) - allF, "Ex mismatch"
    # all subsets S: s(S) and ∂_P(S)
    V = list(range(n))
    sets_s1 = []
    for mask in range(1, (1 << n) - 1):
        S = frozenset(v for v in V if mask >> v & 1)
        if I.s(S) == 1:
            sets_s1.append(frozenset(I.E1(S)))   # ∂_P(S) = E(S_P, Q - S) as (p,q)
    # identity check with a random F
    F = I.random_four_factor(rng)
    for _ in range(200):
        S = frozenset(v for v in V if rng.random() < 0.5)
        eH = sum(1 for (p, q) in I.pq if (p, q) not in F and q in S and p not in S)
        eF = sum(1 for (p, q) in F if p in S and q not in S)
        assert I.s(S) == eH + eF
    for r in range(1, a):
        for TP in itertools.combinations(range(a), r):
            for TQ in itertools.combinations(range(a, n), r):
                T = frozenset(TP) | frozenset(TQ)
                E0 = I.E0(T)
                mx, _ = I.max_in(E0)
                if Fs is not None:
                    bf = max(len(f & set(E0)) for f in Fs)
                    assert bf == mx, "max mismatch"
                rig = mx <= 1
                rest = set(E0) - Ex
                crit = len(rest) <= 1 or any(rest <= d for d in sets_s1)
                nchk += 1; nrig += rig
                if rig != crit:
                    mism += 1; print('MISMATCH', to_g6(Y), sorted(T), mx, file=sys.stderr)
print('instances', ninst, 'balanced T checked', nchk, 'rigid', nrig, 'mismatches', mism)
