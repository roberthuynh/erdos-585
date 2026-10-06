"""SAT search for a block that violates KL1 (referee 3, own encoding).

Block: A = 0..nA-1, C = 0..nC-1 (nC = nA - 2), x[a][c] adjacency, every c of degree 6, every a of
in-block degree d_a in 3..6.  Cut vector c_a with max(0, delta_a - 2) <= c_a <= min(3, delta_a),
sum 7; multiset m <= c, sum 4, m_a >= 1 whenever d_a = 3 (M covers L_A).
Failure: s sets A1_1..A1_s (membership vars), each under-supplied:
    sum_c min(4, e(c, A1_i)) + m(A1_i) <= 4|A1_i| - 1,
and every a has m_a >= 1 or lies outside some A1_i.  Then I_X(m) = empty.
Block sparsity (e(S) <= 3|S| - 6 for proper S, |S| >= 3) is added lazily, per violating S_A, as
sum_c max(0, e(c, S_A) - 3) <= 3|S_A| - 6.
Every model that passes sparsity is re-checked exactly (I_X(m) by enumeration of all subsets).

usage: kl1sat.py nA s [max_iters] [solver] [extra]
  extra: comma list of options:  noK44 (forbid K_{4,4} in the block), seed=N (random phases)
"""
import sys
import time
import random
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

nA = int(sys.argv[1])
s = int(sys.argv[2])
max_iters = int(sys.argv[3]) if len(sys.argv) > 3 else 2000
solver_name = sys.argv[4] if len(sys.argv) > 4 else 'cadical195'
extra = sys.argv[5].split(',') if len(sys.argv) > 5 else []
opts = {}
for e in extra:
    if '=' in e:
        k, v = e.split('=')
        opts[k] = v
    elif e:
        opts[e] = True
nC = nA - 2
pool = IDPool()
clauses = []


def V(*name):
    return pool.id(name)


def add(cl):
    clauses.append(cl)


# ---------------- variables ----------------
x = [[V('x', a, c) for c in range(nC)] for a in range(nA)]
y = [[V('y', i, a) for a in range(nA)] for i in range(s)]
cu = [[V('cu', a, t) for t in range(1, 4)] for a in range(nA)]   # c_a >= t
mu = [[V('mu', a, t) for t in range(1, 4)] for a in range(nA)]   # m_a >= t


def tot_lits(lits, K, tag):
    """outputs u[1..min(K, n)] with u[j] <-> (sum lits >= j) for j < len, and u[last] <-> sum >= last."""
    nodes = [([l], True) for l in lits]
    cnt = 0
    while len(nodes) > 1:
        new = []
        for i in range(0, len(nodes), 2):
            if i + 1 == len(nodes):
                new.append(nodes[i])
                continue
            (a, ea), (b, eb) = nodes[i], nodes[i + 1]
            p, q = len(a), len(b)
            r = min(p + q, K)
            cnt += 1
            c = [V('tot', tag, cnt, j) for j in range(1, r + 1)]
            for ii in range(0, p + 1):
                for jj in range(0, q + 1):
                    t = ii + jj
                    if t == 0:
                        continue
                    t = min(t, r)
                    cl = []
                    if ii > 0:
                        cl.append(-a[ii - 1])
                    if jj > 0:
                        cl.append(-b[jj - 1])
                    cl.append(c[t - 1])
                    add(cl)
            for ii in range(0, p + 1):
                for jj in range(0, q + 1):
                    t = ii + jj + 1
                    if t > r:
                        continue
                    cl = []
                    if ii < p:
                        cl.append(a[ii])
                    elif not ea:
                        continue
                    if jj < q:
                        cl.append(b[jj])
                    elif not eb:
                        continue
                    cl.append(-c[t - 1])
                    add(cl)
            new.append((c, ea and eb and (p + q <= K)))
        nodes = new
    return nodes[0][0]


def card(lits, bound, kind):
    if kind == 'atmost':
        enc = CardEnc.atmost(lits=lits, bound=bound, vpool=pool, encoding=EncType.totalizer)
    elif kind == 'atleast':
        enc = CardEnc.atleast(lits=lits, bound=bound, vpool=pool, encoding=EncType.totalizer)
    else:
        enc = CardEnc.equals(lits=lits, bound=bound, vpool=pool, encoding=EncType.totalizer)
    for cl in enc.clauses:
        add(cl)


# C degrees = 6
for c in range(nC):
    card([x[a][c] for a in range(nA)], 6, 'equals')
# A degrees, unary D[a][t] <-> d_a >= t (t = 1..7)
D = []
for a in range(nA):
    out = tot_lits([x[a][c] for c in range(nC)], 7, ('deg', a))
    D.append(out)
    add([out[2]])           # d_a >= 3
    if len(out) >= 7:
        add([-out[6]])      # d_a <= 6
# unary c, m
for a in range(nA):
    for t in range(2):
        add([-cu[a][t + 1], cu[a][t]])
        add([-mu[a][t + 1], mu[a][t]])
    for t in range(3):
        add([-mu[a][t], cu[a][t]])          # m <= c
    # c_a <= delta_a = 6 - d_a : c >= t -> d <= 6 - t -> not D[7-t]
    for t in range(1, 4):
        add([-cu[a][t - 1], -D[a][7 - t - 1]])
    # c_a >= delta_a - 2 = 4 - d_a: d_a = 3 (not D>=4) -> c >= 1
    add([D[a][3], cu[a][0]])
    # covering: d_a = 3 -> m_a >= 1 (in caseb mode vertex 0 is the one uncovered L-vertex)
    if opts.get('caseb') and a == 0:
        add([-D[a][3]])
        add([-mu[a][0]])
    else:
        add([D[a][3], mu[a][0]])
card([cu[a][t] for a in range(nA) for t in range(3)], 7, 'equals')
card([mu[a][t] for a in range(nA) for t in range(3)], 4, 'equals')
# failure: every a has m_a >= 1 or is outside some A1_i
if opts.get('caseb'):
    add([-y[0][0]])
else:
    for a in range(nA):
        add([mu[a][0]] + [-y[i][a] for i in range(s)])
# each A1_i under-supplied
for i in range(s):
    card([y[i][a] for a in range(nA)], 5, 'atleast')
    card([-y[i][a] for a in range(nA)], 3, 'atleast')
    lits = []
    for c in range(nC):
        zs = []
        for a in range(nA):
            z = V('z', i, a, c)
            add([-z, x[a][c]])
            add([-z, y[i][a]])
            add([z, -x[a][c], -y[i][a]])
            zs.append(z)
        o = tot_lits(zs, 4, ('min4', i, c))
        lits += o
    for a in range(nA):
        for t in range(3):
            p = V('my', i, a, t)
            add([-mu[a][t], -y[i][a], p])
            lits.append(p)
        for r in range(4):
            q = V('ny', i, a, r)
            add([y[i][a], q])
            lits.append(q)
    card(lits, 4 * nA - 1, 'atmost')
# symmetry breaking (light): sets ordered by first member index is hard; break C symmetry by ordering
# neighborhood codes lexicographically is expensive; we only order the s sets by |A1_i| (non-increasing).
for i in range(s - 1):
    # |A1_i| >= |A1_{i+1}|  <=>  sum y_i + sum not y_{i+1} >= nA
    card([y[i][a] for a in range(nA)] + [-y[i + 1][a] for a in range(nA)], nA, 'atleast')

if opts.get('noK44'):
    pass  # handled lazily below

solver = Solver(name=solver_name, bootstrap_with=clauses)
nbase = len(clauses)
clauses = []
rng = random.Random(int(opts.get('seed', 0)))
if 'seed' in opts:
    try:
        solver.set_phases([v if rng.random() < 0.5 else -v for v in range(1, pool.top + 1)])
    except Exception:
        pass

print(f'nA={nA} nC={nC} s={s} vars={pool.top} clauses={nbase}', flush=True)


def check_sparse(cm):
    """return list of violating S_A masks (proper, |S_A|>=4) with excess > 0, worst first (at most 6)."""
    full = (1 << nA) - 1
    viol = []
    for S in range(full):
        k = S.bit_count()
        if k < 4:
            continue
        ex = 0
        for m in cm:
            e = (m & S).bit_count()
            if e > 3:
                ex += e - 3
        if ex > 3 * k - 6:
            viol.append((ex - (3 * k - 6), -k, S))
    viol.sort(reverse=True)
    return [v[2] for v in viol[:6]]


def k44(cm):
    # any 4 C-vertices with >= 4 common neighbours
    from itertools import combinations
    for q in combinations(range(nC), 4):
        common = cm[q[0]] & cm[q[1]] & cm[q[2]] & cm[q[3]]
        if common.bit_count() >= 4:
            return q, common
    return None


def exact_I(cm, mv):
    full = (1 << nA) - 1
    I = full
    for A1 in range(1, full + 1):
        s4 = 0
        for m in cm:
            e = (m & A1).bit_count()
            s4 += 4 if e > 4 else e
        dem = 4 * A1.bit_count() - s4
        mm = sum(mv[a] for a in range(nA) if A1 >> a & 1)
        if mm < dem:
            I &= A1
    return I


t0 = time.time()
it = 0
added = 0
while it < max_iters:
    it += 1
    ok = solver.solve()
    if not ok:
        print(f'UNSAT after {it} iterations, {added} lazy constraints, {time.time() - t0:.1f}s', flush=True)
        break
    model = set(l for l in solver.get_model() if l > 0)
    cm = []
    for c in range(nC):
        m = 0
        for a in range(nA):
            if x[a][c] in model:
                m |= 1 << a
        cm.append(m)
    viol = check_sparse(cm)
    if not viol and opts.get('noK44'):
        kk = k44(cm)
        if kk:
            q, common = kk
            cols = [a for a in range(nA) if common >> a & 1][:4]
            solver.add_clause([-x[a][c] for a in cols for c in q])
            added += 1
            continue
    if viol:
        for S in viol:
            members = [a for a in range(nA) if S >> a & 1]
            k = len(members)
            lits = []
            for c in range(nC):
                o = tot_lits([x[a][c] for a in members], 6, ('sp', S, c))
                lits += o[3:6]
            enc = CardEnc.atmost(lits=lits, bound=3 * k - 6, vpool=pool, encoding=EncType.totalizer)
            for cl in clauses:
                solver.add_clause(cl)
            clauses = []
            for cl in enc.clauses:
                solver.add_clause(cl)
            added += 1
        if it % 10 == 0 or it <= 3:
            print(f'  it {it}: lazy {added}, {time.time() - t0:.1f}s', flush=True)
        continue
    mv = [sum(1 for t in range(3) if mu[a][t] in model) for a in range(nA)]
    cv = [sum(1 for t in range(3) if cu[a][t] in model) for a in range(nA)]
    I = exact_I(cm, mv)
    print(f'MODEL it={it} sparse; exact I_X = {bin(I)}; m={mv} c={cv}', flush=True)
    print('BLOCK', nA, nC, ' '.join(map(str, cm)), ' '.join(map(str, cv)), flush=True)
    if opts.get('caseb'):
        print('caseb check: I_X empty' if I == 0 else 'caseb mismatch', flush=True)
    elif I == 0:
        print('KL1 COUNTEREXAMPLE (block level)', flush=True)
    else:
        print('encoding mismatch?!', flush=True)
    break
else:
    print(f'stopped after {max_iters} iterations, lazy {added}, {time.time() - t0:.1f}s', flush=True)
