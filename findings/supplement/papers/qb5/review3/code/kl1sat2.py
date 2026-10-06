"""SAT search for a block violating KL1, version 2 (referee 3, own encoding).

Same model as kl1sat.py, plus:
  anchors : minimal core family WLOG -> vertex i-1 (i = 1..s) lies in every A1_j (j != i), not in A1_i,
            and has m = 0;
  symsp   : sparsity constraints sum_c (e(c,S)-3)^+ <= 3|S|-6 for the symbolic sets
            S in {A1_i, T_i, A1_i - x (all x), A1_i u A1_j, T_i u T_j}  (all have |S| >= 2);
  lazy    : block sparsity for the remaining sets, per violating S_A (up to `lazyk` per round).
  noK44   : forbid K_{4,4} (lazily).
Every sparse model is re-checked exactly (I_X(m) by enumerating all subsets of A).

usage: kl1sat2.py nA s maxiters [opts]   opts: comma list among anchors,symsp,noK44,lazyk=N,solver=NAME,
       tlimit=SECONDS
"""
import sys
import time
from itertools import combinations
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

nA = int(sys.argv[1])
s = int(sys.argv[2])
max_iters = int(sys.argv[3])
opts = {}
if len(sys.argv) > 4:
    for e in sys.argv[4].split(','):
        if '=' in e:
            k, v = e.split('=')
            opts[k] = v
        elif e:
            opts[e] = True
nC = nA - 2
lazyk = int(opts.get('lazyk', 12))
tlimit = float(opts.get('tlimit', 1e9))
pool = IDPool()
buf = []


def V(*name):
    return pool.id(name)


def add(cl):
    buf.append(cl)


def tot(lits, K, tag):
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
            for ii in range(p + 1):
                for jj in range(q + 1):
                    t = ii + jj
                    if t == 0:
                        continue
                    t = min(t, r)
                    cl = [c[t - 1]]
                    if ii > 0:
                        cl.append(-a[ii - 1])
                    if jj > 0:
                        cl.append(-b[jj - 1])
                    add(cl)
            for ii in range(p + 1):
                for jj in range(q + 1):
                    t = ii + jj + 1
                    if t > r:
                        continue
                    cl = [-c[t - 1]]
                    if ii < p:
                        cl.append(a[ii])
                    elif not ea:
                        continue
                    if jj < q:
                        cl.append(b[jj])
                    elif not eb:
                        continue
                    add(cl)
            new.append((c, ea and eb and (p + q <= K)))
        nodes = new
    return nodes[0][0] if nodes else []


def card(lits, bound, kind):
    f = {'atmost': CardEnc.atmost, 'atleast': CardEnc.atleast, 'equals': CardEnc.equals}[kind]
    enc = f(lits=lits, bound=bound, vpool=pool, encoding=EncType.totalizer)
    for cl in enc.clauses:
        add(cl)


x = [[V('x', a, c) for c in range(nC)] for a in range(nA)]
y = [[V('y', i, a) for a in range(nA)] for i in range(s)]
cu = [[V('cu', a, t) for t in range(3)] for a in range(nA)]
mu = [[V('mu', a, t) for t in range(3)] for a in range(nA)]

for c in range(nC):
    card([x[a][c] for a in range(nA)], 6, 'equals')
D = []
for a in range(nA):
    o = tot([x[a][c] for c in range(nC)], 7, ('deg', a))
    D.append(o)
    add([o[2]])
    if len(o) >= 7:
        add([-o[6]])
for a in range(nA):
    for t in range(2):
        add([-cu[a][t + 1], cu[a][t]])
        add([-mu[a][t + 1], mu[a][t]])
    for t in range(3):
        add([-mu[a][t], cu[a][t]])
    for t in range(1, 4):
        add([-cu[a][t - 1], -D[a][7 - t - 1]])     # c <= delta
    add([D[a][3], cu[a][0]])                       # d = 3 -> c >= 1
    add([D[a][3], mu[a][0]])                       # covering L_A
card([cu[a][t] for a in range(nA) for t in range(3)], 7, 'equals')
card([mu[a][t] for a in range(nA) for t in range(3)], 4, 'equals')
for a in range(nA):
    add([mu[a][0]] + [-y[i][a] for i in range(s)])
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
        lits += tot(zs, 4, ('min4', i, c))
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

if opts.get('anchors'):
    for i in range(s):
        for j in range(s):
            add([-y[j][i]] if j == i else [y[j][i]])
        add([-mu[i][0]])

nsym = 0


def sym_sparsity(mem, tag):
    """mem[a]: literal, True or False. Adds sum_c (e(c,S)-3)^+ + 3*#(a notin S) <= 3nA - 6."""
    global nsym
    nsym += 1
    lits = []
    for c in range(nC):
        ins = []
        for a in range(nA):
            if mem[a] is True:
                ins.append(x[a][c])
            elif mem[a] is False:
                continue
            else:
                z = V('sz', tag, a, c)
                add([-z, x[a][c]])
                add([-z, mem[a]])
                add([z, -x[a][c], -mem[a]])
                ins.append(z)
        if len(ins) >= 4:
            o = tot(ins, 6, ('sp', tag, c))
            lits += o[3:6]
    const = 0
    for a in range(nA):
        if mem[a] is False:
            const += 3
        elif mem[a] is True:
            continue
        else:
            for r in range(3):
                q = V('sq', tag, a, r)
                add([mem[a], q])
                lits.append(q)
    bound = 3 * nA - 6 - const
    if bound < 0:
        add([])
        return
    card(lits, bound, 'atmost')


def OR(l1, l2, tag):
    v = V('or', tag)
    add([-v, l1, l2])
    add([v, -l1])
    add([v, -l2])
    return v


def AND(l1, l2, tag):
    v = V('and', tag)
    add([v, -l1, -l2])
    add([-v, l1])
    add([-v, l2])
    return v


if opts.get('symsp'):
    for i in range(s):
        sym_sparsity([y[i][a] for a in range(nA)], ('A1', i))
        sym_sparsity([-y[i][a] for a in range(nA)], ('T', i))
        for xx in range(nA):
            sym_sparsity([False if a == xx else y[i][a] for a in range(nA)], ('A1x', i, xx))
    for i, j in combinations(range(s), 2):
        sym_sparsity([OR(y[i][a], y[j][a], ('u', i, j, a)) for a in range(nA)], ('A1u', i, j))
        sym_sparsity([OR(-y[i][a], -y[j][a], ('tu', i, j, a)) for a in range(nA)], ('Tu', i, j))

solver = Solver(name=opts.get('solver', 'cadical195'), bootstrap_with=buf)
print(f'nA={nA} nC={nC} s={s} opts={opts} vars={pool.top} clauses={len(buf)} symsets={nsym}', flush=True)
buf = []


def violations(cm):
    full = (1 << nA) - 1
    out = []
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
            out.append((ex - (3 * k - 6), -k, S))
    out.sort(reverse=True)
    return [v[2] for v in out[:lazyk]]


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
added = 0
it = 0
status = 'iterlimit'
while it < max_iters and time.time() - t0 < tlimit:
    it += 1
    ts = time.time()
    if not solver.solve():
        status = 'UNSAT'
        break
    model = set(l for l in solver.get_model() if l > 0)
    cm = []
    for c in range(nC):
        m = 0
        for a in range(nA):
            if x[a][c] in model:
                m |= 1 << a
        cm.append(m)
    viol = violations(cm)
    if not viol and opts.get('noK44'):
        bad = None
        for q in combinations(range(nC), 4):
            common = cm[q[0]] & cm[q[1]] & cm[q[2]] & cm[q[3]]
            if common.bit_count() >= 4:
                bad = (q, [a for a in range(nA) if common >> a & 1][:4])
                break
        if bad:
            q, cols = bad
            solver.add_clause([-x[a][c] for a in cols for c in q])
            added += 1
            continue
    if viol:
        for S in viol:
            mem = [bool(S >> a & 1) for a in range(nA)]
            sym_sparsity(mem, ('lazy', S))
        for cl in buf:
            solver.add_clause(cl)
        buf = []
        added += len(viol)
        if it <= 3 or it % 20 == 0:
            print(f'  it {it}: lazy {added}, solve {time.time() - ts:.1f}s, total {time.time() - t0:.1f}s', flush=True)
        continue
    mv = [sum(1 for t in range(3) if mu[a][t] in model) for a in range(nA)]
    cv = [sum(1 for t in range(3) if cu[a][t] in model) for a in range(nA)]
    I = exact_I(cm, mv)
    print(f'MODEL it={it}: block-sparse, exact I_X = {bin(I)}, m={mv}, c={cv}', flush=True)
    print('BLOCK', nA, nC, ' '.join(map(str, cm)), ' '.join(map(str, cv)), flush=True)
    print('KL1 COUNTEREXAMPLE (block level)' if I == 0 else 'ENCODING MISMATCH', flush=True)
    status = 'FOUND'
    break
print(f'STATUS {status} iterations={it} lazy={added} time={time.time() - t0:.1f}s', flush=True)
