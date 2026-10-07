"""Encoding test for lemmaB_sat.py: in the relaxed model (no H-edge count, at least one E0H and one E1H
edge) the no-one-crossing clauses are satisfiable; decode such a model and confirm with plain BFS on the
decoded digraph D^- (networkx-free) that it really has no one-crossing cycle, i.e. that the SAT encoding
of (*) means what it should."""
import lemmaB_sat as L

def check(n, sp, bP, label, k=1):
    r, model, (u, w, f, h) = L.build_and_solve(n, sp, bP, relaxed=k)
    if not r:
        print(label, 'k =', k, 'relaxed model UNSAT (no test)'); return
    m = set(l for l in model if l > 0)
    aP, aQ, FA, HA = sp
    # vertices: ('AP',i), ('AQ',i), ('BP',i), ('BQ',i); arcs of D^- : F P->Q, H Q->P, inside sides and E0H/E1H
    arcs = []
    for (p, q) in FA: arcs.append((('AP', p), ('AQ', q)))
    for (p, q) in HA: arcs.append((('AQ', q), ('AP', p)))
    for (p, q), v in f.items():
        if v in m: arcs.append((('BP', p), ('BQ', q)))
    for (p, q), v in h.items():
        if v in m: arcs.append((('BQ', q), ('BP', p)))
    E0 = [(y, xp) for (y, xp), v in u.items() if v in m]
    E1 = [(x, yp) for (x, yp), v in w.items() if v in m]
    def reach(src, side):
        seen = {src}; st = [src]
        while st:
            a = st.pop()
            for (s1, t1) in arcs:
                if s1 == a and t1[0][0] == side and t1 not in seen:
                    seen.add(t1); st.append(t1)
        return seen
    found = 0
    for (y, xp) in E0:
        RB = reach(('BP', xp), 'B')
        for (x, yp) in E1:
            RA = reach(('AP', x), 'A')
            if ('BQ', yp) in RB and ('AQ', y) in RA:
                found += 1
    print(label, 'k =', k, 'relaxed model SAT: |E0H| =', len(E0), '|E1H| =', len(E1),
          'one-crossing pairs found by BFS:', found, '(must be 0)')

for k in (1, 3, 5):
    for name, sp in L.specs_55():
        check(22, sp, 6, 'n=22 5+5|6+6 ' + name, k); break
    _, k44 = L.spec_k44()
    check(20, k44, 6, 'n=20 K44|6+6', k)
    check(22, k44, 7, 'n=22 K44|7+7', k)
    for name, sp in L.specs_55():
        check(20, sp, 5, 'n=20 5+5|5+5 ' + name, k); break
