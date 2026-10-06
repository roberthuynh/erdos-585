import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import c1ref, run_shape
fbs = run_shape.load_fb(7)
side = c1ref.side_k44()
for idx in (0, 50, 207):
    for dw in (4, 5):
        m = c1ref.Model(side, 7, dw, FB=fbs[idx], star=True, f2=True, levels=('symA',))
        r = m.solve()
        print('no B-side facts: class', idx, 'deg w', dw, 'SAT' if r[0] else 'UNSAT', round(r[3], 1), flush=True)
        if r[0]:
            print('   ', c1ref.check_config(r[1], dw), 'K44 in X[B+w]:', c1ref.k44_in_Xbw(r[1]))
