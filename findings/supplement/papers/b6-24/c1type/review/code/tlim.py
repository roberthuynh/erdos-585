import sys, time, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import c1ref, run_shape
fbs = run_shape.load_fb(7)
side = c1ref.side_k44()
for idx in [0, 50, 100, 150, 207]:
    for dw in (4, 5):
        m = c1ref.Model(side, 7, dw, FB=fbs[idx], star=True, f2=True, levels=('k44w', 'r12'))
        r = m.solve(time_limit=100)
        print(idx, dw, r[0], r[2], m.cuts, round(r[3], 2), flush=True)
