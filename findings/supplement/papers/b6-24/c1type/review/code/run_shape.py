#!/usr/bin/env python3
"""Driver: run_shape.py <shape> <mode> [options]
shape: n19k44 | n21k44 | n21_55 | n23_55 | n23k44
mode:  enum (F[B] = each genbg class) | free (F[B] variables)
options: nostar  (control: drop (star))
         qfree   (replace F2 by Q H-degree <= 2 and total deficiency d)
         levels=a,b,c  (override the proof-faithful B-side levels)
         workers=N, solver=NAME, limit=SECONDS, sides=i,j (subset of A-side indices), degw=4|5
Prints one line per model and a summary; SAT models are re-checked by check_config.
"""
import multiprocessing as mp
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import c1ref  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
SHAPES = {
    # name: (A side kind, b, proof-faithful levels)
    'n19k44': ('k44', 5, ()),
    'n21k44': ('k44', 6, ('k44w', 'c55')),
    'n21_55': ('55', 5, ('eHB2',)),
    'n23_55': ('55', 6, ('k44w', 'r12')),
    'n23k44': ('k44', 7, ('k44w', 'r12')),
}


def load_fb(b):
    path = os.path.join(HERE, 'fb%d.g6' % b)
    with open(path) as fh:
        return [c1ref.fb_from_genbg(line, b) for line in fh if line.strip()]


def job(args):
    shape, side_idx, fb_idx, degw, opts = args
    kind, b, levels = SHAPES[shape]
    if opts.get('levels') is not None:
        levels = opts['levels']
    sides = [c1ref.side_k44()] if kind == 'k44' else c1ref.sides_55()
    side = sides[side_idx]
    FB = None
    if fb_idx is not None:
        FB = load_fb(b)[fb_idx]
    m = c1ref.Model(side, b, degw, FB=FB, star=opts['star'], f2=opts['f2'], levels=levels,
                    solver=opts['solver'])
    res, cfg, iters, dt = m.solve(time_limit=opts['limit'])
    chk = None
    if res:
        chk = c1ref.check_config(cfg, degw, f2=opts['f2'])
        chk['k44w'] = c1ref.k44_in_Xbw(cfg)
    return (shape, side_idx, side['name'], fb_idx, degw, res, iters, m.cuts, round(dt, 2), chk)


def main():
    shape, mode = sys.argv[1], sys.argv[2]
    opts = dict(star=True, f2=True, levels=None, workers=6, solver='cadical195', limit=None,
                sides=None, degw=(4, 5))
    for a in sys.argv[3:]:
        if a == 'nostar':
            opts['star'] = False
        elif a == 'qfree':
            opts['f2'] = False
        elif a.startswith('levels='):
            v = a.split('=', 1)[1]
            opts['levels'] = tuple(x for x in v.split(',') if x)
        elif a.startswith('workers='):
            opts['workers'] = int(a.split('=')[1])
        elif a.startswith('solver='):
            opts['solver'] = a.split('=')[1]
        elif a.startswith('limit='):
            opts['limit'] = float(a.split('=')[1])
        elif a.startswith('sides='):
            opts['sides'] = [int(x) for x in a.split('=')[1].split(',')]
        elif a.startswith('degw='):
            opts['degw'] = tuple(int(x) for x in a.split('=')[1].split(','))
        else:
            raise SystemExit('bad option ' + a)
    kind, b, levels = SHAPES[shape]
    nsides = 1 if kind == 'k44' else 44
    side_list = opts['sides'] if opts['sides'] is not None else list(range(nsides))
    fb_list = [None] if mode == 'free' else list(range(len(load_fb(b))))
    jobs = [(shape, si, fi, dw, opts) for si in side_list for fi in fb_list for dw in opts['degw']]
    print('# shape=%s mode=%s star=%s f2=%s levels=%s solver=%s jobs=%d' % (
        shape, mode, opts['star'], opts['f2'], opts['levels'] if opts['levels'] is not None else levels,
        opts['solver'], len(jobs)), flush=True)
    t0 = time.time()
    cnt = {True: 0, False: 0, None: 0}
    onecross_sat = 0
    with mp.Pool(opts['workers']) as pool:
        for r in pool.imap_unordered(job, jobs):
            cnt[r[5]] += 1
            if r[5] and r[9]['onecross']:
                onecross_sat += 1
            print(' '.join(str(x) for x in r), flush=True)
    print('# SUMMARY shape=%s mode=%s star=%s f2=%s: UNSAT %d SAT %d UNKNOWN %d (SAT with one-crossing %d) '
          'wall %.1f s' % (shape, mode, opts['star'], opts['f2'], cnt[False], cnt[True], cnt[None],
                           onecross_sat, time.time() - t0), flush=True)


if __name__ == '__main__':
    main()
