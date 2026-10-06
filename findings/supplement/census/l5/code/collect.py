#!/usr/bin/env python3
"""L5B collector: checks every shard, sums counts by stage and side split, reconciles with the
original census (SCOUT.md section 2.4, genbg colour-preserving counts), and checks that the generated
graphs are pairwise distinct (graph6 strings) and pairwise non-isomorphic (labelg canonical forms).
Writes data/census/SUMMARY.json and prints Markdown tables.
"""
import glob
import gzip
import json
import os
import re
import subprocess
import sys

L5B = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
D = os.path.join(L5B, 'data', 'census')
LABELG = os.path.expanduser('~/.cache/erdos585/nauty2_9_3/labelg')

PLAN = {17: 64, 16: 8}
for _n in range(5, 16):
    PLAN[_n] = 1
# SCOUT.md section 2.4 (genbg, colour classes kept): side split -> graphs
ORIGINAL = {'4+5': 0, '5+5': 1, '5+6': 2, '6+6': 13, '6+7': 29, '7+7': 819, '7+8': 2895,
            '8+8': 229913, '8+9': 1237978}


def split_of(n):
    return '%d+%d' % (n // 2, n - n // 2)


def main():
    problems = []
    per_n = {}
    exceptions = []
    for n in sorted(PLAN):
        mod = PLAN[n]
        agg = {'shards_done': 0, 'geng': 0, 'read': 0, 'in_class': 0, 'rejected': 0, 'pair': 0,
               'pair_free': 0, 'P_ok': 0, 'P_bad': 0, 'F': 0, 'X': 0, 'class_ok': 0, 'connected': 0,
               'disconnected': 0, 'swap_auto': 0, 'swap_checked': 0, 'sides': {}, 'S_size': {},
               'sat_seconds': 0.0, 'wall_seconds': 0}
        for r in range(mod):
            base = os.path.join(D, 'n%d_m%d_r%d' % (n, mod, r))
            if not os.path.exists(base + '.done'):
                problems.append('missing shard n=%d %d/%d' % (n, r, mod))
                continue
            agg['shards_done'] += 1
            m = re.search(r'>Z (\d+) graphs generated', open(base + '.geng.err').read())
            g = int(m.group(1)) if m else -1
            if g < 0:
                problems.append('no geng count n=%d r=%d' % (n, r))
            sat = json.load(open(base + '.sat.json'))
            ver = json.load(open(base + '.verify.json'))
            agg['geng'] += g
            agg['read'] += sat['read']
            agg['in_class'] += sat['in_class']
            agg['rejected'] += sum(sat['rejected'].values())
            agg['pair'] += sat['pair']
            agg['pair_free'] += sat['pair_free']
            agg['sat_seconds'] += sat['seconds']
            for k, v in sat['S_size'].items():
                agg['S_size'][k] = agg['S_size'].get(k, 0) + v
            for k in ('P_ok', 'P_bad', 'F', 'X', 'class_ok', 'connected', 'disconnected',
                      'swap_auto', 'swap_checked'):
                agg[k] += ver[k]
            for k, v in ver['sides'].items():
                agg['sides'][k] = agg['sides'].get(k, 0) + v
            agg['wall_seconds'] += int(open(base + '.done').read().split('=')[1])
            if not (g == sat['read'] == ver['lines'] and sat['pair'] == ver['P_ok']
                    and sat['pair_free'] == ver['F'] and ver['P_bad'] == 0):
                problems.append('shard mismatch n=%d r=%d' % (n, r))
            exc = base + '.exc'
            if os.path.exists(exc) and os.path.getsize(exc) > 0:
                exceptions += open(exc).read().splitlines()
        if agg['shards_done'] != mod:
            problems.append('n=%d only %d of %d shards' % (n, agg['shards_done'], mod))
        cf = os.path.join(D, 'count_n%d.txt' % n)
        if os.path.exists(cf):
            m = re.search(r'>Z (\d+) graphs generated', open(cf).read())
            agg['unsplit_count'] = int(m.group(1))
            if agg['unsplit_count'] != agg['geng']:
                problems.append('n=%d unsplit %d != shard sum %d' % (n, agg['unsplit_count'], agg['geng']))
        per_n[n] = agg

    # distinctness: graph6 strings, then labelg canonical forms (nauty, used only for this check)
    for n in sorted(PLAN):
        mod = PLAN[n]
        files = [os.path.join(D, 'n%d_m%d_r%d.out.gz' % (n, mod, r)) for r in range(mod)]
        if not all(os.path.exists(f) for f in files):
            continue
        g6s = []
        for f in files:
            with gzip.open(f, 'rt') as fh:
                g6s += [line.split()[0] for line in fh if line.strip()]
        per_n[n]['distinct_g6'] = len(set(g6s))
        if not g6s:
            per_n[n]['distinct_canonical'] = 0
            continue
        tmp_in = os.path.join(D, 'tmp_all_n%d.g6' % n)
        tmp_out = os.path.join(D, 'tmp_canon_n%d.g6' % n)
        with open(tmp_in, 'w') as fh:
            fh.write('\n'.join(g6s) + '\n')
        subprocess.run([LABELG, '-q', tmp_in, tmp_out], check=True)
        with open(tmp_out) as fh:
            canon = [line.strip() for line in fh if line.strip()]
        per_n[n]['distinct_canonical'] = len(set(canon))
        if len(canon) != len(g6s):
            problems.append('labelg returned %d of %d graphs at n=%d' % (len(canon), len(g6s), n))
        os.remove(tmp_in)
        os.remove(tmp_out)

    recon = {}
    for n in sorted(PLAN):
        a = per_n[n]
        key = split_of(n)
        if n < 9:
            continue
        u = a['in_class']
        colour = u if n % 2 else 2 * u - a['swap_auto']
        recon[key] = {'n': n, 'uncoloured': u, 'swap_auto': a['swap_auto'] if n % 2 == 0 else None,
                      'colour_preserving': colour, 'original': ORIGINAL[key],
                      'match': colour == ORIGINAL[key], 'pair_free': a['pair_free']}
        if colour != ORIGINAL[key]:
            problems.append('count mismatch at %s: %d vs original %d' % (key, colour, ORIGINAL[key]))
        if a['disconnected'] or a['rejected'] or a['X'] or a['class_ok'] != a['in_class']:
            problems.append('class anomaly at n=%d' % n)
        if n % 2 == 0 and a['swap_checked'] != u:
            problems.append('swap check incomplete at n=%d' % n)

    total = {k: sum(per_n[n][k] for n in per_n) for k in
             ('geng', 'in_class', 'pair', 'pair_free', 'P_ok', 'P_bad', 'F', 'X', 'sat_seconds',
              'wall_seconds')}
    total['colour_preserving'] = sum(v['colour_preserving'] for v in recon.values())
    total['original'] = sum(ORIGINAL.values())
    out = {'per_n': {str(k): v for k, v in per_n.items()}, 'reconciliation': recon, 'total': total,
           'exceptions': exceptions, 'problems': problems}
    with open(os.path.join(D, 'SUMMARY.json'), 'w') as fh:
        json.dump(out, fh, indent=1, sort_keys=True)

    print('| n | split | geng (uncoloured) | unsplit geng -u | in class | pair (SAT) | certificates OK | '
          'pair-free | distinct canonical | side-swap autos | colour-preserving | original | match |')
    print('|---|---|---|---|---|---|---|---|---|---|---|---|---|')
    for n in sorted(per_n):
        a = per_n[n]
        rc = recon.get(split_of(n), {})
        print('| %d | %s | %d | %s | %d | %d | %d | %d | %s | %s | %s | %s | %s |' % (
            n, split_of(n), a['geng'], a.get('unsplit_count', '-'), a['in_class'], a['pair'],
            a['P_ok'], a['pair_free'], a.get('distinct_canonical', '-'),
            a['swap_auto'] if n % 2 == 0 and n >= 10 else '-',
            rc.get('colour_preserving', '-'), rc.get('original', '-'), rc.get('match', '-')))
    print()
    print('totals:', json.dumps(total, sort_keys=True))
    print('exceptions:', len(exceptions))
    print('problems:', problems if problems else 'none')
    return 1 if problems or exceptions else 0


if __name__ == '__main__':
    sys.exit(main())
