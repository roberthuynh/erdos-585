"""Small helpers for the c1type lane: graph6 output and the exact pair test (pairc, via files)."""
import os, subprocess, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
PAIRC = os.path.normpath(os.path.join(HERE, '../../../../585-fable/tools/pairc'))
GENBG = os.path.expanduser('~/.cache/erdos585/nauty2_9_3/genbg')


def to_g6(nv, edges):
    """graph6 string of a simple graph on vertices 0..nv-1."""
    bits = []
    adj = set()
    for (a, b) in edges:
        if a == b:
            raise ValueError('loop')
        adj.add((min(a, b), max(a, b)))
    for j in range(1, nv):
        for i in range(j):
            bits.append(1 if (i, j) in adj else 0)
    while len(bits) % 6:
        bits.append(0)
    out = [chr(63 + nv)] if nv <= 62 else None
    for k in range(0, len(bits), 6):
        v = 0
        for t in range(6):
            v = (v << 1) | bits[k + t]
        out.append(chr(63 + v))
    return ''.join(out)


def has_pair_many(graphs, workdir=None):
    """graphs: list of (nv, edges). Returns list of bools (True = has a pair), using pairc mode p.
    graph6 strings are passed through a file, never on a command line."""
    lines = [to_g6(nv, ed) for (nv, ed) in graphs]
    d = workdir or tempfile.mkdtemp(prefix='c1pair_')
    fin = os.path.join(d, 'in.g6')
    with open(fin, 'w') as fh:
        fh.write('\n'.join(lines) + '\n')
    with open(fin) as fh:
        res = subprocess.run([PAIRC, 'p'], stdin=fh, capture_output=True, text=True, timeout=240)
    withpair = set(res.stdout.split())
    return [ln in withpair for ln in lines]
