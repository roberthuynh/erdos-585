"""Refined covering model (lane qb5, round 3; NOTES.md section 7).

M-form: the pair statement holds iff some 4-set M of cut edges has I_X(M) and I_Y(M) nonempty.
Proved (NOTES 7.3): M is X-bad only if
  (a) two vertices of L_A miss M; or
  (b) exactly one vertex a of L_A misses M and some K in (A-ends of M) - a has def = 0 on K,
      every cut edge at K lies in M, and |E(K)| in {3, 4}   [rigid kappa = 0 core around a]; or
  (c) M covers L_A and the overloaded sets cover A           [excluded by Key Lemma KL1].
This script assumes KL1 and checks, over every 7-edge cut graph (genbg -d1:1 -D3:3 n1 n2 7:7) and every
admissible labelling (L_A contains the c = 3 ends, sum over L_A of (3 - c) <= 5; every other end is given
def = 0, the labelling most favourable to (b)), that some M avoids (a) and (b) on both sides.
Mode 'plain' drops (b) (then it is the M-form of Lemma 4.2).
Usage: refined_cover.py [plain] [nu3]
"""
import subprocess
import sys
from itertools import combinations

from generic_check import GENBG, decode, nu

PLAIN = 'plain' in sys.argv[1:]
NU3 = 'nu3' in sys.argv[1:]


def side_bad(M, ends, Lset, cutat):
    """M: frozenset of edge indices; ends: list of end vertices of this side; Lset: L vertices;
    cutat[v]: frozenset of edge indices at v.  Returns True if M is bad on this side via (a) or (b)."""
    VM = {v for v in ends if cutat[v] & M}
    miss = [v for v in Lset if v not in VM]
    if len(miss) >= 2:
        return True
    if len(miss) == 1 and not PLAIN:
        a = miss[0]
        cand = [v for v in VM if v != a and v not in Lset or (v != a and v in Lset and len(cutat[v]) == 3)]
        # def(v) = 0 for non-L ends by choice; an L end has def 0 iff c = 3
        cand = [v for v in VM if v != a and (v not in Lset or len(cutat[v]) == 3)]
        for r in range(1, len(cand) + 1):
            for K in combinations(cand, r):
                EK = frozenset().union(*(cutat[v] for v in K))
                if EK <= M and len(EK) in (3, 4):
                    return True
    return False


def main():
    total = 0
    fails = 0
    examples = []
    for n1 in range(1, 8):
        for n2 in range(1, 8):
            if 3 * n1 < 7 or 3 * n2 < 7:
                continue
            out = subprocess.run([GENBG, '-q', '-d1:1', '-D3:3', str(n1), str(n2), '7:7'],
                                 capture_output=True, text=True).stdout.split()
            for g in out:
                n, adj = decode(g)
                Av = list(range(n1)); Dv = list(range(n1, n1 + n2))
                edges = sorted((a, d) for a in Av for d in adj[a])
                if NU3 and nu(edges) != 3:
                    continue
                cutat = {v: frozenset(i for i, e in enumerate(edges) if v in e) for v in Av + Dv}
                c = {v: len(cutat[v]) for v in Av + Dv}
                Ms = [frozenset(M) for M in combinations(range(7), 4)]
                forcedA = [a for a in Av if c[a] == 3]; optA = [a for a in Av if c[a] < 3]
                forcedD = [d for d in Dv if c[d] == 3]; optD = [d for d in Dv if c[d] < 3]
                LAs = []
                for r in range(len(optA) + 1):
                    for xs in combinations(optA, r):
                        L = forcedA + list(xs)
                        if sum(3 - c[a] for a in L) <= 5:
                            LAs.append(L)
                LDs = []
                for r in range(len(optD) + 1):
                    for xs in combinations(optD, r):
                        L = forcedD + list(xs)
                        if sum(3 - c[d] for d in L) <= 5:
                            LDs.append(L)
                badA = {tuple(L): [side_bad(M, Av, set(L), cutat) for M in Ms] for L in LAs}
                badD = {tuple(L): [side_bad(M, Dv, set(L), cutat) for M in Ms] for L in LDs}
                for LA in LAs:
                    bA = badA[tuple(LA)]
                    for LD in LDs:
                        bD = badD[tuple(LD)]
                        total += 1
                        if all(x or y for x, y in zip(bA, bD)):
                            fails += 1
                            if len(examples) < 15:
                                examples.append((g, n1, n2, edges, LA, LD))
    print('mode', 'plain' if PLAIN else 'refined', 'nu3' if NU3 else 'all', 'labellings', total, 'no good M', fails)
    for ex in examples:
        print(ex)


if __name__ == '__main__':
    main()
