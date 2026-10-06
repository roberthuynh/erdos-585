/* blockkl.c (lane qb5, round 3; NOTES.md section 7).
 *
 * Block-level M-form.  Input lines: "na nc m_1 ... m_nc" where m_j is the bitmask over A = {0..na-1}
 * of the 6 neighbours of the j-th C-vertex (a 2-block: |A| = |C| + 2, C saturated into A).
 * For every multiset m on A with |m| = 4 and m(a) <= min(3, delta_a) that extends to an admissible
 * cut-degree vector (c_a in [max(0, delta_a - 2), min(3, delta_a)], sum c = 7), compute
 *     I(m) = AND of all S subset of A with dem(S) > m(S),   dem(S) = 4|S| - sum_c min(4, e(c, S)).
 * Key Lemma (i) [KL1]: if m(a) >= 1 for every a with d_a = 3 (m covers L_A), then I(m) != 0.
 * Also reports sparsity (g(S) >= 12 inside the block) and min degree.
 * Output per line: sparse flag, |L_A|, #admissible m, #covering m, #covering m with I = 0,
 * min |I(m)| over covering m, #m (any) with I = 0.
 * Usage: blockkl [v] < blocks.txt     (v: print every failing m)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXA 16
static int na, nc;
static unsigned cm[MAXA];
static int dem[1 << MAXA];
static unsigned char popc[1 << MAXA];

static int sparse_ok(int *din) {
    /* d_a >= 3 and for every S_C with 2 <= |S_C| <= nc - 1:
       sum_a (e(a,S_C) - 3)^+ - 3|S_C| <= -6 */
    for (int a = 0; a < na; a++) if (din[a] < 3 || din[a] > 6) return 0;
    for (unsigned s = 1; s < (1u << nc) - 1; s++) {
        int k = __builtin_popcount(s);
        if (k < 2) continue;
        int val = -3 * k;
        for (int a = 0; a < na; a++) {
            int e = 0;
            for (int j = 0; j < nc; j++) if ((s >> j & 1) && (cm[j] >> a & 1)) e++;
            if (e > 3) val += e - 3;
        }
        if (val > -6) return 0;
    }
    return 1;
}

int main(int argc, char **argv) {
    int verbose = argc > 1 && argv[1][0] == 'v';
    for (unsigned s = 0; s < (1u << MAXA); s++) popc[s] = (unsigned char)__builtin_popcount(s);
    char line[4096];
    while (fgets(line, sizeof line, stdin)) {
        char *p = line;
        int off;
        if (sscanf(p, "%d %d%n", &na, &nc, &off) != 2) continue;
        p += off;
        for (int j = 0; j < nc; j++) { sscanf(p, "%u%n", &cm[j], &off); p += off; }
        int din[MAXA] = {0};
        for (int j = 0; j < nc; j++) for (int a = 0; a < na; a++) if (cm[j] >> a & 1) din[a]++;
        int sp = sparse_ok(din);
        unsigned full = (1u << na) - 1;
        for (unsigned S = 0; S <= full; S++) {
            int t = 4 * popc[S];
            for (int j = 0; j < nc; j++) { int e = popc[cm[j] & S]; t -= e < 4 ? e : 4; }
            dem[S] = t;
        }
        int hi[MAXA], lo[MAXA], nL = 0; unsigned Lmask = 0;
        int sumlo = 0, sumhi = 0;
        for (int a = 0; a < na; a++) {
            int dl = 6 - din[a];
            hi[a] = dl < 3 ? dl : 3; lo[a] = dl - 2 > 0 ? dl - 2 : 0;
            sumlo += lo[a]; sumhi += hi[a];
            if (din[a] == 3) { nL++; Lmask |= 1u << a; }
        }
        long nadm = 0, ncov = 0, ncovfail = 0, nanyfail = 0; int minI = 99;
        if (sumlo <= 7 && sumhi >= 7) {
            /* enumerate multisets m with sum 4 */
            int m[MAXA];
            for (int i0 = 0; i0 < na; i0++) for (int i1 = i0; i1 < na; i1++)
            for (int i2 = i1; i2 < na; i2++) for (int i3 = i2; i3 < na; i3++) {
                memset(m, 0, sizeof m);
                m[i0]++; m[i1]++; m[i2]++; m[i3]++;
                int ok = 1, need = 0;
                for (int a = 0; a < na; a++) {
                    if (m[a] > hi[a]) { ok = 0; break; }
                    need += m[a] > lo[a] ? m[a] : lo[a];
                }
                if (!ok || need > 7) continue;
                nadm++;
                unsigned I = full;
                for (unsigned S = 0; S <= full; S++) {
                    if (!(I & ~S)) continue;           /* S already contains I: no change */
                    int ms = 0;
                    for (int a = 0; a < na; a++) if (S >> a & 1) ms += m[a];
                    if (dem[S] > ms) I &= S;
                }
                int cov = ((Lmask & ~(1u << i0) & ~(1u << i1) & ~(1u << i2) & ~(1u << i3)) == 0);
                if (I == 0) nanyfail++;
                if (cov) {
                    ncov++;
                    int sz = __builtin_popcount(I);
                    if (sz < minI) minI = sz;
                    if (I == 0) {
                        ncovfail++;
                        if (verbose) printf("  FAIL m = {%d,%d,%d,%d}\n", i0, i1, i2, i3);
                    }
                }
            }
        }
        printf("sparse %d L %d adm %ld cov %ld covfail %ld minI %d anyfail %ld\n",
               sp, nL, nadm, ncov, ncovfail, minI, nanyfail);
        fflush(stdout);
    }
    return 0;
}
