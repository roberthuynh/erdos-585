/* klsearch.c (lane qb5, round 3; NOTES.md section 7).
 *
 * Local search for a 2-block X (|A| = na, |C| = nc = na - 2, every C-vertex of degree 6 into A, all
 * in-block degrees d_a >= 3, sparse inside the block, admissible: #{d_a = 3} <= 7) and a multiset m on A
 * (|m| = 4, m(a) <= min(3, delta_a), extendable to an admissible cut-degree vector) that covers
 * L_A = {d_a = 3} and has I(m) = 0 (a counterexample to Key Lemma KL1).
 * Score of a block: min over covering admissible m of |I(m)|; secondary: number of demand sets.
 * Moves: a C-vertex swaps one neighbour.  Prints every block reaching score 0 (blockkl.c format).
 * Usage: klsearch na seed steps [restarts] [mode]
 *   mode 0: random start; mode 1: start from a planted two-core piece structure when it fits.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXA 16
static int na, nc;
static unsigned cm[MAXA];
static signed char dem[1 << MAXA];
static unsigned dl[1 << MAXA]; static signed char dv[1 << MAXA]; static int ndl;
static unsigned long long rs;
static unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }

static int degs(int *din) {
    memset(din, 0, sizeof(int) * MAXA);
    for (int j = 0; j < nc; j++) for (int a = 0; a < na; a++) if (cm[j] >> a & 1) din[a]++;
    return 0;
}

static int sparse_ok(void) {
    int din[MAXA]; degs(din);
    int nL = 0;
    for (int a = 0; a < na; a++) { if (din[a] < 3 || din[a] > 6) return 0; if (din[a] == 3) nL++; }
    if (nL > 7) return 0;
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

/* returns score = min |I(m)| over covering admissible m (99 if none), sets *nfail, *ndem */
static int evaluate(int *nfail, int *ndem, int verbose) {
    unsigned full = (1u << na) - 1;
    ndl = 0;
    for (unsigned S = 1; S < full; S++) {
        int t = 4 * __builtin_popcount(S);
        for (int j = 0; j < nc; j++) { int e = __builtin_popcount(cm[j] & S); t -= e < 4 ? e : 4; }
        if (t >= 1) { dl[ndl] = S; dv[ndl] = (signed char)t; ndl++; }
    }
    *ndem = ndl;
    int din[MAXA]; degs(din);
    int hi[MAXA], lo[MAXA]; unsigned Lmask = 0;
    for (int a = 0; a < na; a++) {
        int d = 6 - din[a];
        hi[a] = d < 3 ? d : 3; lo[a] = d - 2 > 0 ? d - 2 : 0;
        if (din[a] == 3) Lmask |= 1u << a;
    }
    int best = 99; *nfail = 0;
    int m[MAXA];
    for (int i0 = 0; i0 < na; i0++) for (int i1 = i0; i1 < na; i1++)
    for (int i2 = i1; i2 < na; i2++) for (int i3 = i2; i3 < na; i3++) {
        unsigned sup = (1u << i0) | (1u << i1) | (1u << i2) | (1u << i3);
        if (Lmask & ~sup) continue;
        memset(m, 0, sizeof m);
        m[i0]++; m[i1]++; m[i2]++; m[i3]++;
        int ok = 1, need = 0;
        for (int a = 0; a < na; a++) {
            if (m[a] > hi[a]) { ok = 0; break; }
            need += m[a] > lo[a] ? m[a] : lo[a];
        }
        if (!ok || need > 7) continue;
        unsigned I = full;
        for (int t = 0; t < ndl && I; t++) {
            unsigned S = dl[t];
            if (!(I & ~S)) continue;
            int ms = ((S >> i0) & 1) + ((S >> i1) & 1) + ((S >> i2) & 1) + ((S >> i3) & 1);
            if (dv[t] > ms) I &= S;
        }
        int sz = __builtin_popcount(I);
        if (sz < best) best = sz;
        if (sz == 0) {
            (*nfail)++;
            if (verbose) printf("  FAIL m = {%d,%d,%d,%d}\n", i0, i1, i2, i3);
        }
    }
    return best;
}

static void print_block(void) {
    printf("%d %d", na, nc);
    for (int j = 0; j < nc; j++) printf(" %u", cm[j]);
    printf("\n");
}

static void random_block(void) {
    for (;;) {
        for (int j = 0; j < nc; j++) {
            unsigned m = 0;
            while (__builtin_popcount(m) < 6) m |= 1u << (rnd() % na);
            cm[j] = m;
        }
        if (sparse_ok()) return;
    }
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: klsearch na seed steps [restarts]\n"); return 1; }
    na = atoi(argv[1]); nc = na - 2;
    rs = 88172645463325252ULL ^ (unsigned long long)atoll(argv[2]) * 2654435761ULL;
    long steps = atol(argv[3]);
    int restarts = argc > 4 ? atoi(argv[4]) : 1;
    for (int r = 0; r < restarts; r++) {
        random_block();
        int nf, nd;
        int sc = evaluate(&nf, &nd, 0);
        long cur = (long)sc * 100000 - nd;
        int bestsc = sc;
        for (long s = 0; s < steps; s++) {
            int j = rnd() % nc;
            unsigned old = cm[j];
            int out, in;
            do { out = rnd() % na; } while (!(old >> out & 1));
            do { in = rnd() % na; } while (old >> in & 1);
            cm[j] = (old & ~(1u << out)) | (1u << in);
            if (!sparse_ok()) { cm[j] = old; continue; }
            int sc2 = evaluate(&nf, &nd, 0);
            long val = (long)sc2 * 100000 - nd;
            if (val <= cur || (rnd() % 1000) < 20) {
                cur = val; sc = sc2;
                if (sc < bestsc) { bestsc = sc; fprintf(stderr, "restart %d step %ld score %d ndem %d\n", r, s, sc, nd); }
                if (sc == 0) {
                    printf("FOUND restart %d step %ld nfail %d\n", r, s, nf);
                    print_block();
                    evaluate(&nf, &nd, 1);
                    fflush(stdout);
                    break;
                }
            } else cm[j] = old;
        }
        fprintf(stderr, "restart %d done best %d\n", r, bestsc);
    }
    return 0;
}
