/* sa_kl1.c -- REVIEW4: simulated-annealing search for a KL1 counterexample, and a source of
 * blocks where the hub/petal structure occurs under a COVERING multiset (never seen in the data).
 *
 * State: a block X = A u C with |A| = na, |C| = na - 2, every c of degree 6 into A, d_a in [3, 6],
 * block-sparse (sum_c (e(c,T) - 3)^+ <= 3|T| - 6 for |T| >= 3).
 * Energy: 10 * min_{covering m} |I_X(m)| - bigcov - 0.1 * min(ndense, 30), where bigcov is the largest
 * union of big overloaded sets over covering m and ndense counts sets T with |T| >= 4, base(T) >= -3.
 * Moves: move one edge c-a to c-a'. Every block visited where some covering m has two maximal
 * overloaded sets sharing >= 3 vertices (a hub), or sharing exactly 1 (N1), or I_X = empty, is written
 * (deduplicated) to OUT in kl1rev's format, so kl1rev can check all lemmas on it.
 *
 * Usage: sa_kl1 na seed steps T0 OUT [startfile-with-one-block-line]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

#define MAXA 18
static int na, nc;
static uint32_t cm[MAXA], fullA;
static int dA[MAXA], del[MAXA];
static int *base; static uint32_t *cand; static int *cbase; static int ncand;
static uint64_t rng;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline int pc(uint32_t x) { return __builtin_popcount(x); }

static int recompute(void) { /* degrees, sparsity, candidate list; returns 1 if valid */
    for (int a = 0; a < na; a++) dA[a] = 0;
    for (int c = 0; c < nc; c++) for (int a = 0; a < na; a++) if (cm[c] >> a & 1) dA[a]++;
    for (int a = 0; a < na; a++) { if (dA[a] < 3 || dA[a] > 6) return 0; del[a] = 6 - dA[a]; }
    ncand = 0;
    for (uint32_t T = 0; T <= fullA; T++) {
        int ex3 = 0, ex2 = 0, t = pc(T);
        for (int c = 0; c < nc; c++) { int e = pc(cm[c] & T); if (e > 3) ex3 += e - 3; if (e > 2) ex2 += e - 2; }
        if (t >= 3 && ex3 > 3 * t - 6) return 0;
        int b = 4 - 4 * t + ex2;
        if (b >= -3) { cand[ncand] = T; cbase[ncand] = b; ncand++; }
        if (T == fullA) break;
    }
    return 1;
}

static int flag_hub, flag_n1, flag_empty;
static int m_[MAXA];
static uint32_t m1, m2; /* bit planes of m */
static int best_ix, best_cov;
static uint32_t ovl[4096]; static int novl;

static void eval_m(void) {
    /* covering? */
    for (int a = 0; a < na; a++) if (del[a] == 3 && m_[a] == 0) return;
    m1 = m2 = 0;
    for (int a = 0; a < na; a++) { if (m_[a] & 1) m1 |= 1u << a; if (m_[a] & 2) m2 |= 1u << a; }
    uint32_t uni = 0, bigu = 0; novl = 0;
    for (int i = 0; i < ncand; i++) {
        uint32_t T = cand[i];
        int th = pc(T & m1) + 2 * pc(T & m2) + cbase[i];
        if (th >= 1) { uni |= T; if (pc(T) >= 3) { bigu |= T; if (novl < 4096) ovl[novl++] = T; } }
    }
    int ix = pc(fullA & ~uni);
    if (ix < best_ix) best_ix = ix;
    if (pc(bigu) > best_cov) best_cov = pc(bigu);
    if (ix == 0) flag_empty = 1;
    if (novl >= 2) {
        /* maximal big overloaded sets (a singleton is never inside a big set's competitor here) */
        for (int i = 0; i < novl; i++) {
            int ismax = 1;
            for (int j = 0; j < novl; j++) if (j != i && (ovl[i] & ovl[j]) == ovl[i] && ovl[i] != ovl[j]) { ismax = 0; break; }
            if (!ismax) continue;
            for (int j = i + 1; j < novl; j++) {
                int jmax = 1;
                for (int k = 0; k < novl; k++) if (k != j && (ovl[j] & ovl[k]) == ovl[j] && ovl[j] != ovl[k]) { jmax = 0; break; }
                if (!jmax) continue;
                int s = pc(ovl[i] & ovl[j]);
                if (s >= 3) flag_hub = 1;
                if (s == 1) flag_n1 = 1;
            }
        }
    }
}
static void enum_m(int a, int left) {
    if (a == na) { if (left == 0) eval_m(); return; }
    int cap = del[a] < 3 ? del[a] : 3;
    for (int v = 0; v <= cap && v <= left; v++) { m_[a] = v; enum_m(a + 1, left - v); }
    m_[a] = 0;
}
static double energy(void) {
    best_ix = na + 1; best_cov = 0; flag_hub = flag_n1 = flag_empty = 0;
    int nL = 0; for (int a = 0; a < na; a++) if (del[a] == 3) nL++;
    if (nL <= 4) enum_m(0, 4);
    int ndense = 0; for (int i = 0; i < ncand; i++) if (pc(cand[i]) >= 4) ndense++;
    if (ndense > 30) ndense = 30;
    return 10.0 * best_ix - best_cov - 0.1 * ndense;
}

/* dedupe of dumped blocks */
#define HSZ (1 << 20)
static uint64_t *hset;
static int seen_block(void) {
    uint64_t h = 1469598103934665603ull;
    uint32_t s[MAXA]; memcpy(s, cm, sizeof(uint32_t) * nc);
    /* order-independent in C: sort masks */
    for (int i = 0; i < nc; i++) for (int j = i + 1; j < nc; j++) if (s[j] < s[i]) { uint32_t t = s[i]; s[i] = s[j]; s[j] = t; }
    for (int i = 0; i < nc; i++) { h ^= s[i]; h *= 1099511628211ull; }
    if (!h) h = 1;
    uint64_t k = h & (HSZ - 1);
    while (hset[k]) { if (hset[k] == h) return 1; k = (k + 1) & (HSZ - 1); }
    hset[k] = h; return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: sa_kl1 na seed steps T0 OUT [start]\n"); return 1; }
    na = atoi(argv[1]); nc = na - 2; rng = strtoull(argv[2], 0, 10) * 0x9E3779B97F4A7C15ull + 7;
    long steps = atol(argv[3]); double T0 = atof(argv[4]);
    FILE *out = fopen(argv[5], "a");
    fullA = (1u << na) - 1;
    base = 0; cand = malloc(sizeof(uint32_t) << na); cbase = malloc(sizeof(int) << na);
    hset = calloc(HSZ, sizeof(uint64_t));
    if (argc >= 7) {
        FILE *f = fopen(argv[6], "r"); int a2, c2;
        if (!f || fscanf(f, "%d %d", &a2, &c2) != 2 || a2 != na) { fprintf(stderr, "bad start\n"); return 1; }
        for (int c = 0; c < nc; c++) { unsigned long x; if (fscanf(f, "%lu", &x) != 1) return 1; cm[c] = (uint32_t)x; }
        fclose(f);
        if (!recompute()) { fprintf(stderr, "start block invalid\n"); return 1; }
    } else {
        for (;;) {
            for (int c = 0; c < nc; c++) { uint32_t s = 0; while (pc(s) < 6) s |= 1u << (xr() % na); cm[c] = s; }
            /* repair low degrees */
            for (int it = 0; it < 1000; it++) {
                int low = -1; for (int a = 0; a < na; a++) { int d = 0; for (int c = 0; c < nc; c++) d += cm[c] >> a & 1; if (d < 3) { low = a; break; } }
                if (low < 0) break;
                int c = xr() % nc; if (cm[c] >> low & 1) continue;
                int a2 = xr() % na; if (!(cm[c] >> a2 & 1)) continue;
                int d2 = 0; for (int cc = 0; cc < nc; cc++) d2 += cm[cc] >> a2 & 1;
                if (d2 <= 3) continue;
                cm[c] ^= (1u << a2) | (1u << low);
            }
            if (recompute()) break;
        }
    }
    double E = energy(), bestE = E;
    long dumped = 0, nhub = 0, nn1 = 0, nempty = 0;
    for (long st = 0; st < steps; st++) {
        double Tt = T0 * (1.0 - (double)st / steps) + 0.05;
        int c = xr() % nc;
        uint32_t nb = cm[c];
        int ai = xr() % 6, k = 0, a = -1;
        for (int x = 0; x < na; x++) if (nb >> x & 1) { if (k == ai) { a = x; break; } k++; }
        int a2 = xr() % na; if (nb >> a2 & 1) continue;
        uint32_t old = cm[c];
        cm[c] = (old & ~(1u << a)) | (1u << a2);
        if (!recompute()) { cm[c] = old; recompute(); continue; }
        double E2 = energy();
        int fh = flag_hub, fn = flag_n1, fe = flag_empty;
        if (fh || fn || fe) {
            if (!seen_block()) {
                fprintf(out, "%d %d", na, nc); for (int i = 0; i < nc; i++) fprintf(out, " %u", cm[i]); fprintf(out, "\n"); fflush(out);
                dumped++; nhub += fh; nn1 += fn; nempty += fe;
                if (fe) fprintf(stderr, "!!! covering m with I_X empty found (step %ld)\n", st);
            }
        }
        if (E2 <= E || exp((E - E2) / Tt) > (double)(xr() % 1000000) / 1e6) { E = E2; if (E < bestE) bestE = E; }
        else { cm[c] = old; recompute(); }
        if (st % 20000 == 0) { fprintf(stderr, "step %ld E %.1f best %.1f dumped %ld (hub %ld n1 %ld empty %ld)\n", st, E, bestE, dumped, nhub, nn1, nempty); }
    }
    fprintf(stderr, "done na %d seed %s: bestE %.1f dumped %ld (hub %ld, n1 %ld, empty %ld)\n", na, argv[2], bestE, dumped, nhub, nn1, nempty);
    fclose(out);
    return 0;
}
