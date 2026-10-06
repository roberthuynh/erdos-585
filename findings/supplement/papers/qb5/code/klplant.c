/* klplant.c (lane qb5, round 3; NOTES.md section 7).
 *
 * Random 2-blocks with planted dense pieces, then local search, looking for X-bad 4-sets M of types
 *   (b) M misses exactly one in-degree-3 vertex a of A and a is not in I(m)   [KL2 failure]
 *   (c) M covers L_A and I(m) = 0                                           [KL1 failure]
 * where m is the endpoint multiset of M on A (|m| = 4, m(a) <= min(3, delta_a), extendable to an
 * admissible cut-degree vector).  Blocks: |A| = na, |C| = na - 2, C saturated (degree 6) into A,
 * 3 <= d_a <= 6, sparse inside the block, #{d_a = 3} <= 7.
 * Usage: klplant na seed starts steps   -> prints blocks with a type (b) or (c) failure (blockkl format)
 * and, on stderr, running statistics.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXA 16
static int na, nc;
static unsigned cm[MAXA];
static unsigned dl[1 << MAXA]; static signed char dv[1 << MAXA]; static int ndl;
static unsigned long long rs;
static unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }

static void degs(int *din) {
    memset(din, 0, sizeof(int) * MAXA);
    for (int j = 0; j < nc; j++) for (int a = 0; a < na; a++) if (cm[j] >> a & 1) din[a]++;
}

static int valid(void) {
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

/* counts: fb = type (b) failures, fc = type (c) failures, ncore = demand sets with |S| >= 5 and
   dem(S) > |S n L|; minI = min |I(m)| - |A - V(m)| over covering m (<= 0) */
static void evaluate(int *fb, int *fc, int *ncore, int *gap, int verbose) {
    unsigned full = (1u << na) - 1;
    int din[MAXA]; degs(din);
    unsigned Lmask = 0;
    int hi[MAXA], lo[MAXA];
    for (int a = 0; a < na; a++) {
        int d = 6 - din[a];
        hi[a] = d < 3 ? d : 3; lo[a] = d - 2 > 0 ? d - 2 : 0;
        if (din[a] == 3) Lmask |= 1u << a;
    }
    ndl = 0; *ncore = 0;
    for (unsigned S = 1; S < full; S++) {
        int t = 4 * __builtin_popcount(S);
        for (int j = 0; j < nc; j++) { int e = __builtin_popcount(cm[j] & S); t -= e < 4 ? e : 4; }
        if (t >= 1) {
            dl[ndl] = S; dv[ndl] = (signed char)t; ndl++;
            if (__builtin_popcount(S) >= 5 && t > __builtin_popcount(S & Lmask)) (*ncore)++;
        }
    }
    *fb = 0; *fc = 0; *gap = 0;
    int m[MAXA];
    for (int i0 = 0; i0 < na; i0++) for (int i1 = i0; i1 < na; i1++)
    for (int i2 = i1; i2 < na; i2++) for (int i3 = i2; i3 < na; i3++) {
        unsigned sup = (1u << i0) | (1u << i1) | (1u << i2) | (1u << i3);
        unsigned miss = Lmask & ~sup;
        int nmiss = __builtin_popcount(miss);
        if (nmiss > 1) continue;
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
        if (nmiss == 1) {
            if (!(I & miss)) {
                (*fb)++;
                if (verbose) printf("  (b) m = {%d,%d,%d,%d} misses %d\n", i0, i1, i2, i3, __builtin_ctz(miss));
            }
        } else {
            int g = __builtin_popcount(I) - __builtin_popcount(full & ~sup);
            if (g < *gap) *gap = g;
            if (!I) {
                (*fc)++;
                if (verbose) printf("  (c) m = {%d,%d,%d,%d}\n", i0, i1, i2, i3);
            }
        }
    }
}

static void print_block(void) {
    printf("%d %d", na, nc);
    for (int j = 0; j < nc; j++) printf(" %u", cm[j]);
    printf("\n");
}

static int planted(void) {
    /* parts of A: r in {2,3}; each C-vertex has a home part and h edges there */
    for (int tries = 0; tries < 100000; tries++) {
        int r = 2 + rnd() % 2;
        int part[MAXA];
        for (int a = 0; a < na; a++) part[a] = rnd() % r;
        int psz[4] = {0};
        for (int a = 0; a < na; a++) psz[part[a]]++;
        int okp = 1;
        for (int i = 0; i < r; i++) if (psz[i] < 3) okp = 0;
        if (!okp) continue;
        for (int j = 0; j < nc; j++) {
            int home = rnd() % r;
            int h = 3 + rnd() % 4;
            if (h > psz[home]) h = psz[home];
            unsigned mk = 0;
            while (__builtin_popcount(mk) < h) { int a = rnd() % na; if (part[a] == home) mk |= 1u << a; }
            while (__builtin_popcount(mk) < 6) { int a = rnd() % na; if (part[a] != home) mk |= 1u << a; }
            cm[j] = mk;
        }
        if (valid()) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: klplant na seed starts steps\n"); return 1; }
    na = atoi(argv[1]); nc = na - 2;
    rs = 88172645463325252ULL ^ ((unsigned long long)atoll(argv[2]) * 2654435761ULL + 12345);
    int starts = atoi(argv[3]); long steps = atol(argv[4]);
    long withcore = 0, found = 0, nacc = 0, nval = 0; int bestgap = 0;
    for (int s = 0; s < starts; s++) {
        if (!planted()) continue;
        int fb, fc, nco, gap;
        evaluate(&fb, &fc, &nco, &gap, 0);
        if (nco) withcore++;
        long cur = -(long)(fb + fc) * 1000000 + (long)gap * 1000 - nco;
        for (long t = 0; t < steps && !(fb + fc); t++) {
            int j = rnd() % nc;
            unsigned old = cm[j];
            int out, in;
            do { out = rnd() % na; } while (!(old >> out & 1));
            do { in = rnd() % na; } while (old >> in & 1);
            cm[j] = (old & ~(1u << out)) | (1u << in);
            if (!valid()) { cm[j] = old; continue; }
            nval++;
            int fb2, fc2, nco2, gap2;
            evaluate(&fb2, &fc2, &nco2, &gap2, 0);
            long val = -(long)(fb2 + fc2) * 1000000 + (long)gap2 * 1000 - nco2;
            if (val <= cur || rnd() % 100 < 3) { nacc++; cur = val; fb = fb2; fc = fc2; nco = nco2; gap = gap2; }
            else cm[j] = old;
        }
        if (fb + fc) {
            found++;
            printf("FOUND start %d fb %d fc %d ncore %d\n", s, fb, fc, nco);
            print_block();
            evaluate(&fb, &fc, &nco, &gap, 1);
            fflush(stdout);
        }
        if (gap < bestgap) bestgap = gap;
        if ((s + 1) % 20 == 0) fprintf(stderr, "starts %d withcore %ld found %ld bestgap %d\n", s + 1, withcore, found, bestgap);
    }
    fprintf(stderr, "done starts %d withcore %ld found %ld valid-moves %ld accepted %ld\n", starts, withcore, found, nval, nacc);
    return 0;
}
