/* lemma42.c -- referee's own check of PAPER2 Lemma 4.2 (covering lemma for 7-edge cuts).
 *
 * Enumeration (own): a 7-edge simple bipartite graph without isolated vertices and with max
 * degree <= 3 is given by na A-rows (bitmasks over nd D-columns), rows sorted non-increasing
 * as integers, every column used, row popcounts 1..3, column sums 1..3, total 7 edges.
 * Every such graph is isomorphic to at least one enumerated matrix (sort the rows).
 *
 * Decision (direct): for p in A, q in D (both ends of cut edges: no isolated vertices here),
 * F = E - E(p) - E(q); every M subset of F with |M| = 4 gives the "OK" pair
 * (cover_A(M) + p, cover_D(M) + q).  (L_A, L_D) succeeds iff some OK pair contains it.
 * Superset closure over the (na+nd)-bit space.
 *
 * Admissible L_A: vertices with c >= 1 (all here), containing every c = 3 vertex,
 * sum over L_A of (3 - c) <= 5.  Same for L_D.
 *
 * mode 0: p, q must be ends of cut edges (as in Lemma 4.2).
 * mode 1: additionally allow p and/or q to be a vertex outside the cut (c = 0).
 *
 * Also counts isomorphism classes (canonical form: min over column permutations of the
 * sorted row tuple), to compare with genbg -d1:1 -D3:3 na nd 7:7.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int mode = 0;
static int budget = 5, msize = 4; /* sensitivity tests only; the lemma is budget 5, msize 4 */
static long long ngraphs = 0, nlab = 0, nfail = 0, npairs_checked = 0;
static int na, nd;
static int rows[8];
static unsigned char ach[1 << 14];

/* canonical forms */
#define HSIZE (1 << 22)
static uint64_t *htab;
static long long nclasses = 0;
static int perms[5040][7];
static int nperm = 0;

static void gen_perms(int n) {
    int p[7];
    for (int i = 0; i < n; i++) p[i] = i;
    nperm = 0;
    /* Heap-free: lexicographic next_permutation */
    while (1) {
        for (int i = 0; i < n; i++) perms[nperm][i] = p[i];
        nperm++;
        int i = n - 2;
        while (i >= 0 && p[i] >= p[i + 1]) i--;
        if (i < 0) break;
        int j = n - 1;
        while (p[j] <= p[i]) j--;
        int t = p[i]; p[i] = p[j]; p[j] = t;
        for (int a = i + 1, b = n - 1; a < b; a++, b--) { t = p[a]; p[a] = p[b]; p[b] = t; }
    }
}

static int cmp_desc(const void *x, const void *y) { return (*(int *)y) - (*(int *)x); }

static void canon_insert(void) {
    uint64_t best = UINT64_MAX;
    for (int k = 0; k < nperm; k++) {
        int r[8];
        for (int i = 0; i < na; i++) {
            int m = 0;
            for (int j = 0; j < nd; j++) if (rows[i] >> j & 1) m |= 1 << perms[k][j];
            r[i] = m;
        }
        qsort(r, na, sizeof(int), cmp_desc);
        uint64_t key = ((uint64_t)na << 56) | ((uint64_t)nd << 52);
        for (int i = 0; i < na; i++) key |= (uint64_t)r[i] << (7 * i);
        if (key < best) best = key;
    }
    uint64_t h = (best * 0x9E3779B97F4A7C15ULL) >> 42;
    while (htab[h] != 0) {
        if (htab[h] == best) return;
        h = (h + 1) & (HSIZE - 1);
    }
    htab[h] = best;
    nclasses++;
}

static void process(void) {
    int ea[7], ed[7], ne = 0;
    int ca[8] = {0}, cd[8] = {0};
    for (int i = 0; i < na; i++)
        for (int j = 0; j < nd; j++)
            if (rows[i] >> j & 1) { ea[ne] = i; ed[ne] = j; ne++; ca[i]++; cd[j]++; }
    if (ne != 7) { fprintf(stderr, "bad edge count\n"); exit(1); }
    ngraphs++;
    canon_insert();
    int nb = na + nd;
    memset(ach, 0, (size_t)1 << nb);
    /* p in A or p = -1 (outside the cut, mode 1); same for q */
    for (int p = (mode ? -1 : 0); p < na; p++)
        for (int q = (mode ? -1 : 0); q < nd; q++) {
            int F[7], nf = 0;
            for (int e = 0; e < 7; e++) if (ea[e] != p && ed[e] != q) F[nf++] = e;
            if (nf < msize) continue;
            for (int x = 0; x < (1 << nf); x++) {
                if (__builtin_popcount(x) != msize) continue;
                int oa = 0, od = 0;
                for (int i = 0; i < nf; i++) if (x >> i & 1) { oa |= 1 << ea[F[i]]; od |= 1 << ed[F[i]]; }
                if (p >= 0) oa |= 1 << p;
                if (q >= 0) od |= 1 << q;
                ach[oa | (od << na)] = 1;
            }
        }
    /* superset closure */
    for (int b = 0; b < nb; b++)
        for (int m = 0; m < (1 << nb); m++)
            if (!(m >> b & 1) && ach[m | (1 << b)]) ach[m] = 1;
    /* admissible labellings */
    int forcedA = 0, forcedD = 0;
    for (int i = 0; i < na; i++) if (ca[i] == 3) forcedA |= 1 << i;
    for (int j = 0; j < nd; j++) if (cd[j] == 3) forcedD |= 1 << j;
    for (int LA = 0; LA < (1 << na); LA++) {
        if ((LA & forcedA) != forcedA) continue;
        int sa = 0;
        for (int i = 0; i < na; i++) if (LA >> i & 1) sa += 3 - ca[i];
        if (sa > budget) continue;
        for (int LD = 0; LD < (1 << nd); LD++) {
            if ((LD & forcedD) != forcedD) continue;
            int sd = 0;
            for (int j = 0; j < nd; j++) if (LD >> j & 1) sd += 3 - cd[j];
            if (sd > budget) continue;
            nlab++;
            if (!ach[LA | (LD << na)]) {
                nfail++;
                if (nfail <= 20) {
                    printf("FAIL na=%d nd=%d rows=", na, nd);
                    for (int i = 0; i < na; i++) printf("%d,", rows[i]);
                    printf(" LA=%d LD=%d\n", LA, LD);
                }
            }
        }
    }
}

/* rows non-increasing, popcount 1..3, total edges 7, column sums <= 3, all columns used */
static void rec(int i, int maxrow, int edges, int *colsum) {
    if (i == na) {
        if (edges != 7) return;
        for (int j = 0; j < nd; j++) if (colsum[j] == 0) return;
        process();
        return;
    }
    int remaining_rows = na - i;
    for (int r = maxrow; r >= 1; r--) {
        int pc = __builtin_popcount(r);
        if (pc > 3) continue;
        if (edges + pc + (remaining_rows - 1) > 7) continue;      /* later rows need >= 1 each */
        if (edges + pc + 3 * (remaining_rows - 1) < 7) continue;  /* later rows give <= 3 each */
        int ok = 1;
        for (int j = 0; j < nd; j++) if ((r >> j & 1) && colsum[j] >= 3) { ok = 0; break; }
        if (!ok) continue;
        for (int j = 0; j < nd; j++) if (r >> j & 1) colsum[j]++;
        rows[i] = r;
        rec(i + 1, r, edges + pc, colsum);
        for (int j = 0; j < nd; j++) if (r >> j & 1) colsum[j]--;
    }
}

int main(int argc, char **argv) {
    if (argc > 1) mode = atoi(argv[1]);
    if (argc > 2) budget = atoi(argv[2]);
    if (argc > 3) msize = atoi(argv[3]);
    htab = calloc(HSIZE, sizeof(uint64_t));
    long long totg = 0, totl = 0, totf = 0, totc = 0;
    for (na = 3; na <= 7; na++)
        for (nd = 3; nd <= 7; nd++) {
            ngraphs = nlab = nfail = nclasses = 0;
            gen_perms(nd);
            int colsum[8] = {0};
            rec(0, (1 << nd) - 1, 0, colsum);
            printf("na=%d nd=%d labelled=%lld classes=%lld labellings=%lld failures=%lld\n",
                   na, nd, ngraphs, nclasses, nlab, nfail);
            totg += ngraphs; totl += nlab; totf += nfail; totc += nclasses;
        }
    printf("TOTAL mode=%d budget=%d msize=%d labelled_graphs=%lld classes=%lld labellings=%lld failures=%lld\n",
           mode, budget, msize, totg, totc, totl, totf);
    return 0;
}
