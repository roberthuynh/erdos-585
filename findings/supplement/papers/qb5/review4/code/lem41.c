/* lem41.c -- REVIEW4 own check of PAPER3 Lemma 4.1 (refined covering lemma), the one computed
 * lemma on the QB(5) path. Written from scratch.
 *
 * E: 7 edges of a simple bipartite graph, sides A (rows) and D (columns), every vertex in <= 3 edges.
 * Every such graph is isomorphic to a p x q 0/1 matrix whose row sums and column sums are
 * non-increasing sequences in {1,2,3} (sort the rows and columns by degree). We enumerate all such
 * matrices (a superset of the isomorphism classes).
 * L_A: rows with c >= 1 (all rows), containing every row with c = 3, sum_{L_A} (3 - c) <= 5; same for L_D.
 * Claim: some 4-set M of E has, on each side, at most one L-vertex a outside V(M), and then no rigid
 * K subset V(M) - a on that side, where K is rigid if every vertex of K n L has c = 3, every E-edge at K
 * is in M, and K meets exactly 3 or 4 edges of E. Modes: refined (as stated), loose (size condition
 * dropped: any nonempty such K), plain (no rigid condition).
 * Rigid test by literal subset search over K (no shortcut).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int p, q, rs[7], cs[7];
static int mat[7][7];
static long nmat, nlab[3], nfail[3];
static int eu[7], ev[7]; /* edges */

static int side_ok(int nv, const int *c, int Lmask, const int *mv, int mode) {
    /* vertices 0..nv-1 on one side; c[v] cut degree, mv[v] edges of M at v */
    int out = 0, a = -1;
    for (int v = 0; v < nv; v++) if ((Lmask >> v & 1) && mv[v] == 0) { out++; a = v; }
    if (out >= 2) return 0;
    if (out == 0 || mode == 2) return 1;
    /* look for a rigid K subset V(M) - a, literal search over subsets of the side */
    for (int K = 1; K < (1 << nv); K++) {
        if (K >> a & 1) continue;
        int ok = 1, ce = 0;
        for (int v = 0; v < nv && ok; v++) if (K >> v & 1) {
            if (mv[v] == 0) ok = 0;                    /* K subset V(M) */
            if ((Lmask >> v & 1) && c[v] != 3) ok = 0;  /* K n L has c = 3 */
            if (mv[v] != c[v]) ok = 0;                 /* every E-edge at K in M */
            ce += c[v];
        }
        if (!ok) continue;
        if (mode == 1 || ce == 3 || ce == 4) return 0; /* a rigid K exists */
    }
    return 1;
}

static void check_matrix(void) {
    nmat++;
    int ne = 0;
    for (int i = 0; i < p; i++) for (int j = 0; j < q; j++) if (mat[i][j]) { eu[ne] = i; ev[ne] = j; ne++; }
    if (ne != 7) { fprintf(stderr, "edge count\n"); exit(1); }
    /* admissible L sets */
    int LA[128], nLA = 0, LD[128], nLD = 0;
    for (int L = 0; L < (1 << p); L++) {
        int ok = 1, bud = 0;
        for (int v = 0; v < p; v++) { if (rs[v] == 3 && !(L >> v & 1)) ok = 0; if (L >> v & 1) bud += 3 - rs[v]; }
        if (ok && bud <= 5) LA[nLA++] = L;
    }
    for (int L = 0; L < (1 << q); L++) {
        int ok = 1, bud = 0;
        for (int v = 0; v < q; v++) { if (cs[v] == 3 && !(L >> v & 1)) ok = 0; if (L >> v & 1) bud += 3 - cs[v]; }
        if (ok && bud <= 5) LD[nLD++] = L;
    }
    for (int mode = 0; mode < 3; mode++) {
        for (int x = 0; x < nLA; x++) for (int y = 0; y < nLD; y++) {
            nlab[mode]++;
            int found = 0;
            for (int Mm = 0; Mm < 128 && !found; Mm++) {
                if (__builtin_popcount(Mm) != 4) continue;
                int ma[7] = {0}, md[7] = {0};
                for (int e = 0; e < 7; e++) if (Mm >> e & 1) { ma[eu[e]]++; md[ev[e]]++; }
                if (side_ok(p, rs, LA[x], ma, mode) && side_ok(q, cs, LD[y], md, mode)) found = 1;
            }
            if (!found) nfail[mode]++;
        }
    }
}

/* fill matrix row by row with exact row sums, then check column sums */
static int colleft[7];
static void fill(int i, int j, int rowleft) {
    if (i == p) { for (int k = 0; k < q; k++) if (colleft[k]) return; check_matrix(); return; }
    if (j == q) { if (rowleft == 0) fill(i + 1, 0, i + 1 < p ? rs[i + 1] : 0); return; }
    /* prune: remaining columns must absorb rowleft */
    if (rowleft > q - j) return;
    mat[i][j] = 0; fill(i, j + 1, rowleft);
    if (rowleft > 0 && colleft[j] > 0) { mat[i][j] = 1; colleft[j]--; fill(i, j + 1, rowleft - 1); colleft[j]++; mat[i][j] = 0; }
}

/* non-increasing sequences in {1,2,3} summing to 7 */
static int seqs[64][7], seqlen[64], nseq;
static void genseq(int *cur, int len, int sum, int maxv) {
    if (sum == 7) { memcpy(seqs[nseq], cur, sizeof(int) * len); seqlen[nseq++] = len; return; }
    for (int v = maxv; v >= 1; v--) if (sum + v <= 7) { cur[len] = v; genseq(cur, len + 1, sum + v, v); }
}

int main(void) {
    int cur[7];
    genseq(cur, 0, 0, 3);
    for (int a = 0; a < nseq; a++) for (int b = 0; b < nseq; b++) {
        p = seqlen[a]; q = seqlen[b];
        memcpy(rs, seqs[a], sizeof(int) * p); memcpy(cs, seqs[b], sizeof(int) * q);
        memcpy(colleft, cs, sizeof(int) * q);
        memset(mat, 0, sizeof mat);
        fill(0, 0, rs[0]);
    }
    printf("degree sequences per side: %d\n", nseq);
    printf("matrices: %ld\n", nmat);
    const char *nm[3] = {"refined (as stated)", "loose (size condition dropped)", "plain (no rigid condition)"};
    for (int m = 0; m < 3; m++) printf("%-32s labellings %ld failures %ld\n", nm[m], nlab[m], nfail[m]);
    return 0;
}
