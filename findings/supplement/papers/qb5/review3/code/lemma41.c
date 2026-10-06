/* Referee check of PAPER3 Lemma 4.1 (refined covering lemma), written from scratch.
 *
 * Objects: E = 7 edges of a simple bipartite graph, sides A (rows) and D (cols), every vertex in 1..3
 * edges (only ends of E matter).  L_A subset of A: contains every c=3 vertex, sum_{L_A}(3-c) <= 5.
 * Same for L_D.  Claim: some 4-subset M of E has, on each side S, at most one L_S-vertex that is not
 * an end of M, and if a is such a vertex, no rigid K subset V(M)-a on side S, where K (nonempty set of
 * S-ends) is rigid if every vertex of K cap L_S has c=3, every E-edge at K lies in M, and c(K) in {3,4}.
 *
 * Two enumerations:
 *   classes : rows as bitmasks in non-increasing order; canonical form by brute force over all row
 *             permutations with sorted column masks; one representative per side-preserving iso class.
 *   grid    : every 0/1 matrix with non-increasing row sums and non-increasing column sums in {1,2,3}
 *             (the enumeration PAPER2/PAPER3 describe), every labelling.
 * Decision: literal subset search for K (no shortcut), cross-checked against the shortcut
 *           "rigid K exists iff m(F) >= 3", F = {v != a : m(v) = c_v >= 1, v notin L or c_v = 3}.
 * Variants: sizes = {3,4} (paper), 'loose' = any nonempty K, 'plain' = no rigid condition at all.
 *
 * usage: lemma41 classes|grid [paper|loose|plain]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int NA, ND;
static int mat[7][7];
static int ne;
static int ea[7], ed[7];
static int cA[7], cD[7];
static int mode = 0; /* 0 paper, 1 loose, 2 plain */

static long long n_side_rej_weighted = 0;
static long long n_graphs = 0, n_label = 0, n_fail = 0, n_rigid_reject = 0, n_shortcut_mismatch = 0;
static long long cell_graphs[8][8], cell_label[8][8];

/* side check, literal.  nv vertices, c[], L mask, m[] from M.  returns 1 if OK. Also counts rigid rejects. */
static int side_ok_literal(int nv, const int *c, int L, const int *m, int *rigid_rejected) {
    int unc = 0, a = -1;
    for (int v = 0; v < nv; v++) if ((L >> v & 1) && m[v] == 0) { unc++; a = v; }
    *rigid_rejected = 0;
    if (unc >= 2) return 0;
    if (unc == 0) return 1;
    if (mode == 2) return 1;
    for (int K = 1; K < (1 << nv); K++) {
        if (K >> a & 1) continue;
        int good = 1, cs = 0;
        for (int v = 0; v < nv && good; v++) if (K >> v & 1) {
            if (m[v] < 1) good = 0;              /* K subset of V(M) */
            else if (m[v] != c[v]) good = 0;     /* every E-edge at K lies in M */
            else if ((L >> v & 1) && c[v] != 3) good = 0;
            cs += c[v];
        }
        if (!good) continue;
        if (mode == 1 || cs == 3 || cs == 4) { *rigid_rejected = 1; return 0; }
    }
    return 1;
}

static int side_ok_shortcut(int nv, const int *c, int L, const int *m) {
    int unc = 0, a = -1;
    for (int v = 0; v < nv; v++) if ((L >> v & 1) && m[v] == 0) { unc++; a = v; }
    if (unc >= 2) return 0;
    if (unc == 0) return 1;
    if (mode == 2) return 1;
    int mf = 0;
    for (int v = 0; v < nv; v++) if (v != a && m[v] >= 1 && m[v] == c[v] && (!(L >> v & 1) || c[v] == 3)) mf += m[v];
    if (mode == 1) return mf == 0;
    return mf <= 2;
}

/* enumerate admissible L masks for a side */
static int list_L(int nv, const int *c, int *out) {
    int cnt = 0, must = 0;
    for (int v = 0; v < nv; v++) if (c[v] == 3) must |= 1 << v;
    for (int L = 0; L < (1 << nv); L++) {
        if ((L & must) != must) continue;
        int b = 0;
        for (int v = 0; v < nv; v++) if (L >> v & 1) b += 3 - c[v];
        if (b <= 5) out[cnt++] = L;
    }
    return cnt;
}

static int Ms[35];
static void init_Ms(void) {
    int k = 0;
    for (int s = 0; s < 128; s++) if (__builtin_popcount(s) == 4) Ms[k++] = s;
}

static void process_graph(void) {
    ne = 0;
    for (int i = 0; i < NA; i++) cA[i] = 0;
    for (int j = 0; j < ND; j++) cD[j] = 0;
    for (int i = 0; i < NA; i++) for (int j = 0; j < ND; j++) if (mat[i][j]) { ea[ne] = i; ed[ne] = j; ne++; cA[i]++; cD[j]++; }
    if (ne != 7) { fprintf(stderr, "ne != 7\n"); exit(1); }
    static int LA[128], LD[128];
    int nla = list_L(NA, cA, LA), nld = list_L(ND, cD, LD);
    n_graphs++;
    cell_graphs[NA][ND]++;
    /* precompute m vectors */
    int mA[35][7], mD[35][7];
    for (int t = 0; t < 35; t++) {
        for (int i = 0; i < 7; i++) { mA[t][i] = 0; mD[t][i] = 0; }
        for (int e = 0; e < 7; e++) if (Ms[t] >> e & 1) { mA[t][ea[e]]++; mD[t][ed[e]]++; }
    }
    for (int yy = 0; yy < nld; yy++) for (int t = 0; t < 35; t++) { int rr; side_ok_literal(ND, cD, LD[yy], mD[t], &rr); if (rr) n_side_rej_weighted += nla; }
    for (int x = 0; x < nla; x++) {
        int okA[35];
        for (int t = 0; t < 35; t++) {
            int rr;
            okA[t] = side_ok_literal(NA, cA, LA[x], mA[t], &rr);
            if (rr) { n_rigid_reject++; n_side_rej_weighted += nld; }
            if (okA[t] != side_ok_shortcut(NA, cA, LA[x], mA[t])) n_shortcut_mismatch++;
        }
        for (int y = 0; y < nld; y++) {
            n_label++;
            cell_label[NA][ND]++;
            int found = 0;
            for (int t = 0; t < 35 && !found; t++) {
                if (!okA[t]) continue;
                int rr;
                int okD = side_ok_literal(ND, cD, LD[y], mD[t], &rr);
                if (okD != side_ok_shortcut(ND, cD, LD[y], mD[t])) n_shortcut_mismatch++;
                if (okD) found = 1;
            }
            if (!found) {
                n_fail++;
                if (n_fail <= 5) {
                    printf("FAIL NA=%d ND=%d LA=%x LD=%x edges:", NA, ND, LA[x], LD[y]);
                    for (int e = 0; e < 7; e++) printf(" %d-%d", ea[e], ed[e]);
                    printf("\n");
                }
            }
        }
    }
}

/* ---------- classes enumeration ---------- */
#define HMAX 200003
static unsigned long long htab[HMAX];
static int hused[HMAX];
static int rows[7];

static unsigned long long canon(void) {
    /* all permutations of rows; for each, column masks over NA bits; sort; encode; min */
    int perm[7];
    for (int i = 0; i < NA; i++) perm[i] = i;
    unsigned long long best = ~0ULL;
    /* Heap-free: iterate permutations with next_permutation */
    for (;;) {
        int col[7];
        for (int j = 0; j < ND; j++) {
            int msk = 0;
            for (int i = 0; i < NA; i++) if (rows[perm[i]] >> j & 1) msk |= 1 << i;
            col[j] = msk;
        }
        /* sort cols descending */
        for (int a = 0; a < ND; a++) for (int b = a + 1; b < ND; b++) if (col[b] > col[a]) { int t = col[a]; col[a] = col[b]; col[b] = t; }
        unsigned long long code = 0;
        for (int j = 0; j < ND; j++) code = code * 128ULL + (unsigned long long)col[j];
        if (code < best) best = code;
        /* next permutation */
        int k = NA - 2;
        while (k >= 0 && perm[k] >= perm[k + 1]) k--;
        if (k < 0) break;
        int l = NA - 1;
        while (perm[l] <= perm[k]) l--;
        int t = perm[k]; perm[k] = perm[l]; perm[l] = t;
        for (int a = k + 1, b = NA - 1; a < b; a++, b--) { t = perm[a]; perm[a] = perm[b]; perm[b] = t; }
    }
    return best * 64ULL + (unsigned long long)(NA * 8 + ND);
}

static int hinsert(unsigned long long key) {
    unsigned long long h = (key * 0x9E3779B97F4A7C15ULL) % HMAX;
    while (hused[h]) { if (htab[h] == key) return 0; h = (h + 1) % HMAX; }
    hused[h] = 1; htab[h] = key; return 1;
}

static void rec_rows(int i, int maxrow, int edges_left) {
    if (i == NA) {
        if (edges_left != 0) return;
        int colsum[7] = {0};
        for (int r = 0; r < NA; r++) for (int j = 0; j < ND; j++) if (rows[r] >> j & 1) colsum[j]++;
        for (int j = 0; j < ND; j++) if (colsum[j] < 1 || colsum[j] > 3) return;
        unsigned long long key = canon();
        if (!hinsert(key)) return;
        for (int r = 0; r < NA; r++) for (int j = 0; j < ND; j++) mat[r][j] = rows[r] >> j & 1;
        process_graph();
        return;
    }
    int rem_rows = NA - i;
    for (int msk = maxrow; msk >= 1; msk--) {
        int pc = __builtin_popcount(msk);
        if (pc > 3) continue;
        if (pc > edges_left - (rem_rows - 1)) continue;
        if (edges_left - pc > 3 * (rem_rows - 1)) continue;
        rows[i] = msk;
        rec_rows(i + 1, msk, edges_left - pc);
    }
}

/* ---------- grid enumeration (non-increasing row sums and column sums) ---------- */
static int rs[7], cs[7];
static int colleft[7];
static void rec_fill(int i) {
    if (i == NA) {
        for (int j = 0; j < ND; j++) if (colleft[j] != 0) return;
        process_graph();
        return;
    }
    /* choose a subset of columns of size rs[i] among columns with colleft > 0 */
    for (int msk = 0; msk < (1 << ND); msk++) {
        if (__builtin_popcount(msk) != rs[i]) continue;
        int ok = 1;
        for (int j = 0; j < ND; j++) if ((msk >> j & 1) && colleft[j] == 0) { ok = 0; break; }
        if (!ok) continue;
        for (int j = 0; j < ND; j++) { mat[i][j] = msk >> j & 1; colleft[j] -= mat[i][j]; }
        /* prune: remaining column demand must fit in remaining rows */
        int ok2 = 1;
        for (int j = 0; j < ND; j++) if (colleft[j] > NA - i - 1) ok2 = 0;
        if (ok2) rec_fill(i + 1);
        for (int j = 0; j < ND; j++) colleft[j] += mat[i][j];
    }
}
static void rec_vec(int *v, int n, int idx, int maxv, int left, void (*done)(void)) {
    if (idx == n) { if (left == 0) done(); return; }
    for (int x = maxv; x >= 1; x--) {
        if (x > left) continue;
        if (left - x > 3 * (n - idx - 1)) continue;
        if (left - x < (n - idx - 1)) continue;
        v[idx] = x;
        rec_vec(v, n, idx + 1, x, left - x, done);
    }
}
static void done_cs(void) {
    for (int j = 0; j < ND; j++) colleft[j] = cs[j];
    rec_fill(0);
}
static void done_rs(void) { rec_vec(cs, ND, 0, 3, 7, done_cs); }

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage\n"); return 1; }
    if (argc >= 3) { if (!strcmp(argv[2], "loose")) mode = 1; else if (!strcmp(argv[2], "plain")) mode = 2; }
    init_Ms();
    int grid = !strcmp(argv[1], "grid");
    for (NA = 3; NA <= 7; NA++) for (ND = 3; ND <= 7; ND++) {
        if (grid) rec_vec(rs, NA, 0, 3, 7, done_rs);
        else rec_rows(0, (1 << ND) - 1, 7);
    }
    printf("enum=%s mode=%s graphs=%lld labellings=%lld failures=%lld rigid_rejects(A side, per M)=%lld shortcut_mismatch=%lld side_rejects_weighted=%lld\n",
           grid ? "grid" : "classes", mode == 0 ? "paper" : mode == 1 ? "loose" : "plain",
           n_graphs, n_label, n_fail, n_rigid_reject, n_shortcut_mismatch, n_side_rej_weighted);
    printf("per (NA,ND) graphs:\n");
    for (int a = 3; a <= 7; a++) { for (int d = 3; d <= 7; d++) printf(" %6lld", cell_graphs[a][d]); printf("\n"); }
    return 0;
}
