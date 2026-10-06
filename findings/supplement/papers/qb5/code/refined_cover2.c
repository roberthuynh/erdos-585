/* refined_cover2.c (lane qb5, round 3; NOTES.md section 7.4): second, independent program for the
 * refined covering lemma.  No code shared with refined_cover.py, no nauty.
 *
 * Enumeration: for every pair of degree sequences (r_1 >= ... >= r_a), (s_1 >= ... >= s_b) of 7 with parts
 * in {1, 2, 3}, every 0/1 matrix with these row and column sums (rows = A-ends, columns = D-ends, filled
 * row by row).  This contains every 7-edge bipartite graph with degrees <= 3 up to isomorphism.
 * Labellings: L_A = (rows of sum 3) u any subset of the other rows with sum over L_A of (3 - r) <= 5; same
 * for columns.  Every non-L end has def = 0 (worst case for (b)).
 * For a 4-set M of the 7 edges, side A is bad iff
 *   (a) >= 2 vertices of L_A have no M-edge, or
 *   (b) exactly one a in L_A has no M-edge and some K among the other rows with def 0 (not in L_A, or
 *       sum 3) whose edges all lie in M has total degree 3 or 4.
 * Same for D.  Claim: every labelling has an M bad on neither side.
 * Mode argument "plain" drops (b).  Prints counts.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int na, nb, rs[8], cs[8];
static int mat[8][8];
static int eA[7], eD[7];
static long nmat = 0, nlab = 0, nfail = 0;
static int plain = 0, loose = 0;
static long nbadb = 0;

static int side_bad(int Msk, const int *end, int nv, const int *deg, int L) {
    /* end[i]: endpoint (on this side) of edge i; deg[v]; L bitmask */
    int hit = 0, full[8] = {0}, inM[8] = {0};
    for (int i = 0; i < 7; i++) {
        if (Msk >> i & 1) { hit |= 1 << end[i]; inM[end[i]]++; }
    }
    for (int v = 0; v < nv; v++) full[v] = (inM[v] == deg[v]);
    int miss = L & ~hit;
    int nm = __builtin_popcount(miss);
    if (nm >= 2) return 1;
    if (nm == 1 && !plain) {
        int a = __builtin_ctz(miss);
        int F[8], nf = 0;
        for (int v = 0; v < nv; v++) {
            if (v == a || !(hit >> v & 1) || !full[v]) continue;
            int def0 = !(L >> v & 1) || deg[v] == 3;
            if (def0) F[nf++] = deg[v];
        }
        for (int s = 1; s < (1 << nf); s++) {
            int t = 0;
            for (int j = 0; j < nf; j++) if (s >> j & 1) t += F[j];
            if (t == 3 || t == 4 || (loose && t >= 1)) { nbadb++; return 1; }
        }
    }
    return 0;
}

static void check_matrix(void) {
    int k = 0;
    for (int i = 0; i < na; i++) for (int j = 0; j < nb; j++) if (mat[i][j]) { eA[k] = i; eD[k] = j; k++; }
    if (k != 7) { fprintf(stderr, "bad edge count\n"); exit(1); }
    nmat++;
    int Ms[35], nM = 0;
    for (int s = 0; s < 128; s++) if (__builtin_popcount(s) == 4) Ms[nM++] = s;
    /* labellings */
    int forcedA = 0, forcedD = 0;
    for (int i = 0; i < na; i++) if (rs[i] == 3) forcedA |= 1 << i;
    for (int j = 0; j < nb; j++) if (cs[j] == 3) forcedD |= 1 << j;
    for (int LA = 0; LA < (1 << na); LA++) {
        if ((LA & forcedA) != forcedA) continue;
        int bud = 0;
        for (int i = 0; i < na; i++) if (LA >> i & 1) bud += 3 - rs[i];
        if (bud > 5) continue;
        int badA[35];
        for (int t = 0; t < nM; t++) badA[t] = side_bad(Ms[t], eA, na, rs, LA);
        for (int LD = 0; LD < (1 << nb); LD++) {
            if ((LD & forcedD) != forcedD) continue;
            int bd = 0;
            for (int j = 0; j < nb; j++) if (LD >> j & 1) bd += 3 - cs[j];
            if (bd > 5) continue;
            nlab++;
            int ok = 0;
            for (int t = 0; t < nM && !ok; t++)
                if (!badA[t] && !side_bad(Ms[t], eD, nb, cs, LD)) ok = 1;
            if (!ok) {
                nfail++;
                if (nfail <= 10) {
                    printf("FAIL rows");
                    for (int i = 0; i < na; i++) { printf(" ["); for (int j = 0; j < nb; j++) printf("%d", mat[i][j]); printf("]"); }
                    printf(" LA %d LD %d\n", LA, LD);
                }
            }
        }
    }
}

static int colrem[8];
static void fill(int i) {
    if (i == na) {
        for (int j = 0; j < nb; j++) if (colrem[j]) return;
        check_matrix();
        return;
    }
    /* choose a subset of columns of size rs[i] with colrem > 0 */
    for (int s = 0; s < (1 << nb); s++) {
        if (__builtin_popcount(s) != rs[i]) continue;
        int ok = 1;
        for (int j = 0; j < nb; j++) if ((s >> j & 1) && colrem[j] == 0) { ok = 0; break; }
        if (!ok) continue;
        /* remaining rows must be able to finish the columns: sum check */
        for (int j = 0; j < nb; j++) { mat[i][j] = s >> j & 1; colrem[j] -= mat[i][j]; }
        int remcols = 0, remrows = 0, feas = 1;
        for (int j = 0; j < nb; j++) { remcols += colrem[j]; if (colrem[j] > na - 1 - i) feas = 0; }
        for (int r = i + 1; r < na; r++) remrows += rs[r];
        if (feas && remcols == remrows) fill(i + 1);
        for (int j = 0; j < nb; j++) colrem[j] += mat[i][j];
    }
}

/* partitions of 7 into parts 1..3, non-increasing */
static int parts[64][8], plen[64], np = 0;
static void gen(int rem, int maxp, int *cur, int len) {
    if (rem == 0) { memcpy(parts[np], cur, sizeof(int) * len); plen[np] = len; np++; return; }
    for (int p = (maxp < rem ? maxp : rem); p >= 1; p--) { cur[len] = p; gen(rem - p, p, cur, len + 1); }
}

int main(int argc, char **argv) {
    plain = argc > 1 && !strcmp(argv[1], "plain");
    loose = argc > 1 && !strcmp(argv[1], "loose");
    int cur[8];
    gen(7, 3, cur, 0);
    for (int x = 0; x < np; x++) for (int y = 0; y < np; y++) {
        na = plen[x]; nb = plen[y];
        memcpy(rs, parts[x], sizeof(int) * na); memcpy(cs, parts[y], sizeof(int) * nb);
        for (int j = 0; j < nb; j++) colrem[j] = cs[j];
        memset(mat, 0, sizeof mat);
        fill(0);
    }
    printf("mode %s: degree-sequence pairs %d, matrices %ld, labellings %ld, failures %ld, side-bad via (b) %ld\n",
           plain ? "plain" : (loose ? "loose (sensitivity: any K)" : "refined"), np * np, nmat, nlab, nfail, nbadb);
    return 0;
}
