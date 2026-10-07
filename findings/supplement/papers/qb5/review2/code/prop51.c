/* prop51.c -- referee's own check of PAPER2 Proposition 5.1, exhaustive part (blocks <= 16).
 *
 * Input: graph6 lines of 2-block graphs X from `genbg -q -d6:0 -D6:6 c c+2 6c:6c`:
 * vertices 0..c-1 = C (degree 6, all neighbours in A), c..2c+1 = A.
 * For every graph:
 *   - d_a = deg_X(a); B1 needs d_a >= 3;
 *   - sparsity inside X: e(S) <= 3|S| - 6 for every S subset of X with |S| >= 3;
 *   - L_A = {a : d_a = 3};
 *   - every A1 subset of A with |A1| <= |A| - 2 and dem_X(A1) > |A1 & L_A| is a "candidate";
 *     dem_X(A1) = 4|A1| - sum_c min(4, e(c, A1));
 *   - a candidate is relevant if, for some p in T = A - A1 and some cut vector allowed by
 *     PAPER2 §1.2 (c_a in [max(0, delta_a - 2), min(3, delta_a)], sum c_a = 7),
 *     dem_X(A1) + c(T - p) >= 5.  The max of c(U) over allowed vectors is
 *     min(sum_U hi, 7 - sum_{A-U} lo) when sum lo <= 7 <= sum hi.
 *   - orbit count: |Aut| (side-preserving) = #{sigma in Sym(A) preserving the multiset of
 *     C-neighbourhoods} * prod(mult!); prints sum of c!(c+2)!/|Aut| for comparison with the
 *     labelled count (completeness check of the generator).
 * Usage: genbg ... | ./prop51 c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int c, na, n;
static int adj[32];          /* adjacency bitmask over all n vertices */
static int row[16];          /* C-vertex neighbourhood as bitmask over A (bit i = A-vertex i) */
static unsigned char ecount[1 << 16];

static long long ng = 0, ng_ok = 0, ncand = 0, nrel = 0, ninfeas = 0;
static long double orbit_sum = 0.0L;
static long long cand_per_k[4] = {0};

/* automorphism enumeration */
static int codeg[16][16], degA[16];
static int sigma[16], used[16];
static long long autcount;
static int sorted_rows[16];

static int cmp_int(const void *x, const void *y) { return (*(const int *)x) - (*(const int *)y); }

static void aut_rec(int i) {
    if (i == na) {
        int r[16];
        for (int k = 0; k < c; k++) {
            int m = 0;
            for (int a = 0; a < na; a++) if (row[k] >> a & 1) m |= 1 << sigma[a];
            r[k] = m;
        }
        qsort(r, c, sizeof(int), cmp_int);
        for (int k = 0; k < c; k++) if (r[k] != sorted_rows[k]) return;
        autcount++;
        return;
    }
    for (int b = 0; b < na; b++) {
        if (used[b] || degA[b] != degA[i]) continue;
        int ok = 1;
        for (int j = 0; j < i; j++) if (codeg[j][i] != codeg[sigma[j]][b]) { ok = 0; break; }
        if (!ok) continue;
        used[b] = 1; sigma[i] = b;
        aut_rec(i + 1);
        used[b] = 0;
    }
}

static long double factl(int k) { long double f = 1; for (int i = 2; i <= k; i++) f *= i; return f; }

static void process(const char *s) {
    int len = (int)strlen(s);
    while (len > 0 && (s[len - 1] == '\n' || s[len - 1] == '\r')) len--;
    n = s[0] - 63;
    if (n != 2 * c + 2) { fprintf(stderr, "bad n %d\n", n); exit(1); }
    memset(adj, 0, sizeof(adj));
    int bit = 0;
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++) {
            int byte = 1 + bit / 6, off = 5 - bit % 6;
            if (byte < len && (((s[byte] - 63) >> off) & 1)) { adj[i] |= 1 << j; adj[j] |= 1 << i; }
            bit++;
        }
    ng++;
    /* structure: C = 0..c-1 degree 6 into A; A = c..n-1 */
    for (int k = 0; k < c; k++) {
        if (__builtin_popcount(adj[k]) != 6) { fprintf(stderr, "C degree\n"); exit(1); }
        if (adj[k] & ((1 << c) - 1)) { fprintf(stderr, "C-C edge\n"); exit(1); }
        row[k] = adj[k] >> c;
    }
    int d[16];
    for (int a = 0; a < na; a++) {
        if (adj[c + a] >> c) { fprintf(stderr, "A-A edge\n"); exit(1); }
        d[a] = __builtin_popcount(adj[c + a]);
        if (d[a] > 6) { fprintf(stderr, "A degree > 6\n"); exit(1); }
    }
    /* orbit count (all graphs) */
    for (int a = 0; a < na; a++) {
        degA[a] = d[a];
        for (int b = 0; b < na; b++) codeg[a][b] = __builtin_popcount(adj[c + a] & adj[c + b]);
    }
    for (int k = 0; k < c; k++) sorted_rows[k] = row[k];
    qsort(sorted_rows, c, sizeof(int), cmp_int);
    autcount = 0;
    memset(used, 0, sizeof(used));
    aut_rec(0);
    long double mult = 1;
    for (int k = 0; k < c;) {
        int j = k;
        while (j < c && sorted_rows[j] == sorted_rows[k]) j++;
        mult *= factl(j - k);
        k = j;
    }
    orbit_sum += factl(c) * factl(na) / ((long double)autcount * mult);

    /* B1 */
    for (int a = 0; a < na; a++) if (d[a] < 3) return;
    /* sparsity inside X */
    int full = 1 << n;
    ecount[0] = 0;
    for (int m = 1; m < full; m++) {
        int v = __builtin_ctz(m);
        int rest = m & (m - 1);
        ecount[m] = ecount[rest] + __builtin_popcount(adj[v] & rest);
        int sz = __builtin_popcount(m);
        if (sz >= 3 && ecount[m] > 3 * sz - 6) return;
    }
    ng_ok++;
    int LA = 0;
    for (int a = 0; a < na; a++) if (d[a] == 3) LA |= 1 << a;
    int lo[16], hi[16], sumlo = 0, sumhi = 0;
    for (int a = 0; a < na; a++) {
        int del = 6 - d[a];
        lo[a] = del - 2 > 0 ? del - 2 : 0;
        hi[a] = del < 3 ? del : 3;
        sumlo += lo[a]; sumhi += hi[a];
    }
    int feasible = (sumlo <= 7 && 7 <= sumhi);
    if (!feasible) ninfeas++;
    for (int A1 = 0; A1 < (1 << na); A1++) {
        int sz = __builtin_popcount(A1);
        if (sz > na - 2) continue;
        int dem = 4 * sz;
        for (int k = 0; k < c; k++) { int e = __builtin_popcount(row[k] & A1); dem -= e < 4 ? e : 4; }
        if (dem <= __builtin_popcount(A1 & LA)) continue;
        ncand++;
        if (dem >= 1 && dem <= 3) cand_per_k[dem]++; else cand_per_k[0]++;
        if (!feasible) continue;
        int T = ((1 << na) - 1) & ~A1;
        for (int p = 0; p < na; p++) {
            if (!(T >> p & 1)) continue;
            int U = T & ~(1 << p);
            int shi = 0, slo_out = 0;
            for (int a = 0; a < na; a++) {
                if (U >> a & 1) shi += hi[a]; else slo_out += lo[a];
            }
            int maxc = shi < 7 - slo_out ? shi : 7 - slo_out;
            if (dem + maxc >= 5) {
                nrel++;
                printf("RELEVANT graph#%lld A1=%d p=%d dem=%d maxc=%d\n", ng, A1, p, dem, maxc);
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: prop51 c\n"); return 1; }
    c = atoi(argv[1]);
    na = c + 2;
    char buf[256];
    while (fgets(buf, sizeof buf, stdin)) if (buf[0] >= 63) process(buf);
    /* labelled count by inclusion-exclusion: each C-vertex picks a 6-subset of A, A-degree <= 6 */
    long double lab = 0;
    for (int j = 0; j <= 6 && j <= na; j++) {
        long double binom_na_j = factl(na) / (factl(j) * factl(na - j));
        long double ways = 0;
        if (na - j >= 6 - j) ways = factl(na - j) / (factl(6 - j) * factl(na - 6));
        long double term = binom_na_j;
        for (int k = 0; k < c; k++) term *= ways;
        /* only vertices forced to degree c count as violations when c >= 7 */
        if (j == 0) lab += term;
        else if (c >= 7) lab += (j % 2 ? -term : term);
    }
    printf("c=%d graphs=%lld sparse_and_d>=3=%lld candidates=%lld (k=1:%lld k=2:%lld k=3:%lld other:%lld) "
           "relevant=%lld infeasible_cut_vectors=%lld\n",
           c, ng, ng_ok, ncand, cand_per_k[1], cand_per_k[2], cand_per_k[3], cand_per_k[0], nrel, ninfeas);
    printf("c=%d orbit_sum=%.1Lf labelled_count=%.1Lf\n", c, orbit_sum, lab);
    return 0;
}
