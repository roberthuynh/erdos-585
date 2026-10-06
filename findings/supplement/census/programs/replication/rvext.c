/* rvext.c -- OUTPROC hook: extend each geng output G (n vertices) by one vertex v of minimum degree.
 * Reduction: if H (n+1 vertices, EF edges, MINDF <= deg <= 6, pair-free, every proper S with
 * |S| >= SPMIN sparse) exists and v is a minimum-degree vertex of H with t = deg v, then G = H - v
 * has EF - t edges, degrees >= t - 1, is pair-free and fully sparse, so geng (with rvprune) outputs
 * a copy of G. This hook tries every N with |N| = t = EF - e(G), N containing every vertex of
 * degree t - 1, every vertex of N of degree <= 5, and keeps H = G + v when every S containing v
 * with SPMIN <= |S| <= n is sparse and H has no pair through v. Survivors are written as graph6. */
#include "rvprune.c"

static long long ext_G = 0, ext_cand = 0, ext_sparse = 0, ext_pair = 0, ext_out = 0, ext_badt = 0;
static int ext_ready = 0, EXT_EF = 35, EXT_MINDF = 4;
static unsigned char ext_eT[1 << 16];

static void ext_write_g6(FILE *f, int N, const rvset *adj) {
    char buf[128];
    int pos = 0, bit = 0, cur = 0;
    buf[pos++] = (char)(63 + N);
    for (int j = 1; j < N; j++)
        for (int i = 0; i < j; i++) {
            cur = (cur << 1) | ((adj[i] >> j) & 1u);
            if (++bit == 6) { buf[pos++] = (char)(63 + cur); bit = 0; cur = 0; }
        }
    if (bit) { cur <<= (6 - bit); buf[pos++] = (char)(63 + cur); }
    buf[pos] = 0;
    fprintf(f, "%s\n", buf);
}

void rvext(FILE *f, graph *g, int n) {
    if (!ext_ready) {
        const char *s;
        if ((s = getenv("RV_EXT_EF"))) EXT_EF = atoi(s);
        if ((s = getenv("RV_EXT_MINDF"))) EXT_MINDF = atoi(s);
        if (!rv_ready) rv_setup();
        fprintf(stderr, "rvext: EF=%d MINDF=%d (sparsity SP=%d SPMIN=%d)\n", EXT_EF, EXT_MINDF, RV_SP, RV_SPMIN);
        ext_ready = 1;
    }
    ext_G++;
    if (n + 1 > 16) rv_die("rvext: n too large");
    rvset adj[32];
    int deg[32], e2 = 0;
    for (int i = 0; i < n; i++) {
        rvset a = 0;
        set *gi = GRAPHROW(g, i, 1);
        for (int j = 0; j < n; j++)
            if (ISELEMENT(gi, j)) a |= 1u << j;
        adj[i] = a;
        deg[i] = __builtin_popcount(a);
        e2 += deg[i];
    }
    int t = EXT_EF - e2 / 2;
    if (t < EXT_MINDF || t > 6 || t > n) { ext_badt++; return; }
    rvset F = 0, A = 0;
    for (int i = 0; i < n; i++) {
        if (deg[i] < t - 1) return; /* v would not be a minimum-degree vertex */
        if (deg[i] == t - 1) F |= 1u << i;
        else if (deg[i] <= 5) A |= 1u << i;
    }
    int nf = __builtin_popcount(F);
    if (nf > t) return;
    rvset full = (1u << n) - 1;
    ext_eT[0] = 0;
    for (rvset T = 1; T <= full; T++) {
        int low = __builtin_ctz(T);
        rvset rest = T & (T - 1);
        ext_eT[T] = (unsigned char)(ext_eT[rest] + __builtin_popcount(adj[low] & rest));
    }
    /* every X subset of A with |X| = t - nf */
    int need = t - nf;
    rvset X = 0;
    for (;;) {
        if (__builtin_popcount(X) == need) {
            rvset N = F | X;
            ext_cand++;
            int bad = 0;
            for (rvset T = 0; T <= full && !bad; T++) {
                int sz = __builtin_popcount(T) + 1;
                if (sz < RV_SPMIN || sz > n) continue; /* S = T + v, proper means |S| <= n */
                if (ext_eT[T] + __builtin_popcount(N & T) > 3 * sz - RV_SP) bad = 1;
            }
            if (bad) { ext_sparse++; }
            else {
                rvset adjH[32];
                for (int i = 0; i < n; i++) adjH[i] = adj[i] | (((N >> i) & 1u) ? (1u << n) : 0);
                adjH[n] = N;
                if (rv3_pair_through(n + 1, adjH, n)) ext_pair++;
                else { ext_out++; ext_write_g6(f, n + 1, adjH); fflush(f); }
            }
        }
        if (X == A) break;
        X = (X - A) & A; /* next subset of A */
    }
}

void rvsummary2(nauty_counter nout, double cpu) {
    rvsummary(nout, cpu);
    fprintf(stderr, "rvext: G=%lld badt=%lld cand=%lld sparse_rej=%lld pair_rej=%lld H_out=%lld\n", ext_G, ext_badt,
            ext_cand, ext_sparse, ext_pair, ext_out);
}
