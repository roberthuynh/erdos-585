/* rvprune.c -- reviewer's PRUNE hook for geng (SMS-CENSUS-REVIEW replication of S10).
 *
 * geng builds each graph by adding vertices 0,1,2,... and calls PRUNE on every intermediate graph
 * (order 1..maxn); the call for order n implies the call for order n-1 passed. So for the graph
 * G_n on vertices 0..n-1 only structures through the newest vertex w = n-1 are new.
 *
 * Rejects G_n (returns 1) when, with SP and SPMIN from the environment (defaults 5 and 2):
 *   - RV_FULL=1 (default): some S containing w with SPMIN <= |S| and S != V(final graph) has
 *     e(S) > 3|S| - SP. (Every proper vertex set of a minimal counterexample is such a set.)
 *     RV_FULL=0: only S = V(G_n) for n < maxn is tested.
 *   - G_n has a pair through w (rvpair.h, certificate-checked).
 * Degree bounds and the final edge count are left to geng's own -d, -D and edge arguments. */
#include "gtools.h"
#include "rvpair.h"
#include "rvpair2.h"
#include "rvpair3.h"

static int rv_ready = 0, RV_SP = 5, RV_SPMIN = 2, RV_FULL = 1, RV_PAIRV = 3;
static long long rv_calls[34], rv_sparse_rej[34], rv_pair_rej[34];
static unsigned char rv_eT[1 << 16];

static void rv_setup(void) {
    const char *s;
    if ((s = getenv("RV_SP"))) RV_SP = atoi(s);
    if ((s = getenv("RV_SPMIN"))) RV_SPMIN = atoi(s);
    if ((s = getenv("RV_FULL"))) RV_FULL = atoi(s);
    if ((s = getenv("RV_PAIRV"))) RV_PAIRV = atoi(s);
    fprintf(stderr, "rvprune: SP=%d SPMIN=%d FULL=%d PAIRV=%d\n", RV_SP, RV_SPMIN, RV_FULL, RV_PAIRV);
    rv_ready = 1;
}

int rvprune(graph *g, int n, int maxn) {
    if (!rv_ready) rv_setup();
    if (n > 16) rv_die("n > 16 in rvprune");
    rv_calls[n]++;
    if (n < 2) return 0;
    rvset adj[32];
    for (int i = 0; i < n; i++) {
        rvset a = 0;
        set *gi = GRAPHROW(g, i, 1);
        for (int j = 0; j < n; j++)
            if (ISELEMENT(gi, j)) a |= 1u << j;
        adj[i] = a;
    }
    int w = n - 1;
    if (RV_FULL) {
        /* every S = T + w, T a subset of {0..n-2} */
        int nt = n - 1;
        rvset full = (1u << nt) - 1;
        rv_eT[0] = 0;
        for (rvset T = 1; T <= full; T++) {
            int low = __builtin_ctz(T);
            rvset rest = T & (T - 1);
            rv_eT[T] = (unsigned char)(rv_eT[rest] + __builtin_popcount(adj[low] & rest));
        }
        for (rvset T = 0; T <= full; T++) {
            int sz = __builtin_popcount(T) + 1;
            if (sz < RV_SPMIN) continue;
            if (n == maxn && T == full) continue; /* the whole final graph is not a proper set */
            int eS = rv_eT[T] + __builtin_popcount(adj[w] & T);
            if (eS > 3 * sz - RV_SP) { rv_sparse_rej[n]++; return 1; }
        }
    } else if (n < maxn && n >= RV_SPMIN) {
        int e2 = 0;
        for (int i = 0; i < n; i++) e2 += __builtin_popcount(adj[i]);
        if (e2 / 2 > 3 * n - RV_SP) { rv_sparse_rej[n]++; return 1; }
    }
    int has = RV_PAIRV == 1 ? rv_pair_through(n, adj, w) : RV_PAIRV == 2 ? rv2_pair_through(n, adj, w) : rv3_pair_through(n, adj, w);
    if (has) { rv_pair_rej[n]++; return 1; }
    return 0;
}

void rvsummary(nauty_counter nout, double cpu) {
    fprintf(stderr, "rvsummary: out=%llu cpu=%.2f pairs_verified=%lld max_pool=%lld\n",
            (unsigned long long)nout, cpu, rv_npairs_verified, rv_max_pool);
    for (int k = 1; k <= 32; k++)
        if (rv_calls[k])
            fprintf(stderr, "rvlevel %d calls %lld sparse_rej %lld pair_rej %lld\n", k, rv_calls[k],
                    rv_sparse_rej[k], rv_pair_rej[k]);
}
