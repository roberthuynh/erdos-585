/* h4prune.c -- PRUNE hook for nauty geng (method B, wave8/exb).

   Built into geng with -DPRUNE=h4prune -DSUMMARY=h4summary (see build.sh).
   geng builds each output graph by adding vertices 0, 1, 2, ... in order,
   every intermediate graph is an induced subgraph of its completions, and
   PRUNE(g, n, maxn) for n vertices is only called after the call for the
   first n - 1 vertices passed (geng.c, "PRUNE feature").  Containing a
   nonempty 4-regular subgraph is inherited by supergraphs, so rejecting
   such an intermediate graph loses no output graph without one.  A graph
   whose parent passed has a 4-regular subgraph only through the newest
   vertex n - 1, so only that vertex is searched.  Every rejection carries
   a certificate (an explicit 4-regular subgraph) checked inside h4.h.  */

#include "gtools.h"
#include "h4.h"

#if WORDSIZE != 32
#error "h4prune.c expects WORDSIZE 32"
#endif

static unsigned long long h4calls[H4MAXN + 1], h4cuts[H4MAXN + 1];

int h4prune(graph *g, int n, int maxn)
{
    h4set adj[H4MAXN];
    h4set all, K;
    int i, v = n - 1;

    (void)maxn;
    ++h4calls[n];
    if (n < 1) return 0;
    for (i = 0; i < n; ++i) adj[i] = __builtin_bitreverse32((uint32_t)g[i]);
    if (H4POP(adj[v]) < 4) return 0;
    all = (n == 32) ? ~(h4set)0 : (H4BIT(n) - 1);
    K = h4_core4(adj, n, all);
    if (!(K & H4BIT(v))) return 0;
    if (h4_through(adj, n, K, v, NULL)) {
        ++h4cuts[n];
        return 1;
    }
    return 0;
}

void h4summary(nauty_counter nout, double cpu)
{
    int n;
    fprintf(stderr, ">H nout=%llu cpu=%.2f nodes=%llu\n",
            (unsigned long long)nout, cpu, h4_nodes);
    for (n = 1; n <= H4MAXN; ++n)
        if (h4calls[n])
            fprintf(stderr, ">H level %d: prune calls %llu, cut %llu\n", n,
                    h4calls[n], h4cuts[n]);
}
