/* PRUNE1 hook for nauty genbg: reject graphs containing a 4-regular subgraph.
 * genbg adds second-class vertices one at a time; vertex n1+n2-1 is the newest and the graph
 * without it already passed (genbg.c, PRUNE notes), so search only with that root. */
#include "gtools.h"
#include "q4core.h"
int q4prune_bg(graph *g, int *deg, int n1, int n2, int maxn2) {
    u32 G[32]; int n = n1 + n2;
    if (n < 5) return 0;
    for (int i = 0; i < n; i++) G[i] = __builtin_bitreverse32((u32)g[i]);
    return q4_rooted(G, n, n - 1, (n == 32) ? 0xffffffffu : ((1u << n) - 1));
}
