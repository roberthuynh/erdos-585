/* q4prune.c: PRUNE hook for nauty geng (compile geng.c with -DPRUNE=q4prune
 * -DMAXN=WORDSIZE -DWORDSIZE=32). Rejects any graph that contains a 4-regular
 * subgraph. geng builds each graph by adding vertex n-1 to a graph that already
 * passed PRUNE, so a 4-regular subgraph of the new graph must contain vertex
 * n-1; we search only with that root. "No 4-regular subgraph" is inherited by
 * induced subgraphs, so the pruning is sound and the output is exactly the set
 * of graphs (within geng's degree and edge bounds) with no 4-regular subgraph.
 * Optional extra test Q4FULLCHECK: also run the full test on final graphs. */
#include "gtools.h"
#include "q4core.h"

long long q4p_calls = 0, q4p_rejects = 0;

int q4prune(graph *g, int n, int maxn) {
    u32 G[32];
    q4p_calls++;
    if (n < 5) return 0;
    for (int i = 0; i < n; i++) G[i] = __builtin_bitreverse32((u32)g[i]);
    int has = q4_rooted(G, n, n - 1, (n == 32) ? 0xffffffffu : ((1u << n) - 1));
#ifdef Q4FULLCHECK
    if (!has && n == maxn && q4_any(G, n)) {
        fprintf(stderr, "Q4FULLCHECK MISMATCH\n"); exit(3);
    }
#endif
    if (has) q4p_rejects++;
    return has;
}

void q4summary(nauty_counter nout, double cpu) {
    fprintf(stderr, ">Q4 prune calls %lld rejects %lld\n", q4p_calls, q4p_rejects);
}
