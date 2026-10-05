/* pairc.c -- exact test for "two edge-disjoint cycles on the same vertex set" in simple graphs.
 *
 * Reads graph6 lines on stdin (n <= 30). For each graph decides whether a pair exists:
 *   exists S, a Hamilton cycle C1 of G[S], and a Hamilton cycle C2 of G[S] - E(C1).
 * The search is complete: every vertex subset S with min degree >= 4 in G[S] is tried (smallest
 * first), every Hamilton cycle C1 of G[S] through min(S) is enumerated by DFS, and the residual
 * graph is searched for a Hamilton cycle by DFS.
 *
 * Output modes (argv[1]):
 *   f  print the graph6 line of every pair-FREE graph            (default)
 *   p  print the graph6 line of every graph WITH a pair
 *   w  print "<graph6> NONE" or "<graph6> PAIR S=<mask> C1=<v,...> C2=<v,...>"
 * A summary line goes to stderr.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint32_t mask;
static int n;
static mask adj[32], res[32];
static int path1[32], path2[32], len1, len2;
static mask S;
static int s0, ssize;
static int spanning_only = 0;

static inline int pc(mask x) { return __builtin_popcount(x); }

static int ham2(int cur, mask visited, int depth) {
    path2[depth - 1] = cur;
    if (depth == ssize) return (res[cur] >> s0) & 1;
    mask cand = res[cur] & S & ~visited;
    /* prune: an unvisited vertex needs two residual neighbors that are unvisited, cur or s0 */
    mask un = S & ~visited;
    mask ok = un | (1u << cur) | (1u << s0);
    for (mask t = un; t; t &= t - 1) {
        int v = __builtin_ctz(t);
        if (pc(res[v] & ok) < 2) return 0;
    }
    for (; cand; cand &= cand - 1) {
        int v = __builtin_ctz(cand);
        if (ham2(v, visited | (1u << v), depth + 1)) return 1;
    }
    return 0;
}

static int ham1(int cur, mask visited, int depth) {
    path1[depth - 1] = cur;
    if (depth == ssize) {
        if (!((adj[cur] >> s0) & 1)) return 0;
        if (path1[1] > cur) return 0; /* each undirected cycle once */
        for (mask t = S; t; t &= t - 1) {
            int v = __builtin_ctz(t);
            res[v] = adj[v] & S;
        }
        for (int i = 0; i < ssize; i++) {
            int a = path1[i], b = path1[(i + 1) % ssize];
            res[a] &= ~(1u << b);
            res[b] &= ~(1u << a);
        }
        len1 = ssize;
        if (ham2(s0, 1u << s0, 1)) { len2 = ssize; return 1; }
        return 0;
    }
    mask cand = adj[cur] & S & ~visited;
    for (; cand; cand &= cand - 1) {
        int v = __builtin_ctz(cand);
        if (ham1(v, visited | (1u << v), depth + 1)) return 1;
    }
    return 0;
}

static int has_pair(void) {
    mask full = (n == 32) ? 0xffffffffu : ((1u << n) - 1);
    /* 4-core of the whole graph: S must lie inside it */
    mask core = full;
    for (int changed = 1; changed;) {
        changed = 0;
        for (mask t = core; t; t &= t - 1) {
            int v = __builtin_ctz(t);
            if (pc(adj[v] & core) < 4) { core &= ~(1u << v); changed = 1; }
        }
    }
    int cs = pc(core);
    if (cs < 5) return 0;
    if (spanning_only) { /* mode for connected 4-regular graphs: the only candidate S is everything */
        if (core != full) return 0;
        S = full; ssize = n; s0 = 0;
        return ham1(0, 1u, 1);
    }
    int idx[32], k = 0;
    for (mask t = core; t; t &= t - 1) idx[k++] = __builtin_ctz(t);
    for (int size = 5; size <= cs; size++) {
        /* all subsets of the core of this size, via Gosper's hack on k-bit masks */
        uint64_t sub = (1ull << size) - 1, lim = 1ull << cs;
        while (sub < lim) {
            mask T = 0;
            for (uint64_t t = sub; t; t &= t - 1) T |= 1u << idx[__builtin_ctzll(t)];
            int good = 1;
            for (mask t = T; t; t &= t - 1) {
                int v = __builtin_ctz(t);
                if (pc(adj[v] & T) < 4) { good = 0; break; }
            }
            if (good) {
                S = T; ssize = size; s0 = __builtin_ctz(T);
                if (ham1(s0, 1u << s0, 1)) return 1;
            }
            uint64_t c = sub & (~sub + 1), r = sub + c;
            sub = (((r ^ sub) >> 2) / c) | r;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    char mode = argc > 1 ? argv[1][0] : 'f';
    if (argc > 2 && argv[2][0] == 'H') spanning_only = 1; /* test S = V only */
    static char line[4096];
    long total = 0, withpair = 0;
    while (fgets(line, sizeof line, stdin)) {
        if (line[0] == '>' || line[0] == '\n') continue;
        size_t L = strlen(line);
        while (L && (line[L - 1] == '\n' || line[L - 1] == '\r')) line[--L] = 0;
        n = line[0] - 63;
        if (n < 1 || n > 30) { fprintf(stderr, "bad n\n"); return 2; }
        memset(adj, 0, sizeof adj);
        int bit = 0, pos = 1;
        for (int j = 1; j < n; j++)
            for (int i = 0; i < j; i++) {
                int ch = line[pos] - 63;
                if ((ch >> (5 - bit)) & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
                if (++bit == 6) { bit = 0; pos++; }
            }
        total++;
        int r = has_pair();
        withpair += r;
        if (mode == 'f' && !r) puts(line);
        else if (mode == 'p' && r) puts(line);
        else if (mode == 'w') {
            if (!r) printf("%s NONE\n", line);
            else {
                printf("%s PAIR S=%u C1=", line, S);
                for (int i = 0; i < len1; i++) printf("%d%s", path1[i], i + 1 < len1 ? "," : "");
                printf(" C2=");
                for (int i = 0; i < len2; i++) printf("%d%s", path2[i], i + 1 < len2 ? "," : "");
                printf("\n");
            }
        }
    }
    fprintf(stderr, "graphs=%ld with_pair=%ld pair_free=%ld\n", total, withpair, total - withpair);
    return 0;
}
