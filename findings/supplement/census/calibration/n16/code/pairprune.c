/* pairprune.c -- geng PRUNE hook and standalone decider, reg5n16 lane (Erdos 585).
 *
 * A pair is two edge-disjoint cycles on the same vertex set S. Graphs here have max degree <= 5
 * and at most 32 vertices (asserted).
 *
 * pair_through(r): is there a pair whose vertex set S contains r?
 *   1. S must lie in the 4-core of G (every vertex of S has >= 4 neighbours in S).
 *   2. Every S containing r with min degree >= 4 in G[S] is enumerated exactly once by a closure
 *      search: a processed vertex v of S fixes all its neighbours (degree 4: all in S; degree 5: all
 *      in S, or exactly one chosen neighbour out of S). Neighbours of processed vertices are always
 *      decided, so later choices never change a processed vertex's count.
 *   3. For each S: the two cycles C1, C2 use exactly 4 edges at every vertex of S, so the unused edges
 *      of G[S] form a perfect matching M of the degree-5 vertices of G[S]. Every such M is
 *      enumerated, F = G[S] - M is 4-regular, and F is tested for a decomposition into two
 *      Hamilton cycles: the red cycle is the one through the edge r-a (a = least F-neighbour of r),
 *      walked from r to a, enumerated by DFS; the blue edges F - red must form one cycle on S.
 *      Pruning: every unvisited vertex keeps >= 2 possible red edges; no blue cycle may close
 *      among interior path vertices (such a cycle misses r).
 *
 * PRUNE mode (compile with -DPRUNE=pairprune -DSUMMARY=pairsummary): geng builds graphs by adding
 * vertices 0,1,2,... and calls PRUNE(g,n,maxn) only after the call for the induced parent on
 * vertices 0..n-2 passed, so a new pair must contain vertex n-1. Pair-freeness is closed under
 * induced subgraphs, so the output is exactly the pair-free graphs geng would otherwise output.
 * When geng runs with -d5 -D5 (5-regular target) one counting test is added: the k-vertex
 * intermediate graph sends c = 5k - 2e edges to the R = maxn - k later vertices, which carry
 * e(R) <= R(R-1)/2 inner edges, so c >= 5R - R(R-1) is necessary for completion.
 *
 * Standalone mode (-DSTANDALONE): reads graph6 lines, decides "has a pair" as OR over r of
 * pair_through(r). Modes: f (print pair-free lines), p (print lines with a pair),
 * w (print "<g6> PAIR S=<mask> C1=... C2=..." or "<g6> NONE"). Summary on stderr.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifndef STANDALONE
#include "gtools.h"
#endif

typedef uint32_t msk;
static msk A[32];          /* adjacency of the whole graph */
static int NV;             /* number of vertices */

static inline int pc(msk x) { return __builtin_popcount(x); }
static inline int lo(msk x) { return __builtin_ctz(x); }
#define BIT(i) (1u << (i))

/* ---------------- Hamilton decomposition of the 4-regular graph F on SS ---------------- */
static msk F[32], SS;
static int ss, R0;
static int path[32], pos[32];
static int found;
static msk wit_S;
static int wit_c1[32], wit_c2[32];

static msk blue_of_interior(int w) {
    int i = pos[w];
    return F[w] & ~(BIT(path[i - 1]) | BIT(path[i + 1]));
}

static int finish_cycle(void) {
    /* path[0..ss-1] is a red Hamilton cycle (path[ss-1] adjacent to R0). Check blue = F - red. */
    msk red[32];
    for (msk t = SS; t; t &= t - 1) red[lo(t)] = 0;
    for (int i = 0; i < ss; i++) {
        int x = path[i], y = path[(i + 1) % ss];
        red[x] |= BIT(y);
        red[y] |= BIT(x);
    }
    int prev = -1, cur = R0, cnt = 0;
    do {
        msk b = F[cur] & ~red[cur];
        if (pc(b) != 2) return 0; /* cannot happen for 4-regular F; defensive */
        int x = lo(b);
        int nxt = (x != prev) ? x : lo(b & (b - 1));
        wit_c2[cnt] = cur;
        prev = cur;
        cur = nxt;
        cnt++;
    } while (cur != R0 && cnt <= ss);
    if (cur == R0 && cnt == ss) {
        wit_S = SS;
        for (int i = 0; i < ss; i++) wit_c1[i] = path[i];
        return 1;
    }
    return 0;
}

static int red_dfs(int cur, msk vis, int depth) {
    /* path[0..depth-1] placed, path[depth-1] == cur */
    if (depth == ss) {
        if (!((F[cur] >> R0) & 1)) return 0;
        return finish_cycle();
    }
    msk un = SS & ~vis;
    msk ok = un | BIT(cur) | BIT(R0);
    for (msk t = un; t; t &= t - 1) {
        int u = lo(t);
        if (pc(F[u] & ok) < 2) return 0;
    }
    for (msk cand = F[cur] & un; cand; cand &= cand - 1) {
        int v = lo(cand);
        path[depth] = v;
        pos[v] = depth;
        if (depth >= 2) {
            /* cur (= path[depth-1], index >= 1) is now interior: its blue edges are fixed. Walk the
             * blue chain from cur through interior vertices; a return to cur is a blue cycle that
             * avoids R0, hence not Hamilton. */
            int prev = cur, x = lo(blue_of_interior(cur)), bad = 0;
            for (int steps = 0; steps <= ss; steps++) {
                if (x == cur) { bad = 1; break; }
                if (x == R0 || x == v || !((vis >> x) & 1)) break;
                msk b = blue_of_interior(x) & ~BIT(prev);
                prev = x;
                x = lo(b);
            }
            if (bad) continue;
        }
        if (red_dfs(v, vis | BIT(v), depth + 1)) return 1;
    }
    return 0;
}

static int ham_decomp(void) {
    /* F is 4-regular on SS, R0 in SS */
    int a = lo(F[R0]);
    path[0] = R0; pos[R0] = 0;
    path[1] = a; pos[a] = 1;
    return red_dfs(a, BIT(R0) | BIT(a), 2);
}

static int match_dfs(msk rem) {
    /* rem: degree-5 vertices of G[S] still unmatched */
    if (!rem) return ham_decomp();
    int v = lo(rem);
    for (msk c = F[v] & rem & ~BIT(v); c; c &= c - 1) {
        int u = lo(c);
        F[v] &= ~BIT(u); F[u] &= ~BIT(v);
        int r = match_dfs(rem & ~BIT(v) & ~BIT(u));
        F[v] |= BIT(u); F[u] |= BIT(v);
        if (r) return 1;
    }
    return 0;
}

static unsigned long long n_sets, n_matchsets;

static int test_S(msk S) {
    n_sets++;
    msk d5 = 0;
    for (msk t = S; t; t &= t - 1) {
        int v = lo(t);
        F[v] = A[v] & S;
        int d = pc(F[v]);
        if (d == 5) d5 |= BIT(v);
        else if (d != 4) { fprintf(stderr, "test_S: degree %d in S (max degree > 5?)\n", d); exit(3); }
    }
    if (pc(d5) & 1) return 0;
    n_matchsets++;
    SS = S; ss = pc(S);
    return match_dfs(d5);
}

static void enum_S(msk In, msk Out, msk todo) {
    if (found) return;
    if (!todo) { if (test_S(In)) found = 1; return; }
    int v = lo(todo);
    todo &= todo - 1;
    msk nb = A[v];
    int slack = pc(nb) - 4 - pc(nb & Out);
    if (slack < 0) return;
    msk fr = nb & ~In & ~Out;
    enum_S(In | fr, Out, todo | fr);           /* all undecided neighbours in S */
    if (slack >= 1) {                           /* slack is at most 1 when max degree <= 5 */
        for (msk t = fr; t && !found; t &= t - 1) {
            int u = lo(t);
            msk add = fr & ~BIT(u);
            enum_S(In | add, Out | BIT(u), todo | add);
        }
    }
}

static int pair_through(int r) {
    msk all = (NV == 32) ? 0xffffffffu : (BIT(NV) - 1);
    for (int v = 0; v < NV; v++)
        if (pc(A[v]) > 5) { fprintf(stderr, "max degree > 5 not supported\n"); exit(3); }
    msk core = all;
    for (int ch = 1; ch;) {
        ch = 0;
        for (msk t = core; t; t &= t - 1) {
            int v = lo(t);
            if (pc(A[v] & core) < 4) { core &= ~BIT(v); ch = 1; }
        }
    }
    if (!((core >> r) & 1)) return 0;
    found = 0;
    R0 = r;
    enum_S(BIT(r), all & ~core, BIT(r));
    return found;
}

#ifndef STANDALONE
/* ---------------- geng hook ---------------- */
extern int TLS_ATTR geng_mindeg, geng_maxdeg;
static unsigned long long calls[33], rej_pair[33], rej_count[33];
#ifdef TIMING
#include <mach/mach_time.h>
static unsigned long long ticks[33];
#endif

int pairprune(graph *g, int n, int maxn) {
    NV = n;
    int e2 = 0;
    for (int i = 0; i < n; i++) {
        msk m = 0;
        setword w = g[i];
        while (w) {
            int j = FIRSTBITNZ(w);
            w ^= bit[j];
            m |= BIT(j);
        }
        A[i] = m;
        e2 += pc(m);
    }
    calls[n]++;
    if (geng_mindeg == 5 && geng_maxdeg == 5) {
        int R = maxn - n;
        int c = 5 * n - e2;            /* e2 = 2e */
        if (c > 5 * R || c < 5 * R - R * (R - 1)) { rej_count[n]++; return 1; }
    }
#ifdef TIMING
    unsigned long long t0 = mach_absolute_time();
    int r = pair_through(n - 1);
    ticks[n] += mach_absolute_time() - t0;
    if (r) { rej_pair[n]++; return 1; }
#else
    if (pair_through(n - 1)) { rej_pair[n]++; return 1; }
#endif
    return 0;
}

#ifndef PRE_FROM
#define PRE_FROM 1
#endif
static unsigned long long pre_calls[33], pre_rej[33];
/* PREPRUNE: same property, tested before geng's canonicity test, at orders >= maxn - PRE_FROM. */
int pairpreprune(graph *g, int n, int maxn) {
    if (n < maxn - PRE_FROM || n == maxn) return 0;
    NV = n;
    for (int i = 0; i < n; i++) {
        msk m = 0;
        setword w = g[i];
        while (w) {
            int j = FIRSTBITNZ(w);
            w ^= bit[j];
            m |= BIT(j);
        }
        A[i] = m;
    }
    pre_calls[n]++;
    if (pair_through(n - 1)) { pre_rej[n]++; return 1; }
    return 0;
}

void pairsummary(nauty_counter nout, double cpu) {
    for (int k = 1; k <= 32; k++)
        if (pre_calls[k])
            fprintf(stderr, ">P n=%d precalls=%llu prerej=%llu\n", k, pre_calls[k], pre_rej[k]);
    fprintf(stderr, ">S outputs=%llu cpu=%.2f sets=%llu matchsets=%llu\n",
            (unsigned long long)nout, cpu, n_sets, n_matchsets);
    for (int k = 1; k <= 32; k++)
        if (calls[k])
            fprintf(stderr, ">L n=%d calls=%llu rej_pair=%llu rej_count=%llu\n", k, calls[k],
                    rej_pair[k], rej_count[k]);
#ifdef TIMING
    { mach_timebase_info_data_t tb; mach_timebase_info(&tb);
      for (int k = 1; k <= 32; k++) if (ticks[k])
        fprintf(stderr, ">T n=%d pair_s=%.3f\n", k, (double)ticks[k] * tb.numer / tb.denom / 1e9); }
#endif
}
#else
/* ---------------- standalone decider ---------------- */
int main(int argc, char **argv) {
    char mode = argc > 1 ? argv[1][0] : 'f';
    static char line[4096];
    long total = 0, withpair = 0;
    while (fgets(line, sizeof line, stdin)) {
        if (line[0] == '>' || line[0] == '\n') continue;
        size_t L = strlen(line);
        while (L && (line[L - 1] == '\n' || line[L - 1] == '\r')) line[--L] = 0;
        int n = line[0] - 63;
        if (n < 1 || n > 30) { fprintf(stderr, "bad n\n"); return 2; }
        NV = n;
        memset(A, 0, sizeof A);
        int b = 0, p = 1;
        for (int j = 1; j < n; j++)
            for (int i = 0; i < j; i++) {
                int ch = line[p] - 63;
                if ((ch >> (5 - b)) & 1) { A[i] |= BIT(j); A[j] |= BIT(i); }
                if (++b == 6) { b = 0; p++; }
            }
        total++;
        int r = 0;
        for (int v = 0; v < n && !r; v++) r = pair_through(v);
        withpair += r;
        if (mode == 'f' && !r) puts(line);
        else if (mode == 'p' && r) puts(line);
        else if (mode == 'w') {
            if (!r) printf("%s NONE\n", line);
            else {
                printf("%s PAIR S=%u C1=", line, wit_S);
                for (int i = 0; i < ss; i++) printf("%d%s", wit_c1[i], i + 1 < ss ? "," : "");
                printf(" C2=");
                for (int i = 0; i < ss; i++) printf("%d%s", wit_c2[i], i + 1 < ss ? "," : "");
                printf("\n");
            }
        }
    }
    fprintf(stderr, "graphs=%ld with_pair=%ld pair_free=%ld\n", total, withpair, total - withpair);
    return 0;
}
#endif
