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

#ifndef BUDGET
#define BUDGET 0
#endif
static long rd_budget;
static int budget_mode, rd_aborted_this, any_aborted;
static int red_dfs(int cur, msk vis, int depth) {
    /* path[0..depth-1] placed, path[depth-1] == cur */
    if (budget_mode) {
        if (rd_budget <= 0) { rd_aborted_this = 1; return 0; }
        rd_budget--;
    }
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
#ifdef WARNSDORFF
    /* try the candidates with the fewest onward red options first (order only; same search) */
    int cl[8], ck[8], ncand = 0;
    for (msk cand = F[cur] & un; cand; cand &= cand - 1) {
        int v = lo(cand);
        int key = pc(F[v] & (un | BIT(R0)));
        int j = ncand++;
        while (j > 0 && ck[j - 1] > key) { cl[j] = cl[j - 1]; ck[j] = ck[j - 1]; j--; }
        cl[j] = v; ck[j] = key;
    }
    for (int ci = 0; ci < ncand; ci++) {
        int v = cl[ci];
#else
    for (msk cand = F[cur] & un; cand; cand &= cand - 1) {
        int v = lo(cand);
#endif
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
    if (!rem) {
        if (budget_mode) {
            rd_budget = BUDGET; rd_aborted_this = 0;
            int r = ham_decomp();
            if (!r && rd_aborted_this) any_aborted = 1;
            return r;
        }
        return ham_decomp();
    }
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

/* ---------------- method B: direct search for C1, C2 in G[S] (no matching loop) ----------------
 * Symmetry: let m be the least of the four neighbours of R0 used by C1 and C2; the cycle through
 * R0-m is called red and is walked from R0 to m, so red closes at a vertex > m and blue uses only
 * neighbours > m at R0. Red: DFS with "every unvisited vertex keeps 2 possible red edges".
 * Blue: Hamilton cycle of G[S] - red, same pruning. Unused edges are then automatically a perfect
 * matching of the degree-5 vertices of G[S]. */
static msk GS[32], RS[32];
static int amin;
static int blueB(int cur, msk vis, int depth) {
    if (depth == ss) {
        if (!((RS[cur] >> R0) & 1)) return 0;
        wit_c2[depth - 1] = cur;
        return 1;
    }
    wit_c2[depth - 1] = cur;
    msk un = SS & ~vis;
    msk ok = un | BIT(cur) | BIT(R0);
    for (msk t = un; t; t &= t - 1) {
        int u = lo(t);
        if (pc(RS[u] & ok) < 2) return 0;
    }
    for (msk cand = RS[cur] & un; cand; cand &= cand - 1) {
        int v = lo(cand);
        if (blueB(v, vis | BIT(v), depth + 1)) return 1;
    }
    return 0;
}
static int redB(int cur, msk vis, int depth) {
    if (depth == ss) {
        if (!((GS[cur] >> R0) & 1) || cur < amin) return 0;
        /* residual and blue search */
        for (msk t = SS; t; t &= t - 1) { int v = lo(t); RS[v] = GS[v]; }
        for (int i = 0; i < ss; i++) {
            int a = path[i], b = path[(i + 1) % ss];
            RS[a] &= ~BIT(b); RS[b] &= ~BIT(a);
        }
        /* blue at R0 only through neighbours > amin */
        msk keep = 0;
        for (msk t = RS[R0]; t; t &= t - 1) { int v = lo(t); if (v > amin) keep |= BIT(v); else RS[v] &= ~BIT(R0); }
        RS[R0] = keep;
        if (pc(RS[R0]) < 2) return 0;
        if (blueB(R0, BIT(R0), 1)) {
            wit_S = SS;
            for (int i = 0; i < ss; i++) wit_c1[i] = path[i];
            return 1;
        }
        return 0;
    }
    msk un = SS & ~vis;
    msk ok = un | BIT(cur) | BIT(R0);
    for (msk t = un; t; t &= t - 1) {
        int u = lo(t);
        if (pc(GS[u] & ok) < 2) return 0;
    }
    for (msk cand = GS[cur] & un; cand; cand &= cand - 1) {
        int v = lo(cand);
        path[depth] = v;
        if (redB(v, vis | BIT(v), depth + 1)) return 1;
    }
    return 0;
}
static int test_S_direct(msk S) {
    for (msk t = S; t; t &= t - 1) { int v = lo(t); GS[v] = A[v] & S; }
    SS = S; ss = pc(S);
    path[0] = R0;
    for (msk c = GS[R0]; c; c &= c - 1) {
        int a = lo(c);
        /* a is the least used neighbour of R0: at least 3 more neighbours > a are needed */
        if (pc(GS[R0] & ~(BIT(a + 1) - 1)) < 3) break;
        amin = a;
        path[1] = a;
        if (redB(a, BIT(R0) | BIT(a), 2)) return 1;
    }
    return 0;
}
#ifndef USE_DIRECT_DEFAULT
#define USE_DIRECT_DEFAULT 0
#endif
static int use_direct = USE_DIRECT_DEFAULT;

static unsigned long long n_sets, n_matchsets;

static int test_S(msk S) {
    n_sets++;
    if (use_direct) return test_S_direct(S);
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
#if BUDGET > 0
    /* pass 1: every matching with a node budget per matching; a found decomposition is genuine.
     * If no matching was cut off, every matching was refuted exhaustively. Else pass 2 is the
     * exhaustive search, so the answer is exact either way. */
    any_aborted = 0;
    budget_mode = 1;
    int r1 = match_dfs(d5);
    budget_mode = 0;
    if (r1) return 1;
    if (!any_aborted) return 0;
#endif
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

/* ---------------- completion test (5-regular target, two vertices missing) ----------------
 * H = A[0..n-1] is pair-free with max degree <= 5; d_v = 5 - deg(v). A 5-regular completion adds
 * x = n and y = n+1: every vertex with d_v = 2 (set D2) is adjacent to both, every vertex with
 * d_v = 1 (set D1) to exactly one, and x ~ y iff sum d_v = 8. So X = D2 + X1, Y = D2 + (D1 - X1)
 * with |X1| = |D1|/2. Returns 1 iff some completion is pair-free (and leaves it in comp_X, comp_Y,
 * comp_exy). good(X) means H + x_X has no pair through x; a pair through x found for X uses exactly
 * four neighbours T of x, and every X' containing T has the same pair, so T is cached. G is pair-free
 * iff good(X), good(Y) and G has no pair through x (a pair avoiding x lies in H + y_Y). */
static unsigned long long comp_calls, comp_tests, comp_cachehits, comp_full, comp_found;
static msk comp_X, comp_Y;
static int comp_exy;

#ifdef TIMING2
#include <mach/mach_time.h>
static unsigned long long tk_bad, tk_good, n_bad, n_good;
#endif
static msk cmp_Tc[256];
static int cmp_nT;

/* 1 iff H + x_X has a pair through x (x = n). Uses and extends the T cache. */
static int side_bad(int n, msk X) {
    for (int i = 0; i < cmp_nT; i++)
        if ((cmp_Tc[i] & ~X) == 0) { comp_cachehits++; return 1; }
    comp_tests++;
    const int x = n;
    for (msk t = X; t; t &= t - 1) A[lo(t)] |= BIT(x);
    A[x] = X;
    NV = n + 1;
#ifdef TIMING2
    unsigned long long t0 = mach_absolute_time();
    int bad = pair_through(x);
    unsigned long long dt = mach_absolute_time() - t0;
    if (bad) { tk_bad += dt; n_bad++; } else { tk_good += dt; n_good++; }
#else
    int bad = pair_through(x);
#endif
    if (bad) {
        msk T = BIT(wit_c1[1]) | BIT(wit_c1[ss - 1]) | BIT(wit_c2[1]) | BIT(wit_c2[ss - 1]);
        if (pc(T) == 4 && (T & ~X) == 0 && cmp_nT < 256) cmp_Tc[cmp_nT++] = T;
    }
    for (msk t = X; t; t &= t - 1) A[lo(t)] &= ~BIT(x);
    A[x] = 0;
    NV = n;
    return bad;
}

static int has_pairfree_completion(int n) {
    msk D1 = 0, D2 = 0;
    int c = 0;
    comp_calls++;
    for (int v = 0; v < n; v++) {
        int d = 5 - pc(A[v]);
        if (d < 0 || d > 2) return 0;
        if (d == 1) D1 |= BIT(v);
        if (d == 2) D2 |= BIT(v);
        c += d;
    }
    if (c != 8 && c != 10) return 0;
    int exy = (c == 8), k = 5 - exy, h = k - pc(D2), m = pc(D1);
    if (h < 0 || 2 * h != m) return 0;
    int p[32], q = 0;
    for (msk t = D1; t; t &= t - 1) p[q++] = lo(t);
    cmp_nT = 0;
    const int x = n, y = n + 1;
    unsigned long long cm = (h == 0) ? 0 : ((1ull << h) - 1), lim = 1ull << m, fullm = lim - 1;
    for (;;) {
        unsigned long long cm2 = fullm & ~cm;
        if (cm <= cm2) {               /* each unordered completion {X, Y} once */
            msk X = D2, Y = D2;
            for (unsigned long long t = cm; t; t &= t - 1) X |= BIT(p[__builtin_ctzll(t)]);
            for (unsigned long long t = cm2; t; t &= t - 1) Y |= BIT(p[__builtin_ctzll(t)]);
            if (!side_bad(n, X) && !side_bad(n, Y)) {
                for (msk t = X; t; t &= t - 1) A[lo(t)] |= BIT(x);
                for (msk t = Y; t; t &= t - 1) A[lo(t)] |= BIT(y);
                A[x] = X | (exy ? BIT(y) : 0);
                A[y] = Y | (exy ? BIT(x) : 0);
                NV = n + 2;
                comp_full++;
                int r = pair_through(x);
                for (msk t = X; t; t &= t - 1) A[lo(t)] &= ~BIT(x);
                for (msk t = Y; t; t &= t - 1) A[lo(t)] &= ~BIT(y);
                A[x] = A[y] = 0;
                NV = n;
                if (!r) { comp_found++; comp_X = X; comp_Y = Y; comp_exy = exy; return 1; }
            }
        }
        if (h == 0) break;
        unsigned long long cc = cm & (~cm + 1), rr = cm + cc;
        cm = (((rr ^ cm) >> 2) / cc) | rr;
        if (cm >= lim) break;
    }
    return 0;
}

#ifndef STANDALONE
/* ---------------- geng hook ---------------- */
extern int TLS_ATTR geng_mindeg, geng_maxdeg;
static unsigned long long calls[33], rej_pair[33], rej_count[33], rej_comp[33];
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
#ifdef COMPLETE14
    if (n == maxn - 2 && geng_mindeg == 5 && geng_maxdeg == 5) {
        if (!has_pairfree_completion(n)) { rej_comp[n]++; return 1; }
        fprintf(stderr, ">C completion found at level %d (geng continues)\n", n);
    }
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
#ifdef COMPLETE14
    for (int k = 1; k <= 32; k++)
        if (rej_comp[k])
            fprintf(stderr, ">K n=%d rej_completion=%llu\n", k, rej_comp[k]);
    fprintf(stderr, ">K comp_calls=%llu comp_tests=%llu comp_cachehits=%llu comp_full=%llu comp_found=%llu\n",
            comp_calls, comp_tests, comp_cachehits, comp_full, comp_found);
#ifdef TIMING2
    { mach_timebase_info_data_t tb; mach_timebase_info(&tb);
      fprintf(stderr, ">T2 bad=%llu bad_s=%.3f good=%llu good_s=%.3f\n", n_bad, (double)tk_bad*tb.numer/tb.denom/1e9, n_good, (double)tk_good*tb.numer/tb.denom/1e9); }
#endif
#endif
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
    if (argc > 2 && argv[2][0] == 'B') use_direct = 1;
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
        if (mode == 'k' || mode == 'c') {
            /* validation of has_pairfree_completion. k: input H (pair-free, 5-regular target with
             * two vertices missing); compares with brute force over all completions.
             * c: input G pair-free 5-regular; for every pair {x,y}, H = G - {x,y} must report a
             * pair-free completion. */
            msk G0[32];
            memcpy(G0, A, sizeof A);
            int N0 = n;
            int npairs = (mode == 'k') ? 1 : N0 * (N0 - 1) / 2;
            for (int pi = 0, xa = 0, ya = 1; pi < npairs; pi++) {
                if (mode == 'c') {
                    /* relabel: drop xa, ya; others keep order */
                    int map[32], q2 = 0;
                    for (int v = 0; v < N0; v++) map[v] = (v == xa || v == ya) ? -1 : q2++;
                    memset(A, 0, sizeof A);
                    for (int v = 0; v < N0; v++) if (map[v] >= 0)
                        for (int u = 0; u < N0; u++) if (map[u] >= 0 && ((G0[v] >> u) & 1)) A[map[v]] |= BIT(map[u]);
                    NV = N0 - 2;
                    if (++ya == N0) { xa++; ya = xa + 1; }
                } else { memcpy(A, G0, sizeof A); NV = N0; }
                int hn = NV, hp = 0;
                for (int v = 0; v < hn && !hp; v++) hp = pair_through(v);
                NV = hn;
                if (hp) { printf("%s SKIP_H_HAS_PAIR\n", line); continue; }
                int res = has_pairfree_completion(hn);
                NV = hn;
                int bf = -1;
                if (mode == 'k') {
                    /* brute force: every completion, full decision */
                    msk H0[32]; memcpy(H0, A, sizeof A);
                    msk D1 = 0, D2 = 0; int c = 0;
                    for (int v = 0; v < hn; v++) { int d = 5 - pc(A[v]); if (d == 1) D1 |= BIT(v); if (d == 2) D2 |= BIT(v); c += d; }
                    int exy = (c == 8), h = 5 - exy - pc(D2), m = pc(D1);
                    bf = 0;
                    if ((c == 8 || c == 10) && h >= 0 && 2 * h == m) {
                        int pp[32], q3 = 0; for (msk t = D1; t; t &= t - 1) pp[q3++] = lo(t);
                        for (unsigned long long cm = 0; cm < (1ull << m) && !bf; cm++) {
                            if (__builtin_popcountll(cm) != h) continue;
                            msk X = D2, Y = D2;
                            for (int i = 0; i < m; i++) { if ((cm >> i) & 1) X |= BIT(pp[i]); else Y |= BIT(pp[i]); }
                            memcpy(A, H0, sizeof A);
                            for (msk t = X; t; t &= t - 1) A[lo(t)] |= BIT(hn);
                            for (msk t = Y; t; t &= t - 1) A[lo(t)] |= BIT(hn + 1);
                            A[hn] = X | (exy ? BIT(hn + 1) : 0);
                            A[hn + 1] = Y | (exy ? BIT(hn) : 0);
                            NV = hn + 2;
                            int anyp = 0;
                            for (int v = 0; v < hn + 2 && !anyp; v++) anyp = pair_through(v);
                            if (!anyp) bf = 1;
                        }
                    }
                    memcpy(A, H0, sizeof A); NV = hn;
                }
                if (mode == 'k') printf("%s comp=%d brute=%d %s\n", line, res, bf, res == bf ? "OK" : "MISMATCH");
                else printf("%s pairidx=%d comp=%d %s\n", line, pi, res, res == 1 ? "OK" : "MISMATCH");
            }
            continue;
        }
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
