/* gen585.c -- exhaustive search for minimal counterexamples to S10-type statements (Erdos 585).
 *
 * Canonical augmentation by vertices (McKay 1998). The canonical deletion vertex m(G) is a vertex
 * of minimum degree: among min-degree vertices, those with the largest invariant inv(); among
 * those, the one with the largest nauty canonical label. A child G = P + v is accepted iff v lies
 * in the Aut(G)-orbit of m(G). Siblings are deduplicated by canonical form when Aut(P) != 1.
 *
 * Level k generates (one per isomorphism class) every graph G on k vertices with
 *   max degree <= MAXD, no pair, e(S) <= 3|S| - SP for all S with |S| >= SPMIN (S != V(G) at the
 *   final level), e(G) >= L_k, and the look-ahead conditions below.
 * Final level N: e = EF exactly and min degree >= MINDF.
 *
 * Pair = two edge-disjoint cycles with the same vertex set. A pair in G = P + v that is not a pair
 * of P has v in its support, so only supports through v are tested (P is pair-free).
 *
 * Usage: gen585 N EF SP SPMIN MINDF [options]
 *   -s K      split level (for res/mod and checkpoints), default 0 (none)
 *   -r R -m M residue class R mod M of split-level nodes
 *   -t SEC    time budget; stop after the current split subtree when exceeded
 *   -f FILE   state file (resume)
 *   -o FILE   output file for final graphs (appended)
 *   -d K      dump every accepted graph at level K to stdout (edge lists)
 *   -L        disable look-ahead prunes (for validation)
 *   -S K      do not extend graphs at level K (with -d K: dump a level and stop)
 *   -x K      apply sparsity only to sets S with |S| <= K (default N - 1: all proper sets)
 *   -p        test mode: read graphs from stdin ("n m u v u v ..."), print 1/0 for has-pair
 */
#define WORDSIZE 32
#define MAXN 32
#include "nauty.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXV 20
typedef uint32_t bits;
#define BIT(i) (1u << (i))
static inline int popc(bits x) { return __builtin_popcount(x); }
static inline int ctz(bits x) { return __builtin_ctz(x); }

static int N, EF, SP, SPMIN, MINDF, MAXD = 6, SPMAX = -1, PAIRV = 1, SDESC = 1;
static int Lb[MAXV + 2], Ub[MAXV + 2], CAP[MAXV + 2];
static int SPLIT = 0, RES = 0, MOD = 1, DUMP = -1, LOOKAHEAD = 1, STOPLEVEL = 99;
static double TBUDGET = 1e18;
static const char *STATEF = NULL, *OUTF = NULL;
static long long splitidx = -1, resume_done = -1;
static int stop_flag = 0;
static double t_start;

static long long nodes[MAXV + 2], tested[MAXV + 2], sparse_rej[MAXV + 2], la_rej[MAXV + 2],
    inv_rej[MAXV + 2], pair_rej[MAXV + 2], canon_rej[MAXV + 2], dup_rej[MAXV + 2];
static long long base_nodes[MAXV + 2], base_tested[MAXV + 2], base_pair_rej[MAXV + 2];
static long long nauty_calls = 0, finals = 0, base_finals = 0, subtrees_done = 0, base_subtrees = 0;
static double base_seconds = 0;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

/* ---------------- pair test ---------------- */
static int hs; /* size of current support */
static bits hla[MAXV], hc1[MAXV];
static int hroot, hfix, hfirst;
static int Vpath[MAXV], Vloc[MAXV];
static const bits *Vgadj;
static void verify_pair(const bits *gadj, int s, const int *loc, const int *p1, const int *p2);
static int HCpath[MAXV];

/* Hamilton cycle existence in R (s vertices, local bits). */
static bits hR[MAXV];
static int hcs, hcroot, hcfirst;
static int hc_dfs(int cur, bits vis, int depth) {
    if (depth == hcs) {
        return (hR[cur] >> hcroot & 1) && hcfirst < cur;
    }
    bits unv = ((BIT(hcs) - 1) & ~vis);
    /* feasibility: every unvisited vertex needs 2 neighbours among unvisited + cur + root */
    bits pool = unv | BIT(cur) | BIT(hcroot);
    bits t = unv;
    while (t) {
        int u = ctz(t);
        t &= t - 1;
        if (popc(hR[u] & pool & ~BIT(u)) < 2) return 0;
    }
    bits cand = hR[cur] & unv;
    while (cand) {
        int w = ctz(cand);
        cand &= cand - 1;
        HCpath[depth] = w;
        if (hc_dfs(w, vis | BIT(w), depth + 1)) return 1;
    }
    return 0;
}
static int hc_dfs_exists(int s, const bits *R) {
    int r = 0, best = 99;
    for (int i = 0; i < s; i++) {
        int d = popc(R[i]);
        if (d < 2) return 0;
        if (d < best) { best = d; r = i; }
    }
    for (int i = 0; i < s; i++) hR[i] = R[i];
    hcs = s;
    hcroot = r;
    HCpath[0] = r;
    bits nb = R[r];
    while (nb) {
        int a = ctz(nb);
        nb &= nb - 1;
        hcfirst = a;
        HCpath[1] = a;
        if (hc_dfs(a, BIT(r) | BIT(a), 2)) return 1;
    }
    return 0;
}


/* Hamilton cycle existence with propagation: a vertex of degree 2 forces both edges; a vertex
   with two forced edges loses its other edges; forced edges are tracked as paths, and a forced
   cycle shorter than s is a contradiction. Then DFS on the reduced graph. Removing an edge is
   done only when no Hamilton cycle can use it, so the answer is unchanged. */
static int hc_exists(int s, const bits *R0) {
    bits R[MAXV], F[MAXV];
    int end[MAXV], len[MAXV];
    for (int i = 0; i < s; i++) { R[i] = R0[i]; F[i] = 0; end[i] = i; len[i] = 1; }
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int u = 0; u < s; u++) {
            int d = popc(R[u]);
            if (d < 2) return 0;
            if (d == 2 && F[u] != R[u]) {
                bits nf = R[u] & ~F[u];
                while (nf) {
                    int w = ctz(nf);
                    nf &= nf - 1;
                    if (popc(F[u]) >= 2 || popc(F[w]) >= 2) return 0;
                    int a = end[u], b = end[w];
                    if (a == w) {
                        if (len[u] != s) return 0;
                        F[u] |= BIT(w);
                        F[w] |= BIT(u);
                        /* forced edges form a Hamilton cycle: record it */
                        int prev = -1, cur = 0;
                        for (int i = 0; i < s; i++) {
                            HCpath[i] = cur;
                            bits nx = F[cur] & ~(prev >= 0 ? BIT(prev) : 0);
                            int nxt = ctz(nx);
                            if (prev < 0) nxt = ctz(F[cur]);
                            prev = cur;
                            cur = nxt;
                        }
                        return 1;
                    }
                    F[u] |= BIT(w);
                    F[w] |= BIT(u);
                    int L = len[u] + len[w];
                    end[a] = b;
                    end[b] = a;
                    len[a] = L;
                    len[b] = L;
                    changed = 1;
                }
            }
            if (popc(F[u]) == 2 && R[u] != F[u]) {
                bits rm = R[u] & ~F[u];
                R[u] = F[u];
                while (rm) {
                    int w = ctz(rm);
                    rm &= rm - 1;
                    R[w] &= ~BIT(u);
                }
                changed = 1;
            }
        }
    }
    return hc_dfs_exists(s, R);
}

/* Enumerate Hamilton cycles C1 through hroot (first edge fixed to hfirst if hfix, else
   orientation first < last) and test the residual for a Hamilton cycle. */
static int c1_dfs(int cur, bits vis, int depth) {
    if (depth == hs) {
        if (!(hla[cur] >> hroot & 1)) return 0;
        if (!hfix && !(hfirst < cur)) return 0;
        hc1[cur] |= BIT(hroot);
        hc1[hroot] |= BIT(cur);
        bits R[MAXV];
        for (int i = 0; i < hs; i++) R[i] = hla[i] & ~hc1[i];
        int ok = hc_exists(hs, R);
        if (ok) verify_pair(Vgadj, hs, Vloc, Vpath, HCpath);
        hc1[cur] &= ~BIT(hroot);
        hc1[hroot] &= ~BIT(cur);
        return ok;
    }
    bits unv = ((BIT(hs) - 1) & ~vis);
    bits pool = unv | BIT(cur) | BIT(hroot);
    bits t = unv;
    while (t) {
        int u = ctz(t);
        t &= t - 1;
        if (popc(hla[u] & pool & ~BIT(u)) < 2) return 0;
    }
    bits cand = hla[cur] & unv;
    while (cand) {
        int w = ctz(cand);
        cand &= cand - 1;
        hc1[cur] |= BIT(w);
        hc1[w] |= BIT(cur);
        Vpath[depth] = w;
        int ok = c1_dfs(w, vis | BIT(w), depth + 1);
        hc1[cur] &= ~BIT(w);
        hc1[w] &= ~BIT(cur);
        if (ok) return 1;
    }
    return 0;
}

static int pair_on_S(bits S, const bits *adj) {
    int idx[MAXV], loc[MAXV], s = 0;
    bits t = S;
    while (t) {
        int u = ctz(t);
        t &= t - 1;
        idx[u] = s;
        loc[s++] = u;
    }
    for (int i = 0; i < s; i++) Vloc[i] = loc[i];
    Vgadj = adj;
    for (int i = 0; i < s; i++) {
        bits a = adj[loc[i]] & S, m = 0;
        while (a) {
            int w = ctz(a);
            a &= a - 1;
            m |= BIT(idx[w]);
        }
        hla[i] = m;
        hc1[i] = 0;
    }
    hs = s;
    hroot = -1;
    for (int i = 0; i < s; i++)
        if (popc(hla[i]) == 4) { hroot = i; break; }
    if (hroot >= 0) {
        /* all four edges at hroot are used; WLOG the one to its lowest neighbour is in C1 */
        hfix = 1;
        hfirst = ctz(hla[hroot]);
        hc1[hroot] |= BIT(hfirst);
        hc1[hfirst] |= BIT(hroot);
        Vpath[0] = hroot;
        Vpath[1] = hfirst;
        int ok = c1_dfs(hfirst, BIT(hroot) | BIT(hfirst), 2);
        return ok;
    }
    hfix = 0;
    hroot = 0;
    bits nb = hla[0];
    while (nb) {
        int a = ctz(nb);
        nb &= nb - 1;
        hfirst = a;
        hc1[0] |= BIT(a);
        hc1[a] |= BIT(0);
        Vpath[0] = 0;
        Vpath[1] = a;
        int ok = c1_dfs(a, BIT(0) | BIT(a), 2);
        hc1[0] &= ~BIT(a);
        hc1[a] &= ~BIT(0);
        if (ok) return 1;
    }
    return 0;
}


/* ---------------- pair test v2: forced C2 edges + verified certificates ----------------
 * Two edge-disjoint Hamilton cycles C1, C2 of G[S]. C1 is built as a path from a root. When a
 * vertex of degree 4 in G[S] has both C1 edges fixed, its other two edges must be C2 edges
 * (every support vertex has exactly two edges in each cycle). Forced C2 edges are tracked as
 * paths; a vertex with three forced C2 edges, or a forced C2 cycle shorter than |S|, is a
 * dead end. C1 never uses a forced C2 edge. When C1 closes, the residual G[S] - E(C1) is
 * searched for a Hamilton cycle. Every positive answer is re-verified from scratch (verify_pair)
 * against the global adjacency before it is used, so a pair rejection never rests on the search
 * logic alone. */
static bits Pla[MAXV], Pc1[MAXV], Pc2[MAXV];
static int Ps, Proot, Pfix, Pfirst;
static int Pend[MAXV], Plen[MAXV], Ppath[MAXV], Ploc[MAXV];
static long long pairs_verified = 0;

static int hc2_dfs(int cur, bits vis, int depth) {
    if (depth == hcs) return (hR[cur] >> hcroot & 1) && hcfirst < cur;
    bits unv = ((BIT(hcs) - 1) & ~vis);
    bits pool = unv | BIT(cur) | BIT(hcroot);
    bits t = unv;
    while (t) {
        int u = ctz(t);
        t &= t - 1;
        if (popc(hR[u] & pool & ~BIT(u)) < 2) return 0;
    }
    bits cand = hR[cur] & unv;
    while (cand) {
        int w = ctz(cand);
        cand &= cand - 1;
        HCpath[depth] = w;
        if (hc2_dfs(w, vis | BIT(w), depth + 1)) return 1;
    }
    return 0;
}
static int hc2_exists(int s, const bits *R) {
    int r = 0, best = 99;
    for (int i = 0; i < s; i++) {
        int d = popc(R[i]);
        if (d < 2) return 0;
        if (d < best) { best = d; r = i; }
    }
    for (int i = 0; i < s; i++) hR[i] = R[i];
    hcs = s;
    hcroot = r;
    HCpath[0] = r;
    bits nb = R[r];
    while (nb) {
        int a = ctz(nb);
        nb &= nb - 1;
        hcfirst = a;
        HCpath[1] = a;
        if (hc2_dfs(a, BIT(r) | BIT(a), 2)) return 1;
    }
    return 0;
}

static int add_c2(int w, int u) {
    if (Pc2[w] >> u & 1) return 1;
    if (popc(Pc2[w]) >= 2 || popc(Pc2[u]) >= 2) return 0;
    int a = Pend[w], b = Pend[u];
    if (a == u) {
        if (Plen[w] != Ps) return 0;
        Pc2[w] |= BIT(u);
        Pc2[u] |= BIT(w);
        return 1;
    }
    int L = Plen[w] + Plen[u];
    Pc2[w] |= BIT(u);
    Pc2[u] |= BIT(w);
    Pend[a] = b;
    Pend[b] = a;
    Plen[a] = L;
    Plen[b] = L;
    return 1;
}
static int force_at(int w) {
    if (popc(Pla[w]) != 4) return 1;
    bits other = Pla[w] & ~Pc1[w];
    while (other) {
        int u = ctz(other);
        other &= other - 1;
        if (!add_c2(w, u)) return 0;
    }
    return 1;
}

static void verify_pair(const bits *gadj, int s, const int *loc, const int *p1, const int *p2) {
    /* p1, p2: local vertex sequences of length s; check in the global graph */
    bits S = 0, S1 = 0, S2 = 0, e1[MAXV] = {0};
    for (int i = 0; i < s; i++) S |= BIT(loc[i]);
    for (int i = 0; i < s; i++) {
        int a = loc[p1[i]], b = loc[p1[(i + 1) % s]];
        if (!(gadj[a] >> b & 1) || (S1 >> a & 1)) { fprintf(stderr, "VERIFY FAIL C1\n"); exit(7); }
        S1 |= BIT(a);
        e1[a] |= BIT(b);
        e1[b] |= BIT(a);
    }
    for (int i = 0; i < s; i++) {
        int a = loc[p2[i]], b = loc[p2[(i + 1) % s]];
        if (!(gadj[a] >> b & 1) || (S2 >> a & 1) || (e1[a] >> b & 1)) { fprintf(stderr, "VERIFY FAIL C2\n"); exit(7); }
        S2 |= BIT(a);
    }
    if (S1 != S || S2 != S || s < 3) { fprintf(stderr, "VERIFY FAIL sets\n"); exit(7); }
    pairs_verified++;
}

static const bits *Pgadj;
static int c1_dfs2(int cur, bits vis, int depth) {
    bits s2[MAXV];
    int se[MAXV], sl[MAXV];
    if (depth == Ps) {
        if (!(Pla[cur] >> Proot & 1)) return 0;
        if (Pc2[cur] >> Proot & 1) return 0;
        if (!Pfix && !(Pfirst < cur)) return 0;
        memcpy(s2, Pc2, sizeof(bits) * Ps);
        memcpy(se, Pend, sizeof(int) * Ps);
        memcpy(sl, Plen, sizeof(int) * Ps);
        Pc1[cur] |= BIT(Proot);
        Pc1[Proot] |= BIT(cur);
        int ok = force_at(cur) && force_at(Proot);
        if (ok) {
            bits R[MAXV];
            for (int i = 0; i < Ps; i++) R[i] = Pla[i] & ~Pc1[i];
            ok = hc2_exists(Ps, R);
            if (ok) verify_pair(Pgadj, Ps, Ploc, Ppath, HCpath);
        }
        Pc1[cur] &= ~BIT(Proot);
        Pc1[Proot] &= ~BIT(cur);
        memcpy(Pc2, s2, sizeof(bits) * Ps);
        memcpy(Pend, se, sizeof(int) * Ps);
        memcpy(Plen, sl, sizeof(int) * Ps);
        return ok;
    }
    bits unv = ((BIT(Ps) - 1) & ~vis);
    bits pool = unv | BIT(cur) | BIT(Proot);
    bits t = unv;
    while (t) {
        int u = ctz(t);
        t &= t - 1;
        if (popc(Pla[u] & ~Pc2[u] & pool & ~BIT(u)) < 2) return 0;
    }
    bits cand = Pla[cur] & unv & ~Pc2[cur];
    while (cand) {
        int w = ctz(cand);
        cand &= cand - 1;
        memcpy(s2, Pc2, sizeof(bits) * Ps);
        memcpy(se, Pend, sizeof(int) * Ps);
        memcpy(sl, Plen, sizeof(int) * Ps);
        Pc1[cur] |= BIT(w);
        Pc1[w] |= BIT(cur);
        int ok = force_at(cur);
        if (ok) {
            Ppath[depth] = w;
            ok = c1_dfs2(w, vis | BIT(w), depth + 1);
        }
        Pc1[cur] &= ~BIT(w);
        Pc1[w] &= ~BIT(cur);
        memcpy(Pc2, s2, sizeof(bits) * Ps);
        memcpy(Pend, se, sizeof(int) * Ps);
        memcpy(Plen, sl, sizeof(int) * Ps);
        if (ok) return 1;
    }
    return 0;
}

static int pair_on_S2(bits S, const bits *adj) {
    int idx[MAXV], s = 0;
    bits t = S;
    while (t) {
        int u = ctz(t);
        t &= t - 1;
        idx[u] = s;
        Ploc[s++] = u;
    }
    for (int i = 0; i < s; i++) {
        bits a = adj[Ploc[i]] & S, m = 0;
        while (a) {
            int w = ctz(a);
            a &= a - 1;
            m |= BIT(idx[w]);
        }
        Pla[i] = m;
        Pc1[i] = 0;
        Pc2[i] = 0;
        Pend[i] = i;
        Plen[i] = 1;
    }
    Ps = s;
    Pgadj = adj;
    Proot = -1;
    for (int i = 0; i < s; i++)
        if (popc(Pla[i]) == 4) { Proot = i; break; }
    if (Proot >= 0) {
        Pfix = 1;
        Pfirst = ctz(Pla[Proot]);
        Pc1[Proot] |= BIT(Pfirst);
        Pc1[Pfirst] |= BIT(Proot);
        Ppath[0] = Proot;
        Ppath[1] = Pfirst;
        return c1_dfs2(Pfirst, BIT(Proot) | BIT(Pfirst), 2);
    }
    Pfix = 0;
    Proot = 0;
    Ppath[0] = 0;
    bits nb = Pla[0];
    while (nb) {
        int a = ctz(nb);
        nb &= nb - 1;
        Pfirst = a;
        Ppath[1] = a;
        Pc1[0] |= BIT(a);
        Pc1[a] |= BIT(0);
        int ok = c1_dfs2(a, BIT(0) | BIT(a), 2);
        Pc1[0] &= ~BIT(a);
        Pc1[a] &= ~BIT(0);
        if (ok) return 1;
    }
    return 0;
}

#define MAXS 40000
static bits Slist[MAXS];
static int nS;
static void enumS(bits I, bits U, const bits *adj) {
    for (;;) {
        int changed = 0;
        bits pool = I | U, t = U;
        while (t) {
            int u = ctz(t);
            t &= t - 1;
            if (popc(adj[u] & pool) < 4) { U &= ~BIT(u); pool &= ~BIT(u); changed = 1; }
        }
        if (!changed) break;
    }
    bits pool = I | U, t = I;
    while (t) {
        int u = ctz(t);
        t &= t - 1;
        if (popc(adj[u] & pool) < 4) return;
    }
    if (!U) {
        if (popc(I) >= 5 && nS < MAXS) Slist[nS++] = I;
        else if (nS >= MAXS) { fprintf(stderr, "Slist overflow\n"); exit(3); }
        return;
    }
    int u = ctz(U);
    enumS(I | BIT(u), U & ~BIT(u), adj);
    enumS(I, U & ~BIT(u), adj);
}

static int cmp_pop(const void *a, const void *b) {
    int x = popc(*(const bits *)a), y = popc(*(const bits *)b);
    return SDESC ? (x < y) - (x > y) : (x > y) - (x < y);
}

/* 1 iff G (n vertices) has a pair whose support contains v */
static int has_pair_through(int n, const bits *adj, int v) {
    bits K = BIT(n) - 1;
    for (;;) {
        int changed = 0;
        bits t = K;
        while (t) {
            int u = ctz(t);
            t &= t - 1;
            if (popc(adj[u] & K) < 4) { K &= ~BIT(u); changed = 1; }
        }
        if (!changed) break;
    }
    if (!(K >> v & 1)) return 0;
    /* restrict to the component of v in G[K]: a support is connected and lies in K */
    bits C = BIT(v), frontier = BIT(v);
    while (frontier) {
        int u = ctz(frontier);
        frontier &= frontier - 1;
        bits nw = adj[u] & K & ~C;
        C |= nw;
        frontier |= nw;
    }
    K = C;
    if (popc(K) < 5) return 0;
    /* lazy order: the whole component first (most positives), then every smaller support */
    if (PAIRV == 2 ? pair_on_S2(K, adj) : pair_on_S(K, adj)) return 1;
    nS = 0;
    enumS(BIT(v), K & ~BIT(v), adj);
    if (nS > 1) qsort(Slist, nS, sizeof(bits), cmp_pop);
    for (int i = 0; i < nS; i++) {
        if (Slist[i] == K) continue;
        if (PAIRV == 2 ? pair_on_S2(Slist[i], adj) : pair_on_S(Slist[i], adj)) return 1;
    }
    return 0;
}

/* ---------------- nauty ---------------- */
static int run_nauty(int n, const bits *adj, int *lab, int *orbits, graph *canong) {
    graph g[MAXN];
    int ptn[MAXN];
    static DEFAULTOPTIONS_GRAPH(options);
    statsblk stats;
    options.getcanon = TRUE;
    EMPTYGRAPH(g, 1, n);
    for (int i = 0; i < n; i++) {
        bits a = adj[i] & ~(BIT(i + 1) - 1);
        while (a) {
            int j = ctz(a);
            a &= a - 1;
            ADDONEEDGE(g, i, j, 1);
        }
    }
    densenauty(g, lab, ptn, orbits, &options, &stats, 1, n, canong);
    nauty_calls++;
    return stats.grpsize1 == 1.0 && stats.grpsize2 == 0; /* 1 iff trivial group */
}

/* ---------------- state ---------------- */
static void save_state(const char *status) {
    if (!STATEF) return;
    char tmp[4096];
    snprintf(tmp, sizeof tmp, "%s.tmp", STATEF);
    FILE *f = fopen(tmp, "w");
    if (!f) return;
    fprintf(f, "status %s\n", status);
    fprintf(f, "done %lld\n", resume_done);
    fprintf(f, "finals %lld\n", base_finals + finals);
    fprintf(f, "subtrees %lld\n", base_subtrees + subtrees_done);
    fprintf(f, "seconds %.1f\n", base_seconds + (now() - t_start));
    for (int k = 1; k <= N; k++) {
        long long nk = (k > SPLIT && SPLIT > 0) ? base_nodes[k] + nodes[k] : nodes[k];
        long long tk = (k > SPLIT && SPLIT > 0) ? base_tested[k] + tested[k] : tested[k];
        long long pk = (k > SPLIT && SPLIT > 0) ? base_pair_rej[k] + pair_rej[k] : pair_rej[k];
        fprintf(f, "level %d %lld %lld %lld\n", k, nk, tk, pk);
    }
    fclose(f);
    rename(tmp, STATEF);
}

static void load_state(void) {
    if (!STATEF) return;
    FILE *f = fopen(STATEF, "r");
    if (!f) return;
    char key[64], status[64];
    while (fscanf(f, "%63s", key) == 1) {
        if (!strcmp(key, "status")) { if (fscanf(f, "%63s", status) != 1) break; }
        else if (!strcmp(key, "done")) { if (fscanf(f, "%lld", &resume_done) != 1) break; }
        else if (!strcmp(key, "finals")) { if (fscanf(f, "%lld", &base_finals) != 1) break; }
        else if (!strcmp(key, "subtrees")) { if (fscanf(f, "%lld", &base_subtrees) != 1) break; }
        else if (!strcmp(key, "seconds")) { if (fscanf(f, "%lf", &base_seconds) != 1) break; }
        else if (!strcmp(key, "level")) {
            int k;
            long long a, b, c;
            if (fscanf(f, "%d %lld %lld %lld", &k, &a, &b, &c) != 4) break;
            if (k > SPLIT && SPLIT > 0 && k <= MAXV) { base_nodes[k] = a; base_tested[k] = b; base_pair_rej[k] = c; }
        }
    }
    fclose(f);
}

static void report_final(int n, const bits *adj) {
    finals++;
    FILE *f = OUTF ? fopen(OUTF, "a") : stdout;
    fprintf(f, "FINAL n=%d edges:", n);
    for (int i = 0; i < n; i++) {
        bits a = adj[i] & ~(BIT(i + 1) - 1);
        while (a) {
            int j = ctz(a);
            a &= a - 1;
            fprintf(f, " %d-%d", i, j);
        }
    }
    fprintf(f, "\n");
    if (OUTF) fclose(f); else fflush(f);
}

static void dump_graph(int n, const bits *adj) {
    int e = 0;
    for (int i = 0; i < n; i++) e += popc(adj[i]);
    printf("%d %d", n, e / 2);
    for (int i = 0; i < n; i++) {
        bits a = adj[i] & ~(BIT(i + 1) - 1);
        while (a) {
            int j = ctz(a);
            a &= a - 1;
            printf(" %d %d", i, j);
        }
    }
    printf("\n");
}


/* ---------------- degree-histogram look-ahead ----------------
 * Relaxation: forget the graph, keep the degree histogram c[0..MAXD]. One step adds a vertex of
 * degree t <= min(MAXD, k, delta + 1) joined to t distinct vertices of degree <= MAXD - 1, such
 * that afterwards every degree is >= t (so every vertex of degree t - 1 is joined, none is lower).
 * Every level j must keep L_j <= e_j <= U_j. Accept iff some sequence reaches k = N with e = EF and
 * min degree >= MINDF. Every real min-degree deletion chain is such a sequence, so a histogram
 * with no completion cannot occur in the chain of any final graph (sound pruning).            */
#define HSIZE (1u << 23)
static uint64_t *hkey;
static signed char *hval;
static long long dp_states = 0, comp_rej = 0, comp_ok = 0;
static int dp_ok(const int *c);
static int dp_try(const int *c, int t, int f, int d, int r, int *x) {
    if (r == 0) {
        int c2[10];
        for (int i = 0; i <= MAXD; i++) c2[i] = c[i];
        if (t >= 1) { c2[t - 1] -= f; c2[t] += f; }
        for (int i = t; i < MAXD; i++) { c2[i] -= x[i]; c2[i + 1] += x[i]; }
        c2[t] += 1;
        return dp_ok(c2);
    }
    if (d >= MAXD) return 0;
    int maxx = c[d] < r ? c[d] : r;
    for (int xx = maxx; xx >= 0; xx--) {
        x[d] = xx;
        int ok = dp_try(c, t, f, d + 1, r - xx, x);
        x[d] = 0;
        if (ok) return 1;
    }
    return 0;
}
static int dp_ok(const int *c) {
    int k = 0, e2 = 0, delta = -1;
    for (int d = 0; d <= MAXD; d++) {
        k += c[d];
        e2 += d * c[d];
        if (delta < 0 && c[d] > 0) delta = d;
    }
    int e = e2 / 2;
    if (k == N) return e == EF && delta >= MINDF;
    if (k > N) return 0;
    uint64_t key = 1;
    for (int d = 0; d <= MAXD; d++) key += (uint64_t)c[d] << (5 * d);
    uint32_t h = (uint32_t)((key * 0x9E3779B97F4A7C15ull) >> 40) & (HSIZE - 1);
    while (hkey[h]) {
        if (hkey[h] == key) return hval[h];
        h = (h + 1) & (HSIZE - 1);
    }
    int res = 0, k1 = k + 1;
    int tmax = MAXD;
    if (tmax > k) tmax = k;
    if (tmax > delta + 1) tmax = delta + 1;
    if (tmax > CAP[k1]) tmax = CAP[k1];
    for (int t = tmax; t >= 0 && !res; t--) {
        if (e + t < Lb[k1] || e + t > Ub[k1]) continue;
        if (k1 == N && t < MINDF) continue;
        int f = (t >= 1) ? c[t - 1] : 0;
        if (f > t) continue;
        int x[10] = {0};
        res = dp_try(c, t, f, t, t - f, x);
    }
    h = (uint32_t)((key * 0x9E3779B97F4A7C15ull) >> 40) & (HSIZE - 1);
    while (hkey[h]) h = (h + 1) & (HSIZE - 1);
    hkey[h] = key;
    hval[h] = (signed char)res;
    if (++dp_states > (long long)(HSIZE * 0.7)) { fprintf(stderr, "dp table full\n"); exit(6); }
    return res;
}

/* ---------------- generation ---------------- */
#define MAXTIGHT 70000
static bits *tightT[MAXV + 2];
static signed char *tightB[MAXV + 2];
static unsigned char *eT[MAXV + 2];

#define MAXSIB 70000
static graph *sibcan[MAXV + 2];
static int nsib[MAXV + 2];

static void extend(int k, const bits *adj, const int *deg, int e);

static int lazy_ntight[MAXV + 2], lazy_aut[MAXV + 2], lazy_thi[MAXV + 2];
static int ensure_tight(int k, const bits *adj) {
    if (lazy_ntight[k] >= 0) return lazy_ntight[k];
    int k1 = k + 1, thi = lazy_thi[k], ntight = 0;
    unsigned char *E = eT[k];
    E[0] = 0;
    bits full = BIT(k) - 1;
    for (bits T = 1; T <= full; T++) {
        int u = ctz(T);
        bits rest = T & (T - 1);
        E[T] = E[rest] + popc(adj[u] & rest);
        int sz = popc(T);
        if (sz + 1 < SPMIN || sz + 1 > SPMAX) continue;
        if (k1 == N && T == full) continue; /* S = V(H) is not proper */
        int b = 3 * (sz + 1) - SP - E[T];
        if (b < thi && b < sz) {
            if (ntight >= MAXTIGHT) { fprintf(stderr, "tight overflow\n"); exit(5); }
            tightT[k][ntight] = T;
            tightB[k][ntight] = (signed char)b;
            ntight++;
        }
    }
    lazy_ntight[k] = ntight;
    return ntight;
}
static int ensure_aut(int k, const bits *adj) {
    if (lazy_aut[k] >= 0) return lazy_aut[k];
    int lab[MAXN], orbits[MAXN];
    graph canong[MAXN];
    lazy_aut[k] = run_nauty(k, adj, lab, orbits, canong);
    return lazy_aut[k];
}

static int lookahead_ok(int k1, int e1, int delta1, const int *deg1) {
    /* graph on k1 vertices, e1 edges, min degree delta1 */
    if (k1 >= N) return 1;
    if (delta1 + (N - k1) < MINDF) return 0;
    int add = 0;
    for (int j = k1 + 1; j <= N; j++) {
        int c = delta1 + (j - k1);
        if (c > MAXD) c = MAXD;
        if (c > CAP[j]) c = CAP[j];
        if (c > j - 1) c = j - 1;
        add += c;
    }
    if (e1 + add < EF) return 0;
    int demand = 0;
    for (int i = 0; i < k1; i++)
        if (deg1[i] < MINDF) demand += MINDF - deg1[i];
    if (demand > EF - e1) return 0;
    return 1;
}

static void consider_child(int k, const bits *adj, const int *deg, int e, int t, bits Nset,
                           int ntight, int autP_trivial) {
    int k1 = k + 1, v = k;
    tested[k1]++;
    bits adj2[MAXV];
    int deg2[MAXV];
    for (int i = 0; i < k; i++) {
        adj2[i] = adj[i];
        deg2[i] = deg[i];
        if (Nset >> i & 1) { adj2[i] |= BIT(v); deg2[i]++; }
    }
    adj2[v] = Nset;
    deg2[v] = t;
    int e1 = e + t;
    if (LOOKAHEAD == 2 && !lookahead_ok(k1, e1, t, deg2)) { la_rej[k1]++; return; } /* DP implies this; -C re-enables as a check */
    /* invariant pre-filter for canonical deletion among min-degree vertices (degree t):
       v must have the largest invariant; reject as soon as some vertex beats it */
    uint64_t invv, best;
    int ties = 1;
    {
        uint64_t sv = 0;
        int tri = 0;
        bits a = adj2[v];
        while (a) {
            int w = ctz(a);
            a &= a - 1;
            sv += (uint64_t)1 << (3 * deg2[w]);
            tri += popc(adj2[w] & adj2[v]);
        }
        invv = (sv << 6) | (uint64_t)(tri / 2);
    }
    best = invv;
    for (int u = 0; u < k; u++) {
        if (deg2[u] != t) continue;
        uint64_t su = 0;
        bits a = adj2[u];
        int tri = 0;
        while (a) {
            int w = ctz(a);
            a &= a - 1;
            su += (uint64_t)1 << (3 * deg2[w]);
            tri += popc(adj2[w] & adj2[u]);
        }
        uint64_t iv = (su << 6) | (uint64_t)(tri / 2);
        if (iv > invv) { best = iv; break; }
        if (iv == invv) ties++;
    }
    if (invv < best) { inv_rej[k1]++; return; }
    if (has_pair_through(k1, adj2, v)) { pair_rej[k1]++; return; }
    /* sparsity for sets through v */
    ntight = ensure_tight(k, adj);
    for (int i = 0; i < ntight; i++)
        if (popc(Nset & tightT[k][i]) > tightB[k][i]) {
            /* re-verify by direct count: e(T + v) > 3|T + v| - SP */
            bits T = tightT[k][i];
            int eS = popc(Nset & T), sz = popc(T) + 1;
            for (int u = 0; u < k; u++) if (T >> u & 1) eS += popc(adj[u] & T);
            eS = popc(Nset & T) + (eS - popc(Nset & T)) / 2;
            if (!(eS > 3 * sz - SP) || sz < SPMIN || sz > SPMAX) { fprintf(stderr, "SPARSITY VERIFY FAIL\n"); exit(8); }
            sparse_rej[k1]++;
            return;
        }
    int lab[MAXN], orbits[MAXN];
    graph canong[MAXN];
    int child_trivial = -1;
    autP_trivial = ensure_aut(k, adj);
    if (ties > 1 || !autP_trivial) {
        child_trivial = run_nauty(k1, adj2, lab, orbits, canong);
        if (ties > 1) {
            int m = -1;
            for (int i = k1 - 1; i >= 0; i--) {
                int u = lab[i];
                if (deg2[u] != t) continue;
                /* recompute invariant of u */
                uint64_t s = 0;
                bits a = adj2[u];
                int tri = 0;
                while (a) {
                    int w = ctz(a);
                    a &= a - 1;
                    s += (uint64_t)1 << (3 * deg2[w]);
                    tri += popc(adj2[w] & adj2[u]);
                }
                uint64_t iv = (s << 6) | (uint64_t)(tri / 2);
                if (iv == best) { m = u; break; }
            }
            if (orbits[m] != orbits[v]) { canon_rej[k1]++; return; }
        }
        if (!autP_trivial) {
            for (int i = 0; i < nsib[k1]; i++)
                if (memcmp(sibcan[k1] + (size_t)i * k1, canong, sizeof(graph) * k1) == 0) {
                    dup_rej[k1]++;
                    return;
                }
            if (nsib[k1] >= MAXSIB) { fprintf(stderr, "sibling overflow\n"); exit(4); }
            memcpy(sibcan[k1] + (size_t)nsib[k1] * k1, canong, sizeof(graph) * k1);
            nsib[k1]++;
        }
    }
    /* accepted */
    nodes[k1]++;
    if (k1 == DUMP) dump_graph(k1, adj2);
    if (k1 >= STOPLEVEL) return;
    if (k1 == N) { report_final(k1, adj2); return; }
    if (k1 == SPLIT) {
        splitidx++;
        if (splitidx % MOD != RES) return;
        if (splitidx <= resume_done) return;
        if (stop_flag) return;
        extend(k1, adj2, deg2, e1);
        resume_done = splitidx;
        subtrees_done++;
        if (now() - t_start > TBUDGET) stop_flag = 1;
        static double lastsave = 0;
        if (now() - lastsave > 20) { save_state("running"); lastsave = now(); }
        return;
    }
    if (stop_flag) return;
    extend(k1, adj2, deg2, e1);
}


static void enum_class(int k, const bits *adj, const int *deg, int e, int t, bits base, int ntight,
                       int autP_trivial, const bits *Acls, const int *x, int d) {
    if (d >= MAXD) { consider_child(k, adj, deg, e, t, base, ntight, autP_trivial); return; }
    if (x[d] == 0) { enum_class(k, adj, deg, e, t, base, ntight, autP_trivial, Acls, x, d + 1); return; }
    int av[MAXV], c = 0;
    bits tA = Acls[d];
    while (tA) { av[c++] = ctz(tA); tA &= tA - 1; }
    int r = x[d], idx[MAXV];
    for (int i = 0; i < r; i++) idx[i] = i;
    for (;;) {
        bits X = 0;
        for (int i = 0; i < r; i++) X |= BIT(av[idx[i]]);
        enum_class(k, adj, deg, e, t, base | X, ntight, autP_trivial, Acls, x, d + 1);
        if (stop_flag && k + 1 <= SPLIT) return;
        int i = r - 1;
        while (i >= 0 && idx[i] == c - r + i) i--;
        if (i < 0) break;
        idx[i]++;
        for (int j = i + 1; j < r; j++) idx[j] = idx[j - 1] + 1;
    }
}

static void enum_comp(int k, const bits *adj, const int *deg, int e, int t, bits F, int ntight, int autP_trivial,
                      const bits *Acls, int *x, int d, int r, const int *hc) {
    if (d >= MAXD) {
        if (r != 0) return;
        if (LOOKAHEAD) {
            int c2[10];
            for (int i = 0; i <= MAXD; i++) c2[i] = hc[i];
            int f = popc(F);
            if (t >= 1) { c2[t - 1] -= f; c2[t] += f; }
            for (int i = t; i < MAXD; i++) { c2[i] -= x[i]; c2[i + 1] += x[i]; }
            c2[t] += 1;
            if (!dp_ok(c2)) { comp_rej++; return; }
            comp_ok++;
        }
        enum_class(k, adj, deg, e, t, F, ntight, autP_trivial, Acls, x, t);
        return;
    }
    int avail = popc(Acls[d]);
    int maxx = avail < r ? avail : r;
    for (int xx = 0; xx <= maxx; xx++) {
        x[d] = xx;
        enum_comp(k, adj, deg, e, t, F, ntight, autP_trivial, Acls, x, d + 1, r - xx, hc);
        if (stop_flag && k + 1 <= SPLIT) { x[d] = 0; return; }
    }
    x[d] = 0;
}

static void extend(int k, const bits *adj, const int *deg, int e) {
    if (k >= N) return;
    int k1 = k + 1;
    int delta = 99;
    for (int i = 0; i < k; i++) if (deg[i] < delta) delta = deg[i];
    if (k == 0) delta = 0;
    int tlo = Lb[k1] - e;
    if (tlo < 0) tlo = 0;
    if (k1 == N && tlo < MINDF) tlo = MINDF;
    int thi = Ub[k1] - e;
    if (thi > MAXD) thi = MAXD;
    if (thi > k) thi = k;
    if (thi > delta + 1) thi = delta + 1;
    if (tlo > thi) return;
    /* tight sets and Aut(P) are computed lazily (ensure_tight / ensure_aut), only when a child
       survives the invariant and pair filters */
    lazy_ntight[k] = -1;
    lazy_aut[k] = -1;
    lazy_thi[k] = thi;
    int ntight = 0, autP_trivial = 1; /* unused placeholders */
    nsib[k1] = 0;
    for (int t = tlo; t <= thi; t++) {
        bits F = 0, A = 0;
        int bad = 0;
        for (int i = 0; i < k; i++) {
            if (deg[i] < t - 1) { bad = 1; break; }
            if (deg[i] == t - 1) F |= BIT(i);
            else if (deg[i] < MAXD) A |= BIT(i);
        }
        if (bad) continue;
        int f = popc(F);
        if (f > t) continue;
        int r = t - f;
        int na = popc(A);
        if (r > na) continue;
        /* group the optional neighbours by degree; enumerate degree compositions, prune each
           composition with the histogram look-ahead, then enumerate the subsets it allows */
        bits Acls[10];
        int hc[10], x[10];
        for (int d = 0; d <= MAXD + 1; d++) { Acls[d] = 0; hc[d] = 0; x[d] = 0; }
        for (int i = 0; i < k; i++) {
            hc[deg[i]]++;
            if (A >> i & 1) Acls[deg[i]] |= BIT(i);
        }
        enum_comp(k, adj, deg, e, t, F, ntight, autP_trivial, Acls, x, t, r, hc);
        if (stop_flag && k1 <= SPLIT) return;
    }
}

static void test_mode(void) {
    int n, m;
    while (scanf("%d %d", &n, &m) == 2) {
        bits adj[MAXV] = {0};
        for (int i = 0; i < m; i++) {
            int a, b;
            if (scanf("%d %d", &a, &b) != 2) return;
            adj[a] |= BIT(b);
            adj[b] |= BIT(a);
        }
        int res = 0;
        for (int v = 0; v < n && !res; v++) res = has_pair_through(n, adj, v);
        printf("%d\n", res);
    }
}

int main(int argc, char **argv) {
    if (argc >= 2 && !strcmp(argv[1], "-p")) { test_mode(); return 0; }
    if (argc >= 2 && !strcmp(argv[1], "-p1")) { PAIRV = 1; test_mode(); return 0; }
    if (argc >= 2 && !strcmp(argv[1], "-p2")) { PAIRV = 2; test_mode(); return 0; }
    if (argc >= 2 && !strcmp(argv[1], "-pa")) { SDESC = 0; test_mode(); return 0; }
    if (argc < 6) {
        fprintf(stderr, "usage: gen585 N EF SP SPMIN MINDF [-s split -r res -m mod -t sec -f state -o out -d lvl -L]\n");
        return 1;
    }
    N = atoi(argv[1]);
    EF = atoi(argv[2]);
    SP = atoi(argv[3]);
    SPMIN = atoi(argv[4]);
    MINDF = atoi(argv[5]);
    for (int i = 6; i < argc; i++) {
        if (!strcmp(argv[i], "-s")) SPLIT = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-r")) RES = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-m")) MOD = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-t")) TBUDGET = atof(argv[++i]);
        else if (!strcmp(argv[i], "-f")) STATEF = argv[++i];
        else if (!strcmp(argv[i], "-o")) OUTF = argv[++i];
        else if (!strcmp(argv[i], "-d")) DUMP = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-L")) LOOKAHEAD = 0;
        else if (!strcmp(argv[i], "-x")) SPMAX = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-S")) STOPLEVEL = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-P1")) PAIRV = 1;
        else if (!strcmp(argv[i], "-P2")) PAIRV = 2;
        else if (!strcmp(argv[i], "-A")) SDESC = 0;
        else if (!strcmp(argv[i], "-C")) LOOKAHEAD = 2;
        else { fprintf(stderr, "bad arg %s\n", argv[i]); return 1; }
    }
    if (N < 2 || N > 17) { fprintf(stderr, "N out of range\n"); return 1; }
    nauty_check(WORDSIZE, 1, N, NAUTYVERSIONID);
    if (SPMAX < 0) SPMAX = N - 1;
    /* bounds */
    Ub[N] = EF;
    Lb[N] = EF;
    for (int k = 1; k < N; k++) {
        int u = (k >= SPMIN && k <= SPMAX) ? 3 * k - SP : k * (k - 1) / 2;
        if (u > k * (k - 1) / 2) u = k * (k - 1) / 2;
        if (u > MAXD * k / 2) u = MAXD * k / 2;
        Ub[k] = u;
    }
    for (int k = N - 1; k >= 1; k--) {
        int l = Lb[k + 1] - (2 * Lb[k + 1]) / (k + 1);
        Lb[k] = l < 0 ? 0 : l;
    }
    for (int j = 1; j <= N; j++) CAP[j] = (2 * Ub[j]) / j;
    fprintf(stderr, "N=%d EF=%d SP=%d SPMIN=%d SPMAX=%d MINDF=%d split=%d res=%d mod=%d lookahead=%d\n", N, EF, SP,
            SPMIN, SPMAX, MINDF, SPLIT, RES, MOD, LOOKAHEAD);
    for (int k = 1; k <= N; k++) fprintf(stderr, "  k=%d L=%d U=%d cap=%d\n", k, Lb[k], Ub[k], CAP[k]);
    for (int k = 0; k <= N; k++) {
        tightT[k] = malloc(sizeof(bits) * MAXTIGHT);
        tightB[k] = malloc(MAXTIGHT);
        eT[k] = malloc((size_t)1 << (k > 0 ? k : 1));
        sibcan[k] = malloc(sizeof(graph) * (size_t)MAXSIB * (k > 0 ? k : 1));
    }
    hkey = calloc(HSIZE, sizeof(uint64_t));
    hval = calloc(HSIZE, 1);
    load_state();
    t_start = now();
    /* root: single vertex */
    bits adj[MAXV] = {0};
    int deg[MAXV] = {0};
    nodes[1] = 1;
    if (DUMP == 1) dump_graph(1, adj);
    if (N == 1) return 0;
    extend(1, adj, deg, 0);
    const char *status = stop_flag ? "partial" : "complete";
    save_state(status);
    double el = now() - t_start;
    printf("STATUS %s seconds=%.1f total_seconds=%.1f finals=%lld nauty=%lld done_idx=%lld dp_states=%lld comp_ok=%lld comp_rej=%lld pairs_verified=%lld pairv=%d\n", status, el,
           base_seconds + el, base_finals + finals, nauty_calls, resume_done, dp_states, comp_ok, comp_rej, pairs_verified, PAIRV);
    for (int k = 1; k <= N; k++) {
        long long nk = (k > SPLIT && SPLIT > 0) ? base_nodes[k] + nodes[k] : nodes[k];
        printf("level %2d nodes %lld (this run %lld) tested %lld sparse_rej %lld la_rej %lld inv_rej %lld "
               "pair_rej %lld canon_rej %lld dup_rej %lld\n",
               k, nk, nodes[k], tested[k], sparse_rej[k], la_rej[k], inv_rej[k], pair_rej[k], canon_rej[k],
               dup_rej[k]);
    }
    return 0;
}
