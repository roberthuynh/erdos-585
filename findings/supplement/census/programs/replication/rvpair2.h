/* rvpair2.h -- reviewer's second pair test (SMS-CENSUS-REVIEW), faster than rvpair.h.
 * Requires rvpair.h (shares rv_verify, rv_eid/rv_eu/rv_ev and rv_die).
 *
 * 1. K = 4-core of G; if w is not in K, no pair through w. Restrict to the component of w in G[K]
 *    (a support is connected and lies in the 4-core).
 * 2. List every S with w in S, S inside that component, |S| >= 5 and min degree >= 4 in G[S], by
 *    include/exclude branching with peeling (a vertex with < 4 neighbours among the vertices still
 *    allowed can never be in S). Sort by size, smallest first.
 * 3. For each S, list Hamilton cycles of G[S] from a fixed root (orientation fixed by first
 *    neighbour < last neighbour) as edge masks. A new cycle is compared with every stored cycle of
 *    the same S. A disjoint match is a pair, and it is re-checked by rv_verify before it is reported. */

static rvset r2_A[32];
static int r2_root, r2_s, r2_found;
static rvset r2_S, r2_on;
static int r2_path[32], r2_plen;
static rvemask r2_c1, r2_c2;
#define R2_MAXHC 400000
static rvemask *r2_hc = NULL;
static int r2_nhc;
#define R2_MAXSUP 70000
static rvset r2_sup[R2_MAXSUP];
static int r2_nsup;

static void r2_supports(rvset I, rvset U) {
    for (;;) {
        rvset pool = I | U, drop = 0, t = U;
        while (t) {
            int u = __builtin_ctz(t);
            t &= t - 1;
            if (rv_pop(r2_A[u] & pool) < 4) drop |= 1u << u;
        }
        if (!drop) break;
        U &= ~drop;
    }
    rvset pool = I | U, t = I;
    while (t) {
        int v = __builtin_ctz(t);
        t &= t - 1;
        if (rv_pop(r2_A[v] & pool) < 4) return;
    }
    if (!U) {
        if (rv_pop(I) >= 5) {
            if (r2_nsup >= R2_MAXSUP) rv_die("support list overflow");
            r2_sup[r2_nsup++] = I;
        }
        return;
    }
    int u = __builtin_ctz(U);
    r2_supports(I | (1u << u), U & ~(1u << u));
    r2_supports(I, U & ~(1u << u));
}

static void r2_hc_dfs(int cur, rvemask em) {
    if (r2_plen == r2_s) {
        if (!((r2_A[cur] >> r2_root) & 1u) || !(r2_path[1] < cur)) return;
        rvemask e = em | ((rvemask)1 << rv_eid[cur][r2_root]);
        for (int i = 0; i < r2_nhc; i++) {
            if ((r2_hc[i] & e) == 0) {
                r2_found = 1;
                r2_c1 = r2_hc[i];
                r2_c2 = e;
                return;
            }
        }
        if (r2_nhc >= R2_MAXHC) rv_die("hamilton cycle list overflow");
        r2_hc[r2_nhc++] = e;
        return;
    }
    rvset unv = r2_S & ~r2_on;
    rvset pool = unv | (1u << cur) | (1u << r2_root);
    rvset t = unv;
    while (t) {
        int u = __builtin_ctz(t);
        t &= t - 1;
        if (rv_pop(r2_A[u] & pool & ~(1u << u)) < 2) return;
    }
    rvset cand = r2_A[cur] & unv;
    while (cand) {
        int u = __builtin_ctz(cand);
        cand &= cand - 1;
        r2_path[r2_plen++] = u;
        r2_on |= 1u << u;
        r2_hc_dfs(u, em | ((rvemask)1 << rv_eid[cur][u]));
        r2_plen--;
        r2_on &= ~(1u << u);
        if (r2_found) return;
    }
}

static int r2_cmp_pop(const void *a, const void *b) {
    int x = rv_pop(*(const rvset *)a), y = rv_pop(*(const rvset *)b);
    return (x > y) - (x < y);
}

/* 1 iff G (vertices 0..n-1) has a pair whose support contains w */
static int rv2_pair_through(int n, const rvset *adjG, int w) {
    if (n > 16) rv_die("n > 16");
    if (!r2_hc) {
        r2_hc = (rvemask *)malloc(sizeof(rvemask) * R2_MAXHC);
        if (!r2_hc) rv_die("malloc");
    }
    rvset K = (1u << n) - 1;
    for (;;) {
        rvset drop = 0, t = K;
        while (t) {
            int v = __builtin_ctz(t);
            t &= t - 1;
            if (rv_pop(adjG[v] & K) < 4) drop |= 1u << v;
        }
        if (!drop) break;
        K &= ~drop;
    }
    if (!((K >> w) & 1u)) return 0;
    rvset C = 1u << w, fr = C;
    while (fr) {
        int v = __builtin_ctz(fr);
        fr &= fr - 1;
        rvset add = adjG[v] & K & ~C;
        C |= add;
        fr |= add;
    }
    if (rv_pop(C) < 5) return 0;
    int ne = 0;
    for (int a = 0; a < n; a++) r2_A[a] = ((C >> a) & 1u) ? (adjG[a] & C) : 0;
    for (int a = 0; a < n; a++) {
        rvset t = r2_A[a] & ~((2u << a) - 1);
        while (t) {
            int b = __builtin_ctz(t);
            t &= t - 1;
            if (ne >= 64) rv_die("more than 64 core edges");
            rv_eid[a][b] = rv_eid[b][a] = ne;
            rv_eu[ne] = a;
            rv_ev[ne] = b;
            ne++;
        }
    }
    r2_nsup = 0;
    r2_supports(1u << w, C & ~(1u << w));
    if (r2_nsup > 1) qsort(r2_sup, r2_nsup, sizeof(rvset), r2_cmp_pop);
    for (int i = 0; i < r2_nsup; i++) {
        r2_S = r2_sup[i];
        r2_s = rv_pop(r2_S);
        /* root: a vertex of least degree in G[S] */
        int best = 99;
        rvset t = r2_S;
        while (t) {
            int v = __builtin_ctz(t);
            t &= t - 1;
            int d = rv_pop(r2_A[v] & r2_S);
            if (d < best) { best = d; r2_root = v; }
        }
        /* restrict adjacency to S for the cycle search */
        rvset save[32];
        for (int a = 0; a < n; a++) { save[a] = r2_A[a]; r2_A[a] = ((r2_S >> a) & 1u) ? (r2_A[a] & r2_S) : 0; }
        r2_nhc = 0;
        r2_found = 0;
        r2_path[0] = r2_root;
        r2_plen = 1;
        r2_on = 1u << r2_root;
        r2_hc_dfs(r2_root, 0);
        for (int a = 0; a < n; a++) r2_A[a] = save[a];
        if (r2_found) {
            rv_verify(adjG, r2_S, r2_c1, r2_c2);
            return 1;
        }
    }
    return 0;
}

static int rv2_has_pair(int n, const rvset *adjG) {
    for (int w = 0; w < n; w++)
        if (rv2_pair_through(n, adjG, w)) return 1;
    return 0;
}
