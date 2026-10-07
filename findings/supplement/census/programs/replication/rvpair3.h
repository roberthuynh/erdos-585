/* rvpair3.h -- reviewer's third pair test (SMS-CENSUS-REVIEW), tuned for graphs that do have a pair.
 * Requires rvpair.h and rvpair2.h (shares rv_verify, rv_eid/rv_eu/rv_ev, r2_A, r2_supports, r2_sup).
 *
 * Supports are the same as in rvpair2.h (w in S, S inside the 4-core component of w, |S| >= 5,
 * min degree >= 4 in G[S]); the whole component is tried first, then the rest by increasing size.
 * For a support S: enumerate Hamilton cycles C1 of G[S] from a fixed root (each once, orientation
 * fixed by first neighbour < last neighbour); for each C1, search G[S] - E(C1) for a Hamilton cycle
 * C2. A pair (C1, C2) is re-checked by rv_verify before it is reported. Every pair of S has its
 * C1 among the enumerated cycles (up to orientation), and then C2 lies in the residual graph, so
 * the search is exhaustive. */

static rvset r3_A[32], r3_R[32];
static int r3_root, r3_s, r3_found;
static rvset r3_S, r3_on, r3_on2;
static int r3_path[32], r3_plen, r3_path2[32], r3_plen2, r3_root2;
static rvemask r3_c1, r3_c2;

/* Hamilton cycle in residual r3_R on r3_S from r3_root2; returns 1 and sets r3_c2 */
static int r3_res_dfs(int cur, rvemask em) {
    if (r3_plen2 == r3_s) {
        if (!((r3_R[cur] >> r3_root2) & 1u)) return 0;
        r3_c2 = em | ((rvemask)1 << rv_eid[cur][r3_root2]);
        return 1;
    }
    rvset unv = r3_S & ~r3_on2;
    rvset pool = unv | (1u << cur) | (1u << r3_root2);
    rvset t = unv;
    while (t) {
        int u = __builtin_ctz(t);
        t &= t - 1;
        if (rv_pop(r3_R[u] & pool & ~(1u << u)) < 2) return 0;
    }
    rvset cand = r3_R[cur] & unv;
    while (cand) {
        int u = __builtin_ctz(cand);
        cand &= cand - 1;
        r3_path2[r3_plen2++] = u;
        r3_on2 |= 1u << u;
        int ok = r3_res_dfs(u, em | ((rvemask)1 << rv_eid[cur][u]));
        r3_plen2--;
        r3_on2 &= ~(1u << u);
        if (ok) return 1;
    }
    return 0;
}

static void r3_c1_dfs(int cur, rvemask em) {
    if (r3_plen == r3_s) {
        if (!((r3_A[cur] >> r3_root) & 1u) || !(r3_path[1] < cur)) return;
        rvemask e1 = em | ((rvemask)1 << rv_eid[cur][r3_root]);
        /* residual adjacency on S */
        int r2best = 99;
        rvset t = r3_S;
        while (t) {
            int v = __builtin_ctz(t);
            t &= t - 1;
            r3_R[v] = r3_A[v];
        }
        rvemask m = e1;
        while (m) {
            int i = __builtin_ctzll(m);
            m &= m - 1;
            r3_R[rv_eu[i]] &= ~(1u << rv_ev[i]);
            r3_R[rv_ev[i]] &= ~(1u << rv_eu[i]);
        }
        t = r3_S;
        while (t) {
            int v = __builtin_ctz(t);
            t &= t - 1;
            int d = rv_pop(r3_R[v]);
            if (d < 2) return;
            if (d < r2best) { r2best = d; r3_root2 = v; }
        }
        r3_path2[0] = r3_root2;
        r3_plen2 = 1;
        r3_on2 = 1u << r3_root2;
        if (r3_res_dfs(r3_root2, 0)) {
            r3_found = 1;
            r3_c1 = e1;
        }
        return;
    }
    rvset unv = r3_S & ~r3_on;
    rvset pool = unv | (1u << cur) | (1u << r3_root);
    rvset t = unv;
    while (t) {
        int u = __builtin_ctz(t);
        t &= t - 1;
        if (rv_pop(r3_A[u] & pool & ~(1u << u)) < 2) return;
    }
    rvset cand = r3_A[cur] & unv;
    while (cand) {
        int u = __builtin_ctz(cand);
        cand &= cand - 1;
        r3_path[r3_plen++] = u;
        r3_on |= 1u << u;
        r3_c1_dfs(u, em | ((rvemask)1 << rv_eid[cur][u]));
        r3_plen--;
        r3_on &= ~(1u << u);
        if (r3_found) return;
    }
}

/* test one support S (adjacency r2_A restricted to the component); 1 iff G[S] has a pair */
static int r3_test_support(int n, const rvset *adjG, rvset S) {
    r3_S = S;
    r3_s = rv_pop(S);
    int best = 99;
    for (int a = 0; a < n; a++) r3_A[a] = ((S >> a) & 1u) ? (r2_A[a] & S) : 0;
    rvset t = S;
    while (t) {
        int v = __builtin_ctz(t);
        t &= t - 1;
        int d = rv_pop(r3_A[v]);
        if (d < 4) return 0; /* not a support */
        if (d < best) { best = d; r3_root = v; }
    }
    r3_found = 0;
    r3_path[0] = r3_root;
    r3_plen = 1;
    r3_on = 1u << r3_root;
    r3_c1_dfs(r3_root, 0);
    if (r3_found) {
        rv_verify(adjG, S, r3_c1, r3_c2);
        return 1;
    }
    return 0;
}

static int rv3_pair_through(int n, const rvset *adjG, int w) {
    if (n > 16) rv_die("n > 16");
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
    if (r3_test_support(n, adjG, C)) return 1;
    r2_nsup = 0;
    r2_supports(1u << w, C & ~(1u << w));
    if (r2_nsup > 1) qsort(r2_sup, r2_nsup, sizeof(rvset), r2_cmp_pop);
    for (int i = 0; i < r2_nsup; i++) {
        if (r2_sup[i] == C) continue;
        if (r3_test_support(n, adjG, r2_sup[i])) return 1;
    }
    return 0;
}

static int rv3_has_pair(int n, const rvset *adjG) {
    for (int w = 0; w < n; w++)
        if (rv3_pair_through(n, adjG, w)) return 1;
    return 0;
}
