/* rvpair.h -- reviewer's independent pair test (SMS-CENSUS-REVIEW). Written from scratch; it does
 * not reuse any code from the lane's gen585.c.
 *
 * A pair is two edge-disjoint cycles C1, C2 with V(C1) = V(C2) = S. Every vertex of S then has
 * degree >= 4 in G[S], so |S| >= 5 and S lies inside the 4-core of G.
 *
 * Method: one depth-first search lists every cycle of length >= 5 through a given vertex w inside
 * the 4-core, each cycle once (orientation fixed by first neighbour < last neighbour), as an edge
 * bitmask. Cycles are bucketed by vertex set; a new cycle is compared with every earlier cycle in
 * its bucket, and an edge-disjoint match is a pair. Every pair found is re-checked from the two edge
 * masks alone (each mask must be a connected 2-regular spanning subgraph of G[S], masks disjoint,
 * every edge present in G); a failed check aborts the program. Vertices are bits 0..n-1, n <= 16. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef uint32_t rvset;
typedef uint64_t rvemask;

#define RV_POOLMAX 6000000
typedef struct { rvemask em; int next; } rv_rec;
static rv_rec *rv_pool = NULL;
static int rv_npool;
static int rv_bhead[1 << 16];
static unsigned rv_bstamp[1 << 16];
static unsigned rv_stamp = 0;

static rvset rv_A[32];          /* adjacency restricted to the 4-core */
static int rv_eid[32][32];       /* edge index inside the 4-core */
static int rv_eu[64], rv_ev[64];
static int rv_W, rv_path[32], rv_plen, rv_found;
static rvset rv_on, rv_certS;
static rvemask rv_cert1, rv_cert2;
static long long rv_npairs_verified = 0, rv_max_pool = 0;

static int rv_pop(rvset x) { return __builtin_popcount(x); }

static void rv_die(const char *msg) {
    fprintf(stderr, "rvpair FATAL: %s\n", msg);
    exit(97);
}

/* independent certificate check against the full adjacency adjG */
static void rv_verify(const rvset *adjG, rvset S, rvemask m1, rvemask m2) {
    if (m1 & m2) rv_die("cert: masks share an edge");
    if (rv_pop(S) < 3) rv_die("cert: support too small");
    for (int which = 0; which < 2; which++) {
        rvemask m = which ? m2 : m1;
        int deg[32] = {0};
        rvset nb[32] = {0};
        rvemask t = m;
        while (t) {
            int i = __builtin_ctzll(t);
            t &= t - 1;
            int a = rv_eu[i], b = rv_ev[i];
            if (!((adjG[a] >> b) & 1u)) rv_die("cert: edge not in graph");
            if (!((S >> a) & 1u) || !((S >> b) & 1u)) rv_die("cert: edge leaves support");
            deg[a]++; deg[b]++;
            nb[a] |= 1u << b; nb[b] |= 1u << a;
        }
        rvset s = S;
        while (s) {
            int v = __builtin_ctz(s);
            s &= s - 1;
            if (deg[v] != 2) rv_die("cert: vertex degree in cycle is not 2");
        }
        /* connectivity of the 2-regular graph on S: then it is one Hamilton cycle of G[S] */
        rvset seen = 1u << __builtin_ctz(S), frontier = seen;
        while (frontier) {
            int v = __builtin_ctz(frontier);
            frontier &= frontier - 1;
            rvset add = nb[v] & ~seen;
            seen |= add;
            frontier |= add;
        }
        if (seen != S) rv_die("cert: cycle not connected");
    }
    rv_npairs_verified++;
}

static void rv_dfs(int cur, rvemask em) {
    rvset nb = rv_A[cur];
    if (rv_plen >= 5 && ((nb >> rv_W) & 1u) && rv_path[1] < cur) {
        rvemask e = em | ((rvemask)1 << rv_eid[cur][rv_W]);
        rvset S = rv_on;
        int ok = 1;
        rvset t = S;
        while (t) {
            int v = __builtin_ctz(t);
            t &= t - 1;
            if (rv_pop(rv_A[v] & S) < 4) { ok = 0; break; }
        }
        if (ok) {
            if (rv_bstamp[S] != rv_stamp) { rv_bstamp[S] = rv_stamp; rv_bhead[S] = -1; }
            for (int r = rv_bhead[S]; r >= 0; r = rv_pool[r].next)
                if ((rv_pool[r].em & e) == 0) {
                    rv_found = 1;
                    rv_cert1 = rv_pool[r].em;
                    rv_cert2 = e;
                    rv_certS = S;
                    return;
                }
            if (rv_npool >= RV_POOLMAX) rv_die("cycle pool overflow");
            rv_pool[rv_npool].em = e;
            rv_pool[rv_npool].next = rv_bhead[S];
            rv_bhead[S] = rv_npool;
            rv_npool++;
        }
    }
    rvset cand = nb & ~rv_on;
    while (cand) {
        int u = __builtin_ctz(cand);
        cand &= cand - 1;
        rv_path[rv_plen++] = u;
        rv_on |= 1u << u;
        rv_dfs(u, em | ((rvemask)1 << rv_eid[cur][u]));
        rv_plen--;
        rv_on &= ~(1u << u);
        if (rv_found) return;
    }
}

/* 1 iff G (vertices 0..n-1, adjacency adjG) has a pair whose support contains w */
static int rv_pair_through(int n, const rvset *adjG, int w) {
    if (n > 16) rv_die("n > 16");
    if (!rv_pool) {
        rv_pool = (rv_rec *)malloc(sizeof(rv_rec) * RV_POOLMAX);
        if (!rv_pool) rv_die("malloc");
    }
    /* 4-core by peeling */
    rvset K = (n == 32) ? 0xffffffffu : ((1u << n) - 1);
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
    if (rv_pop(K) < 5) return 0;
    int ne = 0;
    for (int a = 0; a < n; a++) {
        rv_A[a] = ((K >> a) & 1u) ? (adjG[a] & K) : 0;
    }
    for (int a = 0; a < n; a++) {
        rvset t = rv_A[a] & ~((2u << a) - 1); /* b > a */
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
    rv_stamp++;
    if (rv_stamp == 0) { /* wrapped: clear stamps */
        for (int i = 0; i < (1 << 16); i++) rv_bstamp[i] = 0;
        rv_stamp = 1;
    }
    rv_npool = 0;
    rv_found = 0;
    rv_W = w;
    rv_path[0] = w;
    rv_plen = 1;
    rv_on = 1u << w;
    rv_dfs(w, 0);
    if (rv_npool > rv_max_pool) rv_max_pool = rv_npool;
    if (rv_found) rv_verify(adjG, rv_certS, rv_cert1, rv_cert2);
    return rv_found;
}

/* 1 iff G has any pair */
static int rv_has_pair(int n, const rvset *adjG) {
    for (int w = 0; w < n; w++)
        if (rv_pair_through(n, adjG, w)) return 1;
    return 0;
}
