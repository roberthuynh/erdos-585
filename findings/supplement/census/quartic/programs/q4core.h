/* q4core.h: exact search for a nonempty subgraph H with every degree in {0,4}
 * (a 4-regular subgraph on some vertex subset). Graphs up to 32 vertices,
 * adjacency as bitmasks with bit i = vertex i.
 *
 * Method: depth-first search. The root r is forced into H. At each node we take
 * an "open" vertex (in H, H-degree < 4) with the fewest completions and branch
 * over every way to choose its remaining H-edges among edges to vertices that
 * are allowed and not yet closed (closed = H-degree 4, frozen). A vertex outside
 * H whose available degree drops below 4 is removed (4-core style cascade).
 * Every 4-regular subgraph containing r corresponds to a branch, so the search
 * is exact. */
#ifndef Q4CORE_H
#define Q4CORE_H
#include <stdint.h>
#include <string.h>
typedef uint32_t u32;
#define Q4MAX 32

typedef struct {
    u32 H[Q4MAX];      /* selected edges */
    unsigned char hdeg[Q4MAX];
    u32 closed;        /* in H with H-degree 4: frozen */
    u32 inset;         /* vertices of H (H-degree > 0, or the root) */
    u32 allowed;       /* vertices that may still be used */
} q4state;

static int q4_n;
static const u32 *q4_G;
static long long q4_nodes;
static q4state q4_found;     /* witness of the last successful search */

static const int q4_binom[33][5] = {
 {1,0,0,0,0},{1,1,0,0,0},{1,2,1,0,0},{1,3,3,1,0},{1,4,6,4,1},{1,5,10,10,5},
 {1,6,15,20,15},{1,7,21,35,35},{1,8,28,56,70},{1,9,36,84,126},{1,10,45,120,210},
 {1,11,55,165,330},{1,12,66,220,495},{1,13,78,286,715},{1,14,91,364,1001},
 {1,15,105,455,1365},{1,16,120,560,1820},{1,17,136,680,2380},{1,18,153,816,3060},
 {1,19,171,969,3876},{1,20,190,1140,4845},{1,21,210,1330,5985},{1,22,231,1540,7315},
 {1,23,253,1771,8855},{1,24,276,2024,10626},{1,25,300,2300,12650},{1,26,325,2600,14950},
 {1,27,351,2925,17550},{1,28,378,3276,20475},{1,29,406,3654,23751},{1,30,435,4060,27405},
 {1,31,465,4495,31465},{1,32,496,4960,35960}};

/* remove vertices outside H that can no longer reach degree 4; return 0 on contradiction */
static int q4_cascade(q4state *s) {
    int changed = 1;
    while (changed) {
        changed = 0;
        u32 avail = s->allowed & ~s->closed;
        for (u32 o = s->allowed & ~s->inset; o; o &= o - 1) {
            int u = __builtin_ctz(o);
            if (__builtin_popcount(q4_G[u] & avail) < 4) {
                s->allowed &= ~(1u << u);
                avail &= ~(1u << u);
                changed = 1;
            }
        }
    }
    /* open vertices must still be completable */
    u32 avail = s->allowed & ~s->closed;
    for (u32 o = s->inset & ~s->closed; o; o &= o - 1) {
        int v = __builtin_ctz(o);
        int need = 4 - s->hdeg[v];
        if (__builtin_popcount(q4_G[v] & avail & ~s->H[v]) < need) return 0;
    }
    return 1;
}

static int q4_rec(q4state *s) {
    q4_nodes++;
    u32 open = s->inset & ~s->closed;
    if (!open) { q4_found = *s; return 1; }
    u32 avail = s->allowed & ~s->closed;
    int best = -1, bestcnt = 1 << 30; u32 bestcand = 0;
    for (u32 o = open; o; o &= o - 1) {
        int v = __builtin_ctz(o);
        int need = 4 - s->hdeg[v];
        u32 cand = q4_G[v] & avail & ~s->H[v] & ~(1u << v);
        int c = __builtin_popcount(cand);
        if (c < need) return 0;
        int cnt = q4_binom[c][need];
        if (cnt < bestcnt) { bestcnt = cnt; best = v; bestcand = cand; }
    }
    int v = best, need = 4 - s->hdeg[v];
    /* enumerate subsets of bestcand of size need */
    for (u32 sub = bestcand; ; sub = (sub - 1) & bestcand) {
        if (__builtin_popcount(sub) == need) {
            q4state t = *s;
            int ok = 1;
            for (u32 o = sub; o; o &= o - 1) {
                int u = __builtin_ctz(o);
                t.H[v] |= 1u << u; t.H[u] |= 1u << v;
                t.hdeg[v]++; t.hdeg[u]++;
                t.inset |= 1u << u;
                if (t.hdeg[u] > 4) { ok = 0; break; }
                if (t.hdeg[u] == 4) t.closed |= 1u << u;
            }
            if (ok) {
                t.closed |= 1u << v;          /* v is now complete */
                if (q4_cascade(&t) && q4_rec(&t)) return 1;
            }
        }
        if (sub == 0) break;
    }
    return 0;
}

/* 4-core of the subgraph induced on mask */
static u32 q4_core(const u32 *G, int n, u32 mask) {
    int changed = 1;
    while (changed) {
        changed = 0;
        for (u32 o = mask; o; o &= o - 1) {
            int u = __builtin_ctz(o);
            if (__builtin_popcount(G[u] & mask) < 4) { mask &= ~(1u << u); changed = 1; }
        }
    }
    return mask;
}

/* Is there a 4-regular subgraph containing r and using only vertices in mask? */
static int q4_rooted(const u32 *G, int n, int r, u32 mask) {
    q4_G = G; q4_n = n;
    mask = q4_core(G, n, mask);
    if (!(mask >> r & 1)) return 0;
    q4state s; memset(&s, 0, sizeof s);
    s.allowed = mask; s.inset = 1u << r;
    if (!q4_cascade(&s)) return 0;
    return q4_rec(&s);
}

/* Full test: does G have any 4-regular subgraph? */
static int q4_any(const u32 *G, int n) {
    u32 all = (n == 32) ? 0xffffffffu : ((1u << n) - 1);
    u32 core = q4_core(G, n, all);
    for (int r = 0; r < n; r++) {
        if (!(core >> r & 1)) continue;
        u32 mask = core & ~((1u << r) - 1);   /* vertices >= r */
        if (q4_rooted(G, n, r, mask)) return 1;
    }
    return 0;
}
#endif
