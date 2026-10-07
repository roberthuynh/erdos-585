/* h4.h -- method B decider (wave8/exb): does a graph have a nonempty
   4-regular subgraph?  Written from scratch for this lane; it shares no
   code with method 1 (q4core.h, q4prune_bg.c, genbg_q4).

   Graphs have n <= 32 vertices.  adj[u] is a bit mask: bit w is set iff
   uw is an edge.  No loops (adj[u] never contains u).

   A subgraph H is "4-regular" if every vertex of H has degree exactly 4
   in H.  Every such H lies inside the 4-core of G (the largest vertex set
   K with every vertex of K adjacent to at least 4 vertices of K), because
   H has minimum degree 4.

   h4_through(adj, n, K, v, cert)
       K must be closed under the 4-core rule (h4_core4 output) and contain
       v.  Returns 1 iff G[K] has a 4-regular subgraph H with v in V(H);
       then cert[u] is the H-neighbourhood of u.  Every answer 1 is checked
       by h4_cert_ok before it is returned; a failed check aborts.

   h4_any(adj, n)
       1 iff G has a nonempty 4-regular subgraph (any H either contains the
       chosen vertex v or lies in G - v; repeat on the 4-core of G - v).

   Search: a state holds, for every vertex u, sel[u] (edges at u chosen
   for H) and av[u] (edges at u still undecided).  Edges that are neither
   are excluded from H.  Propagation rules (all consistent with any H that
   agrees with the decisions so far):
     - |sel[x]| = 0 and |av[x]| < 4: x is not in H; exclude its edges.
     - |sel[x]| > 4, or 0 < |sel[x]| and |sel[x]| + |av[x]| < 4: conflict.
     - |sel[x]| = 4: exclude its undecided edges.
     - 0 < |sel[x]| and |sel[x]| + |av[x]| = 4: choose all of av[x].
   Branching: a vertex u with 1 <= |sel[u]| <= 3 is in H and needs exactly
   4 - |sel[u]| more edges from av[u]; try every such subset (fewest
   subsets first).  The search starts by choosing 4 edges at v.  When no
   vertex has 1..3 chosen edges, the chosen edges form a 4-regular graph. */

#ifndef H4_H
#define H4_H

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define H4MAXN 32
typedef uint32_t h4set;

#define H4BIT(x) ((h4set)1 << (x))
#define H4POP(x) __builtin_popcount(x)
#define H4LOW(x) __builtin_ctz(x)

typedef struct {
    h4set sel[H4MAXN];
    h4set av[H4MAXN];
} h4state;

static const int h4binom[8][5] = {
    {1, 0, 0, 0, 0}, {1, 1, 0, 0, 0}, {1, 2, 1, 0, 0}, {1, 3, 3, 1, 0},
    {1, 4, 6, 4, 1}, {1, 5, 10, 10, 5}, {1, 6, 15, 20, 15}, {1, 7, 21, 35, 35}};

static unsigned long long h4_nodes = 0; /* search nodes, for statistics */

/* The 4-core of G[alive]. */
static h4set h4_core4(const h4set *adj, int n, h4set alive)
{
    int changed = 1;
    (void)n;
    while (changed) {
        h4set a = alive;
        changed = 0;
        while (a) {
            int u = H4LOW(a);
            a &= a - 1;
            if (H4POP(adj[u] & alive) < 4) {
                alive &= ~H4BIT(u);
                changed = 1;
            }
        }
    }
    return alive;
}

/* 1 iff sel describes a 4-regular subgraph of G that contains v. */
static int h4_cert_ok(const h4set *adj, int n, const h4set *sel, int v)
{
    int u, w;
    if (v < 0 || v >= n || H4POP(sel[v]) != 4) return 0;
    for (u = 0; u < n; ++u) {
        int d = H4POP(sel[u]);
        if (d != 0 && d != 4) return 0;
        if (sel[u] & ~adj[u]) return 0;
        if (sel[u] & H4BIT(u)) return 0;
        for (w = 0; w < n; ++w)
            if ((sel[u] & H4BIT(w)) && !(sel[w] & H4BIT(u))) return 0;
    }
    for (u = n; u < H4MAXN; ++u)
        if (sel[u]) return 0;
    return 1;
}

/* Propagate to a fixpoint from the vertices in todo; 0 on conflict. */
static int h4_prop(h4state *s, h4set todo)
{
    while (todo) {
        int x = H4LOW(todo);
        int cs, ca;
        todo &= todo - 1;
        cs = H4POP(s->sel[x]);
        ca = H4POP(s->av[x]);
        if (cs > 4) return 0;
        if (cs == 0) {
            if (ca > 0 && ca < 4) {
                h4set a = s->av[x];
                s->av[x] = 0;
                while (a) {
                    int w = H4LOW(a);
                    a &= a - 1;
                    s->av[w] &= ~H4BIT(x);
                    todo |= H4BIT(w);
                }
            }
        } else {
            if (cs + ca < 4) return 0;
            if (ca > 0 && cs == 4) {
                h4set a = s->av[x];
                s->av[x] = 0;
                while (a) {
                    int w = H4LOW(a);
                    a &= a - 1;
                    s->av[w] &= ~H4BIT(x);
                    todo |= H4BIT(w);
                }
            } else if (ca > 0 && cs + ca == 4) {
                h4set a = s->av[x];
                s->av[x] = 0;
                s->sel[x] |= a;
                while (a) {
                    int w = H4LOW(a);
                    a &= a - 1;
                    s->av[w] &= ~H4BIT(x);
                    s->sel[w] |= H4BIT(x);
                    todo |= H4BIT(w);
                }
            }
        }
    }
    return 1;
}

static int h4_rec(h4state *s, h4set K, h4state *out);

/* Branch at u: choose exactly need = 4 - |sel[u]| edges of av[u]. */
static int h4_branch(h4state *s, h4set K, int u, h4state *out)
{
    int need = 4 - H4POP(s->sel[u]);
    h4set av = s->av[u];
    h4set t = av;
    if (need < 1 || H4POP(av) < need) return 0;
    for (;;) {
        if (H4POP(t) == need) {
            h4state s2 = *s;
            h4set drop = av & ~t, a = av;
            ++h4_nodes;
            s2.sel[u] |= t;
            s2.av[u] = 0;
            while (a) {
                int w = H4LOW(a);
                a &= a - 1;
                s2.av[w] &= ~H4BIT(u);
                if (t & H4BIT(w)) s2.sel[w] |= H4BIT(u);
            }
            (void)drop;
            if (h4_prop(&s2, av | H4BIT(u)) && h4_rec(&s2, K, out)) return 1;
        }
        if (t == 0) break;
        t = (t - 1) & av;
    }
    return 0;
}

static int h4_rec(h4state *s, h4set K, h4state *out)
{
    h4set k = K;
    int best = -1, bestc = 1 << 30;
    while (k) {
        int x = H4LOW(k), cs, c, ca;
        k &= k - 1;
        cs = H4POP(s->sel[x]);
        if (cs == 0 || cs == 4) continue;
        ca = H4POP(s->av[x]);
        if (ca > 7) ca = 7; /* cannot happen with max degree <= 7 */
        if (ca < 4 - cs) return 0;
        c = h4binom[ca][4 - cs];
        if (c < bestc) {
            bestc = c;
            best = x;
        }
    }
    if (best < 0) {
        *out = *s;
        return 1;
    }
    return h4_branch(s, K, best, out);
}

/* Does G[K] (K a 4-core containing v) have a 4-regular subgraph through v? */
static int h4_through(const h4set *adj, int n, h4set K, int v, h4set *cert)
{
    h4state s, out;
    int u, r;
    if (!(K & H4BIT(v))) return 0;
    memset(&s, 0, sizeof s);
    for (u = 0; u < n; ++u) s.av[u] = (K & H4BIT(u)) ? (adj[u] & K) : 0;
    for (u = 0; u < n; ++u)
        if (H4POP(s.av[u]) > 7) {
            fprintf(stderr, "h4: degree above 7 is not supported\n");
            abort();
        }
    r = h4_branch(&s, K, v, &out);
    if (r) {
        if (!h4_cert_ok(adj, n, out.sel, v)) {
            fprintf(stderr, "h4: certificate check failed\n");
            abort();
        }
        if (cert) memcpy(cert, out.sel, sizeof out.sel);
    }
    return r;
}

/* Does G have a nonempty 4-regular subgraph? */
static int h4_any(const h4set *adj, int n, h4set *cert)
{
    h4set all = (n == 32) ? ~(h4set)0 : (H4BIT(n) - 1);
    h4set K = h4_core4(adj, n, all);
    while (K) {
        int v = H4LOW(K);
        if (h4_through(adj, n, K, v, cert)) return 1;
        K = h4_core4(adj, n, K & ~H4BIT(v));
    }
    return 0;
}

#endif
