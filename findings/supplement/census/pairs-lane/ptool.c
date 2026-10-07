/* ptool.c -- pairs scout tool (wave3/pairs). graph6 on stdin, n <= 30.
 *
 * Modes (argv[1]):
 *   s        print graphs that are SPARSE: g(S) = 6|S| - 2e(S) >= 10 for every S with
 *            2 <= |S| <= n-1. Exact: an inclusion-minimal violator has an edge, so for every
 *            edge uv we minimize g over S containing u,v by a max flow to a sink z joined to
 *            each v with capacity def(v) = 6 - deg(v) (cut(S) = boundary(S) + def(S) = g(S)),
 *            and for every x we also force x out (so S = V is excluded). Requires Delta <= 6.
 *   S        print graphs that are NOT sparse.
 *   h        spanning-pair test (two edge-disjoint Hamilton cycles of G); prints
 *            "<g6> SP" or "<g6> NOSP".
 *   y n1     C1/C0 port test. Vertices 0..n1-1 are class U, n1..n-1 class W (genbg order).
 *            For every W-vertex y with deg <= 5 (a port): F = 1 if G - y has a 4-factor,
 *            H = 1 if G - y has two edge-disjoint Hamilton cycles. Prints
 *            "<g6> ports=<k> good=<k> sp=<k> list=y:F:H,..."
 *   f        4-factor test of G (balanced bipartite or not; general b-matching by flow only
 *            for bipartite: needs n1 in argv[2]); prints "<g6> F" or "<g6> NOF".
 * Summary to stderr.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint32_t mask;
static int n;
static mask adj[32];
static inline int pc(mask x) { return __builtin_popcount(x); }

/* ---------- max flow on <= 34 nodes, capacity matrix ---------- */
#define MAXV 36
static int cap[MAXV][MAXV], flw[MAXV][MAXV];
static int maxflow(int N, int s, int t, int limit) {
    memset(flw, 0, sizeof flw);
    int total = 0;
    int prev[MAXV], q[MAXV];
    while (total < limit) {
        for (int i = 0; i < N; i++) prev[i] = -1;
        prev[s] = s;
        int h = 0, tl = 0;
        q[tl++] = s;
        while (h < tl && prev[t] < 0) {
            int u = q[h++];
            for (int v = 0; v < N; v++)
                if (prev[v] < 0 && cap[u][v] - flw[u][v] > 0) { prev[v] = u; q[tl++] = v; }
        }
        if (prev[t] < 0) break;
        int b = 1 << 30;
        for (int v = t; v != s; v = prev[v]) { int u = prev[v]; int r = cap[u][v] - flw[u][v]; if (r < b) b = r; }
        for (int v = t; v != s; v = prev[v]) { int u = prev[v]; flw[u][v] += b; flw[v][u] -= b; }
        total += b;
    }
    return total;
}
/* reachable set from s in residual graph (minimal min-cut source side) */
static mask reach_from(int N, int s) {
    int seen[MAXV] = {0}, q[MAXV], h = 0, tl = 0;
    seen[s] = 1; q[tl++] = s;
    while (h < tl) {
        int u = q[h++];
        for (int v = 0; v < N; v++) if (!seen[v] && cap[u][v] - flw[u][v] > 0) { seen[v] = 1; q[tl++] = v; }
    }
    mask m = 0;
    for (int v = 0; v < n; v++) if (seen[v]) m |= 1u << v;
    return m;
}

/* min over S with 2<=|S|<=n-1 of g(S); returns 1 if some such S has g(S) <= 8 */
static int not_sparse(mask *witness) {
    int deg[32];
    for (int v = 0; v < n; v++) { deg[v] = pc(adj[v]); if (deg[v] > 6) return -1; }
    int z = n, src = n + 1, N = n + 2;
    int gV = 0;
    for (int a = 0; a < n; a++) gV += 6 - deg[a];
    mask full = (1u << n) - 1;
    for (int u = 0; u < n; u++)
        for (mask t = adj[u] & ~((2u << u) - 1); t; t &= t - 1) {
            int v = __builtin_ctz(t);
            /* fast path when g(V) >= 8: lambda = min over S containing u,v (S = V allowed);
               the minimal minimizer S* is proper iff a proper S with g(S) <= 8 exists through
               this edge (g is even, so S* = V means every proper S has g >= 10). */
            int xs = (gV >= 8) ? -1 : 0, xe = (gV >= 8) ? -1 : n - 1;
            for (int x = xs; x <= xe; x++) {
                if (x == u || x == v) continue;
                memset(cap, 0, sizeof cap);
                for (int a = 0; a < n; a++) {
                    for (mask r = adj[a]; r; r &= r - 1) cap[a][__builtin_ctz(r)] = 1;
                    cap[a][z] = 6 - deg[a];
                }
                cap[src][u] = cap[src][v] = 1000;
                if (x >= 0) cap[x][z] = 1000;
                int lam = maxflow(N, src, z, 9);
                if (lam <= 8) {
                    mask r = reach_from(N, src);
                    if (r != full) { if (witness) *witness = r; return 1; }
                }
            }
        }
    return 0;
}

/* ---------- Hamilton cycles (from pairc.c) ---------- */
static mask res[32], S;
static int s0, ssize;
static long steps, step_limit = 0; /* 0 = unlimited */
static int aborted;
static int path2w[32];
static int ham2(int cur, mask visited, int depth) {
    if (step_limit && ++steps > step_limit) { aborted = 1; return 1; }
    path2w[depth - 1] = cur;
    if (depth == ssize) return (res[cur] >> s0) & 1;
    mask cand = res[cur] & S & ~visited;
    mask un = S & ~visited;
    mask ok = un | (1u << cur) | (1u << s0);
    for (mask t = un; t; t &= t - 1) { int v = __builtin_ctz(t); if (pc(res[v] & ok) < 2) return 0; }
    for (; cand; cand &= cand - 1) { int v = __builtin_ctz(cand); if (ham2(v, visited | (1u << v), depth + 1)) return 1; }
    return 0;
}
static mask A2[32];
static int path1[32];
static long hcount;
static int ham1(int cur, mask visited, int depth) {
    if (step_limit && ++steps > step_limit) { aborted = 1; return 1; }
    path1[depth - 1] = cur;
    if (depth == ssize) {
        if (!((A2[cur] >> s0) & 1)) return 0;
        if (path1[1] > cur) return 0;
        hcount++;
        for (mask t = S; t; t &= t - 1) { int v = __builtin_ctz(t); res[v] = A2[v] & S; }
        for (int i = 0; i < ssize; i++) { int a = path1[i], b = path1[(i + 1) % ssize]; res[a] &= ~(1u << b); res[b] &= ~(1u << a); }
        return ham2(s0, 1u << s0, 1);
    }
    /* prune: every unvisited vertex needs >= 2 neighbors among unvisited + cur + s0 */
    mask un = S & ~visited;
    mask ok = un | (1u << cur) | (1u << s0);
    for (mask t = un; t; t &= t - 1) { int v = __builtin_ctz(t); if (pc(A2[v] & ok) < 2) return 0; }
    mask cand = A2[cur] & S & ~visited;
    for (; cand; cand &= cand - 1) { int v = __builtin_ctz(cand); if (ham1(v, visited | (1u << v), depth + 1)) return 1; }
    return 0;
}
/* randomized first-cycle search: Warnsdorff order with random tie-breaks */
static unsigned long long rng_state = 88172645463325252ull;
static inline unsigned rnd(void) { rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17; return (unsigned)rng_state; }
static int ham1r(int cur, mask visited, int depth) {
    if (step_limit && ++steps > step_limit) { aborted = 1; return 0; }
    path1[depth - 1] = cur;
    if (depth == ssize) {
        if (!((A2[cur] >> s0) & 1)) return 0;
        hcount++;
        for (mask t = S; t; t &= t - 1) { int v = __builtin_ctz(t); res[v] = A2[v] & S; }
        for (int i = 0; i < ssize; i++) { int a = path1[i], b = path1[(i + 1) % ssize]; res[a] &= ~(1u << b); res[b] &= ~(1u << a); }
        long sv = steps; int r = ham2(s0, 1u << s0, 1); if (aborted) { aborted = 0; r = 0; } steps = sv; return r;
    }
    mask un = S & ~visited;
    mask ok = un | (1u << cur) | (1u << s0);
    for (mask t = un; t; t &= t - 1) { int v = __builtin_ctz(t); if (pc(A2[v] & ok) < 2) return 0; }
    int cand[32], key[32], k = 0;
    for (mask c = A2[cur] & S & ~visited; c; c &= c - 1) {
        int v = __builtin_ctz(c);
        cand[k] = v; key[k] = pc(A2[v] & un) * 64 + (rnd() & 63); k++;
    }
    for (int i = 1; i < k; i++) for (int j = i; j > 0 && key[j] < key[j - 1]; j--) {
        int t = key[j]; key[j] = key[j - 1]; key[j - 1] = t; t = cand[j]; cand[j] = cand[j - 1]; cand[j - 1] = t; }
    for (int i = 0; i < k; i++) if (ham1r(cand[i], visited | (1u << cand[i]), depth + 1)) return 1;
    return 0;
}
/* heuristic: returns 1 if a spanning pair was found within tries*budget steps, 0 = not found */
static int spanning_pair_rand(mask *A, mask T, int tries, long budget) {
    for (mask t = T; t; t &= t - 1) { int v = __builtin_ctz(t); A2[v] = A[v] & T; if (pc(A2[v]) < 4) return 0; }
    S = T; ssize = pc(T);
    long save = step_limit;
    for (int i = 0; i < tries; i++) {
        /* start at a random vertex of minimum degree */
        int best = 99, cnt = 0, pick = -1;
        for (mask t = T; t; t &= t - 1) { int v = __builtin_ctz(t); int d = pc(A2[v]); if (d < best) { best = d; cnt = 0; } if (d == best && (rnd() % (++cnt)) == 0) pick = v; }
        s0 = pick; steps = 0; aborted = 0; step_limit = budget;
        int r = ham1r(s0, 1u << s0, 1);
        if (r) { step_limit = save; return 1; }
    }
    step_limit = save;
    return 0;
}
/* spanning pair of the graph with adjacency A on vertex set T (min degree >= 4 needed) */
static int spanning_pair(mask *A, mask T) {
    for (mask t = T; t; t &= t - 1) { int v = __builtin_ctz(t); A2[v] = A[v] & T; if (pc(A2[v]) < 4) return 0; }
    S = T; ssize = pc(T); s0 = __builtin_ctz(T); hcount = 0; steps = 0; aborted = 0;
    int r = ham1(s0, 1u << s0, 1);
    return aborted ? -1 : r;
}

/* 4-factor of bipartite graph on vertex set T with sides (T & Umask), (T & ~Umask): flow */
static int four_factor(mask *A, mask T, mask Umask) {
    mask TU = T & Umask, TW = T & ~Umask;
    if (pc(TU) != pc(TW)) return 0;
    int src = n, snk = n + 1, N = n + 2;
    memset(cap, 0, sizeof cap);
    for (mask t = TW; t; t &= t - 1) {
        int w = __builtin_ctz(t);
        cap[src][w] = 4;
        for (mask r = A[w] & TU; r; r &= r - 1) cap[w][__builtin_ctz(r)] = 1;
    }
    for (mask t = TU; t; t &= t - 1) cap[__builtin_ctz(t)][snk] = 4;
    int need = 4 * pc(TW);
    return maxflow(N, src, snk, need) == need;
}

static int parse(char *line) {
    n = line[0] - 63;
    if (n < 1 || n > 30) return 0;
    memset(adj, 0, sizeof adj);
    int bit = 0, pos = 1;
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++) {
            int ch = line[pos] - 63;
            if ((ch >> (5 - bit)) & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
            if (++bit == 6) { bit = 0; pos++; }
        }
    return 1;
}

int main(int argc, char **argv) {
    char mode = argc > 1 ? argv[1][0] : 's';
    int n1 = argc > 2 ? atoi(argv[2]) : 0;
    if (argc > 3) step_limit = atol(argv[3]);
    setvbuf(stdout, NULL, _IOLBF, 0);
    static char line[4096];
    long total = 0, hits = 0, aux1 = 0, aux2 = 0;
    while (fgets(line, sizeof line, stdin)) {
        if (line[0] == '>' || line[0] == '\n') continue;
        size_t L = strlen(line);
        while (L && (line[L - 1] == '\n' || line[L - 1] == '\r')) line[--L] = 0;
        if (!parse(line)) { fprintf(stderr, "bad n\n"); return 2; }
        total++;
        mask full = (1u << n) - 1;
        if (mode == 's' || mode == 'S') {
            mask w = 0;
            int ns = not_sparse(&w);
            if (ns < 0) { fprintf(stderr, "Delta > 6\n"); return 2; }
            if (!ns) hits++;
            if ((mode == 's' && !ns) || (mode == 'S' && ns)) puts(line);
        } else if (mode == 'w') {
            int r = spanning_pair(adj, full);
            hits += (r == 1);
            if (r == 1) {
                printf("%s SP C1=", line);
                for (int i = 0; i < ssize; i++) printf("%d%s", path1[i], i + 1 < ssize ? "," : "");
                printf(" C2=");
                for (int i = 0; i < ssize; i++) printf("%d%s", path2w[i], i + 1 < ssize ? "," : "");
                printf("\n");
            } else printf("%s %s\n", line, r == 0 ? "NOSP" : "UNKNOWN");
        } else if (mode == 'h' || mode == 'H') {
            int r = spanning_pair(adj, full);
            if (r < 0) r = spanning_pair_rand(adj, full, 200, 2000000) ? 1 : -1;
            if (r < 0) { aux2++; printf("%s UNKNOWN\n", line); continue; }
            hits += r;
            if (mode == 'h') printf("%s %s %ld\n", line, r ? "SP" : "NOSP", hcount);
            else if (!r) puts(line);
        } else if (mode == 'y') {
            mask Umask = (1u << n1) - 1;
            int ports = 0, good = 0, sp = 0;
            char buf[1024]; buf[0] = 0;
            for (int y = n1; y < n; y++) {
                if (pc(adj[y]) > 5) continue;
                ports++;
                mask T = full & ~(1u << y);
                int F = four_factor(adj, T, Umask);
                int H = F ? spanning_pair(adj, T) : 0;
                if (H < 0) H = spanning_pair_rand(adj, T, 200, 2000000) ? 1 : 2;
                good += F; sp += (H == 1);
                char tmp[32]; snprintf(tmp, sizeof tmp, "%s%d:%d:%d", buf[0] ? "," : "", y, F, H);
                strncat(buf, tmp, sizeof buf - strlen(buf) - 1);
            }
            if (sp) hits++;
            if (good) aux1++;
            printf("%s ports=%d good=%d sp=%d list=%s\n", line, ports, good, sp, buf);
        } else if (mode == 'f') {
            mask Umask = (1u << n1) - 1;
            int r = four_factor(adj, full, Umask);
            hits += r;
            printf("%s %s\n", line, r ? "F" : "NOF");
        }
    }
    fprintf(stderr, "mode=%c graphs=%ld hits=%ld aux1=%ld aux2=%ld\n", mode, total, hits, aux1, aux2);
    return 0;
}
