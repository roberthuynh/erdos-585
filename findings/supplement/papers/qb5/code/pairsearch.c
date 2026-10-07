/* pairsearch.c (lane qb5, round 2): random sparse E5 block pairs and the E5 pair statement.
 *
 * Build: /usr/bin/clang -O3 -o pairsearch pairsearch.c
 * Usage: pairsearch NC NB COUNT SEED NUMODE TWIN
 *   X = A u C with |C| = NC (every C-vertex has 6 neighbours in A), |A| = NC + 2;
 *   Y = B u D with |B| = NB, |D| = NB + 2;  7 cut edges between A and D.
 *   NUMODE 1: keep only cuts with matching number <= 3 (as in a minimal counterexample), 0: any cut.
 *   TWIN in [0,100]: percent chance that a small-side vertex copies the neighbourhood of an earlier one
 *   (creates large demand groups).
 * Every instance is checked: bipartite, Delta <= 6, delta >= 4, e = 3n - 5, sparse (every S with
 * 3 <= |S| <= n-1 spans at most 3|S| - 6 edges; Gray-code enumeration of all 2^n subsets).
 * G has no 4-factor by construction (e(A, D) = 7 < 4(|A| - |C|)); this is re-checked by max flow.
 * For every pair p in P, q in Q it decides by max flow whether G - p - q has a 4-factor.
 * Output (stdout): graph6 of every sparse instance with at most 2 good pairs, with the count.
 * Stats (stderr): instances tried, sparse, histogram of the number of good pairs.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef uint32_t u32;
static int n;
static u32 adj[32];
static uint64_t rs;
static unsigned rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }

/* ---------- max flow for a 4-factor of G[keep] (sides by col) ---------- */
static int cap[34][34];
static int maxflow4(u32 keep, const int *col, int *need){
    /* nodes 0..n-1 vertices, n = source, n+1 = sink */
    int N = n + 2, s = n, t = n + 1;
    memset(cap, 0, sizeof cap);
    int np = 0, nq = 0;
    for (int v = 0; v < n; v++) if (keep >> v & 1) {
        if (col[v] == 0) { np++; cap[s][v] = 4; for (int u = 0; u < n; u++) if ((keep >> u & 1) && (adj[v] >> u & 1)) cap[v][u] = 1; }
        else { nq++; cap[v][t] = 4; }
    }
    *need = 4 * np;
    if (np != nq) return -1;
    int flow = 0, prev[34], q[34];
    for (;;) {
        for (int i = 0; i < N; i++) prev[i] = -1;
        int h = 0, tl = 0; q[tl++] = s; prev[s] = s;
        while (h < tl && prev[t] < 0) { int v = q[h++]; for (int u = 0; u < N; u++) if (cap[v][u] > 0 && prev[u] < 0) { prev[u] = v; q[tl++] = u; } }
        if (prev[t] < 0) break;
        int f = 1000; for (int v = t; v != s; v = prev[v]) if (cap[prev[v]][v] < f) f = cap[prev[v]][v];
        for (int v = t; v != s; v = prev[v]) { cap[prev[v]][v] -= f; cap[v][prev[v]] += f; }
        flow += f;
    }
    return flow;
}

/* ---------- sparsity by Gray code ---------- */
static int sparse_all(void){
    u32 S = 0; int e = 0, sz = 0; u32 full = (n == 32) ? 0xffffffffu : ((1u << n) - 1);
    uint64_t lim = 1ull << n;
    for (uint64_t i = 1; i < lim; i++) {
        int v = __builtin_ctzll(i);
        u32 b = 1u << v;
        if (S & b) { S ^= b; sz--; e -= __builtin_popcount(adj[v] & S); }
        else { e += __builtin_popcount(adj[v] & S); S ^= b; sz++; }
        if (sz >= 3 && S != full && e > 3 * sz - 6) return 0;
    }
    return 1;
}
static int sparse_sub(u32 W){ /* all S subset of W, |S| >= 3 (W != V assumed) */
    int idx[32], k = 0; for (int v = 0; v < n; v++) if (W >> v & 1) idx[k++] = v;
    u32 S = 0; int e = 0, sz = 0;
    for (uint64_t i = 1; i < (1ull << k); i++) {
        int v = idx[__builtin_ctzll(i)]; u32 b = 1u << v;
        if (S & b) { S ^= b; sz--; e -= __builtin_popcount(adj[v] & S); }
        else { e += __builtin_popcount(adj[v] & S); S ^= b; sz++; }
        if (sz >= 3 && e > 3 * sz - 6) return 0;
    }
    return 1;
}

static void g6(void){
    char out[200]; int k = 0; out[k++] = (char)(n + 63);
    int bits = 0, val = 0;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
        val = (val << 1) | ((adj[i] >> j) & 1); bits++;
        if (bits == 6) { out[k++] = (char)(val + 63); bits = 0; val = 0; }
    }
    if (bits) { val <<= (6 - bits); out[k++] = (char)(val + 63); }
    out[k] = 0; printf("%s", out);
}

static int nu_cut(int (*cut)[2], int m){ /* maximum matching of the cut edges */
    int best = 0;
    for (int mask = 0; mask < (1 << m); mask++) {
        int c = __builtin_popcount(mask); if (c <= best) continue;
        u32 used = 0; int ok = 1;
        for (int i = 0; i < m && ok; i++) if (mask >> i & 1) {
            u32 b = (1u << cut[i][0]) | (1u << cut[i][1]);
            if (used & b) ok = 0; used |= b;
        }
        if (ok) best = c;
    }
    return best;
}

/* build a block: small side S (ns vertices, ids s0..), big side L (ns+2, ids l0..), each small vertex
   has 6 neighbours in L; returns 0 on failure; requires in-block degree of L in [3,6] */
static int block(int s0, int ns, int l0, int twin){
    int nl = ns + 2, dl[16]; memset(dl, 0, sizeof dl);
    int nb[16][6];
    for (int i = 0; i < ns; i++) {
        int tries = 0, ok = 0;
        while (!ok && tries++ < 200) {
            int pick[6];
            if (i > 0 && (int)(rnd() % 100) < twin) { int j = rnd() % i; memcpy(pick, nb[j], sizeof pick); }
            else {
                int perm[16]; for (int k = 0; k < nl; k++) perm[k] = k;
                for (int k = nl - 1; k > 0; k--) { int r = rnd() % (k + 1); int t = perm[k]; perm[k] = perm[r]; perm[r] = t; }
                memcpy(pick, perm, sizeof pick);
            }
            ok = 1; for (int k = 0; k < 6; k++) if (dl[pick[k]] >= 6) ok = 0;
            if (ok) { for (int k = 0; k < 6; k++) { dl[pick[k]]++; nb[i][k] = pick[k]; int a = l0 + pick[k], c = s0 + i; adj[a] |= 1u << c; adj[c] |= 1u << a; } }
        }
        if (!ok) return 0;
    }
    for (int k = 0; k < nl; k++) if (dl[k] < 3) return 0;
    return 1;
}

int main(int argc, char **argv){
    if (argc < 7) { fprintf(stderr, "usage: pairsearch NC NB COUNT SEED NUMODE TWIN\n"); return 1; }
    int nc = atoi(argv[1]), nb = atoi(argv[2]); long count = atol(argv[3]); rs = 0x9e3779b97f4a7c15ull ^ (uint64_t)atoll(argv[4]) * 2654435761ull;
    int numode = atoi(argv[5]), twin = atoi(argv[6]);
    int na = nc + 2, nd = nb + 2;
    n = nc + na + nb + nd;
    if (n > 26) { fprintf(stderr, "n too large\n"); return 1; }
    int C0 = 0, A0 = nc, B0 = nc + na, D0 = nc + na + nb;
    int col[32]; for (int v = 0; v < n; v++) col[v] = (v >= A0 && v < B0) || (v >= B0 && v < D0) ? 0 : 1; /* P = A u B */
    long tried = 0, built = 0, sparse = 0, hist[200]; memset(hist, 0, sizeof hist);
    long minGood = 1000000;
    while (sparse < count && tried < count * 20000L) {
        tried++;
        memset(adj, 0, sizeof adj);
        if (!block(C0, nc, A0, twin)) continue;
        if (!block(B0, nb, D0, twin)) continue;
        /* cut: 7 edges A-D, respecting degree <= 6 and final degree >= 4 */
        int cut[7][2], m = 0, att = 0;
        while (m < 7 && att++ < 400) {
            int a = A0 + rnd() % na, d = D0 + rnd() % nd;
            if (adj[a] >> d & 1) continue;
            if (__builtin_popcount(adj[a]) >= 6 || __builtin_popcount(adj[d]) >= 6) continue;
            adj[a] |= 1u << d; adj[d] |= 1u << a; cut[m][0] = a; cut[m][1] = d; m++;
        }
        if (m < 7) continue;
        int ok = 1; for (int v = 0; v < n; v++) if (__builtin_popcount(adj[v]) < 4) ok = 0;
        if (!ok) continue;
        if (numode == 1 && nu_cut(cut, 7) > 3) continue;
        built++;
        u32 Xm = 0, Ym = 0; for (int v = 0; v < n; v++) { if (v < B0) Xm |= 1u << v; else Ym |= 1u << v; }
        if (!sparse_sub(Xm) || !sparse_sub(Ym)) continue;
        if (!sparse_all()) continue;
        sparse++;
        int need; u32 full = (1u << n) - 1;
        int f = maxflow4(full, col, &need);
        if (f == need) { fprintf(stderr, "unexpected 4-factor\n"); continue; }
        int good = 0, goodOut = 0;
        for (int p = 0; p < n; p++) if (col[p] == 0) for (int q = 0; q < n; q++) if (col[q] == 1) {
            u32 keep = full & ~(1u << p) & ~(1u << q);
            int fl = maxflow4(keep, col, &need);
            if (fl == need) { good++; if (!((p >= A0 && p < B0) && (q >= D0))) goodOut++; }
        }
        if (good < 200) hist[good]++;
        if (good < minGood) minGood = good;
        if (goodOut) { fprintf(stderr, "WARNING good pair outside A x D\n"); }
        if (good <= 2) { g6(); printf(" good=%d\n", good); fflush(stdout); }
    }
    fprintf(stderr, "NC=%d NB=%d n=%d numode=%d twin=%d tried=%ld built=%ld sparse=%ld minGood=%ld\n", nc, nb, n, numode, twin, tried, built, sparse, minGood);
    fprintf(stderr, "hist:"); for (int i = 0; i < 200; i++) if (hist[i]) fprintf(stderr, " %d:%ld", i, hist[i]); fprintf(stderr, "\n");
    return 0;
}
