/* hdq.c -- wave4/h22b: second, independent checker for H22 (connected bipartite 4-regular graphs).
 * Written for this lane; it shares no code with pairs/ptool.c, pairs/cuts.c or review/code/hd.c,
 * and its HD search is a different algorithm (edge 2-colouring search, not Hamilton-cycle enumeration).
 *
 * Input: graph6 lines on stdin, n <= 32. For every graph:
 *   1. parse; check 4-regular, connected, and (unless -g) bipartite with two equal sides;
 *   2. 2-edge-cut filter: for each edge e, a bridge f of G - e gives the cut {e, f}
 *      (DFS lowpoints); -B also runs a brute-force check over all pairs of edges and compares;
 *   3. colour-swap test (unless -g or -S): is there an automorphism exchanging the two sides?
 *      (individualization-refinement isomorphism search from (G, A|B) to (G, B|A));
 *   4. HD decider: depth-first search over 2-colourings of the edges, 2 red and 2 blue at each
 *      vertex, tracking the ends of the monochromatic paths so that no cycle of either colour
 *      closes before it has n edges, with forcing (a vertex with 2 edges of one colour gets the
 *      other colour on the rest; an edge joining the two ends of a short path gets the other colour)
 *      and a prune (the red-available and blue-available graphs must be connected and bridgeless).
 *      A decomposition found is re-checked by verify(), which shares nothing with the search.
 *      Since a Hamilton cycle crosses every edge cut at least twice, an HD graph has no 2-edge cut,
 *      so the decider is run on graphs with a 2-edge cut only as a test (-d; default on).
 *
 * Output, one line per graph:
 *   <g6> H <hexmask> <sw>                 HD; red edges = bits of mask over edge ids (graph6 bit order)
 *   <g6> C <a>-<b>,<c>-<d> <sw> <dec>     2-edge cut {ab, cd}; dec = N (decider: no HD), L (node limit),
 *                                         - (decider not run), H (decider found HD: inconsistency)
 *   <g6> X <sw> <dec>                     exception: no 2-edge cut and decider N or L
 *   <g6> E <reason>                       input error
 * <sw> is 1 if some automorphism swaps the sides, 0 if none, - if not computed.
 * Summary on stderr.
 *
 * Edge ids: graph6 bit order, i.e. for j = 1..n-1, for i = 0..j-1, the k-th present pair is edge k.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 32
#define MAXM 64

static int n, m;
static int eu[MAXM], ev[MAXM];
static int inc[MAXN][4], dg[MAXN];
static int eid[MAXN][MAXN];
static uint32_t adjm[MAXN];
static int side[MAXN];

/* ---------------- parsing and basic checks ---------------- */

/* returns 0 ok, else an error string index */
static const char *parse_g6(const char *s) {
    if (!s[0]) return "empty";
    int c = (unsigned char)s[0];
    if (c < 63 || c > 126) return "badchar";
    if (c == 126) return "n>62";
    n = c - 63;
    if (n > MAXN || n < 1) return "n";
    int need = n * (n - 1) / 2;
    int nbytes = (need + 5) / 6;
    if ((int)strlen(s) != 1 + nbytes) return "length";
    for (int i = 0; i < n; i++) { dg[i] = 0; adjm[i] = 0; for (int j = 0; j < n; j++) eid[i][j] = -1; }
    m = 0;
    int k = 0;
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++, k++) {
            int byte = (unsigned char)s[1 + k / 6] - 63;
            if (byte < 0 || byte > 63) return "badchar";
            if ((byte >> (5 - k % 6)) & 1) {
                if (m >= MAXM) return "m";
                if (dg[i] >= 4 || dg[j] >= 4) return "deg>4";
                eu[m] = i; ev[m] = j; eid[i][j] = eid[j][i] = m;
                inc[i][dg[i]++] = m; inc[j][dg[j]++] = m;
                adjm[i] |= 1u << j; adjm[j] |= 1u << i;
                m++;
            }
        }
    for (int i = 0; i < n; i++) if (dg[i] != 4) return "notreg4";
    return 0;
}

static int connected_all(void) {
    uint32_t seen = 1, fr = 1;
    while (fr) {
        uint32_t nx = 0;
        for (uint32_t t = fr; t; t &= t - 1) nx |= adjm[__builtin_ctz(t)];
        nx &= ~seen; seen |= nx; fr = nx;
    }
    return seen == (n == 32 ? 0xffffffffu : ((1u << n) - 1));
}

/* BFS 2-colouring; returns 1 if bipartite with |A| = |B| */
static int bipartite_equal(void) {
    int q[MAXN], h = 0, t = 0, cntA = 0;
    for (int i = 0; i < n; i++) side[i] = -1;
    side[0] = 0; q[t++] = 0;
    while (h < t) {
        int v = q[h++];
        for (int k = 0; k < 4; k++) {
            int e = inc[v][k], w = eu[e] ^ ev[e] ^ v;
            if (side[w] < 0) { side[w] = 1 - side[v]; q[t++] = w; }
            else if (side[w] == side[v]) return 0;
        }
    }
    for (int i = 0; i < n; i++) { if (side[i] < 0) return 0; if (side[i] == 0) cntA++; }
    return 2 * cntA == n;
}

/* ---------------- 2-edge-cut filter ---------------- */

static int tin[MAXN], low[MAXN], timer_, brf;
static void dfs_bridge(int v, int pe, int skip) {
    tin[v] = low[v] = ++timer_;
    for (int k = 0; k < 4; k++) {
        int e = inc[v][k];
        if (e == skip || e == pe) continue;
        int w = eu[e] ^ ev[e] ^ v;
        if (tin[w]) { if (tin[w] < low[v]) low[v] = tin[w]; }
        else {
            dfs_bridge(w, e, skip);
            if (low[w] < low[v]) low[v] = low[w];
            if (low[w] > tin[v] && brf < 0) brf = e;
        }
    }
}
/* returns 1 and the cut {*e1, *e2} if G has an edge cut of size <= 2 (e2 = -1 for a bridge) */
static int find_2cut(int *e1, int *e2) {
    for (int skip = -1; skip < m; skip++) {
        memset(tin, 0, sizeof tin); timer_ = 0; brf = -1;
        dfs_bridge(0, -1, skip);
        if (timer_ < n) { *e1 = skip; *e2 = -1; return 1; } /* G - skip disconnected */
        if (brf >= 0) { *e1 = brf; *e2 = skip; if (skip < 0) { *e1 = brf; *e2 = -1; } return 1; }
    }
    return 0;
}
/* brute force: any set of <= 2 edges whose removal disconnects G */
static int conn_without(int a, int b) {
    uint32_t A[MAXN];
    memcpy(A, adjm, sizeof(uint32_t) * n);
    if (a >= 0) { A[eu[a]] &= ~(1u << ev[a]); A[ev[a]] &= ~(1u << eu[a]); }
    if (b >= 0) { A[eu[b]] &= ~(1u << ev[b]); A[ev[b]] &= ~(1u << eu[b]); }
    uint32_t seen = 1, fr = 1;
    while (fr) {
        uint32_t nx = 0;
        for (uint32_t t = fr; t; t &= t - 1) nx |= A[__builtin_ctz(t)];
        nx &= ~seen; seen |= nx; fr = nx;
    }
    return seen == (n == 32 ? 0xffffffffu : ((1u << n) - 1));
}
static int brute_2cut(void) {
    for (int a = -1; a < m; a++)
        for (int b = a + 1; b < m; b++)
            if (!conn_without(a, b)) return 1;
    return 0;
}

/* ---------------- colour-swap test ---------------- */

typedef struct { int key[5]; int who; } Sig;
static int cmp_sig(const void *x, const void *y) {
    const Sig *a = x, *b = y;
    for (int i = 0; i < 5; i++) if (a->key[i] != b->key[i]) return a->key[i] < b->key[i] ? -1 : 1;
    return 0;
}
static int ndistinct(const int *c) {
    int seen[2 * MAXN + 2] = {0}, k = 0;
    for (int v = 0; v < n; v++) if (!seen[c[v]]) { seen[c[v]] = 1; k++; }
    return k;
}
static void sort4(int *a) {
    for (int i = 1; i < 4; i++) for (int j = i; j > 0 && a[j] < a[j - 1]; j--) { int t = a[j]; a[j] = a[j - 1]; a[j - 1] = t; }
}
/* joint colour refinement of two colourings of G; returns the number of colours, or -1 if the
   colour histograms differ (no colour-preserving isomorphism between the two coloured graphs) */
static int refine(int *c1, int *c2) {
    int prev = ndistinct(c1);
    for (;;) {
        Sig s[2 * MAXN];
        for (int g = 0; g < 2; g++) {
            int *c = g ? c2 : c1;
            for (int v = 0; v < n; v++) {
                Sig *x = &s[g * n + v];
                x->key[0] = c[v];
                for (int k = 0; k < 4; k++) { int e = inc[v][k]; x->key[1 + k] = c[eu[e] ^ ev[e] ^ v]; }
                sort4(x->key + 1);
                x->who = g * n + v;
            }
        }
        qsort(s, 2 * n, sizeof(Sig), cmp_sig);
        int nc[2 * MAXN], r = -1;
        for (int i = 0; i < 2 * n; i++) {
            if (i == 0 || cmp_sig(&s[i], &s[i - 1])) r++;
            nc[s[i].who] = r;
        }
        int h[2 * MAXN] = {0};
        for (int v = 0; v < n; v++) { h[nc[v]]++; h[nc[n + v]]--; }
        for (int i = 0; i <= r; i++) if (h[i]) return -1;
        for (int v = 0; v < n; v++) { c1[v] = nc[v]; c2[v] = nc[n + v]; }
        int now = r + 1;
        if (now == prev) return now;
        prev = now;
    }
}
static long iso_nodes;
static int iso_search(const int *c1, const int *c2, int ncol) {
    iso_nodes++;
    int size[2 * MAXN + 2] = {0};
    for (int v = 0; v < n; v++) size[c1[v]]++;
    int best = -1;
    for (int c = 0; c < ncol; c++) if (size[c] > 1 && (best < 0 || size[c] < size[best])) best = c;
    if (best < 0) {
        int pos2[2 * MAXN + 2], map[MAXN];
        for (int w = 0; w < n; w++) pos2[c2[w]] = w;
        for (int v = 0; v < n; v++) map[v] = pos2[c1[v]];
        for (int e = 0; e < m; e++) if (!((adjm[map[eu[e]]] >> map[ev[e]]) & 1)) return 0;
        return 1;
    }
    int v = 0;
    while (c1[v] != best) v++;
    for (int w = 0; w < n; w++) {
        if (c2[w] != best) continue;
        int d1[MAXN], d2[MAXN];
        memcpy(d1, c1, sizeof(int) * n); memcpy(d2, c2, sizeof(int) * n);
        d1[v] = ncol; d2[w] = ncol;
        int k = refine(d1, d2);
        if (k < 0) continue;
        if (iso_search(d1, d2, k)) return 1;
    }
    return 0;
}
/* 1 if some automorphism of G maps side 0 onto side 1 */
static int swap_aut(void) {
    int c1[MAXN], c2[MAXN];
    for (int v = 0; v < n; v++) { c1[v] = side[v]; c2[v] = 1 - side[v]; }
    int k = refine(c1, c2);
    if (k < 0) return 0;
    return iso_search(c1, c2, k);
}

/* ---------------- HD decider ---------------- */

typedef struct {
    signed char col[MAXM];          /* -1 unset, 0 red, 1 blue */
    unsigned char deg[2][MAXN];     /* edges of each colour at v */
    unsigned char oth[2][MAXN];     /* other end of the colour-c path ending at v (valid if deg < 2) */
    int cnt[2], ncol;
} St;

static long nodes, node_limit = 20000000L;
static St found;

static int setcol(St *s, int e0, int c0) {
    enum { QMAX = 8 * MAXM };
    int qe[QMAX], qc[QMAX], qh = 0, qt = 0;
    qe[qt] = e0; qc[qt] = c0; qt++;
    while (qh < qt) {
        int e = qe[qh], c = qc[qh]; qh++;
        if (s->col[e] >= 0) { if (s->col[e] != c) return 0; continue; }
        int u = eu[e], v = ev[e];
        if (s->deg[c][u] >= 2 || s->deg[c][v] >= 2) return 0;
        int a = s->oth[c][u], b = s->oth[c][v];
        int closing = (a == v);
        if (closing && s->cnt[c] != n - 1) return 0;
        s->col[e] = (signed char)c;
        s->deg[c][u]++; s->deg[c][v]++; s->cnt[c]++; s->ncol++;
        if (!closing) { s->oth[c][a] = (unsigned char)b; s->oth[c][b] = (unsigned char)a; }
        int xs[2] = {u, v};
        for (int i = 0; i < 2; i++) {
            int x = xs[i];
            if (s->deg[c][x] == 2)
                for (int k = 0; k < 4; k++) { int f = inc[x][k]; if (s->col[f] < 0) { if (qt >= QMAX) { fprintf(stderr, "queue overflow\n"); exit(4); } qe[qt] = f; qc[qt] = 1 - c; qt++; } }
        }
        if (!closing) {
            int f = eid[a][b];
            if (s->cnt[c] < n - 1) {
                if (f >= 0 && s->col[f] < 0) { if (qt >= QMAX) { fprintf(stderr, "queue overflow\n"); exit(4); } qe[qt] = f; qc[qt] = 1 - c; qt++; }
            } else { /* spanning path: its closing edge must be colour c */
                if (f < 0 || s->col[f] == 1 - c) return 0;
                if (s->col[f] < 0) { if (qt >= QMAX) { fprintf(stderr, "queue overflow\n"); exit(4); } qe[qt] = f; qc[qt] = c; qt++; }
            }
        }
    }
    return 1;
}

/* the graph of edges coloured c or uncoloured must be connected and bridgeless */
static const St *av_s; static int av_c;
static void dfs_av(int v, int pe) {
    tin[v] = low[v] = ++timer_;
    for (int k = 0; k < 4; k++) {
        int e = inc[v][k];
        if (e == pe) continue;
        if (av_s->col[e] >= 0 && av_s->col[e] != av_c) continue;
        int w = eu[e] ^ ev[e] ^ v;
        if (tin[w]) { if (tin[w] < low[v]) low[v] = tin[w]; }
        else {
            dfs_av(w, e);
            if (low[w] < low[v]) low[v] = low[w];
            if (low[w] > tin[v]) brf = e;
        }
    }
}
static int avail_ok(const St *s, int c) {
    av_s = s; av_c = c;
    memset(tin, 0, sizeof tin); timer_ = 0; brf = -1;
    dfs_av(0, -1);
    return timer_ == n && brf < 0;
}

static int pick_edge(const St *s) {
    int bv = -1, bu = 9;
    for (int v = 0; v < n; v++) {
        int u = 4 - s->deg[0][v] - s->deg[1][v];
        if (u > 0 && u < bu) { bu = u; bv = v; }
    }
    if (bv < 0) return -1;
    for (int k = 0; k < 4; k++) if (s->col[inc[bv][k]] < 0) return inc[bv][k];
    return -1;
}

static int search(const St *s, int root) {
    if (node_limit && ++nodes > node_limit) return -1;
    if (s->ncol == m) { found = *s; return 1; }
    if (!avail_ok(s, 0) || !avail_ok(s, 1)) return 0;
    int e = pick_edge(s);
    if (e < 0) return 0;
    for (int c = 0; c < 2; c++) {
        if (root && c == 1) break; /* red/blue symmetry: the first edge may be taken red */
        St t = *s;
        if (!setcol(&t, e, c)) continue;
        int r = search(&t, 0);
        if (r) return r;
    }
    return 0;
}

/* returns 1 (HD, mask of red edges in *mask), 0 (not HD), -1 (node limit) */
static int decide_hd(uint64_t *mask) {
    St s;
    memset(&s, 0, sizeof s);
    for (int e = 0; e < m; e++) s.col[e] = -1;
    for (int v = 0; v < n; v++) { s.oth[0][v] = s.oth[1][v] = (unsigned char)v; }
    nodes = 0;
    int r = search(&s, 1);
    if (r == 1) {
        *mask = 0;
        for (int e = 0; e < m; e++) if (found.col[e] == 0) *mask |= 1ull << e;
    }
    return r;
}

/* independent check of a decomposition: red = edges in mask, blue = the rest;
   each colour must be 2-regular and connected on all n vertices */
static int verify(uint64_t mask) {
    if (m != 2 * n) return 0;
    for (int col = 0; col < 2; col++) {
        uint32_t A[MAXN];
        for (int v = 0; v < n; v++) A[v] = 0;
        for (int e = 0; e < m; e++) {
            int isred = (int)((mask >> e) & 1);
            if ((col == 0) == (isred == 1)) { A[eu[e]] |= 1u << ev[e]; A[ev[e]] |= 1u << eu[e]; }
        }
        for (int v = 0; v < n; v++) if (__builtin_popcount(A[v]) != 2) return 0;
        uint32_t seen = 1, fr = 1;
        while (fr) {
            uint32_t nx = 0;
            for (uint32_t t = fr; t; t &= t - 1) nx |= A[__builtin_ctz(t)];
            nx &= ~seen; seen |= nx; fr = nx;
        }
        if (seen != (n == 32 ? 0xffffffffu : ((1u << n) - 1))) return 0;
    }
    return 1;
}

int main(int argc, char **argv) {
    int general = 0, brute = 0, noswap = 0, dec_on_cut = 1;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-g")) general = 1;          /* any 4-regular graph: skip bipartite and swap */
        else if (!strcmp(argv[i], "-B")) brute = 1;       /* also brute-force the 2-cut test */
        else if (!strcmp(argv[i], "-S")) noswap = 1;      /* skip the swap test */
        else if (!strcmp(argv[i], "-D")) dec_on_cut = 0;  /* do not run the decider on 2-cut graphs */
        else if (!strncmp(argv[i], "-n", 2)) node_limit = atol(argv[i] + 2);
        else { fprintf(stderr, "usage: hdq [-g] [-B] [-S] [-D] [-n#] < g6\n"); return 2; }
    }
    setvbuf(stdout, NULL, _IOFBF, 1 << 16);
    static char line[4096];
    long tot = 0, cH = 0, cC = 0, cX = 0, cE = 0, sw = 0, swC = 0, cutN = 0, cutL = 0, cutH = 0, cutSkip = 0;
    long bruteMismatch = 0, verifyFail = 0, nodesH = 0, maxNodesH = 0, nodesC = 0, maxNodesC = 0;
    while (fgets(line, sizeof line, stdin)) {
        size_t L = strlen(line);
        while (L && (line[L - 1] == '\n' || line[L - 1] == '\r')) line[--L] = 0;
        if (!L || line[0] == '>') continue;
        tot++;
        const char *err = parse_g6(line);
        if (!err && !connected_all()) err = "disconnected";
        if (!err && m != 2 * n) err = "m!=2n";
        if (!err && !general && !bipartite_equal()) err = "notbipartite_equal";
        if (err) { printf("%s E %s\n", line, err); cE++; continue; }
        int e1 = -1, e2 = -1;
        int cut = find_2cut(&e1, &e2);
        if (brute) {
            int bc = brute_2cut();
            if (bc != cut) { bruteMismatch++; printf("%s E brute_mismatch\n", line); cE++; continue; }
        }
        int s = -1;
        if (!general && !noswap) { iso_nodes = 0; s = swap_aut(); sw += s; }
        char sws = s < 0 ? '-' : (char)('0' + s);
        uint64_t mask = 0;
        if (cut) {
            cC++; if (s == 1) swC++;
            char dec = '-';
            if (dec_on_cut) {
                int r = decide_hd(&mask);
                nodesC += nodes; if (nodes > maxNodesC) maxNodesC = nodes;
                if (r == 1) { dec = 'H'; cutH++; } else if (r == 0) { dec = 'N'; cutN++; } else { dec = 'L'; cutL++; }
            } else cutSkip++;
            if (e2 >= 0) printf("%s C %d-%d,%d-%d %c %c\n", line, eu[e1], ev[e1], eu[e2], ev[e2], sws, dec);
            else printf("%s C %d-%d %c %c\n", line, eu[e1], ev[e1], sws, dec);
            continue;
        }
        int r = decide_hd(&mask);
        nodesH += nodes; if (nodes > maxNodesH) maxNodesH = nodes;
        if (r == 1) {
            if (!verify(mask)) { verifyFail++; printf("%s E verify_failed %llx\n", line, (unsigned long long)mask); cE++; continue; }
            cH++;
            printf("%s H %llx %c\n", line, (unsigned long long)mask, sws);
        } else {
            cX++;
            printf("%s X %c %c\n", line, sws, r == 0 ? 'N' : 'L');
        }
    }
    fflush(stdout);
    fprintf(stderr, "hdq graphs=%ld H=%ld C=%ld X=%ld E=%ld swap=%ld swapC=%ld cutN=%ld cutL=%ld cutH=%ld cutSkip=%ld "
                    "bruteMismatch=%ld verifyFail=%ld nodesH=%ld maxNodesH=%ld nodesC=%ld maxNodesC=%ld\n",
            tot, cH, cC, cX, cE, sw, swC, cutN, cutL, cutH, cutSkip, bruteMismatch, verifyFail, nodesH, maxNodesH, nodesC, maxNodesC);
    return (cE || cutH) ? 3 : 0;
}
