/* s6n22.c -- S6 test over a stream of bipartite 6-regular graphs (wave6/s6n22).
 *
 * Input (stdin): graph6 lines, each a simple bipartite 6-regular graph B on 2m vertices with classes
 * A = 0..m-1 and B = m..2m-1 (genbg order). Lines starting with '>' are skipped.
 *
 * Per graph: exact E10 test, i.e. the minimum edge cut over S with 2 <= |S| <= 2m-2 (for each subset T
 * of A and each k, the best S with S n A = T and |S n B| = k takes the k B-vertices with most
 * neighbours in T; cut = 6|S| - 2e(S)). Non-E10 graphs are counted and skipped (unless -a).
 * Per E10 graph, every edge oy (o in A, y in B; Y = B - o - y is symmetric in o, y, so 6m tests):
 *   tier 1: Asratian-Mirumian frame walk. Random bijection pi: N(o)-y -> N(y)-o, Y+ = Y + Lambda,
 *           random frame (random 4-factor F of Y split into four perfect matchings, colours 0-3;
 *           (Y - F) + Lambda coloured 4/5 along its cycles). Moves: legal 3-transformations (one
 *           component of three colour classes recoloured by a random proper 3-edge-colouring; legal
 *           iff Lambda stays in colours 4, 5) and Lambda re-pairings. Phi = min over the three
 *           pairings of colours 0-3 of c(N_a u N_b) + c(N_c u N_d). Accept if Phi does not rise,
 *           else with probability 1/20. Stop at Phi = 2 or after M1 iterations; R1 walks.
 *   tier 2: DFS. Enumerate Hamilton cycles H1 of Y (random order), test Y - E(H1) for a Hamilton
 *           cycle (complete DFS); budget N2 DFS nodes in total.
 *   tier 3: the test is written to <prefix>.surv for the exact SAT decider.
 * Every pair found by tier 1 or 2 is checked directly (verify_pair): two cyclic vertex sequences of
 * length 2m-2 over V(B) - o - y, consecutive vertices adjacent in B, each sequence a permutation, and
 * the 2(2m-2) unordered vertex pairs distinct. A pair that fails the check counts as verify_fail
 * (a bug, not a result) and the test goes on to the next tier.
 * A test where tier 1 stalls gets one line in <prefix>.stall: the graph, o, y, the final frame of the
 * last walk (Lambda edges with colours, colours of the Y edges in canonical order), Phi at the end,
 * the minimum Phi seen, and the tier that then solved it.
 *
 * PIPELINE (v2, after the pilot: the DFS decides a test in about 1.4 us, the AM walk in about 30 us):
 *   AM sample (graphs with index % AMS == 0, all their edges): AM walk first, short budget MS
 *     iterations; on a stall the frame is saved, the same walk continues to MX iterations, then
 *     DFS (NA nodes, then NB nodes), then survivor.
 *   every other test: DFS (NA nodes) -> AM fallback (RF fresh walks of MF iterations) -> DFS (NB
 *     nodes) -> survivor (<prefix>.surv, decided by SAT afterwards).
 * Usage: s6n22 [-p prefix] [-s shard] [-S seed] [-A ams] [-M ms] [-X mx] [-F mf] [-R rf] [-N na]
 *              [-B nb] [-a] [-d] [-x maxstall] [-q]
 *   -a  test every graph, also non-E10 ones;  -d  no DFS (AM only; failures go to .surv)
 *   -x  write at most this many stall lines (default unlimited; counts are always complete)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

typedef uint32_t mask;
#define MAXV 30
#define MAXK 15
#define MAXE 96
#define POP(x) __builtin_popcount(x)
#define CTZ(x) __builtin_ctz(x)

static int m, nv;
static mask adjB[MAXV];
static char g6line[512];

/* ---------------- RNG (splitmix64) ---------------- */
static uint64_t rs;
static inline uint64_t rnd64(void) {
    uint64_t z = (rs += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static inline int rndint(int k) { return (int)((rnd64() >> 33) % (uint64_t)k); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static inline int rndbit(mask x) { /* a uniformly random set bit of x (x != 0) */
    int c = POP(x), r = rndint(c);
    while (r--) x &= x - 1;
    return CTZ(x);
}
static inline uint64_t mix(uint64_t a, uint64_t b) {
    uint64_t z = a * 0x9E3779B97F4A7C15ULL ^ (b + 0x632BE59BD9B4E019ULL + (a << 6) + (a >> 2));
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static inline uint64_t nowns(void) { return clock_gettime_nsec_np(CLOCK_UPTIME_RAW); }

/* ---------------- graph6 ---------------- */
static int parse_g6(const char *s) {
    int n = s[0] - 63;
    if (n < 2 || n > MAXV) return -1;
    memset(adjB, 0, sizeof adjB);
    const char *p = s + 1;
    int bit = 6, val = 0;
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++) {
            if (bit == 6) {
                if (*p < 63 || *p > 126) return -1;
                val = *p++ - 63;
                bit = 0;
            }
            if (val & (32 >> bit)) { adjB[i] |= 1u << j; adjB[j] |= 1u << i; }
            bit++;
        }
    return n;
}

/* ---------------- E10: minimum essential edge cut ---------------- */
static int min_ess_cut(void) {
    int best = 1 << 30;
    for (mask T = 0; T < (1u << m); T++) {
        int t = POP(T), hist[7] = {0, 0, 0, 0, 0, 0, 0};
        for (int j = m; j < nv; j++) hist[POP(adjB[j] & T)]++;
        int s = t, e = 0;
        if (s >= 2 && s <= nv - 2 && 6 * s - 2 * e < best) best = 6 * s - 2 * e;
        for (int c = 6; c >= 0; c--)
            for (int h = 0; h < hist[c]; h++) {
                s++; e += c;
                if (s >= 2 && s <= nv - 2 && 6 * s - 2 * e < best) best = 6 * s - 2 * e;
            }
    }
    return best;
}

/* ---------------- the test instance Y = B - o - y ---------------- */
static int O, Yv;               /* o in A, y in B (original labels) */
static int K;                   /* vertices per side of Y */
static int qv[MAXK], pv[MAXK];  /* Y index -> original label */
static int qi[MAXV], pi_[MAXV]; /* original label -> Y index */
static mask yQ[MAXK];           /* Y adjacency: q -> mask over P indices */
static int degQ[MAXK], degP[MAXK];
static int eidY[MAXK][MAXK];    /* Y edge id of (q, p), -1 if none */
static int nY;                  /* number of Y edges */
static int NE;                  /* edges of Y+ = nY + 5 */

/* frame */
static int eq[MAXE], ep[MAXE], lam[MAXE], col[MAXE];
static int atQ[MAXK][6], atP[MAXK][6];

static void setup_instance(int o, int y) {
    O = o; Yv = y; K = m - 1;
    int a = 0, b = 0;
    for (int v = 0; v < m; v++) if (v != o) { qv[a] = v; qi[v] = a; a++; }
    for (int v = m; v < nv; v++) if (v != y) { pv[b] = v; pi_[v] = b; b++; }
    nY = 0;
    for (int q = 0; q < K; q++) {
        yQ[q] = 0; degQ[q] = 0;
        for (int p = 0; p < K; p++) eidY[q][p] = -1;
    }
    for (int p = 0; p < K; p++) degP[p] = 0;
    for (int q = 0; q < K; q++) {
        mask nb = adjB[qv[q]] & ~(1u << y);
        for (mask r = nb; r; r &= r - 1) {
            int p = pi_[CTZ(r)];
            yQ[q] |= 1u << p;
            eidY[q][p] = nY; eq[nY] = q; ep[nY] = p; lam[nY] = 0; nY++;
            degQ[q]++; degP[p]++;
        }
    }
    NE = nY + 5;
}

/* ---------------- frame construction ---------------- */
static mask Hq[MAXK];
static int Hdq[MAXK], Hdp[MAXK], bq[MAXK], bp[MAXK];
static mask visP;

static int baug(int q) {
    mask cand = yQ[q] & ~Hq[q] & ~visP;
    while (cand) {
        int p = rndbit(cand);
        cand &= ~(1u << p);
        visP |= 1u << p;
        if (Hdp[p] < bp[p]) { Hq[q] |= 1u << p; Hdp[p]++; Hdq[q]++; return 1; }
        for (int q2 = 0; q2 < K; q2++) {
            if (q2 == q || !((Hq[q2] >> p) & 1)) continue;
            if (baug(q2)) {
                Hq[q2] &= ~(1u << p); Hdq[q2]--;
                Hq[q] |= 1u << p; Hdq[q]++;
                return 1;
            }
        }
    }
    return 0;
}

static int matchP[MAXK];
static mask Fq[MAXK];
static int kuhn(int q, mask *vis) {
    mask cand = Fq[q] & ~*vis;
    while (cand) {
        int p = rndbit(cand);
        cand &= ~(1u << p);
        *vis |= 1u << p;
        if (matchP[p] < 0 || kuhn(matchP[p], vis)) { matchP[p] = q; return 1; }
    }
    return 0;
}

static int build_frame(void) {
    /* Lambda: random bijection N(o)-y -> N(y)-o */
    int Po[8], Qy[8], np = 0, nq = 0;
    for (mask r = adjB[O] & ~(1u << Yv); r; r &= r - 1) Po[np++] = pi_[CTZ(r)];
    for (mask r = adjB[Yv] & ~(1u << O); r; r &= r - 1) Qy[nq++] = qi[CTZ(r)];
    if (np != 5 || nq != 5) return 0;
    for (int i = 4; i > 0; i--) { int j = rndint(i + 1); int t = Qy[i]; Qy[i] = Qy[j]; Qy[j] = t; }
    for (int i = 0; i < 5; i++) { int e = nY + i; ep[e] = Po[i]; eq[e] = Qy[i]; lam[e] = 1; }
    /* random b-matching H of Y with deg_H = deg_Y - 4 */
    int ord[MAXK];
    for (int q = 0; q < K; q++) { Hq[q] = 0; Hdq[q] = 0; bq[q] = degQ[q] - 4; ord[q] = q; }
    for (int p = 0; p < K; p++) { Hdp[p] = 0; bp[p] = degP[p] - 4; }
    for (int i = K - 1; i > 0; i--) { int j = rndint(i + 1); int t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
    for (int i = 0; i < K; i++) {
        int q = ord[i];
        if (bq[q] < 0) return 0;
        while (Hdq[q] < bq[q]) { visP = 0; if (!baug(q)) return 0; }
    }
    for (int p = 0; p < K; p++) if (Hdp[p] != bp[p]) return 0;
    /* F = Y - H into four perfect matchings, colours 0..3 */
    for (int q = 0; q < K; q++) Fq[q] = yQ[q] & ~Hq[q];
    for (int c = 0; c < 4; c++) {
        for (int p = 0; p < K; p++) matchP[p] = -1;
        for (int i = K - 1; i > 0; i--) { int j = rndint(i + 1); int t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
        for (int i = 0; i < K; i++) { mask vis = 0; if (!kuhn(ord[i], &vis)) return 0; }
        for (int p = 0; p < K; p++) {
            int q = matchP[p];
            col[eidY[q][p]] = c;
            Fq[q] &= ~(1u << p);
        }
    }
    /* H + Lambda: 2-regular; colour cycles alternately 4, 5 */
    int incQ[MAXK][2], incP[MAXK][2], nIq[MAXK], nIp[MAXK];
    for (int i = 0; i < K; i++) { nIq[i] = 0; nIp[i] = 0; }
    int hl[64], nh = 0;
    for (int q = 0; q < K; q++)
        for (mask r = Hq[q]; r; r &= r - 1) hl[nh++] = eidY[q][CTZ(r)];
    for (int i = 0; i < 5; i++) hl[nh++] = nY + i;
    for (int i = 0; i < nh; i++) {
        int e = hl[i];
        if (nIq[eq[e]] >= 2 || nIp[ep[e]] >= 2) return 0;
        incQ[eq[e]][nIq[eq[e]]++] = e; incP[ep[e]][nIp[ep[e]]++] = e;
    }
    for (int i = 0; i < K; i++) if (nIq[i] != 2 || nIp[i] != 2) return 0;
    static int done[MAXE];
    for (int i = 0; i < nh; i++) done[hl[i]] = 0;
    for (int i = 0; i < nh; i++) {
        int e = hl[i];
        if (done[e]) continue;
        int c = 4 + rndint(2);
        for (;;) {
            col[e] = c; done[e] = 1; c = 9 - c;
            int p = ep[e];
            int e2 = incP[p][0] == e ? incP[p][1] : incP[p][0];
            if (done[e2]) break;
            col[e2] = c; done[e2] = 1; c = 9 - c;
            int q = eq[e2];
            int e3 = incQ[q][0] == e2 ? incQ[q][1] : incQ[q][0];
            if (done[e3]) break;
            e = e3;
        }
    }
    for (int i = 0; i < K; i++) for (int c = 0; c < 6; c++) { atQ[i][c] = -1; atP[i][c] = -1; }
    for (int e = 0; e < NE; e++) {
        if (atQ[eq[e]][col[e]] >= 0 || atP[ep[e]][col[e]] >= 0) return 0;
        atQ[eq[e]][col[e]] = e; atP[ep[e]][col[e]] = e;
    }
    return 1;
}

/* ---------------- Phi ---------------- */
static const int PR[3][4] = {{0, 1, 2, 3}, {0, 2, 1, 3}, {0, 3, 1, 2}};
static inline int cyc(int a, int b) {
    mask all = (1u << K) - 1, seen = 0;
    int c = 0;
    while (seen != all) {
        int q0 = CTZ(~seen & all), q = q0;
        c++;
        do { seen |= 1u << q; q = eq[atP[ep[atQ[q][a]]][b]]; } while (q != q0);
    }
    return c;
}
static int phi(int *pr) {
    int best = 1000, bi = 0;
    for (int i = 0; i < 3; i++) {
        int v = cyc(PR[i][0], PR[i][1]);
        if (v >= best) continue;
        v += cyc(PR[i][2], PR[i][3]);
        if (v < best) { best = v; bi = i; if (best == 2) break; }
    }
    *pr = bi;
    return best;
}

/* ---------------- AM moves ---------------- */
static int Tc[3];
static int KE[MAXE], nKE, oldc[MAXE], newc[MAXE];
static int matchEP[MAXK], inM[MAXE], dn[MAXE];
static int undo_type, ue1, ue2;

static int kuhnK(int q, mask *vis) {
    int o0 = rndint(3);
    for (int t = 0; t < 3; t++) {
        int e = atQ[q][Tc[(o0 + t) % 3]];
        int p = ep[e];
        if ((*vis >> p) & 1) continue;
        *vis |= 1u << p;
        if (matchEP[p] < 0 || kuhnK(eq[matchEP[p]], vis)) { matchEP[p] = e; return 1; }
    }
    return 0;
}

static int other_rem_P(int p, int e) {
    for (int t = 0; t < 3; t++) { int f = atP[p][Tc[t]]; if (f != e && !inM[f]) return f; }
    return -1;
}
static int other_rem_Q(int q, int e) {
    for (int t = 0; t < 3; t++) { int f = atQ[q][Tc[t]]; if (f != e && !inM[f]) return f; }
    return -1;
}

static int am_move(void) {
    if (rnd01() < 0.1) { /* Lambda re-pairing */
        int c = 4 + rndint(2), L[5], nl = 0;
        for (int i = 0; i < 5; i++) if (col[nY + i] == c) L[nl++] = nY + i;
        if (nl < 2) return 0;
        int i = rndint(nl), j = rndint(nl - 1);
        if (j >= i) j++;
        int e1 = L[i], e2 = L[j], q1 = eq[e1], q2 = eq[e2];
        eq[e1] = q2; eq[e2] = q1;
        atQ[q1][c] = e2; atQ[q2][c] = e1;
        undo_type = 1; ue1 = e1; ue2 = e2;
        return 1;
    }
    int cs[6] = {0, 1, 2, 3, 4, 5};
    for (int i = 0; i < 3; i++) { int j = i + rndint(6 - i); int t = cs[i]; cs[i] = cs[j]; cs[j] = t; }
    Tc[0] = cs[0]; Tc[1] = cs[1]; Tc[2] = cs[2];
    /* component K of colours Tc from a random start vertex */
    mask KQ = 0, KP = 0, fq = 0, fp = 0;
    int s = rndint(2 * K);
    if (s < K) { KQ = fq = 1u << s; } else { KP = fp = 1u << (s - K); }
    while (fq | fp) {
        if (fq) {
            int q = CTZ(fq); fq &= fq - 1;
            for (int t = 0; t < 3; t++) { int p = ep[atQ[q][Tc[t]]]; if (!((KP >> p) & 1)) { KP |= 1u << p; fp |= 1u << p; } }
        } else {
            int p = CTZ(fp); fp &= fp - 1;
            for (int t = 0; t < 3; t++) { int q = eq[atP[p][Tc[t]]]; if (!((KQ >> q) & 1)) { KQ |= 1u << q; fq |= 1u << q; } }
        }
    }
    nKE = 0;
    int haslam = 0;
    for (mask r = KQ; r; r &= r - 1) {
        int q = CTZ(r);
        for (int t = 0; t < 3; t++) { int e = atQ[q][Tc[t]]; KE[nKE++] = e; oldc[e] = col[e]; if (lam[e]) haslam = 1; }
    }
    int nq = POP(KQ), qo[MAXK], k2 = 0;
    for (mask r = KQ; r; r &= r - 1) qo[k2++] = CTZ(r);
    for (int tr = 0; tr < 10; tr++) {
        for (mask r = KP; r; r &= r - 1) matchEP[CTZ(r)] = -1;
        for (int i = nq - 1; i > 0; i--) { int j = rndint(i + 1); int t = qo[i]; qo[i] = qo[j]; qo[j] = t; }
        for (int i = 0; i < nq; i++) { mask vis = 0; if (!kuhnK(qo[i], &vis)) return 0; }
        for (int i = 0; i < nKE; i++) { inM[KE[i]] = 0; dn[KE[i]] = 0; }
        for (mask r = KP; r; r &= r - 1) inM[matchEP[CTZ(r)]] = 1;
        int pr3[3] = {Tc[0], Tc[1], Tc[2]};
        for (int i = 2; i > 0; i--) { int j = rndint(i + 1); int t = pr3[i]; pr3[i] = pr3[j]; pr3[j] = t; }
        int c0 = pr3[0], c1 = pr3[1], c2 = pr3[2];
        for (int i = 0; i < nKE; i++) {
            int e = KE[i];
            if (inM[e]) { newc[e] = c0; dn[e] = 1; }
        }
        for (int i = 0; i < nKE; i++) {
            int e = KE[i];
            if (dn[e]) continue;
            int c = rndint(2) ? c1 : c2;
            for (;;) {
                newc[e] = c; dn[e] = 1; c = (c == c1) ? c2 : c1;
                int e2 = other_rem_P(ep[e], e);
                if (e2 < 0 || dn[e2]) break;
                newc[e2] = c; dn[e2] = 1; c = (c == c1) ? c2 : c1;
                int e3 = other_rem_Q(eq[e2], e2);
                if (e3 < 0 || dn[e3]) break;
                e = e3;
            }
        }
        int legal = 1;
        if (haslam)
            for (int i = 0; i < nKE; i++) { int e = KE[i]; if (lam[e] && newc[e] < 4) { legal = 0; break; } }
        if (!legal) continue;
        for (int i = 0; i < nKE; i++) col[KE[i]] = newc[KE[i]];
        for (int i = 0; i < nKE; i++) { int e = KE[i]; atQ[eq[e]][col[e]] = e; atP[ep[e]][col[e]] = e; }
        undo_type = 2;
        return 1;
    }
    return 0;
}

static void am_undo(void) {
    if (undo_type == 1) {
        int c = col[ue1], q1 = eq[ue1], q2 = eq[ue2];
        eq[ue1] = q2; eq[ue2] = q1;
        atQ[q1][c] = ue2; atQ[q2][c] = ue1;
    } else if (undo_type == 2) {
        for (int i = 0; i < nKE; i++) col[KE[i]] = oldc[KE[i]];
        for (int i = 0; i < nKE; i++) { int e = KE[i]; atQ[eq[e]][col[e]] = e; atP[ep[e]][col[e]] = e; }
    }
}

/* ---------------- direct check of a pair ---------------- */
static int verify_pair(const int *c1, const int *c2, int N) {
    mask allow = ((nv == 32) ? 0xffffffffu : ((1u << nv) - 1)) & ~(1u << O) & ~(1u << Yv);
    mask used[MAXV];
    memset(used, 0, sizeof used);
    for (int w = 0; w < 2; w++) {
        const int *c = w ? c2 : c1;
        mask seen = 0;
        for (int i = 0; i < N; i++) {
            int v = c[i];
            if (v < 0 || v >= nv || !((allow >> v) & 1) || ((seen >> v) & 1)) return 0;
            seen |= 1u << v;
        }
        if (seen != allow) return 0;
        for (int i = 0; i < N; i++) {
            int a = c[i], b = c[(i + 1) % N];
            if (!((adjB[a] >> b) & 1)) return 0;
            if ((used[a] >> b) & 1) return 0;
            used[a] |= 1u << b; used[b] |= 1u << a;
        }
    }
    return 1;
}

static int cyc_seq(int a, int b, int *out) {
    int n = 0, q = 0;
    do {
        out[n++] = qv[q];
        int e = atQ[q][a];
        int p = ep[e];
        out[n++] = pv[p];
        q = eq[atP[p][b]];
        if (n > 2 * K) return -1;
    } while (q != 0);
    return n;
}

/* ---------------- tier 2: DFS ---------------- */
static mask gY[2 * MAXK], g2[2 * MAXK];
static int NV2;
static long nodebud;
static int path1[2 * MAXK], path2[2 * MAXK];

static int dfs_hc(const mask *g, int s, int head, mask U, int depth, int *path, int randomize, int stage) {
    if (--nodebud < 0) return -1;
    if (U == 0) {
        if (!((g[head] >> s) & 1)) return 0;
        if (stage == 2) return 1;
        /* stage 1: H1 = path; test Y - H1 */
        for (int v = 0; v < NV2; v++) g2[v] = g[v];
        for (int i = 0; i < NV2; i++) {
            int a = path[i], b = path[(i + 1) % NV2];
            g2[a] &= ~(1u << b); g2[b] &= ~(1u << a);
        }
        path2[0] = 0;
        int r = dfs_hc(g2, 0, 0, ((1u << NV2) - 1) & ~1u, 1, path2, 0, 2);
        return r; /* 1 found, 0 continue enumerating H1, -1 budget */
    }
    mask avail = U | (1u << head) | (1u << s);
    for (mask r = U; r; r &= r - 1) {
        int u = CTZ(r);
        if (POP(g[u] & avail) < 2) return 0;
    }
    if (!(g[s] & (U | (1u << head)))) return 0;
    mask cand = g[head] & U;
    while (cand) {
        int v = randomize ? rndbit(cand) : CTZ(cand);
        cand &= ~(1u << v);
        path[depth] = v;
        int r = dfs_hc(g, s, v, U & ~(1u << v), depth + 1, path, randomize, stage);
        if (r != 0) return r;
    }
    return 0;
}

static int tier2(long budget, long *used) {
    NV2 = 2 * K;
    for (int q = 0; q < K; q++) {
        gY[q] = yQ[q] << K;
    }
    for (int p = 0; p < K; p++) {
        mask x = 0;
        for (int q = 0; q < K; q++) if ((yQ[q] >> p) & 1) x |= 1u << q;
        gY[K + p] = x;
    }
    nodebud = budget;
    path1[0] = 0;
    int r = dfs_hc(gY, 0, 0, ((1u << NV2) - 1) & ~1u, 1, path1, 1, 1);
    *used = budget - (nodebud < 0 ? 0 : nodebud);
    if (r == 0) return 0;   /* exhausted: Y has no two edge-disjoint Hamilton cycles */
    if (r != 1) return -1;  /* budget */
    int c1[2 * MAXK], c2[2 * MAXK];
    for (int i = 0; i < NV2; i++) {
        c1[i] = path1[i] < K ? qv[path1[i]] : pv[path1[i] - K];
        c2[i] = path2[i] < K ? qv[path2[i]] : pv[path2[i] - K];
    }
    return verify_pair(c1, c2, NV2) ? 1 : -2;
}

/* ---------------- counters ---------------- */
static long long n_graphs, n_bad, n_e10, n_non, n_tests, n_vfail, n_noframe, n_surv, n_nopair_exh;
static long long n_dfs1, n_am_fb, n_dfs2, n_dfs_nodes;
static long long n_s_tests, n_s_solved, n_s_stall, n_s_cont, n_s_dfs, n_s_noframe, n_stall_written;
static long long cut_hist[64], phi0_hist[16], mv_hist[16], phiend_hist[16], contmv_hist[16];
static uint64_t t_e10, t_dfs1, t_ams, t_fb, t_all0;
static const char *prefix = "s6n22";
static long shard = 0;
static uint64_t seed = 1;
static int AMS = 8;            /* AM sample: graphs with index % AMS == 0 run the AM walk first (0: none) */
static int MS = 64;            /* short AM budget (iterations) in the sample */
static int MX = 1000;          /* total AM budget for the continuation after a short-budget stall */
static int MF = 1000, RF = 3;  /* AM fallback after a DFS budget-out: iterations per walk, walks */
static long NA = 50000, NB = 5000000; /* DFS budgets (nodes): first pass, last pass */
static int testall = 0, quiet = 0, nodfs = 0;
static long long maxstall = -1;
static FILE *fstall, *fsurv, *fbad;
static char stallbuf[1024];

static int mvbucket(long x) {
    int b = 0;
    while (x > 0 && b < 15) { x >>= 1; b++; }
    return b; /* 0: 0 moves, b: [2^(b-1), 2^b) */
}

/* Lambda edges (P-end, Q-end, colour; original labels) and colours of the Y edges in canonical order
   (sorted by (A-vertex, B-vertex) original labels; the edge ids are in that order). */
static void frame_string(char *buf, size_t sz) {
    size_t k = 0;
    k += snprintf(buf + k, sz - k, "lam=");
    for (int i = 0; i < 5; i++) {
        int e = nY + i;
        k += snprintf(buf + k, sz - k, "%s%d-%d:%d", i ? "," : "", pv[ep[e]], qv[eq[e]], col[e]);
    }
    k += snprintf(buf + k, sz - k, " col=");
    for (int e = 0; e < nY && k + 2 < sz; e++) buf[k++] = '0' + col[e];
    buf[k] = 0;
}

static int check_phi2(int pr) {
    int N = 2 * K, c1[2 * MAXK], c2[2 * MAXK];
    int l1 = cyc_seq(PR[pr][0], PR[pr][1], c1), l2 = cyc_seq(PR[pr][2], PR[pr][3], c2);
    if (l1 == N && l2 == N && verify_pair(c1, c2, N)) return 1;
    n_vfail++;
    fprintf(fbad, "VFAIL am %s o=%d y=%d\n", g6line, O, Yv);
    return 0;
}

/* continue the walk on the current frame for at most `budget` iterations */
static int walk(int budget, int *cur, int *pr, int *phi_min, int *used) {
    int it;
    for (it = 0; it < budget && *cur > 2; it++) {
        if (!am_move()) continue;
        int npr, nw = phi(&npr);
        if (nw <= *cur || rnd01() < 0.05) { *cur = nw; *pr = npr; if (nw < *phi_min) *phi_min = nw; }
        else am_undo();
    }
    *used = it;
    return *cur == 2;
}

/* AM from fresh frames: R walks of M iterations. 1 solved (verified), 0 not, -1 no frame */
static int am_fresh(int M, int R) {
    for (int w = 0; w < R; w++) {
        if (!build_frame()) { n_noframe++; return -1; }
        int pr, cur = phi(&pr), pm = cur, used;
        if (walk(M, &cur, &pr, &pm, &used) && check_phi2(pr)) return 1;
    }
    return 0;
}

/* DFS: 1 found and verified, 0 exhausted (no pair), -1 budget, -2 verify failure */
static int dfs(long budget) {
    long used = 0;
    int r = tier2(budget, &used);
    n_dfs_nodes += used;
    if (r == -2) { n_vfail++; fprintf(fbad, "VFAIL dfs %s o=%d y=%d\n", g6line, O, Yv); }
    if (r == 0) { n_nopair_exh++; fprintf(fbad, "DFS_EXHAUSTED_NOPAIR %s o=%d y=%d\n", g6line, O, Yv); }
    return r;
}

static void survivor(void) {
    n_surv++;
    fprintf(fsurv, "%s %d %d\n", g6line, O, Yv);
    fflush(fsurv);
}

static void am_sample_test(void) {
    n_s_tests++;
    if (!build_frame()) {
        n_s_noframe++; n_noframe++;
        if (!nodfs) {
            int r = dfs(NA);
            if (r == 1 || (r == -1 && dfs(NB) == 1)) { n_s_dfs++; return; }
        }
        survivor();
        return;
    }
    int pr, cur = phi(&pr), pm = cur, used = 0;
    phi0_hist[cur < 15 ? cur : 15]++;
    if (walk(MS, &cur, &pr, &pm, &used) && check_phi2(pr)) { n_s_solved++; mv_hist[mvbucket(used)]++; return; }
    n_s_stall++;
    phiend_hist[cur < 15 ? cur : 15]++;
    int phi_stall = cur, pm_stall = pm, used2 = 0, solved = 0, cont = -1;
    frame_string(stallbuf, sizeof stallbuf);
    const char *how = "survivor";
    if (MX > MS && walk(MX - MS, &cur, &pr, &pm, &used2) && check_phi2(pr)) {
        solved = 1; n_s_cont++; contmv_hist[mvbucket(used2)]++; how = "am_continued"; cont = used2;
    }
    if (!solved && !nodfs) {
        int r = dfs(NA);
        if (r == 1 || (r == -1 && dfs(NB) == 1)) { solved = 1; n_s_dfs++; how = "dfs"; }
    }
    if (!solved) survivor();
    if (maxstall < 0 || n_stall_written < maxstall) {
        fprintf(fstall, "%s o=%d y=%d phi_stall=%d phi_min=%d moves_short=%d cont_moves=%d solved_by=%s %s\n",
                g6line, O, Yv, phi_stall, pm_stall, MS, cont, how, stallbuf);
        n_stall_written++;
    }
}

static void write_summary(const char *suffix) {
    char fn[1024];
    snprintf(fn, sizeof fn, "%s.%s", prefix, suffix);
    char tmp[1100];
    snprintf(tmp, sizeof tmp, "%s.tmp", fn);
    FILE *f = fopen(tmp, "w");
    if (!f) return;
    double wall = (nowns() - t_all0) / 1e9;
    fprintf(f, "shard=%ld\nm=%d\nseed=%llu\nAMS=%d\nMS=%d\nMX=%d\nMF=%d\nRF=%d\nNA=%ld\nNB=%ld\ndfs=%d\ntestall=%d\n",
            shard, m, (unsigned long long)seed, AMS, MS, MX, MF, RF, NA, NB, !nodfs, testall);
    fprintf(f, "graphs=%lld\nbad_input=%lld\ne10=%lld\nnon_e10=%lld\ntests=%lld\n", n_graphs, n_bad, n_e10, n_non, n_tests);
    fprintf(f, "dfs1_solved=%lld\nam_fallback_solved=%lld\ndfs2_solved=%lld\n", n_dfs1, n_am_fb, n_dfs2);
    fprintf(f, "ams_tests=%lld\nams_solved_short=%lld\nams_stalls=%lld\nams_solved_continued=%lld\nams_solved_dfs=%lld\nams_noframe=%lld\n",
            n_s_tests, n_s_solved, n_s_stall, n_s_cont, n_s_dfs, n_s_noframe);
    fprintf(f, "survivors=%lld\ndfs_exhausted_nopair=%lld\nnoframe=%lld\nverify_fail=%lld\nstall_lines=%lld\ndfs_nodes=%lld\n",
            n_surv, n_nopair_exh, n_noframe, n_vfail, n_stall_written, n_dfs_nodes);
    fprintf(f, "sec_e10=%.3f\nsec_dfs1=%.3f\nsec_ams=%.3f\nsec_fallback=%.3f\nsec_wall=%.3f\n",
            t_e10 / 1e9, t_dfs1 / 1e9, t_ams / 1e9, t_fb / 1e9, wall);
    fprintf(f, "mincut_hist=");
    for (int i = 0; i < 64; i++) if (cut_hist[i]) fprintf(f, "%d:%lld,", i, cut_hist[i]);
    fprintf(f, "\nams_phi0_hist=");
    for (int i = 0; i < 16; i++) if (phi0_hist[i]) fprintf(f, "%d:%lld,", i, phi0_hist[i]);
    fprintf(f, "\nams_moves_log2_hist=");
    for (int i = 0; i < 16; i++) if (mv_hist[i]) fprintf(f, "%d:%lld,", i, mv_hist[i]);
    fprintf(f, "\nams_stall_phi_hist=");
    for (int i = 0; i < 16; i++) if (phiend_hist[i]) fprintf(f, "%d:%lld,", i, phiend_hist[i]);
    fprintf(f, "\nams_cont_moves_log2_hist=");
    for (int i = 0; i < 16; i++) if (contmv_hist[i]) fprintf(f, "%d:%lld,", i, contmv_hist[i]);
    fprintf(f, "\n");
    fclose(f);
    rename(tmp, fn);
}

static void run_test(long long gi, int o, int y) {
    setup_instance(o, y);
    rs = mix(mix(mix(seed, (uint64_t)shard), (uint64_t)gi), (uint64_t)(o * 64 + y));
    n_tests++;
    uint64_t t0 = nowns();
    if (AMS > 0 && gi % AMS == 0) { am_sample_test(); t_ams += nowns() - t0; return; }
    int r = nodfs ? -1 : dfs(NA);
    uint64_t t1 = nowns();
    t_dfs1 += t1 - t0;
    if (r == 1) { n_dfs1++; return; }
    int solved = 0;
    if (am_fresh(MF, RF) == 1) { n_am_fb++; solved = 1; }
    else if (!nodfs && r == -1 && dfs(NB) == 1) { n_dfs2++; solved = 1; }
    t_fb += nowns() - t1;
    if (!solved) survivor();
}

int main(int argc, char **argv) {
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-p") && i + 1 < argc) prefix = argv[++i];
        else if (!strcmp(argv[i], "-s") && i + 1 < argc) shard = atol(argv[++i]);
        else if (!strcmp(argv[i], "-S") && i + 1 < argc) seed = strtoull(argv[++i], 0, 10);
        else if (!strcmp(argv[i], "-A") && i + 1 < argc) AMS = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-M") && i + 1 < argc) MS = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-X") && i + 1 < argc) MX = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-F") && i + 1 < argc) MF = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-R") && i + 1 < argc) RF = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-N") && i + 1 < argc) NA = atol(argv[++i]);
        else if (!strcmp(argv[i], "-B") && i + 1 < argc) NB = atol(argv[++i]);
        else if (!strcmp(argv[i], "-x") && i + 1 < argc) maxstall = atoll(argv[++i]);
        else if (!strcmp(argv[i], "-a")) testall = 1;
        else if (!strcmp(argv[i], "-d")) nodfs = 1;
        else if (!strcmp(argv[i], "-q")) quiet = 1;
        else { fprintf(stderr, "bad arg %s\n", argv[i]); return 2; }
    }
    char fn[1024];
    snprintf(fn, sizeof fn, "%s.stall", prefix); fstall = fopen(fn, "w");
    snprintf(fn, sizeof fn, "%s.surv", prefix); fsurv = fopen(fn, "w");
    snprintf(fn, sizeof fn, "%s.bad", prefix); fbad = fopen(fn, "w");
    if (!fstall || !fsurv || !fbad) { fprintf(stderr, "cannot open outputs\n"); return 2; }
    t_all0 = nowns();
    long long gi = -1;
    while (fgets(g6line, sizeof g6line, stdin)) {
        size_t L = strlen(g6line);
        while (L && (g6line[L - 1] == '\n' || g6line[L - 1] == '\r')) g6line[--L] = 0;
        if (!L || g6line[0] == '>') continue;
        gi++;
        n_graphs++;
        int n = parse_g6(g6line);
        if (n < 4 || (n & 1)) { n_bad++; fprintf(fbad, "BADINPUT %s\n", g6line); continue; }
        nv = n; m = n / 2;
        mask Am = (1u << m) - 1, Bm = ((1u << nv) - 1) & ~Am;
        int ok = 1;
        for (int v = 0; v < nv && ok; v++) {
            mask own = v < m ? Am : Bm;
            if ((adjB[v] & own) || POP(adjB[v]) != 6) ok = 0;
        }
        if (!ok || m - 1 > MAXK) { n_bad++; fprintf(fbad, "BADINPUT %s\n", g6line); continue; }
        uint64_t t0 = nowns();
        int mc = min_ess_cut();
        t_e10 += nowns() - t0;
        cut_hist[mc < 63 ? mc : 63]++;
        if (mc < 10) { n_non++; if (!testall) continue; }
        else n_e10++;
        for (int o = 0; o < m; o++)
            for (mask r = adjB[o]; r; r &= r - 1) run_test(gi, o, CTZ(r));
        if (!quiet && (n_graphs % 20000) == 0) write_summary("prog");
    }
    write_summary("sum");
    fclose(fstall); fclose(fsurv); fclose(fbad);
    return 0;
}
