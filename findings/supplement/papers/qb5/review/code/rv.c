/* rv.c: independent referee checker for the QB(5) paper (wave4/qb5/PAPER.md).
 * Written from scratch by the referee; shares no code with qb5/code/.
 *
 * Reads graph6 lines on stdin. Modes (argv[1]):
 *   c2     full C2 analysis per graph (Lemma 3.1 identities, Lemma 3.2 types,
 *          bad W-vertices by max flow and by violation enumeration, Thm 5.1 checks,
 *          W-small 2-blocks, alpha-petal pairs and their (2,0)/(0,2) splits,
 *          Lemma 4.1 lattice check on all of script-A).
 *   e5     full E5 analysis per graph (Thm 6.1 structure on every violation,
 *          cut matching numbers, K44, good pairs (p,q)).
 *   sparse sparsity only (prints min g over proper sets with |S| >= 3).
 * Output: one line per graph, key=value fields; "FAIL ..." lines on any mismatch.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 26
typedef uint32_t set;
static int n, ne;
static set adj[MAXN];
static int deg[MAXN], dfc[MAXN], col[MAXN];
static uint8_t *E = NULL; /* E[S] = number of edges inside S */
static set ALL;
static long nfail = 0;
static int quiet = 0;
static long AG[32];
static const char *AGN[22] = {"graphs","sparse","sparse_u0","sparse_u1u2","nbadW","badW_gamma","badW_alpha","badW_b1a","badW_b1b","badW_b2","badW_other",
  "graphs_with_nongamma_bad","allportsbad","core_fail","has_Wsmall2block_on_ZU","has_alpha_petal","alpha_split","alpha_split_both_ports",
  "max_dbadport_u1u2_no2block","max_dbadport_u1u2_with2block","lattice_split_in_A","lattice_check_skipped"};

static int pc(set x) { return __builtin_popcount(x); }

static int parse_g6(const char *s) {
    const unsigned char *p = (const unsigned char *)s;
    if (*p < 63 || *p > 126) return -1;
    int nn = *p++ - 63;
    if (nn > MAXN || nn < 1) return -1;
    n = nn;
    memset(adj, 0, sizeof adj);
    int cur = 0, nb = 0;
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++) {
            if (nb == 0) {
                if (*p < 63 || *p > 126) return -1;
                cur = *p++ - 63;
                nb = 6;
            }
            nb--;
            if ((cur >> nb) & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
        }
    ne = 0;
    for (int v = 0; v < n; v++) { deg[v] = pc(adj[v]); ne += deg[v]; dfc[v] = 6 - deg[v]; }
    ne /= 2;
    ALL = (n == 32) ? 0xffffffffu : ((1u << n) - 1);
    return 0;
}

/* 2-colour by BFS; returns 1 if connected and bipartite */
static int bipart(void) {
    for (int v = 0; v < n; v++) col[v] = -1;
    int q[MAXN], h = 0, t = 0;
    col[0] = 0; q[t++] = 0;
    while (h < t) {
        int v = q[h++];
        for (int u = 0; u < n; u++) if (adj[v] >> u & 1) {
            if (col[u] < 0) { col[u] = 1 - col[v]; q[t++] = u; }
            else if (col[u] == col[v]) return 0;
        }
    }
    return t == n;
}

static void build_E(void) {
    size_t N = (size_t)1 << n;
    E = realloc(E, N);
    E[0] = 0;
    for (size_t S = 1; S < N; S++) {
        int v = __builtin_ctz((set)S);
        set R = (set)S & ((set)S - 1);
        E[S] = E[R] + pc(adj[v] & R);
    }
}
static int g(set S) { return 6 * pc(S) - 2 * E[S]; }

/* min g over S with 3 <= |S| <= n-1; also count S with g<12 */
static int min_g_proper(long *nbad) {
    int m = 1000; long b = 0;
    for (set S = 1; S < ALL; S++) {
        int k = pc(S);
        if (k < 3) continue;
        int gg = g(S);
        if (gg < m) m = gg;
        if (gg < 12) b++;
    }
    *nbad = b;
    return m;
}

/* Edmonds-Karp: does G[M] have a spanning 4-regular subgraph? (bipartite, sides by col) */
static int has4factor(set M) {
    set L = 0, R = 0;
    for (int v = 0; v < n; v++) if (M >> v & 1) { if (col[v] == 0) L |= 1u << v; else R |= 1u << v; }
    if (pc(L) != pc(R)) return 0;
    if (M == 0) return 0;
    int S = n, T = n + 1, NN = n + 2;
    static int cap[MAXN + 2][MAXN + 2];
    memset(cap, 0, sizeof cap);
    for (int v = 0; v < n; v++) {
        if (L >> v & 1) {
            cap[S][v] = 4;
            for (int u = 0; u < n; u++) if ((R >> u & 1) && (adj[v] >> u & 1)) cap[v][u] = 1;
        }
        if (R >> v & 1) cap[v][T] = 4;
    }
    int flow = 0, need = 4 * pc(L);
    for (;;) {
        int prv[MAXN + 2], q[MAXN + 2], h = 0, t = 0;
        for (int i = 0; i < NN; i++) prv[i] = -1;
        prv[S] = S; q[t++] = S;
        while (h < t && prv[T] < 0) {
            int x = q[h++];
            for (int y = 0; y < NN; y++) if (cap[x][y] > 0 && prv[y] < 0) { prv[y] = x; q[t++] = y; }
        }
        if (prv[T] < 0) break;
        int b = 1000;
        for (int y = T; y != S; y = prv[y]) { int x = prv[y]; if (cap[x][y] < b) b = cap[x][y]; }
        for (int y = T; y != S; y = prv[y]) { int x = prv[y]; cap[x][y] -= b; cap[y][x] += b; }
        flow += b;
    }
    return flow == need;
}

static int sumdef(set S) { int d = 0; for (int v = 0; v < n; v++) if (S >> v & 1) d += dfc[v]; return d; }

/* matching number of an edge list (brute force, <= 12 edges) */
static int matchnum(int m, int (*ed)[2]) {
    int best = 0;
    for (int mask = 0; mask < (1 << m); mask++) {
        int k = pc(mask); if (k <= best) continue;
        set used = 0; int ok = 1;
        for (int i = 0; i < m && ok; i++) if (mask >> i & 1) {
            set b = (1u << ed[i][0]) | (1u << ed[i][1]);
            if (used & b) ok = 0; else used |= b;
        }
        if (ok) best = k;
    }
    return best;
}

static int hasK44(void) {
    /* choose 4 vertices on side 0 with >= 4 common neighbours */
    int s0[MAXN], c0 = 0;
    for (int v = 0; v < n; v++) if (col[v] == 0) s0[c0++] = v;
    for (int a = 0; a < c0; a++) for (int b = a + 1; b < c0; b++) for (int c = b + 1; c < c0; c++) for (int d = c + 1; d < c0; d++)
        if (pc(adj[s0[a]] & adj[s0[b]] & adj[s0[c]] & adj[s0[d]]) >= 4) return 1;
    return 0;
}

#define FAILF(...) do { nfail++; printf("FAIL "); printf(__VA_ARGS__); printf("\n"); } while (0)

/* ---------------- C2 ---------------- */
enum { T_GAMMA, T_ALPHA, T_B1A, T_B1B, T_B2, T_OTHER, NT };
static const char *tname[NT] = {"gamma", "alpha", "beta1a", "beta1b", "beta2", "other"};

#define MAXPET 200000
static set apet[MAXPET]; static int napet;
static set Aset[MAXPET]; static int nA;

static void addset(set *arr, int *cnt, set x) {
    for (int i = 0; i < *cnt; i++) if (arr[i] == x) return;
    if (*cnt < MAXPET) arr[(*cnt)++] = x;
}

static void do_c2(int gi, const char *line) {
    if (!bipart()) { FAILF("g%d not connected bipartite", gi); return; }
    int c0 = 0; for (int v = 0; v < n; v++) c0 += (col[v] == 0);
    int usd = (2 * c0 < n) ? 0 : 1; /* U = smaller side */
    set Um = 0, Wm = 0;
    for (int v = 0; v < n; v++) { if (col[v] == usd) Um |= 1u << v; else Wm |= 1u << v; }
    int s = pc(Um);
    int maxdeg = 0; for (int v = 0; v < n; v++) if (deg[v] > maxdeg) maxdeg = deg[v];
    if (pc(Wm) != s + 1 || ne != 3 * n - 5 || maxdeg > 6 || sumdef(Um) != 2) {
        FAILF("g%d not a C2 instance (s=%d |W|=%d e=%d D(U)=%d maxdeg=%d)", gi, s, pc(Wm), ne, sumdef(Um), maxdeg);
        return;
    }
    build_E();
    long nb; int mg = min_g_proper(&nb);
    int sparse = (nb == 0);
    set Zu = 0; for (int v = 0; v < n; v++) if ((Um >> v & 1) && dfc[v] > 0) Zu |= 1u << v;
    int isu0 = (pc(Zu) == 1);
    int u0 = isu0 ? __builtin_ctz(Zu) : -1;
    set Nu0 = isu0 ? adj[u0] : 0;
    /* bad by flow */
    int badflow[MAXN] = {0}, badenum[MAXN] = {0}, types[MAXN] = {0};
    for (int w = 0; w < n; w++) if (Wm >> w & 1) badflow[w] = !has4factor(ALL & ~(1u << w));
    /* enumerate all S = A u C */
    napet = 0; nA = 0;
    long nviol = 0, typecount[NT] = {0};
    for (set S = 0; S <= ALL; S++) {
        set A = S & Wm, C = S & Um;
        int k = pc(A) - pc(C);
        int sig = E[A | (Um & ~C)] - 4 * k;
        if (sig < 0 && k < 1) FAILF("g%d violation with k<1", gi);
        if (sig >= 0) { if (S == ALL) break; continue; }
        nviol++;
        set Q = ALL & ~S;
        int DC = sumdef(C), DA = sumdef(A);
        int eps = DC + E[C | (Wm & ~A)];
        if (sig != 2 * k - DA + eps) FAILF("g%d slack identity", gi);
        int gQ = g(Q), kQ = pc(Q & Um) - pc(Q & Wm), hQ = 6 * pc(Q & Wm) - E[Q];
        if (gQ != 10 + 2 * k + 2 * sig - 2 * DC || kQ != k - 1 || hQ != 8 - 2 * k + sig - DC)
            FAILF("g%d Lemma 3.1 identity (g=%d k=%d sig=%d DC=%d)", gi, gQ, k, sig, DC);
        int ty;
        if (k == 1 && sig == -1 && DC == 0 && pc(Q) == 2) ty = T_GAMMA;
        else if (k == 2 && sig == -1 && DC == 0) ty = T_ALPHA;
        else if (k == 3 && sig == -1 && DC == 0) ty = T_B1A;
        else if (k == 3 && sig == -1 && DC == 1) ty = T_B1B;
        else if (k == 3 && sig == -2 && DC == 0) ty = T_B2;
        else ty = T_OTHER;
        if (Q & Wm) typecount[ty]++; else nviol--;
        /* table values */
        static const int tg[NT] = {10, 12, 14, 12, 12, -1}, tk[NT] = {0, 1, 2, 2, 2, -9}, th[NT] = {5, 3, 1, 0, 0, -1};
        if (ty != T_OTHER && (gQ != tg[ty] || kQ != tk[ty] || hQ != th[ty])) FAILF("g%d table (g,kappa,h) type %s", gi, tname[ty]);
        if (ty != T_B1B && ty != T_OTHER && (Zu & ~Q)) FAILF("g%d petal misses Z_U type %s", gi, tname[ty]);
        for (int w = 0; w < n; w++) if (Q >> w & 1 && Wm >> w & 1) {
            badenum[w] = 1; types[w] |= 1 << ty;
            int dw = dfc[w];
            switch (ty) {
            case T_GAMMA: {
                set qu = Q & Um; int u = __builtin_ctz(qu);
                if (!(deg[u] == 4 && (adj[w] >> u & 1) && DA == 8 - dw)) FAILF("g%d gamma constraints", gi);
                break; }
            case T_ALPHA: if (!(eps <= 3 - dw && DA == 5 + eps)) FAILF("g%d alpha constraints w=%d eps=%d dw=%d", gi, w, eps, dw); break;
            case T_B1A: if (!(eps + dw <= 1 && DA == 7 + eps)) FAILF("g%d b1a constraints", gi);
                if (dw >= 1 && !(dw == 1 && eps == 0 && sumdef(Q & Wm) == 1)) FAILF("g%d b1a port", gi);
                break;
            case T_B1B: if (!(eps == 1 && dw == 0 && DA == 8)) FAILF("g%d b1b constraints", gi); break;
            case T_B2: if (!(eps == 0 && dw == 0 && DA == 8)) FAILF("g%d b2 constraints", gi); break;
            default: FAILF("g%d type other at w=%d (k=%d sig=%d DC=%d |Q|=%d)", gi, w, k, sig, DC, pc(Q));
            }
            if (dw >= 1 && (ty == T_B1B || ty == T_B2)) FAILF("g%d port with beta1b/beta2", gi);
        }
        if (ty == T_ALPHA) addset(apet, &napet, Q);
        if (S == ALL) break;
    }
    int nbad = 0, nbadport = 0, dbadport = 0, goodport = 0, goodoff = 0, nport = 0, allportsbad = 1;
    int tyw[NT] = {0};
    for (int w = 0; w < n; w++) if (Wm >> w & 1) {
        if (badflow[w] != badenum[w]) FAILF("g%d flow/enumeration disagree at w=%d", gi, w);
        if (dfc[w] > 0) nport++;
        if (badflow[w]) {
            nbad++;
            for (int t = 0; t < NT; t++) if (types[w] >> t & 1) tyw[t]++;
            if (dfc[w] > 0) { nbadport++; dbadport += dfc[w]; }
        } else {
            if (dfc[w] > 0) goodport = 1;
            if (isu0 && !(Nu0 >> w & 1)) goodoff = 1;
        }
        if (dfc[w] > 0 && !badflow[w]) allportsbad = 0;
    }
    int onlygamma = 1; for (int w = 0; w < n; w++) if ((Wm >> w & 1) && badflow[w] && types[w] != (1 << T_GAMMA)) onlygamma = 0;
    /* W-small 2-blocks containing Z_U, and script-A */
    int n2b = 0; nA = 0;
    for (set S = 1; S < ALL; S++) {
        if ((S & Zu) != Zu) continue;
        int k = pc(S); if (k < 3) continue;
        int kap = pc(S & Um) - pc(S & Wm);
        int gg = g(S);
        if (gg == 12 && kap == 2) n2b++;
        if (gg == 12 && kap == 1 && k >= 4) addset(Aset, &nA, S);
    }
    /* Lemma 4.1 on all pairs of script-A */
    long lat11 = 0, lat20 = 0, lat02 = 0;
    int latdone = (nA <= 6000);
    if (latdone) for (int i = 0; i < nA; i++) for (int j = i + 1; j < nA; j++) {
        set I = Aset[i] & Aset[j], Un = Aset[i] | Aset[j];
        if (pc(I) < 3 || Un == ALL || g(I) != 12 || g(Un) != 12) FAILF("g%d Lemma 4.1 basic", gi);
        int kI = pc(I & Um) - pc(I & Wm), kU = pc(Un & Um) - pc(Un & Wm);
        if (kI == 1 && kU == 1) lat11++; else if (kI == 2 && kU == 0) lat20++; else if (kI == 0 && kU == 2) lat02++;
        else FAILF("g%d Lemma 4.1 kappa split (%d,%d)", gi, kI, kU);
        if ((kI == 2 || kU == 2) && n2b == 0) FAILF("g%d split without W-small 2-block", gi);
    }
    /* alpha-petal pairs */
    long sp20 = 0, sp02 = 0, sp20port = 0, sp02port = 0;
    int ex_i = -1, ex_j = -1;
    for (int i = 0; i < napet; i++) for (int j = i + 1; j < napet; j++) {
        set I = apet[i] & apet[j], Un = apet[i] | apet[j];
        int kI = pc(I & Um) - pc(I & Wm), kU = pc(Un & Um) - pc(Un & Wm);
        int porti = 0, portj = 0;
        for (int w = 0; w < n; w++) if ((Wm >> w & 1) && dfc[w] > 0) { if (apet[i] >> w & 1) porti = 1; if (apet[j] >> w & 1) portj = 1; }
        if (kI == 2 && kU == 0) { sp20++; if (porti && portj) sp20port++; if (ex_i < 0) { ex_i = i; ex_j = j; } }
        if (kI == 0 && kU == 2) { sp02++; if (porti && portj) sp02port++; }
    }
    /* Theorem 5.1 checks */
    int core = isu0 ? goodoff : goodport;
    if (!core && sparse) FAILF("g%d Theorem 5.1 core check fails", gi);
    if (!isu0 && sparse) {
        int bound = n2b ? 6 : 5;
        if (dbadport > bound) FAILF("g%d bad-port deficiency %d > %d", gi, dbadport, bound);
    }
    if (quiet) {
        AG[0]++; if (sparse) { AG[1]++; AG[isu0 ? 2 : 3]++; AG[4] += nbad; for (int t = 0; t < NT; t++) AG[5 + t] += tyw[t];
            if (!onlygamma && nbad) AG[11]++; if (allportsbad) AG[12]++; if (!core) AG[13]++; if (n2b) AG[14]++;
            if (napet) AG[15]++; if (sp20 || sp02) AG[16]++; if (sp20port || sp02port) AG[17]++;
            if (!isu0) { int ix = n2b ? 19 : 18; if (dbadport > AG[ix]) AG[ix] = dbadport; }
            if (lat20 || lat02) AG[20]++; if (nA < 0 || !latdone) AG[21]++; }
        int interesting = sparse && (!onlygamma && nbad || allportsbad || !core || n2b || napet || sp20 || sp02);
        if (!interesting) return;
    }
    printf("g%d n=%d sparse=%d ming=%d zu=%s n2b=%d nviol=%ld types[g,a,b1a,b1b,b2,o]=%ld,%ld,%ld,%ld,%ld,%ld "
           "nbad=%d badW_types[g,a,b1a,b1b,b2,o]=%d,%d,%d,%d,%d,%d onlygamma=%d nport=%d nbadport=%d dbadport=%d allportsbad=%d "
           "goodport=%d goodoff=%d core=%d nA=%d lat11=%ld lat20=%ld lat02=%ld napet=%d asplit20=%ld asplit02=%ld split20ports=%ld split02ports=%ld",
           gi, n, sparse, mg, isu0 ? "u0" : "u1u2", n2b, nviol,
           typecount[0], typecount[1], typecount[2], typecount[3], typecount[4], typecount[5],
           nbad, tyw[0], tyw[1], tyw[2], tyw[3], tyw[4], tyw[5], onlygamma, nport, nbadport, dbadport, allportsbad,
           goodport, goodoff, core, nA * (latdone ? 1 : -1), lat11, lat20, lat02, napet, sp20, sp02, sp20port, sp02port);
    if (ex_i >= 0) {
        set I = apet[ex_i] & apet[ex_j];
        printf(" ex_I=");
        for (int v = 0; v < n; v++) if (I >> v & 1) printf("%d,", v);
        printf(" ex_Q-I="); for (int v = 0; v < n; v++) if ((apet[ex_i] & ~I) >> v & 1) printf("%d,", v);
        printf(" ex_Q'-I="); for (int v = 0; v < n; v++) if ((apet[ex_j] & ~I) >> v & 1) printf("%d,", v);
    }
    if (isu0) printf(" u0=%d", u0);
    printf("\n");
    (void)line;
}

/* ---------------- E5 ---------------- */
static void do_e5(int gi, int dopairs) {
    if (!bipart()) { FAILF("g%d not connected bipartite", gi); return; }
    set Pm = 0, Qm = 0;
    for (int v = 0; v < n; v++) { if (col[v] == 0) Pm |= 1u << v; else Qm |= 1u << v; }
    int maxdeg = 0; for (int v = 0; v < n; v++) if (deg[v] > maxdeg) maxdeg = deg[v];
    if (pc(Pm) != pc(Qm) || ne != 3 * n - 5 || maxdeg > 6 || sumdef(Pm) != 5 || sumdef(Qm) != 5) {
        FAILF("g%d not an E5 instance", gi); return;
    }
    build_E();
    long nb; int mg = min_g_proper(&nb);
    int sparse = (nb == 0);
    int f4 = has4factor(ALL);
    int mindeg = 9; for (int v = 0; v < n; v++) if (deg[v] < mindeg) mindeg = deg[v];
    long nviol = 0; int mmin = 99, mmax = -1, structok = 1;
    int sizesX[64] = {0};
    for (int orient = 0; orient < 2; orient++) {
        set P = orient ? Qm : Pm, Q = orient ? Pm : Qm;
        for (set S = 0; S <= ALL; S++) {
            set A = S & P, C = S & Q;
            int k = pc(A) - pc(C);
            int sig = E[A | (Q & ~C)] - 4 * k;
            if (sig < 0 && k < 1) FAILF("g%d e5 violation k<1", gi);
            if (sig >= 0) { if (S == ALL) break; continue; }
            nviol++;
            int DA = sumdef(A), DC = sumdef(C);
            int eps = DC + E[C | (P & ~A)];
            if (sig != 2 * k - DA + eps) FAILF("g%d e5 slack identity", gi);
            set X = A | C, Y = ALL & ~X, B = P & ~A, D = Q & ~C;
            int ok = (k == 2 && sig == -1 && eps == 0 && DA == 5 && g(X) == 12 && g(Y) == 12 && sumdef(D) == 5 && sumdef(B) == 0 && DC == 0
                      && pc(C) >= 4 && pc(B) >= 4);
            /* N(C) in A, N(B) in D */
            for (int v = 0; v < n; v++) {
                if ((C >> v & 1) && (adj[v] & ~A)) ok = 0;
                if ((B >> v & 1) && (adj[v] & ~D)) ok = 0;
            }
            int ed[80][2], m = 0;
            for (int v = 0; v < n; v++) if (X >> v & 1) for (int u = 0; u < n; u++) if ((Y >> u & 1) && (adj[v] >> u & 1)) {
                if (!((A >> v & 1) && (D >> u & 1))) ok = 0;
                if (m < 80) { ed[m][0] = v; ed[m][1] = u; } m++;
            }
            if (m != 7) ok = 0;
            if (!ok) { structok = 0; FAILF("g%d Theorem 6.1 structure", gi); }
            else {
                int mn = matchnum(7, ed);
                if (mn < mmin) mmin = mn;
                if (mn > mmax) mmax = mn;
                if (pc(X) < 64) sizesX[pc(X)]++;
                /* first step of Lemma 6.3 (sparsity only): a vertex with >= 3 cut edges has exactly 3, in-block degree 3, degree 6 */
                for (int v = 0; v < n; v++) {
                    int cv = 0; for (int i = 0; i < 7; i++) if (ed[i][0] == v || ed[i][1] == v) cv++;
                    if (cv >= 3) {
                        set blk = (X >> v & 1) ? X : Y;
                        if (!(cv == 3 && pc(adj[v] & blk) == 3 && deg[v] == 6)) FAILF("g%d Lemma 6.3 first step v=%d", gi, v);
                    }
                }
            }
            if (S == ALL) break;
        }
    }
    int k44 = hasK44();
    int goodpairs = -1, totalpairs = pc(Pm) * pc(Qm);
    int gpA_D = 0;
    if (dopairs) {
        goodpairs = 0;
        for (int p = 0; p < n; p++) if (Pm >> p & 1) for (int q = 0; q < n; q++) if (Qm >> q & 1)
            if (has4factor(ALL & ~(1u << p) & ~(1u << q))) goodpairs++;
    }
    (void)gpA_D;
    printf("g%d n=%d sparse=%d ming=%d mindeg=%d has4factor=%d nviol=%ld structok=%d cutmatch_min=%d cutmatch_max=%d K44=%d goodpairs=%d/%d Xsizes=",
           gi, n, sparse, mg, mindeg, f4, nviol, structok, mmin, mmax, k44, goodpairs, totalpairs);
    for (int i = 0; i < 64; i++) if (sizesX[i]) printf("%d:%d,", i, sizesX[i]);
    printf("\n");
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: rv c2|e5|e5pairs|sparse < g6\n"); return 2; }
    char line[4096];
    int gi = 0;
    while (fgets(line, sizeof line, stdin)) {
        size_t L = strlen(line);
        while (L && (line[L - 1] == '\n' || line[L - 1] == '\r')) line[--L] = 0;
        if (L == 0) continue;
        const char *s = line;
        if (strncmp(s, ">>graph6<<", 10) == 0) s += 10;
        if (parse_g6(s) < 0) { FAILF("parse error line %d", gi); gi++; continue; }
        if (!strcmp(argv[1], "c2")) do_c2(gi, s);
        else if (!strcmp(argv[1], "c2q")) { quiet = 1; do_c2(gi, s); }
        else if (!strcmp(argv[1], "e5")) do_e5(gi, 0);
        else if (!strcmp(argv[1], "e5pairs")) do_e5(gi, 1);
        else if (!strcmp(argv[1], "sparse")) {
            build_E(); long nb; int mg = min_g_proper(&nb);
            int bp = bipart();
            printf("g%d n=%d e=%d bip=%d sparse=%d ming=%d\n", gi, n, ne, bp, nb == 0, mg);
        }
        gi++;
        fflush(stdout);
    }
    if (quiet) { for (int i = 0; i < 22; i++) fprintf(stderr, "%s=%ld ", AGN[i], AG[i]); fprintf(stderr, "\n"); }
    fprintf(stderr, "graphs=%d fails=%ld\n", gi, nfail);
    return nfail ? 1 : 0;
}
