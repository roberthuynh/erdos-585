/* kl1rev.c -- REVIEW4 independent checker for PAPER4 (proof of KL1).
 * Written from scratch for the review; shares no code with qb5/code.
 *
 * Input: one block per line, "na nc mask_1 ... mask_nc [extra fields ignored]".
 * mask_c is a bitmask over A = {0..na-1}: c ~ a iff bit a is set.
 *
 * For every block: validate (H1)-(H3) (|A| = |C| + 2, every c of degree 6, d_a >= 3,
 * block sparsity g(S) >= 12 for all S subset X with |S| >= 3).
 * For every multiset m on A with m(A) = 4, 0 <= m(a) <= min(3, delta_a):
 *   theta*(T) = m(T) + 4 - 4|T| + sum_c (e(c,T) - 2)^+, overloaded iff >= 1,
 *   maximal overloaded sets, I_X = A minus their union, and every claim of PAPER4 §2-§3
 *   that can be tested on the data (see the V-codes below).
 *
 * Usage: kl1rev [-v] [-s seed] < blocks
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXA 24
#define MAXC 22
#define MAXOV 200000
#define MAXMX 4096

static int na, nc;
static uint32_t cm[MAXC];
static int dA[MAXA], del[MAXA];
static uint32_t fullA, fullC;
static int verbose = 0;

static inline int pc(uint32_t x) { return __builtin_popcount(x); }

/* ---- basic set functions on S = (TA subset A, TC subset C) ---- */
static int eS(uint32_t TA, uint32_t TC) { int s = 0; for (int c = 0; c < nc; c++) if (TC >> c & 1) s += pc(cm[c] & TA); return s; }
static int msum(const int *v, uint32_t TA) { int s = 0; for (int a = 0; a < na; a++) if (TA >> a & 1) s += v[a]; return s; }
static int gS(uint32_t TA, uint32_t TC) { return 6 * (pc(TA) + pc(TC)) - 2 * eS(TA, TC); }
static int kapS(uint32_t TA, uint32_t TC) { return pc(TA) - pc(TC); }
/* theta(S) by the definition m(S_A) + 4 - kappa - g/2 */
static int thS(const int *m, uint32_t TA, uint32_t TC) {
    int g = gS(TA, TC);
    return msum(m, TA) + 4 - kapS(TA, TC) - g / 2;
}
static int dAS(uint32_t TA, uint32_t TC) { int s = 0; for (int c = 0; c < nc; c++) if (!(TC >> c & 1)) s += pc(cm[c] & TA); return s; }
static int dCS(uint32_t TA, uint32_t TC) { int s = 0; for (int c = 0; c < nc; c++) if (TC >> c & 1) s += 6 - pc(cm[c] & TA); return s; }
static uint32_t Cge(uint32_t T, int k) { uint32_t r = 0; for (int c = 0; c < nc; c++) if (pc(cm[c] & T) >= k) r |= 1u << c; return r; }
static int thstar(const int *m, uint32_t T) { /* direct formula */
    int s = msum(m, T) + 4 - 4 * pc(T);
    for (int c = 0; c < nc; c++) { int e = pc(cm[c] & T); if (e > 2) s += e - 2; }
    return s;
}

/* ---- violation counters ---- */
enum { V0, V1, V1b, V2, V3, V4, V5, V6, V7, V8, NV };
static const char *vname[NV] = {
    "V0 Lemma 2.1 identities (random S, S')",
    "V1 theta* <= 2 on |T|>=3",
    "V1b Lemma 2.2(b),(c) on X'(T), T big overloaded",
    "V2 Lemma 3.2 on pairs of maximal sets",
    "V3 hub-free maximal family covers A (Lemma 3.3)",
    "V4 Lemma 3.4 (whole maximal family)",
    "V5 Lemma 3.5 (whole maximal family)",
    "V6 KL1: covering m with I_X empty",
    "V7 minimal subcover without a pair sharing >= 3",
    "V8 per-petal bounds of the proof of Thm 3.1 (covering m)",
};
static long viol[NV];
static long nblocks, nbad_struct, nnonsparse, nmult, ncover, nIXempty_cov, nIXempty_noncov;
static long npair0, npair1, npair2, npair3, nhubm, nhubm_cov, nmincov, nmincov_nohub, nhub_beta, nhub_delta, npet[5];
static long nfail_w3petal, nfail_yy, nfail_other, nsing_cov, nrmax;

static void report(int code, const char *msg, int line, const int *m) {
    viol[code]++;
    if (viol[code] <= 20) {
        fprintf(stderr, "VIOLATION %s line %d: %s | m =", vname[code], line, msg);
        for (int a = 0; a < na; a++) fprintf(stderr, " %d", m[a]);
        fprintf(stderr, "\n");
    }
}

/* candidate sets: base(T) = 4 - 4|T| + sum (e-2)^+ >= -3 (else theta* <= 0 for every m) */
static uint32_t *cand; static int *cbase; static int ncand;
static uint32_t ov[MAXOV]; static int ovth[MAXOV]; static int nov;
static uint32_t mx[MAXMX]; static int mxth[MAXMX]; static int nmx;

static uint64_t rng = 88172645463325252ull;
static uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static int lineno;

/* minimal subcover enumeration over maximal family */
static int covsel[MAXMX], ncovsel;
static long mincov_found;
static const int *gm; static const int *gw;
static uint64_t seen[8192]; static int nseen;
static void check_mincover(void) {
    /* minimality: each member has a private vertex */
    for (int i = 0; i < ncovsel; i++) {
        uint32_t others = 0;
        for (int j = 0; j < ncovsel; j++) if (j != i) others |= mx[covsel[j]];
        if ((mx[covsel[i]] & ~others) == 0) return;
    }
    /* dedupe: the same minimal cover can be reached by several branch orders */
    uint64_t key = 0; for (int i = 0; i < ncovsel; i++) key |= 1ull << (covsel[i] & 63);
    for (int i = 0; i < nseen; i++) if (seen[i] == key) return;
    if (nseen < 8192) seen[nseen++] = key;
    mincov_found++;
    nmincov++;
    int hub = 0;
    for (int i = 0; i < ncovsel && !hub; i++)
        for (int j = i + 1; j < ncovsel; j++)
            if (pc(mx[covsel[i]] & mx[covsel[j]]) >= 3) { hub = 1; break; }
    if (!hub) { nmincov_nohub++; report(V7, "hub-free minimal subcover", lineno, gm); }
}
static void enum_covers(uint32_t covered) {
    if (mincov_found > 5000) return;
    if (covered == fullA) { check_mincover(); return; }
    /* lowest uncovered vertex, branch on members containing it, with index order to limit duplicates */
    int v = __builtin_ctz(~covered & fullA);
    for (int i = 0; i < nmx; i++) {
        if (!(mx[i] >> v & 1)) continue;
        int dup = 0; for (int k = 0; k < ncovsel; k++) if (covsel[k] == i) dup = 1;
        if (dup) continue;
        covsel[ncovsel++] = i;
        enum_covers(covered | mx[i]);
        ncovsel--;
    }
}

static void analyze_m(const int *m) {
    int w[MAXA];
    int covering = 1;
    for (int a = 0; a < na; a++) { w[a] = del[a] - m[a]; if (del[a] == 3 && m[a] == 0) covering = 0; }
    nmult++; if (covering) ncover++;
    gm = m; gw = w;

    /* overloaded sets among candidates */
    nov = 0;
    for (int i = 0; i < ncand; i++) {
        int th = msum(m, cand[i]) + cbase[i];
        if (th >= 1) { if (nov >= MAXOV) { fprintf(stderr, "MAXOV\n"); exit(2); } ov[nov] = cand[i]; ovth[nov] = th; nov++; }
        if (pc(cand[i]) >= 3 && th > 2) report(V1, "theta*>2", lineno, m);
    }
    /* maximal */
    nmx = 0;
    for (int i = 0; i < nov; i++) {
        int ismax = 1;
        for (int j = 0; j < nov; j++) if (j != i && (ov[i] & ov[j]) == ov[i] && ov[j] != ov[i]) { ismax = 0; break; }
        if (ismax) { if (nmx >= MAXMX) { fprintf(stderr, "MAXMX\n"); exit(2); } mx[nmx] = ov[i]; mxth[nmx] = ovth[i]; nmx++; }
    }
    uint32_t uni = 0; for (int i = 0; i < nmx; i++) uni |= mx[i];
    uint32_t IX = fullA & ~uni;

    /* V1b: Lemma 2.2(b),(c) for big overloaded T on S = X'(T) */
    for (int i = 0; i < nov; i++) {
        uint32_t T = ov[i]; if (pc(T) < 3) continue;
        uint32_t Cp = Cge(T, 3);
        int th = thS(m, T, Cp), k = kapS(T, Cp), g = gS(T, Cp), mt = msum(m, T);
        int h = msum(w, T) + dAS(T, Cp);
        if (th != ovth[i]) report(V1b, "theta(X'(T)) != theta*(T)", lineno, m);
        if (Cp == 0) report(V1b, "C'(T) empty", lineno, m);
        if (k < -1 || k > mt - 3) report(V1b, "kappa(X'(T)) out of [-1, m-3]", lineno, m);
        if (th > mt - 2 - k || ((th == mt - 2 - k) != (g == 12))) report(V1b, "theta <= m-2-kappa / equality", lineno, m);
        if (3 * th > 2 * mt - h || ((3 * th == 2 * mt - h) != (g == 12))) report(V1b, "3theta <= 2m - w - dA / equality", lineno, m);
        if (th != 4 + 2 * k - h) report(V1b, "Lemma 2.1(a) on X'(T)", lineno, m);
        if (th != mt + 4 - 4 * k - dCS(T, Cp)) report(V1b, "Lemma 2.1(b) on X'(T)", lineno, m);
        if (mt < 2) report(V1b, "m(T) < 2", lineno, m);
    }

    /* V2: pairs of maximal sets */
    int hubi = -1, hubj = -1;
    for (int i = 0; i < nmx; i++) for (int j = i + 1; j < nmx; j++) {
        uint32_t T = mx[i], U = mx[j], I = T & U;
        int ti = mxth[i], tj = mxth[j];
        if (thstar(m, T | U) > 0) report(V2, "theta*(T u T') > 0 for two maximal sets", lineno, m);
        uint32_t S1C = Cge(T, 3), S2C = Cge(U, 3);
        int thI = thS(m, I, S1C & S2C);
        /* e(S - S', S' - S) */
        uint32_t DA1 = T & ~U, DC1 = S1C & ~S2C, DA2 = U & ~T, DC2 = S2C & ~S1C;
        int cross = eS(DA1, DC2) + eS(DA2, DC1);
        if (thI < ti + tj + cross || thI < 2) report(V2, "theta(S n S') < theta*T + theta*T' + e(...)", lineno, m);
        int s = pc(I);
        if (s == 0) npair0++;
        else if (s == 2) { npair2++; report(V2, "|T n T'| = 2", lineno, m); }
        else if (s == 1) {
            npair1++;
            int a = __builtin_ctz(I);
            int J = pc(S1C & S2C);
            if (m[a] < ti + tj || m[a] < 2) report(V2, "(N1) m(a) < theta*T + theta*T'", lineno, m);
            if (J > m[a] - 2) report(V2, "(N1) |C'(T) n C'(T')| > m(a) - 2", lineno, m);
            if (verbose) {
                int k1 = kapS(T, S1C), k2 = kapS(U, S2C);
                int aJ = 0; for (int c = 0; c < nc; c++) if (((S1C & S2C) >> c & 1) && (cm[c] >> a & 1)) aJ++;
                printf("N1 line %d a=%d m(a)=%d d_a=%d theta*=(%d,%d) m(T)=(%d,%d) |T|=(%d,%d) kappa=(%d,%d) |J|=%d a~J=%d covering=%d IX=%x m=",
                       lineno, a, m[a], dA[a], ti, tj, msum(m, T), msum(m, U), pc(T), pc(U), k1, k2, J,
                       aJ, covering, IX);
                for (int b = 0; b < na; b++) printf("%d", m[b]);
                printf(" T=%x T'=%x\n", T, U);
            }
        } else {
            npair3++;
            if (thstar(m, I) != 2 || ti != 1 || tj != 1) report(V2, "(N3) theta*(T n T') != 2 or theta* != 1", lineno, m);
            if (hubi < 0) { hubi = i; hubj = j; }
        }
    }

    /* V3: hub-free maximal family must not cover A */
    if (hubi < 0 && IX == 0) report(V3, "hub-free maximal family covers A", lineno, m);

    /* V4/V5/V8: hub structure for the whole maximal family */
    if (hubi >= 0) {
        nhubm++; if (covering) nhubm_cov++;
        uint32_t K = mx[hubi] & mx[hubj];
        int mK = msum(m, K), wK = msum(w, K);
        if (thstar(m, K) != 2) report(V4, "theta*(K) != 2", lineno, m);
        if (mK < 3) report(V4, "m(K) < 3", lineno, m);
        for (int i = 0; i < ncand; i++) {
            uint32_t T = cand[i];
            if ((T & K) == K && T != K && msum(m, T) + cbase[i] >= 2) { report(V4, "strict superset of K with theta* >= 2", lineno, m); break; }
        }
        uint32_t KpC = Cge(K, 2);
        int thKp = thS(m, K, KpC), kKp = kapS(K, KpC), gKp = gS(K, KpC);
        int dAK = dAS(K, KpC), dCK = dCS(K, KpC), dK = dAK + dCK;
        if (thKp != 2) report(V4, "theta(K+) != 2", lineno, m);
        int caseb = 0;
        if (covering) { if (kKp == -1) nhub_beta++; else if (kKp == 0) nhub_delta++; }
        if (kKp == -1) { caseb = 1; if (wK != 0 || dAK != 0 || dK != mK + 6) report(V4, "case beta data", lineno, m); }
        else if (kKp == 0) { caseb = 2; if (mK != 4 || gKp != 12 || dK != 8 - wK) report(V4, "case delta data", lineno, m); }
        else report(V4, "kappa(K+) not in {-1,0}", lineno, m);
        /* (c), (d) */
        int nbig = 0, nsing = 0; int bigidx[MAXMX];
        for (int i = 0; i < nmx; i++) {
            uint32_t T = mx[i];
            if (pc(T) >= 3) {
                bigidx[nbig++] = i;
                if ((T & K) != K) report(V4, "big maximal set does not contain K", lineno, m);
                if (mxth[i] != 1) report(V4, "big maximal set theta* != 1", lineno, m);
            } else if (pc(T) == 1) {
                nsing++;
                int u = __builtin_ctz(T);
                if ((K >> u & 1) || m[u] != 1) report(V4, "singleton member u in K or m(u) != 1", lineno, m);
            } else report(V4, "maximal set of size 0 or 2", lineno, m);
        }
        if (nsing > 1 || (mK == 4 && nsing > 0)) report(V4, "too many singletons", lineno, m);
        if (covering && nsing) nsing_cov++;
        if (covering && nbig > nrmax) nrmax = nbig;
        for (int x = 0; x < nbig; x++) for (int y = x + 1; y < nbig; y++)
            if ((mx[bigidx[x]] & mx[bigidx[y]]) != K) report(V4, "two big maximal sets do not meet exactly in K", lineno, m);
        /* Lemma 3.5 */
        uint32_t Pu_A = 0, Pu_C = 0; int sumE = 0;
        for (int x = 0; x < nbig; x++) {
            uint32_t T = mx[bigidx[x]];
            uint32_t SA = T, SC = Cge(T, 3) | KpC;
            uint32_t PA = SA & ~K, PC = SC & ~KpC;
            int thSi = thS(m, SA, SC);
            if (thSi != 1) report(V5, "theta(S_i) != 1", lineno, m);
            if ((PA & Pu_A) || (PC & Pu_C)) report(V5, "petals not disjoint", lineno, m);
            Pu_A |= PA; Pu_C |= PC;
            if (PA == 0) report(V5, "Q_i empty", lineno, m);
            int Ei = eS(K, PC) + eS(PA, KpC);
            sumE += Ei;
            int thP = thS(m, PA, PC);
            if (thP != 3 - Ei) report(V5, "theta(P_i) != 3 - E_i", lineno, m);
            int kS = kapS(SA, SC), mT = msum(m, T), wQ = msum(w, PA), mQ = msum(m, PA), kP = kapS(PA, PC);
            if (wK + wQ > 3 + 2 * kS) report(V5, "w(K)+w(Q_i) > 3 + 2 kappa(S_i)", lineno, m);
            if (kS < -1 || kS > mT - 3) report(V5, "kappa(S_i) out of range", lineno, m);
            int sz = pc(PA) + pc(PC);
            if (covering) { if (sz == 1) npet[0]++; else if (sz == 2 && pc(PA) == 1) npet[1]++; else if (sz == 2) npet[2]++; else if (kP == 2) npet[4]++; else npet[3]++; }
            if (sz >= 3) { if (Ei < 5 - mQ + kP) report(V5, "(d) |P_i|>=3 bound", lineno, m); }
            else if (sz == 1) { int y = __builtin_ctz(PA); if (Ei != 3 - m[y]) report(V5, "(d) {y}", lineno, m); }
            else if (pc(PA) == 1) { int y = __builtin_ctz(PA), c = __builtin_ctz(PC); int eyc = (cm[c] >> y) & 1; if (Ei != 5 - m[y] - eyc) report(V5, "(d) {y,c}", lineno, m); }
            else if (pc(PA) == 2) { if (Ei != 7 - mQ) report(V5, "(d) {y,y'}", lineno, m); }
            else report(V5, "(d) petal shape", lineno, m);
            /* V8: per-petal bounds used in the proof, under covering */
            if (covering) {
                if (caseb == 1) {
                    /* 3 w(Q_i) <= 2 (E_i + m(Q_i)), plus 1 if |P_i| >= 3 and kappa(P_i) = 2 */
                    int ex = (sz >= 3 && kP == 2) ? 1 : 0;
                    if (3 * wQ > 2 * (Ei + mQ) + ex) report(V8, "case beta petal bound", lineno, m);
                    if (kP != kS + 1 || kP < 0 || kP > 2) report(V8, "case beta kappa(P_i)", lineno, m);
                } else if (caseb == 2) {
                    if (wQ >= Ei) report(V8, "case delta petal bound w(Q_i) < E_i", lineno, m);
                }
            }
        }
        if (sumE > dK) report(V5, "sum E_i > boundary of K+", lineno, m);
        /* record how non-covering failures look (proof uses covering only at petals {y}, {y,y'}) */
        if (!covering && IX == 0) {
            int w3 = 0, yy = 0;
            for (int x = 0; x < nbig; x++) {
                uint32_t T = mx[bigidx[x]], PA = T & ~K, PC = (Cge(T, 3) | KpC) & ~KpC;
                int sz = pc(PA) + pc(PC);
                if (sz == 1 && w[__builtin_ctz(PA)] == 3) w3 = 1;
                if (sz == 2 && pc(PA) == 2 && msum(w, PA) >= 5) yy = 1;
            }
            if (w3) nfail_w3petal++; else if (yy) nfail_yy++; else nfail_other++;
        }
    }

    /* V6 KL1 */
    if (IX == 0) {
        if (covering) { nIXempty_cov++; report(V6, "KL1 fails", lineno, m); }
        else nIXempty_noncov++;
        /* V7 minimal subcovers */
        mincov_found = 0; ncovsel = 0; nseen = 0;
        if (nmx > 64) { fprintf(stderr, "nmx > 64 at line %d, subcover dedupe disabled\n", lineno); }
        enum_covers(0);
    }
}


static int m_cur[MAXA];
static void enum_m(int a, int left) {
    if (a == na) { if (left == 0) analyze_m(m_cur); return; }
    int cap = del[a] < 3 ? del[a] : 3;
    for (int v = 0; v <= cap && v <= left; v++) { m_cur[a] = v; enum_m(a + 1, left - v); }
    m_cur[a] = 0;
}

static void identities_check(void) {
    int m[MAXA], w[MAXA];
    /* random m with m <= delta, m(A) = 4 is not needed for identities; use any m <= delta */
    for (int a = 0; a < na; a++) { m[a] = del[a] ? (int)(xr() % (del[a] + 1)) : 0; w[a] = del[a] - m[a]; }
    for (int it = 0; it < 40; it++) {
        uint32_t A1 = (uint32_t)xr() & fullA, C1 = (uint32_t)xr() & fullC, A2 = (uint32_t)xr() & fullA, C2 = (uint32_t)xr() & fullC;
        int t1 = thS(m, A1, C1), t2 = thS(m, A2, C2);
        int k1 = kapS(A1, C1);
        int h1 = msum(w, A1) + dAS(A1, C1);
        if (t1 != 4 + 2 * k1 - h1) report(V0, "2.1(a)", lineno, m);
        if (t1 != msum(m, A1) + 4 - 4 * k1 - dCS(A1, C1)) report(V0, "2.1(b)", lineno, m);
        int tu = thS(m, A1 | A2, C1 | C2), ti = thS(m, A1 & A2, C1 & C2);
        int cross = eS(A1 & ~A2, C2 & ~C1) + eS(A2 & ~A1, C1 & ~C2);
        if (tu + ti != t1 + t2 + cross) report(V0, "2.1(c)", lineno, m);
        for (int c = 0; c < nc; c++) if (!(C1 >> c & 1)) {
            if (thS(m, A1, C1 | (1u << c)) != t1 + pc(cm[c] & A1) - 2) report(V0, "2.1(d)", lineno, m);
        }
    }
}

int main(int argc, char **argv) {
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-v")) verbose = 1;
        else if (!strcmp(argv[i], "-s") && i + 1 < argc) rng = strtoull(argv[++i], 0, 10) * 2654435761ull + 1;
    }
    char buf[4096];
    cand = malloc(sizeof(uint32_t) * (1u << 22));
    cbase = malloc(sizeof(int) * (1u << 22));
    lineno = 0;
    while (fgets(buf, sizeof buf, stdin)) {
        lineno++;
        char *p = buf; int nread;
        if (sscanf(p, "%d %d%n", &na, &nc, &nread) != 2) continue;
        p += nread;
        int ok = 1;
        for (int c = 0; c < nc; c++) { unsigned long x; if (sscanf(p, "%lu%n", &x, &nread) != 1) { ok = 0; break; } cm[c] = (uint32_t)x; p += nread; }
        if (!ok || na > 22 || nc > MAXC) { fprintf(stderr, "bad line %d\n", lineno); continue; }
        nblocks++;
        fullA = (na == 32) ? 0xffffffffu : ((1u << na) - 1); fullC = (1u << nc) - 1;
        int bad = (na != nc + 2);
        for (int a = 0; a < na; a++) dA[a] = 0;
        for (int c = 0; c < nc; c++) { if (pc(cm[c]) != 6 || (cm[c] & ~fullA)) bad = 1; for (int a = 0; a < na; a++) if (cm[c] >> a & 1) dA[a]++; }
        for (int a = 0; a < na; a++) { del[a] = 6 - dA[a]; if (dA[a] < 3) bad = 1; }
        if (bad) { nbad_struct++; fprintf(stderr, "line %d: violates (H1)/(H3)\n", lineno); continue; }
        /* sparsity and candidates in one pass over all T subset A */
        int sparse = 1; ncand = 0;
        for (uint32_t T = 0; T <= fullA; T++) {
            int ex3 = 0, ex2 = 0;
            for (int c = 0; c < nc; c++) { int e = pc(cm[c] & T); if (e > 3) ex3 += e - 3; if (e > 2) ex2 += e - 2; }
            int t = pc(T);
            if (t >= 3 && ex3 > 3 * t - 6) sparse = 0;
            int base = 4 - 4 * t + ex2;
            if (base >= -3) { cand[ncand] = T; cbase[ncand] = base; ncand++; }
            if (T == fullA) break;
        }
        if (!sparse) { nnonsparse++; fprintf(stderr, "line %d: not block-sparse\n", lineno); continue; }
        identities_check();
        enum_m(0, 4);
    }
    printf("blocks %ld (bad structure %ld, not sparse %ld)\n", nblocks, nbad_struct, nnonsparse);
    printf("multisets %ld (covering %ld)\n", nmult, ncover);
    printf("pairs of maximal sets: disjoint %ld, one vertex %ld, two vertices %ld, >=3 %ld\n", npair0, npair1, npair2, npair3);
    printf("multisets with a hub (two maximal sets sharing >= 3): %ld (covering %ld: case beta %ld, delta %ld)\n", nhubm, nhubm_cov, nhub_beta, nhub_delta);
    printf("petals under covering m: {y} %ld, {y,c} %ld, {y,y'} %ld, |P|>=3 kappa<=1 %ld, |P|>=3 kappa=2 %ld\n", npet[0], npet[1], npet[2], npet[3], npet[4]);
    printf("I_X empty: covering %ld, non-covering %ld; minimal subcovers %ld (hub-free %ld)\n", nIXempty_cov, nIXempty_noncov, nmincov, nmincov_nohub);
    printf("covering hub multisets with a singleton maximal set: %ld; most big maximal sets around one hub: %ld\n", nsing_cov, nrmax);
    printf("non-covering failures: with a petal {y}, w(y)=3: %ld; with a petal {y,y'}, w>=5: %ld; other: %ld\n", nfail_w3petal, nfail_yy, nfail_other);
    for (int i = 0; i < NV; i++) printf("%-60s %ld\n", vname[i], viol[i]);
    return 0;
}
