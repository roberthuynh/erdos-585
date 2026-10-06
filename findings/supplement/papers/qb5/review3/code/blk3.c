/* Referee-3 block checker, written from scratch.
 * Input lines:  nA nC mask_1 .. mask_nC  [c_0 .. c_{nA-1}]
 *   mask_j = neighbourhood of C-vertex j as a bitmask over A (bit i = A-vertex i).
 *   If a cut vector is given, only it is used; otherwise every admissible cut vector
 *   (max(0, delta-2) <= c_a <= min(3, delta), sum 7) is enumerated.
 * For every cut vector c and every multiset m <= c with |m| = 4:
 *   - computes overloaded sets T (theta(T) = m(T) - 4 + dem(A-T) >= 1) and I_X(m) = A - U{T};
 *   - M covering L_A: KL1 (I_X != empty), Prop 5.2 (no two disjoint under-supplied sets),
 *     Prop 5.3 (no two core-type under-supplied sets with intersection inside V(M)),
 *     Lemma 3.2 for overloaded |T|>=2;
 *   - exactly one uncovered L-vertex a: case (b) iff a in an overloaded T; Lemma 3.4 shape for every
 *     overloaded T containing a; Lemma 3.2 too.
 * Also: block validity, block sparsity (proper S, |S|>=3), Lemma 3.1 (i),(ii),(iv) for every T, and the
 * paper's "extendable covering multiset" count (m_a <= min(3,delta_a), sum 4, extendable, covering L_A).
 * Output per block one line; totals at the end.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXA 20
#define MAXC 18

static int nA, nC;
static unsigned cmask[MAXC];
static int dA[MAXA], delta[MAXA];
static int *kT, *CpT, *eppT, *popT, *deltaT;
static int *msum;
static unsigned Lmask;

static long long T_blocks, T_cvecs, T_cover, T_cover_fail, T_one, T_caseb, T_l34_viol, T_l32_viol, T_p52_viol, T_p53_viol, T_ext_cover, T_ext_fail, T_l31_viol, T_nonsparse, T_invalid;

static int pc(unsigned x) { return __builtin_popcount(x); }

static int check_sparse(void) {
    unsigned full = (1u << nA) - 1;
    for (unsigned S = 0; S < full; S++) {
        int s = pc(S);
        if (s < 4) continue;
        int sum = 0;
        for (int j = 0; j < nC; j++) { int x = pc(cmask[j] & S); if (x > 3) sum += x - 3; }
        if (sum > 3 * s - 6) return 0;
    }
    return 1;
}

static void precompute(void) {
    unsigned full = (1u << nA) - 1;
    for (unsigned T = 0; T <= full; T++) {
        unsigned A1 = full & ~T;
        int s = 0, cp = 0, epp = 0;
        for (int j = 0; j < nC; j++) {
            int x = pc(cmask[j] & A1); s += x > 4 ? 4 : x;
            int y = pc(cmask[j] & T);
            if (y >= 3) cp++; else epp += y;
        }
        kT[T] = 4 * pc(A1) - s;
        CpT[T] = cp; eppT[T] = epp; popT[T] = pc(T);
        int dsum = 0; for (int i = 0; i < nA; i++) if (T >> i & 1) dsum += delta[i];
        deltaT[T] = dsum;
    }
}

static int lemma31_check(void) {
    unsigned full = (1u << nA) - 1;
    int viol = 0;
    for (unsigned T = 0; T <= full; T++) {
        unsigned A1 = full & ~T;
        int kap = popT[T] - CpT[T], k = kT[T], epp = eppT[T];
        int eCpA1 = 0;
        for (int j = 0; j < nC; j++) if (pc(cmask[j] & T) >= 3) eCpA1 += pc(cmask[j] & A1);
        if (eCpA1 != 8 - 4 * kap - k) viol++;
        if (deltaT[T] != 2 * kap + 8 - k - epp) viol++;
        int sizeXp = popT[T] + CpT[T], sizeXpp = pc(A1) + (nC - CpT[T]);
        if (sizeXp >= 3 && T != full && kap + k > 2) viol++;
        if (sizeXpp >= 3 && A1 != full && epp < 3 * kap) viol++;
        if (sizeXpp >= 4 && A1 != full) {
            for (int x = 0; x < nA; x++) if (A1 >> x & 1) {
                int ex = 0;
                for (int j = 0; j < nC; j++) if (pc(cmask[j] & T) <= 2 && (cmask[j] >> x & 1)) ex++;
                if (ex < 3 + 3 * kap - epp) viol++;
            }
        }
    }
    return viol;
}

static int cvec[MAXA], mvec[MAXA];
static int blk_fail, blk_caseb, blk_cover;
static char failbuf[4096];

static void eval_m(void) {
    unsigned full = (1u << nA) - 1;
    msum[0] = 0;
    for (unsigned T = 1; T <= full; T++) { unsigned low = T & (~T + 1); int i = __builtin_ctz(low); msum[T] = msum[T ^ low] + mvec[i]; }
    unsigned VM = 0; for (int i = 0; i < nA; i++) if (mvec[i]) VM |= 1u << i;
    int unc = 0, a = -1;
    for (int i = 0; i < nA; i++) if ((Lmask >> i & 1) && mvec[i] == 0) { unc++; a = i; }
    if (unc >= 2) return;
    unsigned uni = 0;
    for (unsigned T = 1; T <= full; T++) {
        int theta = msum[T] - 4 + kT[T];
        if (theta >= 1) uni |= T;
    }
    unsigned I = full & ~uni;
    if (unc == 0) {
        T_cover++; blk_cover++;
        if (I == 0) {
            T_cover_fail++; blk_fail++;
            if (strlen(failbuf) < 3000) { char t[256]; int o = 0; o += sprintf(t + o, " [c="); for (int i = 0; i < nA; i++) o += sprintf(t + o, "%d", cvec[i]); o += sprintf(t + o, " m="); for (int i = 0; i < nA; i++) o += sprintf(t + o, "%d", mvec[i]); sprintf(t + o, "]"); strcat(failbuf, t); }
        }
        /* collect under-supplied sets (complements of overloaded T, T != empty) */
        static unsigned us[1 << 16]; int nus = 0;
        for (unsigned T = 1; T < full; T++) {
            int theta = msum[T] - 4 + kT[T];
            if (theta < 1) continue;
            unsigned A1 = full & ~T;
            if (nus < (1 << 16)) us[nus++] = A1;
            if (popT[T] >= 2) { /* Lemma 3.2 */
                int kap = popT[T] - CpT[T], k = kT[T], epp = eppT[T];
                int w = deltaT[T] - msum[T];
                int bad = 0;
                if (popT[T] < 3 || pc(A1) < 5) bad = 1;
                if (kap < -1 || kap > 2 - k || k < 1 || k > 3) bad = 1;
                if (msum[T] < theta + 2 + kap || msum[T] < 2) bad = 1;
                if (w > 2 * msum[T] - 3 * theta - epp) bad = 1;
                if (bad) T_l32_viol++;
            }
        }
        for (int x = 0; x < nus; x++) for (int y = x + 1; y < nus; y++) {
            if ((us[x] & us[y]) == 0) T_p52_viol++;
            if (pc(us[x]) >= 5 && pc(full & ~us[x]) >= 3 && pc(us[y]) >= 5 && pc(full & ~us[y]) >= 3) {
                if (((us[x] & us[y]) & ~VM) == 0) T_p53_viol++;
            }
        }
    } else {
        T_one++;
        if (!((I >> a) & 1)) { T_caseb++; blk_caseb++; }
        for (unsigned T = 1; T <= full; T++) {
            if (!((T >> a) & 1)) continue;
            int theta = msum[T] - 4 + kT[T];
            if (theta < 1) continue;
            int kap = popT[T] - CpT[T], k = kT[T], epp = eppT[T];
            int bad = 0;
            if (kap != 0 || (k != 1 && k != 2) || epp != 0 || theta != 1) bad = 1;
            int cTa = 0;
            for (int i = 0; i < nA; i++) if ((T >> i & 1) && i != a) {
                if (delta[i] - cvec[i] != 0) bad = 1;   /* def = 0 */
                if (cvec[i] != mvec[i]) bad = 1;        /* every cut edge in M */
                cTa += cvec[i];
            }
            if (cTa != msum[T] || cTa != 5 - k) bad = 1;
            if (bad) T_l34_viol++;
            /* Lemma 3.2 as well */
            int w = deltaT[T] - msum[T];
            int bad2 = 0;
            if (popT[T] < 3 || pc(full & ~T) < 5) bad2 = 1;
            if (kap < -1 || kap > 2 - k || k < 1 || k > 3) bad2 = 1;
            if (msum[T] < theta + 2 + kap) bad2 = 1;
            if (w > 2 * msum[T] - 3 * theta - epp) bad2 = 1;
            if (bad2) T_l32_viol++;
        }
    }
}

static void rec_m(int i, int left) {
    if (i == nA) { if (left == 0) eval_m(); return; }
    int hi = cvec[i] < left ? cvec[i] : left;
    for (int x = 0; x <= hi; x++) { mvec[i] = x; rec_m(i + 1, left - x); }
    mvec[i] = 0;
}

static int lo[MAXA], hi[MAXA];
static int ncv;
static void rec_c(int i, int left) {
    if (i == nA) { if (left == 0) { ncv++; T_cvecs++; rec_m(0, 4); } return; }
    int rest_lo = 0, rest_hi = 0;
    for (int j = i + 1; j < nA; j++) { rest_lo += lo[j]; rest_hi += hi[j]; }
    for (int x = lo[i]; x <= hi[i]; x++) {
        if (left - x < rest_lo || left - x > rest_hi) continue;
        cvec[i] = x; rec_c(i + 1, left - x);
    }
}

/* paper's extendable covering multisets (cut vector not fixed) */
static int ext_m[MAXA];
static void rec_ext(int i, int left) {
    if (i == nA) {
        if (left) return;
        int s = 0, smax = 0;
        for (int a = 0; a < nA; a++) {
            int l = delta[a] - 2; if (l < 0) l = 0; if (ext_m[a] > l) l = ext_m[a];
            s += l; smax += delta[a] < 3 ? delta[a] : 3;
        }
        if (s > 7 || smax < 7) return;
        for (int a = 0; a < nA; a++) if ((Lmask >> a & 1) && ext_m[a] == 0) return;
        T_ext_cover++;
        for (int a = 0; a < nA; a++) mvec[a] = ext_m[a];
        unsigned full = (1u << nA) - 1;
        msum[0] = 0;
        unsigned uni = 0;
        for (unsigned T = 1; T <= full; T++) { unsigned low = T & (~T + 1); int b = __builtin_ctz(low); msum[T] = msum[T ^ low] + mvec[b]; if (msum[T] - 4 + kT[T] >= 1) uni |= T; }
        if ((full & ~uni) == 0) T_ext_fail++;
        return;
    }
    int h = delta[i] < 3 ? delta[i] : 3; if (h > left) h = left;
    for (int x = 0; x <= h; x++) { ext_m[i] = x; rec_ext(i + 1, left - x); }
    ext_m[i] = 0;
}

int main(int argc, char **argv) {
    int skip_l31 = argc > 1 && !strcmp(argv[1], "nol31");
    kT = malloc(sizeof(int) << MAXA); CpT = malloc(sizeof(int) << MAXA); eppT = malloc(sizeof(int) << MAXA);
    popT = malloc(sizeof(int) << MAXA); deltaT = malloc(sizeof(int) << MAXA); msum = malloc(sizeof(int) << MAXA);
    char line[8192];
    int lineno = 0;
    while (fgets(line, sizeof line, stdin)) {
        lineno++;
        char *p = line; int nread;
        if (sscanf(p, "%d %d%n", &nA, &nC, &nread) != 2) continue;
        p += nread;
        for (int j = 0; j < nC; j++) { sscanf(p, "%u%n", &cmask[j], &nread); p += nread; }
        int given[MAXA], ng = 0, x;
        while (ng < nA && sscanf(p, "%d%n", &x, &nread) == 1) { given[ng++] = x; p += nread; }
        T_blocks++;
        int valid = (nA == nC + 2);
        for (int i = 0; i < nA; i++) dA[i] = 0;
        for (int j = 0; j < nC; j++) { if (pc(cmask[j]) != 6) valid = 0; for (int i = 0; i < nA; i++) if (cmask[j] >> i & 1) dA[i]++; }
        Lmask = 0; int sd = 0;
        for (int i = 0; i < nA; i++) { delta[i] = 6 - dA[i]; sd += delta[i]; if (dA[i] < 3) valid = 0; if (dA[i] == 3) Lmask |= 1u << i; }
        if (sd != 12) valid = 0;
        if (!valid) { T_invalid++; printf("line %d INVALID\n", lineno); continue; }
        int sparse = check_sparse();
        if (!sparse) T_nonsparse++;
        precompute();
        int l31 = (sparse && !skip_l31) ? lemma31_check() : 0;
        T_l31_viol += l31;
        blk_fail = blk_caseb = blk_cover = 0; failbuf[0] = 0;
        ncv = 0;
        if (ng == nA) {
            int s = 0; for (int i = 0; i < nA; i++) { cvec[i] = given[i]; s += given[i]; }
            if (s != 7) { printf("line %d bad cut vector\n", lineno); continue; }
            ncv = 1; T_cvecs++; rec_m(0, 4);
        } else {
            for (int i = 0; i < nA; i++) { lo[i] = delta[i] - 2 < 0 ? 0 : delta[i] - 2; hi[i] = delta[i] < 3 ? delta[i] : 3; }
            rec_c(0, 7);
        }
        long long before = T_ext_cover;
        rec_ext(0, 4);
        printf("line %d nA=%d sparse=%d L=%d cvecs=%d coverMs=%d KL1fail=%d caseb=%d extcover=%lld l31viol=%d%s\n", lineno, nA, sparse, pc(Lmask), ncv, blk_cover, blk_fail, blk_caseb, T_ext_cover - before, l31, failbuf);
    }
    printf("TOTAL blocks=%lld invalid=%lld nonsparse=%lld cvecs=%lld coverMs=%lld KL1fail=%lld oneUnc=%lld caseb=%lld L34viol=%lld L32viol=%lld P52viol=%lld P53viol=%lld L31viol=%lld extCover=%lld extFail=%lld\n",
           T_blocks, T_invalid, T_nonsparse, T_cvecs, T_cover, T_cover_fail, T_one, T_caseb, T_l34_viol, T_l32_viol, T_p52_viol, T_p53_viol, T_l31_viol, T_ext_cover, T_ext_fail);
    return 0;
}
