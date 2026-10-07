/* Referee 2: exact subset enumeration for C1 instances (own code).
 *
 * Input on stdin:  s r m   then m lines "u w" (0 <= u < s <= w < s+r).
 * Vertices 0..s-1 are U, s..s+r-1 are W. n = s + r <= 40.
 *
 * Modes (argv[1]):
 *   ming            min over 2 <= |S| <= n-1 of g(S) = 6|S| - 2 e(S); count of S with g <= 8.
 *   petals u1       all Q with Q != V, |Q| >= 2, g(Q) = 10, kappa(Q) = 1, u1 in Q;
 *                   then pairwise closure under intersection and union, and chain test.
 *   viol y          every S subset of V - y with slack sigma < 0 in G - y, where
 *                   A = S cap W, C = S cap U, k = |A| - |C|, sigma = e(A, U - C) - 4k.
 *                   Prints the profile (k, sigma, D(C), g(V-S), kappa(V-S)) and each complement.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t u64;
static int s, r, n, m;
static u64 adj[64];
static int deg[64];
static u64 Umask, Wmask, Vmask;

static int pc(u64 x) { return __builtin_popcountll(x); }

static int g_of(u64 S) {
    int e = 0;
    u64 Su = S & Umask;
    while (Su) { int v = __builtin_ctzll(Su); e += pc(adj[v] & S); Su &= Su - 1; }
    return 6 * pc(S) - 2 * e;
}
static int kappa_of(u64 S) { return pc(S & Umask) - pc(S & Wmask); }

static int cmpu64(const void *a, const void *b) {
    u64 x = *(const u64 *)a, y = *(const u64 *)b;
    return (x > y) - (x < y);
}
static int in_list(u64 *L, long cnt, u64 q) {
    long lo = 0, hi = cnt - 1;
    while (lo <= hi) {
        long mid = (lo + hi) / 2;
        if (L[mid] == q) return 1;
        if (L[mid] < q) lo = mid + 1; else hi = mid - 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage\n"); return 2; }
    if (scanf("%d %d %d", &s, &r, &m) != 3) return 2;
    n = s + r;
    if (n > 40) { fprintf(stderr, "n too big\n"); return 2; }
    for (int i = 0; i < m; i++) {
        int u, w;
        if (scanf("%d %d", &u, &w) != 2) return 2;
        if (!(0 <= u && u < s && s <= w && w < n)) { fprintf(stderr, "bad edge\n"); return 2; }
        adj[u] |= 1ULL << w; adj[w] |= 1ULL << u;
    }
    Umask = (1ULL << s) - 1; Vmask = (1ULL << n) - 1; Wmask = Vmask ^ Umask;
    int DUg = 0;
    for (int v = 0; v < n; v++) deg[v] = pc(adj[v]);
    for (int u = 0; u < s; u++) DUg += 6 - deg[u];

    if (strcmp(argv[1], "ming") == 0) {
        /* Gray code over all subsets */
        u64 S = 0; int size = 0, e = 0;
        int best = 1 << 30; long cnt_le8 = 0; u64 bestS = 0;
        u64 total = 1ULL << n;
        for (u64 i = 1; i < total; i++) {
            int v = __builtin_ctzll(i);
            u64 b = 1ULL << v;
            int d = pc(adj[v] & S);
            if (S & b) { S ^= b; size--; e -= d; } else { S ^= b; size++; e += d; }
            if (size >= 2 && size <= n - 1) {
                int g = 6 * size - 2 * e;
                if (g < best) { best = g; bestS = S; }
                if (g <= 8) cnt_le8++;
            }
        }
        /* sanity: recompute */
        if (g_of(bestS) != best) { fprintf(stderr, "internal mismatch\n"); return 3; }
        printf("ming %d count_le8 %ld witness %llx\n", best, cnt_le8, (unsigned long long)bestS);
        return 0;
    }

    if (strcmp(argv[1], "petals") == 0) {
        int u1 = atoi(argv[2]);
        long cap = 1 << 20, cnt = 0;
        u64 *L = malloc(sizeof(u64) * cap);
        u64 S = 0; int size = 0, e = 0, su = 0;
        u64 total = 1ULL << n;
        for (u64 i = 1; i < total; i++) {
            int v = __builtin_ctzll(i);
            u64 b = 1ULL << v;
            int d = pc(adj[v] & S);
            int isU = (b & Umask) != 0;
            if (S & b) { S ^= b; size--; e -= d; su -= isU; } else { S ^= b; size++; e += d; su += isU; }
            if (size >= 2 && size <= n - 1 && ((S >> u1) & 1)) {
                int g = 6 * size - 2 * e;
                int kap = su - (size - su);
                if (g == 10 && kap == 1) {
                    if (cnt == cap) { cap *= 2; L = realloc(L, sizeof(u64) * cap); }
                    L[cnt++] = S;
                }
            }
        }
        qsort(L, cnt, sizeof(u64), cmpu64);
        long bad_cap = 0, bad_cup = 0, incomparable = 0, pairs = 0;
        int maxcheck = cnt <= 4000;
        if (maxcheck) {
            for (long a = 0; a < cnt; a++)
                for (long c = a + 1; c < cnt; c++) {
                    u64 I = L[a] & L[c], J = L[a] | L[c];
                    pairs++;
                    if (I != L[a] && I != L[c]) incomparable++;
                    if (!in_list(L, cnt, I)) bad_cap++;
                    if (!in_list(L, cnt, J)) bad_cup++;
                }
        }
        printf("petals %ld pairs %ld checked %d bad_cap %ld bad_cup %ld incomparable %ld\n",
               cnt, pairs, maxcheck, bad_cap, bad_cup, incomparable);
        for (long a = 0; a < cnt && a < 64; a++) printf("P %llx\n", (unsigned long long)L[a]);
        free(L);
        return 0;
    }

    if (strcmp(argv[1], "viol") == 0) {
        int y = atoi(argv[2]);
        /* enumerate subsets of V - y using a Gray code on n-1 positions */
        int pos[64], np = 0;
        for (int v = 0; v < n; v++) if (v != y) pos[np++] = v;
        u64 S = 0; int e = 0, sa = 0, sc = 0, sumdegA = 0, defC = 0, sumdeg = 0;
        int etot = 0; for (int v = 0; v < s; v++) etot += deg[v];
        long nviol = 0; int minsig = 1 << 30;
        long prof[8][16][4]; memset(prof, 0, sizeof prof); /* k 0..7, sigma+8, D(C) */
        long odd = 0;
        u64 total = 1ULL << np;
        for (u64 i = 1; i < total; i++) {
            int t = __builtin_ctzll(i);
            int v = pos[t];
            u64 b = 1ULL << v;
            int d = pc(adj[v] & S);
            int isU = (b & Umask) != 0;
            int sign = (S & b) ? -1 : 1;
            S ^= b; e += sign * d; sumdeg += sign * deg[v];
            if (isU) { sc += sign; defC += sign * (6 - deg[v]); }
            else { sa += sign; sumdegA += sign * deg[v]; }
            int k = sa - sc;
            int sigma = sumdegA - e - 4 * k;   /* e(A, U - C) - 4k, A avoids y */
            if (sigma < minsig) minsig = sigma;
            if (sigma < 0) {
                nviol++;
                u64 Q = Vmask & ~S;
                int gQ = 6 * (n - pc(S)) - 2 * (etot - sumdeg + e);
                int kQ = kappa_of(Q);
                if (gQ != g_of(Q)) { fprintf(stderr, "g mismatch\n"); return 3; }
                if (k >= 0 && k < 8 && sigma >= -8 && defC < 4) prof[k][sigma + 8][defC]++;
                else odd++;
                /* Lemma 3.1 identity check: g(Q) = 6 + 2DU + 2k + 2sigma - 2D(C) */
                int DU = DUg;
                if (gQ != 6 + 2 * DU + 2 * k + 2 * sigma - 2 * defC || kQ != k - 1) {
                    fprintf(stderr, "Lemma 3.1 mismatch\n"); return 3;
                }
                if (nviol <= 200000) printf("V %llx k %d sigma %d DC %d gQ %d kQ %d\n",
                        (unsigned long long)Q, k, sigma, defC, gQ, kQ);
            }
        }
        printf("viol y %d nviol %ld minsig %d odd %ld\n", y, nviol, minsig, odd);
        for (int k = 0; k < 8; k++) for (int sg = 0; sg < 16; sg++) for (int dc = 0; dc < 4; dc++)
            if (prof[k][sg][dc]) printf("profile k %d sigma %d DC %d count %ld\n", k, sg - 8, dc, prof[k][sg][dc]);
        return 0;
    }
    fprintf(stderr, "unknown mode\n");
    return 2;
}
