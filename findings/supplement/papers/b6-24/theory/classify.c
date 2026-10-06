/* classify.c -- for each graph6 line (bipartite E4 instance, n <= 26, classes by BFS 2-colouring,
 * P = class of vertex 0), enumerate ALL subsets S with 2 <= |S| <= n-1 (Gray code) and for every S
 * with s(S) = 4(|S_P|-|S_Q|) + e(S_Q, P-S) in {0,1} print nothing but tally the type
 *   (s, j, D(S_Q), D(S_P), g(S), g(V-S), dP(S), dQ(S)).
 * Also reports min g over 2 <= |S| <= n-1 (sparsity) and flags any s<=1 set not in the predicted list.
 * Predicted (NOTES §4), for sparse E4 (min g >= 10), 2 <= |S| <= n-1:
 *   s=0: (j=1, DQ=4, g=10, dQ=4, dP=2-DP)  or  (j=2, DQ=4, DP=0, g=12, dP=0, dQ=8)
 *   s=1: (j=0, DQ=4, g=10, dQ=1)  or (j=1, DQ=3, g=10, dQ=5, dP=2-DP) or (j=1, DQ=4, g=12, dQ=5, dP=3-DP)
 *        or (j=2, DQ=3, DP=0, g=12, dP=0, dQ=9) or (j=2, DQ=4, DP<=1, g=14, dP=1-DP, dQ=9)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint32_t mask;
static int n; static mask adj[32]; static int deg[32], col[32];
static int readg6(const char *s) {
    int k = 0; n = s[k++] - 63;
    memset(adj, 0, sizeof adj);
    int bit = 0, val = 0, bits = 0;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
        if (bits == 0) { val = s[k++] - 63; bits = 6; }
        bits--; if ((val >> bits) & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
    }
    (void)bit; return n;
}
static long tally[64][2]; /* not used */
int main(int argc, char **argv) {
    char line[256]; long ngraphs = 0, nbadpred = 0, nsparse = 0;
    long cnt[2][8]; memset(cnt, 0, sizeof cnt);
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, "\r\n ")] = 0; if (!line[0]) continue;
        readg6(line); ngraphs++;
        for (int v = 0; v < n; v++) { deg[v] = __builtin_popcount(adj[v]); col[v] = -1; }
        int q[32], h = 0, t = 0; col[0] = 0; q[t++] = 0;
        while (h < t) { int u = q[h++]; for (mask m = adj[u]; m; m &= m - 1) { int w = __builtin_ctz(m); if (col[w] < 0) { col[w] = 1 - col[u]; q[t++] = w; } } }
        mask Pm = 0, Qm = 0; for (int v = 0; v < n; v++) { if (col[v] == 0) Pm |= 1u << v; else Qm |= 1u << v; }
        /* Gray code */
        mask S = 0; int size = 0, eS = 0; int ming = 1 << 30;
        mask full = (n == 32) ? 0xffffffffu : ((1u << n) - 1);
        int DPtot = 0, DQtot = 0; for (int v = 0; v < n; v++) { if (Pm >> v & 1) DPtot += 6 - deg[v]; else DQtot += 6 - deg[v]; }
        int bad = 0;
        static int out_type[2][16];
        for (unsigned long i = 1; i < (1ul << n); i++) {
            int b = __builtin_ctzl(i);
            if (S >> b & 1) { S &= ~(1u << b); size--; eS -= __builtin_popcount(adj[b] & S); }
            else { eS += __builtin_popcount(adj[b] & S); S |= 1u << b; size++; }
            if (size < 2 || size > n - 1) continue;
            int g = 6 * size - 2 * eS; if (g < ming) ming = g;
            int sp = __builtin_popcount(S & Pm), sq = __builtin_popcount(S & Qm);
            /* dQ = e(S_Q, P - S) */
            int dQ = 0, dP = 0, DQ = 0, DP = 0;
            for (mask m = S & Qm; m; m &= m - 1) { int v = __builtin_ctz(m); dQ += __builtin_popcount(adj[v] & Pm & ~S); DQ += 6 - deg[v]; }
            int s = 4 * (sp - sq) + dQ;
            if (s > 1) continue;
            for (mask m = S & Pm; m; m &= m - 1) { int v = __builtin_ctz(m); dP += __builtin_popcount(adj[v] & Qm & ~S); DP += 6 - deg[v]; }
            int j = sq - sp;
            /* g(V-S) */
            int ec = 0; mask C = full & ~S; for (mask m = C; m; m &= m - 1) { int v = __builtin_ctz(m); ec += __builtin_popcount(adj[v] & C); } ec /= 2;
            int gc = 6 * (n - size) - 2 * ec;
            int ok = 0;
            if (s == 0) {
                if (j == 1 && DQ == 4 && g == 10 && dQ == 4 && dP == 2 - DP) ok = 1;
                if (j == 2 && DQ == 4 && DP == 0 && g == 12 && dP == 0 && dQ == 8) ok = 2;
            } else {
                if (j == 0 && DQ == 4 && g == 10 && dQ == 1) ok = 3;
                if (j == 1 && DQ == 3 && g == 10 && dQ == 5 && dP == 2 - DP) ok = 4;
                if (j == 1 && DQ == 4 && g == 12 && dQ == 5 && dP == 3 - DP) ok = 5;
                if (j == 2 && DQ == 3 && DP == 0 && g == 12 && dP == 0 && dQ == 9) ok = 6;
                if (j == 2 && DQ == 4 && DP <= 1 && g == 14 && dP == 1 - DP && dQ == 9) ok = 7;
            }
            cnt[s][ok]++;
            if (!ok) { bad++; if (bad <= 3) fprintf(stderr, "UNPREDICTED %s S=%x s=%d j=%d DQ=%d DP=%d g=%d gc=%d dP=%d dQ=%d\n", line, S, s, j, DQ, DP, g, gc, dP, dQ); }
        }
        if (ming >= 10) nsparse++;
        if (bad && ming >= 10) nbadpred++;
    }
    printf("graphs %ld sparse %ld sparse-with-unpredicted %ld\n", ngraphs, nsparse, nbadpred);
    for (int s = 0; s < 2; s++) { printf("s=%d types:", s); for (int k = 0; k < 8; k++) printf(" %d:%ld", k, cnt[s][k]); printf("\n"); }
    return 0;
}
