/* sparse_gray.c -- referee's own exhaustive sparsity check for one graph6 graph (n <= 30).
 * Visits every vertex subset S in Gray-code order, keeping e(S) incrementally, and reports
 *   max over 3 <= |S| <= n-1 of e(S) - 3|S|   (sparse iff this is <= -6),
 * the number of S attaining it, the number of violating S (e(S) > 3|S| - 6), and one argmax.
 * Usage: ./sparse_gray < file.g6   (first line used)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

int main(void) {
    char s[512];
    if (!fgets(s, sizeof s, stdin)) return 1;
    int len = (int)strlen(s);
    while (len > 0 && (s[len - 1] == '\n' || s[len - 1] == '\r')) len--;
    int n = s[0] - 63;
    if (n > 30) { fprintf(stderr, "n too large\n"); return 1; }
    uint32_t adj[32] = {0};
    int bit = 0, m = 0;
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++) {
            int byte = 1 + bit / 6, off = 5 - bit % 6;
            if (byte < len && (((s[byte] - 63) >> off) & 1)) { adj[i] |= 1u << j; adj[j] |= 1u << i; m++; }
            bit++;
        }
    uint32_t S = 0;
    int e = 0, sz = 0;
    int best = -1000000;
    long long nbest = 0, nviol = 0;
    uint32_t argbest = 0;
    uint64_t total = 1ull << n;
    for (uint64_t g = 1; g < total; g++) {
        int v = __builtin_ctzll(g);           /* Gray code: flip bit v */
        uint32_t b = 1u << v;
        if (S & b) { S &= ~b; e -= __builtin_popcount(adj[v] & S); sz--; }
        else { e += __builtin_popcount(adj[v] & S); S |= b; sz++; }
        if (sz >= 3 && sz <= n - 1) {
            int val = e - 3 * sz;
            if (val > best) { best = val; nbest = 1; argbest = S; }
            else if (val == best) nbest++;
            if (val > -6) nviol++;
        }
    }
    printf("n=%d m=%d max(e(S)-3|S|) over 3<=|S|<=n-1 = %d (attained by %lld sets), violating sets = %lld\n",
           n, m, best, nbest, nviol);
    printf("one argmax set:");
    for (int v = 0; v < n; v++) if (argbest >> v & 1) printf(" %d", v);
    printf("\n%s\n", (best <= -6) ? "SPARSE" : "NOT SPARSE");
    return 0;
}
