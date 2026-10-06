/* cuts.c -- small-cut profile of bipartite 4-regular graphs (graph6 on stdin, n <= 26, genbg order:
 * vertices 0..n1-1 are side P, the rest side Q; n1 = argv[1]).
 * Over every T containing vertex 0 with 2 <= |T| <= n-2 (complements give the rest):
 *   min2  : number of T with boundary 2
 *   bal4  : number of T with boundary 4, |T_P| = |T_Q|
 *   pass4 : number of T with boundary 4, sides differing by one, all 4 boundary edges on the larger side
 *           (one-passage cut), both T and V-T with >= 2 vertices
 *   ess   : min boundary over these T
 * Prints "<g6> ess=.. two=.. bal4=.. pass4=..". Gray-code enumeration.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint32_t mask;
static int n, n1;
static mask adj[32];
static inline int pc(mask x) { return __builtin_popcount(x); }
int main(int argc, char **argv) {
    n1 = atoi(argv[1]);
    static char line[4096];
    while (fgets(line, sizeof line, stdin)) {
        size_t L = strlen(line);
        while (L && (line[L - 1] == '\n' || line[L - 1] == '\r')) line[--L] = 0;
        if (!L) continue;
        n = line[0] - 63;
        memset(adj, 0, sizeof adj);
        int bit = 0, pos = 1;
        for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
            int ch = line[pos] - 63;
            if ((ch >> (5 - bit)) & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
            if (++bit == 6) { bit = 0; pos++; }
        }
        mask Pm = (1u << n1) - 1;
        /* enumerate subsets of vertices 1..n-1, T = {0} + subset */
        int m = n - 1;
        mask T = 1u; int e = 0, sz = 1, tp = 1, tq = 0; /* vertex 0 is in P */
        long two = 0, bal4 = 0, pass4 = 0; int ess = 99;
        for (uint32_t i = 1; i < (1u << m); i++) {
            int b = __builtin_ctz(i) + 1; /* vertex b toggles */
            if ((T >> b) & 1) { T &= ~(1u << b); e -= pc(adj[b] & T); sz--; if ((Pm >> b) & 1) tp--; else tq--; }
            else { e += pc(adj[b] & T); T |= 1u << b; sz++; if ((Pm >> b) & 1) tp++; else tq++; }
            if (sz < 2 || sz > n - 2) continue;
            int bd = 4 * sz - 2 * e;
            if (bd < ess) ess = bd;
            if (bd == 2) two++;
            if (bd == 4) {
                if (tp == tq) bal4++;
                else {
                    /* one-passage: larger side carries all 4 boundary edges */
                    int bq = 4 * tq - e, bp = 4 * tp - e; /* boundary edges at T_Q and at T_P */
                    if ((tp == tq + 1 && bq == 0) || (tq == tp + 1 && bp == 0)) pass4++;
                }
            }
        }
        printf("%s ess=%d two=%ld bal4=%ld pass4=%ld\n", line, ess, two, bal4, pass4);
    }
    return 0;
}
