/* rvpairtest.c -- stdin harness for the reviewer's pair tests.
 * Usage: rvpairtest [v1|v2|v3] [g6|el] [sparse SP SPMIN] [toel]
 *   input  : "n m u1 v1 ... um vm" lines (el, default) or graph6 lines (g6)
 *   output : "1"/"0" per graph (has a pair); with sparse: second column, 1 iff every proper S with
 *            |S| >= SPMIN has e(S) <= 3|S| - SP; with toel: just print the graph as an edge list. */
#include "rvpair.h"
#include "rvpair2.h"
#include "rvpair3.h"
#include <string.h>

static int read_g6(rvset *adj, int *np) {
    char line[512];
    if (!fgets(line, sizeof line, stdin)) return 0;
    int len = (int)strcspn(line, "\r\n");
    line[len] = 0;
    if (len == 0) return -1;
    int n = line[0] - 63, pos = 1, bit = 0, cur = 0;
    if (n < 0 || n > 16) { fprintf(stderr, "bad g6\n"); exit(2); }
    for (int i = 0; i < n; i++) adj[i] = 0;
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++) {
            if (bit == 0) { cur = line[pos++] - 63; bit = 6; }
            bit--;
            if ((cur >> bit) & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
        }
    *np = n;
    return 1;
}

int main(int argc, char **argv) {
    int ver = 1, g6 = 0, dosp = 0, toel = 0, SP = 0, SPMIN = 0;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "v1")) ver = 1;
        else if (!strcmp(argv[i], "v2")) ver = 2;
        else if (!strcmp(argv[i], "v3")) ver = 3;
        else if (!strcmp(argv[i], "g6")) g6 = 1;
        else if (!strcmp(argv[i], "el")) g6 = 0;
        else if (!strcmp(argv[i], "toel")) toel = 1;
        else if (!strcmp(argv[i], "tog6")) toel = 2;
        else if (!strcmp(argv[i], "sparse") && i + 2 < argc) { dosp = 1; SP = atoi(argv[i + 1]); SPMIN = atoi(argv[i + 2]); i += 2; }
        else { fprintf(stderr, "bad arg %s\n", argv[i]); return 2; }
    }
    for (;;) {
        rvset adj[32] = {0};
        int n;
        if (g6) {
            int r = read_g6(adj, &n);
            if (r == 0) break;
            if (r < 0) continue;
        } else {
            int m;
            if (scanf("%d %d", &n, &m) != 2) break;
            for (int i = 0; i < m; i++) {
                int a, b;
                if (scanf("%d %d", &a, &b) != 2) return 1;
                adj[a] |= 1u << b;
                adj[b] |= 1u << a;
            }
        }
        if (toel == 2) {
            char buf[128];
            int pos = 0, bit = 0, cur = 0;
            buf[pos++] = (char)(63 + n);
            for (int j = 1; j < n; j++)
                for (int i = 0; i < j; i++) {
                    cur = (cur << 1) | ((adj[i] >> j) & 1u);
                    if (++bit == 6) { buf[pos++] = (char)(63 + cur); bit = 0; cur = 0; }
                }
            if (bit) { cur <<= (6 - bit); buf[pos++] = (char)(63 + cur); }
            buf[pos] = 0;
            printf("%s\n", buf);
            continue;
        }
        if (toel) {
            int m = 0;
            for (int i = 0; i < n; i++) m += __builtin_popcount(adj[i]);
            printf("%d %d", n, m / 2);
            for (int i = 0; i < n; i++)
                for (int j = i + 1; j < n; j++)
                    if ((adj[i] >> j) & 1u) printf(" %d %d", i, j);
            printf("\n");
            continue;
        }
        int p = ver == 3 ? rv3_has_pair(n, adj) : ver == 2 ? rv2_has_pair(n, adj) : rv_has_pair(n, adj);
        if (!dosp) { printf("%d\n", p); continue; }
        int ok = 1;
        rvset full = (1u << n) - 1;
        for (rvset S = 1; S < full && ok; S++) {
            int sz = __builtin_popcount(S);
            if (sz < SPMIN) continue;
            int e2 = 0;
            rvset t = S;
            while (t) { int v = __builtin_ctz(t); t &= t - 1; e2 += __builtin_popcount(adj[v] & S); }
            if (e2 / 2 > 3 * sz - SP) ok = 0;
        }
        printf("%d %d\n", p, ok);
    }
    fprintf(stderr, "pairs_verified=%lld\n", rv_npairs_verified);
    return 0;
}
