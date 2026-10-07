/* e5check.c (lane qb5, round 2): independent decider for E5 pair certificates.
 * Build: /usr/bin/clang -O3 -o e5check e5check.c
 * Reads graph6 lines (n <= 32) on stdin. For each graph prints:
 *   bipartite, balanced, maxdeg, mindeg, e - (3n - 5), sparse (every S with 3 <= |S| <= n-1 spans at most
 *   3|S| - 6 edges; Gray-code enumeration of all subsets), has4factor (max flow), number of pairs
 *   (p, q) on opposite sides with a 4-factor in G - p - q, and the list of those pairs if at most 12
 *   (all of them with any argument, e.g. e5check all).
 * Shares no code with e5pairs.py / generic_inst.py (networkx) or pairsearch.c.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint32_t u32;
static int n; static u32 adj[32];

static int parse(const char *s){
    n = s[0] - 63; if (n < 1 || n > 32) return 0;
    memset(adj, 0, sizeof adj);
    int k = 0, len = strlen(s), bitpos = 0;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
        int byte = 1 + bitpos / 6, off = 5 - bitpos % 6; bitpos++;
        if (byte >= len) return 0;
        if (((s[byte] - 63) >> off) & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
        k++;
    }
    return 1;
}

static int capm[34][34];
static int flow4(u32 keep, const int *col, int *need){
    int N = n + 2, s = n, t = n + 1, np = 0, nq = 0;
    memset(capm, 0, sizeof capm);
    for (int v = 0; v < n; v++) if (keep >> v & 1) {
        if (col[v] == 0) { np++; capm[s][v] = 4; for (int u = 0; u < n; u++) if ((keep >> u & 1) && (adj[v] >> u & 1)) capm[v][u] = 1; }
        else { nq++; capm[v][t] = 4; }
    }
    *need = 4 * np; if (np != nq) return -1;
    int fl = 0, pr[34], q[34];
    for (;;) {
        for (int i = 0; i < N; i++) pr[i] = -1;
        int h = 0, tl = 0; q[tl++] = s; pr[s] = s;
        while (h < tl && pr[t] < 0) { int v = q[h++]; for (int u = 0; u < N; u++) if (capm[v][u] > 0 && pr[u] < 0) { pr[u] = v; q[tl++] = u; } }
        if (pr[t] < 0) break;
        for (int v = t; v != s; v = pr[v]) { capm[pr[v]][v]--; capm[v][pr[v]]++; }
        fl++;
    }
    return fl;
}

static int sparse(void){
    u32 S = 0, full = (n == 32) ? 0xffffffffu : ((1u << n) - 1); int e = 0, sz = 0;
    for (uint64_t i = 1; i < (1ull << n); i++) {
        int v = __builtin_ctzll(i); u32 b = 1u << v;
        if (S & b) { S ^= b; sz--; e -= __builtin_popcount(adj[v] & S); }
        else { e += __builtin_popcount(adj[v] & S); S ^= b; sz++; }
        if (sz >= 3 && S != full && e > 3 * sz - 6) return 0;
    }
    return 1;
}

int main(int argc, char **argv){
    int listall = argc > 1; char line[256];
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, " \r\n")] = 0;
        if (!line[0] || !parse(line)) continue;
        int col[32]; for (int i = 0; i < n; i++) col[i] = -1;
        int bip = 1;
        for (int r = 0; r < n; r++) if (col[r] < 0) {
            col[r] = 0; int st[32], sp = 0; st[sp++] = r;
            while (sp) { int v = st[--sp]; for (int u = 0; u < n; u++) if (adj[v] >> u & 1) { if (col[u] < 0) { col[u] = 1 - col[v]; st[sp++] = u; } else if (col[u] == col[v]) bip = 0; } }
        }
        int n0 = 0, mx = 0, mn = 99, e = 0;
        for (int v = 0; v < n; v++) { int d = __builtin_popcount(adj[v]); e += d; if (d > mx) mx = d; if (d < mn) mn = d; if (col[v] == 0) n0++; }
        e /= 2;
        int sp = sparse(), need;
        u32 full = (n == 32) ? 0xffffffffu : ((1u << n) - 1);
        int f = flow4(full, col, &need);
        int good = 0; char lst[4096]; lst[0] = 0;
        for (int p = 0; p < n; p++) if (col[p] == 0) for (int q = 0; q < n; q++) if (col[q] == 1) {
            u32 keep = full & ~(1u << p) & ~(1u << q);
            int fl = flow4(keep, col, &need);
            if (fl == need) { good++; if (strlen(lst) < 4000) { char b[24]; sprintf(b, " %d-%d", p, q); strcat(lst, b); } }
        }
        printf("%s bip=%d balanced=%d maxdeg=%d mindeg=%d excess=%d sparse=%d has4factor=%d goodpairs=%d%s%s\n",
               line, bip, n0 * 2 == n, mx, mn, e - (3 * n - 5), sp, f == need, good, (good <= 12 || listall) ? " :" : "", (good <= 12 || listall) ? lst : "");
        fflush(stdout);
    }
    return 0;
}
