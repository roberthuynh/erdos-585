/* pairbf.c: exact pair finder by plain cycle enumeration (written for this review).
 *
 * Every simple cycle C1 of the graph is generated exactly once (DFS from its minimum vertex s
 * through vertices > s; keep the direction whose second vertex is smaller than its last).
 * For each C1, a backtracking search looks for a Hamilton cycle of the graph
 * (V(C1), E(G[V(C1)]) - E(C1)). A pair exists iff some C1 succeeds.
 * Usage: pairbf <edges file> [max_seconds]
 * Prints "PAIR" with both cycles (vertex sequences) or "NO PAIR" with the number of cycles. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 256
#define MAXE 1024
#define MAXD 16

static int n = 0, m = 0;
static int eu[MAXE], ev[MAXE];
static int deg[MAXN], nbr[MAXN][MAXD], nbe[MAXN][MAXD];
static int path[MAXN], epath[MAXN], plen;
static char onpath[MAXN], inC1v[MAXN], inC1e[MAXE];
static long long ncycles = 0;
static int found = 0, timed_out = 0;
static int hpath[MAXN], hlen, hstart, hsize;
static char hvis[MAXN];
static double tmax = 1e18;
static struct timespec t0;
static double elapsed(void) {
    struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t);
    return (t.tv_sec - t0.tv_sec) + 1e-9 * (t.tv_nsec - t0.tv_nsec);
}

static int ham_rec(int v) {
    if (hlen == hsize) {
        for (int i = 0; i < deg[v]; i++)
            if (nbr[v][i] == hstart && !inC1e[nbe[v][i]]) return 1;
        return 0;
    }
    for (int i = 0; i < deg[v]; i++) {
        int w = nbr[v][i], e = nbe[v][i];
        if (!inC1v[w] || hvis[w] || inC1e[e]) continue;
        hvis[w] = 1; hpath[hlen++] = w;
        if (ham_rec(w)) return 1;
        hlen--; hvis[w] = 0;
    }
    return 0;
}

static void check_partner(int closing_edge) {
    for (int i = 0; i < plen; i++) inC1v[path[i]] = 1;
    for (int i = 0; i < plen - 1; i++) inC1e[epath[i]] = 1;
    inC1e[closing_edge] = 1;
    int ok = 1;
    for (int i = 0; i < plen && ok; i++) {
        int v = path[i], c = 0;
        for (int j = 0; j < deg[v]; j++)
            if (inC1v[nbr[v][j]] && !inC1e[nbe[v][j]]) c++;
        if (c < 2) ok = 0;
    }
    if (ok) {
        hstart = path[0]; hsize = plen; hlen = 1; hpath[0] = hstart;
        memset(hvis, 0, sizeof(hvis)); hvis[hstart] = 1;
        if (ham_rec(hstart)) {
            found = 1;
            printf("PAIR on %d vertices\nC1:", plen);
            for (int i = 0; i < plen; i++) printf(" %d", path[i]);
            printf("\nC2:");
            for (int i = 0; i < hsize; i++) printf(" %d", hpath[i]);
            printf("\n");
        }
    }
    for (int i = 0; i < plen; i++) inC1v[path[i]] = 0;
    for (int i = 0; i < plen - 1; i++) inC1e[epath[i]] = 0;
    inC1e[closing_edge] = 0;
}

static long long nodes = 0;

static void dfs(int s, int v) {
    if ((++nodes & 0xFFFFF) == 0 && elapsed() > tmax) { timed_out = 1; return; }
    for (int i = 0; i < deg[v] && !found && !timed_out; i++) {
        int w = nbr[v][i], e = nbe[v][i];
        if (w == s) {
            if (plen >= 3 && path[1] < path[plen - 1]) {
                ncycles++;
                if ((ncycles & 0xFFFFF) == 0 &&
                    elapsed() > tmax) { timed_out = 1; return; }
                check_partner(e);
            }
        } else if (w > s && !onpath[w]) {
            onpath[w] = 1; path[plen] = w; epath[plen - 1] = e; plen++;
            dfs(s, w);
            plen--; onpath[w] = 0;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: pairbf edges [max_seconds]\n"); return 2; }
    if (argc > 2) tmax = atof(argv[2]);
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror("open"); return 2; }
    char line[256];
    while (fgets(line, sizeof line, f)) {
        if (line[0] == '#' || line[0] == '\n') continue;
        int a, b;
        if (sscanf(line, "%d %d", &a, &b) != 2) continue;
        if (a == b || m >= MAXE || a >= MAXN || b >= MAXN) { fprintf(stderr, "bad edge\n"); return 2; }
        eu[m] = a; ev[m] = b;
        if (deg[a] >= MAXD || deg[b] >= MAXD) { fprintf(stderr, "degree too large\n"); return 2; }
        nbr[a][deg[a]] = b; nbe[a][deg[a]++] = m;
        nbr[b][deg[b]] = a; nbe[b][deg[b]++] = m;
        m++;
        if (a + 1 > n) n = a + 1;
        if (b + 1 > n) n = b + 1;
    }
    fclose(f);
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int s = 0; s < n && !found && !timed_out; s++) {
        plen = 1; path[0] = s; onpath[s] = 1;
        dfs(s, s);
        onpath[s] = 0;
    }
    if (found) printf("cycles enumerated before the pair: %lld\n", ncycles);
    else if (timed_out) printf("TIMEOUT after %lld cycles (incomplete)\n", ncycles);
    else printf("NO PAIR (complete), %lld cycles enumerated\n", ncycles);
    return 0;
}
