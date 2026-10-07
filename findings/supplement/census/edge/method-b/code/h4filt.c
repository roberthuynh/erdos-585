/* h4filt.c -- method B stand-alone decider (wave8/exb).

   Reads graph6 lines on stdin.  For each graph: decode (own decoder),
   check it is bipartite (BFS 2-colouring), record edges, minimum and
   maximum degree and the sizes of the colour classes (connected graphs;
   a disconnected graph is tallied as such), and decide with h4_any whether
   it has a nonempty 4-regular subgraph.  Graphs WITHOUT one are copied to
   stdout unchanged.  A tally goes to stderr at the end:

     >T total N with_H A without_H B nonbip C
     >S e=.. sides=a+b mindeg=.. maxdeg=.. conn=1 count=.. without_H=..

   Options: -q  no per-class tally lines (totals only).
            -a  copy every graph to stdout with a verdict column
                ("H" or "0"), for cross-checking against other deciders. */

#include "h4.h"

#define MAXLINE 256

static int decode_g6(const char *s, int *pn, h4set *adj)
{
    int n, i, j, k = 0, bitpos = 0, len;
    const char *p;
    while (*s == ' ') ++s;
    if (s[0] == '>' || s[0] == ':' || s[0] == '&') return -1;
    n = (unsigned char)s[0] - 63;
    if (n < 0 || n > 62 || n > H4MAXN) return -1;
    len = (int)strlen(s);
    while (len > 0 && (s[len - 1] == '\n' || s[len - 1] == '\r')) --len;
    if (len != 1 + (n * (n - 1) / 2 + 5) / 6) return -1;
    for (i = 0; i < n; ++i) adj[i] = 0;
    p = s + 1;
    for (j = 1; j < n; ++j)
        for (i = 0; i < j; ++i) {
            int byte = ((unsigned char)p[k / 6]) - 63;
            int bit = (byte >> (5 - (k % 6))) & 1;
            (void)bitpos;
            if (byte < 0 || byte > 63) return -1;
            if (bit) {
                adj[i] |= H4BIT(j);
                adj[j] |= H4BIT(i);
            }
            ++k;
        }
    *pn = n;
    return 0;
}

/* 2-colour; returns number of components, or -1 if not bipartite.
   side0/side1 = colour class sizes summed over components with the colour
   of each component's lowest vertex fixed to 0 (only meaningful when
   connected). */
static int bicolour(const h4set *adj, int n, int *c0, int *c1)
{
    int col[H4MAXN], q[H4MAXN], i, head, tail, comps = 0;
    for (i = 0; i < n; ++i) col[i] = -1;
    *c0 = *c1 = 0;
    for (i = 0; i < n; ++i) {
        if (col[i] >= 0) continue;
        ++comps;
        col[i] = 0;
        head = tail = 0;
        q[tail++] = i;
        while (head < tail) {
            int u = q[head++];
            h4set a = adj[u];
            if (col[u] == 0) ++*c0; else ++*c1;
            while (a) {
                int w = H4LOW(a);
                a &= a - 1;
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    q[tail++] = w;
                } else if (col[w] == col[u])
                    return -1;
            }
        }
    }
    return comps;
}

typedef struct {
    int e, a, b, dmin, dmax, conn;
    unsigned long long count, without;
} tallyrow;

#define MAXROWS 4096
static tallyrow rows[MAXROWS];
static int nrows = 0;

static void tally(int e, int a, int b, int dmin, int dmax, int conn, int has)
{
    int i;
    for (i = 0; i < nrows; ++i)
        if (rows[i].e == e && rows[i].a == a && rows[i].b == b &&
            rows[i].dmin == dmin && rows[i].dmax == dmax && rows[i].conn == conn)
            break;
    if (i == nrows) {
        if (nrows == MAXROWS) {
            fprintf(stderr, "h4filt: too many tally rows\n");
            exit(2);
        }
        rows[i].e = e; rows[i].a = a; rows[i].b = b;
        rows[i].dmin = dmin; rows[i].dmax = dmax; rows[i].conn = conn;
        rows[i].count = rows[i].without = 0;
        ++nrows;
    }
    ++rows[i].count;
    if (!has) ++rows[i].without;
}

int main(int argc, char **argv)
{
    char line[MAXLINE];
    h4set adj[H4MAXN];
    unsigned long long total = 0, withH = 0, withoutH = 0, nonbip = 0;
    int quiet = 0, all = 0, i;

    for (i = 1; i < argc; ++i) {
        if (strcmp(argv[i], "-q") == 0) quiet = 1;
        else if (strcmp(argv[i], "-a") == 0) all = 1;
        else {
            fprintf(stderr, "usage: h4filt [-q] [-a] < in.g6 > out.g6\n");
            return 2;
        }
    }
    while (fgets(line, sizeof line, stdin)) {
        int n, u, e = 0, dmin = 99, dmax = 0, c0, c1, comps, has;
        if (line[0] == '\n' || line[0] == '\0') continue;
        if (decode_g6(line, &n, adj) != 0) {
            fprintf(stderr, "h4filt: bad graph6 line: %s", line);
            return 3;
        }
        ++total;
        for (u = 0; u < n; ++u) {
            int d = H4POP(adj[u]);
            e += d;
            if (d < dmin) dmin = d;
            if (d > dmax) dmax = d;
        }
        e /= 2;
        if (dmax > 7) {
            fprintf(stderr, "h4filt: max degree %d > 7 not supported\n", dmax);
            return 3;
        }
        comps = bicolour(adj, n, &c0, &c1);
        if (comps < 0) ++nonbip;
        has = h4_any(adj, n, NULL);
        if (has) ++withH; else ++withoutH;
        if (comps < 0)
            tally(e, -1, -1, dmin, dmax, 0, has);
        else if (comps == 1)
            tally(e, c0 < c1 ? c0 : c1, c0 < c1 ? c1 : c0, dmin, dmax, 1, has);
        else
            tally(e, -1, -1, dmin, dmax, comps, has);
        if (all) {
            size_t L = strlen(line);
            while (L > 0 && (line[L - 1] == '\n' || line[L - 1] == '\r')) line[--L] = '\0';
            printf("%s %s\n", line, has ? "H" : "0");
        } else if (!has)
            fputs(line, stdout);
    }
    fprintf(stderr, ">T total %llu with_H %llu without_H %llu nonbip %llu nodes %llu\n",
            total, withH, withoutH, nonbip, h4_nodes);
    if (!quiet)
        for (i = 0; i < nrows; ++i)
            fprintf(stderr, ">S e=%d sides=%d+%d mindeg=%d maxdeg=%d conn=%d count=%llu without_H=%llu\n",
                    rows[i].e, rows[i].a, rows[i].b, rows[i].dmin, rows[i].dmax,
                    rows[i].conn, rows[i].count, rows[i].without);
    return 0;
}
