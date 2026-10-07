/* rvsave.c -- second pass: geng with rvprune, plus a final-level filter that keeps only graphs G
 * admitting at least one extension neighbourhood (t = EF - e(G) in [MINDF, 6], #deg(t-1) <= t,
 * #deg in [t,5] >= t - #deg(t-1)); every kept G is written as graph6. Used to compare with the
 * lane's level-12 set of the n = 13 tree. */
#include "rvprune.c"
static long long sv_dprej = 0, sv_out = 0;
static int sv_EF = 35, sv_MINDF = 4, sv_ready = 0;
int rvprune2(graph *g, int n, int maxn) {
    if (!sv_ready) {
        const char *s;
        if ((s = getenv("RV_EXT_EF"))) sv_EF = atoi(s);
        if ((s = getenv("RV_EXT_MINDF"))) sv_MINDF = atoi(s);
        sv_ready = 1;
    }
    if (n == maxn) {
        int deg[32], e2 = 0;
        for (int i = 0; i < n; i++) {
            set *gi = GRAPHROW(g, i, 1);
            int d = 0;
            for (int j = 0; j < n; j++) if (ISELEMENT(gi, j)) d++;
            deg[i] = d;
            e2 += d;
        }
        int t = sv_EF - e2 / 2, f = 0, a = 0, low = 0;
        for (int i = 0; i < n; i++) {
            if (deg[i] < t - 1) low = 1;
            else if (deg[i] == t - 1) f++;
            else if (deg[i] <= 5) a++;
        }
        if (t < sv_MINDF || t > 6 || low || f > t || a < t - f) { sv_dprej++; return 1; }
    }
    return rvprune(g, n, maxn);
}
void rvsaveout(FILE *f, graph *g, int n) {
    rvset adj[32];
    for (int i = 0; i < n; i++) {
        rvset a = 0;
        set *gi = GRAPHROW(g, i, 1);
        for (int j = 0; j < n; j++) if (ISELEMENT(gi, j)) a |= 1u << j;
        adj[i] = a;
    }
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
    fprintf(f, "%s\n", buf);
    sv_out++;
}
void rvsavesum(nauty_counter nout, double cpu) {
    rvsummary(nout, cpu);
    fprintf(stderr, "rvsave: dp_rej=%lld G_out=%lld\n", sv_dprej, sv_out);
}
