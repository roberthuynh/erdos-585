/* blocksig.c: C port of pairdp.Block.enumerate_local + signature (same definitions, same
 * edge orders), for speed. Usage: blocksig <edges file> <first vertex> <block size>
 * Output: "COUNT <number of local colourings>", "LOCAL <global edge indices of local edges>",
 * "BOUNDARY <global edge indices>", then one line per distinct signature:
 * "SIG <bcol csv>|<red pairs a-b,...>|<rc>|<blue pairs>|<bc>|<witness colours of local edges>" */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 512
#define MAXE 2048
#define MAXD 16
#define MAXL 128
#define MAXPAT 128

static int n = 0, m = 0;
static int eu[MAXE], ev[MAXE];
static int adeg[MAXN], anb[MAXN][MAXD], aed[MAXN][MAXD];
static int bs, bsz;                /* block = [bs, bs + bsz) */
static int nloc, loc[MAXL];        /* local edges (global indices), Python order */
static int lidx[MAXE];
static int isbd[MAXL], nbd, bd[MAXL];
static int order[MAXL], nord;
static int vinc[MAXN][MAXD], vdeg[MAXN];  /* local edge indices at each block vertex */
static int col[MAXL];
static long long count = 0;
static int npat[MAXD + 1];
static signed char pat[MAXD + 1][MAXPAT][MAXD];

static int inblk(int v) { return v >= bs && v < bs + bsz; }

static void make_patterns(int k) {
    int c = 0;
    for (int i = 0; i < k; i++) pat[k][c][i] = 0;
    c++;
    for (int r1 = 0; r1 < k; r1++) for (int r2 = r1 + 1; r2 < k; r2++) {
        int rest[MAXD], nr = 0;
        for (int i = 0; i < k; i++) if (i != r1 && i != r2) rest[nr++] = i;
        for (int b1 = 0; b1 < nr; b1++) for (int b2 = b1 + 1; b2 < nr; b2++) {
            for (int i = 0; i < k; i++) pat[k][c][i] = 0;
            pat[k][c][r1] = 1; pat[k][c][r2] = 1;
            pat[k][c][rest[b1]] = 2; pat[k][c][rest[b2]] = 2;
            c++;
        }
    }
    npat[k] = c;
}

/* ---- signature hash set ---- */
#define HSIZE 65536
static char *hkey[HSIZE];
static char *hwit[HSIZE];
static int nsig = 0;

static unsigned long long fnv(const char *s) {
    unsigned long long h = 1469598103934665603ULL;
    while (*s) { h ^= (unsigned char)*s++; h *= 1099511628211ULL; }
    return h;
}

static int cmpint2(const void *a, const void *b) {
    const int *x = a, *y = b;
    if (x[0] != y[0]) return x[0] - y[0];
    return x[1] - y[1];
}

static void signature(void) {
    char key[4096], wit[1024];
    int p = 0;
    for (int i = 0; i < nbd; i++) p += sprintf(key + p, i ? ",%d" : "%d", col[lidx[bd[i]]]);
    for (int X = 1; X <= 2; X++) {
        int pairs[MAXL][2], np = 0;
        static int reached[MAXN], vis_t[MAXE];
        for (int i = 0; i < bsz; i++) reached[bs + i] = 0;
        for (int i = 0; i < nbd; i++) vis_t[bd[i]] = 0;
        for (int i = 0; i < nbd; i++) {
            int e0 = bd[i];
            if (col[lidx[e0]] != X || vis_t[e0]) continue;
            vis_t[e0] = 1;
            int cur = inblk(eu[e0]) ? eu[e0] : ev[e0];
            int came = e0;
            for (;;) {
                reached[cur] = 1;
                int nxt = -1, cnt = 0;
                for (int j = 0; j < vdeg[cur]; j++) {
                    int le = vinc[cur][j], ge = loc[le];
                    if (col[le] == X && ge != came) { nxt = ge; cnt++; }
                }
                if (cnt != 1) { fprintf(stderr, "walk error\n"); exit(3); }
                if (isbd[lidx[nxt]]) {
                    vis_t[nxt] = 1;
                    pairs[np][0] = e0 < nxt ? e0 : nxt;
                    pairs[np][1] = e0 < nxt ? nxt : e0;
                    np++;
                    break;
                }
                came = nxt;
                cur = (eu[nxt] == cur) ? ev[nxt] : eu[nxt];
            }
        }
        qsort(pairs, np, sizeof(pairs[0]), cmpint2);
        /* internal closed cycles: vertices with X-degree > 0 not reached */
        static int seen[MAXN];
        for (int i = 0; i < bsz; i++) seen[bs + i] = 0;
        int ncyc = 0;
        for (int i = 0; i < bsz; i++) {
            int v = bs + i, xd = 0;
            for (int j = 0; j < vdeg[v]; j++) if (col[vinc[v][j]] == X) xd++;
            if (xd == 0 || reached[v] || seen[v]) continue;
            ncyc++;
            int stack[MAXN], sp = 0;
            stack[sp++] = v; seen[v] = 1;
            while (sp) {
                int x = stack[--sp];
                for (int j = 0; j < vdeg[x]; j++) {
                    int le = vinc[x][j], ge = loc[le];
                    if (col[le] != X || isbd[le]) continue;
                    int y = (eu[ge] == x) ? ev[ge] : eu[ge];
                    if (!seen[y]) { seen[y] = 1; stack[sp++] = y; }
                }
            }
        }
        if (ncyc > 2) ncyc = 2;
        p += sprintf(key + p, "|");
        for (int i = 0; i < np; i++) p += sprintf(key + p, i ? ",%d-%d" : "%d-%d", pairs[i][0], pairs[i][1]);
        p += sprintf(key + p, "|%d", ncyc);
    }
    unsigned long long h = fnv(key);
    int slot = (int)(h & (HSIZE - 1));
    while (hkey[slot]) {
        if (strcmp(hkey[slot], key) == 0) return;
        slot = (slot + 1) & (HSIZE - 1);
    }
    for (int i = 0; i < nloc; i++) wit[i] = (char)('0' + col[i]);
    wit[nloc] = 0;
    hkey[slot] = strdup(key);
    hwit[slot] = strdup(wit);
    nsig++;
}

static void rec(int i) {
    if (i == nord) { count++; signature(); return; }
    int v = order[i], k = vdeg[v];
    for (int q = 0; q < npat[k]; q++) {
        int ok = 1;
        for (int j = 0; j < k; j++) {
            int c = col[vinc[v][j]];
            if (c != -1 && c != pat[k][q][j]) { ok = 0; break; }
        }
        if (!ok) continue;
        int newly[MAXD], nn = 0;
        for (int j = 0; j < k; j++)
            if (col[vinc[v][j]] == -1) { col[vinc[v][j]] = pat[k][q][j]; newly[nn++] = vinc[v][j]; }
        rec(i + 1);
        for (int j = 0; j < nn; j++) col[newly[j]] = -1;
    }
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage\n"); return 2; }
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror("open"); return 2; }
    bs = atoi(argv[2]); bsz = atoi(argv[3]);
    char line[256];
    while (fgets(line, sizeof line, f)) {
        if (line[0] == '#' || line[0] == '\n') continue;
        int a, b;
        if (sscanf(line, "%d %d", &a, &b) != 2) continue;
        eu[m] = a; ev[m] = b;
        anb[a][adeg[a]] = b; aed[a][adeg[a]++] = m;
        anb[b][adeg[b]] = a; aed[b][adeg[b]++] = m;
        m++;
        if (a + 1 > n) n = a + 1;
        if (b + 1 > n) n = b + 1;
    }
    fclose(f);
    for (int k = 0; k <= MAXD; k++) if (k * (k - 1) / 2 * (k - 2) * (k - 3) / 4 + 1 < MAXPAT) make_patterns(k);
    /* local edges in Python order: for v in verts ascending, for (w, ei) in adj[v] */
    static int seenE[MAXE];
    for (int v = bs; v < bs + bsz; v++)
        for (int j = 0; j < adeg[v]; j++) {
            int ei = aed[v][j];
            if (!seenE[ei]) { seenE[ei] = 1; lidx[ei] = nloc; loc[nloc++] = ei; }
        }
    for (int i = 0; i < nloc; i++) {
        int ei = loc[i];
        isbd[i] = !(inblk(eu[ei]) && inblk(ev[ei]));
        if (isbd[i]) bd[nbd++] = ei;
    }
    for (int v = bs; v < bs + bsz; v++) {
        vdeg[v] = adeg[v];
        for (int j = 0; j < adeg[v]; j++) vinc[v][j] = lidx[aed[v][j]];
    }
    /* BFS order inside the block from its first vertex (any order is correct) */
    static int vis[MAXN];
    for (int s = bs; s < bs + bsz; s++) {
        if (vis[s]) continue;
        int q[MAXN], qh = 0, qt = 0;
        q[qt++] = s; vis[s] = 1;
        while (qh < qt) {
            int x = q[qh++];
            order[nord++] = x;
            for (int j = 0; j < adeg[x]; j++) {
                int w = anb[x][j];
                if (inblk(w) && !vis[w]) { vis[w] = 1; q[qt++] = w; }
            }
        }
    }
    for (int i = 0; i < nloc; i++) col[i] = -1;
    rec(0);
    printf("COUNT %lld\nLOCAL", count);
    for (int i = 0; i < nloc; i++) printf(" %d", loc[i]);
    printf("\nBOUNDARY");
    for (int i = 0; i < nbd; i++) printf(" %d", bd[i]);
    printf("\n");
    for (int s = 0; s < HSIZE; s++)
        if (hkey[s]) printf("SIG %s|%s\n", hkey[s], hwit[s]);
    return 0;
}
