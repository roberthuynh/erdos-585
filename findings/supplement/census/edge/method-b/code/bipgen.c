/* bipgen.c -- method B generator (wave8/exb), written for this lane.

   Generates bicoloured graphs: class A of n1 vertices (0..n1-1) and class
   B of n2 vertices (n1..n1+n2-1), every edge between A and B, degrees of
   A-vertices in [dA, DA], of B-vertices in [dB, DB], edges in [emin, emax],
   one graph per isomorphism class (isomorphisms preserve A and B), the
   same objects that nauty's genbg counts.  With pruning on (default) only
   graphs with no nonempty 4-regular subgraph are kept, decided by h4.h.

   Method: canonical augmentation (McKay's canonical construction path)
   by B-vertices, implemented here from scratch; nauty is used only for
   automorphism groups and canonical labelling (densenauty).
     - Start: A alone.  A child of P is P plus one B-vertex b with
       neighbourhood S (a subset of A); one S per orbit of Aut(P) on
       subsets of A.
     - Canonical deletion vertex of G: among the B-vertices of minimum
       degree, those with the largest f(x) = sum of the degrees of the
       neighbours of x; among those, the one placed last by nauty's
       canonical labelling of G with the ordered partition
       [A][rest of B][those]; its Aut(G)-orbit is O(G).
     - G = P + b is accepted iff b lies in O(G).
   Every isomorphism class at level k is then produced exactly once from
   the unique class of its parent.  Necessary conditions used to cut the
   tree (each holds for every graph on the canonical path of a graph in
   the class): B-degrees along the path are non-increasing (the deleted
   vertex has minimum degree), A-degrees stay <= DA and can still reach
   dA, and the edges still to come fit the remaining B-vertices and the
   remaining A-capacity.  With pruning, a child with a 4-regular subgraph
   is dropped (supergraphs keep it); every drop carries a checked
   certificate (h4.h).  The parent is 4-regular-free, so only subgraphs
   through b are searched.

   Usage: bipgen [-u] [-P] [-q] [-1] [-l LEVEL] n1 n2 emin:emax dA:dB DA:DB [res/mod]
     -u      count only, write no graphs
     -1      stop after the first output graph (existence checks)
     -P      no 4-regular pruning (whole class, for counts)
     -l L    split level for res/mod (number of B-vertices); default chosen
     res/mod shard: only subtrees of level-L nodes with index = res (mod mod)
   Output: graph6 on stdout; statistics on stderr (">B" lines). */

#include "gtools.h"
#include "h4.h"

#if WORDSIZE != 32
#error "bipgen.c expects WORDSIZE 32"
#endif

#define MAXA 12
#define MAXB 12
#define NSUB (1 << MAXA)

static int n1, n2, emin, emax, dA, dB, DA, DB;
static int prune = 1, countonly = 0, quietstats = 0, stopfirst = 0;
static double t_start;
static void finish(void);
static long long res = 0, mod = 1;
static int splitlevel = -1;
static unsigned long long splitcounter = 0;

static h4set nbB[MAXB];  /* neighbourhood (subset of A) of B-vertex j */
static int degB[MAXB];
static int degA[MAXA];
static int ecur = 0;
static h4set adjH[H4MAXN]; /* whole graph for the decider, bit v = vertex v */

static unsigned long long cnt_nodes[MAXB + 2], cnt_hcut[MAXB + 2],
    cnt_canonrej[MAXB + 2], cnt_feasrej[MAXB + 2], cnt_nauty = 0, cnt_out = 0,
    cnt_cand[MAXB + 2];

static int subsz[MAXA + 1][NSUB];
static int nsubsz[MAXA + 1];

/* automorphism generators, per level, restricted to A */
#define MAXGENS 64
static int gens[MAXB + 2][MAXGENS][MAXA];
static int ngens[MAXB + 2];
static int gensvalid[MAXB + 2];
static int *curgens_n;
static int (*curgens)[MAXA];

static void autproc(int count, int *perm, int *orbits, int numorbits,
                    int stabvertex, int n)
{
    int a;
    (void)count; (void)orbits; (void)numorbits; (void)stabvertex; (void)n;
    if (*curgens_n >= MAXGENS) {
        fprintf(stderr, ">E bipgen: too many generators\n");
        exit(4);
    }
    for (a = 0; a < n1; ++a) {
        if (perm[a] >= n1) {
            fprintf(stderr, ">E bipgen: automorphism leaves class A\n");
            exit(4);
        }
        curgens[*curgens_n][a] = perm[a];
    }
    ++*curgens_n;
}

static graph gN[MAXN], cgN[MAXN];
static int lab[MAXN], ptn[MAXN], orb[MAXN];

static void build_nauty(int k)
{
    int n = n1 + k, j;
    EMPTYGRAPH(gN, 1, n);
    for (j = 0; j < k; ++j) {
        h4set s = nbB[j];
        while (s) {
            int a = H4LOW(s);
            s &= s - 1;
            ADDONEEDGE(gN, a, n1 + j, 1);
        }
    }
}

/* Aut(P) for the current graph with k B-vertices, partition [A][B]. */
static void compute_group(int k)
{
    static DEFAULTOPTIONS_GRAPH(opt);
    statsblk st;
    int n = n1 + k, i;
    build_nauty(k);
    for (i = 0; i < n; ++i) { lab[i] = i; ptn[i] = 1; }
    ptn[n1 - 1] = 0;
    ptn[n - 1] = 0;
    opt.defaultptn = FALSE;
    opt.getcanon = FALSE;
    opt.userautomproc = autproc;
    ngens[k] = 0;
    curgens_n = &ngens[k];
    curgens = gens[k];
    densenauty(gN, lab, ptn, orb, &opt, &st, 1, n, NULL);
    ++cnt_nauty;
    gensvalid[k] = 1;
}

/* Canonical test for G = current graph with k+1 B-vertices, the newest
   being b = n1 + k.  cand = mask over B indices (0..k) of the B-vertices
   of minimum degree with the largest f; b is in cand and |cand| >= 2.
   Returns 1 iff b is in the orbit of the last-placed vertex of cand.
   Stores the generators of Aut(G) in gens[k+1]. */
static int canon_test(int k, h4set cand)
{
    static DEFAULTOPTIONS_GRAPH(opt);
    statsblk st;
    int n = n1 + k + 1, i, pos = 0, j, t;
    build_nauty(k + 1);
    for (i = 0; i < n1; ++i) { lab[pos] = i; ptn[pos] = 1; ++pos; }
    ptn[pos - 1] = 0;
    {
        int start = pos;
        for (j = 0; j <= k; ++j)
            if (!(cand & H4BIT(j))) { lab[pos] = n1 + j; ptn[pos] = 1; ++pos; }
        if (pos > start) ptn[pos - 1] = 0;
    }
    for (j = 0; j <= k; ++j)
        if (cand & H4BIT(j)) { lab[pos] = n1 + j; ptn[pos] = 1; ++pos; }
    ptn[pos - 1] = 0;
    if (pos != n) { fprintf(stderr, ">E bipgen: partition size\n"); exit(4); }
    opt.defaultptn = FALSE;
    opt.getcanon = TRUE;
    opt.userautomproc = autproc;
    ngens[k + 1] = 0;
    curgens_n = &ngens[k + 1];
    curgens = gens[k + 1];
    densenauty(gN, lab, ptn, orb, &opt, &st, 1, n, cgN);
    ++cnt_nauty;
    gensvalid[k + 1] = 1;
    t = lab[n - 1];
    return orb[n1 + k] == orb[t];
}

static void write_g6(int n)
{
    char buf[256];
    int i, j, k = 0, p = 0, x = 0;
    buf[p++] = (char)(n + 63);
    for (j = 1; j < n; ++j)
        for (i = 0; i < j; ++i) {
            int bit = (adjH[i] >> j) & 1;
            x = (x << 1) | bit;
            if (++k == 6) { buf[p++] = (char)(x + 63); k = 0; x = 0; }
        }
    if (k > 0) { x <<= (6 - k); buf[p++] = (char)(x + 63); }
    buf[p++] = '\n';
    buf[p] = '\0';
    fputs(buf, stdout);
}

/* orbit representatives of candidate subsets at level k */
static int reps[MAXB + 2][NSUB];
static int nreps[MAXB + 2];
static unsigned char seen[NSUB];
static int queue_[NSUB];

static h4set apply_gen(const int *g, h4set s)
{
    h4set r = 0;
    while (s) {
        int a = H4LOW(s);
        s &= s - 1;
        r |= H4BIT(g[a]);
    }
    return r;
}

static void make_reps(int k, int smax)
{
    h4set full = 0;
    int a, s, i, gi;
    int trivial;
    for (a = 0; a < n1; ++a)
        if (degA[a] >= DA) full |= H4BIT(a);
    if (!gensvalid[k]) compute_group(k);
    trivial = (ngens[k] == 0);
    nreps[k] = 0;
    for (s = smax; s >= dB; --s) {
        for (i = 0; i < nsubsz[s]; ++i) {
            int S = subsz[s][i];
            if (S & full) continue;
            if (trivial) { reps[k][nreps[k]++] = S; continue; }
            if (seen[S]) continue;
            /* BFS the orbit of S; S is its smallest member (increasing order,
               and the orbit stays inside the candidate set) */
            {
                int qh = 0, qt = 0;
                seen[S] = 1;
                queue_[qt++] = S;
                while (qh < qt) {
                    int T = queue_[qh++];
                    for (gi = 0; gi < ngens[k]; ++gi) {
                        int U = (int)apply_gen(gens[k][gi], (h4set)T);
                        if (!seen[U]) { seen[U] = 1; queue_[qt++] = U; }
                    }
                }
                reps[k][nreps[k]++] = S;
            }
        }
    }
    if (!trivial) memset(seen, 0, sizeof seen);
}

static void extend(int k);

static void try_child(int k, int S)
{
    int d = H4POP((h4set)S), r = n2 - (k + 1), a, j;
    int newe = ecur + d, Rlo = emin - newe, Rhi = emax - newe;
    int need = 0, cap = 0, b = n1 + k;
    int minB = (k == 0) ? DB : degB[k - 1];
    int nauty_needed = 0;
    h4set cand = 0;

    ++cnt_cand[k + 1];
    /* edges still to come: between r*dB and r*d, inside [Rlo, Rhi] */
    if (Rhi < r * dB || Rlo > r * d) { ++cnt_feasrej[k + 1]; return; }
    for (a = 0; a < n1; ++a) {
        int nd = degA[a] + ((S >> a) & 1);
        if (nd + r < dA) { ++cnt_feasrej[k + 1]; return; }
        if (nd < dA) need += dA - nd;
        cap += DA - nd;
    }
    /* the edges still to come, R, satisfy max(Rlo, r*dB) <= R <= min(Rhi, r*d);
       they must cover the A-deficits (need) and fit the A-capacity (cap) */
    if (need > Rhi || need > r * d || cap < Rlo || cap < r * dB) { ++cnt_feasrej[k + 1]; return; }
    if (r == 0 && (newe < emin || newe > emax)) { ++cnt_feasrej[k + 1]; return; }

    /* canonicity pre-test with invariants */
    if (k >= 1 && d == minB) {
        long fb = 0, fmax;
        int ties = 0;
        h4set s = (h4set)S;
        while (s) { int x = H4LOW(s); s &= s - 1; fb += degA[x] + 1; }
        fmax = fb;
        for (j = 0; j < k; ++j) {
            long f = 0;
            h4set t = nbB[j];
            if (degB[j] != d) continue;
            while (t) { int x = H4LOW(t); t &= t - 1; f += degA[x] + ((S >> x) & 1); }
            if (f > fmax) { ++cnt_canonrej[k + 1]; return; }
            if (f == fmax) { ++ties; cand |= H4BIT(j); }
        }
        if (ties > 0) { nauty_needed = 1; cand |= H4BIT(k); }
    }

    /* add b */
    nbB[k] = (h4set)S;
    degB[k] = d;
    for (a = 0; a < n1; ++a)
        if ((S >> a) & 1) { ++degA[a]; adjH[a] |= H4BIT(b); }
    adjH[b] = (h4set)S;
    ecur = newe;
    gensvalid[k + 1] = 0;

    if (prune && d >= 4) {
        h4set all = H4BIT(b + 1) - 1;
        h4set K = h4_core4(adjH, b + 1, all);
        if ((K & H4BIT(b)) && h4_through(adjH, b + 1, K, b, NULL)) {
            ++cnt_hcut[k + 1];
            goto undo;
        }
    }
    if (nauty_needed && !canon_test(k, cand)) {
        ++cnt_canonrej[k + 1];
        goto undo;
    }

    ++cnt_nodes[k + 1];
    if (k + 1 == splitlevel) {
        unsigned long long idx = splitcounter++;
        if ((long long)(idx % (unsigned long long)mod) != res) goto undo;
    }
    if (k + 1 == n2) {
        for (a = 0; a < n1; ++a)
            if (degA[a] < dA || degA[a] > DA) {
                fprintf(stderr, ">E bipgen: final A-degree out of range\n");
                exit(4);
            }
        ++cnt_out;
        if (!countonly) write_g6(n1 + n2);
        if (stopfirst) { finish(); exit(0); }
    } else
        extend(k + 1);

undo:
    for (a = 0; a < n1; ++a)
        if ((S >> a) & 1) { --degA[a]; adjH[a] &= ~H4BIT(b); }
    adjH[b] = 0;
    nbB[k] = 0;
    degB[k] = 0;
    ecur -= d;
}

static void extend(int k)
{
    int smax = (k == 0) ? DB : degB[k - 1];
    int i;
    if (smax > DB) smax = DB;
    if (smax > n1) smax = n1;
    if (smax < dB) return;
    make_reps(k, smax);
    for (i = 0; i < nreps[k]; ++i) try_child(k, reps[k][i]);
}

static int parse_pair(const char *s, int *x, int *y)
{
    if (sscanf(s, "%d:%d", x, y) == 2) return 0;
    if (sscanf(s, "%d", x) == 1) { *y = *x; return 0; }
    return -1;
}

int main(int argc, char **argv)
{
    int i, pos = 0;
    char *args[8];
    double t0;
    for (i = 1; i < argc; ++i) {
        if (strcmp(argv[i], "-u") == 0) countonly = 1;
        else if (strcmp(argv[i], "-P") == 0) prune = 0;
        else if (strcmp(argv[i], "-q") == 0) quietstats = 1;
        else if (strcmp(argv[i], "-1") == 0) stopfirst = 1;
        else if (strcmp(argv[i], "-l") == 0 && i + 1 < argc) splitlevel = atoi(argv[++i]);
        else if (pos < 8) args[pos++] = argv[i];
        else { fprintf(stderr, ">E bipgen: too many arguments\n"); return 2; }
    }
    if (pos < 5) {
        fprintf(stderr, "Usage: bipgen [-u] [-P] [-q] [-l L] n1 n2 emin:emax dA:dB DA:DB [res/mod]\n");
        return 2;
    }
    n1 = atoi(args[0]);
    n2 = atoi(args[1]);
    if (parse_pair(args[2], &emin, &emax) || parse_pair(args[3], &dA, &dB) ||
        parse_pair(args[4], &DA, &DB)) {
        fprintf(stderr, ">E bipgen: bad arguments\n");
        return 2;
    }
    if (pos >= 6 && sscanf(args[5], "%lld/%lld", &res, &mod) != 2) {
        fprintf(stderr, ">E bipgen: bad res/mod\n");
        return 2;
    }
    if (DB > n1) DB = n1;
    if (DA > n2) DA = n2;
    if (n1 < 1 || n1 > MAXA || n2 < 1 || n2 > MAXB || n1 + n2 > 20 || DA > 7 ||
        dB < 0 || dA < 0 || res < 0 || mod < 1 || res >= mod) {
        fprintf(stderr, ">E bipgen: unsupported parameters\n");
        return 2;
    }
    if (splitlevel < 0) splitlevel = (n2 >= 5) ? n2 - 4 : 1;
    if (splitlevel > n2) splitlevel = n2;
    nauty_check(WORDSIZE, 1, n1 + n2, NAUTYVERSIONID);
    for (i = 0; i < (1 << n1); ++i) {
        int s = H4POP((h4set)i);
        subsz[s][nsubsz[s]++] = i;
    }
    t_start = CPUTIME;
    (void)t0;
    extend(0);
    finish();
    return 0;
}

static void finish(void)
{
    int i;
    fflush(stdout);
    fprintf(stderr, ">B bipgen n1=%d n2=%d e=%d:%d d=%d:%d D=%d:%d prune=%d res/mod=%lld/%lld split=%d%s\n",
            n1, n2, emin, emax, dA, dB, DA, DB, prune, res, mod, splitlevel,
            stopfirst ? " (stop at first output)" : "");
    if (!quietstats)
        for (i = 1; i <= n2; ++i)
            fprintf(stderr, ">B level %d: candidates %llu feasrej %llu canonrej %llu hcut %llu nodes %llu\n",
                    i, cnt_cand[i], cnt_feasrej[i], cnt_canonrej[i], cnt_hcut[i], cnt_nodes[i]);
    fprintf(stderr, ">B nauty calls %llu, h4 search nodes %llu, split nodes %llu\n",
            cnt_nauty, h4_nodes, splitcounter);
    fprintf(stderr, ">Z %llu graphs generated in %.2f sec\n", cnt_out, CPUTIME - t_start);
}
