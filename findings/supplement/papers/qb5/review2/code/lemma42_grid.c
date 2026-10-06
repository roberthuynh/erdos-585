/* lemma42_grid.c -- referee's re-implementation of the enumeration *described* in PAPER2 §4,
 * program (1), to reproduce its counts (22,792 graphs, 15,342,638 labellings), with the
 * referee's own decision (superset closure of achievable OK-pairs, as in lemma42.c).
 * Graphs: 7-edge subsets of {0..6} x {0..6}, every degree <= 3, degree sequences
 * non-increasing on both sides (isolated vertices last).
 * mode 0: p, q ends of cut edges; mode 1: p or q may be an isolated vertex (or absent).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int mode = 0;
static int ea[7], ed[7];
static long long ngraphs = 0, nlab = 0, nfail = 0;
static unsigned char ach[1 << 14];

static void process(void) {
    int ca[7] = {0}, cd[7] = {0};
    for (int e = 0; e < 7; e++) { ca[ea[e]]++; cd[ed[e]]++; }
    for (int i = 0; i < 6; i++) if (ca[i] < ca[i + 1] || cd[i] < cd[i + 1]) return;
    ngraphs++;
    int na = 0, nd = 0;
    while (na < 7 && ca[na] > 0) na++;
    while (nd < 7 && cd[nd] > 0) nd++;
    int nb = na + nd;
    memset(ach, 0, (size_t)1 << nb);
    for (int p = (mode ? -1 : 0); p < na; p++)
        for (int q = (mode ? -1 : 0); q < nd; q++) {
            int F[7], nf = 0;
            for (int e = 0; e < 7; e++) if (ea[e] != p && ed[e] != q) F[nf++] = e;
            if (nf < 4) continue;
            for (int x = 0; x < (1 << nf); x++) {
                if (__builtin_popcount(x) != 4) continue;
                int oa = 0, od = 0;
                for (int i = 0; i < nf; i++) if (x >> i & 1) { oa |= 1 << ea[F[i]]; od |= 1 << ed[F[i]]; }
                if (p >= 0) oa |= 1 << p;
                if (q >= 0) od |= 1 << q;
                ach[oa | (od << na)] = 1;
            }
        }
    for (int b = 0; b < nb; b++)
        for (int m = 0; m < (1 << nb); m++)
            if (!(m >> b & 1) && ach[m | (1 << b)]) ach[m] = 1;
    int fA = 0, fD = 0;
    for (int i = 0; i < na; i++) if (ca[i] == 3) fA |= 1 << i;
    for (int j = 0; j < nd; j++) if (cd[j] == 3) fD |= 1 << j;
    for (int LA = 0; LA < (1 << na); LA++) {
        if ((LA & fA) != fA) continue;
        int sa = 0;
        for (int i = 0; i < na; i++) if (LA >> i & 1) sa += 3 - ca[i];
        if (sa > 5) continue;
        for (int LD = 0; LD < (1 << nd); LD++) {
            if ((LD & fD) != fD) continue;
            int sd = 0;
            for (int j = 0; j < nd; j++) if (LD >> j & 1) sd += 3 - cd[j];
            if (sd > 5) continue;
            nlab++;
            if (!ach[LA | (LD << na)]) nfail++;
        }
    }
}

static int degA[7], degD[7];
static void rec(int k, int start) {
    if (k == 7) { process(); return; }
    for (int pos = start; pos < 49; pos++) {
        int a = pos / 7, d = pos % 7;
        if (degA[a] >= 3 || degD[d] >= 3) continue;
        if (49 - pos < 7 - k) break;
        ea[k] = a; ed[k] = d; degA[a]++; degD[d]++;
        rec(k + 1, pos + 1);
        degA[a]--; degD[d]--;
    }
}

int main(int argc, char **argv) {
    if (argc > 1) mode = atoi(argv[1]);
    rec(0, 0);
    printf("grid mode=%d graphs=%lld labellings=%lld failures=%lld\n", mode, ngraphs, nlab, nfail);
    return 0;
}
