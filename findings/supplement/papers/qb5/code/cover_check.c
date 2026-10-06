/* cover_check.c (lane qb5, round 2): second, independent decider for Lemma 6.5 (NOTES.md section 6).
 * Build: /usr/bin/clang -O3 -o cover_check cover_check.c
 * Statement checked (covering form): for every set E of 7 edges between A = {0..6} and D = {0..6}
 * (simple, every degree <= 3) and every admissible labelling L_A, L_D (subsets of the endpoints; every
 * vertex with c = 3 is in L; on each side sum over L of (3 - c) <= 5), there are p in A, q in D and a set
 * M of 4 edges of E, none at p or q, that covers every vertex of (L_A - p) u (L_D - q).
 * p and q range over the 7 labels and an extra label 7 (a vertex with no cut edge, outside L); run with
 * argument 1 to forbid every c = 0 choice (no interior vertex available).
 * Enumeration: all labelled edge sets with non-increasing degree sequences on both sides (a superset of
 * the isomorphism classes); no nauty, no code shared with generic_check.py.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int ea[7], ed[7], noint;
static long graphs = 0, configs = 0, fails = 0;
static int degA[7], degD[7];

static int solve(int LA, int LD){
    /* search p, q, M */
    for (int p = 0; p < 8; p++) {          /* p = 7: a vertex of A without cut edges, outside L */
        if (noint && (p == 7 || degA[p] == 0)) continue;
        for (int q = 0; q < 8; q++) {
            if (noint && (q == 7 || degD[q] == 0)) continue;
            int avail[7], na = 0;
            for (int i = 0; i < 7; i++) if (ea[i] != p && ed[i] != q) avail[na++] = i;
            if (na < 4) continue;
            int needA = LA & ~(1 << p), needD = LD & ~(1 << q);
            for (int s = 0; s < (1 << na); s++) {
                if (__builtin_popcount(s) != 4) continue;
                int cA = 0, cD = 0;
                for (int j = 0; j < na; j++) if (s >> j & 1) { cA |= 1 << ea[avail[j]]; cD |= 1 << ed[avail[j]]; }
                if ((needA & ~cA) == 0 && (needD & ~cD) == 0) return 1;
            }
        }
    }
    return 0;
}

static void labellings(void){
    graphs++;
    int forcedA = 0, forcedD = 0, optA = 0, optD = 0;
    for (int v = 0; v < 7; v++) {
        if (degA[v] == 3) forcedA |= 1 << v; else if (degA[v] >= 1) optA |= 1 << v;
        if (degD[v] == 3) forcedD |= 1 << v; else if (degD[v] >= 1) optD |= 1 << v;
    }
    for (int xa = optA;; xa = (xa - 1) & optA) {
        int LA = forcedA | xa, bA = 0;
        for (int v = 0; v < 7; v++) if (LA >> v & 1) bA += 3 - degA[v];
        if (bA <= 5) {
            for (int xd = optD;; xd = (xd - 1) & optD) {
                int LD = forcedD | xd, bD = 0;
                for (int v = 0; v < 7; v++) if (LD >> v & 1) bD += 3 - degD[v];
                if (bD <= 5) {
                    configs++;
                    if (!solve(LA, LD)) {
                        fails++;
                        if (fails <= 5) {
                            printf("FAIL edges:"); for (int i = 0; i < 7; i++) printf(" %d-%d", ea[i], ed[i]);
                            printf("  LA=0x%x LD=0x%x\n", LA, LD);
                        }
                    }
                }
                if (xd == 0) break;
            }
        }
        if (xa == 0) break;
    }
}

static void rec(int k, int start){
    if (k == 7) {
        for (int v = 0; v + 1 < 7; v++) if (degA[v] < degA[v + 1] || degD[v] < degD[v + 1]) return;
        labellings();
        return;
    }
    for (int idx = start; idx < 49; idx++) {
        int a = idx / 7, d = idx % 7;
        if (degA[a] >= 3 || degD[d] >= 3) continue;
        ea[k] = a; ed[k] = d; degA[a]++; degD[d]++;
        rec(k + 1, idx + 1);
        degA[a]--; degD[d]--;
    }
}

int main(int argc, char **argv){
    noint = (argc > 1 && atoi(argv[1]) == 1);
    rec(0, 0);
    printf("noint=%d labelled graphs (sorted degrees)=%ld configurations=%ld failures=%ld\n", noint, graphs, configs, fails);
    return 0;
}
