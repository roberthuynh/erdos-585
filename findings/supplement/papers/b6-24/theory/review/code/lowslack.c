/* lowslack.c (referee's own code, wave4/theory review).
 * For each graph (graph6, one per line, read from a file): 2-colour it by BFS, check that it is an
 * E4 instance (connected bipartite, |P| = |Q|, Delta <= 6, e = 3n - 4, D(P) = D(Q) = 4), check
 * sparsity by brute force (g(S) >= 10 for 2 <= |S| <= n-1), and list every S with 2 <= |S| <= n-1
 * and s(S) = 4|S_P| - 4|S_Q| + dQ(S) <= 1 (Gray code over all 2^n subsets). Each such S is matched
 * against the seven rows of PAPER Lemma 3.1 (s, j, D(S_Q), D(S_P), g, dQ, dP). Both orientations
 * (P = colour of vertex 0, and swapped) are run. Also checks, for every S, the identities
 * s = g/2 - j - D(S_Q), dQ = g/2 + 3j - D(S_Q), dP = g/2 - 3j - D(S_P), and the complement remarks
 * (F1 with |V-S| >= 2 has D(S_P) = 0, dP = 2, g(V-S) = 10; U0 is a (5,1) set).
 * Usage: lowslack file.g6 [maxgraphs]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 24
static int n; static uint32_t adj[MAXN]; static int deg[MAXN];

static int parse_g6(const char *s) {
  const unsigned char *p = (const unsigned char *)s;
  if (*p == '>') return -1;
  n = *p++ - 63;
  if (n > MAXN || n < 1) return -1;
  memset(adj, 0, sizeof(adj));
  int bit = 0; int val = 0;
  for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
    if (bit == 0) { val = *p++ - 63; bit = 6; }
    bit--;
    if (val >> bit & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
  }
  for (int i = 0; i < n; i++) deg[i] = __builtin_popcount(adj[i]);
  return 0;
}

static const char *TYPES[] = {"F1", "F2", "U0", "U1", "U2", "U3", "U4"};
/* returns type index or -1. Rows: s j dQ dP g delQ delP */
static int match_row(int s, int j, int dq, int dp, int g, int delq, int delp) {
  if (s == 0 && j == 1 && dq == 4 && g == 10 && delq == 4 && delp == 2 - dp) return 0;
  if (s == 0 && j == 2 && dq == 4 && dp == 0 && g == 12 && delq == 8 && delp == 0) return 1;
  if (s == 1 && j == 0 && dq == 4 && g == 10 && delq == 1 && delp == 5 - dp) return 2;
  if (s == 1 && j == 1 && dq == 3 && g == 10 && delq == 5 && delp == 2 - dp) return 3;
  if (s == 1 && j == 1 && dq == 4 && g == 12 && delq == 5 && delp == 3 - dp) return 4;
  if (s == 1 && j == 2 && dq == 3 && dp == 0 && g == 12 && delq == 9 && delp == 0) return 5;
  if (s == 1 && j == 2 && dq == 4 && dp <= 1 && g == 14 && delq == 9 && delp == 1 - dp) return 6;
  return -1;
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage\n"); return 1; }
  FILE *f = fopen(argv[1], "r");
  long maxg = argc > 2 ? atol(argv[2]) : -1;
  char line[1024];
  long ng = 0, notinst = 0, notsparse = 0, unmatched = 0, idfail = 0, compfail = 0;
  long cnt[2][7] = {{0}};
  long negs = 0;
  while (fgets(line, sizeof line, f)) {
    if (maxg >= 0 && ng >= maxg) break;
    line[strcspn(line, "\r\n")] = 0;
    if (!line[0] || parse_g6(line) < 0) continue;
    ng++;
    /* BFS colouring */
    int col[MAXN]; for (int i = 0; i < n; i++) col[i] = -1;
    int q[MAXN], qh = 0, qt = 0; col[0] = 0; q[qt++] = 0; int bip = 1;
    while (qh < qt) { int u = q[qh++]; for (int v = 0; v < n; v++) if (adj[u] >> v & 1) {
      if (col[v] < 0) { col[v] = 1 - col[u]; q[qt++] = v; } else if (col[v] == col[u]) bip = 0; } }
    int e = 0; for (int i = 0; i < n; i++) e += deg[i]; e /= 2;
    int c0 = 0, maxd = 0; for (int i = 0; i < n; i++) { c0 += col[i] == 0; if (deg[i] > maxd) maxd = deg[i]; }
    int D0 = 0, D1 = 0; for (int i = 0; i < n; i++) { if (col[i] == 0) D0 += 6 - deg[i]; else D1 += 6 - deg[i]; }
    if (!bip || qt != n || 2 * c0 != n || maxd > 6 || e != 3 * n - 4 || D0 != 4 || D1 != 4) { notinst++; continue; }
    for (int orient = 0; orient < 2; orient++) {
      uint32_t Pm = 0; for (int i = 0; i < n; i++) if ((col[i] == 0) == (orient == 0)) Pm |= 1u << i;
      /* Gray code */
      uint32_t S = 0; int sp = 0, sq = 0, eS = 0, degSP = 0, degSQ = 0, DSP = 0, DSQ = 0;
      int sparse_ok = 1;
      uint32_t full = (n == 32) ? 0xffffffffu : ((1u << n) - 1);
      for (uint64_t k = 1; k < (1ULL << n); k++) {
        int v = __builtin_ctzll(k);
        uint32_t b = 1u << v;
        int isP = (Pm >> v) & 1;
        if (S & b) { /* remove */
          S &= ~b; eS -= __builtin_popcount(adj[v] & S);
          if (isP) { sp--; degSP -= deg[v]; DSP -= 6 - deg[v]; } else { sq--; degSQ -= deg[v]; DSQ -= 6 - deg[v]; }
        } else {
          eS += __builtin_popcount(adj[v] & S); S |= b;
          if (isP) { sp++; degSP += deg[v]; DSP += 6 - deg[v]; } else { sq++; degSQ += deg[v]; DSQ += 6 - deg[v]; }
        }
        int sz = sp + sq;
        int g = 6 * sz - 2 * eS;
        int delq = degSQ - eS, delp = degSP - eS;
        int j = sq - sp;
        int s = 4 * sp - 4 * sq + delq;
        /* identities, every S */
        if (2 * s != g - 2 * j - 2 * DSQ || 2 * delq != g + 6 * j - 2 * DSQ || 2 * delp != g - 6 * j - 2 * DSP) idfail++;
        if (s < 0) negs++;
        if (sz >= 2 && sz <= n - 1) {
          if (g < 10) sparse_ok = 0;
          if (s <= 1) {
            int t = match_row(s, j, DSQ, DSP, g, delq, delp);
            if (t < 0) { unmatched++; if (unmatched < 10) printf("UNMATCHED graph %ld S=%x s=%d j=%d dq=%d dp=%d g=%d delq=%d delp=%d\n", ng, S, s, j, DSQ, DSP, g, delq, delp); }
            else {
              cnt[orient][t]++;
              /* complement remarks */
              uint32_t C = full & ~S; int csz = n - sz;
              int eC = 0; for (int u = 0; u < n; u++) if (C >> u & 1) eC += __builtin_popcount(adj[u] & C);
              eC /= 2; int gC = 6 * csz - 2 * eC;
              if (t == 0 && csz >= 2 && !(DSP == 0 && delp == 2 && gC == 10)) compfail++;
              if (t == 2) { /* (5,1) set: D(T_Q)=4, D(T_P)=0, dP=5, D(P-T)=4, D(Q-T)=0, g = g(V-T) = 10 */
                if (!(DSQ == 4 && DSP == 0 && delp == 5 && g == 10 && gC == 10)) compfail++;
              }
            }
          }
        }
      }
      if (!sparse_ok) { notsparse++; }
    }
  }
  printf("file %s graphs %ld not_instance %ld not_sparse(orient-runs) %ld unmatched %ld identity_failures %ld negative_s %ld complement_remark_failures %ld\n",
         argv[1], ng, notinst, notsparse, unmatched, idfail, negs, compfail);
  for (int o = 0; o < 2; o++) {
    printf("orientation %d:", o);
    for (int t = 0; t < 7; t++) printf(" %s=%ld", TYPES[t], cnt[o][t]);
    printf("\n");
  }
  return 0;
}
