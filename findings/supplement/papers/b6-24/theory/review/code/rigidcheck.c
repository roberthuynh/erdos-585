/* rigidcheck.c (referee's own code, wave4/theory review).
 * Brute-force test of PAPER Lemma 1.1, Theorem 2.1 and Corollary 2.2 on small bipartite graphs.
 * For each graph6 line (from a file): BFS 2-colouring (P = colour of the smallest vertex of each
 * component), all 4-factors by backtracking, Ex = edges in no 4-factor, s(S) for all 2^n sets.
 *  (L11) for sampled 4-factors F and every S: out-degree of S in D(F) equals s(S).
 *  (C22i) Ex = union over forced S (s(S) = 0) of E(S_P, Q - S).
 *  (C22ii) for every balanced T with 2 <= |T| <= n-2: rigid (max_F |F cap E0(T)| <= 1, brute force)
 *          iff (A) |E0(T) - Ex| <= 1 or (B) some S with s(S) = 1 has E0(T) - Ex inside E(S_P, Q-S);
 *          the same with E1(T); and rigid(T) == rigid(V - T).
 *  (T21) if n <= NT21: for random E0 and for E0(T) of random T, max_F |F cap E0| equals
 *        min over pi in {0..R}^V of Phi(pi) (levels form); weak duality checked on every pi; and the
 *        levels form equals the direct dual objective for every pi.
 * Usage: rigidcheck file.g6 [maxgraphs] [seed]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 22
#define NT21 10
static int n, ne; static uint32_t adj[MAXN]; static int deg[MAXN];
static int ep[64], eq[64];   /* edge ends, ep in P, eq in Q */
static int isP[MAXN];
static uint64_t inc[MAXN];  /* incident edge masks */

static uint64_t rng = 88172645463325252ULL;
static uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static int parse_g6(const char *s) {
  const unsigned char *p = (const unsigned char *)s;
  n = *p++ - 63;
  if (n > MAXN || n < 1) return -1;
  memset(adj, 0, sizeof(adj));
  int bit = 0, val = 0;
  for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
    if (bit == 0) { val = *p++ - 63; bit = 6; }
    bit--;
    if (val >> bit & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
  }
  for (int i = 0; i < n; i++) deg[i] = __builtin_popcount(adj[i]);
  return 0;
}

static uint64_t *fac; static size_t nfac, capfac; static size_t FACLIM = 3000000;
static int capQ[MAXN];
static int Plist[MAXN], nP;
static int overflow;

static void rec(int k, uint64_t F) {
  if (overflow) return;
  if (k == nP) {
    for (int v = 0; v < n; v++) if (!isP[v] && capQ[v] != 0) return;
    if (nfac == capfac) { capfac = capfac ? capfac * 2 : 1 << 16; fac = realloc(fac, capfac * 8); }
    fac[nfac++] = F;
    if (nfac >= FACLIM) overflow = 1;
    return;
  }
  int p = Plist[k];
  /* choose 4 incident edges among those with capQ > 0 */
  int cand[8], nc = 0;
  for (int i = 0; i < ne; i++) if (ep[i] == p && capQ[eq[i]] > 0) cand[nc++] = i;
  if (nc < 4) return;
  for (int a = 0; a < nc; a++) for (int b = a + 1; b < nc; b++) for (int c = b + 1; c < nc; c++) for (int d = c + 1; d < nc; d++) {
    int ids[4] = {cand[a], cand[b], cand[c], cand[d]};
    for (int t = 0; t < 4; t++) capQ[eq[ids[t]]]--;
    /* prune: every Q vertex must still be fillable by remaining P vertices */
    int ok = 1;
    for (int v = 0; v < n && ok; v++) if (!isP[v]) {
      if (capQ[v] < 0) { ok = 0; break; }
      int avail = 0;
      for (int kk = k + 1; kk < nP; kk++) if (adj[Plist[kk]] >> v & 1) avail++;
      if (avail < capQ[v]) ok = 0;
    }
    if (ok) rec(k + 1, F | (1ULL << ids[0]) | (1ULL << ids[1]) | (1ULL << ids[2]) | (1ULL << ids[3]));
    for (int t = 0; t < 4; t++) capQ[eq[ids[t]]]++;
  }
}

static int *sval; static uint64_t *MP, *MQ; /* s(S), E(S_P,Q-S), E(S_Q,P-S) as edge masks */

static uint64_t edges_out_P(uint32_t S) { /* E(S_P, Q - S) */
  uint64_t m = 0;
  for (int i = 0; i < ne; i++) if ((S >> ep[i] & 1) && !(S >> eq[i] & 1)) m |= 1ULL << i;
  return m;
}
static uint64_t edges_out_Q(uint32_t S) { /* E(S_Q, P - S) */
  uint64_t m = 0;
  for (int i = 0; i < ne; i++) if ((S >> eq[i] & 1) && !(S >> ep[i] & 1)) m |= 1ULL << i;
  return m;
}

int main(int argc, char **argv) {
  if (argc < 2) return 1;
  FILE *f = fopen(argv[1], "r");
  long maxg = argc > 2 ? atol(argv[2]) : -1;
  if (argc > 3) rng ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
  char line[1024];
  long ng = 0, nofac = 0, skipped = 0, fail_l11 = 0, fail_c22i = 0, fail_c22ii = 0, fail_c22ii_E1 = 0,
       fail_compl = 0, fail_t21 = 0, fail_weak = 0, fail_formula = 0, nT = 0, nrigid = 0, nA = 0, nB = 0,
       t21tests = 0, nEx = 0;
  while (fgets(line, sizeof line, f)) {
    if (maxg >= 0 && ng >= maxg) break;
    line[strcspn(line, "\r\n")] = 0;
    if (!line[0] || parse_g6(line) < 0) continue;
    ng++;
    /* colouring */
    int col[MAXN]; for (int i = 0; i < n; i++) col[i] = -1;
    int bip = 1;
    for (int r = 0; r < n; r++) if (col[r] < 0) {
      int q[MAXN], qh = 0, qt = 0; col[r] = 0; q[qt++] = r;
      while (qh < qt) { int u = q[qh++]; for (int v = 0; v < n; v++) if (adj[u] >> v & 1) {
        if (col[v] < 0) { col[v] = 1 - col[u]; q[qt++] = v; } else if (col[v] == col[u]) bip = 0; } }
    }
    ne = 0; nP = 0;
    for (int i = 0; i < n; i++) { isP[i] = col[i] == 0; if (isP[i]) Plist[nP++] = i; inc[i] = 0; }
    int maxd = 0; for (int i = 0; i < n; i++) if (deg[i] > maxd) maxd = deg[i];
    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (adj[i] >> j & 1) {
      int p = isP[i] ? i : j, qv = isP[i] ? j : i;
      if (ne < 64) { ep[ne] = p; eq[ne] = qv; inc[p] |= 1ULL << ne; inc[qv] |= 1ULL << ne; }
      ne++;
    }
    if (!bip || ne > 64 || maxd > 6 || 2 * nP != n) { skipped++; continue; }
    nfac = 0; overflow = 0;
    for (int v = 0; v < n; v++) capQ[v] = 4;
    rec(0, 0);
    if (overflow) { skipped++; continue; }
    if (nfac == 0) { nofac++; continue; }
    uint64_t uni = 0; for (size_t i = 0; i < nfac; i++) uni |= fac[i];
    uint64_t allE = (ne == 64) ? ~0ULL : ((1ULL << ne) - 1);
    uint64_t Ex = allE & ~uni;
    if (Ex) nEx++;
    size_t NS = 1ULL << n;
    sval = realloc(sval, NS * sizeof(int)); MP = realloc(MP, NS * 8); MQ = realloc(MQ, NS * 8);
    for (size_t S = 0; S < NS; S++) {
      int sp = 0, sq = 0;
      for (int v = 0; v < n; v++) if (S >> v & 1) { if (isP[v]) sp++; else sq++; }
      MP[S] = edges_out_P((uint32_t)S); MQ[S] = edges_out_Q((uint32_t)S);
      sval[S] = 4 * sp - 4 * sq + __builtin_popcountll(MQ[S]);
    }
    /* (L11): sampled factors */
    for (int t = 0; t < 6; t++) {
      size_t fi = (t == 0) ? 0 : (t == 1 ? nfac - 1 : xr() % nfac);
      uint64_t F = fac[fi];
      for (size_t S = 0; S < NS; S++) {
        /* out-arcs: F-edges from S_P to Q-S, H-edges from S_Q to P-S */
        int out = __builtin_popcountll(MP[S] & F) + __builtin_popcountll(MQ[S] & ~F & allE);
        if (out != sval[S]) fail_l11++;
      }
    }
    /* (C22i) */
    uint64_t U = 0;
    size_t ns1 = 0; uint64_t *s1 = malloc(NS * 8);
    for (size_t S = 0; S < NS; S++) { if (sval[S] == 0) U |= MP[S]; if (sval[S] == 1) s1[ns1++] = MP[S]; }
    if (U != Ex) fail_c22i++;
    /* (C22ii) */
    char *rig = calloc(NS, 1);
    for (size_t T = 0; T < NS; T++) {
      int tp = 0, tq = 0;
      for (int v = 0; v < n; v++) if (T >> v & 1) { if (isP[v]) tp++; else tq++; }
      if (tp != tq || tp + tq < 2 || tp + tq > n - 2) continue;
      nT++;
      uint64_t E0 = MQ[T], E1 = MP[T];
      int rigid = 1;
      for (size_t i = 0; i < nfac; i++) if (__builtin_popcountll(fac[i] & E0) >= 2) { rigid = 0; break; }
      /* sanity: c_F(T) via E1 equals via E0 (PAPER (1)) on a few factors */
      for (int t = 0; t < 2; t++) { uint64_t F = fac[xr() % nfac]; if (__builtin_popcountll(F & E0) != __builtin_popcountll(F & E1)) fail_compl++; }
      rig[T] = rigid; nrigid += rigid;
      for (int which = 0; which < 2; which++) {
        uint64_t R = (which ? E1 : E0) & ~Ex;
        int crit = 0, A = 0, B = 0;
        if (__builtin_popcountll(R) <= 1) { crit = 1; A = 1; }
        else for (size_t k = 0; k < ns1; k++) if ((R & ~s1[k]) == 0) { crit = 1; B = 1; break; }
        if (crit != rigid) { if (which) fail_c22ii_E1++; else fail_c22ii++; }
        if (!which && rigid) { nA += A; nB += B; }
      }
    }
    for (size_t T = 0; T < NS; T++) {
      uint32_t C = (uint32_t)((NS - 1) & ~T);
      if (rig[T] != rig[C]) fail_compl++;
    }
    free(rig);
    /* (T21) */
    if (n <= NT21) {
      for (int trial = 0; trial < 8; trial++) {
        uint64_t E0;
        if (trial < 4) E0 = xr() & allE;
        else { /* E0(T) of a random balanced T */
          uint32_t T; int tp, tq;
          do { T = (uint32_t)(xr() & (NS - 1)); tp = tq = 0; for (int v = 0; v < n; v++) if (T >> v & 1) { if (isP[v]) tp++; else tq++; } } while (tp != tq || tp == 0 || 2 * tp == n);
          E0 = MQ[T];
        }
        int mx = 0; for (size_t i = 0; i < nfac; i++) { int c = __builtin_popcountll(fac[i] & E0); if (c > mx) mx = c; }
        int R = (n <= 8) ? 3 : 2; long best = 1L << 30;
        int pi[MAXN]; for (int v = 0; v < n; v++) pi[v] = 0;
        for (;;) {
          /* levels form */
          long phi = 0;
          for (int t = 1; t <= R; t++) { uint32_t St = 0; for (int v = 0; v < n; v++) if (pi[v] >= t) St |= 1u << v; phi += sval[St]; }
          int uncut = 0;
          for (int i = 0; i < ne; i++) if ((E0 >> i & 1) && pi[ep[i]] <= pi[eq[i]]) uncut++;
          phi += uncut;
          /* direct dual objective */
          long dir = 0;
          for (int v = 0; v < n; v++) dir += isP[v] ? 4 * pi[v] : -4 * pi[v];
          for (int i = 0; i < ne; i++) { int z = (int)((E0 >> i) & 1) + pi[eq[i]] - pi[ep[i]]; if (z > 0) dir += z; }
          if (dir != phi) fail_formula++;
          if (phi < mx) fail_weak++;
          if (phi < best) best = phi;
          int v = 0; while (v < n && pi[v] == R) { pi[v] = 0; v++; }
          if (v == n) break;
          pi[v]++;
        }
        t21tests++;
        if (best != mx) { fail_t21++; if (fail_t21 < 5) printf("T21 mismatch graph %ld max %d min %ld\n", ng, mx, best); }
      }
    }
    free(s1);
  }
  printf("file %s graphs %ld skipped %ld no4factor %ld graphs_with_Ex %ld | balancedT %ld rigid %ld (A %ld, B-only %ld) | "
         "fail L1.1 %ld C2.2i %ld C2.2ii(E0) %ld C2.2ii(E1) %ld complement/(1) %ld | T2.1 tests %ld fail %ld weak %ld formula %ld\n",
         argv[1], ng, skipped, nofac, nEx, nT, nrigid, nA, nB, fail_l11, fail_c22i, fail_c22ii, fail_c22ii_E1, fail_compl,
         t21tests, fail_t21, fail_weak, fail_formula);
  return 0;
}
