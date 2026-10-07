/* Round 4 (lane qb5): computer check of the lemmas behind the KL1 proof of PAPER4.
 * Input lines: "na nc mask_1 ... mask_nc [ignored]" (mask_j = A-neighbours of the j-th C-vertex).
 * For every multiset m on A with m(A) = 4 and m(a) <= min(3, delta_a) (covering L_A or not):
 *   theta*(T) = m(T) + 4 - 4|T| + sum_c (e(c,T) - 2)^+  for all T (PAPER3 theta(T)).
 *   F1  theta*(empty) = 4, theta*({a}) = m(a), theta* <= 0 on pairs, theta* <= 2 on |T| >= 3.
 *   F2  merging lemma on every pair of maximal overloaded sets.
 *   F3  hub claims: T n T' (|.| >= 3) is a maximal theta* >= 2 set K; every maximal overloaded set
 *       meeting K in >= 2 vertices contains K; one meeting K in one vertex a has m(a) = 3.
 *   F4  KL1: if m covers L_A, the overloaded sets do not cover A.
 *   F5  (proof structure) if the overloaded sets cover A (possible only when m misses L_A), no minimal
 *       subcover by maximal overloaded sets has all pairwise intersections of size <= 1 (Step B), and
 *       every minimal subcover has a member pair sharing >= 3 vertices plus a one-vertex petal y with
 *       w(y) = 3 (an uncovered in-degree-3 vertex), as Step C predicts.
 * Usage: merge_check < blocks   (prints counters; nonzero "viol" means a failed claim) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXA 16
#define MAXC 16
static int na, nc, msk[MAXC], deg[MAXA], del[MAXA];
static int base[1 << MAXA], th[1 << MAXA];
static unsigned char up1[1 << MAXA], up2[1 << MAXA];
static int m[MAXA];
static long nblock, nm, ncov, nfailcov, nfailnon, npairs[4], viol[8], nsub, nsubhubfree, nsubnopetal3;
static int pc(unsigned x) { return __builtin_popcount(x); }
static void check_m(void) {
  int full = (1 << na) - 1, T, v, i, j;
  int covering = 1;
  for (v = 0; v < na; v++) if (deg[v] == 3 && m[v] == 0) covering = 0;
  nm++; if (covering) ncov++;
  for (T = 0; T <= full; T++) {
    int mt = 0; for (v = 0; v < na; v++) if (T >> v & 1) mt += m[v];
    th[T] = mt + base[T];
  }
  /* F1 */
  if (th[0] != 4) viol[0]++;
  for (T = 1; T <= full; T++) {
    int s = pc(T);
    if (s == 1) { for (v = 0; v < na; v++) if (T == 1 << v && th[T] != m[v]) viol[0]++; }
    else if (s == 2) { if (th[T] > 0) viol[0]++; }
    else if (th[T] > 2) viol[0]++;
  }
  /* superset closures */
  for (T = full; T >= 0; T--) {
    unsigned char a1 = th[T] >= 1, a2 = th[T] >= 2 && T != 0;
    for (v = 0; v < na; v++) if (!(T >> v & 1)) { a1 |= up1[T | 1 << v]; a2 |= up2[T | 1 << v]; }
    up1[T] = a1; up2[T] = a2;
  }
  int mx[4096], nmx = 0, cov = 0;
  for (T = 1; T <= full; T++) if (th[T] >= 1) {
    int ismax = 1; for (v = 0; v < na; v++) if (!(T >> v & 1) && up1[T | 1 << v]) { ismax = 0; break; }
    if (ismax) { if (nmx < 4096) mx[nmx++] = T; cov |= T; }
  }
  /* F2, F3 */
  for (i = 0; i < nmx; i++) for (j = i + 1; j < nmx; j++) {
    int I = mx[i] & mx[j], s = pc(I);
    if (s == 0) { npairs[0]++; if (th[mx[i]] + th[mx[j]] > 4) viol[1]++; }
    else if (s == 1) { npairs[1]++; int a = __builtin_ctz(I); if (m[a] < th[mx[i]] + th[mx[j]]) viol[1]++; }
    else if (s == 2) { npairs[2]++; viol[1]++; }
    else {
      npairs[3]++;
      if (th[I] != 2 || th[mx[i]] != 1 || th[mx[j]] != 1) viol[1]++;
      int ismax2 = 1; for (v = 0; v < na; v++) if (!(I >> v & 1) && up2[I | 1 << v]) ismax2 = 0;
      if (!ismax2) viol[2]++;
      for (int k = 0; k < nmx; k++) {
        int J = mx[k] & I;
        if (pc(J) >= 2 && (mx[k] & I) != I) viol[2]++;
        if (pc(J) == 1 && m[__builtin_ctz(J)] != 3) viol[2]++;
      }
    }
  }
  if (cov == full) {
    if (covering) { nfailcov++; viol[3]++; }
    else nfailnon++;
    /* F5: minimal subcovers */
    if (nmx <= 22) {
      for (long sub = 1; sub < (1L << nmx); sub++) {
        int u = 0; for (i = 0; i < nmx; i++) if (sub >> i & 1) u |= mx[i];
        if (u != full) continue;
        int minimal = 1;
        for (i = 0; i < nmx && minimal; i++) if (sub >> i & 1) {
          int u2 = 0; for (j = 0; j < nmx; j++) if (j != i && (sub >> j & 1)) u2 |= mx[j];
          if (u2 == full) minimal = 0;
        }
        if (!minimal) continue;
        nsub++;
        int hubfree = 1;
        for (i = 0; i < nmx; i++) if (sub >> i & 1) for (j = i + 1; j < nmx; j++) if (sub >> j & 1)
          if (pc(mx[i] & mx[j]) >= 3) hubfree = 0;
        if (hubfree) { nsubhubfree++; viol[4]++; continue; }
        /* one-vertex petal y with w(y) = 3: a member T containing the hub K with T - K = {y} */
        int found = 0;
        for (i = 0; i < nmx && !found; i++) if (sub >> i & 1) for (j = 0; j < nmx && !found; j++)
          if (j != i && (sub >> j & 1) && pc(mx[i] & mx[j]) >= 3) {
            int K = mx[i] & mx[j], P = mx[i] & ~K;
            if (pc(P) == 1) { int y = __builtin_ctz(P); if (del[y] - m[y] == 3) found = 1; }
          }
        if (!found) { nsubnopetal3++; viol[5]++; }
      }
    }
  }
}
static void rec(int v, int left) {
  if (v == na) { if (left == 0) check_m(); return; }
  int cap = del[v] < 3 ? del[v] : 3;
  for (int x = 0; x <= cap && x <= left; x++) { m[v] = x; rec(v + 1, left - x); }
  m[v] = 0;
}
int main(void) {
  char line[4096];
  while (fgets(line, sizeof line, stdin)) {
    char *p = line; int k;
    if (sscanf(p, "%d %d%n", &na, &nc, &k) != 2) continue; p += k;
    if (na > MAXA || nc > MAXC || na != nc + 2) { fprintf(stderr, "bad block\n"); continue; }
    for (int j = 0; j < nc; j++) { sscanf(p, "%d%n", &msk[j], &k); p += k; }
    for (int v = 0; v < na; v++) { deg[v] = 0; for (int j = 0; j < nc; j++) deg[v] += msk[j] >> v & 1; del[v] = 6 - deg[v]; }
    int full = (1 << na) - 1;
    for (int T = 0; T <= full; T++) {
      int s = 4 - 4 * pc(T);
      for (int j = 0; j < nc; j++) { int e = pc(msk[j] & T); if (e > 2) s += e - 2; }
      base[T] = s;
    }
    nblock++;
    rec(0, 4);
  }
  printf("blocks %ld  multisets %ld (covering %ld)\n", nblock, nm, ncov);
  printf("pairs of maximal overloaded sets: disjoint %ld, one vertex %ld, two vertices %ld, >= 3 %ld\n",
         npairs[0], npairs[1], npairs[2], npairs[3]);
  printf("I_X empty: covering %ld, non-covering %ld; minimal subcovers checked %ld (hub-free %ld, no w=3 petal %ld)\n",
         nfailcov, nfailnon, nsub, nsubhubfree, nsubnopetal3);
  printf("viol F1 %ld F2 %ld F3 %ld F4 %ld F5a %ld F5b %ld\n", viol[0], viol[1], viol[2], viol[3], viol[4], viol[5]);
  return 0;
}
