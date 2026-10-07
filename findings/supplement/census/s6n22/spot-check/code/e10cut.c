/* e10cut.c (wave8/s6spot): exact minimum essential edge cut of every graph in a graph6 file.
 *
 * For each graph B on n <= 31 vertices: min |delta(S)| over all S with 2 <= |S| <= n - 2, by
 * Gray-code enumeration of every S that contains vertex 0 (each bipartition {S, V - S} once).
 * delta is updated in O(1) per step: adding v changes it by deg(v) - 2|N(v) & S|.
 * Checks on every graph (exit 3 on a violation): every degree equals -r (default 6), and with -b n1
 * every edge joins {0..n1-1} to {n1..n-1}.
 *
 * Output, one line per graph in input order:
 *   <index> <mincut> <|argmin S|> <argmin S as hex mask> <edge hash>
 * The edge hash is h = h * 1000003 + (64u + v) mod 2^64 over the edges u < v in (u, v) order,
 * starting from h = 0; spantest.py computes the same hash from its own decoder.
 * Summary on stderr: graphs read and the histogram of mincut values.
 *
 * Usage: e10cut [-r deg] [-b n1] file.g6 > file.cut
 * Shares no code with wave6/s6n22.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 31

static int decode_g6(const char *s, int *n_out, uint32_t *nb) {
  size_t len = strlen(s);
  while (len > 0 && (s[len - 1] == '\n' || s[len - 1] == '\r')) len--;
  if (len < 1) return -1;
  int n = s[0] - 63;
  if (n < 2 || n > MAXN) return -2;
  int nbits = n * (n - 1) / 2;
  int nchars = (nbits + 5) / 6;
  if ((int)len != 1 + nchars) return -3;
  for (int i = 0; i < n; i++) nb[i] = 0;
  int k = 0;
  for (int j = 1; j < n; j++) {
    for (int i = 0; i < j; i++, k++) {
      int c = s[1 + k / 6] - 63;
      if (c < 0 || c > 63) return -4;
      if ((c >> (5 - k % 6)) & 1) {
        nb[i] |= 1u << j;
        nb[j] |= 1u << i;
      }
    }
  }
  /* padding bits must be zero */
  for (; k < 6 * nchars; k++) {
    int c = s[1 + k / 6] - 63;
    if ((c >> (5 - k % 6)) & 1) return -5;
  }
  *n_out = n;
  return 0;
}

int main(int argc, char **argv) {
  int want_deg = 6, n1 = -1;
  const char *path = NULL;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "-r") && i + 1 < argc) want_deg = atoi(argv[++i]);
    else if (!strcmp(argv[i], "-b") && i + 1 < argc) n1 = atoi(argv[++i]);
    else path = argv[i];
  }
  if (!path) {
    fprintf(stderr, "usage: e10cut [-r deg] [-b n1] file.g6\n");
    return 2;
  }
  FILE *f = fopen(path, "r");
  if (!f) {
    perror(path);
    return 2;
  }
  static long hist[64 * MAXN];
  char line[512];
  long idx = 0;
  int maxcut_seen = 0;
  while (fgets(line, sizeof line, f)) {
    if (line[0] == '\n') continue;
    int n;
    uint32_t nb[MAXN];
    int rc = decode_g6(line, &n, nb);
    if (rc) {
      fprintf(stderr, "e10cut: bad graph6 at index %ld (code %d)\n", idx, rc);
      return 3;
    }
    int deg[MAXN];
    for (int v = 0; v < n; v++) {
      deg[v] = __builtin_popcount(nb[v]);
      if (want_deg >= 0 && deg[v] != want_deg) {
        fprintf(stderr, "e10cut: index %ld vertex %d has degree %d\n", idx, v, deg[v]);
        return 3;
      }
    }
    if (n1 > 0) {
      uint32_t lowm = (1u << n1) - 1u;
      for (int v = 0; v < n; v++) {
        uint32_t bad = (v < n1) ? (nb[v] & lowm) : (nb[v] & ~lowm);
        if (bad) {
          fprintf(stderr, "e10cut: index %ld edge inside a side at vertex %d\n", idx, v);
          return 3;
        }
      }
    }
    /* Gray code over vertices 1..n-1; vertex 0 always in S */
    uint32_t S = 1u;
    int size = 1, cut = deg[0];
    int best = 1 << 30;
    uint32_t bestS = 0;
    uint32_t total = 1u << (n - 1);
    for (uint32_t i = 1; i < total; i++) {
      int v = __builtin_ctz(i) + 1;
      uint32_t bit = 1u << v;
      /* v is not its own neighbour, so |N(v) & S| is the same before and after the toggle */
      int sgn = (S & bit) ? -1 : 1;
      cut += sgn * (deg[v] - 2 * __builtin_popcount(nb[v] & S));
      size += sgn;
      S ^= bit;
      if (cut < best && size >= 2 && size <= n - 2) {
        best = cut;
        bestS = S;
      }
    }
    /* internal consistency: the incremental cut must equal |delta(S)| recomputed directly for the
       final S (the reflected Gray code ends at {0, n-1}) and for the recorded argmin */
    for (int pass = 0; pass < 2; pass++) {
      uint32_t T = pass ? bestS : S;
      int want = pass ? best : cut, direct = 0;
      for (int v = 0; v < n; v++)
        if (T >> v & 1u) direct += __builtin_popcount(nb[v] & ~T);
      if (direct != want || (pass == 0 && S != (1u | (1u << (n - 1))))) {
        fprintf(stderr, "e10cut: consistency check failed at index %ld\n", idx);
        return 4;
      }
    }
    uint64_t h = 0;
    for (int u = 0; u < n; u++)
      for (int v = u + 1; v < n; v++)
        if (nb[u] >> v & 1u) h = h * 1000003ull + (uint64_t)(64 * u + v);
    printf("%ld %d %d %x %016llx\n", idx, best, __builtin_popcount(bestS), bestS,
           (unsigned long long)h);
    if (best >= 0 && best < 64 * MAXN) hist[best]++;
    if (best > maxcut_seen) maxcut_seen = best;
    idx++;
  }
  fclose(f);
  fprintf(stderr, "graphs=%ld mincut_hist=", idx);
  for (int c = 0; c <= maxcut_seen && c < 64 * MAXN; c++)
    if (hist[c]) fprintf(stderr, "%d:%ld,", c, hist[c]);
  fprintf(stderr, "\n");
  return 0;
}
