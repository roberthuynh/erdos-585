/* bipcensus.c (referee's own code, wave4/theory review).
 * Exhaustive census of bipartite graphs with fixed colour classes P (np vertices) and Q (nq
 * vertices) and e edges, emin <= e <= emax: every labelled subgraph of K_{np,nq} with that many
 * edges is generated (missing-edge subsets), tested for a pair (two edge-disjoint cycles on the
 * same vertex set) by two independent methods, and reduced to colour-preserving isomorphism
 * classes by a canonical form (min over column permutations of the sorted row masks).
 * Method A: enumerate all cycles of G by DFS, group by vertex set, look for an edge-disjoint pair.
 * Method B: precompute all minimal "pair masks" (union of two edge-disjoint cycles with the same
 *           vertex set) of K_{np,nq} and test containment.
 * Also reports whether G contains K_{4,4}.
 * Usage: bipcensus np nq emin emax
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int NP, NQ, NV, NE;
typedef struct { uint32_t vm; uint64_t em; } cyc_t;

static cyc_t *cyc; static size_t ncyc, capcyc;
static uint32_t adj[16];
static int path[16];
static uint64_t pathem[16];

static inline int eidx(int p, int q) { return p * NQ + (q - NP); }
static inline uint64_t ebit(int u, int v) {
  int p = u < NP ? u : v, q = u < NP ? v : u;
  return 1ULL << eidx(p, q);
}

static void push_cyc(uint32_t vm, uint64_t em) {
  if (ncyc == capcyc) { capcyc = capcyc ? 2 * capcyc : 4096; cyc = realloc(cyc, capcyc * sizeof(cyc_t)); }
  cyc[ncyc].vm = vm; cyc[ncyc].em = em; ncyc++;
}

/* DFS from start s, current vertex path[d-1], vertices used in vm, only vertices > s */
static void dfs(int s, int d, uint32_t vm, uint64_t em) {
  int u = path[d - 1];
  uint32_t nb = adj[u];
  for (int v = s + 1; v < NV; v++) {
    if (!(nb >> v & 1)) continue;
    if (vm >> v & 1) continue;
    path[d] = v;
    dfs(s, d + 1, vm | (1u << v), em | ebit(u, v));
  }
  /* close the cycle */
  if (d >= 4 && (adj[u] >> s & 1)) {
    if (path[1] < path[d - 1]) push_cyc(vm, em | ebit(u, s));
  }
}

static void all_cycles(void) {
  ncyc = 0;
  for (int s = 0; s < NV; s++) { path[0] = s; dfs(s, 1, 1u << s, 0); }
}

static int cmpcyc(const void *a, const void *b) {
  const cyc_t *x = a, *y = b;
  if (x->vm != y->vm) return x->vm < y->vm ? -1 : 1;
  return x->em < y->em ? -1 : (x->em > y->em);
}

static void build_adj(uint64_t g) {
  memset(adj, 0, sizeof(adj));
  for (int p = 0; p < NP; p++) for (int j = 0; j < NQ; j++) if (g >> (p * NQ + j) & 1) {
    adj[p] |= 1u << (NP + j); adj[NP + j] |= 1u << p;
  }
}

static int has_pair_A(uint64_t g) {
  build_adj(g);
  all_cycles();
  qsort(cyc, ncyc, sizeof(cyc_t), cmpcyc);
  size_t i = 0;
  while (i < ncyc) {
    size_t j = i;
    while (j < ncyc && cyc[j].vm == cyc[i].vm) j++;
    for (size_t a = i; a < j; a++) for (size_t b = a + 1; b < j; b++)
      if ((cyc[a].em & cyc[b].em) == 0) return 1;
    i = j;
  }
  return 0;
}

static uint64_t *pm; static size_t npm;
static int cmpu64(const void *a, const void *b) {
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b; return x < y ? -1 : (x > y);
}
static void build_pair_masks(void) {
  uint64_t full = (NE == 64) ? ~0ULL : ((1ULL << NE) - 1);
  build_adj(full); all_cycles();
  qsort(cyc, ncyc, sizeof(cyc_t), cmpcyc);
  size_t cap = 1 << 16; pm = malloc(cap * sizeof(uint64_t)); npm = 0;
  size_t i = 0;
  while (i < ncyc) {
    size_t j = i;
    while (j < ncyc && cyc[j].vm == cyc[i].vm) j++;
    for (size_t a = i; a < j; a++) for (size_t b = a + 1; b < j; b++)
      if ((cyc[a].em & cyc[b].em) == 0) {
        if (npm == cap) { cap *= 2; pm = realloc(pm, cap * sizeof(uint64_t)); }
        pm[npm++] = cyc[a].em | cyc[b].em;
      }
    i = j;
  }
  qsort(pm, npm, sizeof(uint64_t), cmpu64);
  size_t k = 0;
  for (size_t a = 0; a < npm; a++) if (a == 0 || pm[a] != pm[a - 1]) pm[k++] = pm[a];
  npm = k;
  /* keep minimal masks only */
  char *dead = calloc(npm, 1);
  for (size_t a = 0; a < npm; a++) for (size_t b = 0; b < npm; b++)
    if (a != b && !dead[b] && (pm[b] & pm[a]) == pm[b] && pm[b] != pm[a]) { dead[a] = 1; break; }
  k = 0;
  for (size_t a = 0; a < npm; a++) if (!dead[a]) pm[k++] = pm[a];
  npm = k; free(dead);
  fprintf(stderr, "K_{%d,%d}: %zu cycles, %zu minimal pair masks\n", NP, NQ, ncyc, npm);
}
static int has_pair_B(uint64_t g) {
  for (size_t a = 0; a < npm; a++) if ((pm[a] & g) == pm[a]) return 1;
  return 0;
}

static int has_k44(uint64_t g) {
  /* rows as NQ-bit masks; need 4 rows whose common neighbourhood has >= 4 columns */
  uint32_t row[8];
  for (int p = 0; p < NP; p++) row[p] = (uint32_t)((g >> (p * NQ)) & ((1u << NQ) - 1));
  for (uint32_t s = 0; s < (1u << NP); s++) {
    if (__builtin_popcount(s) != 4) continue;
    uint32_t c = (1u << NQ) - 1;
    for (int p = 0; p < NP; p++) if (s >> p & 1) c &= row[p];
    if (__builtin_popcount(c) >= 4) return 1;
  }
  return 0;
}

/* canonical form under S_NP x S_NQ: min over column permutations of sorted rows */
static int perms[5040][7]; static int nperm;
static void gen_perms(int k) {
  int a[7]; for (int i = 0; i < k; i++) a[i] = i;
  nperm = 0;
  for (;;) {
    memcpy(perms[nperm++], a, sizeof(a));
    int i = k - 2; while (i >= 0 && a[i] > a[i + 1]) i--;
    if (i < 0) break;
    int j = k - 1; while (a[j] < a[i]) j--;
    int t = a[i]; a[i] = a[j]; a[j] = t;
    for (int l = i + 1, r = k - 1; l < r; l++, r--) { t = a[l]; a[l] = a[r]; a[r] = t; }
  }
}
static uint64_t canon(uint64_t g) {
  uint64_t best = ~0ULL;
  uint32_t row[8], r2[8];
  for (int p = 0; p < NP; p++) row[p] = (uint32_t)((g >> (p * NQ)) & ((1u << NQ) - 1));
  for (int t = 0; t < nperm; t++) {
    for (int p = 0; p < NP; p++) {
      uint32_t x = 0;
      for (int j = 0; j < NQ; j++) if (row[p] >> j & 1) x |= 1u << perms[t][j];
      r2[p] = x;
    }
    /* insertion sort descending */
    for (int a = 1; a < NP; a++) { uint32_t x = r2[a]; int b = a - 1; while (b >= 0 && r2[b] < x) { r2[b + 1] = r2[b]; b--; } r2[b + 1] = x; }
    uint64_t c = 0;
    for (int p = 0; p < NP; p++) c = (c << NQ) | r2[p];
    if (c < best) best = c;
  }
  return best;
}

int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: bipcensus np nq emin emax\n"); return 1; }
  NP = atoi(argv[1]); NQ = atoi(argv[2]); NV = NP + NQ; NE = NP * NQ;
  int emin = atoi(argv[3]), emax = atoi(argv[4]);
  int nopair = (argc > 5 && strcmp(argv[5], "nopair") == 0);
  gen_perms(NQ);
  build_pair_masks();
  uint64_t full = (NE == 64) ? ~0ULL : ((1ULL << NE) - 1);
  for (int e = emax; e >= emin; e--) {
    int miss = NE - e;
    /* iterate over all subsets of size miss of NE edges (Gosper) */
    long nlab = 0, nlab_pf = 0, disagree = 0, nk44 = 0, pf_with_k44 = 0;
    size_t capc = 1 << 20, nc = 0, ncpf = 0;
    uint64_t *cf = malloc(capc * 8), *cfpf = malloc(capc * 8);
    uint64_t m = miss ? ((1ULL << miss) - 1) : 0;
    for (;;) {
      uint64_t g = full & ~m;
      int a = nopair ? 1 : has_pair_A(g), b = nopair ? 1 : has_pair_B(g), k = has_k44(g);
      nlab++; if (a != b) disagree++;
      if (k) nk44++;
      if (!a) { nlab_pf++; if (k) pf_with_k44++; }
      uint64_t c = canon(g);
      if (nc == capc) { capc *= 2; cf = realloc(cf, capc * 8); cfpf = realloc(cfpf, capc * 8); }
      cf[nc++] = c; if (!a) cfpf[ncpf++] = c;
      if (miss == 0) break;
      uint64_t lo = m & -m, r = m + lo;
      m = (((r ^ m) >> 2) / lo) | r;
      if (m >> NE) break;
    }
    qsort(cf, nc, 8, cmpu64); qsort(cfpf, ncpf, 8, cmpu64);
    size_t niso = 0, nisopf = 0;
    for (size_t i = 0; i < nc; i++) if (i == 0 || cf[i] != cf[i - 1]) niso++;
    for (size_t i = 0; i < ncpf; i++) if (i == 0 || cfpf[i] != cfpf[i - 1]) nisopf++;
    printf("np=%d nq=%d e=%d labelled=%ld labelled_pairfree=%ld methodA_vs_B_disagree=%ld "
           "labelled_with_K44=%ld pairfree_with_K44=%ld iso_classes=%zu iso_pairfree=%zu\n",
           NP, NQ, e, nlab, nlab_pf, disagree, nk44, pf_with_k44, niso, nisopf);
    fflush(stdout);
    free(cf); free(cfpf);
  }
  return 0;
}
