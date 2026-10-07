/* gdl_small.c (lane qb5, round 2): exhaustive check that small 2-blocks are generic (NOTES.md section 6).
 * Build: /usr/bin/clang -O3 -o gdl_small gdl_small.c
 * Input: graph6 lines from  genbg -q -d6:0 -D6:6 c c+2 6c:6c  (first c vertices = small side C, all of
 *   degree 6; last c+2 = big side A).  Keeps blocks with every in-block degree d_a >= 3 that are sparse
 *   (every S with |S| >= 3 spans at most 3|S| - 6 edges; X is a proper subset of the E5 graph).
 * For every p in A and every A1 in A - p with |A1| <= |A| - 2 it computes k = dem(A1) =
 *   4|A1| - sum_c min(4, e(c, A1)) and, when k > |A1 n L| (L = {d_a = 3}), asks whether some admissible
 *   cut-degree vector makes A1 p-relevant: c_a in [max(0, delta_a - 2), min(3, delta_a)], sum c = 7,
 *   and c(A - p - A1) >= 5 - k  (delta_a = 6 - d_a).  Prints counts and the first such block.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint32_t u32;
static int n; static u32 adj[32];
static int parse(const char *s){
    n = s[0] - 63; if (n < 1 || n > 32) return 0;
    memset(adj, 0, sizeof adj); int bp = 0, len = strlen(s);
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
        int byte = 1 + bp / 6, off = 5 - bp % 6; bp++;
        if (byte >= len) return 0;
        if (((s[byte] - 63) >> off) & 1) { adj[i] |= 1u << j; adj[j] |= 1u << i; }
    }
    return 1;
}
static int sparse_all(void){
    u32 S = 0; int e = 0, sz = 0;
    for (uint64_t i = 1; i < (1ull << n); i++) {
        int v = __builtin_ctzll(i); u32 b = 1u << v;
        if (S & b) { S ^= b; sz--; e -= __builtin_popcount(adj[v] & S); }
        else { e += __builtin_popcount(adj[v] & S); S ^= b; sz++; }
        if (sz >= 3 && e > 3 * sz - 6) return 0;
    }
    return 1;
}
int main(int argc, char **argv){
    int c = atoi(argv[1]); char line[256];
    long blocks = 0, kept = 0, nongen = 0, relevant = 0, relblocks = 0;
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, " \r\n")] = 0; if (!parse(line)) continue;
        blocks++;
        int na = n - c; int d[32], ok = 1;
        for (int i = 0; i < na; i++) { d[i] = __builtin_popcount(adj[c + i]); if (d[i] < 3) ok = 0; }
        if (!ok || !sparse_all()) continue;
        kept++;
        u32 L = 0; for (int i = 0; i < na; i++) if (d[i] == 3) L |= 1u << i;
        int lo[32], hi[32], slo = 0, shi = 0;
        for (int i = 0; i < na; i++) { int dl = 6 - d[i]; lo[i] = dl - 2 > 0 ? dl - 2 : 0; hi[i] = dl < 3 ? dl : 3; slo += lo[i]; shi += hi[i]; }
        if (slo > 7 || shi < 7) continue; /* no admissible cut-degree vector */
        u32 nbA[32]; for (int j = 0; j < c; j++) nbA[j] = adj[j] >> c; /* neighbourhoods of C in A-bits */
        int blockrel = 0;
        for (u32 A1 = 0; A1 < (1u << na); A1++) {
            int sz = __builtin_popcount(A1); if (sz > na - 2) continue;
            int sup = 0; for (int j = 0; j < c; j++) { int e = __builtin_popcount(nbA[j] & A1); sup += e < 4 ? e : 4; }
            int k = 4 * sz - sup; if (k <= __builtin_popcount(A1 & L)) continue;
            nongen++;
            for (int p = 0; p < na; p++) {
                if (A1 >> p & 1) continue;
                u32 R = ((1u << na) - 1) & ~A1 & ~(1u << p); /* A - p - A1 */
                /* max c(R) subject to box and sum 7: min(sum_hi(R), 7 - sum_lo(not R)) */
                int hR = 0, loNot = 0; for (int i = 0; i < na; i++) { if (R >> i & 1) hR += hi[i]; else loNot += lo[i]; }
                int mx = hR < 7 - loNot ? hR : 7 - loNot;
                if (mx >= 5 - k) {
                    relevant++; blockrel = 1;
                    if (relevant <= 3) printf("relevant non-generic: %s p=%d A1=0x%x k=%d\n", line, c + p, A1, k);
                }
            }
        }
        relblocks += blockrel;
    }
    printf("c=%d blocks=%ld sparse_with_d>=3=%ld nongeneric_groups=%ld relevant(p,A1)=%ld blocks_with_relevant=%ld\n",
           c, blocks, kept, nongen, relevant, relblocks);
    return 0;
}
