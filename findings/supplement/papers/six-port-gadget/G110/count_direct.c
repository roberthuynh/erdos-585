/* Reviewer-written exhaustive row-choice counter. No memoization or library. */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

static int n, a[10][10], degree[10], opts[10][128], nopts[10];
static uint64_t answer, nodes;

static void visit(int r) {
    ++nodes;
    if (r == n) {
        for (int c=0;c<n;++c) if (degree[c] != 3) return;
        ++answer;
        return;
    }
    for (int k=0;k<nopts[r];++k) {
        int mask=opts[r][k], ok=1;
        for (int c=0;c<n;++c)
            if ((mask & (1<<c)) && degree[c] >= 3) ok=0;
        if (!ok) continue;
        for (int c=0;c<n;++c) if (mask & (1<<c)) ++degree[c];
        visit(r+1);
        for (int c=0;c<n;++c) if (mask & (1<<c)) --degree[c];
    }
}

int main(void) {
    if (scanf("%d", &n)!=1 || n<1 || n>9) return 2;
    for (int r=0;r<n;++r) {
        int neighbors=0;
        for (int c=0;c<n;++c) {
            if (scanf("%d", &a[r][c])!=1 || (a[r][c]!=0 && a[r][c]!=1)) return 3;
            if (a[r][c]) neighbors |= 1<<c;
        }
        for (int mask=0;mask<(1<<n);++mask)
            if ((mask & ~neighbors)==0 && __builtin_popcount((unsigned)mask)==3)
                opts[r][nopts[r]++]=mask;
    }
    visit(0);
    printf("%llu %llu\n", (unsigned long long)answer, (unsigned long long)nodes);
    return 0;
}
