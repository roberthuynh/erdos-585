/* Local finite experiment for Erdos 585. No solver verdict is a Lean proof.
 * Each PRUNE call assumes the induced parent already passed, as documented
 * by geng. Therefore any new forbidden pair must contain vertex n-1.
 * A first cycle is enumerated explicitly. A second independent Hamiltonian
 * search uses its exact support and excludes every edge of the first cycle.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "gtools.h"
#define LIM 11
static uint16_t adj[LIM], core, blue[LIM];
static int root, order[LIM], first, found, size_now;
static uint64_t witness[2], witness_support;
static unsigned long long calls[12], rejects[12], red_trials;
static int pop(uint16_t x) { return __builtin_popcount((unsigned)x); }
static int low(uint16_t x) { return __builtin_ctz((unsigned)x); }
static uint64_t edge(int a,int b) {
    if(a>b){int t=a;a=b;b=t;}
    return UINT64_C(1) << (b*(b-1)/2+a);
}
static int blue_dfs(int last,uint16_t remaining,uint64_t edges) {
    if(!remaining) {
        if(blue[last] & (1u<<root)) {
            witness[1]=edges|edge(last,root);return 1;
        }
        return 0;
    }
    if(!(blue[last]&remaining) || !(blue[root]&remaining))return 0;
    uint16_t permitted=remaining|(1u<<last)|(1u<<root);
    for(uint16_t z=remaining;z;z&=z-1) {
        int v=low(z);
        if(pop(blue[v]&permitted)<2)return 0;
    }
    uint16_t options=blue[last]&remaining;
    while(options) {
        int v=low(options);options&=options-1;
        if(blue_dfs(v,remaining^(1u<<v),edges|edge(last,v)))return 1;
    }
    return 0;
}
static int try_red(int last,uint16_t used,uint64_t edges,int length) {
    if(length<5 || first>=last || !(adj[last]&(1u<<root)))return 0;
    for(uint16_t z=used;z;z&=z-1) {
        int v=low(z);
        if(pop(adj[v]&used)<4)return 0;
        blue[v]=adj[v]&used;
    }
    for(int i=0;i<length;i++) {
        int a=order[i],b=order[(i+1)%length];
        blue[a]&=~(1u<<b);blue[b]&=~(1u<<a);
    }
    ++red_trials;
    if(blue_dfs(root,used^(1u<<root),0)) {
        witness[0]=edges|edge(last,root);witness_support=used;return 1;
    }
    return 0;
}
static void red_dfs(int last,uint16_t used,uint64_t edges,int length) {
    if(try_red(last,used,edges,length)){found=1;return;}
    uint16_t choices=adj[last]&core&~used;
    while(choices && !found) {
        int v=low(choices);choices&=choices-1;
        order[length]=v;
        red_dfs(v,used|(1u<<v),edges|edge(last,v),length+1);
    }
}
static int detect(int n,int required) {
    core=(1u<<n)-1;
    int changed=1;
    while(changed) {
        changed=0;
        for(int v=0;v<n;v++)if((core>>v&1) && pop(adj[v]&core)<4) {
            core&=~(1u<<v);changed=1;
        }
    }
    if(pop(core)<5)return 0;
    uint16_t original=core;found=0;
    int start=required>=0?required:4,end=required>=0?required+1:n;
    for(root=start;root<end && !found;root++) {
        if(!(original>>root&1))continue;
        core=original&((1u<<(root+1))-1);order[0]=root;
        uint16_t choices=adj[root]&core;
        while(choices && !found) {
            first=low(choices);choices&=choices-1;order[1]=first;
            red_dfs(first,(1u<<root)|(1u<<first),edge(root,first),2);
        }
    }
    return found;
}
int erdos585_prune(graph *g,int n,int maxn) {
    (void)maxn;
    if(n>LIM){fprintf(stderr,"unsupported order\n");exit(2);}
    ++calls[n];
    for(int a=0;a<n;a++) {
        adj[a]=0;
        for(int b=0;b<n;b++)if(ISELEMENT(g+a,b))adj[a]|=1u<<b;
    }
    int r=detect(n,n-1);rejects[n]+=r;return r;
}
void erdos585_summary(nauty_counter nout,double cpu) {
    fprintf(stderr,"585 summary outputs=%llu cpu=%.3f red_trials=%llu\n",
        (unsigned long long)nout,cpu,red_trials);
    for(int n=1;n<=LIM;n++)if(calls[n])
        fprintf(stderr,"585 n=%d calls=%llu rejected=%llu\n",n,calls[n],rejects[n]);
}
#ifdef STANDALONE
/* Input: n decimal-edge-mask. Output: pair flag and explicit cycle masks. */
int main(void) {
    int n;unsigned long long mask;
    while(scanf("%d %llu",&n,&mask)==2) {
        if(n<1||n>LIM)return 2;
        memset(adj,0,sizeof adj);
        for(int b=1;b<n;b++)for(int a=0;a<b;a++)if(mask&edge(a,b)) {
            adj[a]|=1u<<b;adj[b]|=1u<<a;
        }
        int r=detect(n,-1);
        printf("%d %llu %llu %llu\n",r,r?(unsigned long long)witness_support:0,
            r?(unsigned long long)witness[0]:0,r?(unsigned long long)witness[1]:0);
    }
    return 0;
}
#endif
