/* Fresh cycle-pair decider, finite-upper-11-12 lane, 2026-10-07.
 * No earlier solver source is included or copied.
 * Enumerates supports, first Hamilton cycles, then residual Hamilton cycles.
 * Supports use actual vertex indices and every reported cycle is connected.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#define NMAX 12
static uint32_t adj[NMAX], residual[NMAX];
static int n, k, anchor, first[NMAX], second[NMAX], found1[NMAX], found2[NMAX];
static uint64_t supports, first_cycles;
static int pc(uint32_t x) { return __builtin_popcount(x); }
static int lb(uint32_t x) { return __builtin_ctz(x); }
static int residual_cycle(int depth, uint32_t left) {
    int v=second[depth-1];
    if (!left) return !!(residual[v] & (1u<<anchor));
    /* In a completion, an unvisited vertex can use only unvisited vertices
     * and the two current path endpoints. This is a necessary condition. */
    for (uint32_t scan=left; scan; scan&=scan-1) {
        int u=lb(scan);
        int avail=pc(residual[u]&left) + !!(residual[u]&(1u<<v))
                  + !!(residual[u]&(1u<<anchor));
        if (avail<2) return 0;
    }
    uint32_t choices=residual[v]&left;
    while (choices) {
        int u=lb(choices); choices &= choices-1;
        second[depth]=u;
        if (residual_cycle(depth+1,left&~(1u<<u))) return 1;
    }
    return 0;
}
static int first_cycle(int depth, uint32_t left) {
    int v=first[depth-1];
    if (!left) {
        if (!(adj[v]&(1u<<anchor)) || first[1]>first[k-1]) return 0;
        ++first_cycles;
        memcpy(residual,adj,sizeof(adj));
        for (int i=0;i<k;i++) {
            int a=first[i], b=first[(i+1)%k];
            residual[a]&=~(1u<<b); residual[b]&=~(1u<<a);
        }
        uint32_t all=0; for(int i=0;i<k;i++) all|=1u<<first[i];
        second[0]=anchor;
        if (!residual_cycle(1,all&~(1u<<anchor))) return 0;
        memcpy(found1,first,k*sizeof(int)); memcpy(found2,second,k*sizeof(int));
        return 1;
    }
    uint32_t choices=adj[v]&left;
    while (choices) {
        int u=lb(choices); choices &= choices-1;
        first[depth]=u;
        if (first_cycle(depth+1,left&~(1u<<u))) return 1;
    }
    return 0;
}
static int pair(void) {
    uint32_t bound=1u<<n;
    for (k=5;k<=n;k++) for(uint32_t s=1;s<bound;s++) {
        if(pc(s)!=k) continue;
        int eligible=1;
        for(uint32_t scan=s;scan;scan&=scan-1) if(pc(adj[lb(scan)]&s)<4) {
            eligible=0; break;
        }
        if (!eligible) continue;
        ++supports; anchor=lb(s); first[0]=anchor;
        if(first_cycle(1,s&~(1u<<anchor))) return 1;
    }
    return 0;
}
static int decode(const char *line) {
    const unsigned char *p=(const unsigned char *)line;
    if(strncmp(line,">>graph6<<",10)==0) p+=10;
    n=*p++-63;
    if(n<0||n>NMAX) return 0;
    memset(adj,0,sizeof(adj));
    int need=n*(n-1)/2, pos=0, word=0;
    for(int j=1;j<n;j++) for(int i=0;i<j;i++,pos++) {
        if(pos%6==0) {if(*p<63||*p>126) return 0;word=*p++-63;}
        if(word&(1<<(5-pos%6))) {adj[i]|=1u<<j;adj[j]|=1u<<i;}
    }
    (void)need;
    return *p=='\0'||*p=='\n'||*p=='\r';
}
int main(int argc,char **argv) {
    FILE *cert=NULL;
    if(argc==3 && strcmp(argv[1],"--cert")==0) {
        cert=fopen(argv[2],"w"); if(!cert){perror(argv[2]);return 2;}
    } else if(argc!=1) {fprintf(stderr,"usage: pair_decider [--cert FILE] < graph6\n");return 2;}
    char line[128]; uint64_t seen=0,yes=0,no=0;
    clock_t start=clock();
    while(fgets(line,sizeof(line),stdin)) {
        if(line[0]=='\n'||line[0]=='\r')continue;
        if(strcmp(line,">>graph6<<\n")==0)continue;
        ++seen;
        if(!decode(line)){fprintf(stderr,"bad graph6 at line %llu\n",(unsigned long long)seen);return 2;}
        if(pair()) {
            ++yes;
            if(cert) {
                fprintf(cert,"%llu\t%d\t",(unsigned long long)seen,k);
                for(int i=0;i<k;i++) fprintf(cert,"%s%d",i?",":"",found1[i]);
                fprintf(cert,"\t");
                for(int i=0;i<k;i++) fprintf(cert,"%s%d",i?",":"",found2[i]);
                fputc('\n',cert);
            }
        } else {++no;fputs(line,stdout);}
        if(seen%100000==0) {
            fprintf(stderr,"progress seen=%llu pair=%llu free=%llu cpu=%.3f\n",
              (unsigned long long)seen,(unsigned long long)yes,(unsigned long long)no,
              (double)(clock()-start)/CLOCKS_PER_SEC);fflush(stderr);
        }
    }
    if(ferror(stdin)||ferror(stdout)){fprintf(stderr,"stream error\n");return 2;}
    if(cert && fclose(cert)!=0)return 2;
    fprintf(stderr,"complete seen=%llu pair=%llu free=%llu supports=%llu first_cycles=%llu cpu=%.6f\n",
        (unsigned long long)seen,(unsigned long long)yes,(unsigned long long)no,
        (unsigned long long)supports,(unsigned long long)first_cycles,
        (double)(clock()-start)/CLOCKS_PER_SEC);
    return 0;
}
