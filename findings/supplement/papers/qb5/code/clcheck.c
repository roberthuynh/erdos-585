/* clcheck.c: test the chain of Theorem 5.1 (lane qb5) on C2 instances, exhaustively over vertex sets.
 * For each graph6 C2 instance (n <= 24): sparsity (min g over 3 <= |S| <= n-1), Z_U, whether a
 * W-small 2-block contains Z_U (g = 12, kappa = 2), the bad ports and their petal types, and:
 *  (A) every petal of a bad port is alpha, beta1a or gamma;
 *  (B) the union of all alpha petals of ports has g = 12, kappa = 1 (when no such 2-block);
 *  (D) two beta1a petals of distinct ports meet exactly in Z_U (when no such 2-block);
 *  (CL) bad ports carry deficiency <= 5 (when Z_U = {u1,u2} and no such 2-block).
 * Prints one line per graph with -v, a line per failure always, and a summary on stderr. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned int u32;
static int n; static u32 A[32];
static int parse(const char *s){
    n = s[0]-63; if(n<1||n>24) return 0;
    memset(A,0,sizeof A);
    int bit=0; const char *p=s+1; int val=0;
    for(int j=1;j<n;j++) for(int i=0;i<j;i++){
        if(bit==0){ val=*p++-63; bit=6; }
        bit--; if((val>>bit)&1){ A[i]|=1u<<j; A[j]|=1u<<i; }
    }
    return 1;
}
static int *eS; static int *dW;
#define MAXP 4096
int main(int argc,char**argv){
    int verbose = (argc>1 && !strcmp(argv[1],"-v"));
    eS = malloc(sizeof(int)<<24); dW = malloc(sizeof(int)<<24);
    char line[512];
    long long ng=0, nsparse=0, nu0=0, nu12=0, nw2b=0, nclapplies=0, nclok=0, nfailA=0, nfailB=0, nfailD=0;
    long long nalphaports=0, nbetaonly=0, hist[9]={0}, histw[9]={0}, nclp=0, nclpok=0;
    static u32 alphaQ[MAXP]; static u32 b1aQ[MAXP]; static int b1aport[MAXP];
    while(fgets(line,sizeof line,stdin)){
        line[strcspn(line,"\r\n")]=0; if(!parse(line)) continue; ng++;
        int col[32]; for(int i=0;i<n;i++) col[i]=-1;
        int ok=1; col[0]=0; int stack[32], sp=0; stack[sp++]=0;
        while(sp){ int v=stack[--sp]; for(int u=0;u<n;u++) if(A[v]>>u&1){ if(col[u]<0){col[u]=1-col[v]; stack[sp++]=u;} else if(col[u]==col[v]) ok=0; } }
        for(int i=0;i<n;i++) if(col[i]<0) ok=0;
        if(!ok) continue;
        u32 c0=0,c1=0; for(int i=0;i<n;i++){ if(col[i]) c1|=1u<<i; else c0|=1u<<i; }
        int n0=__builtin_popcount(c0), n1=__builtin_popcount(c1);
        if(abs(n0-n1)!=1) continue;
        u32 Um = n0<n1?c0:c1, Wm = n0<n1?c1:c0;
        int deg[32]; for(int i=0;i<n;i++) deg[i]=__builtin_popcount(A[i]);
        u32 ZU=0; int DU=0; for(int i=0;i<n;i++) if(Um>>i&1){ DU+=6-deg[i]; if(deg[i]<6) ZU|=1u<<i; }
        if(DU!=2) continue;
        int isu0 = (__builtin_popcount(ZU)==1);
        u32 ports=0; for(int i=0;i<n;i++) if((Wm>>i&1)&&deg[i]<=5) ports|=1u<<i;
        u32 full=(1u<<n)-1;
        eS[0]=0; dW[0]=0;
        int ming=1000, w2b=0;
        u32 badports=0; int ptypes[32]; memset(ptypes,0,sizeof ptypes);
        int na=0, nb=0;
        for(u32 S=1; S<=full; S++){
            int lo=__builtin_ctz(S); u32 rest=S&(S-1);
            eS[S]=eS[rest]+__builtin_popcount(A[lo]&rest);
            dW[S]=dW[rest]+((Wm>>lo&1)?deg[lo]:0);
            int sz=__builtin_popcount(S), sW=__builtin_popcount(S&Wm), sU=sz-sW;
            if(S!=full && sz>=3){
                int g=6*sz-2*eS[S]; if(g<ming) ming=g;
                if(g==12 && sU-sW==2 && (S&ZU)==ZU) w2b=1;
            }
            u32 avoidp = ports & ~S;
            if(!avoidp) continue;
            int f = dW[S]-eS[S]-4*sW+4*sU;
            if(f>=0) continue;
            badports |= avoidp;
            u32 Q=full&~S; int qsz=__builtin_popcount(Q), k=sW-sU, DC=0;
            for(u32 o=S&Um;o;o&=o-1) DC+=6-deg[__builtin_ctz(o)];
            int t; /* 0 gamma 1 alpha 2 beta1a 3 other */
            if(qsz==2) t=0; else if(k==2&&f==-1&&DC==0) t=1; else if(k==3&&f==-1&&DC==0) t=2; else t=3;
            for(u32 o=avoidp;o;o&=o-1) ptypes[__builtin_ctz(o)]|=1<<t;
            if(t==1 && na<MAXP) alphaQ[na++]=Q;
            if(t==2 && nb<MAXP){ b1aQ[nb]=Q; b1aport[nb]=__builtin_ctz(avoidp); nb++; }
        }
        if(ming<12) continue;
        nsparse++;
        if(isu0) nu0++; else nu12++;
        if(w2b) nw2b++;
        int Dbad=0; for(u32 o=badports;o;o&=o-1) Dbad+=6-deg[__builtin_ctz(o)];
        if(Dbad<=8){ if(w2b && !isu0) histw[Dbad]++; else if(!isu0) hist[Dbad]++; }
        if(!isu0){ nclp++; if(Dbad<=6) nclpok++; else printf("FAIL(CL') %s Dbad=%d\n",line,Dbad); }
        int failA=0; for(int i=0;i<n;i++) if(badports>>i&1) if(ptypes[i]&8) failA=1;
        if(failA){ nfailA++; printf("FAIL(A) %s\n",line); }
        /* alpha-only and beta-only ports */
        u32 alphaports=0, betaonly=0;
        for(int i=0;i<n;i++) if(badports>>i&1){ if(ptypes[i]&2) alphaports|=1u<<i; else if(ptypes[i]&4) betaonly|=1u<<i; }
        nalphaports += __builtin_popcount(alphaports); nbetaonly += __builtin_popcount(betaonly);
        if(!isu0 && !w2b){
            nclapplies++;
            if(Dbad<=5) nclok++; else printf("FAIL(CL) %s Dbad=%d\n",line,Dbad);
            if(na>0){
                u32 R=0; for(int i=0;i<na;i++) R|=alphaQ[i];
                int kR=__builtin_popcount(R&Um)-__builtin_popcount(R&Wm);
                int gR=6*__builtin_popcount(R)-2*eS[R];
                if(!(kR==1 && gR==12 && R!=full)){ nfailB++; printf("FAIL(B) %s kR=%d gR=%d\n",line,kR,gR); }
            }
            for(int i=0;i<nb;i++) for(int j=i+1;j<nb;j++){
                if(b1aport[i]==b1aport[j]) continue;
                if(!((betaonly>>b1aport[i]&1)&&(betaonly>>b1aport[j]&1))) continue;
                if((b1aQ[i]&b1aQ[j])!=ZU){ nfailD++; printf("FAIL(D) %s\n",line); i=nb; break; }
            }
        }
        if(verbose) printf("%s sparse u0=%d w2block=%d badports=%d Dbad=%d alpha-ports=%d beta-only=%d nalphaQ=%d nb1aQ=%d\n",
            line,isu0,w2b,__builtin_popcount(badports),Dbad,__builtin_popcount(alphaports),__builtin_popcount(betaonly),na,nb);
    }
    fprintf(stderr,"graphs %lld sparse C2 %lld (u0 %lld, u1u2 %lld), with W-small 2-block on Z_U %lld\n",ng,nsparse,nu0,nu12,nw2b);
    fprintf(stderr,"(CL) applies %lld, holds %lld; FAIL A %lld B %lld D %lld; alpha-ports %lld beta1a-only ports %lld\n",
        nclapplies,nclok,nfailA,nfailB,nfailD,nalphaports,nbetaonly);
    fprintf(stderr,"(CL') u1u2 instances %lld, bad-port deficiency <= 6 in %lld\n",nclp,nclpok);
    fprintf(stderr,"bad-port deficiency 0..8, u1u2 without W-small 2-block on Z_U:"); for(int i=0;i<=8;i++) fprintf(stderr," %lld",hist[i]); fprintf(stderr,"\n");
    fprintf(stderr,"bad-port deficiency 0..8, u1u2 with W-small 2-block on Z_U:"); for(int i=0;i<=8;i++) fprintf(stderr," %lld",histw[i]); fprintf(stderr,"\n");
    return 0;
}
