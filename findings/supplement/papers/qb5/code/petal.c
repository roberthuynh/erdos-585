/* petal.c: QB(5) petal and tight-set analyzer (lane qb5, wave 4).
 *
 * Input: graph6 lines on stdin, bipartite, n <= 24. Sides by BFS 2-colouring (graphs are connected).
 * For a C2 instance (sides s, s+1; U = smaller side) it computes, by exhaustive enumeration of all
 * vertex sets S, the slack f(S) = e(S_W, U - S_U) - 4(|S_W| - |S_U|). For w in W - S, f(S) is the
 * slack of (S_W, S_U) in the balanced graph G - w (C1-PAPER Lemma 1.4), so w is "bad" (G - w has no
 * 4-factor) iff some S avoiding w has f(S) < 0. Each violating S is typed by its complement
 * Q = V - S: k = |S_W| - |S_U|, sigma = f(S), D(C) = deficiency of S_U, g(Q), kappa(Q):
 *   gamma: |Q| = 2;  alpha: k=2, sigma=-1, D(C)=0;  beta1a: k=3, sigma=-1, D(C)=0;
 *   beta1b: k=3, sigma=-1, D(C)=1;  beta2: k=3, sigma=-2;  other: anything else.
 * It also lists all sets with 3 <= |S| <= n-1 and g(S) = 6|S| - 2e(S) <= 12 (sparsity check and
 * tight sets by kappa). For an E5 instance (equal sides) it decides whether G has a 4-factor the
 * same way (f over all S, sides P = colour 0).
 *
 * Output: one line per graph (with -v) and a summary on stderr.
 * Usage: petal [-v] [-a] < file.g6     (-a: print only graphs with every W-vertex bad or a 2-block)
 */
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
enum {T_GAMMA, T_ALPHA, T_B1A, T_B1B, T_B2, T_OTHER, NT};
static const char *TN[NT]={"gamma","alpha","beta1a","beta1b","beta2","other"};
int main(int argc,char**argv){
    int verbose=0, onlyinteresting=0;
    for(int i=1;i<argc;i++){ if(!strcmp(argv[i],"-v")) verbose=1; else if(!strcmp(argv[i],"-a")) onlyinteresting=1; }
    eS = malloc(sizeof(int)<<24); dW = malloc(sizeof(int)<<24);
    char line[512];
    long long ng=0, nC2=0, nE5=0, nother=0, nsparse_fail=0, nallbad=0, nportsbad=0, nE5no4f=0;
    long long wtypecount[1<<NT]; memset(wtypecount,0,sizeof wtypecount);
    long long tightk[5]={0}, g_with_2block=0, nbadw=0, ngoodw=0;
    long long nu0inst=0, nu0fail=0, nu12inst=0, nu12fail=0;
    long long nalphag=0, nalpha_union_bad=0, nunion_ok=0, splits[3]={0,0,0}, spother=0, ngsplit=0;
    while(fgets(line,sizeof line,stdin)){
        line[strcspn(line,"\r\n")]=0; if(!parse(line)) continue; ng++;
        /* 2-colour */
        int col[32]; for(int i=0;i<n;i++) col[i]=-1;
        int ok=1; col[0]=0; int stack[32], sp=0; stack[sp++]=0;
        while(sp){ int v=stack[--sp]; for(int u=0;u<n;u++) if(A[v]>>u&1){ if(col[u]<0){col[u]=1-col[v]; stack[sp++]=u;} else if(col[u]==col[v]) ok=0; } }
        for(int i=0;i<n;i++) if(col[i]<0) ok=0;
        if(!ok){ nother++; continue; }
        u32 c0=0,c1=0; for(int i=0;i<n;i++){ if(col[i]) c1|=1u<<i; else c0|=1u<<i; }
        int n0=__builtin_popcount(c0), n1=__builtin_popcount(c1);
        u32 Um, Wm; int isC2;
        if(n0==n1){ isC2=0; Um=c1; Wm=c0; nE5++; }
        else if(abs(n0-n1)==1){ isC2=1; if(n0<n1){Um=c0;Wm=c1;} else {Um=c1;Wm=c0;} nC2++; }
        else { nother++; continue; }
        int deg[32]; for(int i=0;i<n;i++) deg[i]=__builtin_popcount(A[i]);
        u32 full=(n==32)?0xffffffffu:((1u<<n)-1);
        /* DP: e(S), degree sum over S_W, deficiency sum over S_U */
        eS[0]=0; dW[0]=0;
        int mingproper=1000; int tk[5]={0}; int has2block=0;
        int minf_all=1000;
        u32 badmask=0; int wtypes[32]; memset(wtypes,0,sizeof wtypes);
        u32 Ru[NT]; memset(Ru,0,sizeof Ru); static u32 alist[1<<16]; int na=0;
        for(u32 S=1; S<=full; S++){
            int lo=__builtin_ctz(S); u32 rest=S&(S-1);
            eS[S]=eS[rest]+__builtin_popcount(A[lo]&rest);
            dW[S]=dW[rest]+((Wm>>lo&1)?deg[lo]:0);
            int sz=__builtin_popcount(S);
            int sW=__builtin_popcount(S&Wm), sU=sz-sW;
            int f = dW[S]-eS[S]-4*sW+4*sU;
            if(S!=full && sz>=3){
                int g=6*sz-2*eS[S];
                if(g<mingproper) mingproper=g;
                if(g==12){ int kap=sU-sW; if(kap>=-2&&kap<=2) tk[kap+2]++; if(kap==2||kap==-2) has2block=1; }
            }
            if(isC2){
                u32 avoid = Wm & ~S;
                if(f<0 && avoid){
                    badmask|=avoid;
                    /* type */
                    u32 Q=full&~S; int qsz=__builtin_popcount(Q);
                    int k=sW-sU; int DC=0; for(u32 o=S&Um;o;o&=o-1){int v=__builtin_ctz(o); DC+=6-deg[v];}
                    int t;
                    if(qsz==2) t=T_GAMMA;
                    else if(k==2&&f==-1&&DC==0) t=T_ALPHA;
                    else if(k==3&&f==-1&&DC==0) t=T_B1A;
                    else if(k==3&&f==-1&&DC==1) t=T_B1B;
                    else if(k==3&&f==-2) t=T_B2;
                    else t=T_OTHER;
                    for(u32 o=avoid;o;o&=o-1) wtypes[__builtin_ctz(o)]|=1<<t;
                    Ru[t]|=Q; if(t==T_ALPHA && na<(1<<16)) alist[na++]=Q;
                }
            } else {
                /* E5: slack of (S_P, S_Q) with P = Wm side; 4-factor iff all >= 0 */
                if(f<minf_all) minf_all=f;
            }
        }
        if(mingproper<12) nsparse_fail++;
        for(int i=0;i<5;i++) tightk[i]+=tk[i];
        if(has2block) g_with_2block++;
        int interesting=0;
        if(isC2){
            int allbad = (badmask==Wm);
            { u32 ZUm=0; int DUs=0; for(int i=0;i<n;i++) if((Um>>i&1)&&deg[i]<6){ ZUm|=1u<<i; DUs+=6-deg[i]; }
              if(__builtin_popcount(ZUm)==1 && DUs==2 && mingproper>=12){ int u0=__builtin_ctz(ZUm); u32 Wp=Wm&~A[u0];
                nu0inst++; if((badmask&Wp)==Wp){ nu0fail++; printf("FAIL(u0: every W-vertex off N(u0) bad) %s\n",line);} }
              if(__builtin_popcount(ZUm)==2 && DUs==2 && mingproper>=12){ u32 pts=0; for(int i=0;i<n;i++) if((Wm>>i&1)&&deg[i]<=5) pts|=1u<<i;
                nu12inst++; if((badmask&pts)==pts){ nu12fail++; printf("FAIL(u1u2: every port bad) %s\n",line);} } }
            u32 ports=0; for(int i=0;i<n;i++) if((Wm>>i&1)&&deg[i]<=5) ports|=1u<<i;
            int portsbad = ((badmask&ports)==ports);
            if(allbad) nallbad++;
            if(portsbad) nportsbad++;
            for(int i=0;i<n;i++) if(Wm>>i&1){ if(badmask>>i&1){ nbadw++; wtypecount[wtypes[i]]++; } else ngoodw++; }
            /* union of all alpha petals, and of all petals */
            u32 Rall=0; for(int t=0;t<NT;t++) Rall|=Ru[t];
            int kR = __builtin_popcount(Ru[T_ALPHA]&Um)-__builtin_popcount(Ru[T_ALPHA]&Wm);
            int kAll = __builtin_popcount(Rall&Um)-__builtin_popcount(Rall&Wm);
            if(Ru[T_ALPHA]){ nalphag++; if(kR!=1) nalpha_union_bad++; }
            if(Rall && Rall!=full && kAll>=1) nunion_ok++;
            /* pairwise splits among alpha petals */
            long long sp[3]={0,0,0};
            for(int i=0;i<na;i++) for(int j=i+1;j<na;j++){
                u32 I=alist[i]&alist[j], Un=alist[i]|alist[j];
                int kI=__builtin_popcount(I&Um)-__builtin_popcount(I&Wm);
                int kU=__builtin_popcount(Un&Um)-__builtin_popcount(Un&Wm);
                if(kI==1&&kU==1) sp[0]++; else if(kI==2&&kU==0) sp[1]++; else if(kI==0&&kU==2) sp[2]++; else spother++;
            }
            for(int i=0;i<3;i++) splits[i]+=sp[i];
            if(sp[1]||sp[2]) ngsplit++;
            interesting = allbad || has2block;
            if(verbose || (onlyinteresting && interesting)){
                int DU=0,DWs=0; for(int i=0;i<n;i++){ if(Um>>i&1) DU+=6-deg[i]; else DWs+=6-deg[i]; }
                printf("%s C2 DU=%d DW=%d ming=%d tight[k=-2..2]=%d,%d,%d,%d,%d bad=%d/%d portsbad=%d",
                    line,DU,DWs,mingproper,tk[0],tk[1],tk[2],tk[3],tk[4],__builtin_popcount(badmask),__builtin_popcount(Wm),portsbad);
                for(int i=0;i<n;i++) if(Wm>>i&1){
                    printf(" w%d(d%d):",i,deg[i]);
                    if(!(badmask>>i&1)) printf("good"); else { int first=1; for(int t=0;t<NT;t++) if(wtypes[i]>>t&1){ printf("%s%s",first?"":"+",TN[t]); first=0; } }
                }
                printf("\n");
            }
        } else {
            if(minf_all<0) nE5no4f++;
            interesting = (minf_all<0) || has2block;
            if(verbose || (onlyinteresting && interesting))
                printf("%s E5 ming=%d tight[k=-2..2]=%d,%d,%d,%d,%d has4factor=%d\n",line,mingproper,tk[0],tk[1],tk[2],tk[3],tk[4],minf_all>=0);
        }
    }
    fprintf(stderr,"graphs %lld C2 %lld E5 %lld other %lld sparsity_fail %lld\n",ng,nC2,nE5,nother,nsparse_fail);
    fprintf(stderr,"C2: allWbad %lld portsbad %lld; W-vertices good %lld bad %lld\n",nallbad,nportsbad,ngoodw,nbadw);
    fprintf(stderr,"E5: without 4-factor %lld\n",nE5no4f);
    fprintf(stderr,"core: u0 instances %lld, all W off N(u0) bad in %lld; u1u2 instances %lld, all ports bad in %lld\n",nu0inst,nu0fail,nu12inst,nu12fail);
    fprintf(stderr,"alpha petals: graphs %lld, union kappa != 1 in %lld; alpha pairs (1,1) %lld (2,0) %lld (0,2) %lld other %lld; graphs with a split %lld\n",nalphag,nalpha_union_bad,splits[0],splits[1],splits[2],spother,ngsplit);
    fprintf(stderr,"tight sets (g=12, 3<=|S|<=n-1) by kappa -2..2: %lld %lld %lld %lld %lld; graphs with a 2-block %lld\n",
        tightk[0],tightk[1],tightk[2],tightk[3],tightk[4],g_with_2block);
    fprintf(stderr,"bad W-vertex type sets:");
    for(int m=1;m<(1<<NT);m++) if(wtypecount[m]){ fprintf(stderr," {"); int first=1; for(int t=0;t<NT;t++) if(m>>t&1){ fprintf(stderr,"%s%s",first?"":",",TN[t]); first=0;} fprintf(stderr,"}:%lld",wtypecount[m]); }
    fprintf(stderr,"\n");
    return 0;
}
