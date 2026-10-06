/* e5k.c: for E5 instances, (1) where good pairs (p,q) lie relative to the unique cut,
 * (2) the set of k = |A'|-|C'| over violations (A',C') of G - p - q, all bad pairs, both orientations.
 * Independent referee code. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint32_t set;
static int n; static set adj[32]; static int deg[32], col[32];
static uint8_t *E;
static int pc(set x){return __builtin_popcount(x);}
static int parse(const char*s){const unsigned char*p=(const unsigned char*)s;n=*p++-63;memset(adj,0,sizeof adj);int cur=0,nb=0;
 for(int j=1;j<n;j++)for(int i=0;i<j;i++){if(!nb){cur=*p++-63;nb=6;}nb--;if(cur>>nb&1){adj[i]|=1u<<j;adj[j]|=1u<<i;}}
 for(int v=0;v<n;v++)deg[v]=pc(adj[v]);return 0;}
static void bip(void){for(int v=0;v<n;v++)col[v]=-1;int q[32],h=0,t=0;col[0]=0;q[t++]=0;while(h<t){int v=q[h++];for(int u=0;u<n;u++)if(adj[v]>>u&1&&col[u]<0){col[u]=1-col[v];q[t++]=u;}}}
static int has4(set M){ /* flow */
 set L=0,R=0;for(int v=0;v<n;v++)if(M>>v&1){if(col[v]==0)L|=1u<<v;else R|=1u<<v;}
 if(pc(L)!=pc(R))return 0;int S=n,T=n+1,NN=n+2;static int cap[34][34];memset(cap,0,sizeof cap);
 for(int v=0;v<n;v++){if(L>>v&1){cap[S][v]=4;for(int u=0;u<n;u++)if((R>>u&1)&&(adj[v]>>u&1))cap[v][u]=1;}if(R>>v&1)cap[v][T]=4;}
 int fl=0;for(;;){int pr[34],q[34],h=0,t=0;for(int i=0;i<NN;i++)pr[i]=-1;pr[S]=S;q[t++]=S;
  while(h<t&&pr[T]<0){int x=q[h++];for(int y=0;y<NN;y++)if(cap[x][y]>0&&pr[y]<0){pr[y]=x;q[t++]=y;}}
  if(pr[T]<0)break;int b=99;for(int y=T;y!=S;y=pr[y]){int x=pr[y];if(cap[x][y]<b)b=cap[x][y];}
  for(int y=T;y!=S;y=pr[y]){int x=pr[y];cap[x][y]-=b;cap[y][x]+=b;}fl+=b;}
 return fl==4*pc(L);}
int main(void){char line[512];int gi=0;
 while(fgets(line,sizeof line,stdin)){line[strcspn(line,"\r\n")]=0;if(!*line)continue;parse(line);bip();
  set ALL=(1u<<n)-1,Pm=0,Qm=0;for(int v=0;v<n;v++){if(col[v]==0)Pm|=1u<<v;else Qm|=1u<<v;}
  size_t N=(size_t)1<<n;E=realloc(E,N);E[0]=0;for(size_t S=1;S<N;S++){int v=__builtin_ctz((set)S);set R=(set)S&((set)S-1);E[S]=E[R]+pc(adj[v]&R);}
  /* find the cut with A subset of Pm: violation of G */
  set Aa=0,Cc=0;int found=0;
  for(set S=0;S<=ALL&&!found;S++){set A=S&Pm,C=S&Qm;int k=pc(A)-pc(C);if(k<1)continue;int sig=E[A|(Qm&~C)]-4*k;if(sig<0){Aa=A;Cc=C;found=1;} if(S==ALL)break;}
  set Bb=Pm&~Aa,Dd=Qm&~Cc;
  /* good pairs classification */
  int good=0,goodAD=0,goodcls[4]={0}; /* index: (p in A)*2 + (q in D) */
  int badpair[32][32];memset(badpair,0,sizeof badpair);
  for(int p=0;p<n;p++)if(Pm>>p&1)for(int q=0;q<n;q++)if(Qm>>q&1){
    int ok=has4(ALL&~(1u<<p)&~(1u<<q));
    if(ok){good++;int ix=((Aa>>p&1)?2:0)+((Dd>>q&1)?1:0);goodcls[ix]++;if(ix==3)goodAD++;}
    else badpair[p][q]=1;}
  /* k-range over violations of G-p-q for bad pairs, both orientations */
  int kseen[2][16];memset(kseen,0,sizeof kseen);long nchk=0;int mism=0;
  for(int orient=0;orient<2;orient++){set P=orient?Qm:Pm,Q=orient?Pm:Qm;
   for(set S=0;S<=ALL;S++){set A=S&P,C=S&Q;int k=pc(A)-pc(C);
    if(k>=1&&A!=P&&C!=Q){int f=E[A|(Q&~C)]-4*k;
     /* violation of G-p-q needs p in P-A, q in Q-C, f - e(A,q) < 0 */
     for(int q=0;q<n;q++)if((Q&~C)>>q&1){int eq=pc(adj[q]&A);if(f-eq<0){
       for(int p=0;p<n;p++)if((P&~A)>>p&1){int pp=orient?q:p,qq=orient?p:q; if(!badpair[pp][qq])mism++; else kseen[orient][k<16?k:15]=1;}}}}
    if(S==ALL)break;}}
  printf("g%d n=%d good=%d/%d good[pA,qD]=%d good[pA,qC]=%d good[pB,qD]=%d good[pB,qC]=%d kset_PQ=",gi,n,good,pc(Pm)*pc(Qm),goodcls[3],goodcls[2],goodcls[1],goodcls[0]);
  for(int k=0;k<16;k++)if(kseen[0][k])printf("%d,",k);printf(" kset_QP=");for(int k=0;k<16;k++)if(kseen[1][k])printf("%d,",k);
  printf(" mismatch=%d |A|=%d |B|=%d\n",mism,pc(Aa),pc(Bb));gi++;fflush(stdout);}
 return 0;}
