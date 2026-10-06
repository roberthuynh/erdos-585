/* q4.c: decide whether a bipartite graph (first n1 vertices = class 1, as genbg writes them)
 * has a nonempty 4-regular subgraph. Complete method: a 4-regular bipartite subgraph has equal
 * parts S1 subset class1, S2 subset class2 with |S1| = |S2| >= 4 and G[S1 u S2] has a 4-factor;
 * enumerate all such pairs (pruned: S2 vertices need >= 4 neighbours in S1 and vice versa) and test
 * each by max flow. Prints counts; writes graphs with NO 4-regular subgraph to stdout.
 * Independent referee code. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint32_t set;
static int n, n1; static set adj[32];
static int pc(set x){return __builtin_popcount(x);}
static int parse(const char*s){const unsigned char*p=(const unsigned char*)s;n=*p++-63;memset(adj,0,sizeof adj);int cur=0,nb=0;
 for(int j=1;j<n;j++)for(int i=0;i<j;i++){if(!nb){cur=*p++-63;nb=6;}nb--;if(cur>>nb&1){adj[i]|=1u<<j;adj[j]|=1u<<i;}}return 0;}
static int flow4(set L, set R){ /* 4-factor of G[L u R], L in class1, R in class2, |L|=|R| */
 int S=n,T=n+1,NN=n+2;static int cap[34][34];memset(cap,0,sizeof cap);
 for(int v=0;v<n;v++){if(L>>v&1){cap[S][v]=4;for(int u=0;u<n;u++)if((R>>u&1)&&(adj[v]>>u&1))cap[v][u]=1;}if(R>>v&1)cap[v][T]=4;}
 int fl=0;for(;;){int pr[34],q[34],h=0,t=0;for(int i=0;i<NN;i++)pr[i]=-1;pr[S]=S;q[t++]=S;
  while(h<t&&pr[T]<0){int x=q[h++];for(int y=0;y<NN;y++)if(cap[x][y]>0&&pr[y]<0){pr[y]=x;q[t++]=y;}}
  if(pr[T]<0)break;int b=99;for(int y=T;y!=S;y=pr[y]){int x=pr[y];if(cap[x][y]<b)b=cap[x][y];}
  for(int y=T;y!=S;y=pr[y]){int x=pr[y];cap[x][y]-=b;cap[y][x]+=b;}fl+=b;}
 return fl==4*pc(L);}
static long nflow;
/* choose S2 of size m from cand (bitmask) with each S1 vertex having >= 4 nbrs in S2 */
static int rec(set S1, set cand, set chosen, int need){
 if(need==0){ for(int v=0;v<n;v++) if(S1>>v&1){ if(pc(adj[v]&chosen)<4) return 0; }
   nflow++; return flow4(S1,chosen); }
 if(pc(cand)<need) return 0;
 int v=__builtin_ctz(cand); set rest=cand&(cand-1);
 if(rec(S1,rest,chosen|(1u<<v),need-1)) return 1;
 return rec(S1,rest,chosen,need);
}
static int hasq4(void){
 set C1=(1u<<n1)-1, C2=((1u<<n)-1)&~C1;
 /* m = 4 first: K44 */
 for(int m=4; m<=n1 && m<=n-n1; m++){
  for(set S1=0; S1<=C1; S1++){ if(pc(S1)!=m) continue;
   set cand=0; for(int u=n1;u<n;u++) if(pc(adj[u]&S1)>=4) cand|=1u<<u;
   if(pc(cand)<m) continue;
   /* each S1 vertex needs >= 4 nbrs among cand */
   int ok=1; for(int v=0;v<n1;v++) if((S1>>v&1)&&pc(adj[v]&cand)<4) ok=0;
   if(!ok) continue;
   if(rec(S1,cand,0,m)) return 1;
  }
 }
 (void)C2; return 0;
}
int main(int argc,char**argv){ n1=atoi(argv[1]); char line[512]; long gi=0,yes=0,no=0;
 while(fgets(line,sizeof line,stdin)){line[strcspn(line,"\r\n")]=0;if(!*line)continue;parse(line);
  if(hasq4()) yes++; else { no++; printf("%s\n",line); } gi++; }
 fprintf(stderr,"graphs=%ld with_q4=%ld without_q4=%ld flowtests=%ld\n",gi,yes,no,nflow); return 0;}
