/* Count blocks with a non-generic big-side vertex (PAPER2 Def 3.2), actual cut vector. Own code.
   input: blk3 format with cut vector. */
#include <stdio.h>
#include <stdlib.h>
static int pc(unsigned x){return __builtin_popcount(x);}
int main(void){
  char line[8192]; int nA,nC; unsigned cm[20]; int c[20];
  int *dem = malloc(sizeof(int)<<20);
  long blocks=0, withcore=0, ngv=0;
  while(fgets(line,sizeof line,stdin)){
    char *p=line; int nr;
    if(sscanf(p,"%d %d%n",&nA,&nC,&nr)!=2) continue; p+=nr;
    for(int j=0;j<nC;j++){sscanf(p,"%u%n",&cm[j],&nr);p+=nr;}
    for(int i=0;i<nA;i++){sscanf(p,"%d%n",&c[i],&nr);p+=nr;}
    unsigned full=(1u<<nA)-1, L=0;
    for(int i=0;i<nA;i++){int d=0; for(int j=0;j<nC;j++) if(cm[j]>>i&1) d++; if(d==3) L|=1u<<i;}
    for(unsigned S=0;S<=full;S++){int s=0; for(int j=0;j<nC;j++){int x=pc(cm[j]&S); s+= x>4?4:x;} dem[S]=4*pc(S)-s;}
    int bad=0;
    for(int q=0;q<nA;q++){
      int ng=0;
      for(unsigned S=0;S<=full && !ng;S++){
        if(S>>q&1) continue;
        if(pc(S) > nA-2) continue;
        unsigned rest = full & ~S & ~(1u<<q);
        int cr=0; for(int i=0;i<nA;i++) if(rest>>i&1) cr+=c[i];
        if(dem[S]+cr>=5 && dem[S] > pc(S&L)) ng=1;
      }
      if(ng){bad++; ngv++;}
    }
    blocks++; if(bad) withcore++;
  }
  printf("blocks=%ld blocks_with_nongeneric_vertex=%ld nongeneric_vertices=%ld\n",blocks,withcore,ngv);
  return 0;
}
