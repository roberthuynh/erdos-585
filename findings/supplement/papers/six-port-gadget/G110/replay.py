"""Read-only replay of the two frozen certificates, with two fresh counts."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import hashlib
import json
import subprocess

HERE = Path(__file__).resolve().parent
P110 = HERE.parent.parent
CONTROL = P110 / 'scout-gadget/parity-control-certificate.json'
FIXED = P110 / 'certificates/FIXED-MATCHING.json'


def direct(matrix):
    text = str(len(matrix))+'\n'+'\n'.join(' '.join(map(str,row)) for row in matrix)+'\n'
    p = subprocess.run([str(HERE/'count_direct')], input=text, text=True,
                       capture_output=True, timeout=240, check=True)
    count, nodes = map(int,p.stdout.split())
    return count, nodes


def column_dp(matrix):
    # Multiply one column's elementary symmetric polynomial at a time.
    # The state records row exponents, and exponents above three are discarded.
    n=len(matrix)
    states={(0,)*n:1}
    for col in range(n):
        allowed=[r for r in range(n) if matrix[r][col]]
        nxt=Counter()
        for triple in combinations(allowed,3):
            for old,weight in states.items():
                if any(old[r]>=3 for r in triple): continue
                new=list(old)
                for r in triple: new[r]+=1
                nxt[tuple(new)]+=weight
        states=nxt
    return states.get((3,)*n,0)


controls=[]
for n,expected in [(3,1),(4,24)]:
    matrix=[[1]*n for _ in range(n)]
    a,nodes=direct(matrix); b=column_dp(matrix)
    assert a==b==expected
    controls.append({'graph':f'K{n},{n}', 'expected':expected, 'direct':a, 'column_dp':b})
matrix=[[0,0,0],[1,1,1],[1,1,1]]
assert direct(matrix)[0]==column_dp(matrix)==0
controls.append({'graph':'one isolated vertex on a 3-by-3 bipartite graph', 'expected':0})

c=json.loads(CONTROL.read_text())
s=c['B_shore_size']; o=c['removed_left']; y=c['removed_right_for_factor_count']
edges={tuple(e) for e in c['B_edges']}
assert len(edges)==len(c['B_edges'])==6*s
assert all(0<=a<s and 0<=b<s for a,b in edges)
assert all(sum(a==i for a,b in edges)==6 for i in range(s))
assert all(sum(b==j for a,b in edges)==6 for j in range(s))
gamma={(a,b) for a,b in edges if a!=o}
I=[i for i in range(s) if i!=o]
O=list(range(s))
assert len(gamma)==6*len(I)==c['Gamma_edges']
assert len(I)+len(O)==c['Gamma_vertices']
assert all(sum(a==i for a,b in gamma)==6 for i in I)
degO={j:sum(b==j for a,b in gamma) for j in O}
ports=sorted(j for j in O if degO[j]==5)
assert len(ports)==6 and ports==c['ports']
assert all(degO[j] in (5,6) for j in O)
assert y in ports
cols=[j for j in O if j!=y]
matrix=[[int((i,j) in gamma) for j in cols] for i in I]
a,nodes=direct(matrix); b=column_dp(matrix)
assert a==b==c['cubic_factors_by_DP']==c['cubic_factors_by_independent_MITM']==84577
assert a%2==1

quartic={tuple(e) for e in c['quartic_edges']}
assert len(quartic)==len(c['quartic_edges'])==28
assert quartic<=gamma
supportI=sorted({i for i,j in quartic}); supportO=sorted({j for i,j in quartic})
assert all(sum(a==i for a,b in quartic)==4 for i in supportI)
assert all(sum(b==j for a,b in quartic)==4 for j in supportO)
assert supportI==I and supportO==cols

f=json.loads(FIXED.read_text())
fe={frozenset(e) for e in f['edges']}
assert len(fe)==len(f['edges'])
cycles=f['cycles']
cycle_edges=[]
for cycle in cycles:
    assert len(cycle)>=3 and len(cycle)==len(set(cycle))
    ce={frozenset((cycle[i],cycle[(i+1)%len(cycle)])) for i in range(len(cycle))}
    assert len(ce)==len(cycle) and ce<=fe
    cycle_edges.append(ce)
assert set(cycles[0])==set(cycles[1])
assert not cycle_edges[0]&cycle_edges[1]
v=f['removed_vertex']
neighbors={u for edge in fe if v in edge for u in edge if u!=v}
fixed={frozenset(e) for e in f['admissible_fixed_matching']}
assert len(fixed)==2 and not fixed&fe
assert set.union(*(set(e) for e in fixed))==neighbors
assert sum(map(len,fixed))==len(neighbors)
actual=set()
for cycle in cycles:
    k=cycle.index(v)
    actual.add(frozenset((cycle[(k-1)%len(cycle)],cycle[(k+1)%len(cycle)])))
assert actual=={frozenset(e) for e in f['actual_matching_induced_by_this_pair']}
assert actual!=fixed
out={
 'status':'independent finite replay complete; no Lean or project PASS',
 'parity_control':{'B_shore_size':s, 'Gamma_vertices':len(I)+len(O),
   'Gamma_edges':len(gamma), 'ports':ports,
   'direct_exhaustive_row_count':a, 'direct_nodes':nodes,
   'independent_column_polynomial_DP_count':b,
   'odd':bool(a%2), 'quartic_edges':len(quartic),
   'quartic_support_left':supportI, 'quartic_support_right':supportO},
 'fixed_matching':{'pair_valid':True,'fixed':sorted(map(sorted,fixed)),
   'actual':sorted(map(sorted,actual)),'mismatch':True,
   'scope':'one valid pair does not follow a prescribed admissible matching; not a W1 refutation'},
 'controls':controls,
 'input_sha256':{str(p.relative_to(P110)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [CONTROL,FIXED]},
 'review_sources_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in [HERE/'count_direct.c',HERE/'replay.py']}
}
(HERE/'replay-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
