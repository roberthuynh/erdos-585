"""Independent meet-in-middle cubic count and explicit quartic certificate."""
from collections import Counter
from itertools import combinations, product
from pathlib import Path
import json
HERE=Path(__file__).parent
record=json.loads((HERE/'parity-probe.json').read_text())[-1]
s=record['shore_size_B']; edges={tuple(e) for e in record['B_edges']}
o=record['deleted_I']; y=record['deleted_O']
I=[i for i in range(s) if i!=o]
O=[j for j in range(s) if j!=y]
pos={j:k for k,j in enumerate(O)}
rows=[[pos[j] for a,j in sorted(edges) if a==i and j!=y] for i in I]
assert len(edges)==6*s and len(edges)==len(record['B_edges'])
assert all(sum(a==i for a,j in edges)==6 for i in range(s))
assert all(sum(b==j for i,b in edges)==6 for j in range(s))
Gamma={(i,j) for i,j in edges if i!=o}
ports=sorted(j for j in range(s) if sum(b==j for i,b in Gamma)==5)
assert len(ports)==6
assert all(sum(b==j for i,b in Gamma) in [5,6] for j in range(s))

def half_counter(part):
    result=Counter()
    for options in product(*(list(combinations(row,3)) for row in part)):
        vec=[0]*len(O)
        for triple in options:
            for c in triple: vec[c]+=1
        if max(vec,default=0)<=3: result[tuple(vec)]+=1
    return result
left=half_counter(rows[:3]); right=half_counter(rows[3:])
count=sum(weight*right[tuple(3-x for x in degree)] for degree,weight in left.items())
assert count==record['cubic_factor_count']==84577

# Deliberately separate witness search: four edges per row, column degrees four.
choices=[list(combinations(row,4)) for row in rows]
used=[0]*len(O)
selected=[]
def find(r):
    if r==len(rows): return all(x==4 for x in used)
    for choice in choices[r]:
        if any(used[c]==4 for c in choice): continue
        for c in choice: used[c]+=1
        selected.append(choice)
        if all(used[c]+sum(c in row for row in rows[r+1:])>=4 for c in range(len(O))) and find(r+1):
            return True
        selected.pop()
        for c in choice: used[c]-=1
    return False
assert find(0)
quartic=[(I[r],O[c]) for r,choice in enumerate(selected) for c in choice]
assert set(quartic)<=Gamma
assert len(quartic)==4*len(I)
assert all(sum(a==i for a,b in quartic)==4 for i in I)
assert all(sum(b==j for a,b in quartic)==4 for j in O)
result={'control_type':'valid G110 positive control; parity-repair falsifier only',
        'B_shore_size':s,'Gamma_vertices':2*s-1,'Gamma_edges':len(Gamma),
        'removed_left':o,'removed_right_for_factor_count':y,'ports':ports,
        'cubic_factors_by_DP':record['cubic_factor_count'],
        'cubic_factors_by_independent_MITM':count,
        'cubic_factor_count_is_odd':bool(count%2),
        'B_edges':sorted(edges),'quartic_edges':quartic,
        'quartic_degree_checks':True,
        'all_G110_degree_checks':True}
(HERE/'parity-control-certificate.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['B_edges','quartic_edges']},indent=2))
