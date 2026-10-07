"""Small fixed-control check of the cubic-factor parity repair; no census."""
from itertools import combinations
import json, random, time
from pathlib import Path
OUT=Path(__file__).parent

def cubic_count(rows, columns):
    choices=[list(combinations(row,3)) for row in rows]
    choices.sort(key=len)
    counts={(0,)*columns:1}
    for opts in choices:
        following={}
        for old,weight in counts.items():
            for choice in opts:
                if any(old[c] == 3 for c in choice):
                    continue
                new=list(old)
                for c in choice: new[c]+=1
                key=tuple(new)
                following[key]=following.get(key,0)+weight
        counts=following
    return counts.get((3,)*columns,0)

def host(s,seed):
    rng=random.Random(seed)
    edges={(i,(i+t)%s) for i in range(s) for t in range(6)}
    for step in range(500):
        (a,b),(c,d)=rng.sample(sorted(edges),2)
        if a!=c and b!=d and (a,d) not in edges and (c,b) not in edges:
            edges.remove((a,b)); edges.remove((c,d))
            edges.add((a,d)); edges.add((c,b))
    assert all(sum(i==a for i,j in edges)==6 for a in range(s))
    assert all(sum(j==b for i,j in edges)==6 for b in range(s))
    return sorted(edges)

results=[]
for s,seed in [(6,0),(7,1),(8,2),(9,3),(9,4),(9,5)]:
    edges=host(s,seed)
    ports=[j for i,j in edges if i==0]
    y=ports[0]
    columns=[j for j in range(s) if j!=y]
    index={j:i for i,j in enumerate(columns)}
    rows=[[index[j] for i,j in edges if i==a and j!=y] for a in range(1,s)]
    count=cubic_count(rows,s-1)
    record={'shore_size_B':s,'seed':seed,'deleted_I':0,'deleted_O':y,'ports':ports,
            'cubic_factor_count':count,'parity':count%2,'B_edges':edges}
    results.append(record)
    print(json.dumps({k:v for k,v in record.items() if k!='B_edges'}),flush=True)
    (OUT/'parity-probe.json').write_text(json.dumps(results,indent=2)+'\n')
    if count%2: break
