#!/usr/bin/env python3
"""Cross-check the new native detector against both pre-existing programs."""
import itertools,json,random,subprocess,time
from pathlib import Path
import networkx as nx
from erdos585_extension import verify_both,WITNESS11
import erdos585_verify as independent
OUT=Path(__file__).resolve().parents[1]/'reports/585-overnight'

def mask(edges):
    return sum(1<<(b*(b-1)//2+a) for a,b in (sorted(e) for e in edges))
def unmask(n,x):
    return [(a,b) for b in range(1,n) for a in range(b) if x>>(b*(b-1)//2+a)&1]

def run():
    start=time.monotonic();cases=[]
    for g in nx.graph_atlas_g():
        if len(g):cases.append((len(g),sorted(g.edges())))
    rng=random.Random(58520261002)
    for n in range(8,12):
        es=list(itertools.combinations(range(n),2))
        # The first reference checker materializes every simple cycle. Dense
        # eleven-vertex graphs make this an audit of runtime, not of coverage.
        for _ in range(100):cases.append((n,sorted(rng.sample(es,rng.randrange(min(35,len(es))+1)))))
    cases.extend([(11,WITNESS11),(11,WITNESS11+[(9,10)])])
    inp=''.join(f'{n} {mask(es)}\n' for n,es in cases)
    proc=subprocess.run(['[temporary path]'],input=inp,text=True,
        capture_output=True,check=True,timeout=200)
    rows=proc.stdout.splitlines();assert len(rows)==len(cases)
    yes=no=0
    progress=OUT/'geng-detector-audit-progress.json'
    for i,((n,es),row) in enumerate(zip(cases,rows)):
        positive,s,r,b=map(int,row.split())
        expected=not verify_both(n,es)
        assert bool(positive)==expected,(i,n,es,row)
        if positive:
            ctx=independent.Ctx(n)
            assert independent.witness_ok(ctx,ctx.mask(es),
                (s,ctx.mask(unmask(n,r)),ctx.mask(unmask(n,b))))
            yes+=1
        else:no+=1
        if (i+1)%100==0:
            state=dict(checked=i+1,total=len(cases),positive=yes,negative=no,
                seconds=time.monotonic()-start,status='in_progress')
            progress.write_text(json.dumps(state,indent=2)+'\n')
            print(json.dumps(state),flush=True)
    result=dict(cases=len(cases),positive=yes,negative=no,
        scope='all nonempty atlas graphs through seven vertices; 400 seeded random graphs on 8..11 with at most 35 edges; known eleven-vertex controls',
        status='all native verdicts agree with both independent existing programs',
        seconds=time.monotonic()-start,
        limitation='Detector controls only; not an exhaustive result for eleven vertices.')
    (OUT/'geng-detector-audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':run()
