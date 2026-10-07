#!/usr/bin/env python3
"""Second exhaustive method for the finite eleven-vertex question.

No nauty, SAT solver, native detector, or existing ten-vertex catalogue is used.
Start with all eight-vertex complements through ten edges, independently
canonicalized. Extend at a minimum-degree vertex and retain all dense pair-free
classes. Completeness follows by deleting a minimum-degree vertex. Every positive
rejection has a checked pair; every negative is checked by both older programs.
State is saved after every parent graph. This remains computational evidence.
"""
import itertools,json,math,time
from pathlib import Path
import erdos585_verify as ref
from erdos585_extension import verify_both,atomic_json,WITNESS11
OUT=Path(__file__).resolve().parents[1]/'reports/585-overnight'
STATE=OUT/'deletion-exhaustive-state.json'

def emit(state):
    atomic_json(STATE,state)

def check(ctx,m):
    w=ref.find_pair(ctx,ctx.adj(m))
    if w is not None:
        assert ref.witness_ok(ctx,m,w)
        return w
    assert verify_both(ctx.n,ctx.edges(m))
    return None

def start_eight(state,deadline):
    c=ref.Ctx(8)
    if not ref.gen_levels(c,10,state,str(STATE),deadline,lambda s:print(s,flush=True)):
        return False
    levels=state['levels']['8']
    for k,rows in levels.items():
        assert sum(math.factorial(8)//aut for _,aut in rows)==math.comb(28,int(k))
    if '8' in state['catalogues']:return True
    for m,_ in levels['8']:
        assert check(c,c.full^m) is not None
    kept={}
    for k in (9,10):
        for m,_ in levels[str(k)]:
            g=c.full^m
            if check(c,g) is None:
                f,a=ref.canon(c,g);kept[f]=a
    rows=sorted([m,a] for m,a in kept.items())
    state['catalogues']['8']=rows
    state['bounds']['8']=19
    state['counts']['8']={str(e):sum(m.bit_count()==e for m,_ in rows) for e in (18,19)}
    emit(state);print('eight '+json.dumps(state['counts']['8']),flush=True)
    return True

def extend(state,n,lower,target,deadline):
    key=str(n)
    if key in state['catalogues']:return True
    prev=state['catalogues'][str(n-1)];old=ref.Ctx(n-1);ctx=ref.Ctx(n)
    work=state.setdefault('work',{}).setdefault(key,dict(next_parent=0,kept={},rejected=0,tests=0))
    upper=target if target is not None else n*state['bounds'][str(n-1)]//(n-2)
    for idx in range(work['next_parent'],len(prev)):
        m,_=prev[idx];es=old.edges(m);base=ctx.mask(es);e=len(es)
        deg=[x.bit_count() for x in old.adj(m)]
        for d in range(max(0,lower-e),min(n-1,upper-e)+1):
            total=e+d
            if n*d>2*total:continue
            for nbrs in itertools.combinations(range(n-1),d):
                ns=set(nbrs)
                if any(deg[v]+(v in ns)<d for v in range(n-1)):continue
                gm=base|sum(ctx.ebit[v][n-1] for v in nbrs)
                work['tests']+=1
                if check(ctx,gm) is not None:work['rejected']+=1
                else:
                    f,a=ref.canon(ctx,gm);work['kept'][str(f)]=a
        work['next_parent']=idx+1
        emit(state)
        if idx%10==0:print(json.dumps(dict(n=n,parents=idx+1,total=len(prev),tests=work['tests'],kept=len(work['kept']))),flush=True)
        if time.time()>deadline:return False
    rows=sorted([int(m),a] for m,a in work['kept'].items())
    state['catalogues'][key]=rows
    if target is None:
        state['bounds'][key]=max((m.bit_count() for m,_ in rows),default=lower-1)
    state['counts'][key]={str(e):sum(m.bit_count()==e for m,_ in rows) for e in range(lower,upper+1)}
    emit(state);print('finished '+key+' '+json.dumps(state['counts'][key]),flush=True)
    return True

def run():
    started=time.monotonic();deadline=time.time()+210
    state=json.loads(STATE.read_text()) if STATE.exists() else dict(levels={},catalogues={},bounds={},counts={})
    if not start_eight(state,deadline):return
    if not extend(state,9,22,None,deadline):return
    if not extend(state,10,27,None,deadline):return
    if not extend(state,11,32,32,deadline):return
    assert not state['catalogues']['11']
    assert verify_both(11,WITNESS11)
    state['status']='complete'
    state['conclusion']='computational evidence f(11)=31; no Lean theorem'
    emit(state)
    result=dict(status='complete',counts=state['counts'],bounds=state['bounds'],
        extension_tests={k:v['tests'] for k,v in state['work'].items()},
        positive_rejections={k:v['rejected'] for k,v in state['work'].items()},
        lower_witness_edges=sorted(WITNESS11),lower_witness_independent_checks=2,
        method='minimum-degree vertex deletion; independent Python canonicalization and cycle enumeration; no nauty or SAT',
        conclusion=state['conclusion'],last_invocation_seconds=time.monotonic()-started)
    atomic_json(OUT/'deletion-exhaustive-result.json',result)
    print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':run()
