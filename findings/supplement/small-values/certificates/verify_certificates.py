#!/usr/bin/env python3
"""Verify coverage and actual cycle witnesses, independently of the C search.

This verifier reads graph6 by indexing its triangular positions directly. It
checks extension completeness by every 10-bit mask, whereas the producer uses
itertools combinations. It never asks whether a graph has a pair.
"""
import collections,datetime,hashlib,json,pathlib
HERE=pathlib.Path(__file__).resolve().parent
DATA=HERE/'data';LOG=HERE/'receipts'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def edges(text):
    text=text.strip(); n=ord(text[0])-63
    assert len(text)==1+(n*(n-1)//2+5)//6
    out=set()
    for j in range(1,n):
        for i in range(j):
            pos=j*(j-1)//2+i
            if ((ord(text[1+pos//6])-63)>>(5-pos%6))&1:out.add((i,j))
    return n,out
def degrees(n,es):
    degree=[0]*n
    for i,j in es:degree[i]+=1;degree[j]+=1
    return degree
def cycle_vertices(text,n,es):
    vs=list(map(int,text.split(',')))
    assert len(vs)>=5 and len(set(vs))==len(vs)
    assert all(0<=v<n for v in vs)
    ce={tuple(sorted((vs[i],vs[(i+1)%len(vs)]))) for i in range(len(vs))}
    assert len(ce)==len(vs) and ce<=es
    return set(vs),ce
def verify(e):
    parents=DATA/f'parent-n10-e{e}.free.g6'
    childfile=DATA/f'children-n11-e{e+5}.g6'
    mapfile=DATA/f'children-n11-e{e+5}.jsonl'
    certfile=DATA/f'children-n11-e{e+5}.cycles.tsv'
    ps=parents.read_text().splitlines(); children=childfile.read_text().splitlines()
    meta=[json.loads(x) for x in mapfile.read_text().splitlines()]
    certs=[x.split('\t') for x in certfile.read_text().splitlines()]
    assert len(children)==len(meta)==len(certs)
    actual=collections.defaultdict(set)
    histogram=collections.Counter()
    for index,(text,m,c) in enumerate(zip(children,meta,certs),1):
        assert m['child']==int(c[0])==index
        pi=m['parent'];assert 1<=pi<=len(ps)
        pn,pe=edges(ps[pi-1]);n,ce=edges(text)
        assert pn==10 and n==11 and len(pe)==e and len(ce)==e+5
        assert {x for x in ce if 10 not in x}==pe
        nb={i for i,j in ce if j==10};assert nb==set(m['neighbors']) and len(nb)==5
        mask=sum(1<<i for i in nb)
        assert mask not in actual[pi];actual[pi].add(mask)
        assert min(degrees(n,ce))==5
        s1,c1=cycle_vertices(c[2],n,ce);s2,c2=cycle_vertices(c[3],n,ce)
        assert int(c[1])==len(s1)==len(s2) and s1==s2 and c1.isdisjoint(c2)
        histogram[len(s1)]+=1
    expected_total=0
    for pi,text in enumerate(ps,1):
        n,es=edges(text); assert n==10 and len(es)==e
        ds=degrees(n,es);assert min(ds)>=4
        expected={mask for mask in range(1<<10) if mask.bit_count()==5 and
                  all(ds[i]+((mask>>i)&1)>=5 for i in range(10))}
        assert actual[pi]==expected,(pi,actual[pi]^expected)
        expected_total+=len(expected)
    assert expected_total==len(children)
    return {'parent_edges':e,'parents':len(ps),'extensions':len(children),
            'coverage_by_all_neighbor_masks':True,'literal_cycle_pairs_verified':len(certs),
            'cycle_support_size_histogram':dict(sorted(histogram.items())),
            'input_hashes':{p.name:sha(p) for p in (parents,childfile,mapfile,certfile)}}
if __name__=='__main__':
    report={'timestamp':datetime.datetime.now().astimezone().isoformat(),
            'verifier_source_sha256':sha(__file__),'checked':[verify(26),verify(27)]}
    report['complete']=True
    (LOG/'independent-certificate-verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
