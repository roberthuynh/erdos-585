#!/usr/bin/env python3
"""Independent minimum-degree extension enumeration, without isomorph pruning."""
import datetime,hashlib,itertools,json,pathlib,subprocess,time
HERE=pathlib.Path(__file__).resolve().parent
DATA=HERE/'data'; LOG=HERE/'receipts'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def decode(s):
    s=s.strip(); n=ord(s[0])-63; adj=[set() for _ in range(n)]; pos=0
    assert 0<=n<=12
    for j in range(1,n):
        for i in range(j):
            word=ord(s[1+pos//6])-63
            if word & (1<<(5-pos%6)):adj[i].add(j);adj[j].add(i)
            pos+=1
    return adj
def encode(adj):
    n=len(adj); bits=[int(i in adj[j]) for j in range(1,n) for i in range(j)]
    bits += [0]*((-len(bits))%6)
    return chr(n+63)+''.join(chr(63+sum(bits[s+t]<<(5-t) for t in range(6))) for s in range(0,len(bits),6))
def run(e):
    parents=DATA/f'parent-n10-e{e}.free.g6'
    lines=parents.read_text().splitlines()
    out=DATA/f'children-n11-e{e+5}.g6'; meta=DATA/f'children-n11-e{e+5}.jsonl'
    per=[]; total=0
    with out.open('w') as stream,meta.open('w') as details:
        for index,g6 in enumerate(lines,1):
            a=decode(g6); assert len(a)==10
            assert sum(map(len,a))==2*e and min(map(len,a))>=4
            admissible=0
            for nb in itertools.combinations(range(10),5):
                ns=set(nb)
                if any(len(a[v])+int(v in ns)<5 for v in range(10)):continue
                child=[set(x) for x in a]+[ns]
                for v in nb:child[v].add(10)
                assert min(map(len,child))==5
                total+=1;admissible+=1
                stream.write(encode(child)+'\n')
                details.write(json.dumps({'child':total,'parent':index,'neighbors':nb})+'\n')
            per.append(admissible)
    command=['timeout','240',str(HERE/'pair_decider'),'--cert',str(DATA/f'children-n11-e{e+5}.cycles.tsv')]
    started=datetime.datetime.now().astimezone().isoformat();t=time.monotonic()
    with out.open('rb') as stream,(DATA/f'children-n11-e{e+5}.free.g6').open('wb') as free,(LOG/f'children-n11-e{e+5}.decider.log').open('wb') as err:
        result=subprocess.run(command,stdin=stream,stdout=free,stderr=err)
    wall=time.monotonic()-t
    record={'started':started,'parent_order':10,'parent_edges':e,'child_order':11,'child_edges':e+5,
            'added_degree':5,'child_min_degree':5,'parents':len(lines),'admissible_children':total,
            'per_parent_children':per,'command':command,'decider_exit':result.returncode,'wall_seconds':wall,
            'parents_sha256':sha(parents),'children_sha256':sha(out),'mapping_sha256':sha(meta),
            'cycle_certificates_sha256':sha(DATA/f'children-n11-e{e+5}.cycles.tsv'),
            'survivors_sha256':sha(DATA/f'children-n11-e{e+5}.free.g6'),
            'survivors':sum(1 for _ in (DATA/f'children-n11-e{e+5}.free.g6').open('rb')),
            'cycle_certificate_lines':sum(1 for _ in (DATA/f'children-n11-e{e+5}.cycles.tsv').open('rb'))}
    record['complete']=result.returncode==0 and record['cycle_certificate_lines']==total and record['survivors']==0
    (LOG/f'children-n11-e{e+5}.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({k:v for k,v in record.items() if k!='per_parent_children'}),flush=True)
    if not record['complete']:raise SystemExit('incomplete or counterexample')
if __name__=='__main__':
    for e in (26,27):run(e)
