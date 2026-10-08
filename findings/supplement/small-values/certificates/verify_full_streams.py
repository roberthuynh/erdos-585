#!/usr/bin/env python3
"""Check every positive rejection and exact survivor subsequence of full levels.

This is a certificate validator, not a cycle-search decider. Completeness of the
upper exclusions requires all positive rejections to be sound. Negative answers
may conservatively retain extra graphs and do not create an upper-bound gap.
"""
import datetime,hashlib,json,pathlib,time
from verify_certificates import edges,degrees,cycle_vertices
HERE=pathlib.Path(__file__).resolve().parent
DATA=HERE/'data';LOG=HERE/'receipts'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def next_cert(stream):
    line=stream.readline()
    if not line:return None
    fields=line.rstrip('\n').split('\t');assert len(fields)==4
    return fields
reports=[]
for label,e,mindeg in [('parent-n10-e26',26,4),('parent-n10-e27',27,4),('baseline-n10-e28',28,0)]:
    allfile=DATA/(label+'.all.g6');certfile=DATA/(label+'.cycles.tsv');freefile=DATA/(label+'.free.g6')
    start=time.monotonic();seen=positive=negative=0
    with allfile.open() as graphs,certfile.open() as certs,freefile.open() as free:
        cert=next_cert(certs);lastcert=0
        for row,text in enumerate(graphs,1):
            seen+=1;n,es=edges(text);assert n==10 and len(es)==e
            assert min(degrees(n,es))>=mindeg
            if cert is not None and int(cert[0])==row:
                assert row>lastcert;lastcert=row
                s1,c1=cycle_vertices(cert[2],n,es);s2,c2=cycle_vertices(cert[3],n,es)
                assert len(s1)==len(s2)==int(cert[1]) and s1==s2 and c1.isdisjoint(c2)
                positive+=1;cert=next_cert(certs)
                if cert is not None:assert int(cert[0])>row
            else:
                assert cert is None or int(cert[0])>row
                assert free.readline()==text,'survivor subsequence mismatch'
                negative+=1
        assert cert is None and free.readline()==''
    receipt=json.loads((LOG/(label+'.json')).read_text())
    assert receipt['complete'] and seen==receipt['generated']==receipt['all_graphs_lines']
    assert positive==receipt['cycle_certificate_lines'] and negative==receipt['free_catalogue_lines']
    hashes={'all_graphs_sha256':sha(allfile),'cycle_certificates_sha256':sha(certfile),'free_catalogue_sha256':sha(freefile)}
    assert all(receipt[k]==v for k,v in hashes.items())
    report={'label':label,'graphs':seen,'literal_cycle_pairs_verified':positive,
            'survivors':negative,'exact_survivor_subsequence':True,'wall_seconds':time.monotonic()-start,**hashes}
    reports.append(report)
    (LOG/(label+'.certificate-verified.json')).write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report),flush=True)
summary={'timestamp':datetime.datetime.now().astimezone().isoformat(),'verifier_source_sha256':sha(__file__),
         'checks':reports,'total_graphs':sum(r['graphs'] for r in reports),
         'total_positive_rejections_checked':sum(r['literal_cycle_pairs_verified'] for r in reports),
         'complete':True}
(LOG/'full-stream-certificate-verification.json').write_text(json.dumps(summary,indent=2)+'\n')
