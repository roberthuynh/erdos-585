#!/usr/bin/env python3
"""Independent complete eight-vertex check of hereditary geng pruning."""
import json,subprocess,time
from pathlib import Path
import networkx as nx
from erdos585_extension import verify_both
OUT=Path(__file__).resolve().parents[1]/'reports/585-overnight'
def run():
    start=time.monotonic()
    raw=subprocess.run(['geng','-q','-l','8'],capture_output=True,check=True).stdout.splitlines()
    expected=set()
    for i,line in enumerate(raw):
        g=nx.from_graph6_bytes(line)
        if verify_both(8,sorted(g.edges())):expected.add(line)
        if (i+1)%2000==0:print(json.dumps(dict(checked=i+1,total=len(raw),seconds=time.monotonic()-start)),flush=True)
    filtered=subprocess.run(['[temporary path]','-l','8'],capture_output=True,check=True)
    actual=filtered.stdout.splitlines()
    assert len(actual)==len(set(actual))
    assert set(actual)==expected,(len(actual),len(expected),len(set(actual)^expected))
    result=dict(order=8,all_isomorphism_classes=len(raw),pairfree_isomorphism_classes=len(expected),
        status='exact canonical graph6 output agrees with both independent Python checkers on every graph',
        seconds=time.monotonic()-start,limitation='Computational audit of the generator and prune rule, not a Lean proof.')
    (OUT/'geng-complete-eight-audit.json').write_text(json.dumps(result,indent=2)+'\n')
    (OUT/'geng-complete-eight-audit.log').write_bytes(filtered.stderr)
    print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':run()
