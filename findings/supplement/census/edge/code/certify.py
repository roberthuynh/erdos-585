"""certify.py: SAT certificates that graphs have no nonempty 4-regular subgraph.

Usage: python certify.py IN.g6 OUTDIR
For each graph (line i of IN.g6): writes OUTDIR/g<i>.cnf (validate_sat.py's encoding, see witness.py)
and OUTDIR/g<i>.drat (glucose4 proof), checks the proof with witness.rup_check, and prints one line
per graph plus a summary "CERTIFIED k of m". Exit status 0 iff every graph is certified.
Also used by collect.py on any output graph of a job.
"""
import os
import sys

import networkx as nx
from pysat.solvers import Solver

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from witness import cnf, rup_check  # noqa: E402


def certify_file(inp, outdir):
    os.makedirs(outdir, exist_ok=True)
    lines = [l.strip() for l in open(inp) if l.strip()]
    ok_all, report = 0, []
    for i, l in enumerate(lines):
        g = nx.from_graph6_bytes(l.encode())
        nv, cl = cnf(g)
        with open(os.path.join(outdir, f"g{i}.cnf"), "w") as f:
            f.write(f"p cnf {nv} {len(cl)}\n")
            for c in cl:
                f.write(" ".join(map(str, c)) + " 0\n")
        with Solver(name="glucose4", bootstrap_with=cl, with_proof=True) as s:
            sat = s.solve()
            proof = [] if sat else s.get_proof()
        open(os.path.join(outdir, f"g{i}.drat"), "w").write("\n".join(proof) + "\n")
        ok, nl, msg = (False, 0, "SAT: has a 4-regular subgraph") if sat else rup_check(cl, proof)
        ok_all += ok
        report.append(f"g{i} {l} n={g.number_of_nodes()} e={g.number_of_edges()} "
                      f"{'CERTIFIED' if ok else 'NOT CERTIFIED'} ({msg}, {nl} lemmas)")
    report.append(f"CERTIFIED {ok_all} of {len(lines)}")
    return ok_all == len(lines), "\n".join(report)


if __name__ == "__main__":
    good, text = certify_file(sys.argv[1], sys.argv[2])
    print(text)
    sys.exit(0 if good else 1)
