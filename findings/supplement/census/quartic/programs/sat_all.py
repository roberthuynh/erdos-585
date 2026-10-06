"""Decide every graph in a graph6 stream with validate_sat.py's SAT encoding (imported, unchanged).

Usage: python sat_all.py IN.g6|- UNSAT_OUT.g6
Prints one line "SAT <n> UNSAT <m>". Every SAT answer is a witness checked by validate_sat's
check_witness (nonempty, 4-regular, inside the graph). Every UNSAT graph (no 4-regular subgraph)
is written to UNSAT_OUT.g6. Independent of q4core.h.
"""
import sys
sys.path.insert(0, "[local path]")
import networkx as nx
from validate_sat import has_q4, check_witness

src = sys.stdin if sys.argv[1] == "-" else open(sys.argv[1])
sat = unsat = 0
with open(sys.argv[2], "w") as out:
    for line in src:
        line = line.strip()
        if not line:
            continue
        g = nx.from_graph6_bytes(line.encode())
        H = has_q4(g)
        if H is None:
            unsat += 1
            out.write(line + "\n")
            out.flush()
        else:
            check_witness(g, H)
            sat += 1
print(f"SAT {sat} UNSAT {unsat}", flush=True)
