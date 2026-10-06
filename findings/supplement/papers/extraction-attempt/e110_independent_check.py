"""Independent finite certificate checks for E110. No search for cycle pairs."""
from pathlib import Path
import ast
import hashlib
import itertools
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
AUTHOR = HERE.parent / "main-extraction"
source_path = ROOT / "openmath/Openmath/Proofs/BipartiteFive.lean"
source = source_path.read_text()
saved = json.loads((ROOT / "reports/585-overnight/paper109/bipartite-five-check/verification.json").read_text())
controls = json.loads((AUTHOR / "CONTROL-CHECK.json").read_text())
source_sha = hashlib.sha256(source_path.read_bytes()).hexdigest()
assert source_sha == saved["proof_sha256"] == controls["source_sha256"]
assert saved["result"] == "PASS"

block = set(ast.literal_eval(re.search(r"def blockEdges\b.*?:=\s*(\[.*?\])", source, re.S).group(1)))
def pair(a, b):
    return (a, b) if a < b else (b, a)
block = {pair(*e) for e in block}
# These are the literal recursive connectors inspected in the unchanged source.
l26 = {(9, 22), (11, 24), (12, 25)}
l52 = {(11, 50), (12, 51), (24, 37)}
l104 = {(38, 77), (25, 90)}
def adj13(a, b):
    return pair(a, b) in block
def adj26(a, b):
    return (a // 13 == b // 13 and adj13(a % 13, b % 13)) or pair(a, b) in l26
def adj52(a, b):
    return (a // 26 == b // 26 and adj26(a % 26, b % 26)) or pair(a, b) in l52
def adj104(a, b):
    return (a // 52 == b // 52 and adj52(a % 52, b % 52)) or pair(a, b) in l104
def color(v):
    return 0 if ((v % 13 in {3, 4, 5, 7, 9, 11, 12}) == (v // 13 % 2 == 1)) else 1

V0 = set(range(104))
edges = {(a, b) for a, b in itertools.combinations(V0, 2) if adj104(a, b)}
assert len(edges) == 260
assert all(sum(v in e for e in edges) == 5 for v in V0)
assert all(color(a) != color(b) for a, b in edges)
deleted = {0, 55}
V = V0 - deleted
H = {e for e in edges if not set(e) & deleted}
degrees = {v: sum(v in e for e in H) for v in V}
assert len(H) == 250
assert {d: sum(t == d for t in degrees.values()) for d in {4, 5}} == {4: 10, 5: 92}
P = {v for v in V if color(v) == 1}
Q = V - P
assert len(P) == len(Q) == 51
X = P & set(range(52))
Y = Q & set(range(52))
assert len(X) == 26 and len(Y) == 25
def cut_edges(A, B):
    return {e for e in H if (e[0] in A and e[1] in B) or (e[1] in A and e[0] in B)}
a_edges, b_edges = cut_edges(X, Q - Y), cut_edges(P - X, Y)
assert a_edges == {(38, 77)} and b_edges == {(25, 90)}
dx = sum(5 - degrees[v] for v in X)
dy = sum(5 - degrees[v] for v in Y)
assert (dx, dy) == (5, 0)
assert dx - dy == 5 * (len(X) - len(Y)) - len(a_edges) + len(b_edges)
matching = [tuple(e) for e in controls["balanced_deletion"]["perfect_matching"]]
assert len(matching) == 51 and all(pair(*e) in H for e in matching)
occurrences = [v for e in matching for v in e]
assert len(occurrences) == len(set(occurrences)) == len(V)
assert set(occurrences) == V

cycle_edges = []
for c in controls["Q4"]["cycles"]:
    assert c[0] == c[-1] and len(c) == 17 and set(c[:-1]) == set(range(16))
    E = {pair(x, y) for x, y in zip(c, c[1:])}
    assert len(E) == 16 and all((x ^ y).bit_count() == 1 for x, y in E)
    cycle_edges.append(E)
cube = {(x, y) for x, y in itertools.combinations(range(16), 2) if (x ^ y).bit_count() == 1}
assert not cycle_edges[0] & cycle_edges[1]
assert cycle_edges[0] | cycle_edges[1] == cube
crossings = [[sum(((x ^ y) >> j) & 1 for x, y in E) for E in cycle_edges] for j in range(4)]
assert crossings == [[4, 4], [6, 2], [4, 4], [2, 6]]
max_codegree = max(sum((u ^ w).bit_count() == 1 and (v ^ w).bit_count() == 1 for w in range(16)) for u, v in itertools.combinations(range(16), 2))
assert max_codegree == 2

states = list(itertools.product(range(3), repeat=2))
# Independent bitset enumeration of the entire cross-incompatibility relation.
incompatible = [sum(1 << j for j, t in enumerate(states) if s[0] == t[0] or s[1] == t[1]) for s in states]
maximum = 0
for left in range(512):
    right = 511
    for i in range(9):
        if left & (1 << i):
            right &= incompatible[i]
    maximum = max(maximum, left.bit_count() * right.bit_count())
assert maximum == 9

freeze = json.loads((AUTHOR / "FREEZE.json").read_text())
hashes = {}
for name, spec in freeze["files"].items():
    payload = (AUTHOR / name).read_bytes()
    actual = hashlib.sha256(payload).hexdigest()
    assert actual == spec["sha256"] and len(payload) == spec["bytes"]
    hashes[name] = actual
out = {
    "status": "all independent finite certificate checks passed",
    "scope": "source receipt identity, source-adjacency H102, Hall cut, supplied matching, supplied Q4 cycles, nine-state bound, author manifest; no avoidance search, Lean, or oracle",
    "parent_proof_sha256_matches_saved_PASS": source_sha,
    "H102": {"vertices": 102, "edges": 250, "degree_counts": {"4": 10, "5": 92}, "shore_sizes": [51, 51], "Hall_t_a_b_DX_DY": [1, 1, 1, 5, 0], "verified_matching_size": 51},
    "Q4_crossings": crossings,
    "Q4_max_codegree": max_codegree,
    "nine_state_max_product": maximum,
    "author_files_verified": hashes,
}
(HERE / "E110-INDEPENDENT-CHECK.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps({k: v for k, v in out.items() if k != "author_files_verified"}, indent=2))
