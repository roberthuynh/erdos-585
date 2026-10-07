"""Build control graphs: Γ5 substituted into 5-regular bipartite multigraphs.

Γ5 local labels: I = a1 a2 a3 x4 x5 x6 -> 0..5, O = b1 b2 b3 o4 o5 o6 o7 -> 6..12, copy k at 13k + local.
Deficient slots: o5 (local 10, one link), o6 (11, two links), o7 (12, two links).

P1: L = x0y0 x4, x1y1 x4, x0y1, x1y0 (pair: two 2-cycles).        expect: pair (converse intuition)
P2: L = doubled 8-cycle plus a perfect matching (pair: two 8-cycles). expect: pair (converse intuition)
N1: L5 with the link rule stated in PROOF-R1.md lines 109-110.        expect: no pair (Theorem R1)
N2: L5 with a random valid link assignment (seed 7).                  expect: no pair (Theorem R1)
"""
import os
import random
from collections import Counter

O5, O6, O7 = 10, 11, 12
GAMMA5 = []
names = ["a1", "a2", "a3", "x4", "x5", "x6", "b1", "b2", "b3", "o4", "o5", "o6", "o7"]
ix = {s: i for i, s in enumerate(names)}
for a in ["a1", "a2", "a3"]:
    for b in ["b1", "b2", "b3"]:
        GAMMA5.append((ix[a], ix[b]))
for v, nbrs in [("x4", ["b1", "b2", "b3"]), ("o4", ["a1", "a2", "x4"]), ("x5", ["b1", "b2", "o4"]),
                ("o5", ["a3", "x4", "x5"]), ("x6", ["b3", "o4", "o5"]), ("o6", ["a1", "a2", "x6"]),
                ("o7", ["a3", "x5", "x6"])]:
    for w in nbrs:
        GAMMA5.append((ix[v], ix[w]))
assert len(GAMMA5) == 30


def build(ncopies, links):
    """links: list of (copy_u, slot_u, copy_w, slot_w)."""
    E = []
    for k in range(ncopies):
        for (a, b) in GAMMA5:
            E.append((13 * k + a, 13 * k + b))
    use = Counter()
    for (u, su, w, sw) in links:
        assert u != w
        E.append((13 * u + su, 13 * w + sw))
        use[(u, su)] += 1
        use[(w, sw)] += 1
    for k in range(ncopies):
        assert use[(k, O5)] == 1 and use[(k, O6)] == 2 and use[(k, O7)] == 2, (k, use)
    keys = [(min(a, b), max(a, b)) for a, b in E]
    assert len(set(keys)) == len(keys), "not simple"
    deg = Counter(x for e in E for x in e)
    assert all(deg[v] == 5 for v in range(13 * ncopies))
    return E


def write(name, E, comment):
    os.makedirs("controls", exist_ok=True)
    with open(os.path.join("controls", name + ".edges"), "w") as f:
        f.write("# %s\n" % comment)
        for a, b in E:
            f.write("%d %d\n" % (a, b))


# P1
links = [(0, O6, 2, O6), (0, O6, 2, O7), (0, O7, 2, O6), (0, O7, 2, O7),
         (1, O6, 3, O6), (1, O6, 3, O7), (1, O7, 3, O6), (1, O7, 3, O7),
         (0, O5, 3, O5), (1, O5, 2, O5)]
write("P1", build(4, links), "control P1: Γ5 into x0y0^4 x1y1^4 x0y1 x1y0")

# P2: cycle positions 0..7 (even = x side, odd = y side)
links = []
for p in range(8):
    q = (p + 1) % 8
    links.append((p, O6, q, O6))
    links.append((p, O7, q, O7))
for (p, q) in [(0, 3), (2, 5), (4, 7), (6, 1)]:
    links.append((p, O5, q, O5))
write("P2", build(8, links), "control P2: Γ5 into doubled 8-cycle plus perfect matching")

# L5 with copies x0..x3 = 0..3, y0..y3 = 4..7
X = {"x0": 0, "x1": 1, "x2": 2, "x3": 3, "y0": 4, "y1": 5, "y2": 6, "y3": 7}
L5 = {("x0", "y2"): 2, ("x0", "y3"): 3, ("x1", "y1"): 1, ("x1", "y2"): 3, ("x1", "y3"): 1,
      ("x2", "y0"): 2, ("x2", "y1"): 3, ("x3", "y0"): 3, ("x3", "y1"): 1, ("x3", "y3"): 1}

# N1: the rule of lines 109-110
links = []
for (a, b) in [("x0", "y3"), ("x1", "y2"), ("x2", "y1"), ("x3", "y0")]:
    for s in (O5, O6, O7):
        links.append((X[a], s, X[b], s))
for (a, b) in [("x0", "y2"), ("x2", "y0")]:
    links.append((X[a], O6, X[b], O6))
    links.append((X[a], O7, X[b], O7))
links += [(X["x1"], O6, X["y1"], O6), (X["x1"], O7, X["y3"], O6),
          (X["x3"], O6, X["y1"], O7), (X["x3"], O7, X["y3"], O7)]
write("N1", build(8, links), "control N1: Γ5 into L5, link rule of PROOF-R1.md lines 109-110")

# N2: random valid assignment
rng = random.Random(7)
while True:
    slots = {k: [O5, O6, O6, O7, O7] for k in range(8)}
    for k in slots:
        rng.shuffle(slots[k])
    links = []
    for (a, b), m in L5.items():
        for _ in range(m):
            links.append((X[a], slots[X[a]].pop(), X[b], slots[X[b]].pop()))
    try:
        E = build(8, links)
        break
    except AssertionError:
        continue
write("N2", E, "control N2: Γ5 into L5, random valid link assignment (seed 7)")
print("wrote controls/P1.edges P2.edges N1.edges N2.edges")
