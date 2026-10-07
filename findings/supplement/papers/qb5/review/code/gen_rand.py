# Own random generator (referee): C2 instances with a W-small 2-block T on Z_U and a random 3-block B.
# T: sides T_U (t+2), T_W (t), every T_W vertex adjacent to exactly 6 T_U vertices.
# B: sides B_U (b), B_W (b+3), every B_U vertex adjacent to exactly 6 B_W vertices.
# Cut: 10 edges T_U--B_W, T_U cut degrees forced by D(T_U) = 2 (Z_U = {u0} or {u1,u2}), Delta <= 6.
# Usage: gen_rand.py t b zu count seed
import random, sys
t, b, zu, count, seed = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
rng = random.Random(seed)
def g6(n, E):
    A = set((min(x,y), max(x,y)) for x, y in E)
    bits = [1 if (i, j) in A else 0 for j in range(1, n) for i in range(j)]
    while len(bits) % 6: bits.append(0)
    s = chr(63 + n)
    for i in range(0, len(bits), 6):
        v = 0
        for x in bits[i:i+6]: v = 2*v + x
        s += chr(63 + v)
    return s
TU = list(range(t + 2)); TW = list(range(t + 2, 2*t + 2))
BU = list(range(2*t + 2, 2*t + 2 + b)); BW = list(range(2*t + 2 + b, 2*t + 2 + 2*b + 3))
n = 2*t + 2*b + 5
out = []; tries = 0
while len(out) < count and tries < 200000:
    tries += 1
    E = set()
    for w in TW:
        for u in rng.sample(TU, 6): E.add((u, w))
    for u in BU:
        for w in rng.sample(BW, 6): E.add((u, w))
    degT = {u: sum(1 for (x, y) in E if x == u) for u in TU}
    deff = {u: 0 for u in TU}
    if zu == 'u0': deff[rng.choice(TU)] = 2
    else:
        a, c = rng.sample(TU, 2); deff[a] = 1; deff[c] = 1
    cneed = {u: 6 - deff[u] - degT[u] for u in TU}
    if any(v < 0 for v in cneed.values()) or sum(cneed.values()) != 10: continue
    degB = {w: sum(1 for (x, y) in E if y == w) for w in BW}
    room = {w: min(3, 6 - degB[w]) for w in BW}
    stubs = [u for u in TU for _ in range(cneed[u])]
    rng.shuffle(stubs)
    ok = True; cut = set()
    for u in stubs:
        opts = [w for w in BW if room[w] > 0 and (u, w) not in cut]
        if not opts: ok = False; break
        w = rng.choice(opts); cut.add((u, w)); room[w] -= 1
    if not ok: continue
    E |= cut
    deg = {}
    for (x, y) in E: deg[x] = deg.get(x, 0) + 1; deg[y] = deg.get(y, 0) + 1
    if any(deg.get(v, 0) < 4 or deg.get(v, 0) > 6 for v in range(n)): continue
    assert len(E) == 3*n - 5
    out.append(g6(n, E))
print("\n".join(out))
print(f"t={t} b={b} zu={zu} made={len(out)} tries={tries}", file=sys.stderr)
