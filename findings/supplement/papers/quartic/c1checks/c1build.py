"""Sub-case instance builder, copied verbatim from check_subcase.py (split_sum, build) so that
other scripts can import it without running check_subcase.py."""
import random

from c1common import BG, random_bipartite_degrees


def split_sum(total, nparts, cap, rng):
    """random list of nparts nonnegative ints <= cap summing to total"""
    for _ in range(1000):
        parts = [0] * nparts
        for _ in range(total):
            i = rng.randrange(nparts)
            parts[i] += 1
        if max(parts) <= cap:
            return parts
    return None


def build(c, t, eps, variant, rng, capT=3):
    s = c + t
    Cp = list(range(c))                    # C'
    Ur = list(range(c, c + t))             # U - C'
    u1 = c + t - 1
    A = list(range(c + 2))                 # W indices 0..c+1
    Wr = list(range(c + 2, c + 2 + t - 1)) # W - A
    y = Wr[0]
    degU = {u: 6 for u in range(s)}
    degU[u1] = 5
    degW = {w: 6 for w in range(s + 1)}
    if eps == 1:
        for a in rng.sample(A, 6):
            degW[a] = 5
        degW[y] = 5
    elif variant == "y4":
        degW[y] = 4
        if rng.random() < 0.5:
            for a in rng.sample(A, 5):
                degW[a] = 5
        else:
            a4 = rng.choice(A)
            degW[a4] = 4
            for a in rng.sample([x for x in A if x != a4], 3):
                degW[a] = 5
    else:  # y55
        degW[y] = 5
        degW[Wr[1]] = 5
        for a in rng.sample(A, 5):
            degW[a] = 5
    # T-edge distribution
    r = split_sum(7, t, capT, rng)
    if r is None:
        return None
    r = dict(zip(Ur, r))
    if r[u1] > 2 and capT <= 3:
        return None
    sa = split_sum(7, c + 2, capT, rng)
    if sa is None:
        return None
    sa = dict(zip(A, sa))
    cstar, wprime = (None, None)
    if eps == 1:
        cstar = rng.choice(Cp)
        wprime = rng.choice(Wr)
    # P2: U-side C', W-side A
    duP2 = [6 - (1 if (eps == 1 and u == cstar) else 0) for u in Cp]
    dwP2 = [degW[a] - sa[a] for a in A]
    if min(dwP2) < 0 or max(dwP2) > c:
        return None
    P2 = random_bipartite_degrees(duP2, dwP2, rng)
    if P2 is None:
        return None
    # P1: U-side U - C', W-side W - A
    duP1 = [degU[u] - r[u] for u in Ur]
    dwP1 = [degW[w] - (1 if w == wprime else 0) for w in Wr]
    if min(duP1) < 0 or max(duP1) > t - 1 or max(dwP1) > t:
        return None
    P1 = random_bipartite_degrees(duP1, dwP1, rng)
    if P1 is None:
        return None
    edges = []
    for (i, j) in P2.edges:
        edges.append((Cp[i], A[j]))
    for (i, j) in P1.edges:
        edges.append((Ur[i], Wr[j]))
    # T edges: match stubs
    for _ in range(200):
        ast = [a for a in A for _ in range(sa[a])]
        ust = [u for u in Ur for _ in range(r[u])]
        rng.shuffle(ust)
        T = list(zip(ust, ast))
        if len(set(T)) == 7:
            break
    else:
        return None
    edges += T
    f = None
    if eps == 1:
        f = (cstar, wprime)
        edges.append(f)
    G = BG(s, s + 1, edges)
    info = dict(c=c, t=t, eps=eps, variant=variant, s=s, Cp=Cp, Ur=Ur, u1=u1, A=[s + a for a in A],
                Wr=[s + w for w in Wr], y=s + y, T=[(u, s + a) for (u, a) in T],
                f=None if f is None else (f[0], s + f[1]), r=r, sa={s + a: sa[a] for a in A})
    return G, info


