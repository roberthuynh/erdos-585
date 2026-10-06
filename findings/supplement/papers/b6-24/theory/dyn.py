"""Repair dynamics on 4-factors. D(F): arcs p->q for F-edges, q->p for H-edges."""
import sys, random, collections
sys.path.insert(0, '.')
from tools import *

def digraph(I, F):
    D = nx.DiGraph()
    D.add_nodes_from(I.Y)
    for (p, q) in I.pq:
        if (p, q) in F: D.add_edge(p, q, f=1)
        else: D.add_edge(q, p, f=0)
    return D

def cycle_edges(I, cyc):
    """cyc: list of vertices v0..vk-1 (closed). Return set of (p,q) edges."""
    out = []
    for i in range(len(cyc)):
        u, v = cyc[i], cyc[(i + 1) % len(cyc)]
        out.append((u, v) if u in I.P else (v, u))
    return out

def swap(F, edges):
    F = set(F)
    for e in edges:
        if e in F: F.remove(e)
        else: F.add(e)
    return frozenset(F)

def lemma7_cycle(I, F, T):
    """Shortest cycle in D - {e1,e2} through an E0 H-arc (Lemma 7(a)); None if none."""
    D = digraph(I, F)
    cut = [(p, q) for (p, q) in F if (p in T) != (q in T)]
    for (p, q) in cut:
        if D.has_edge(p, q): D.remove_edge(p, q)
    best = None
    for (p, q) in I.E0(T):
        if (p, q) in F: continue
        # H-arc q -> p; need path p ~> q
        try:
            path = nx.shortest_path(D, p, q)
        except nx.NetworkXNoPath:
            continue
        if best is None or len(path) < len(best):
            best = path
    return best

def positive_cycle(I, F, T):
    """Any directed cycle of D(F) with positive gain for T (gain: +1 E0 H-arc, -1 E0 F-arc)."""
    E0 = set(I.E0(T))
    G = nx.DiGraph()
    for (p, q) in I.pq:
        w = 0
        if (p, q) in F:
            if (p, q) in E0: w = 1      # weight = -gain
            G.add_edge(p, q, weight=w)
        else:
            if (p, q) in E0: w = -1
            G.add_edge(q, p, weight=w)
    G.add_node('S')
    for v in I.Y: G.add_edge('S', v, weight=0)
    try:
        cyc = nx.find_negative_cycle(G, 'S')
    except nx.NetworkXError:
        return None
    cyc = cyc[:-1]
    return cyc

def atoms(I, F):
    B = I.bad_sets(F)
    V = frozenset(I.Y)
    fam = set()
    for T in B:
        fam.add(T); fam.add(V - T)
    mins = [T for T in fam if not any(U < T for U in fam)]
    return B, mins
