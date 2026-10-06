"""gen_inst.py (referee's own generator, wave4/theory review).

Writes graph6 files of small bipartite test graphs (Delta <= 6) for rigidcheck:
  rand_small.g6  random a+a graphs, a in {4, 5}, degrees in [4, 6]       (Theorem 2.1 brute force)
  rand_mid.g6    random a+a graphs, a in {6, 7}, degrees in [4, 6]
  blocks.g6      two dense blocks (K44 minus 0-2 edges, or K55 minus a perfect matching and more)
                 joined by 1-4 cross edges, plus 0-5 random extra edges (rigid sets appear here)
Usage: python gen_inst.py seed outdir
"""
import random
import sys
import networkx as nx


def g6(G):
    return nx.to_graph6_bytes(nx.convert_node_labels_to_integers(G, ordering="sorted"), header=False).decode().strip()


def rand_bip(a, rnd, extra):
    P = list(range(a)); Q = list(range(a, 2 * a))
    for _ in range(1000):
        G = nx.Graph(); G.add_nodes_from(P + Q)
        ok = True
        # random 4-regular core via random permutations (union of 4 perfect matchings, retry on clash)
        for _k in range(4):
            for _t in range(200):
                perm = Q[:]; rnd.shuffle(perm)
                if all(not G.has_edge(p, q) for p, q in zip(P, perm)):
                    G.add_edges_from(zip(P, perm)); break
            else:
                ok = False; break
        if not ok:
            continue
        for _ in range(extra):
            p = rnd.choice(P); q = rnd.choice(Q)
            if not G.has_edge(p, q) and G.degree(p) < 6 and G.degree(q) < 6:
                G.add_edge(p, q)
        # random deletions keeping degree >= 4 is pointless here: core is 4-regular
        return G
    return None


def two_blocks(rnd):
    # block i has classes Pi, Qi of size ai
    a1 = rnd.choice([4, 4, 5]); a2 = rnd.choice([4, 4, 5])
    if a1 + a2 > 9:
        a2 = 4
    G = nx.Graph()
    P1 = [("p1", i) for i in range(a1)]; Q1 = [("q1", i) for i in range(a1)]
    P2 = [("p2", i) for i in range(a2)]; Q2 = [("q2", i) for i in range(a2)]
    for (P, Q, a) in ((P1, Q1, a1), (P2, Q2, a2)):
        for p in P:
            for q in Q:
                G.add_edge(p, q)
        if a == 5:  # K55 minus a perfect matching, then maybe minus more
            for i in range(5):
                G.remove_edge(P[i], Q[i])
            drop = 0
        else:
            drop = rnd.choice([0, 1, 1, 2])
        for _ in range(drop):
            es = [(p, q) for p in P for q in Q if G.has_edge(p, q)]
            p, q = rnd.choice(es)
            if G.degree(p) > 3 and G.degree(q) > 3:
                G.remove_edge(p, q)
    k = rnd.choice([1, 2, 2, 3, 4])
    for _ in range(k):
        if rnd.random() < 0.5:
            p = rnd.choice(P1); q = rnd.choice(Q2)
        else:
            p = rnd.choice(P2); q = rnd.choice(Q1)
        if G.degree(p) < 6 and G.degree(q) < 6:
            G.add_edge(p, q)
    for _ in range(rnd.choice([0, 1, 2, 3, 5])):
        if rnd.random() < 0.5:
            p = rnd.choice(P1 + P2); q = rnd.choice(Q1 + Q2)
        else:
            p = rnd.choice(P1); q = rnd.choice(Q1)
        if not G.has_edge(p, q) and G.degree(p) < 6 and G.degree(q) < 6:
            G.add_edge(p, q)
    # relabel P first
    order = sorted(G.nodes(), key=lambda x: (x[0][0] != "p", x))
    H = nx.relabel_nodes(G, {v: i for i, v in enumerate(order)})
    return H


def main():
    seed = int(sys.argv[1]); out = sys.argv[2]
    rnd = random.Random(seed)
    with open(f"{out}/rand_small_{seed}.g6", "w") as f:
        for _ in range(60):
            G = rand_bip(rnd.choice([4, 5]), rnd, rnd.randint(0, 8))
            if G is not None:
                f.write(g6(G) + "\n")
    with open(f"{out}/rand_mid_{seed}.g6", "w") as f:
        for _ in range(40):
            G = rand_bip(rnd.choice([6, 7]), rnd, rnd.randint(0, 6))
            if G is not None:
                f.write(g6(G) + "\n")
    with open(f"{out}/blocks_{seed}.g6", "w") as f:
        for _ in range(60):
            f.write(g6(two_blocks(rnd)) + "\n")


if __name__ == "__main__":
    main()
