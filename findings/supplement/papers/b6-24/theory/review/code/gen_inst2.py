"""gen_inst2.py (referee's own generator): two-block graphs that always have a 4-factor.

Block types: K44 - e (ends p, q of degree 3) and K55 - perfect matching - e (ends of degree 3).
Two blocks are joined by the two compensating edges p(1)q(2), p(2)q(1) (so a 4-factor exists),
then 0-7 random extra edges are added anywhere subject to Delta <= 6.
Usage: python gen_inst2.py seed count outfile
"""
import random
import sys
import networkx as nx


def block(kind, tag):
    G = nx.Graph()
    a = 4 if kind == 4 else 5
    P = [(tag, "p", i) for i in range(a)]
    Q = [(tag, "q", i) for i in range(a)]
    for i, p in enumerate(P):
        for j, q in enumerate(Q):
            if kind == 5 and i == j:
                continue
            G.add_edge(p, q)
    # remove one edge p0 q_j
    j = 1 if kind == 5 else 0
    G.remove_edge(P[0], Q[j])
    return G, P, Q, P[0], Q[j]


def main():
    seed = int(sys.argv[1]); cnt = int(sys.argv[2]); out = sys.argv[3]
    rnd = random.Random(seed)
    with open(out, "w") as f:
        for _ in range(cnt):
            k1 = 4; k2 = rnd.choice([4, 4, 5])
            G1, P1, Q1, a1, b1 = block(k1, 1)
            G2, P2, Q2, a2, b2 = block(k2, 2)
            G = nx.union(G1, G2)
            G.add_edge(a1, b2); G.add_edge(a2, b1)
            P = P1 + P2; Q = Q1 + Q2
            for _e in range(rnd.randint(0, 7)):
                p = rnd.choice(P); q = rnd.choice(Q)
                if not G.has_edge(p, q) and G.degree(p) < 6 and G.degree(q) < 6:
                    G.add_edge(p, q)
            order = P + Q
            H = nx.relabel_nodes(G, {v: i for i, v in enumerate(order)})
            H = nx.convert_node_labels_to_integers(H, ordering="sorted")
            f.write(nx.to_graph6_bytes(H, header=False).decode().strip() + "\n")


if __name__ == "__main__":
    main()
