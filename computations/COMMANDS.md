# Reproducing f(1) to f(10)

Python 3.10 or later, standard library only. Run from the repository root. The programs write their
reports to files that git ignores (`*.out.md`, `585-verify.md`, `585-n9.md`, `*state*.json`);
`585-small-n.md` is the committed result.

## f(1) to f(8): backtracking, with a level-by-level cross-check (about 15 s)

    python3 computations/erdos585_small.py --nmin 1 --nmax 8 --levelwise 8

For each n the program finds f(n) and every extremal class, then counts the pair-free graphs again,
one edge at a time up to isomorphism, and prints `match=True` when the two agree. At n = 8 the second
count gives 12 extremal classes (175,560 labelled graphs) and 10,512 pair-free graphs in all,
counting the empty graph: the number the census pair test `census/programs/pairc.c` also finds.

## f(7) and f(8): an independent checker (a few seconds)

    python3 computations/erdos585_verify.py lower --state computations/verify-state.json
    python3 computations/erdos585_verify.py upper7 --state computations/verify-state.json
    python3 computations/erdos585_verify.py extremal7 --state computations/verify-state.json
    python3 computations/erdos585_verify.py upper8 --state computations/verify-state.json
    python3 computations/erdos585_verify.py extremal8 --state computations/verify-state.json

Written without code from `erdos585_small.py`. It re-checks every witness, and its counts of graphs
up to isomorphism match OEIS A008406.

## f(9) = 23 and f(10) = 27 (about 20 s)

    python3 computations/erdos585_n9.py levels --n 9 --k 13 --state computations/n9-state.json
    python3 computations/erdos585_n9.py comp --n 9 --k 12 --state computations/n9-state.json
    python3 computations/erdos585_n9.py comp --n 9 --k 13 --state computations/n9-state.json
    python3 computations/erdos585_n9.py ext10 --n 9 --k 13 --state computations/n9-state.json
    python3 computations/erdos585_n9.py ext --n 9 --state computations/n9-state.json

- `levels` lists the graphs on 9 vertices with up to 13 edges, up to isomorphism: 5,995 classes with
  12 edges and 10,120 with 13 (both OEIS A008406).
- `comp --k 12`: every 24-edge graph on 9 vertices is the complement of a 12-edge graph, and all 5,995
  complements have a pair, each with a re-checked witness. So f(9) ≤ 23.
- `comp --k 13`: exactly 8 classes of 23-edge graphs have no pair (997,920 labelled graphs). So
  f(9) = 23, with 8 extremal classes.
- `ext10` adds a tenth vertex to each of the 8 classes. Joined to 4 vertices it gives 27-edge graphs,
  28 of them without a pair (7 classes), so f(10) ≥ 27. Joined to 5 vertices it gives 1,008 graphs
  with 28 edges, and every one has a pair.
- Upper bound f(10) ≤ 27. A pair-free graph on 10 vertices with 28 edges has a vertex of degree at
  most 5, since the average degree is 5.6. Deleting a vertex of minimum degree leaves a pair-free graph
  on 9 vertices with at least 23 = f(9) edges, so that degree is exactly 5 and what remains is one of
  the 8 extremal classes. All 1,008 such graphs have a pair, a contradiction.
- `ext` runs the same argument one size down: all 672 degree-5 extensions of the 12 extremal classes
  for n = 8 have a pair, which gives f(9) ≤ 23 a second way.

## The same values by backtracking (slow)

    python3 computations/erdos585_small.py --nmin 9 --nmax 9 --fprev 19 --value-only --seed 22
    python3 computations/erdos585_small.py --nmin 10 --nmax 10 --fprev 23 --value-only

A third, separate search for f(9) and f(10). As originally run, n = 9 took 151.3 s (778,065 nodes) and
n = 10 took 21,925.5 s (31,175,037 nodes).
