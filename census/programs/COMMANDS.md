# Census commands

nauty 2.9.3 `geng` on the PATH; build the pair test with `clang -O2 -o pairc pairc.c`.
`./pairc f` prints every pair-free graph (graph6) and a summary line on stderr; `./pairc f H`
tests only the whole vertex set, which for a connected 4-regular graph is a Hamilton-decomposition
test. The logs in `../logs/` are the stderr summaries of these runs.

```
# validation: all graphs on 8 vertices (expects 10512 pair-free)
geng -q 8 | ./pairc f | wc -l
# maximum degree 6, minimum degree 4, at least 3n-4 edges (n = 11 shown)
geng -q -d4 -D6 11 29:33 | ./pairc f
# n = 12 in twelve parts
for r in 0 1 2 3 4 5 6 7 8 9 10 11; do geng -q -d4 -D6 12 32:36 $r/12 | ./pairc f & done; wait
# bipartite, same bounds (n = 17 shown)
geng -q -b -d4 -D6 17 47:51 | ./pairc f
# connected 4-regular graphs with no Hamilton decomposition (n = 16 shown)
geng -q -c -d4 -D4 16 | ./pairc f H
# all 6-regular graphs (n = 14 shown)
geng -q -d6 -D6 14 42:42 | ./pairc f
```

Notes on the runs:

- The validation count 10,512 is also found by `computations/erdos585_small.py --levelwise 8`, which
  shares no code with `pairc.c`.
- n = 12 ran in 12 parts as shown. Bipartite n = 18 and 6-regular n = 14 were split the same way,
  into 12 parts (`r/12`) and 6 parts (`r/6`); bipartite n = 13 to 16 ran unsplit like n = 17.
- Each `graphs=… with_pair=… pair_free=…` line is the summary from `pairc`. Lines such as
  `exit=0 (geng|pairc pipeline finished)` and the dates come from the shell loop that ran each part.
- Where OEIS lists the population, the counts match it: 12,346 graphs on 8 vertices (A000088),
  367,860 and 21,609,301 6-regular graphs on 13 and 14 vertices (A165627; the second includes two
  disjoint copies of K7), and 805,491 and 8,037,418 connected 4-regular graphs on 15 and 16 vertices
  (A006820).
- Times on the original machine: n = 11 in 12 s, n = 12 in about 4 minutes on 12 processes, and about
  1.5 hours for one of the 12 parts of bipartite n = 18.
- Minimum degree 4 (`-d4`) loses nothing: deleting a vertex of degree at most 3 from a pair-free graph
  with maximum degree at most 6 and at least 3n − 4 edges leaves one on n − 1 vertices with the same
  properties, so a smallest such graph has minimum degree at least 4.
- Debian and Ubuntu install `geng` as `nauty-geng`.
