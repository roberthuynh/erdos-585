# Erdős Problem 585: kernel-checked finite results, three pair-free 5-regular graphs, and a reduction at degree six

Robert Huynh · October 6, 2026

## Summary

**The problem.** What is the maximum number f(n) of edges of a graph on n vertices with no two
edge-disjoint cycles on the same vertex set? ([erdosproblems.com/585](https://www.erdosproblems.com/585);
[Er76b].) Call two such cycles a **pair**. It is known that c·n log log n ≤ f(n) ≤ n (log n)^O(1)
[PRS95, CJMM24]. Nothing here changes either bound.

**What this document contains.** Each item is labeled by its evidence: **Lean-proved** (checked by
the Lean kernel), **computed** (exhaustive search), or **written proof** (AI-written and reviewed by a separate AI
agent in a fresh context, with its own code where it computed, often on the same model as the author;
section 7 names the models; not yet checked by a mathematician, making each one still a candidate).

1. **4-regular subgraphs at maximum degree six** (**Lean-proved**): every bipartite graph with
   maximum degree at most 6, n ≥ 3 vertices and at least 3n − 5 edges has a nonempty 4-regular
   subgraph (QB(5)); QB(4), the same with n ≥ 2 vertices and at least 3n − 4 edges, came first and has
   a shorter proof. So for every bipartite 6-regular graph B and every vertex o, B − o has one. QB(4),
   with Tutte's f-factor theorem, gives 3n − 2 edges for all simple graphs with maximum degree at most
   6 (P_2; **written proof**, three reviews). For bipartite graphs with maximum degree at most 6 and
   4 ≤ n ≤ 19, an edge census by two methods finds that 3n − 7 edges already suffice, and graphs with
   3n − 8 edges and no nonempty 4-regular subgraph exist for 11 ≤ n ≤ 20 (**computed**, unreviewed;
   section 5, question 4). The nearest published bound the literature search found is 3n − 2 edges for
   bipartite graphs, where [AFK84, Remark 3.6] gives a nonempty 4-divisible subgraph, 4-regular when
   the maximum degree is at most 7. "QB(4)" and "QB(5)" are this project's labels, not names from the
   literature.
2. **Three pair-free 5-regular graphs** (**Lean-proved**): on 18 vertices, on 32 vertices, and a
   bipartite one on 104 vertices. No 5-regular graph on at most 16 vertices is pair-free
   (**computed**), so the 18-vertex one is the smallest. Degree 5 does not force a pair, even in
   bipartite graphs, and degree 6 is the first open case as far as I know.
3. **Exact values, bounds and a census**: the values through n = 10 reproduce the
   [Erdős Problem a Day report](https://erdosproblemaday.com/report/585)
   (July 28, 2026; read October 8, 2026). The new computational entries beyond that report
   are f(11) = 31 and f(12) = 36. Values through n = 7 are **Lean-proved**;
   the larger upper bounds are **computed**. The linear lower bounds are **Lean-proved**,
   and a census finds that maximum degree at most 6 and at least 3n − 4 edges force a pair
   through 14 vertices, and through 18 in bipartite graphs (**computed**).
   A calibration at degree 5 shows why the regular-graph part of this census is weak evidence
   (section 4.4).
4. **What B6 would give** (**written proof**): if every bipartite 6-regular graph has a pair (B6), then
   f(n) = Θ(n log log n), an immediate consequence of [PRS95] and [JS23], checked against those papers.
5. **Two steps toward B6**: B6 is equivalent to its vertex-deleted form, by a substitution theorem
   (**written proof**); and candidate written proofs that rest on four censuses, each with a second
   method (for one, only on the classes the proofs use, with shared search code), argue that the
   bipartite part of the census in item 3 extends to 23 vertices, so that every bipartite 6-regular
   graph on at most 24 vertices has a pair (**written proof** and **computed**; section 5, question 2).
6. **A conditional route to O(n (log n)⁴), and a barrier** (**written proof**; the barrier's statement
   is **Lean-proved**): a reduction of f(n) = O(n (log n)⁴) to the polylogarithmic-degree analog of
   B6, by [CJMM-reg, Theorem 1.5] applied directly; a proposed route to that analog through an open
   extraction statement; and a barrier to a specific proof method.

**How it was made.** AI systems (OpenAI: GPT-6 Astra, reasoning effort extra high and max; Anthropic:
Claude Fable 5.1 and Claude Opus 5.5) produced the proofs, programs and reviews under my direction.
Section 7 outlines what we did.
Every Lean-proved item passed a fresh check on the Lean files of `v0.3` on October 6, 2026, and `leanchecker` replayed every compiled module through the kernel. Nothing here is claimed as new until an expert has compared it with the
literature.

**Help needed.**

- *Key open questions:* are the three pair-free 5-regular graphs new or folklore, and does "every
  (bipartite) 6-regular graph has a pair" appear anywhere in the literature?
- *Checking the claims:* every claim in section 1 points to its evidence (a Lean declaration, a log or
  a written argument), and the appendices and the supplement hold the statements, edge lists, logs
  and reviews. A useful order is section 2 (the statement), section 4.1 (QB(4) and QB(5)), section 4.2
  with appendix B (the graphs), then section 4.6 with appendix D (Theorem R1). Section 6 lists specific
  checks.

## 1. Claims and evidence

Paths starting with `supplement/` are in the supplement, the folder beside this document; all other
paths are in the public repository at tag `v0.3`. A name in parentheses after a path is relative to that
path. Appendix A gives every Lean statement with its file and line. Here n is the number of
vertices, e the number of edges and Δ the maximum degree.

| | Claim | Evidence | Section; files |
|---|---|---|---|
| 1 | QB(5): a bipartite graph with Δ ≤ 6, n ≥ 3 and e ≥ 3n − 5 has a nonempty 4-regular subgraph | Lean-proved; also a written proof in four parts, each reviewed once | §4.1; `Openmath/Proofs/QB5/Statement.lean`, `supplement/papers/qb5/` |
| 2 | QB(4): a bipartite graph with Δ ≤ 6, n ≥ 2 and e ≥ 3n − 4 has a nonempty 4-regular subgraph; so does B − o, for every bipartite 6-regular B and every vertex o | Lean-proved | §4.1; `Openmath/Proofs/QB4/Statement.lean` |
| 3 | P_2: every graph with Δ ≤ 6, n ≥ 2 and e ≥ 3n − 2 has a nonempty 4-regular subgraph | written proof, three reviews | §4.1; `supplement/papers/quartic/C1-PAPER.md` (section 5.4) and its reviews |
| 4 | ex(n) ≤ 3n − 8 for 4 ≤ n ≤ 19, with ex(17) = 43, ex(18) = 46, ex(19) = 49, for bipartite graphs with Δ ≤ 6 and no nonempty 4-regular subgraph; so 3n − 7 edges force a nonempty 4-regular subgraph for 4 ≤ n ≤ 19 | computed, two methods, unreviewed | §5; `supplement/census/edge/` (`EX.md`, `method-b/EX-B.md`) |
| 5 | A pair-free 5-regular graph on 18 vertices | Lean-proved | §4.2; `Openmath/Proofs/RegularFive18.lean`, `graphs/regular-five-18.edges` |
| 6 | A pair-free 5-regular graph on 32 vertices | Lean-proved | §4.2; `Openmath/Proofs/RegularFive.lean`, `graphs/regular-five-32.edges` |
| 7 | A pair-free bipartite 5-regular graph on 104 vertices | Lean-proved | §4.2; `Openmath/Proofs/BipartiteFive.lean`, `graphs/bipartite-five-104.edges` |
| 8 | No pair-free 5-regular graph on at most 16 vertices, so the smallest has 18 | computed; through 14 vertices by two methods; at 16 by one complete census (unreviewed), with a second method on its triangle-free and bipartite graphs and on a 0.14% sample | §4.4; `supplement/census/calibration/logs/` (`driver_reg5_n14.log`; the second method: last line of `driver_xc_reg5_n14.log`), `supplement/census/calibration/n16/REG5N16.md`, `supplement/census/calibration/n16-second-method/REG5N16-B.md` |
| 9 | f(n) = n(n−1)/2 for n ≤ 4; f(5) = 9, f(6) = 12, f(7) = 16 | Lean-proved | §4.3; `Openmath/Proofs/Final.lean` |
| 10 | f(8) = 19, f(9) = 23, f(10) = 27 | computed, two to four separately written methods each | §4.4; `computations/COMMANDS.md`, `supplement/small-values/` |
| 11 | f(11) = 31, f(12) = 36 | computed, two methods each; the lower bounds Lean-proved | §4.4; `supplement/small-values/logs/`; the lower bounds in `Openmath/Proofs/Final.lean` |
| 12 | Linear lower bounds, the strongest of them for large n being f(n) ≥ 5n − 15⌊√n⌋ − 10 for n ≥ 16 | Lean-proved | §4.3; `Openmath/Proofs/Final.lean` |
| 13 | Δ ≤ 6 and e ≥ 3n − 4 force a pair for 2 ≤ n ≤ 14, and for bipartite n ≤ 18 | computed; n ≤ 13 independently replicated, n = 14 by one reviewed program; bipartite 14 ≤ n ≤ 18 by one program, with a second on the classes of section 5, question 2 | §4.4; `census/logs/` (n = 11 and 12, bipartite 13 to 18); `supplement/papers/census-extension/SMS-CENSUS-REVIEW.md` (a second program for every n ≤ 12, and the replication at n = 13); `supplement/census/programs/gen585/runs.log` (n = 13, 14) |
| 14 | No pair-free 6-regular graph on at most 15 vertices | computed (n = 15 via row 13 at n = 14) | §4.4; `census/logs/reg6-n13.err`, `census/logs/reg6-n14-part*.err` |
| 15 | B6 ⇒ f(n) = Θ(n log log n), an immediate consequence of [PRS95] and [JS23] | written proof, checked against the sources | §4.5; [PRS95], [JS23], [CJMM24] |
| 16 | Theorem R1; B6 ⇔ its vertex-deleted form | written proof, reviewed | §4.6; appendix D, `supplement/papers/r1-substitution/` |
| 17 | Δ ≤ 6 and e ≥ 3n − 4 force a pair in every bipartite graph with 2 ≤ n ≤ 23; so every bipartite 6-regular graph on at most 24 vertices has, for every vertex o, a pair avoiding o | written proof and computed; three written proofs, each reviewed once, and Lemma 4.4 of `supplement/papers/quartic/C1-PAPER.md` (three reviews); four censuses, two methods each (for one, the second covers only the classes the proofs use and shares the first method's Hamilton-cycle search) | §5; `supplement/papers/b6-24/` (`c1type/PAPER.md`, Corollary C, first), `supplement/papers/pairs/`, `supplement/census/pairs-lane/`, `supplement/census/h22/`, `supplement/census/l5/` |
| 18 | S6 (section 5, question 3) holds for every bipartite 6-regular graph on 22 vertices | computed, one method, unreviewed; an independent spot-check of 0.376% agrees | §5; `supplement/census/s6n22/` (`RESULT.md`, `spot-check/SPOTCHECK.md`) |
| 19 | Two routes toward B6 ruled out by counterexamples | computed certificates; reviewed once, accepted with fixes | §5; `supplement/papers/pairs/` |
| 20 | f(n) = O(n (log n)⁴) if every bipartite r-regular graph with r ≥ A (log 2N)³ has a pair, by [CJMM-reg, Theorem 1.5] | written proof, conditional | §4.7; `supplement/papers/` (`lemma-f/`, `bipartite-hamilton/`, `extraction-attempt/`, `vertex-deletion/`) |
| 21 | A barrier to a specific proof method (R1-plus) | Lean-proved statement; written argument | §4.8; `supplement/lean/Openmath/Proofs/ParabolaBarrier104.lean` |
| 22 | Twin-core forcing, a special case at 3v − 2 edges | Lean-proved | §4.3; `supplement/lean/Openmath/Proofs/TwinNoSingleton.lean`, `TwinCoreForcing.lean` |

Every review named in this table was by an AI agent (section 7); no mathematician has reviewed any
written proof.

Sections 4.1 and 5 also report some computed facts, each with its file; nothing else is claimed. In
particular, nothing here bounds f(n) asymptotically beyond the known results.

## 2. Definitions

The statement file is `Openmath/Target.lean`, byte-identical to the statement submitted to the
formal-conjectures repository in pull request 6774, which is still under review (its SHA-256 is
recorded as `STATEMENT_SHA256` in `scripts/check_axioms.py`). Its two definitions, verbatim
(lines 44-46 and 53-55):

```lean
def HasTwoEdgeDisjointCyclesSameVertexSet {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (u v : V) (p : G.Walk u u) (q : G.Walk v v), p.IsCycle ∧ q.IsCycle ∧
    {w | w ∈ p.support} = {w | w ∈ q.support} ∧ List.Disjoint p.edges q.edges

noncomputable def maxEdges (n : ℕ) : ℕ :=
  sSup {m | ∃ G : SimpleGraph (Fin n), ¬ HasTwoEdgeDisjointCyclesSameVertexSet G ∧
    G.edgeSet.ncard = m}
```

- The predicate says G has a pair: two closed walks that are cycles in Mathlib's sense, visit the same
  vertex set (possibly a proper subset of V(G)), and share no edge. Equivalently, some subgraph of G is
  4-regular and is the union of two edge-disjoint Hamilton cycles of itself.
- `maxEdges n` is f(n). Its set of edge counts contains 0 and is bounded by n(n−1)/2, so the supremum
  is attained.
- The predicate is not vacuous: K5 has a pair, proved in `Target.lean` itself and, for the `Finset`
  form used in the proofs (`HasPairF`), as `Erdos585.hasPair_top_five`. Arithmetic in the statements is on ℕ, so
  `a - b` is truncated at 0.

## 3. How to verify

The Lean results build with Lean `v4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and
formal_conjectures `137aec5c7abd3aa61f7a73138a97279acfc79e93`. From the root of the public repository
[roberthuynh/erdos-585](https://github.com/roberthuynh/erdos-585) at tag `v0.3`:

```bash
lake exe cache get && lake build
./check.sh Openmath/Proofs/QB5/Statement.lean Erdos585.qb5
```

`check.sh` builds the file, counts `sorry` (comments ignored) and prints the axioms; a pass ends with
`RESULT: PASS build=ok sorry=0 axioms=[propext,Classical.choice,Quot.sound] disallowed=[]`. No Lean
file uses `native_decide`, and `lake env leanchecker <module>`, which replays a compiled module's
declarations through the kernel, passes on every module (transcripts in `supplement/checks/`).
Transcripts of runs that rebuild `Target.lean` also show its four "declaration uses `sorry`"
warnings: it states the open problem with `sorry`, the formal-conjectures convention, and the axiom
check shows that no result depends on it. `python3 scripts/check_axioms.py` checks the axioms and statements of all 25 headline
results at once. Lean files outside the repository's Lean build are in
`supplement/lean/Openmath/Proofs/`: copy them into the repository's `Openmath/Proofs/` and run the same
command. `supplement/MANIFEST.md` gives each supplement file's SHA-256, and appendix A has every
statement verbatim.

## 4. Results

### 4.1 4-regular subgraphs at maximum degree six (Lean-proved; written proof, reviewed)

**QB(5)** (`Erdos585.qb5`). Every finite simple bipartite graph with maximum degree at most 6, n ≥ 3
vertices and at least 3n − 5 edges has a nonempty 4-regular subgraph. Its proof builds on QB(4)'s; see
*Is 3n − 4 best possible?* below.

**QB(4)** (`Erdos585.qb4`). Every finite simple bipartite graph with maximum degree at most 6, n ≥ 2
vertices and at least 3n − 4 edges has a nonempty 4-regular subgraph.

**The vertex-deleted form of QB(4)** (`Erdos585.exists_four_regular_avoiding_of_bipartite_six_regular`). For
every bipartite 6-regular graph B and every vertex o, B − o has a nonempty 4-regular subgraph. This
settles G110, a question the project's earlier notes left open (`supplement/papers/six-port-gadget/`).
B − o has 3n − 3 edges on its n vertices, so it is also a case of QB(4).

**P_2** (written proof). Every simple graph, bipartite or not, with maximum degree at most 6, n ≥ 2 vertices
and at least 3n − 2 edges has a nonempty 4-regular subgraph.

*The Lean statements.* All three are about Mathlib's `SimpleGraph` on a finite vertex type and take
the graph's decidability instance as an argument (`[DecidableRel G.Adj]`), so they apply to a concrete
graph as it is given. QB(4) assumes `G.IsBipartite`, `G.maxDegree ≤ 6`, `2 ≤ Fintype.card V` and
`3 * Fintype.card V ≤ G.edgeSet.ncard + 4`, which is e ≥ 3n − 4 without truncated subtraction; QB(5)
assumes the same with `3 ≤ Fintype.card V` and `3 * Fintype.card V ≤ G.edgeSet.ncard + 5`; the
vertex-deleted form assumes `B.IsBipartite` and `B.IsRegularOfDegree 6`. The conclusion is a subgraph
`H` with at least one vertex (`H.verts.Nonempty`) in which every vertex has degree exactly 4
(`H.coe.IsRegularOfDegree 4`, whose degree count uses classical decidability; the value does not
depend on it), and in the vertex-deleted form `o ∉ H.verts`. Appendix A gives all three
verbatim. All three pass `check.sh` with only the three standard axioms, and `leanchecker` replays the
six modules of `Openmath/Proofs/QB4/` and the 17 of `Openmath/Proofs/QB5/` through the kernel.

*How the proof goes.* The written proof is `supplement/papers/quartic/C1-PAPER.md`; the table below
maps its lemmas to the Lean declarations. Write D for deficiency, the sum of 6 − deg over a set of
vertices, e(S) for the number of edges with both ends in S, and g(S) = 6|S| − 2e(S). A bipartite
graph with Δ ≤ 6 and exactly 3n − 4 edges has g(V) = 8, which leaves two shapes: equal sides with
deficiency at most 4 on each (the class E4), or sides of sizes s and s + 1 whose smaller side has
deficiency at most 1 (the class C1; elsewhere C1 also names a cycle of a pair, in appendices C and D,
and a confidence rating, in section 8). E4 reduces to smaller C1 instances
(Lemma 1.5), so QB(4) is equivalent to "every C1 instance has a 4-regular subgraph" (Theorem 4.3,
Corollary 5.3). In a smallest C1 instance G without one:

1. Every vertex set S with 2 ≤ |S| ≤ n − 1 has g(S) ≥ 10, since a denser set would span an E4
   instance of size at most s or a smaller C1 instance, both settled by the induction (Lemma 2.1).
2. Call a vertex of the larger side with degree at most 5 a port. For each port y, G − y is balanced
   and has no spanning 4-regular subgraph, so the bipartite 4-factor criterion (Lemma 1.4; in Lean,
   Hall's theorem applied to Tutte's gadget) gives a violated cut. Sparsity fixes its shape: the
   smaller side has deficiency exactly 1, at one vertex u1 of degree 5, and the complement of the cut
   is a set Q with g(Q) = 10 and one more vertex on the smaller side than on the larger, containing y
   and u1 (Lemma 3.2). Call Q a petal.
3. u1 has at least three neighbors in every petal, so two petals always share a second vertex, and
   with the submodularity of g the union of two petals is a petal (Lemmas 4.1, 4.2).
4. The union of the petals of all ports is therefore a petal. By Lemma 4.1(2) a petal has in-petal
   deficiency exactly 2 on the larger side of G, so it carries at most 2 of that side's deficiency,
   but the ports carry all of it, which is 7 (Theorem 4.3).

P_2 follows from the same theorem: by Tutte's f-factor theorem and a counting identity from an earlier
reviewed report, a smallest counterexample would be a C1 instance with a saturated smaller side, plus
one edge inside the larger side (section 5.4 of the written proof).

| | Written proof | Lean declaration (namespace `Erdos585.QB4`, folder `Openmath/Proofs/QB4/`) |
|---|---|---|
| 1 | Identities 1.1 to 1.3 (1.2 as the inequality the proof uses) | `gv_eq_left`, `gv_eq_right`, `gv_union_add_gv_inter_le`, `gv_erase_left` (`Defs.lean`) |
| 2 | Lemma 1.4, the direction used | `exists_four_factor` (`FourFactor.lean`) |
| 3 | Lemma 1.5 | `quartic_of_isE4` (`Reductions.lean`) |
| 4 | Lemma 2.1 | `sparse_of_minimal`, with the case split `small_gv_cases` (`Reductions.lean`) |
| 5 | Lemma 3.1 | `gv_sdiff_sdiff` (`Defs.lean`) |
| 6 | Lemma 3.2 | `petal_of_violation` (`Core.lean`) |
| 7 | Lemmas 4.1 and 4.2 (Lean states the union half of 4.2) | `IsPetal.df_le_two`, `IsPetal.three_le_dg`, `IsPetal.union` (`Core.lean`) |
| 8 | Lemma 4.4 and Theorem 4.3 (`sparse_core` in contradiction form) | `sparse_core` (`Core.lean`), `quartic_of_sparse` (`FourFactor.lean`), `quartic_of_isC1` (`Main.lean`) |
| 9 | Corollary 5.2 | `quartic_of_isE4'` (`Main.lean`) |
| 10 | Corollary 5.3 | `quartic_of_dense` (`Main.lean`); `Erdos585.qb4` (`Statement.lean`) |
| 11 | Corollary 5.1 | `Erdos585.exists_four_regular_avoiding_of_bipartite_six_regular` (`Statement.lean`) |

*Review.* Three AI referees re-derived every step and wrote their own check programs (`C1-REVIEW.md`
with `review-1-code/`, `C1-REVIEW-2.md` with `review-2-code/`, `C1-REVIEW-3.md` with
`review-3-code/`). The first two ran on Claude Opus 5.5 (the second was requested on a different
model; its transcript shows Opus 5.5). The second wrote its derivations and code before reading the
first review, but it was given at the start the correction note `C1-CORRECTIONS.md`, which records
the first review's verdict, its one fix and its two optional observations. The third ran on Claude
Fable 5.1 and read none of the other reviews, nor the correction note, until its own verdict was
written (`C1-REVIEW-3-LOG.md`). All three accept Theorem 4.3 and Corollaries 5.1 to 5.4. The first
found a one-word fix in a remark after Corollary 5.3, which changes no statement; the second
confirmed it, and the third, which had not found it, adopted it after comparing. For QB(4) and the
vertex-deleted form the Lean proof makes the reviews a reading aid; P_2 is not in Lean. No
mathematician has checked any of it.

*The literature* (searched October 4 and 5; no novelty claimed; the search notes are not included, and every source named here can be checked directly). Alon, Friedland and Kalai [AFK84,
Remark 3.6] give a nonempty 4-divisible subgraph, hence a 4-regular one when Δ ≤ 7, in every bipartite
graph with more than 3(n − 1) edges, that is, from 3n − 2 edges. QB(4) is two edges lower, and it needs
simplicity: tripling every edge of a path gives a bipartite multigraph with Δ = 6, 3n − 3 edges and no
4-regular subgraph. In every loopless multigraph, more than 3n − 2 edges force a nonempty 4-divisible
subgraph (4-regular when Δ ≤ 7), and for every n ≥ 3 some loopless multigraph with 3n − 2 edges has
none [AFK84, Theorem 3.1 and Proposition 3.2]. The failure at 3n − 2 persists at Δ ≤ 6 (a path on an
odd number of vertices with every edge tripled, plus one single edge joining its ends), so P_2 sits
exactly at the multigraph threshold and needs simple graphs. The asymptotic theorems
[JS23, CJMM-reg] do not control the additive constant: the bipartite graph on {1, …, n} with i ~ j
when |i − j| ∈ {1, 3, 5} has Δ = 6 and 3n − 9 edges and is 3-degenerate, so it has no 4-regular
subgraph, and at Δ = 6 the open question is the additive constant c in 3n − c, about which the
asymptotic theorems say nothing. The results on regular factors of vertex-deleted subgraphs [EK22,
Ka25] give spanning factors of degree at most half the host degree, so they do not reach a 4-regular
subgraph of B − o at degree 6. The literature search found no statement of QB(4), its vertex-deleted form or P_2. One
possible source could not be read (Bollobás's *Extremal Graph Theory*), so a folklore remark is not
ruled out.

*Is 3n − 4 best possible?* At n = 2 trivially: K2 has 3n − 5 edges and no nonempty 4-regular subgraph. For
n ≥ 3 it is not: every bipartite graph with Δ ≤ 6, n ≥ 3 vertices and at least 3n − 5 edges has a
nonempty 4-regular subgraph (QB(5), **Lean-proved** as `Erdos585.qb5`). The written proof runs
through four papers, each frozen with a list of
SHA-256 hashes and each reviewed once by its own referee, who re-derived every step by hand and redid
the computations with code written from scratch; all four reports are final and found no
mathematical error. The author and the four referees were Claude Opus 5.5 agents of the third track
(section 7). The Lean proof is by Claude Opus 5.5 agents, and a separate Claude Fable 5.1 reader checked
its statement against the papers. The proof uses one computed finite lemma, Lemma 4.1 of `PAPER3.md`, computed by two
programs and recomputed by two of the referees; in Lean the kernel checks it (`decide +kernel` in
`CoverCheck1.lean` to `CoverCheck3.lean`). The fixes the first three reports require are carried
as corrections in the later papers, not in the frozen earlier ones (`PAPER4.md`, section 1.1, lists
them). The last report requires one wording fix that the frozen `PAPER4.md` does not carry
(`REVIEW4.md`, fix J1): its account of its own computer checks overstates which lemmas they test. In
particular, the author's data never reach the covering case of the hub count in the proof of KL1, the
block lemma the proof turns on; the referee's own checks do (717,812 covering multisets with a hub,
no failure), and one subcase is checked by hand only; the Lean proof checks every case. The papers, the reports, the files the hash
lists name and each referee's code are in `supplement/papers/qb5/` (the referees' data are not);
section 0 of `PAPER4.md` states the result, and section 5 of `REVIEW4.md` sets out the chain.

Whether 3n − 6 edges, or even 3n − 7, suffice for every n is open. An edge census shows that 3n − 7
suffice for 4 ≤ n ≤ 19 (section 5, question 4), and the census of 4-cores points the same way, with
the caveat of section 4.4: no bipartite
graph with Δ ≤ 6, e ≥ 3n − 6 and no nonempty 4-regular subgraph has a nonempty 4-core of at most 18 vertices
(through 16 vertices by two programs, 17 and 18 by one; the counts are in
`supplement/census/quartic/CENSUS.md`, with the programs and the n = 18 log beside it). And 3n − 8
edges do not suffice: the bipartite graph `J?BvfRguFo?` (graph6) on 11 vertices, with 25 edges and
degrees 4 to 6, has no nonempty 4-regular subgraph (computed with two deciders, in the unreviewed P_4 report of
section 5, question 4,
`supplement/papers/p4-attempt/checks/data/qb8_counterexample.g6`).

*What it means for B6.* A pair is a 4-regular subgraph that splits into two edge-disjoint Hamilton
cycles of itself. By Corollary B (section 4.6), B6 is equivalent to finding, in every bipartite
6-regular B and for every vertex o, a pair avoiding o. The vertex-deleted form of QB(4) gives a 4-regular
subgraph avoiding o, but not the split. So a pair-free bipartite 6-regular graph, if one exists, has
4-regular subgraphs avoiding every vertex, and none of them splits. The open step is the split
(section 5, question 3).

### 4.2 Three pair-free 5-regular graphs (Lean-proved)

Prior context: Read and Wilson, *An Atlas of Graphs* (Oxford University Press, 1998), Chapter 5, p.155, already record that a 5-regular graph need not contain a 4-regular subgraph. Such a graph has no cycle pair. Thus generic existence at degree five is not a new claim here. That passage does not establish the exact 18-vertex minimum or the 104-vertex bipartite construction; those require their own certificates and priority comparison.

**A 5-regular graph on 18 vertices** (`Erdos585.RegularFive18.exists_five_regular_pairfree`). The
9-vertex block has a triangle 0, 1, 2 joined to each of 3, 4, 5, and a triangle 6, 7, 8 with 6
adjacent to 3, 4 and 5, 7 adjacent to 3 and 4, and 8 adjacent to 5 (21 edges; vertices 7 and 8 have
degrees 4 and 3, the others 5). Every vertex has at most three neighbors with a smaller label, so every
subgraph of the block has a vertex of degree at most 3, and the block has no pair. Two copies (the
second on 9, …, 17) joined by the edges 8–17, 8–16 and 7–17 form a 5-regular graph with 45 edges. A
pair that met both copies would cross this 3-edge cut at least four times, so every pair lies in one
copy, which has none. The Lean proof follows this route, with the cut lemma of `CutGluing.lean`. The
graph does have 4-regular subgraphs, for example one with 34 edges on every vertex except 16, using
the cut edges 7–17 and 8–17: delete vertex 16 and the matching 0–1, 2–5, 3–7, 4–6, 9–10, 11–14. None lies inside a copy, so each crosses the
cut in exactly two edges, which a pair cannot do. No 5-regular graph on at most 16 vertices is
pair-free (section 4.4), so 18 is the smallest order of a pair-free 5-regular graph.

**A 5-regular graph on 32 vertices** (`Erdos585.RegularFive.exists_five_regular_pairfree`). The
8-vertex block is the double wheel on C5 without its hub edge (15 edges) plus a vertex 0 of degree 3.
Two blocks joined by the edges 0–9, 0–10, 1–8 form a half, and two halves joined by 2–18 and 8–24
form the graph. A cycle crosses an edge cut an even number of times, so a pair that crosses a cut uses
at least four of its edges. The cut between the halves has two edges, so every pair lies in one half;
inside a half the cut between the blocks has three, so every pair lies in one block. A
pair is 4-regular on its vertex set, so it avoids the block's degree-3 vertex and lies in the double
wheel, which is pair-free. The Lean proof follows this route. The graph is not bipartite (triangle
4, 5, 6).

**A bipartite 5-regular graph on 104 vertices**
(`Erdos585.BipartiteFive.exists_bipartite_five_regular_pairfree`, which also proves the 2-coloring).
The 13-vertex block is K3,3 plus seven vertices, each joined to three earlier ones; vertices 9, 11
and 12 have block degrees 4, 3 and 3. Eight copies are joined by 20 edges following an 8-vertex
bipartite 5-regular multigraph, grouped into edge cuts of sizes two and three. Every subgraph of the
block has a vertex of degree at most 3, so the block has no pair, and the cuts confine any pair to
one copy. The Lean proof uses this cut route; Theorem R1 (section 4.6) explains why such graphs exist.

An independent block-decomposition program also finds no pair in the Lean graph (1,179
boundary-consistent assignments). A second, nonisomorphic 104-vertex graph built from the same block
and skeleton passes the same program but is not covered by the Lean result. Appendix B lists the
edges of both Lean graphs, labeled as in the Lean files.

*Why these graphs are elementary.* The two cycles of a pair form a 4-edge-connected subgraph, since
every cut of it is crossed twice by each cycle. The 18-vertex and 104-vertex graphs have no
4-edge-connected subgraph at all, and the only ones in the 32-vertex graph are its four 7-vertex double wheels without the hub
edge, which are pair-free (these facts recomputed for this document). A graph with no 4-edge-connected subgraph has
at most 3(n − 1) edges, so this certificate exists for 5-regular graphs but never for 6-regular ones.

### 4.3 Exact values and lower bounds (Lean-proved)

| | Result | Declaration (in `Openmath/Proofs/Final.lean`) |
|---|---|---|
| 1 | f(n) = n(n−1)/2 for n ≤ 4 | `maxEdges_eq_choose_two_of_le_four` |
| 2 | f(5) = 9, f(6) = 12, f(7) = 16 | `maxEdges_five`, `maxEdges_six`, `maxEdges_seven` |
| 3 | f(n) ≥ 4n − 13 for n ≥ 10; f(11) ≥ 31; f(12) ≥ 36 | `four_mul_sub_thirteen_le_maxEdges`, `thirty_one_le_maxEdges_eleven`, `thirty_six_le_maxEdges_twelve` |
| 4 | f(n) ≥ 5n − 15⌊√n⌋ − 10 for n ≥ 16 | `five_mul_sub_sqrt_le_maxEdges` |
| 5 | f(2k² + 2) ≥ 8k² − 3k + 1; f(m² + 3m + 2) ≥ 5m² | `complete_matching_subdivision_lower_bound`, `latin_incidence_lower_bound` |
| 6 | f(n) ≥ 3n − 6 (n ≥ 5); ≥ 3n − 5 (n ≥ 7); ≥ 3n − 4 (n ≥ 9) | `three_mul_sub_six_le_maxEdges`, `three_mul_sub_five_le_maxEdges`, `three_mul_sub_four_le_maxEdges` |
| 7 | f(n+1) ≥ f(n) + 3 for n ≥ 3 | `maxEdges_succ_ge` |

The constructions behind the bounds are explicit and Lean-proved pair-free: the double wheel K2 ∨ C_m
(two adjacent hubs joined to every vertex of a cycle), K2 ∨ θ(2,3,3) on 9 vertices, a family with two
hubs (4n − 13, hence f(11) ≥ 31), the join of two adjacent hubs with the Petersen graph (f(12) ≥ 36),
Latin-square incidence graphs (5m² and 5n − 15⌊√n⌋ − 10), and matching subdivisions (from a graph H
and a matching M: keep M, subdivide every other edge of H once, and add two adjacent hubs joined to
everything; the Lean statement does not need M to lie in H). All these bounds are linear in n, so
asymptotically they fall below the c·n log log n bound of [PRS95].

*Twin-core forcing (special case).* A bipartite graph with maximum degree at most 6 and exactly 3v − 2
edges, in which every left vertex has a twin (another left vertex with the same neighborhood), has a
pair (`Erdos585.TwinNoSingleton.hasPair_of_no_singleton_twins`; a grouped form is
`Erdos585.TwinCoreForcing.groupedGraph_hasPair_of_no_singletons`). The hypotheses are satisfiable
(three left and six right vertices, all edges but one, every left vertex doubled: 12 vertices and
34 = 3·12 − 2 edges), but never by a 6-regular graph, which has 3v edges.

### 4.4 Computations (computed)

**Exact values.** f(1), …, f(12) = 0, 1, 3, 6, 9, 12, 16, 19, 23, 27, 31, 36.
Values through n = 10 were reported by [Erdős Problem a Day](https://erdosproblemaday.com/report/585)
(July 28, 2026; read October 8, 2026). This repository reproduces them; only f(11) and f(12)
are new entries relative to that report. Appendix C lists the programs, counts and replication scope.
The sequence was not found in OEIS in the dated search (October 6, 2026).

**Saved upper certificates at 11 and 12.** The [certificate packet](supplement/small-values/certificates/README.md)
supports the existing computational values f(11)=31 and f(12)=36. Its complete
ten-vertex streams contain 816,231 graphs, with 815,724 positive cycle-pair
certificates and 507 retained parents. A separate checker verifies all 2,504
admissible extensions. Canonical generation still uses nauty; separate search
and certificate checks are not independent canonical generators or Lean upper proofs.

**Census.** nauty `geng` 2.9.3 generates one graph per isomorphism class, and `pairc.c` tests each
for a pair (validated on all 12,346 graphs on 8 vertices, where it finds 10,512 pair-free ones, the
same count as the separately written `computations/erdos585_small.py --levelwise 8`).

| | Class (Δ = maximum degree, δ = minimum degree) | n | Graphs | Pair-free |
|---|---|---|---|---|
| 1 | Δ ≤ 6, δ ≥ 4, e ≥ 3n − 4 | 11; 12 | 2,157,714; 107,242,738 | 0 |
| 2 | same, bipartite | 18 | 18,153,661 | 0 |
| 3 | 6-regular | 13; 14 | 367,860; 21,609,301 | 0 |
| 4 | Δ ≤ 6, δ ≥ 4, e = 3n − 5 | 7 to 11 | 7; 76; 1,620; 53,886; 2,360,506 | 1, 2, 3, 11, 0 |
| 5 | connected 4-regular, no Hamilton decomposition | 15; 16 | of 805,491; of 8,037,418 | 1,386; 8,719 |

The statement W1, "for n ≥ 2, Δ ≤ 6 and e ≥ 3n − 4 force a pair", implies B6 and is sharp: K2 ∨ C5 has 3n − 5
edges and no pair. A separate canonical-augmentation program (`gen585.c`) extended W1 to n = 13 and
14; a reviewer replicated n = 13 with different code, and n = 14 rests on that one reviewed program.
A 6-regular graph on 15 vertices minus a vertex has 39 ≥ 3·14 − 4 edges, so no 6-regular graph on 15
vertices is pair-free, with the same caveat. A connected 4-regular graph has a pair exactly when it
has a Hamilton decomposition, so the last row counts pair-free 4-regular graphs. Appendix C has every
count, its replication status and the gaps in the record.

**Calibration at degree 5.** The same test finds no pair-free 5-regular graph on at most 14 vertices:
1, 3, 60, 7,849 and 3,459,386 graphs on 6, 8, 10, 12 and 14 vertices, all with a pair (n = 12 and 14
also by a second, SAT-based decider whose witnesses were all replayed; every n ≤ 14 again by a SAT pair
decider on plain `geng` output, every pair checked). A census of all 5-regular graphs on 16 vertices
(`geng` with a pair-pruning hook, in 20,000 shards) finds none pair-free either. A second method,
with separate code, finds a checked pair in each of the 388 triangle-free and the 41 bipartite ones
and in each of the 3,612,814 graphs of a random 0.14% of the shards. Pair-free 5-regular graphs
exist on 18 vertices (section 4.2), giving least order 18 subject to the reported complete
16-vertex census. The tag retains the completed-shard index and aggregate records,
but omits the raw per-shard logs and empty outputs. A complete independent replication
is not established here (`supplement/census/calibration/n16/`; the second method in
`supplement/census/calibration/n16-second-method/`). So at degree 5 a census of regular graphs through 14 vertices
would have looked as clean as the degree-6 census does, and the regular-graph rows above say little on
their own about larger 6-regular graphs. What the degree-6 record does show is narrower. The least
deficiency 6n − 2e of a pair-free graph with Δ ≤ 6 is 10 for every n from 7 to 14 (K2 ∨ C5 plus
vertices of degree 3), against 3 at degree 5 (at 9 and 11 vertices), where the analog is 5n − 2e. So a pair-free 6-regular
graph cannot be glued from small blocks across a cut of at most three edges: by W1, each side would need
at least 15 vertices (this bound is in the calibration notes and has not been reviewed). Details and
logs: `supplement/census/calibration/`.

### 4.5 The degree-6 reduction (written proof, checked against the sources)

**Claim.** If B6 holds, then f(n) = Θ(n log log n). It is an immediate consequence of [PRS95] and
[JS23], and nothing in the argument is special to 6.

*Proof.* The lower bound is unconditional: [PRS95, Theorem 1] gives graphs with c·n log log n edges
and no 3-regular subgraph; they are bipartite, so by König's theorem they have no k-regular subgraph
for any k ≥ 3, as the paper notes after the theorem (also restated in [JS23, Theorem 1.1] and [CJMM24,
arXiv p. 2]), and the union of a pair is 4-regular. For the upper bound, let G have m ≥ C(6)·n log log n edges. A spanning
bipartite subgraph H keeps at least m/2 edges, so its average degree is at least C(6) log log n ≥
C(6) log log Δ(H). By [JS23, Theorem 1.2] (published version, with Δ ≥ 3), H contains a 6-regular
subgraph, which is simple, nonempty and bipartite, so B6 gives a pair in G. ∎

The chain was checked against each cited paper's own text: [JS23] and [CJMM24] while preparing this
document and again in a separate literature review on October 5, and [PRS95] on October 5. No
constant is explicit. B6 is open, and no published result the literature search found states or refutes it.

### 4.6 Theorem R1 and the vertex-deleted form of B6 (written proof, reviewed)

A *d-gadget* is a simple bipartite graph Γ with sides I and O, every vertex of I of degree d, every
vertex of O of degree at most d, and |O| = |I| + 1. A *substitution* of Γ into a d-regular multigraph
L replaces each vertex of L by a copy of Γ and each edge of L by a link edge between O-vertices of the
two copies, so that the result is simple and d-regular (bipartite if L is).

**Theorem R1.** If Γ is a pair-free d-gadget with d ≤ 7 and L is a pair-free d-regular multigraph,
then every substitution of Γ into L is pair-free.

**Corollary B.** "Every bipartite 6-regular graph has a pair" is equivalent to "for every bipartite
6-regular graph B and every vertex o, B − o has a pair".

The key step (Lemma 1, appendix D) is a count: a pair that meets a copy but is not inside it uses
exactly four of the copy's link edges, two per cycle, because the number used is
4(|S ∩ O| − |S ∩ I|) and there are at most 7. Corollary B applies R1 to the gadget B − o (its six
deficiency units sit on six distinct vertices, so a simple substitution exists) and a pair-free
bipartite 6-regular multigraph on 16 vertices. The vertex-deleted statement allows a different pair
for each o. So any proof of B6 must find pairs avoiding a prescribed vertex, and one bipartite
6-regular graph with a vertex on every pair would give a pair-free one.

*Review.* A separate reviewer (a Claude Opus 5.5 subagent of the same track, in a fresh context,
with its own code) found Lemma 1 sound, and R1 and its corollaries
sound after wording and citation-scope fixes, all applied; it also machine-checked the alternative
104-vertex graph by exact block decomposition. R1 is one-directional: the reviewer found gadgets for
which the converse fails. Substitution of this kind goes back to Meredith's non-Hamiltonian 4-regular
graphs [Me73], which take the Petersen graph with a perfect matching doubled and replace each vertex
by K4,3; R1 extends the
count from Hamilton cycles to pairs and from K4,3 to any pair-free gadget. The working documents call R1 "Fable R1", after the track that found it;
it is unrelated to the recoloring barrier of section 4.8.

### 4.7 A conditional route to O(n (log n)⁴) (written proof, conditional)

Write B(polylog) for the statement that every bipartite r-regular graph with r ≥ A (log 2N)³ has a
pair, the analog of B6 at polylogarithmic degree. If B(polylog) holds, then f(n) = O(n (log n)⁴),
by [CJMM-reg, Theorem 1.5] with r = ⌈A (log 2n)³⌉, in the way section 4.5 uses [JS23]. The project
proposed one route to B(polylog), through the extraction statement E110 (precise form in section 5).
E110 assumes the graph is pair-free, so given Lemma F and BM-2 below it is equivalent to B(polylog):
it is a proof strategy, not a weaker hypothesis. The other ingredients are written proofs, reviewed but not
formalized:

| | Ingredient | Status |
|---|---|---|
| 1 | E110 (avoidance-conditioned balanced extraction) | open; one attempt reviewed as a correct failure analysis |
| 2 | Lemma F: a balanced near-regular expander has a spanning regular factor (proof in appendix D) | reviewed, accepted |
| 3 | BM-2 quantitative candidate: a bipartite d-regular expander with d ≥ C γ⁻¹⁰ (log n)³ would have two edge-disjoint Hamilton cycles (γ⁻¹² in the conservative route) | unverified main Hamiltonicity input; an earlier written AI review accepted it, but supporting lemmas do not constitute a complete proof; not attributable to [Mü26] |
| 4 | [CJMM-reg, Theorem 1.5]: for r ≤ n/2, average degree C·r log(n/r) forces an r-regular subgraph | published; quote checked |

E110, Lemma F and BM-2 together would give B(polylog), and with it f(n) = O(n (log n)⁴).
The V110 vertex-deletion reduction is conditional on the unverified main BM/BM-2 input.
Under that input, a bipartite r-regular expander with r ≥ C_V γ⁻¹⁰ (log 2N)³ would retain
two edge-disjoint Hamilton cycles after deleting up to ⌊γ²r/32⌋ vertices from each side.
The earlier written review does not complete that input. The conditional reduction does not
reach degree 6, and no novelty is claimed for it.
Papers and reviews: `supplement/papers/`.

### 4.8 A method barrier (Lean-proved; written argument)

The parabola palette is prior Sidon/2-cap geometry. Huang, Tait and Won, *Sidon sets and 2-caps in F_3^n*, Involve 12(6) (2019), 995–1003, Theorem 3.2 proves the equivalence, and the proof of Theorem 3.4 credits the parabola Sidon construction to Cilleruelo’s Example 1 (*Combinatorial problems in finite fields and Sidon sets*, Combinatorica 32 (2012), 497–511). The candidate contribution here is the stated recoloring-detector obstruction, not that geometry.

The barrier concerns explicit hosts that do contain pairs (by [CJMM24], for large parameters; this is
not Lean-proved). It rules out one proof method, not the existence of pair-free graphs.

- **The recoloring barrier (R1-plus)** (`Erdos585.ParabolaBarrier104.arbitrary_polylog_barrier`). On a C4-free bipartite family
  with N = 2·3²ᵏ vertices and degree 3ᵏ, after any one round of two-color swaps from its canonical
  edge coloring, no two-colored cycle has an edge-disjoint partner cycle on the same vertex set; the
  degree exceeds C (log N)^A, for any fixed C and A, for arbitrarily large k. So a method that searches for a
  pair among two-colored cycles after one recoloring round fails.

## 5. Open questions

1. **E110.** For absolute constants 0 < γ ≤ 1/4, 0 < η ≤ γ²/8, c > 0, A > 0: must every bipartite
   r-regular pair-free graph on N ≥ 4 vertices with r ≥ A (log 2N)³ contain a nonempty balanced
   bipartite subgraph H on h vertices with all degrees in [(1 − η)k, k] for some k ≥ max(c·r, 16/γ²)
   and e_H(S, V(H) ∖ S) ≥ γk|S| for 1 ≤ |S| ≤ h/2? A yes gives f(n) = O(n (log n)⁴); given Lemma F and BM-2, a yes is
   equivalent to B(polylog) (section 4.7).
2. **B6, in its vertex-deleted form.** Does every nonempty finite bipartite 6-regular graph B contain,
   for every vertex o, a pair avoiding o? A yes gives f(n) = Θ(n log log n). Candidate written proofs on
   computed censuses give it for every B on at most 24 vertices and every o (row 17). They argue that a
   smallest bipartite graph (fewest
   vertices, then fewest edges) with
   Δ ≤ 6, n ≥ 2, e ≥ 3n − 4 and no pair is an E4 instance (n even) or a C1 instance (n odd) that is
   sparse in the sense of question 3 (`supplement/papers/pairs/PAPER.md`, Lemma 1); that none is of E4
   type with n ≤ 22 (Corollary B of `supplement/papers/b6-24/theory/ADDENDUM-B.md`, not the Corollary B
   of section 4.6); and that none is of C1 type with n = 19, 21 or 23 (Theorem C of
   `supplement/papers/b6-24/c1type/PAPER.md`). The census excludes n ≤ 18, so W1 holds for bipartite
   graphs through 23 vertices; B − o has |B| − 1 vertices, maximum degree 6 and 3(|B| − 1) − 3 edges,
   so it has a pair.

   The proofs use four censuses, each computed by two methods: W1 for bipartite
   graphs through 18 vertices (row 13; the second method uses a different generator and covers the
   classes a smallest counterexample can lie in, but takes its Hamilton-cycle search from the first
   method's program), no pair-free bipartite graph with δ ≥ 4, Δ ≤ 6 and 3n − 5 edges on at most 17
   vertices, none on 5 + 5 vertices with 22 or more edges, and a Hamilton decomposition for every
   connected bipartite 4-regular graph on at most 22 vertices with no 2-edge cut. For the last three
   the two methods share no decision code. Separate SAT models by the authors and by the referees
   agree with the case analyses behind Corollary B and Theorem C; the C1-type referee's model also
   settles the one shape the author's model left open. Each paper was reviewed once. The reviews of
   the rigid-set paper (`supplement/papers/b6-24/theory/PAPER.md`) with its addendum and of the
   C1-type paper found no mathematical error; the review of the pairs paper found its Proposition 5
   false for sets of two vertices and true for three or more, the form the later papers use.

   A direct census of all 121,790 bipartite 6-regular graphs on 10 + 10 vertices also finds a pair in each
   graph (B6 itself, not the vertex-deleted form; one method;
   `supplement/papers/b6-24/theory/b6_20_part_*.err`). The bound is still small: the smallest
   pair-free 5-regular graph has 18 vertices (sections 4.2 and 4.4). Section 4.1 supplies a 4-regular
   subgraph avoiding o; what is missing is one that splits into two Hamilton cycles. I know of no
   reduction to a named Hamilton-decomposition conjecture: a pair is a Hamilton-decomposable 4-regular
   subgraph, which is weaker than decomposing the whole host.
3. **The split, after QB(4).** Call a bipartite graph with Δ ≤ 6 and e = 3n − 4 *sparse* if every
   vertex set S with 2 ≤ |S| ≤ n − 1 has g(S) ≥ 10 (as in section 4.1). The third track's (section 7) pairs paper
   (written proofs and certificates, reviewed once and accepted with fixes; `supplement/papers/pairs/`)
   gives a written argument that a smallest bipartite graph (fewest vertices, then fewest edges)
   with Δ ≤ 6, n ≥ 2, e ≥ 3n − 4 and no pair is a sparse E4 or C1 instance, and that a sparse E4
   instance has a spanning 4-regular subgraph (a 4-factor). The open step is a 4-factor, or a smaller
   4-regular subgraph, that splits into two edge-disjoint Hamilton cycles. A 4-factor can have a cut
   of two edges, which no pair crosses; an exchange lemma repairs one such cut unless the deficiency is
   concentrated or the side of the cut is a (5,1) set (a balanced set with a single edge leaving one
   of its sides, which every 4-factor cuts in at most two edges, as in the 20-vertex example below),
   and whether repeated exchanges terminate is open. Two natural statements are false, so they can be
   skipped; a third, S6, is open and checked at 22 vertices (one method, unreviewed):
   - *"Every sparse instance has two edge-disjoint Hamilton cycles."* A sparse E4 instance on 20
     vertices has none: two copies of K5,5, on {0, …, 4} ∪ {10, …, 14} and on {5, …, 9} ∪ {15, …, 19},
     joined by the matching 0–15, 1–16, 2–17, 3–18, 4–19 and the edge 10–5. It has 56 = 3n − 4 edges and
     Δ = 6, and it does have a pair, inside K4,4 (`supplement/papers/pairs/data/rigid20.g6`).
   - *A marked-edge statement:* "if Y has m ≤ 11 vertices, Δ ≤ 6 and 3m − 3 edges, ab and cd are
     disjoint edges and Y − ab − cd is pair-free, then Y has a pair with ab and cd on different
     cycles." Six graphs on 11 vertices with 30 edges are counterexamples
     (`supplement/papers/pairs/data/t1_none.txt`, with the marked edges). The referee confirmed them
     with its own tester; the author agent's first program had a labeling bug that did not affect these six.
     W1 is not affected.
   - *S6, open, checked at 22 vertices.* For a bipartite 6-regular graph B and a vertex o, call Γ = B − o
     sparse if g(S) ≥ 10 for every S with 2 ≤ |S| ≤ n − 1, as above (Γ has n = |B| − 1 vertices and
     3n − 3 edges, one more than the graphs above). Its *ports* are the six neighbors of o, the vertices
     of degree 5 on the larger side of Γ. **S6** is the statement: if Γ is sparse, then for every port
     y, Γ − y has two edge-disjoint Hamilton cycles, a pair avoiding o. Γ is sparse exactly when every
     edge cut of B with at least two vertices on each side has at least 10 edges (B is *E10*), so the
     condition does not depend on o (a written proof: `supplement/papers/s6/PAPER.md`, Lemma 1.1, reviewed). If S6 held
     at every size, a smallest counterexample to the vertex-deleted form would have an edge cut of at
     most 8 edges with at least two vertices on each side (a written proof: section 6 of the same paper, reviewed). S6
     holds for every bipartite 6-regular graph on 22 vertices (row 18).

     nauty `genbg` gives 156,473,848
     graphs on 11 + 11 vertices, one per isomorphism class with the two sides kept apart; 3 are not E10
     (their smallest such cut has 6 or 8 edges), so S6 asks nothing of them. For each of the other
     156,473,845 and each of its 66 edges oy, a C program found two edge-disjoint Hamilton cycles of
     B − o − y and checked them: 10,327,273,770 tests, none failing. On the 333,908 tests where its
     randomized recoloring search stalled before it continued and succeeded, a separate SAT program
     also found and checked a pair. This is one method and unreviewed: one generator and one decision
     program, a SAT cross-check of the stalled tests and of 300 sampled tests only, and the generator's
     slicing checked against the full class count at 10 + 10 vertices only
     (`supplement/census/s6n22/RESULT.md`, `JOBS.md`). An independent spot-check of a recorded random
     sample of 50 slices (588,094 graphs and 38,814,204 tests, 0.376% of the census; its own E10 test,
     SAT encoding and witness check, sharing only the generator and the SAT library) agrees with every
     count and finds two checked Hamilton cycles in every test
     (`supplement/census/s6n22/spot-check/SPOTCHECK.md`). It also shows that S6 needs its hypothesis: on
     the 3 graphs that are not E10, the conclusion fails in 22 of their 198 tests, at the edges of their
     small cuts. Row 17 does not use S6, and none of this says anything about larger graphs.
4. **The constants.** QB(4) is not best possible for n ≥ 3: QB(5), Lean-proved (section
   4.1), lowers the threshold to 3n − 5. Do 3n − 6 edges suffice, as the census suggests, or 3n − 7?
   (3n − 8 do not; section 4.1.) For small n an edge census answers both. On 17, 18 and 19 vertices
   the largest bipartite graphs with Δ ≤ 6 and no nonempty 4-regular subgraph have 43, 46 and 49
   edges, that is 3n − 8, by two methods each (row 4). Both methods also cover the smaller orders, so
   3n − 7 edges suffice for 4 ≤ n ≤ 19, and 3n − 6 edges for 4 ≤ n ≤ 20 (n = 20 by one method). Graphs
   with 3n − 8 edges and no nonempty 4-regular subgraph exist for 11 ≤ n ≤ 20
   (`supplement/census/edge/data/witness_n15.g6` to `witness_n20.g6`, checked by both methods, and
   `supplement/census/edge/method-b/data/chain_witness_n*.g6`; unreviewed). And P_4: does
   every graph with Δ ≤ 6, n ≥ 2 and e ≥ 3n − 4 have a nonempty 4-regular subgraph? It holds for n ≤ 14 by W1
   (a pair is a 4-regular subgraph), and a separate minimal-counterexample search confirms n ≤ 13;
   K2 ∨ C5 (3n − 5 edges, no nonempty 4-regular subgraph) would make it sharp. The core step of section 4.1
   does not carry over to general graphs: there are graphs with 3n − 4 edges and the same sparsity in
   which neither G nor any G − y has a spanning 4-regular subgraph, for example `HCXf~z{` on 9 vertices
   and `JCOfuzsnCf_` on 11 (graph6; these and nine on 12 vertices are in
   `supplement/papers/p4-attempt/`, checked by two deciders, one of them `checks/check_deep.py` in that
   folder; the report is not reviewed).

## 6. Audit requests, in detail

The [literature comparisons](../literature/README.md) record prior methods, exact source locations
and access limits.

1. **Statement.** Do the definitions in section 2 say what the problem says (cycles in Mathlib's
   sense, equal vertex sets, edge-disjoint, labeled vertices, supremum attained)?
2. **Lean results.** Re-run `check.sh` on the rows of section 1 and check that each statement says
   what its row says (ℕ subtraction, `Nat.sqrt`, the hypotheses of the twin-core and barrier
   statements, and in the two QB(4) statements the edge inequality, the decidability instances, and
   what `H.coe.IsRegularOfDegree 4` says about a `Subgraph`).
3. **The three graphs.** From the edge lists alone, confirm that all three are 5-regular and pair-free
   and that the largest is bipartite. Read and Wilson already record generic five-regular graphs
   without a quartic (section 4.2). The comparisons needed here concern exact orders, the bipartite
   restriction and the minimum-order census. (A connected 4-regular graph without a Hamilton
   decomposition is pair-free.)
4. **The census.** Replicate the single-program claims (n = 14, and bipartite graphs through 18).
   Check that `pairc.c` is complete and sound: the runs saved no witnesses, so re-run a sample with
   `./pairc w` and check the printed pairs independently.
5. **Theorem R1, Corollary B and the reduction** (sections 4.5 and 4.6, appendix D).
6. **QB(4)** (section 4.1): sections 2 to 4 of `supplement/papers/quartic/C1-PAPER.md`, about 120
   lines, against `Openmath/Proofs/QB4/`; and Corollaries 0.1 and 5.4 with section 5.4 for P_2, which
   is not in Lean.
7. **QB(5)** (section 4.1): the Lean statement in `Openmath/Proofs/QB5/Statement.lean` (what it
   assumes and concludes) and, for the argument, the proof of KL1 in sections 2 and 3 of
   `supplement/papers/qb5/PAPER4.md`, which one referee has checked; Lemma 4.1 of `PAPER3.md`, the
   computed lemma (two programs in `code/`, and the kernel-checked `CoverCheck1.lean` to
   `CoverCheck3.lean`); and the chain from the first paper to the last, as section 5 of `REVIEW4.md`
   sets it out.
8. **B6 through 24 vertices** (section 5, question 2): Corollary C of
   `supplement/papers/b6-24/c1type/PAPER.md` and the chain it cites, and the four censuses with their
   second methods.
9. **The conditional route** (section 4.7), above all BM-2, the least-checked ingredient.
10. **Prior art** for any item above, especially QB(4), QB(5), B6 and W1.

## 7. How this was made

I pointed AI agents (OpenAI's GPT-6 Astra and Anthropic's Claude Fable 5.1 and Claude Opus 5.5) at
the recent literature to find techniques that might apply to Erdős 585. The agents proposed ideas,
wrote proofs and search programs, and reviewed each other's work. The Lean results were also checked
by the Lean kernel, and the exact values were cross-checked by separately written programs. Between
passes I steered them back toward the main question when they tunneled into dead ends or into
methods that would cost more than my budget allowed, and I made sure we had checkpoints and new
directions to try.

Most of my steering was setting the rules for what counts as progress and pushing the agents toward
novel approaches. First, I set the rules for what actually counted. A Lean result counted only when
`check.sh` passed: the build has no `sorry` and uses only the 3 standard axioms. For QB(5), a
separate agent also compared the Lean statement with the written one, and separate reviewers checked
every row of the public README's "Verified in Lean" table against its Lean statement. In the later
passes, every main written claim needed either a Lean proof or a review by a separate agent in a
fresh context, and results for fixed sizes were recorded as fixed-size results, never as the general
case. For the key computer searches I asked for a second, separately written program, and the
findings say which searches have one. In the last pass, long computations ran as a small pilot
first, with a budget cap and a stop command. I tracked what each pass cost (section 8 has the
figures), parked directions that were not paying off, and had the agents keep a dated log of my
decisions.

Second, I kept pushing the agents to look at the math literature and at other AI-assisted math
research for related results and methods they could apply here, instead of starting from scratch.
For example, the conditional route in the findings goes through a recent theorem of Chakraborti,
Janzer, Methuku and Montgomery on regular subgraphs.

The formal statements, Lean proofs, written proofs, constructions and search programs behind these
findings were produced with AI agents; the table below says which model did what. I read the
results, the checks and the claims they support.

I'm an MBA candidate at Harvard Business School, not in a mathematics program, and I did not check
the mathematics myself. I take full responsibility for any errors. No mathematician has reviewed the
mathematics yet, although I am looking for help: if you find an error or know of prior work, or are
willing to help, please open an issue in the public repository and I'd love to get in contact with
you.

The AI systems and their roles, from the project's logs:

| | Period (2026) | Model | Role | Main outputs here |
|---|---|---|---|---|
| 1 | Sep 29 to Oct 1 | Claude Fable 5.1, Claude Opus 5.5 | statement drafting, first Lean proofs, two independent computations, by one lead agent (Fable 5.1, then Opus 5.5 from October 1) with 22 Opus 5.5 subagents | the statement; f(n) for n ≤ 5, the extension lemma and the double-wheel and θ-wheel constructions in Lean; f(1) to f(8) by two programs; the f(9) and f(10) runs |
| 2 | Oct 1 to 4 | OpenAI GPT-6 Astra | 110 numbered research passes by a lead agent and worker agents in OpenAI's Codex, with Codex's automatic approval reviewer; separate worker agents reviewed each claim; only the lead ran `check.sh` | f(6), f(7) and the other lower bounds of §4.3; f(11) and f(12); the 32-vertex graph; twin-core forcing; the recoloring barrier R1-plus; E110, V110 and G110 |
| 3 | Oct 3 to 4 | Claude Fable 5.1, Claude Opus 5.5 | a separate track on degree six, started from scratch: a Fable 5.1 lead agent with four Opus 5.5 subagents | Theorem R1 and its corollaries; the 104-vertex graph and its Lean file; the `geng` and `pairc` census; the review of R1 (an Opus 5.5 subagent) |
| 4 | Oct 4 | Claude Opus 5.5, Claude Haiku 4.5 | a second track started from scratch, with subagents; Haiku 4.5 ran its web searches | the n = 13 and 14 census extension and its replication; BM-2 (with its first version) and Lemma F, with their reviews |
| 5 | Oct 4 | Claude Opus 5.5 | foundations audit | the checks of the degree-6 reduction and of the statement against their sources |
| 6 | Oct 4 | Claude Opus 5.5 | preparing this document | statements and edge lists extracted from the Lean files; every Lean result re-run; citations checked at source; a separate fact check |
| 7 | Oct 4 to 6 | Claude Opus 5.5 | a third track on degree six: a lead agent with author, referee, census, literature and Lean subagents, in which each main written claim needed a separate referee or a Lean proof (the censuses added on October 5 and 6 are unreviewed); the outputs listed here came from Opus 5.5 agents, and small shares of the track ran on Claude Sonnet 5.5 (nested helpers) and Claude Haiku 4.5 (web searches) | QB(4), its vertex-deleted form and P_2 with the first review; the Lean proofs of the first two; the 18-vertex graph and its Lean file; the degree-5 calibration; the literature search; the counterexamples of section 5; QB(5) as a written proof with its four reviews; B6 through 24 vertices, with the rigid-set and C1-type papers, their reviews and the censuses' second methods; the S6 paper (`supplement/papers/s6/`) and its review; S6 at 22 vertices and its spot-check; the 16-vertex census of 5-regular graphs and its second method; the edge census and its second method |
| 8 | Oct 5 | Claude Fable 5.1 | the S6 scout lane of the third track (va6 in the working documents) | the statement S6 and the SAT decider that the S6 run at 22 vertices uses to cross-check its stalled tests |
| 9 | Oct 5 | Claude Opus 5.5 | second review of the QB(4) proof (requested on Claude Fable 5.1; every call in its transcript ran on Opus 5.5) | `C1-REVIEW-2.md` |
| 10 | Oct 5 | Claude Fable 5.1 | third review of the QB(4) proof, with no access to the other reviews before its verdict | `C1-REVIEW-3.md` |
| 11 | Oct 5 to 6 | Claude Opus 5.5 | revising this document | the v0.3 release files, the new sections, re-runs of every Lean check on the `v0.3` files |
| 12 | Oct 6 | Claude Opus 5.5 | the Lean proof of QB(5), by a planning subagent and five build subagents of the third track's lead agent | `Openmath/Proofs/QB5/` (17 modules) |
| 13 | Oct 6 | Claude Fable 5.1 | a separate reading of the Lean statement of QB(5) against the papers | the verdict that `Erdos585.qb5` states the papers' QB(5) |

The supplement's working documents are verbatim
apart from local paths, link targets, one marked correction, Lean copyright lines, marked omissions, the
name of a task tracker and one omitted row of a check transcript (`supplement/MANIFEST.md`), and call
the models by the project's short names ("Fable", "Opus", and "Codex" for GPT-6 Astra, which ran in
OpenAI's Codex); `supplement/README.md` has a glossary and `supplement/PROVENANCE.json`
records every edit.

## 8. A data point for the OPDP atlas

The scale of each pass, from the project's private cost ledger, with costs at API list prices:

| | Period (2026) | Wall-clock time | Agent sessions | Model responses | Cost | Main outputs |
|---|---|---|---|---|---|---|
| 1 | Sep 29 to Oct 1 | about 8 hours with the lead agent active, over a span of 63 hours | 25 | at least 1,226 | $267.87 | the statement; f(n) for n ≤ 5 in Lean; f(1) to f(8) by two programs |
| 2 | Oct 1 to 4 | 58.4 hours with at least one Codex task running | 240 | 18,844 | $5,671.60 | f(6) and f(7) in Lean, f(11) and f(12), and the lower bounds; the 32- and 104-vertex graphs; twin-core forcing; Theorem R1; the census through 14 vertices; the conditional route and the barrier |
| 3 | Oct 4 to 6 | about 37 hours | 91 | at least 7,483 | $1,415.34, plus at least $536.66 for the sessions that supported it | QB(4), QB(5) in Lean and P_2; the 18-vertex graph and the least order 18; B6 through 24 vertices; S6 at 22 vertices; the edge census |

The OPDP atlas [OPDP] (record 2194, the same from v1.2 to v1.8) rates Erdős 585 T2 Research Sprint and AI-favored
(AI difficulty 1.8, confidence C1). The record is itself flagged for curation (`malformed_import_fragment`,
priority P0, action "Repair imported background and re-run scoring"), so these ratings may be re-scored.
Its tractability band is T9: 85–95% for novel, independently
checked partial progress, not full resolution, in 100 combined expert-plus-AI hours, with "exact
computation plus proof certificate" as the most credible first mode. Measured against
that record: the finite questions fell quickly, by the first mode it names (exact values through
n = 12, explicit lower-bound constructions, the pair-free 5-regular graphs), and the asymptotic
question did not move. Novelty and an independent check by a person are open; they are what this
document asks for. The hours in the table are wall-clock hours of agents running, many in parallel and
with no expert time, so they are not the forecast's unit of combined expert-plus-AI hours. From the
start of the third pass to the first passing Lean check of QB(4) took about 12 hours. Model responses
for the first and third passes are counted from their transcripts, which miss some, and the cost of
the sessions that supported the third pass is a transcript tally, a lower bound.

## References

- [AFK84] N. Alon, S. Friedland, G. Kalai, Regular subgraphs of almost regular graphs, J. Combin.
  Theory Ser. B 37 (1984), 79–91; Theorem 3.1 and Proposition 3.2 are on p. 83, Remark 3.6 on p. 85.
- [CJMM24] D. Chakraborti, O. Janzer, A. Methuku, R. Montgomery, Edge-disjoint cycles with the same
  vertex set, Adv. Math. 469 (2025), 110228; arXiv:2404.07190.
- [CJMM-reg] D. Chakraborti, O. Janzer, A. Methuku, R. Montgomery, Regular subgraphs at every
  density, Trans. Amer. Math. Soc. 379 (2026), 8069–8090; arXiv:2411.11785. Theorem numbers follow the
  arXiv version.
- [EK22] Y. Egawa, K. Kimura, Regular graph and some vertex-deleted subgraph, Springer Proc. Math.
  Stat. 388 (2022), 245–259.
- [Er76b] P. Erdős, Problems and results in graph theory and combinatorial analysis, Proceedings
  of the Fifth British Combinatorial Conference (Aberdeen, 1975), Congressus Numerantium XV (1976), 169–192; the key is erdosproblems.com's. Problem 29 defines
  f_2(n), the least number of edges that forces two edge-disjoint cycles with the same vertex set, so
  f(n) = f_2(n) − 1.
- [JS23] O. Janzer, B. Sudakov, Resolution of the Erdős–Sauer problem on regular subgraphs, Forum
  Math. Pi 11 (2023), e19; arXiv:2204.12455.
- [Ka25] P. Katerinis, A note on regular factors in vertex-deleted subgraphs of regular bipartite
  graphs, Australas. J. Combin. 93(1) (2025), 211–215.
- [Me73] G. H. J. Meredith, Regular n-valent n-connected nonHamiltonian non-n-edge-colorable graphs,
  J. Combin. Theory Ser. B 14 (1973), 55–60.
- [Mü26] A. Müyesser, Hamiltonicity of mildly pseudorandom regular graphs, arXiv:2609.35766 (2026).
- [OPDP] A. Zarzuelo Urdiales, Ulam OPDP Difficulty Atlas (dataset),
  https://github.com/alejandrozu/ulam-opdp-difficulty-atlas; record 2194 (EP-585).
- [PRS95] L. Pyber, V. Rödl, E. Szemerédi, Dense graphs without 3-regular subgraphs, J. Combin.
  Theory Ser. B 63 (1995), 41–54.

Bibliographic data and quoted statements were checked against each source's own text (arXiv or
publisher pages and saved copies) except where noted. Further sources used by the working documents
(Bradač–Janzer, Draganić et al., Kim–Wormald, Tashkinov, Huang–Tait–Won, Cilleruelo) are cited there.

## Appendix A. Verbatim Lean statements

Every statement below passed `check.sh` again on October 6, 2026, on the Lean files of `v0.3`, with
the supplement's Lean files copied in for those under `supplement/` (transcripts in
`supplement/checks/`). Paths starting with `Openmath/` are in the public repository at tag `v0.3`;
paths starting with `supplement/` are in the supplement.

```lean
-- Openmath/Proofs/Final.lean:50  (Erdos585.maxEdges_eq_choose_two_of_le_four)
theorem maxEdges_eq_choose_two_of_le_four (n : ℕ) (hn : n ≤ 4) : maxEdges n = n.choose 2

-- Openmath/Proofs/Final.lean:54  (Erdos585.maxEdges_five)
theorem maxEdges_five : maxEdges 5 = 9

-- Openmath/Proofs/Final.lean:58  (Erdos585.maxEdges_six)
theorem maxEdges_six : maxEdges 6 = 12

-- Openmath/Proofs/Final.lean:62  (Erdos585.maxEdges_seven)
theorem maxEdges_seven : maxEdges 7 = 16

-- Openmath/Proofs/Final.lean:66  (Erdos585.three_mul_sub_six_le_maxEdges)
theorem three_mul_sub_six_le_maxEdges (n : ℕ) (hn : 5 ≤ n) : 3 * n - 6 ≤ maxEdges n

-- Openmath/Proofs/Final.lean:70  (Erdos585.three_mul_sub_five_le_maxEdges)
theorem three_mul_sub_five_le_maxEdges (n : ℕ) (hn : 7 ≤ n) : 3 * n - 5 ≤ maxEdges n

-- Openmath/Proofs/Final.lean:74  (Erdos585.three_mul_sub_four_le_maxEdges)
theorem three_mul_sub_four_le_maxEdges (n : ℕ) (hn : 9 ≤ n) : 3 * n - 4 ≤ maxEdges n

-- Openmath/Proofs/Final.lean:90  (Erdos585.maxEdges_succ_ge)
theorem maxEdges_succ_ge (n : ℕ) (hn : 3 ≤ n) : maxEdges n + 3 ≤ maxEdges (n + 1)

-- Openmath/Proofs/Final.lean:107  (Erdos585.four_mul_sub_thirteen_le_maxEdges)
theorem four_mul_sub_thirteen_le_maxEdges (n : ℕ) (hn : 10 ≤ n) :
    4 * n - 13 ≤ maxEdges n

-- Openmath/Proofs/Final.lean:112  (Erdos585.thirty_one_le_maxEdges_eleven)
theorem thirty_one_le_maxEdges_eleven : 31 ≤ maxEdges 11

-- Openmath/Proofs/Final.lean:116  (Erdos585.thirty_six_le_maxEdges_twelve)
theorem thirty_six_le_maxEdges_twelve : 36 ≤ maxEdges 12

-- Openmath/Proofs/Final.lean:102  (Erdos585.complete_matching_subdivision_lower_bound)
theorem complete_matching_subdivision_lower_bound (k : ℕ) :
    8 * k ^ 2 - 3 * k + 1 ≤ maxEdges (2 * k ^ 2 + 2)

-- Openmath/Proofs/Final.lean:120  (Erdos585.latin_incidence_lower_bound)
theorem latin_incidence_lower_bound (m : ℕ) : 5 * m ^ 2 ≤ maxEdges (m ^ 2 + 3 * m + 2)

-- Openmath/Proofs/Final.lean:124  (Erdos585.five_mul_sub_sqrt_le_maxEdges)
theorem five_mul_sub_sqrt_le_maxEdges (n : ℕ) (hn : 16 ≤ n) :
    5 * n - 15 * Nat.sqrt n - 10 ≤ maxEdges n

-- Openmath/Proofs/Final.lean:79
--   (Erdos585.doubleWheel_not_hasTwoEdgeDisjointCyclesSameVertexSet)
theorem doubleWheel_not_hasTwoEdgeDisjointCyclesSameVertexSet (k : ℕ) (hk : 2 ≤ k) :
    ¬ HasTwoEdgeDisjointCyclesSameVertexSet (doubleWheel (k + 3))

-- Openmath/Proofs/Final.lean:84
--   (Erdos585.thetaWheel_not_hasTwoEdgeDisjointCyclesSameVertexSet)
theorem thetaWheel_not_hasTwoEdgeDisjointCyclesSameVertexSet :
    ¬ HasTwoEdgeDisjointCyclesSameVertexSet thetaWheel

-- Openmath/Proofs/Final.lean:94
--   (Erdos585.matchingSubdivision_not_hasTwoEdgeDisjointCyclesSameVertexSet)
theorem matchingSubdivision_not_hasTwoEdgeDisjointCyclesSameVertexSet
    {V : Type*} [Fintype V] [DecidableEq V] (H M : SimpleGraph V)
    [DecidableRel H.Adj] [DecidableRel M.Adj] (hM : ∀ v, M.degree v ≤ 1) :
    ¬ HasTwoEdgeDisjointCyclesSameVertexSet (MatchingSubdivision.ofBase H M)
```

```lean
-- Openmath/Proofs/RegularFive.lean:105  (Erdos585.RegularFive.exists_five_regular_pairfree)
theorem exists_five_regular_pairfree :
    ∃ G : SimpleGraph (Fin 32), (∀ v, (G.neighborSet v).ncard = 5) ∧
      ¬ HasTwoEdgeDisjointCyclesSameVertexSet G

-- Openmath/Proofs/BipartiteFive.lean:171
--   (Erdos585.BipartiteFive.exists_bipartite_five_regular_pairfree)
theorem exists_bipartite_five_regular_pairfree :
    ∃ G : SimpleGraph (Fin 104), (∀ v, (G.neighborSet v).ncard = 5) ∧ G.Colorable 2 ∧
      ¬ HasTwoEdgeDisjointCyclesSameVertexSet G
```

```lean
-- Openmath/Proofs/RegularFive18.lean:92  (Erdos585.RegularFive18.exists_five_regular_pairfree)
theorem exists_five_regular_pairfree :
    ∃ G : SimpleGraph (Fin 18), (∀ v, (G.neighborSet v).ncard = 5) ∧
      ¬ HasTwoEdgeDisjointCyclesSameVertexSet G

-- Openmath/Proofs/QB5/Statement.lean:39  (Erdos585.qb5)
open scoped Classical in
/-- **QB(5)**: a bipartite graph with maximum degree at most six, `n ≥ 3` vertices and at least
`3n - 5` edges has a nonempty 4-regular subgraph. -/
theorem qb5 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite) (hdeg : G.maxDegree ≤ 6) (hn : 3 ≤ Fintype.card V)
    (he : 3 * Fintype.card V ≤ G.edgeSet.ncard + 5) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 4

-- Openmath/Proofs/QB4/Statement.lean:206  (Erdos585.qb4)
open scoped Classical in
/-- **QB(4)**: a bipartite graph with maximum degree at most six,
`n ≥ 2` vertices and at least `3n - 4` edges has a nonempty 4-regular subgraph. -/
theorem qb4 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite) (hdeg : G.maxDegree ≤ 6) (hn : 2 ≤ Fintype.card V)
    (he : 3 * Fintype.card V ≤ G.edgeSet.ncard + 4) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 4

-- Openmath/Proofs/QB4/Statement.lean:226
--   (Erdos585.exists_four_regular_avoiding_of_bipartite_six_regular)
open scoped Classical in
/-- **A vertex-deleted form**: for a bipartite 6-regular graph `B` and any vertex
`o`, the graph `B - o` has a nonempty 4-regular subgraph, stated as a nonempty 4-regular subgraph
of `B` avoiding `o`. -/
theorem exists_four_regular_avoiding_of_bipartite_six_regular {V : Type*} [Fintype V]
    (B : SimpleGraph V) [DecidableRel B.Adj] (hbip : B.IsBipartite) (hreg : B.IsRegularOfDegree 6)
    (o : V) :
    ∃ H : B.Subgraph, H.verts.Nonempty ∧ o ∉ H.verts ∧ H.coe.IsRegularOfDegree 4
```

```lean
-- supplement/lean/Openmath/Proofs/TwinNoSingleton.lean:30-31  (section variables)
variable {A R : Type*} [Fintype A] [Fintype R] [DecidableEq R]
    (G : SimpleGraph (A ⊕ R)) [DecidableRel G.Adj]

-- supplement/lean/Openmath/Proofs/TwinNoSingleton.lean:113
--   (Erdos585.TwinNoSingleton.hasPair_of_no_singleton_twins)
theorem hasPair_of_no_singleton_twins
    (hleft : ∀ a b : A, ¬ G.Adj (.inl a) (.inl b))
    (hright : ∀ r s : R, ¬ G.Adj (.inr r) (.inr s))
    (hmax : ∀ v, G.degree v ≤ 6)
    (hedges : G.edgeFinset.card + 2 = 3 * Fintype.card (A ⊕ R))
    (htwins : ∀ a : A, ∃ b : A, b ≠ a ∧
      ∀ r : R, G.Adj (.inl a) (.inr r) ↔ G.Adj (.inl b) (.inr r)) :
    HasTwoEdgeDisjointCyclesSameVertexSet G

-- supplement/lean/Openmath/Proofs/TwinCoreForcing.lean:33  (section variables)
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq I] [DecidableEq R]

-- supplement/lean/Openmath/Proofs/TwinCoreForcing.lean:415
--   (Erdos585.TwinCoreForcing.groupedGraph_hasPair_of_no_singletons)
theorem groupedGraph_hasPair_of_no_singletons (J : Finset (I × R)) (k : I → ℕ)
    (hk : ∀ i, 2 ≤ k i)
    (hmax : ∀ v, (groupedGraph J k).degree v ≤ 6)
    (hedges : (groupedGraph J k).edgeFinset.card + 2 =
      3 * Fintype.card ((Σ i, Fin (k i)) ⊕ R)) :
    HasTwoEdgeDisjointCyclesSameVertexSet (groupedGraph J k)
```

```lean
-- supplement/lean/Openmath/Proofs/ParabolaBarrier104.lean:145
--   (Erdos585.ParabolaBarrier104.arbitrary_polylog_barrier)
theorem arbitrary_polylog_barrier (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧ 2 ≤ k ∧ FamilyProperties k ∧
      ∀ v : FamilyVertex k,
        C * Real.rpow (Real.log (Fintype.card (FamilyVertex k))) A <
          ((familyGraph k).degree v : ℝ)
```

The R1-plus statement uses two definitions from the same file, verbatim:

```lean
-- supplement/lean/Openmath/Proofs/ParabolaBarrier104.lean:48
--   (Erdos585.ParabolaBarrier104.OneRoundBarrier)
/-- The full detector contract, with actual moves and connected cycles.
This definition has no assumed degree, closure or detector-failure premise. -/
def OneRoundBarrier : Prop :=
  FullColoring (Parabola104.canonical (F := F)) ∧
  ∀ (a b : F), a ≠ b →
    ∀ J : Set (twoFactor (Parabola104.canonical (F := F)) a b).ConnectedComponent,
      FullColoring (swap Parabola104.canonical a b J) ∧
      (∀ (i j : F), i ≠ j →
        ∀ D : (twoFactor (swap Parabola104.canonical a b J) i j).ConnectedComponent,
          ∃ (u : (F × F) × Bool)
            (p : (twoFactor (swap Parabola104.canonical a b J) i j).Walk u u),
              p.IsCycle ∧ p.toSubgraph.verts = D.supp) ∧
      (∀ (i j : F) (u : (F × F) × Bool)
        (p : (twoFactor (swap Parabola104.canonical a b J) i j).Walk u u),
        p.IsCycle →
          ¬ ∃ (w : (F × F) × Bool) (q : Parabola104.fullGraph.Walk w w),
            q.IsCycle ∧
            (p.mapLe (twoFactor_le (swap Parabola104.canonical a b J) i j)).support.toFinset =
              q.support.toFinset ∧
            Disjoint
              (p.mapLe (twoFactor_le (swap Parabola104.canonical a b J) i j)).edges.toFinset
              q.edges.toFinset)

-- supplement/lean/Openmath/Proofs/ParabolaBarrier104.lean:123
--   (Erdos585.ParabolaBarrier104.FamilyProperties)
/-- Structural and detector properties of the explicitly defined graph. -/
def FamilyProperties (k : ℕ) : Prop :=
  (familyGraph k).Connected ∧
  (familyGraph k).IsBipartite ∧
  Fintype.card (FamilyVertex k) = 2 * 3 ^ (2 * k) ∧
  (∀ v : FamilyVertex k, (familyGraph k).degree v = 3 ^ k) ∧
  (∀ (u : FamilyVertex k) (p : (familyGraph k).Walk u u), p.IsCycle → p.length ≠ 4) ∧
  OneRoundBarrier (F := FamilyField k)
```

## Appendix B. Edge lists

**The 18-vertex graph** (45 edges; labels as in `RegularFive18.lean`, copy c of the block on 9c, …,
9c + 8; also `supplement/graphs/regular-five-18.edges`):

```edges
0-1
0-2
0-3
0-4
0-5
1-2
1-3
1-4
1-5
2-3
2-4
2-5
3-6
3-7
4-6
4-7
5-6
5-8
6-7
6-8
7-8
7-17
8-16
8-17
9-10
9-11
9-12
9-13
9-14
10-11
10-12
10-13
10-14
11-12
11-13
11-14
12-15
12-16
13-15
13-16
14-15
14-17
15-16
15-17
16-17
```

**The 32-vertex graph** (80 edges; labels as in `RegularFive.lean`, copy c of the block on 8c, …,
8c + 7; also `supplement/graphs/regular-five-32.edges`):

```edges
0-3
0-4
0-5
0-9
0-10
1-3
1-4
1-6
1-7
1-8
2-3
2-5
2-6
2-7
2-18
3-6
3-7
4-5
4-6
4-7
5-6
5-7
8-11
8-12
8-13
8-24
9-11
9-12
9-14
9-15
10-11
10-13
10-14
10-15
11-14
11-15
12-13
12-14
12-15
13-14
13-15
16-19
16-20
16-21
16-25
16-26
17-19
17-20
17-22
17-23
17-24
18-19
18-21
18-22
18-23
19-22
19-23
20-21
20-22
20-23
21-22
21-23
24-27
24-28
24-29
25-27
25-28
25-30
25-31
26-27
26-29
26-30
26-31
27-30
27-31
28-29
28-30
28-31
29-30
29-31
```

**The 104-vertex graph** (260 edges; labels as in `BipartiteFive.lean`, copy c of the block on 13c, …,
13c + 12; also `supplement/graphs/bipartite-five-104.edges`). One color class is

0, 1, 2, 6, 8, 10, 16, 17, 18, 20, 22, 24, 25, 26, 27, 28, 32, 34, 36, 42, 43, 44, 46, 48, 50, 51, 52, 53, 54, 58, 60, 62, 68, 69, 70, 72, 74, 76, 77, 78, 79, 80, 84, 86, 88, 94, 95, 96, 98, 100, 102, 103;

the other 52 vertices form the other class (`BipartiteFive.side`, proved proper by `decide`).

```edges
0-3
0-4
0-5
0-7
0-11
1-3
1-4
1-5
1-7
1-11
2-3
2-4
2-5
2-9
2-12
3-6
3-8
4-6
4-8
5-6
5-10
6-7
6-9
7-8
7-10
8-9
8-12
9-10
9-22
10-11
10-12
11-24
11-50
12-25
12-51
13-16
13-17
13-18
13-20
13-24
14-16
14-17
14-18
14-20
14-24
15-16
15-17
15-18
15-22
15-25
16-19
16-21
17-19
17-21
18-19
18-23
19-20
19-22
20-21
20-23
21-22
21-25
22-23
23-24
23-25
24-37
25-90
26-29
26-30
26-31
26-33
26-37
27-29
27-30
27-31
27-33
27-37
28-29
28-30
28-31
28-35
28-38
29-32
29-34
30-32
30-34
31-32
31-36
32-33
32-35
33-34
33-36
34-35
34-38
35-36
35-48
36-37
36-38
37-50
38-51
38-77
39-42
39-43
39-44
39-46
39-50
40-42
40-43
40-44
40-46
40-50
41-42
41-43
41-44
41-48
41-51
42-45
42-47
43-45
43-47
44-45
44-49
45-46
45-48
46-47
46-49
47-48
47-51
48-49
49-50
49-51
52-55
52-56
52-57
52-59
52-63
53-55
53-56
53-57
53-59
53-63
54-55
54-56
54-57
54-61
54-64
55-58
55-60
56-58
56-60
57-58
57-62
58-59
58-61
59-60
59-62
60-61
60-64
61-62
61-74
62-63
62-64
63-76
63-102
64-77
64-103
65-68
65-69
65-70
65-72
65-76
66-68
66-69
66-70
66-72
66-76
67-68
67-69
67-70
67-74
67-77
68-71
68-73
69-71
69-73
70-71
70-75
71-72
71-74
72-73
72-75
73-74
73-77
74-75
75-76
75-77
76-89
78-81
78-82
78-83
78-85
78-89
79-81
79-82
79-83
79-85
79-89
80-81
80-82
80-83
80-87
80-90
81-84
81-86
82-84
82-86
83-84
83-88
84-85
84-87
85-86
85-88
86-87
86-90
87-88
87-100
88-89
88-90
89-102
90-103
91-94
91-95
91-96
91-98
91-102
92-94
92-95
92-96
92-98
92-102
93-94
93-95
93-96
93-100
93-103
94-97
94-99
95-97
95-99
96-97
96-101
97-98
97-100
98-99
98-101
99-100
99-103
100-101
101-102
101-103
```

The alternative 104-vertex graph is `supplement/graphs/bipartite-five-104-alt.edges` (not
isomorphic to the Lean graph: it has 542 four-cycles, the Lean graph 538).

## Appendix C. Census details

**Method.** The test peels the graph to its 4-core, tries every vertex subset S of the core with
minimum induced degree at least 4 (smallest first), enumerates every Hamilton cycle C1 of G[S]
through the least vertex of S, and searches G[S] − E(C1) for a second Hamilton cycle. Restricting to
δ ≥ 4 loses nothing, because deleting a vertex of degree at most 3 does not lower e − 3n, and a graph
with e ≥ 3n − 4 > 3n − 6 edges is not 3-degenerate, so its 4-core is nonempty. Programs,
commands and every log: `supplement/census/`.

**All counts** (0 pair-free unless stated):

| | Class | n | Graphs tested | Pair-free |
|---|---|---|---|---|
| 1 | Δ ≤ 6, δ ≥ 4, e ≥ 3n − 4 | 6, 7, 8, 9, 10 | 2, 14, 108, 1,857, 53,651 | 0 |
| 2 | same | 11 | 2,157,714 | 0 |
| 3 | same | 12 | 107,242,738 | 0 |
| 4 | same, bipartite | 13, 14, 15, 16, 17 | 12, 206, 588, 31,335, 196,531 | 0 |
| 5 | same, bipartite | 18 | 18,153,661 | 0 |
| 6 | 6-regular | 13 | 367,860 | 0 |
| 7 | 6-regular | 14 | 21,609,301 | 0 |
| 8 | bipartite 6-regular | 16, 18 | 7, 157 | 0 |
| 9 | Δ ≤ 6, δ ≥ 4, e = 3n − 5 | 7, 8, 9, 10, 11 | 7, 76, 1,620, 53,886, 2,360,506 | 1, 2, 3, 11, 0 |
| 10 | Δ ≤ 6, δ ≥ 4, e = 3n − 6 | 11 | 2,360,506 | 3,718 |
| 11 | connected 4-regular, Hamilton-decomposition test | 15, 16 | 805,491; 8,037,418 | 1,386; 8,719 without a decomposition |

The two n = 11 rows with 2,360,506 graphs are not a copying error: at n = 11, complementation maps
graphs with degrees in [4, 6] and 28 edges one-to-one onto those with 27 edges (an observation made
while preparing this document). None of the 17 pair-free graphs with e = 3n − 5 for n = 7, …, 10 has a
4-regular subgraph at all.

**Replication status.**

| | Claim | Status |
|---|---|---|
| 1 | ex(17), ex(18), ex(19) | two methods |
| 2 | no pair-free 5-regular graph on 16 vertices | one complete program; a second method on the triangle-free and bipartite classes and on a 0.14% sample |
| 3 | W1 for n ≤ 12 | computed twice (geng with pairc; gen585 reruns, `supplement/papers/census-extension/SMS-CENSUS-REVIEW.md`) |
| 4 | W1 for n = 13 | computed, independently replicated (different generator and pair test, 800 slices) |
| 5 | W1 for n = 14, hence no 6-regular pair-free graph on 15 vertices | one reviewed program (3,582.5 core-seconds) |
| 6 | W1 for bipartite graphs, n ≤ 18 | one program, one run per n; on the classes a smallest counterexample can lie in (sparse E4 with a ≤ 9, C1 with s ≤ 8), a second program (genbg with ptool; `supplement/census/pairs-lane/`) |
| 7 | 6-regular graphs, n ≤ 14 | direct single runs; also implied by replicated W1 at n − 1 |
| 8 | L5, H22 and the 5 + 5 census (section 5, question 2) | two methods each |
| 9 | S6 at 22 vertices | one program; an independent 0.376% spot-check |
| 10 | the 3n − 5 counts 1, 2, 3, 11, 0 | computed, independently replicated |
| 11 | 4-regular Hamilton-decomposition counts | one program |

**Gaps in the record.** For n ≤ 10, the entries of the rows e ≥ 3n − 4 and e = 3n − 5 come from the
census notes; their count logs were not saved. A later separate program reproduces these totals, and
the 17 pair-free graphs with e = 3n − 5 are listed in `supplement/census/logs/frontier-n{7,8,9,10}-level-5.g6`.
A direct 6-regular run at n = 15 was stopped at about 37%, with no part finished, and a bipartite 6-regular run at n = 20 was
stopped; neither is claimed. A check of `pairc.c` against a second method on 365 graphs has no saved
log, and the filter that selected the 4-edge-connected 4-regular graphs without a decomposition (3 at
n = 15, 15 at n = 16) was not saved as a script.

**Small values.** n ≤ 6: also brute force over all labeled graphs. n = 7 and 8: two programs with
different code agree. n = 9: backtracking with `erdos585_small.py` (151.3 s, 778,065 nodes) and, in
`erdos585_n9.py`, all 5,995 isomorphism classes of 12-edge complements, each with a verified witness,
and reduction from the 12 extremal classes at n = 8 (all 672 degree-5 extensions contain a pair).
n = 10: reduction from the n = 9 classes (all 1,008 degree-5 extensions contain a pair); backtracking
(21,925.5 s, 31,175,037 nodes); `erdos585_geng_filter.c` (7 outputs, all with 27 edges); and the
deletion catalog (7 classes with 27 edges, none with 28), which agrees with a separate canonical
nauty run. n = 11: a `geng` prune hook with a cycle detector, and an independent deletion search that
uses neither. n = 12: the same `geng` method, and an independent targeted audit that starts from all
828 ten-vertex 26-edge classes of the deletion catalog and rejects all 2,367 eligible eleven-vertex
31-edge extensions with minimum degree at least 5, so no twelve-vertex graph with 37 edges is
pair-free (`supplement/small-values/logs/twelve-upper-independent-result.json`; the "still running"
note in `geng-twelve-result.json` predates it). Only one exhaustive method shows that the extremal
graph for n = 12 is unique up to isomorphism (not claimed in section 1). The backtracking program, the
independent checker and the n = 9 program, with the results (`585-small-n.md`) and their commands and
outputs (`COMMANDS.md`), are in the public repository under `computations/`; the `geng` filter, the
deletion catalog and every program, log and note for n = 9 to 12 are in `supplement/small-values/`.

## Appendix D. Proofs

**Conventions.** A multigraph is loopless and may have parallel edges; a cycle is a connected
2-regular subgraph, so two parallel edges form a cycle of length 2. In a substitution, every O-vertex o
lies on exactly d − deg_Γ(o) link edges; the deficiencies sum to d.

**Lemma 1 (single passage).** Let G be a substitution of a d-gadget into L with d ≤ 7, and let
(C1, C2) be a pair of G on vertex set S. If S meets Γ_u, then either S ⊆ V(Γ_u), or exactly four link
edges at Γ_u lie in C1 ∪ C2, two in each cycle.

*Proof.* H = C1 ∪ C2 is 4-regular on S. Let S_I, S_O be the vertices of S on the two sides of Γ_u, and
x the number of link edges at Γ_u used by H. Every neighbor of an I-vertex is an O-vertex of the same
copy, so the 4|S_I| H-edges at S_I end in S_O; the 4|S_O| edge ends at S_O are those edges plus the x
link edges. So x = 4(|S_O| − |S_I|). There are only d ≤ 7 link edges at Γ_u, so x ∈ {0, 4}. If x = 0,
C1 is connected and cannot leave the copy, so S ⊆ V(Γ_u). If x = 4, the link edges at Γ_u are the edge
cut around the copy; each cycle meets both sides and crosses the cut an even, positive number of
times, so each uses exactly two. ∎

**Proof of Theorem R1.** A pair inside one copy would be a pair of Γ. Otherwise, by Lemma 1 each cycle
C_i uses exactly two link edges at every copy it meets. Delete the edges inside copies; the remaining
link edges of C_i form an edge set E_i of L in which every vertex of U (the copies met) has degree 2.
E_i is connected: walking around C_i, consecutive vertices lie in the same copy or in copies joined by
an edge of E_i, and the walk visits every copy in U. A connected 2-regular loopless multigraph is a
cycle (of length 2 if |U| = 2). So E_1, E_2 are cycles of L on the same vertex set U, edge-disjoint
because link edges correspond one-to-one to edges of L. That is a pair in L. ∎

**Proof of Corollary B.** One direction is trivial. Suppose B − o is pair-free, with o in side X of B.
Then B − o is a 6-gadget with I = X − o and O = Y; the six neighbors of o have degree 5, so the six
deficiency units sit on six distinct vertices and a simple substitution into any 6-regular multigraph
exists. Let K be the 4-regular multigraph on {0, 1, 2, 3} with edges 03 (three times), 12 (three
times), 02 and 13; K has no two edge-disjoint Hamilton cycles. Replace each vertex of K by a 4-cycle
abcd with ab, bc, cd tripled and da single, orient K as 0→3, 0→3, 3→0, 3→1, 1→2, 1→2, 2→1, 2→0, and for
each arc u→w join d of piece u to a of piece w. This gives a bipartite 6-regular multigraph L6b on 16
vertices. It is pair-free: each piece is pair-free and attached by exactly four edges, so a pair that
leaves a piece passes through each piece it meets once per cycle and projects to a pair of K. K has
no pair: no edge has multiplicity four, K has no triangle, and it has no two edge-disjoint Hamilton
cycles. Theorem R1 applied to B − o and L6b gives a bipartite 6-regular graph with no pair. ∎

**Corollary C (no easy certificate).** A 6-gadget has 3n − 3 edges. A bipartite graph in which every
subgraph has a vertex of degree at most 3 has at most 3n − 9 edges (n ≥ 6), and a simple graph in which
every subgraph of minimum degree at least 4 has an edge cut of size at most 3 has at most 3n − 6
edges (n ≥ 3). So neither degeneracy nor small cuts can certify a pair-free 6-gadget.

**Lemma F** (statement in section 4.7; verbatim from the source report, reviewed: accepted, with the
note that in the expansion convention of BM-2 the factor is a (γ/4)-expander, not a (γ/2)-expander):

> **Lemma F (bipartite, balanced).** Let H be bipartite with parts P, Q, |P| = |Q| = N/2, all degrees
> in [(1-η)k, k], and e_H(Z, V(H) \ Z) >= γk|Z| for every Z with 1 <= |Z| <= N/2, where 0 < γ <= 1,
> η <= γ^2/8 and k >= 16/γ^2. Put θ = (η + 2/k)/γ and k' = floor((1 - η - θ)k). Then H has a
> spanning k'-regular subgraph F, k' >= (1 - 3γ/8)k - 1, and e_F(Z, V(F) \ Z) >= (γ/2)k'|Z| for every
> |Z| <= N/2.
>
> *Proof.* By max-flow min-cut (source to P with capacity k', unit edges, Q to sink with capacity
> k'), H has a k'-factor iff k'|X| <= k'|Y| + e(X, Q \ Y) for all X ⊆ P and Y ⊆ Q. The condition is
> self-complementary: for X' = Q \ Y and Y' = P \ X it reads k'|X'| <= k'|Y'| + e(X', P \ Y'), the
> same condition with the sides swapped. So suppose (X, Y) violates it with Z = X ∪ Y of size at
> most N/2 (otherwise use the complementary pair, whose union V(H) \ Z is smaller than N/2).
> Violation gives k'(|X| - |Y|) > e(X, Q \ Y) >= 0, so |X| > |Y| and |Y| < |Z|/2. Degree counts give
> e(X, Y) + e(X, Q \ Y) >= (1-η)k|X| and e(X, Y) + e(Y, P \ X) <= k|Y|. Hence
> e(Y, P \ X) < (k - k')|Y| - ((1-η)k - k')|X| <= ((η+θ)k + 1)|Y| - θk|X|.
> Non-negativity gives |X| - |Y| < ((ηk + 1)/(θk))|Y|, so e(X, Q \ Y) < k'(|X| - |Y|) <
> ((ηk + 1)/θ)|Y|; and, using |X| > |Y|, e(Y, P \ X) < (ηk + 1)|Y|. Adding,
> e(Z, V \ Z) < (ηk + 1)(1 + 1/θ)|Y| < (η + 1/k)(1 + 1/θ)k|Z|/2 <= (η + 1/k + γ)k|Z|/2 < γk|Z|,
> using (η + 1/k)/θ <= γ and η + 1/k <= 3γ^2/16 < γ. This contradicts expansion. For the bounds:
> θ <= γ/4 because 2/k <= γ^2/8, so η + θ <= 3γ/8. Each vertex loses at most k - k' <= (3γ/8)k + 1
> edges, so e_F(Z, V \ Z) >= (γ - 3γ/8 - 1/k)k|Z| >= (γ/2)k'|Z|. ∎

## Appendix E. Other Lean-proved declarations

56 other declarations passed `check.sh` on October 4, 2026 (2 to 12
seconds each on a built project, as `supplement/lean/DECLARATIONS.md` lists; the October 4 transcripts
record no times), and all of them passed again on October 6 on the Lean files of
`v0.3`, with the supplement's Lean files copied in: special cases (Haar graphs, cube-like graphs,
Wenger graphs), counterexamples to specific lifting or raising rules, and supporting lemmas. None of
them changes the bounds above. `supplement/lean/DECLARATIONS.md` lists each with its file, and
`supplement/checks/` holds the transcript of every check.

## Appendix F. Supplement contents

`supplement/MANIFEST.md` lists the current files, sizes and SHA-256 values, including the corrections
and added small-value certificates. `supplement/PROVENANCE.json` preserves the original v0.3
export's source paths, hashes and edits; it is historical, not the current release inventory.

- `lean/Openmath/Proofs/`: 58 Lean files outside the repository's Lean build (twin-core,
  R1-plus, the declarations of `lean/DECLARATIONS.md`, and their imports).
- `checks/`: the transcript of every October 4 `check.sh` run, and the October 5 and 6 checks of the
  `v0.3` release files, with the supplement's Lean files copied in.
- `graphs/`: the three edge lists, the coloring, the alternative 104-vertex graph, and
  `verify_graphs.py`, which checks all four from the edge lists alone in a few seconds, with no
  packages.
- `census/`: programs, commands and census logs: the W1 census, `census/quartic/` (the census of
  bipartite graphs without a 4-regular subgraph behind section 4.1's sharpness paragraph, called F1
  there), `census/calibration/` (the degree-5 calibration, with the 16-vertex census in `n16/` and its
  second method in `n16-second-method/`), `census/pairs-lane/`, `census/h22/` and `census/l5/` (the
  censuses of section 5, question 2), `census/s6n22/` (S6 at 22 vertices, with `spot-check/`) and
  `census/edge/` (the edge census of section 5, question 4). `small-values/`: programs, logs and notes
  for n = 9 to 12.
- `papers/`: the write-ups behind sections 4.1, 4.3, 4.4, 4.6, 4.7, 4.8 and 5, with their reviews and
  certificates; `papers/quartic/` holds the written proof of QB(4) and P_2, its three reviews with the
  referees' code, and the two earlier reports it cites; `papers/qb5/` holds the four papers of the
  written proof of QB(5) (the Lean proof is in the public repository), each with its frozen hash list and its referee's report, the code and data the
  hash lists name, and each referee's code; `papers/b6-24/` holds the written proof of B6 through 24
  vertices and `papers/s6/` the paper behind S6 (section 5, questions 2 and 3); `papers/pairs/` and
  `papers/p4-attempt/` hold the sources of section 5, questions 2 to 4; `papers/six-port-gadget/` holds the project's earlier
  notes on G110, the question that section 4.1 now settles.

Labels used here and in the supplement's working documents:

| | Here | In the supplement | Meaning |
|---|---|---|---|
| 1 | E110, V110, G110 | the same | statements named after research pass 110 (sections 4.1, 4.7 and 5) |
| 2 | ex(n) | the same | the edge census of section 5, question 4 |
| 3 | the four censuses of section 5, question 2 | F2 (or census F2), L5, the 5 + 5 census, H22 | see the supplement's glossary |
| 4 | R1 | "Fable R1" | the substitution theorem of section 4.6 |
| 5 | R1-plus | `ParabolaBarrier104` | the recoloring barrier of section 4.8 |
| 6 | S6, E10, port | the same | section 5, question 3 |
| 7 | the vertex-deleted form of B6 | VA6 | every bipartite 6-regular B has, for every vertex o, a pair in B − o |
| 8 | W1 | S10 (census documents and programs) | Δ ≤ 6 and e ≥ 3n − 4 force a pair |
| 9 | W1 for bipartite graphs | W1b | Δ ≤ 6 and e ≥ 3n − 4 force a pair, for bipartite graphs |
