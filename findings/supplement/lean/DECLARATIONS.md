# Other declarations with a passing check

The other declarations that passed `check.sh` on October 4, 2026: special cases
(Haar graphs, cube-like graphs, Wenger graphs), counterexamples to specific lifting or raising rules, and
supporting lemmas. None of them changes the bounds in the findings document. All of them passed again on
October 6 on the Lean files of the public repository's tag `v0.3`, with the files of `lean/Openmath/Proofs/`
copied in. Files under `Openmath/Proofs/` that are not in `v0.3` are in `lean/Openmath/Proofs/`; the
transcript of each check is in `checks/`.

| | Declaration | File | Check, October 4 | Check on `v0.3`, October 6 |
|---|---|---|---|---|
| 1 | `Erdos585.AdjacentHubs.thirty_six_le` | `Openmath/Proofs/AdjacentHubs.lean` | PASS (12 s) | PASS |
| 2 | `Erdos585.BipartiteBalance.at_most_one_exceptional` | `Openmath/Proofs/BipartiteBalance.lean` | PASS (7 s) | PASS |
| 3 | `Erdos585.BipartiteEulerian.counterexample` | `Openmath/Proofs/BipartiteEulerian.lean` | PASS (6 s) | PASS |
| 4 | `Erdos585.BipartiteObstruction.missing_matching_three` | `Openmath/Proofs/BipartiteObstruction.lean` | PASS (6 s) | PASS |
| 5 | `Erdos585.BipartiteSeparation.counterexample` | `Openmath/Proofs/BipartiteSeparation.lean` | PASS (5 s) | PASS |
| 6 | `Erdos585.CoverTransfer.counterexample` | `Openmath/Proofs/CoverTransfer.lean` | PASS (6 s) | PASS |
| 7 | `Erdos585.Cubelike.card_le_three_of_avoiding` | `Openmath/Proofs/Cubelike.lean` | PASS (6 s) | PASS |
| 8 | `Erdos585.Cubelike.forest_certificate` | `Openmath/Proofs/Cubelike.lean` | PASS (7 s) | PASS |
| 9 | `Erdos585.Cubelike.hasPair_of_four` | `Openmath/Proofs/Cubelike.lean` | PASS (6 s) | PASS |
| 10 | `Erdos585.Cubelike.regular_gamma_cubelike` | `Openmath/Proofs/Cubelike.lean` | PASS (6 s) | PASS |
| 11 | `Erdos585.CubelikeForest.cycle_law_forest_of_certificate` | `Openmath/Proofs/CubelikeForest.lean` | PASS (3 s) | PASS |
| 12 | `Erdos585.CubelikeSplit.counterexample` | `Openmath/Proofs/CubelikeSplit.lean` | PASS (6 s) | PASS |
| 13 | `Erdos585.CubelikeWitness.hasPair_folded` | `Openmath/Proofs/CubelikeWitness.lean` | PASS (6 s) | PASS |
| 14 | `Erdos585.CubelikeWitness.hasPair_q4` | `Openmath/Proofs/CubelikeWitness.lean` | PASS (6 s) | PASS |
| 15 | `Erdos585.CycleLift.splitGraph_pairfree` | `Openmath/Proofs/CycleLift.lean` | PASS (6 s) | PASS |
| 16 | `Erdos585.DensityCore.regular_six_core` | `Openmath/Proofs/DensityCore.lean` | PASS (6 s) | PASS |
| 17 | `Erdos585.DirectedState.counterexample` | `Openmath/Proofs/DirectedState.lean` | PASS (7 s) | PASS |
| 18 | `Erdos585.DirectedState.forced_of_two_six_cuts` | `Openmath/Proofs/DirectedState.lean` | PASS (6 s) | PASS |
| 19 | `Erdos585.FactorExchange.no_spanning_cycle` | `Openmath/Proofs/FactorExchange.lean` | PASS (6 s) | PASS |
| 20 | `Erdos585.Haar.rankThree_hasPair` | `Openmath/Proofs/Haar.lean` | PASS (5 s) | PASS |
| 21 | `Erdos585.HaarClassification.hasPair_of_four` | `Openmath/Proofs/HaarClassification.lean` | PASS (7 s) | PASS |
| 22 | `Erdos585.HaarComposite.hasTwoEdgeDisjointCyclesSameVertexSet` | `Openmath/Proofs/HaarComposite.lean` | PASS (6 s) | PASS |
| 23 | `Erdos585.HaarCompositeEven.hasTwoEdgeDisjointCyclesSameVertexSet_all` | `Openmath/Proofs/HaarCompositeEven.lean` | PASS (6 s) | PASS |
| 24 | `Erdos585.HaarCycle.cycle_of_two_matchings` | `Openmath/Proofs/HaarCycle.lean` | PASS (2 s) | PASS |
| 25 | `Erdos585.HaarCycle.splice_isCycleOn` | `Openmath/Proofs/HaarCycle.lean` | PASS (2 s) | PASS |
| 26 | `Erdos585.HaarDegree.four_le_card_of_pair` | `Openmath/Proofs/HaarDegree.lean` | PASS (6 s) | PASS |
| 27 | `Erdos585.HaarExtraction.family_boundary` | `Openmath/Proofs/HaarExtraction.lean` | PASS (6 s) | PASS |
| 28 | `Erdos585.HaarGamma.hasPair_iff` | `Openmath/Proofs/HaarGamma.lean` | PASS (7 s) | PASS |
| 29 | `Erdos585.HaarGamma.regular_gamma_haar` | `Openmath/Proofs/HaarGamma.lean` | PASS (6 s) | PASS |
| 30 | `Erdos585.HaarPair.hasPair_of_matching_permutations` | `Openmath/Proofs/HaarPair.lean` | PASS (6 s) | PASS |
| 31 | `Erdos585.HaarRankOne.hasPair_of_four_distinct` | `Openmath/Proofs/HaarRankOne.lean` | PASS (5 s) | PASS |
| 32 | `Erdos585.HaarRankTwo.hasPair` | `Openmath/Proofs/HaarRankTwo.lean` | PASS (6 s) | PASS |
| 33 | `Erdos585.HaarSixCycle.exists_six_cycle` | `Openmath/Proofs/HaarSixCycle.lean` | PASS (6 s) | PASS |
| 34 | `Erdos585.IncidenceExpansion.three_hamilton_cycles` | `Openmath/Proofs/IncidenceExpansion.lean` | PASS (7 s) | PASS |
| 35 | `Erdos585.LatinIncidence.five_mul_sq_le` | `Openmath/Proofs/LatinIncidence.lean` | PASS (6 s) | PASS |
| 36 | `Erdos585.LatinIncidence.five_mul_sub_sqrt_le` | `Openmath/Proofs/LatinIncidence.lean` | PASS (6 s) | PASS |
| 37 | `Erdos585.LocalMatchingProbe.probe_unmatched_bounds` | `Openmath/Proofs/LocalMatchingProbe.lean` | PASS (3 s) | PASS |
| 38 | `Erdos585.MatchingJoin.matching_join_raising_counterexample` | `Openmath/Proofs/MatchingJoinCore.lean` | PASS (6 s) | PASS |
| 39 | `Erdos585.MatchingSubdivision.complete_even_lower_bound` | `Openmath/Proofs/MatchingSubdivision.lean` | PASS (6 s) | PASS |
| 40 | `Erdos585.MatchingSubdivision.lower_bound` | `Openmath/Proofs/MatchingSubdivision.lean` | PASS (7 s) | PASS |
| 41 | `Erdos585.MatchingSubdivision.no_four_regular` | `Openmath/Proofs/MatchingSubdivision.lean` | PASS (6 s) | PASS |
| 42 | `Erdos585.MatchingSubdivision.ofBase_edge_count` | `Openmath/Proofs/MatchingSubdivision.lean` | PASS (6 s) | PASS |
| 43 | `Erdos585.MatchingSubdivision.ofBase_not_hasPair` | `Openmath/Proofs/MatchingSubdivision.lean` | PASS (6 s) | PASS |
| 44 | `Erdos585.MatchingSubdivision.ofBase_vertex_count` | `Openmath/Proofs/MatchingSubdivision.lean` | PASS (6 s) | PASS |
| 45 | `Erdos585.PortCompletion.exists_good_pairing` | `Openmath/Proofs/PortCompletion.lean` | PASS (7 s) | PASS |
| 46 | `Erdos585.RegularFive.graph_edge_count` | `Openmath/Proofs/RegularFive.lean` | PASS (6 s) | PASS |
| 47 | `Erdos585.RimDensity.four_bounds` | `Openmath/Proofs/RimDensity.lean` | PASS (6 s) | PASS |
| 48 | `Erdos585.SignedPrismCore.signed_prism_raising_counterexample` | `Openmath/Proofs/SignedPrismCore.lean` | PASS (6 s) | PASS |
| 49 | `Erdos585.TwoHub.thirty_one_le` | `Openmath/Proofs/TwoHub.lean` | PASS (6 s) | PASS |
| 50 | `Erdos585.TwoHubFamily.four_mul_sub_thirteen_le` | `Openmath/Proofs/TwoHubFamily.lean` | PASS (6 s) | PASS |
| 51 | `Erdos585.Wenger.no_six_cycle` | `Openmath/Proofs/Wenger.lean` | PASS (4 s) | PASS |
| 52 | `Erdos585.card_edges_delete_vertex` | `Openmath/Proofs/SmallExact.lean` | PASS (5 s) | PASS |
| 53 | `Erdos585.delete_vertex_bound` | `Openmath/Proofs/SmallExact.lean` | PASS (7 s) | PASS |
| 54 | `Erdos585.hasPair_six_of_thirteen` | `Openmath/Proofs/SmallExact.lean` | PASS (6 s) | PASS |
| 55 | `Erdos585.not_hasPairF_induce` | `Openmath/Proofs/SmallExact.lean` | PASS (6 s) | PASS |
| 56 | `Erdos585.not_hasPairF_of_small_cut` | `Openmath/Proofs/CutGluing.lean` | PASS (6 s) | PASS |
