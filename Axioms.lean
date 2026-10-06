import Openmath.Target
import Openmath.Proofs.TopFive
import Openmath.Proofs.Final
import Openmath.Proofs.RegularFive
import Openmath.Proofs.BipartiteFive
import Openmath.Proofs.RegularFive18
import Openmath.Proofs.QB4.Statement
import Openmath.Proofs.QB5.Statement

/-! Prints the axioms of every result listed in
    `scripts/headline-theorems.json`; `scripts/check_axioms.py`
    checks the output. -/

#print axioms Erdos585.maxEdges_eq_choose_two_of_le_four
#print axioms Erdos585.maxEdges_five
#print axioms Erdos585.maxEdges_six
#print axioms Erdos585.maxEdges_seven
#print axioms Erdos585.three_mul_sub_six_le_maxEdges
#print axioms Erdos585.three_mul_sub_five_le_maxEdges
#print axioms Erdos585.three_mul_sub_four_le_maxEdges
#print axioms Erdos585.maxEdges_succ_ge
#print axioms Erdos585.four_mul_sub_thirteen_le_maxEdges
#print axioms Erdos585.thirty_one_le_maxEdges_eleven
#print axioms Erdos585.thirty_six_le_maxEdges_twelve
#print axioms Erdos585.complete_matching_subdivision_lower_bound
#print axioms Erdos585.latin_incidence_lower_bound
#print axioms Erdos585.five_mul_sub_sqrt_le_maxEdges
#print axioms Erdos585.doubleWheel_not_hasTwoEdgeDisjointCyclesSameVertexSet
#print axioms Erdos585.thetaWheel_not_hasTwoEdgeDisjointCyclesSameVertexSet
#print axioms Erdos585.matchingSubdivision_not_hasTwoEdgeDisjointCyclesSameVertexSet
#print axioms Erdos585.RegularFive.exists_five_regular_pairfree
#print axioms Erdos585.BipartiteFive.exists_bipartite_five_regular_pairfree
#print axioms Erdos585.RegularFive18.exists_five_regular_pairfree
#print axioms Erdos585.qb5
#print axioms Erdos585.qb4
#print axioms Erdos585.exists_four_regular_avoiding_of_bipartite_six_regular
#print axioms Erdos585.hasPair_top_five
#print axioms Erdos585.hasTwoEdgeDisjointCyclesSameVertexSet_top_five
