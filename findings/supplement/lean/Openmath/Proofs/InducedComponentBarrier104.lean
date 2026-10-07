import Openmath.Proofs.Extension

/-!
# Actual cycle partners in induced components of maximum degree three

This is the graph/cycle bridge used by the pass104 parabola barrier.
It does not itself supply the explicit family or the legal recolorings.
Both walks below are genuine cycles in the original graph; support and
edge disjointness are the existing finite-set presentation of the
project's faithful cycle predicate.
-/

namespace Erdos585.InducedComponentBarrier104

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G H : SimpleGraph V} [DecidableRel H.Adj]

/-- A cycle in a component that is induced in `G` and has maximum degree
at most three cannot have an edge-disjoint `G`-cycle on the same support. -/
theorem no_partner
    (hHG : H ≤ G)
    (hclosed : ∀ x y, H.Reachable x y → G.Adj x y → H.Adj x y)
    (hdegree : ∀ x, H.degree x ≤ 3)
    {u : V} (p : H.Walk u u) (hp : p.IsCycle) :
    ¬ ∃ (w : V) (q : G.Walk w w), q.IsCycle ∧
      (p.mapLe hHG).support.toFinset = q.support.toFinset ∧
      Disjoint (p.mapLe hHG).edges.toFinset q.edges.toFinset := by
  rintro ⟨w, q, hq, hsupport, hdisjoint⟩
  have hpG : (p.mapLe hHG).IsCycle := hp.mapLe hHG
  have hu : u ∈ (p.mapLe hHG).support := (p.mapLe hHG).start_mem_support
  have hfour : (pairNbrs (p.mapLe hHG) q u).card = 4 :=
    card_pairNbrs hpG hq hsupport hdisjoint hu
  have hsub : pairNbrs (p.mapLe hHG) q u ⊆ H.neighborFinset u := by
    intro x hx
    have hxG : G.Adj u x := adj_of_mem_pairNbrs hx
    have hxS : x ∈ (p.mapLe hHG).support :=
      mem_support_of_mem_pairNbrs hsupport (mem_pairNbrs_symm hx)
    have hxP : x ∈ p.support := by simpa only [Walk.support_mapLe_eq_support] using hxS
    have hxR : H.Reachable u x := ⟨p.takeUntil x hxP⟩
    exact (mem_neighborFinset H u x).2 (hclosed u x hxR hxG)
  have hbound := Finset.card_le_card hsub
  rw [hfour, H.card_neighborFinset_eq_degree] at hbound
  have hthree := hdegree u
  omega

end Erdos585.InducedComponentBarrier104
