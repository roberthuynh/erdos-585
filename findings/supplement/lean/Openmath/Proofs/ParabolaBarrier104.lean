import Openmath.Proofs.InducedComponentBarrier104
import Openmath.Proofs.ParabolaAlgebra104
import Openmath.Proofs.ParabolaGrowth104
import Openmath.Proofs.ParabolaGraph104
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The literal finite-field family for the one-transformation barrier

The endpoint includes the literal graph, genuine component-union swaps,
actual connected cycle witnesses and an unrestricted actual second cycle.
It is a limitation of this supplied-coloring method, not graph avoidance.
-/

namespace Erdos585.ParabolaBarrier104

open SimpleGraph KempeSwap104

section GenericField

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
variable [CharP F 3] [Algebra (ZMod 3) F]

/-- Every actual cycle exposed by the specified transformation has no
edge-disjoint original-host cycle on its actual vertex support. -/
theorem exposed_cycle_no_partner (a b : F)
    (J : Set (twoFactor (Parabola104.canonical (F := F)) a b).ConnectedComponent)
    (i j : F) {u : (F × F) × Bool}
    (p : (twoFactor (swap Parabola104.canonical a b J) i j).Walk u u)
    (hp : p.IsCycle) :
    ¬ ∃ (w : (F × F) × Bool) (q : Parabola104.fullGraph.Walk w w),
      q.IsCycle ∧
      (p.mapLe (twoFactor_le (swap Parabola104.canonical a b J) i j)).support.toFinset =
        q.support.toFinset ∧
      Disjoint
        (p.mapLe (twoFactor_le (swap Parabola104.canonical a b J) i j)).edges.toFinset
        q.edges.toFinset := by
  obtain ⟨T, hT, hcard, hfactor⟩ :=
    swap_factor_palette (Parabola104.canonical (F := F)) a b J i j
  rw [Parabola104.canonical_colorSubgraph] at hfactor
  have hnone := InducedComponentBarrier104.no_partner
    (Parabola104.graph_le_full T)
    (fun x y hr he => Parabola104.three_color_component_induced T hT hcard hr he)
    (fun x => by rw [Parabola104.graph_degree]; exact hcard)
    (p.mapLe hfactor) (hp.mapLe hfactor)
  simpa only [Walk.support_mapLe_eq_support, Walk.edges_mapLe_eq_edges] using hnone

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

theorem one_round_barrier : OneRoundBarrier (F := F) := by
  refine ⟨Parabola104.canonical_full, ?_⟩
  intro a b _ J
  refine ⟨swap_fullColoring _ Parabola104.canonical_full a b J, ?_, ?_⟩
  · intro i j hij D
    exact swap_twoFactor_component_cycle _ Parabola104.canonical_full a b J hij D
  · intro i j u p hp
    exact exposed_cycle_no_partner a b J i j p hp

end GenericField

instance prime_three : Fact (Nat.Prime 3) := ⟨by decide⟩

abbrev FamilyField (k : ℕ) := GaloisField 3 k

noncomputable instance fieldFintype (k : ℕ) : Fintype (FamilyField k) :=
  Fintype.ofFinite _

noncomputable instance fieldDecidableEq (k : ℕ) : DecidableEq (FamilyField k) :=
  Classical.decEq _

abbrev FamilyVertex (k : ℕ) := (FamilyField k × FamilyField k) × Bool

noncomputable def familyGraph (k : ℕ) : SimpleGraph (FamilyVertex k) :=
  Parabola104.fullGraph

noncomputable instance familyGraphDecidable (k : ℕ) : DecidableRel (familyGraph k).Adj :=
  Parabola104.fullGraph_decidable

theorem field_card (k : ℕ) (hk : 2 ≤ k) :
    Fintype.card (FamilyField k) = 3 ^ k := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 3 k (by omega)

theorem vertex_card (k : ℕ) (hk : 2 ≤ k) :
    Fintype.card (FamilyVertex k) = 2 * 3 ^ (2 * k) := by
  simp only [FamilyVertex, Fintype.card_prod, Fintype.card_bool, field_card k hk]
  rw [show 2 * k = k + k by omega, pow_add]
  ring

/-- The numerical estimate refers to the cardinality of the actual vertex type. -/
theorem family_ledger_exceeds_polylog (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧ 2 ≤ k ∧
      C * Real.rpow (Real.log (Fintype.card (FamilyVertex k))) A <
        (Fintype.card (FamilyField k) : ℝ) := by
  obtain ⟨k, hK, hk, hlarge⟩ :=
    ParabolaGrowth104.exists_polylog_lt_pow_three C A hC hA K
  refine ⟨k, hK, hk, ?_⟩
  rw [vertex_card k hk, field_card k hk]
  exact_mod_cast hlarge

/-- Structural and detector properties of the explicitly defined graph. -/
def FamilyProperties (k : ℕ) : Prop :=
  (familyGraph k).Connected ∧
  (familyGraph k).IsBipartite ∧
  Fintype.card (FamilyVertex k) = 2 * 3 ^ (2 * k) ∧
  (∀ v : FamilyVertex k, (familyGraph k).degree v = 3 ^ k) ∧
  (∀ (u : FamilyVertex k) (p : (familyGraph k).Walk u u), p.IsCycle → p.length ≠ 4) ∧
  OneRoundBarrier (F := FamilyField k)

theorem family_properties (k : ℕ) (hk : 2 ≤ k) : FamilyProperties k := by
  refine ⟨Parabola104.fullGraph_connected, Parabola104.fullGraph_bipartite,
    vertex_card k hk, ?_, ?_, one_round_barrier⟩
  · intro v
    change Parabola104.fullGraph.degree v = 3 ^ k
    rw [Parabola104.fullGraph_degree, field_card k hk]
  · intro u p hp
    exact Parabola104.fullGraph_no_four_cycle p hp

/-- No fixed real polylogarithmic degree threshold can guarantee success
for one two-class transformation of every supplied coloring. The witness
is the literal connected, bipartite, C4-free family, at arbitrarily large
indices; the successful-pair prohibition is only on its exposed supports. -/
theorem arbitrary_polylog_barrier (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧ 2 ≤ k ∧ FamilyProperties k ∧
      ∀ v : FamilyVertex k,
        C * Real.rpow (Real.log (Fintype.card (FamilyVertex k))) A <
          ((familyGraph k).degree v : ℝ) := by
  obtain ⟨k, hK, hk, hlarge⟩ := family_ledger_exceeds_polylog C A hC hA K
  refine ⟨k, hK, hk, family_properties k hk, ?_⟩
  intro v
  change C * Real.rpow (Real.log (Fintype.card (FamilyVertex k))) A <
    (Parabola104.fullGraph.degree v : ℝ)
  rw [Parabola104.fullGraph_degree]
  exact hlarge

end Erdos585.ParabolaBarrier104
