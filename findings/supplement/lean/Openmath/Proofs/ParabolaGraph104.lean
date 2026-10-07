import Openmath.Proofs.ParabolaAlgebra104
import Openmath.Proofs.HaarComponents104
import Openmath.Proofs.KempeSwap104
import Openmath.Proofs.HaarDegree

/-! # The literal characteristic-three parabola graph and its canonical colors -/

noncomputable section

namespace Erdos585.Parabola104

open SimpleGraph Finset

variable {F : Type*} [Field F] [DecidableEq F]

def colors (T : Finset F) : Finset (F × F) := T.image point

def graph (T : Finset F) : SimpleGraph ((F × F) × Bool) := Haar.graph (colors T)

instance graph_decidable (T : Finset F) : DecidableRel (graph T).Adj :=
  inferInstanceAs (DecidableRel (Haar.graph (colors T)).Adj)

@[simp] theorem mem_colors {T : Finset F} {x : F × F} :
    x ∈ colors T ↔ ∃ a ∈ T, point a = x := by
  simp [colors]

@[simp] theorem point_mem_colors {T : Finset F} {a : F} : point a ∈ colors T ↔ a ∈ T := by
  simp [colors, point_injective.eq_iff]

@[simp] theorem colors_card (T : Finset F) : (colors T).card = T.card :=
  Finset.card_image_of_injective T point_injective

theorem graph_bipartite (T : Finset F) : (graph T).IsBipartite :=
  Haar.graph_bipartite (colors T)

variable [Fintype F]

def fullGraph : SimpleGraph ((F × F) × Bool) := graph (univ : Finset F)

instance fullGraph_decidable : DecidableRel (fullGraph (F := F)).Adj :=
  graph_decidable univ

theorem graph_le_full (T : Finset F) : graph T ≤ (fullGraph : SimpleGraph ((F × F) × Bool)) :=
  Haar.graph_mono (Finset.image_subset_image (Finset.subset_univ T))

theorem graph_degree (T : Finset F) (x : (F × F) × Bool) : (graph T).degree x = T.card := by
  calc
    (graph T).degree x = (Haar.graph (colors T)).degree x := by
      rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
      exact Fintype.card_congr (Equiv.refl _)
    _ = T.card := (HaarDegree.degree_eq_card (colors T) x).trans (colors_card T)

theorem fullGraph_degree (x : (F × F) × Bool) : fullGraph.degree x = Fintype.card F := by
  calc
    fullGraph.degree x = (graph (univ : Finset F)).degree x := by
      rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
      exact Fintype.card_congr (Equiv.refl _)
    _ = Fintype.card F := by simpa only [Finset.card_univ] using graph_degree (univ : Finset F) x

theorem fullGraph_bipartite : (fullGraph : SimpleGraph ((F × F) × Bool)).IsBipartite :=
  graph_bipartite univ

def canonical : (fullGraph : SimpleGraph ((F × F) × Bool)).EdgeLabeling F :=
  EdgeLabeling.mk
    (fun x y _ => if x.2 then x.1.1 - y.1.1 else y.1.1 - x.1.1)
    (by
      intro x y h
      rcases h with h | h <;> simp [h.1, h.2.1])

@[simp] theorem canonical_get_cross (X Y : F × F)
    (h : fullGraph.Adj (X, false) (Y, true)) :
    canonical.get (X, false) (Y, true) h = Y.1 - X.1 := rfl

theorem canonical_label_cross (a : F) (X Y : F × F) :
    (canonical.labelGraph a).Adj (X, false) (Y, true) ↔ Y - X = point a := by
  rw [EdgeLabeling.labelGraph_adj]
  change (∃ h : fullGraph.Adj (X, false) (Y, true), canonical.get _ _ h = a) ↔ _
  constructor
  · rintro ⟨h, hc⟩
    obtain ⟨b, _, hb⟩ := mem_colors.mp ((Haar.graph_cross _ _ _).mp h)
    have hba : b = a := by
      rw [canonical_get_cross] at hc
      have hb' := congrArg Prod.fst hb
      simpa [point, hc] using hb'
    simpa [hba] using hb.symm
  · intro h
    have hg : fullGraph.Adj (X, false) (Y, true) :=
      (Haar.graph_cross _ _ _).mpr (mem_colors.mpr ⟨a, mem_univ a, h.symm⟩)
    refine ⟨hg, ?_⟩
    simpa [point] using congrArg Prod.fst h

theorem canonical_label_same (a : F) (X Y : F × F) (b : Bool) :
    ¬ (canonical.labelGraph a).Adj (X, b) (Y, b) := by
  intro h
  exact Haar.graph_same _ _ _ b (EdgeLabeling.labelGraph_le canonical h)

theorem canonical_labelGraph (a : F) : canonical.labelGraph a = graph {a} := by
  ext ⟨X, b⟩ ⟨Y, c⟩
  cases b <;> cases c
  · simp [canonical_label_same, graph, Haar.graph_same]
  · simp [canonical_label_cross, graph, colors, Haar.graph_cross]
  · rw [SimpleGraph.adj_comm, canonical_label_cross, SimpleGraph.adj_comm]
    simp [graph, colors, Haar.graph_cross]
  · simp [canonical_label_same, graph, Haar.graph_same]

theorem canonical_full : KempeSwap104.FullColoring (canonical (F := F)) := by
  intro v a
  rw [canonical_labelGraph]
  obtain ⟨X, b⟩ := v
  cases b
  · refine ⟨(X + point a, true), ?_, ?_⟩
    · simp [graph, colors, Haar.graph_cross]
    · rintro ⟨Y, c⟩ h
      cases c
      · exact (Haar.graph_same _ _ _ false h).elim
      · have h' : Y - X = point a := by simpa [graph, colors, Haar.graph_cross] using h
        have hy : Y = X + point a := by rw [← h']; abel
        exact congrArg (fun P : F × F => (P, true)) hy
  · refine ⟨(X - point a, false), ?_, ?_⟩
    · apply SimpleGraph.Adj.symm
      apply (Haar.graph_cross _ _ _).mpr
      simp [colors]
    · rintro ⟨Y, c⟩ h
      cases c
      · have h' : X - Y = point a := by
          simpa [graph, colors, Haar.graph_cross] using h.symm
        have hy : Y = X - point a := by rw [← h']; abel
        exact congrArg (fun P : F × F => (P, false)) hy
      · exact (Haar.graph_same _ _ _ true h).elim

theorem canonical_colorSubgraph (T : Finset F) :
    KempeSwap104.colorSubgraph canonical T = graph T := by
  ext x y
  rw [KempeSwap104.colorSubgraph_adj]
  simp only [canonical_labelGraph]
  obtain ⟨X, b⟩ := x
  obtain ⟨Y, c⟩ := y
  cases b <;> cases c <;> simp [graph, Haar.graph, colors]
  all_goals
    constructor
    · rintro ⟨a, ha, h⟩
      exact ⟨a, ha, h.symm⟩
    · rintro ⟨a, ha, h⟩
      exact ⟨a, ha, h.symm⟩

omit [Field F] [Fintype F] in
private theorem exists_eq_triple (T : Finset F) (hne : T.Nonempty) (hc : T.card ≤ 3) :
    ∃ a b c : F, T = {a, b, c} := by
  have hp := hne.card_pos
  have h : T.card = 1 ∨ T.card = 2 ∨ T.card = 3 := by omega
  rcases h with h | h | h
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact ⟨a, a, a, by simp⟩
  · obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp h
    exact ⟨a, b, b, by simp⟩
  · obtain ⟨a, b, c, _, _, _, rfl⟩ := Finset.card_eq_three.mp h
    exact ⟨a, b, c, rfl⟩

variable [CharP F 3] [Algebra (ZMod 3) F]

omit [Fintype F] [CharP F 3] in
private theorem differenceSpan_triple (a b c : F) :
    HaarComponents104.differenceSpan (colors {a, b, c}) (point a) =
      Submodule.span (ZMod 3) ({point b - point a, point c - point a} : Set (F × F)) := by
  unfold HaarComponents104.differenceSpan
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨s, hs, rfl⟩
    obtain ⟨d, hd, rfl⟩ := mem_colors.mp hs
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · simp
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Submodule.subset_span ⟨point b, point_mem_colors.mpr (by simp), rfl⟩
    · exact Submodule.subset_span ⟨point c, point_mem_colors.mpr (by simp), rfl⟩

private theorem triple_cross_induced (a b c : F) (X Y : F × F)
    (hr : (graph {a, b, c}).Reachable (X, false) (Y, true))
    (he : fullGraph.Adj (X, false) (Y, true)) :
    (graph {a, b, c}).Adj (X, false) (Y, true) := by
  have ha : point a ∈ colors {a, b, c} := by simp
  have hh := (HaarComponents104.reachable_iff_mem_differenceSpan
    (colors {a, b, c}) ha X Y true).mp hr
  obtain ⟨z, _, hz⟩ := mem_colors.mp ((Haar.graph_cross _ _ _).mp he)
  simp only [ite_true] at hh
  rw [← hz, differenceSpan_triple] at hh
  have hm := point_span_pair a b c z hh
  apply (Haar.graph_cross _ _ _).mpr
  exact mem_colors.mpr ⟨z, by simpa using hm, hz⟩

theorem three_color_component_induced (T : Finset F) (hT : T.Nonempty) (hcard : T.card ≤ 3)
    {u v : (F × F) × Bool} (hreach : (graph T).Reachable u v)
    (hedge : fullGraph.Adj u v) : (graph T).Adj u v := by
  obtain ⟨a, b, c, rfl⟩ := exists_eq_triple T hT hcard
  obtain ⟨X, d⟩ := u
  obtain ⟨Y, e⟩ := v
  cases d <;> cases e
  · exact (Haar.graph_same _ _ _ false hedge).elim
  · exact triple_cross_induced a b c X Y hreach hedge
  · exact (triple_cross_induced a b c Y X hreach.symm hedge.symm).symm
  · exact (Haar.graph_same _ _ _ true hedge).elim

theorem differenceSpan_full_zero :
    HaarComponents104.differenceSpan (colors (univ : Finset F)) (point (0 : F)) = ⊤ := by
  have h0 : point (0 : F) = (0 : F × F) := by ext <;> simp [point]
  rw [HaarComponents104.differenceSpan, h0]
  simpa [colors] using
    (span_range_point_eq_top (F := F))

theorem fullGraph_connected : (fullGraph : SimpleGraph ((F × F) × Bool)).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨(0, false), ?_⟩
  rintro ⟨Y, b⟩
  apply (HaarComponents104.reachable_iff_mem_differenceSpan
    (colors (univ : Finset F))
    (point_mem_colors.mpr (mem_univ (0 : F))) 0 Y b).mpr
  rw [differenceSpan_full_zero]
  exact Submodule.mem_top

omit [Algebra (ZMod 3) F] in
theorem common_right_unique (X W Y Z : F × F) (hne : X ≠ W)
    (hXY : fullGraph.Adj (X, false) (Y, true))
    (hXZ : fullGraph.Adj (X, false) (Z, true))
    (hWY : fullGraph.Adj (W, false) (Y, true))
    (hWZ : fullGraph.Adj (W, false) (Z, true)) : Y = Z := by
  obtain ⟨a, _, ha⟩ := mem_colors.mp ((Haar.graph_cross _ _ _).mp hXY)
  obtain ⟨b, _, hb⟩ := mem_colors.mp ((Haar.graph_cross _ _ _).mp hXZ)
  obtain ⟨c, _, hc⟩ := mem_colors.mp ((Haar.graph_cross _ _ _).mp hWY)
  obtain ⟨d, _, hd⟩ := mem_colors.mp ((Haar.graph_cross _ _ _).mp hWZ)
  have hsum : point a + point d = point b + point c := by rw [ha, hb, hc, hd]; abel
  rcases point_pair_sum hsum with ⟨hab, _⟩ | ⟨hac, _⟩
  · rw [hab] at ha
    exact sub_left_injective (ha.symm.trans hb)
  · rw [hac] at ha
    exact (hne (sub_right_injective (ha.symm.trans hc))).elim

omit [Algebra (ZMod 3) F] in
theorem common_left_unique (Y Z X W : F × F) (hne : Y ≠ Z)
    (hXY : fullGraph.Adj (X, false) (Y, true))
    (hXZ : fullGraph.Adj (X, false) (Z, true))
    (hWY : fullGraph.Adj (W, false) (Y, true))
    (hWZ : fullGraph.Adj (W, false) (Z, true)) : X = W := by
  by_contra hn
  exact hne (common_right_unique X W Y Z hn hXY hXZ hWY hWZ)

omit [Algebra (ZMod 3) F] in
theorem common_neighbors_unique (x w y z : (F × F) × Bool) (hne : x ≠ w)
    (hxy : fullGraph.Adj x y) (hxz : fullGraph.Adj x z)
    (hwy : fullGraph.Adj w y) (hwz : fullGraph.Adj w z) : y = z := by
  obtain ⟨X, b⟩ := x
  obtain ⟨W, c⟩ := w
  obtain ⟨Y, d⟩ := y
  obtain ⟨Z, e⟩ := z
  cases b <;> cases c <;> cases d <;> cases e
  all_goals try exact (Haar.graph_same _ _ _ _ hxy).elim
  all_goals try exact (Haar.graph_same _ _ _ _ hxz).elim
  all_goals try exact (Haar.graph_same _ _ _ _ hwy).elim
  · exact Prod.ext (common_right_unique X W Y Z
      (fun h => hne (Prod.ext h rfl)) hxy hxz hwy hwz) rfl
  · exact Prod.ext (common_left_unique X W Y Z
      (fun h => hne (Prod.ext h rfl)) hxy.symm hwy.symm hxz.symm hwz.symm) rfl

omit [Algebra (ZMod 3) F] in
theorem fullGraph_no_four_cycle {u : (F × F) × Bool}
    (p : fullGraph.Walk u u) (hp : p.IsCycle) : p.length ≠ 4 := by
  intro hl
  have h02 : p.getVert 0 ≠ p.getVert 2 := by
    intro h
    have hi := hp.getVert_injOn' (by simp [hl]) (by simp [hl]) h
    omega
  have h13 : p.getVert 1 ≠ p.getVert 3 := by
    intro h
    have hi := hp.getVert_injOn' (by simp [hl]) (by simp [hl]) h
    omega
  apply h13
  apply common_neighbors_unique (p.getVert 0) (p.getVert 2) _ _ h02
  · exact p.adj_getVert_succ (by omega : 0 < p.length)
  · have h30 := p.adj_getVert_succ (by omega : 3 < p.length)
    have h40 : p.getVert 4 = p.getVert 0 := by rw [← hl, p.getVert_length, p.getVert_zero]
    exact h40 ▸ h30.symm
  · exact (p.adj_getVert_succ (by omega : 1 < p.length)).symm
  · exact p.adj_getVert_succ (by omega : 2 < p.length)

end Erdos585.Parabola104
