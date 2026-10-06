/-
Copyright 2026 Robert Huynh.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Openmath.Proofs.QB5.C2Hub
import Openmath.Proofs.QB5.C2TwoBlock
import Openmath.Proofs.QB5.E5

/-!
# QB(5): the top of the proof

The case analysis that proves QB(5), the statement of `Erdos585.qb5` (`Statement.lean`), in the pair
setting of `Defs.lean`, whose module docstring defines the labels (C1, E4, C2, E5, sparse, quartic
subgraph). The induction covers every pair with `g ≤ 10`.

* `quartic_of_sparse_c2`: a sparse C2 instance has a quartic subgraph. The deficiency `D(U) = 2`
  sits on one `U`-vertex of degree four (`quartic_of_sparse_c2_hub`, `C2Hub.lean`) or on two of
  degree five (`quartic_of_sparse_c2_ports`, `C2TwoBlock.lean`).
* `quartic_of_gv_le_ten`: the pair form of QB(5), by strong induction on `|X| + |Y|`. In the
  induction step, a pair with no quartic subgraph, `g ≤ 10` and at least three vertices is sparse
  (`sparse5_of_minimal`) and is an E4, C1, E5 or C2 instance (`small_gv_cases5`). QB4 closes E4
  and C1 at every size (`quartic_of_isE4'`, `quartic_of_isC1`), `quartic_of_sparse_e5`
  (`E5.lean`) closes E5, and `quartic_of_sparse_c2` closes C2.
* `quartic_of_dense5`: a pair with degrees at most six, `n ≥ 3` vertices and at least `3n - 5`
  adjacent pairs has `g ≤ 10`, so it has a quartic subgraph.
-/

open Finset

namespace Erdos585.QB5

open QB4

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### C2, and the induction -/

/-- **A sparse C2 instance is never quartic-free.** Since `D(U) = 2`, either some `U`-vertex has
degree four (`quartic_of_sparse_c2_hub`), or every `U`-vertex has degree at least five
(`quartic_of_sparse_c2_ports`). -/
theorem quartic_of_sparse_c2 {U W : Finset V} {s : ℕ} (h : IsC2 G U W s)
    (hsp : Sparse5 G U W) : Quartic G U W := by
  by_cases h4 : ∃ u0 ∈ U, dg G W u0 = 4
  · obtain ⟨u0, hu0, hd⟩ := h4
    exact quartic_of_sparse_c2_hub h hsp hu0 hd
  · refine quartic_of_sparse_c2_ports h hsp fun u hu => ?_
    have hle := single_le_sum (f := fun u => 6 - (dg G W u : ℤ))
      (fun u hu => by have := h.degU u hu; omega) hu
    change 6 - (dg G W u : ℤ) ≤ df G W U at hle
    have hne : dg G W u ≠ 4 := fun h' => h4 ⟨u, hu, h'⟩
    have h2 := h.defU
    omega

/-- **QB(5), pair form, by strong induction on `|X| + |Y|`**: a pair with degrees at most six, at
least three vertices and `g ≤ 10` has a quartic subgraph. A counterexample is sparse, because the
smaller pairs with `g ≤ 10` have quartic subgraphs, and it is an E4, C1, E5 or C2 instance in some
orientation. -/
theorem quartic_of_gv_le_ten {X Y : Finset V} (hdX : ∀ x ∈ X, dg G Y x ≤ 6)
    (hdY : ∀ y ∈ Y, dg G X y ≤ 6) (h3 : 3 ≤ #X + #Y) (hg : gv G X Y ≤ 10) : Quartic G X Y := by
  generalize hn : #X + #Y = n
  induction n using Nat.strong_induction_on generalizing X Y with
  | _ n ih =>
    by_contra hq
    have hsp : Sparse5 G X Y := sparse5_of_minimal (fun X' hX' Y' hY' h3' hlt hg' =>
      ih (#X' + #Y') (hn ▸ hlt) (fun x hx => (dg_mono hY' x).trans (hdX x (hX' hx)))
        (fun y hy => (dg_mono hX' y).trans (hdY y (hY' hy))) h3' hg' rfl) hq
    rcases small_gv_cases5 hdX hdY h3 hg with hE | hC | hC | hE | hC | hC
    · exact hq (quartic_of_isE4' hE)
    · exact hq (quartic_of_isC1 hC)
    · exact hq (quartic_of_isC1 hC).swap
    · exact hq (quartic_of_sparse_e5 hE hsp)
    · exact hq (quartic_of_sparse_c2 hC hsp)
    · exact hq (quartic_of_sparse_c2 hC hsp.swap).swap

/-- **QB(5), pair form.** A pair `(U, W)` with degrees at most six, `n ≥ 3` vertices and at least
`3n - 5` adjacent pairs has a quartic subgraph, since then `g(U, W) ≤ 10`. -/
theorem quartic_of_dense5 {U W : Finset V} (hdU : ∀ u ∈ U, dg G W u ≤ 6)
    (hdW : ∀ w ∈ W, dg G U w ≤ 6) (hn : 3 ≤ #U + #W) (he : 3 * (#U + #W) ≤ ec G U W + 5) :
    Quartic G U W :=
  quartic_of_gv_le_ten hdU hdW hn (by unfold gv; omega)

end Erdos585.QB5
