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
import Openmath.Proofs.QB4.Reductions

/-!
# QB(4): C1 holds, and the pair form of QB(4)

* `quartic_of_isC1`: every C1 instance has a quartic subgraph. The proof is a strong induction on
  the size `s`. A quartic-free instance of size `s`, with C1 holding below `s`, is sparse
  (`sparse_of_minimal`), and a sparse instance has a quartic subgraph (`quartic_of_sparse`, which
  combines the 4-factor criterion with the petal argument of `sparse_core`).
* `quartic_of_isE4'`: E4 holds at every size.
* `quartic_of_dense`, QB(4) for pairs: a pair with degrees at most six, at least two
  vertices and at least `3n - 4` edges has a quartic subgraph.
-/

open Finset

namespace Erdos585.QB4

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **C1 holds.** Every C1 instance has a quartic subgraph. -/
theorem quartic_of_isC1 {U W : Finset V} {s : ℕ} (h : IsC1 G U W s) : Quartic G U W := by
  induction s using Nat.strong_induction_on generalizing U W with
  | _ s ih =>
    by_contra hq
    have hsp := sparse_of_minimal h (fun s' hs' U' W' h' => ih s' hs' h') hq
    have hU : U.Nonempty := card_pos.1 (by rw [h.cardU]; exact h.pos)
    exact hq (quartic_of_sparse (by rw [h.cardW, h.cardU]) hU h.degU h.degW h.defU hsp)

/-- **E4 holds.** Every E4 instance has a quartic subgraph. -/
theorem quartic_of_isE4' {P Q : Finset V} {a : ℕ} (h : IsE4 G P Q a) : Quartic G P Q :=
  quartic_of_isE4 h fun _ _ _ _ h' => quartic_of_isC1 h'

/-- **QB(4), pair form.** A pair `(U, W)` with degrees at most six, `n ≥ 2`
vertices and at least `3n - 4` adjacent pairs has a quartic subgraph. Then `g(U, W) ≤ 8`, so the
pair is an E4 instance or a C1 instance in one of the two orientations (`small_gv_cases`). -/
theorem quartic_of_dense {U W : Finset V} (hdU : ∀ u ∈ U, dg G W u ≤ 6)
    (hdW : ∀ w ∈ W, dg G U w ≤ 6) (hn : 2 ≤ #U + #W) (he : 3 * (#U + #W) ≤ ec G U W + 4) :
    Quartic G U W := by
  have hg : gv G U W ≤ 8 := by
    unfold gv
    omega
  rcases small_gv_cases hdU hdW hn hg with hE | hC | hC
  · exact quartic_of_isE4' hE
  · exact quartic_of_isC1 hC
  · exact (quartic_of_isC1 hC).swap

end Erdos585.QB4
