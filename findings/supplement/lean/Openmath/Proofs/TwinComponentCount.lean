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
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Component count after a reachability-preserving merge

This helper permits edge deletions. Its premise is preservation of every old
reachability relation, together with one newly connected pair of components.
The quotient map is surjective and not injective, so its finite cardinal drops.
It is infrastructure for the actual twin-cycle construction, not a forcing
statement by itself.
-/

namespace Erdos585.TwinComponentCount

open SimpleGraph

/-- A merge that preserves all old connectivity strictly lowers component count. -/
theorem card_lt_of_reachable_merge {V : Type*} [Finite V]
    (G H : SimpleGraph V)
    (hpres : ∀ u v, G.Reachable u v → H.Reachable u v)
    {u v : V} (hold : ¬ G.Reachable u v) (hnew : H.Reachable u v) :
    Nat.card H.ConnectedComponent < Nat.card G.ConnectedComponent := by
  classical
  let f : G.ConnectedComponent → H.ConnectedComponent :=
    Quot.lift H.connectedComponentMk
      (fun a b h => ConnectedComponent.sound (hpres a b h))
  have hsurj : Function.Surjective f := by
    intro c
    induction c using ConnectedComponent.ind with
    | _ w => exact ⟨G.connectedComponentMk w, rfl⟩
  have hninj : ¬ Function.Injective f := by
    intro hinj
    apply hold
    apply ConnectedComponent.exact
    apply hinj
    exact ConnectedComponent.sound hnew
  let := Fintype.ofFinite G.ConnectedComponent
  let := Fintype.ofFinite H.ConnectedComponent
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_surjective_not_injective f hsurj hninj

end Erdos585.TwinComponentCount
