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
import FormalConjecturesUtil
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

/-!+# A finite obstruction to replacing connectivity with four-cut balance

Two directed Hamilton cycles on seven vertices admit a degree-balanced coloring
that separates two marked arcs and crosses every four-arc cut twice. No coloring
into two directed Hamilton cycles separates those arcs. This finite quotient is
used by the local bipartite construction; that lift is a separate proof obligation.
-/

namespace Erdos585.DirectedState
open Finset Function
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def first : Fin 7 → Fin 7 := ![1, 2, 3, 4, 5, 6, 0]
def second : Fin 7 → Fin 7 := ![2, 5, 6, 0, 1, 3, 4]

def red (b : Fin 7 → Bool) (v : Fin 7) : Fin 7 :=
  if b v then second v else first v

def blue (b : Fin 7 → Bool) (v : Fin 7) : Fin 7 :=
  if b v then first v else second v

/-- Each vertex is reached within one traversal of seven iterates. -/
def Hamilton (f : Fin 7 → Fin 7) : Prop :=
  ∀ u v, ∃ k : Fin 7, f^[k.val] u = v

instance (f : Fin 7 → Fin 7) : Decidable (Hamilton f) :=
  inferInstanceAs (Decidable (∀ u v, ∃ k : Fin 7, f^[k.val] u = v))

def arcs : Finset (Fin 7 × Fin 7) :=
  univ.image (fun v => (v, first v)) ∪ univ.image (fun v => (v, second v))

def crosses (S : Finset (Fin 7)) (E : Finset (Fin 7 × Fin 7)) :
    Finset (Fin 7 × Fin 7) := E.filter fun e => (e.1 ∈ S) != (e.2 ∈ S)

def redArcs (b : Fin 7 → Bool) : Finset (Fin 7 × Fin 7) :=
  univ.image fun v => (v, red b v)

def blueArcs (b : Fin 7 → Bool) : Finset (Fin 7 × Fin 7) :=
  univ.image fun v => (v, blue b v)

def relaxed : Fin 7 → Bool := ![false, false, true, false, false, true, false]

theorem planted : Hamilton first ∧ Hamilton second := by decide

/-- The marked arcs are first 2 and first 6. -/
theorem forced : ∀ b : Fin 7 → Bool,
    Hamilton (red b) → Hamilton (blue b) → b 2 = b 6 := by decide

theorem relaxed_permutations :
    Bijective (red relaxed) ∧ Bijective (blue relaxed) := by decide

theorem relaxed_separates : relaxed 2 ≠ relaxed 6 := by decide

theorem relaxed_cuts : ∀ S : Finset (Fin 7),
    (crosses S arcs).card = 4 →
      (crosses S (redArcs relaxed)).card = 2 ∧
      (crosses S (blueArcs relaxed)).card = 2 := by decide

theorem relaxed_not_hamilton :
    ¬ Hamilton (red relaxed) ∧ ¬ Hamilton (blue relaxed) := by decide

/-- Two particular six-arc cuts recover the connectivity information lost above. -/
theorem forced_of_two_six_cuts : ∀ b : Fin 7 → Bool,
    Bijective (red b) → Bijective (blue b) →
    2 ≤ (crosses {3, 4, 5} (redArcs b)).card →
    2 ≤ (crosses {3, 4, 5} (blueArcs b)).card →
    2 ≤ (crosses {4, 5, 6} (redArcs b)).card →
    2 ≤ (crosses {4, 5, 6} (blueArcs b)).card → b 2 = b 6 := by decide

theorem larger_cuts :
    (crosses {3, 4, 5} arcs).card = 6 ∧ (crosses {4, 5, 6} arcs).card = 6 := by decide

/-- The quotient obstruction is nonvacuous, and the relaxation passes every four-cut test. -/
theorem counterexample :
    Hamilton first ∧ Hamilton second ∧
    (∀ b : Fin 7 → Bool, Hamilton (red b) → Hamilton (blue b) → b 2 = b 6) ∧
    Bijective (red relaxed) ∧ Bijective (blue relaxed) ∧
    relaxed 2 ≠ relaxed 6 ∧
    (∀ S : Finset (Fin 7), (crosses S arcs).card = 4 →
      (crosses S (redArcs relaxed)).card = 2 ∧
      (crosses S (blueArcs relaxed)).card = 2) ∧
    ¬ Hamilton (red relaxed) ∧ ¬ Hamilton (blue relaxed) :=
  ⟨planted.1, planted.2, forced, relaxed_permutations.1, relaxed_permutations.2,
    relaxed_separates, relaxed_cuts, relaxed_not_hamilton⟩

end Erdos585.DirectedState
