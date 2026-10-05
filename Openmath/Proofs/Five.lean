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
import Openmath.Proofs.Counting
import Openmath.Proofs.TopFive

/-!
# Erdős 585: the small cases

For $n \leq 4$ the extremal number is $\binom{n}{2}$, and for $n = 5$ it is $9$.
-/

open SimpleGraph Finset

namespace Erdos585

/-- $K_5$ minus one edge has nine edges. -/
lemma ncard_edgeSet_top_deleteEdge_five :
    ((⊤ : SimpleGraph (Fin 5)).deleteEdges {s(0, 1)}).edgeSet.ncard = 9 := by
  classical
  rw [← coe_edgeFinset, Set.ncard_coe_finset]
  decide

/-- $9$ is attained on five vertices. -/
theorem nine_mem_edgeCounts_five : 9 ∈ edgeCounts 5 :=
  ⟨(⊤ : SimpleGraph (Fin 5)).deleteEdges {s(0, 1)}, not_hasPair_top_deleteEdge_five,
    ncard_edgeSet_top_deleteEdge_five⟩

/-- The extremal number for $n = 5$ is $9$. -/
theorem five : IsGreatest (edgeCounts 5) 9 :=
  ⟨nine_mem_edgeCounts_five, edgeCounts_five_upper⟩

/-- For $n \leq 4$ the extremal number is $\binom{n}{2}$. -/
theorem le_four (n : ℕ) (hn : n ≤ 4) : IsGreatest (edgeCounts n) (n.choose 2) :=
  le_four' n hn

end Erdos585
