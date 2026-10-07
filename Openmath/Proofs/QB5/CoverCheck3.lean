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
import Openmath.Proofs.QB5.CoverCheck

/-!
# QB(5): kernel runs of the checker behind `refined_cover`, part 3

`decide +kernel` evaluation (kernel reduction only) of the checker of `CoverCheck.lean`, the
finite check behind `refined_cover` in the proof of QB(5) (`Erdos585.qb5`), on the `D` side codes
with first digits `0, 1, 2, 3`: the `D` sides whose first four edges have four different ends.
For each of them, `checkD` says that for every compatible canonical `A` side and every admissible
`L_A` and `L_D`, some four of the seven cut edges pass the test of `good` on both sides. This is
the largest single prefix: no other run checks as many valid `D` side codes (`validSide`).
-/

namespace Erdos585.QB5.CoverCheck

/-- The checker on the `D` side codes with first digits `0, 1, 2, 3` (kernel evaluation). -/
theorem checkPre3_1_2_3 : checkPre3 1 2 3 = true := by decide +kernel

end Erdos585.QB5.CoverCheck
