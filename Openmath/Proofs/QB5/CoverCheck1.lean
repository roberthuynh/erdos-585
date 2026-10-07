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
# QB(5): kernel runs of the checker behind `refined_cover`, part 1

`decide +kernel` evaluations (kernel reduction only) of the checker of `CoverCheck.lean`, the
finite check behind `refined_cover` in the proof of QB(5) (`Erdos585.qb5`). In words, `checkD d`
says: if `d` is a valid code of the `D` side (`validSide`), then for every canonical `A` side
compatible with it and every admissible `L_A` and `L_D`, some four of the seven cut edges pass the
test of `good` on both sides. This file checks that the list `canonA` of canonical `A` sides is
complete (`checkCanon_eq`), and that `checkD` holds on every `D` side code whose digits
`(d1, d2)` at edges 1 and 2 are `(0, 0)`, `(0, 1)`, `(0, 2)`, `(1, 0)` or `(1, 1)` (digit 0 is
always 0). The remaining prefix `(1, 2)` is split between `CoverCheck2.lean` and
`CoverCheck3.lean`.
-/

namespace Erdos585.QB5.CoverCheck

/-- Every canonical side code is one of the eight codes of `canonA` (kernel evaluation). -/
theorem checkCanon_eq : checkCanon = true := by decide +kernel

/-- The checker on the `D` side codes with first digits `0, 0, 0` (kernel evaluation). -/
theorem checkPre_0_0 : checkPre 0 0 = true := by decide +kernel

/-- The checker on the `D` side codes with first digits `0, 0, 1` (kernel evaluation). -/
theorem checkPre_0_1 : checkPre 0 1 = true := by decide +kernel

/-- The checker on the `D` side codes with first digits `0, 0, 2` (kernel evaluation). -/
theorem checkPre_0_2 : checkPre 0 2 = true := by decide +kernel

/-- The checker on the `D` side codes with first digits `0, 1, 0` (kernel evaluation). -/
theorem checkPre_1_0 : checkPre 1 0 = true := by decide +kernel

/-- The checker on the `D` side codes with first digits `0, 1, 1` (kernel evaluation). -/
theorem checkPre_1_1 : checkPre 1 1 = true := by decide +kernel

end Erdos585.QB5.CoverCheck
