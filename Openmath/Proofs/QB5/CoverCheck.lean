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
import Mathlib.Data.Nat.Bitwise

/-!
# QB(5): the checker behind `refined_cover` (definitions only)

`refined_cover` (`Cover.lean`), a step in the proof of QB(5) (`Erdos585.qb5`, `Statement.lean`),
is a statement about seven edges `0, …, 6`, the *cut edges*, each with one end on the `A` side and
one end on the `D` side. Up to renaming the ends it has finitely many cases: it depends only on
which edges share an end on each side and on which ends lie in its sets `L_A` and `L_D`. This file
defines a Boolean checker for it; the files `CoverCheck1.lean` to `CoverCheck3.lean` run the
checker in the kernel (`decide +kernel`), and `Cover.lean` proves that a successful run implies
`refined_cover`. The file holds definitions only, so a change to the proofs in `Cover.lean` does
not force the kernel runs to be repeated.

Encoding. The ends on one side are recorded by a *code* `g`: the number whose base-8 digit `i`
(`dig g i`) is the least edge with the same end as edge `i`, the *representative* of that end.
Write `c` for the number of cut edges at an end. A set `L` of ends is a 7-bit mask over the
representatives, and an *`L`-end* is an end in `L`. The 35 four-sets (sets of four cut edges) are
numbered by `k`; `Mk k` is the `k`-th one as a 7-bit mask. A four-set `M` *misses* an end if no
edge of `M` is at that end, and an edge is *counted* for `M` if its end is outside `L` or has
three cut edges, and every cut edge at that end lies in `M`. For a side and `L`, `good g l` is the
35-bit mask of the four-sets `M` that pass the following test, computed for all 35 four-sets at
once:

* `u1`, `u2` mark the `M` that miss at least one, respectively two, `L`-ends;
* `f1`, `f2`, `f3` mark the `M` with at least one, two, three counted edges;
* `M` passes unless it misses two `L`-ends, or misses one and has at least three counted edges.

`goodSide_of_testBit` (`Cover.lean`) proves that a four-set that passes on a side satisfies
`GoodSide` (`Defs.lean`) on that side.

`checkD d` checks one side `d` (the `D` side) against the eight canonical codes of the `A` side
(codes in which the edges at each end are consecutive and the number of edges per end does not
increase); `checkPre` and `checkPre3` run it over ranges of codes. All arithmetic uses the `Nat`
primitives that the kernel evaluates directly.
-/

namespace Erdos585.QB5.CoverCheck

/-- `allBelow n f` is `true` when `f i` is `true` for every `i < n`. -/
def allBelow : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, f => f n && allBelow n f

/-- Bit `i` of `m`, with the kernel's `Nat` primitives. -/
def bitB (m i : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1

/-- Base-8 digit `i` of a side code: the representative of the end of edge `i`. -/
def dig (g i : ℕ) : ℕ := Nat.land (Nat.shiftRight g (Nat.mul 3 i)) 7

/-- The mask of the 35 four-sets of edges, `2 ^ 35 - 1`. -/
def ALL : ℕ := 34359738367

/-- The 35 four-sets of edges, in increasing order, as 7-bit masks packed in base `2 ^ 7`. -/
def MPACK : ℕ :=
  53408810645051156694119421735846128017683049684649645018245659832512596879

/-- For each edge `e`, the 35-bit mask of the four-sets that contain `e`, packed in base
`2 ^ 35`. -/
def CPACK : ℕ :=
  56539052154658863432450759460028219599163833450860406831079970625594037999

/-- For each edge `e`, the 35-bit mask of the four-sets that do not contain `e`, packed in base
`2 ^ 35`. -/
def NCPACK : ℕ :=
  53918249435114214760563745172907315651249159399828811427815769794832

/-- The `k`-th four-set of edges, as a 7-bit mask. -/
def Mk (k : ℕ) : ℕ := Nat.land (Nat.shiftRight MPACK (Nat.mul 7 k)) 127

/-- The four-sets that contain edge `e`, as a 35-bit mask. -/
def cM (e : ℕ) : ℕ := Nat.land (Nat.shiftRight CPACK (Nat.mul 35 e)) ALL

/-- The four-sets that do not contain edge `e`, as a 35-bit mask. -/
def ncM (e : ℕ) : ℕ := Nat.land (Nat.shiftRight NCPACK (Nat.mul 35 e)) ALL

/-- The mask of the `i < n` with `p i`. -/
def maskOf (p : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.lor (maskOf p n) (cond (p n) (Nat.shiftLeft 1 n) 0)

/-- The number of edges `j < n` whose representative is `v`. -/
def cnt (g v : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => Nat.add (cnt g v j) (cond (Nat.beq (dig g j) v) 1 0)

/-- The number of cut edges at the end of edge `i`. -/
def size (g i : ℕ) : ℕ := cnt g (dig g i) 7

/-- The AND of the masks `t j` over the edges `j < n` whose representative is `v`. -/
def andBlk (g v : ℕ) (t : ℕ → ℕ) : ℕ → ℕ
  | 0 => ALL
  | j + 1 => cond (Nat.beq (dig g j) v) (Nat.land (t j) (andBlk g v t j)) (andBlk g v t j)

/-- The four-sets that miss every edge at the end with representative `r`. -/
def missR (g r : ℕ) : ℕ := andBlk g r ncM 7

/-- The four-sets that contain every edge at the end with representative `r`. -/
def inR (g r : ℕ) : ℕ := andBlk g r cM 7

/-- `r` is a representative and its end lies in `L` (mask `l`). -/
def isLRep (g l r : ℕ) : Bool := Nat.beq (dig g r) r && bitB l r

/-- The four-sets that miss at least one `L`-end among the representatives `r < n`. -/
def u1 (g l : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => cond (isLRep g l r) (Nat.lor (u1 g l r) (missR g r)) (u1 g l r)

/-- The four-sets that miss at least two `L`-ends among the representatives `r < n`. -/
def u2 (g l : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 =>
    cond (isLRep g l r) (Nat.lor (u2 g l r) (Nat.land (u1 g l r) (missR g r))) (u2 g l r)

/-- The four-sets `M` for which edge `j` is counted: the end of `j` is outside `L` or has three
cut edges, and all its cut edges lie in `M`. -/
def zM (g l j : ℕ) : ℕ :=
  cond (!bitB l (dig g j) || Nat.beq (size g j) 3) (inR g (dig g j)) 0

/-- The four-sets with at least one counted edge among the edges `j < n`. -/
def f1 (g l : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => Nat.lor (f1 g l j) (zM g l j)

/-- The four-sets with at least two counted edges among the edges `j < n`. -/
def f2 (g l : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => Nat.lor (f2 g l j) (Nat.land (f1 g l j) (zM g l j))

/-- The four-sets with at least three counted edges among the edges `j < n`. -/
def f3 (g l : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => Nat.lor (f3 g l j) (Nat.land (f2 g l j) (zM g l j))

/-- The four-sets that are good on the side `g` with `L`-mask `l`: neither two missed `L`-ends,
nor one missed `L`-end together with at least three counted edges. -/
def good (g l : ℕ) : ℕ :=
  Nat.xor ALL (Nat.land ALL (Nat.lor (u2 g l 7) (Nat.land (u1 g l 7) (f3 g l 7))))

/-- The representatives of the side `g`, as a 7-bit mask. -/
def repMask (g : ℕ) : ℕ := maskOf (fun r => Nat.beq (dig g r) r) 7

/-- `Σ_{r ∈ L, r < n} (3 - c_r)` for the `L`-mask `l`, where `c_r = size g r` is the number of
cut edges at the end of `r`. -/
def budget (g l : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => Nat.add (budget g l r) (cond (bitB l r) (Nat.sub 3 (size g r)) 0)

/-- `l` is an admissible `L`-mask: its bits are representatives, it contains the representative
of every end with three cut edges, and `Σ_L (3 - c) ≤ 5`. -/
def admissible (g l : ℕ) : Bool :=
  Nat.beq (Nat.land l (Nat.xor 127 (repMask g))) 0 &&
    allBelow 7 (fun r => !(Nat.beq (dig g r) r && Nat.beq (size g r) 3) || bitB l r) &&
    Nat.ble (budget g l 7) 5

/-- The good masks of the admissible `l < n`. -/
def masksAux (g : ℕ) : ℕ → List ℕ
  | 0 => []
  | l + 1 => cond (admissible g l) (good g l :: masksAux g l) (masksAux g l)

/-- The good masks of all admissible `L` of the side `g`. -/
def masks (g : ℕ) : List ℕ := masksAux g 128

/-- Every good mask in `xs` meets every good mask in `ys`. -/
def pairOK (xs ys : List ℕ) : Bool :=
  xs.all fun x => ys.all fun y => !Nat.beq (Nat.land x y) 0

/-- The codes `a` and `d` of the two sides are compatible: no two edges have the same end on both
sides (the cut is simple). -/
def compat (a d : ℕ) : Bool :=
  allBelow 7 fun i => allBelow i fun j =>
    !(Nat.beq (dig a j) (dig a i) && Nat.beq (dig d j) (dig d i))

/-- `d` is a side: its digits are representatives, and every end has at most three cut edges. -/
def validSide (d : ℕ) : Bool :=
  allBelow 7 fun i => Nat.beq (dig d (dig d i)) (dig d i) && Nat.ble (size d i) 3

/-- The eight canonical codes of the `A` side: the edges at each end are consecutive, and the
numbers of edges at the ends, in order from edge 0, are at most three and non-increasing (`3+3+1`,
`3+2+2`, `3+2+1+1`, `3+1+1+1+1`, `2+2+2+1`, `2+2+1+1+1`, `2+1+1+1+1+1`, `1+1+1+1+1+1+1`). -/
def canonA : List ℕ := [1684992, 1488384, 1750528, 1754624, 1721472, 1754240, 1754752, 1754760]

/-- A side code is canonical: it passes `validSide`, the edges at each end are consecutive, and
the number of cut edges at the end of edge `i` does not increase with `i`. -/
def canonical (a : ℕ) : Bool :=
  validSide a &&
    allBelow 6 (fun i => Nat.beq (dig a (i + 1)) (i + 1) || Nat.beq (dig a (i + 1)) (dig a i)) &&
    allBelow 6 (fun i => Nat.ble (size a (i + 1)) (size a i))

/-- The check for one `D` side: if it is a side, then for every canonical `A` side compatible
with it, every good mask of `A` meets every good mask of `D`. -/
def checkD (d : ℕ) : Bool :=
  !validSide d || canonA.all fun a => !compat a d || pairOK (masks a) (masks d)

/-- The side code with digits `0, d1, …, d6`. -/
def mkCode (d1 d2 d3 d4 d5 d6 : ℕ) : ℕ :=
  Nat.add (Nat.mul d1 8) (Nat.add (Nat.mul d2 64) (Nat.add (Nat.mul d3 512)
    (Nat.add (Nat.mul d4 4096) (Nat.add (Nat.mul d5 32768) (Nat.mul d6 262144)))))

/-- `checkD` on every code with digits `0, d1, d2, d3` and `d4 ≤ 4`, `d5 ≤ 5`, `d6 ≤ 6`. -/
def checkPre3 (d1 d2 d3 : ℕ) : Bool :=
  allBelow 5 fun d4 => allBelow 6 fun d5 => allBelow 7 fun d6 =>
    checkD (mkCode d1 d2 d3 d4 d5 d6)

/-- `checkD` on every code with digits `0, d1, d2` and `d3 ≤ 3`, …, `d6 ≤ 6`. -/
def checkPre (d1 d2 : ℕ) : Bool := allBelow 4 fun d3 => checkPre3 d1 d2 d3

/-- Every canonical code with digits `dᵢ ≤ i` is one of the eight in `canonA`. -/
def checkCanon : Bool :=
  allBelow 2 fun d1 => allBelow 3 fun d2 => allBelow 4 fun d3 => allBelow 5 fun d4 =>
    allBelow 6 fun d5 => allBelow 7 fun d6 =>
      !canonical (mkCode d1 d2 d3 d4 d5 d6) ||
        canonA.any fun a => Nat.beq a (mkCode d1 d2 d3 d4 d5 d6)

end Erdos585.QB5.CoverCheck
