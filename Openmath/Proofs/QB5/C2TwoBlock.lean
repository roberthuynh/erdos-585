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
import Openmath.Proofs.QB5.C2Petals

/-!
# QB(5), C2 with two deficient `U`-vertices: a maximal `W`-small 2-block and the count

Part of the proof of QB(5) (`Erdos585.qb5`), with `C2Petals.lean`, whose notation and families
`Fam g k` this file uses. Let `(U, W)` be a sparse C2 instance whose deficiency `D_U = 2` sits on
the two vertices of `Z`, both of degree five (`C2P.Setting`). Then some port `y` (a vertex of `W`
of degree at most five) is good: the balanced pair `(W - y, U)` has no violated cut, that is, it
satisfies the cut condition of `exists_four_factor` (`C2P.false_of_bad_ports`). So `(U, W)` has a
quartic subgraph (`quartic_of_sparse_c2_ports`). Suppose instead that every port carries a
violated cut.

* `T = (XT, YT)` is a `W`-small 2-block on `Z` (a member of `Fam 12 2`) of maximum size
  `|XT| + |YT|`. The pair `(Z, ∅)` is one (`C2P.Setting.fam_Z`), so `T` always exists, and the
  case `T = (Z, ∅)` needs no separate argument. A sub-pair `R` is *above* `T` if `R ⊇ T`.
* Every port `y` has an α- or a β-petal (`C2P.port_petal`), and `y ∉ YT` (`notMem_of_port`). If
  some member of `𝒜 = Fam 12 1` above `T` contains `y`, let `R_y` be the largest such member,
  which contains all of them (`closure`). Otherwise the petal `Q` of `y` is a β-petal, and
  `R_y = T ∪ Q` lies in `Fam 14 2` (`union_beta`). The *part* of `y` is `(R_y)_W - YT`, the
  `W`-vertices of `R_y` outside `T`.
* Two parts are equal or disjoint (`closure`, `beta_beta`, `alpha_beta`). Each part has
  `3 D(part) ≤ 2 c(part)` (`C2P.part_bound`), where `c(part)` counts the edges between the part
  and `XT`. These are boundary edges of `T`, disjoint parts use disjoint sets of them, and `T` has
  ten (`C2P.block_boundary`). The ports carry `D(W) = 8`, so `3 · 8 ≤ 2 · 10` (`C2P.budget`), a
  contradiction.

The lattice steps use only `g ≥ 12` on proper sub-pairs containing `Z` (`C2P.Setting.twelve_le_gv`).

* `C2P.false_of_bad_ports`: not every port carries a violated cut.
* `quartic_of_sparse_c2_ports`: the statement used by `Main.lean`.
-/

open Finset

namespace Erdos585.QB5

open QB4

namespace C2P

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {U W Z XT YT : Finset V}

/-! ### Maximality of `T` -/

omit [DecidableEq V] in
/-- A `W`-small 2-block above the maximal `T` has no `W`-vertex outside `YT`. -/
private lemma not_above (hmax : ∀ X Y, Fam G U W Z 12 2 X Y → #X + #Y ≤ #XT + #YT)
    {X Y : Finset V} (hF : Fam G U W Z 12 2 X Y) (hTX : XT ⊆ X) (hTY : YT ⊆ Y) {y : V}
    (hy : y ∈ Y) (hyT : y ∉ YT) : False := by
  have h1 := hmax X Y hF
  have h2 := card_le_card hTX
  have h3 : #YT < #Y := card_lt_card ⟨hTY, fun h => hyT (h hy)⟩
  omega

omit [DecidableEq V] in
/-- A `W`-small 2-block above the maximal `T` has the same `W`-side as `T`. -/
private lemma subset_of_above (hmax : ∀ X Y, Fam G U W Z 12 2 X Y → #X + #Y ≤ #XT + #YT)
    {X Y : Finset V} (hF : Fam G U W Z 12 2 X Y) (hTX : XT ⊆ X) (hTY : YT ⊆ Y) : Y ⊆ YT := by
  have h1 := hmax X Y hF
  have h2 := card_le_card hTX
  have h3 := card_le_card hTY
  have he : YT = Y := eq_of_subset_of_card_le hTY (by omega)
  rw [← he]

omit [DecidableEq V] in
/-- A port is not in the `W`-side of a `W`-small 2-block on `Z`. -/
private lemma notMem_of_port (hS : Setting G U W Z) (hT : Fam G U W Z 12 2 XT YT) {y : V}
    (hp : dg G U y ≤ 5) : y ∉ YT := fun hy => by
  have := six_le_dg_of_block hS hT hy
  omega

/-- A member of `Fam 14 2` has `h = 1`, so it contains at most one port. -/
private lemma false_of_two_ports (hS : Setting G U W Z) {X Y : Finset V}
    (hF : Fam G U W Z 14 2 X Y) {y y' : V} (hy : y ∈ Y) (hy' : y' ∈ Y) (hne : y ≠ y')
    (hp : dg G U y ≤ 5) (hp' : dg G U y' ≤ 5) : False := by
  obtain ⟨hX, hY, -, -, hg, hk⟩ := hF
  have h1 := gv_eq_left (G := G) X Y
  have h2 : df G U Y ≤ df G X Y := df_anti hX
  have h3 : df G U {y, y'} ≤ df G U Y :=
    df_le_of_subset (insert_subset hy (singleton_subset_iff.2 hy')) fun z hz => hS.degW z (hY hz)
  have h4 : df G U {y, y'} = (6 - (dg G U y : ℤ)) + (6 - (dg G U y' : ℤ)) := by
    unfold df
    rw [sum_pair hne]
  have hk' : (#X : ℤ) = #Y + 2 := by exact_mod_cast hk
  have hp1 : (dg G U y : ℤ) ≤ 5 := by exact_mod_cast hp
  have hp2 : (dg G U y' : ℤ) ≤ 5 := by exact_mod_cast hp'
  linarith

/-! ### Unions with `T` -/

/-- **`T` and an α-petal.** The union of `T` with a member `Q` of `𝒜` that contains a `W`-vertex
`y ∉ YT` (in the use, an α-petal of the port `y`) is in `𝒜`: by `lattice`, `T ∩ Q` and `T ∪ Q`
both have `g = 12`, their `κ` sum to `3`, and `κ(T ∪ Q) = 2` would give a `W`-small 2-block
strictly above `T`. -/
private lemma union_alpha (hS : Setting G U W Z) (hT : Fam G U W Z 12 2 XT YT)
    (hmax : ∀ X Y, Fam G U W Z 12 2 X Y → #X + #Y ≤ #XT + #YT) {X Y : Finset V}
    (hQ : Fam G U W Z 12 1 X Y) {y : V} (hy : y ∈ Y) (hyT : y ∉ YT) :
    Fam G U W Z 12 1 (XT ∪ X) (YT ∪ Y) := by
  obtain ⟨hlt, hgu, hgi, hsum⟩ := lattice hS hT hQ (by norm_num)
  obtain ⟨hXT, hYT, hZT, -, -, hkT⟩ := hT
  obtain ⟨hX, hY, -, -, -, hk⟩ := hQ
  have hXu := card_union_add_card_inter XT X
  have hYu := card_union_add_card_inter YT Y
  have hκu := hS.six_mul_le_gv (union_subset hXT hX) (union_subset hYT hY)
  have hκi := hS.six_mul_le_gv ((inter_subset_left : XT ∩ X ⊆ XT).trans hXT)
    ((inter_subset_left : YT ∩ Y ⊆ YT).trans hYT)
  have hgu' : gv G (XT ∪ X) (YT ∪ Y) = 12 := by linarith
  rcases (by omega : #(XT ∪ X) = #(YT ∪ Y) + 1 ∨ #(XT ∪ X) = #(YT ∪ Y) + 2) with h1 | h2
  · exact ⟨union_subset hXT hX, union_subset hYT hY, hZT.trans subset_union_left, hlt, hgu', h1⟩
  · exact (not_above hmax ⟨union_subset hXT hX, union_subset hYT hY, hZT.trans subset_union_left,
      hlt, hgu', h2⟩ subset_union_left subset_union_left (mem_union_right _ hy) hyT).elim

/-- **`T` and a β-petal.** The union of `T` with a member `Q` of `Fam 14 2` that contains a
`W`-vertex `y ∉ YT` (in the use, a β-petal of the port `y`) has `g = 14` and `κ = 2`: by
`lattice`, both `T ∩ Q` and `T ∪ Q` have `g ≤ 14`, so `κ ≤ 2`, and `κ` sums to `4`; `g = 12`
would give a `W`-small 2-block strictly above `T`. -/
private lemma union_beta (hS : Setting G U W Z) (hT : Fam G U W Z 12 2 XT YT)
    (hmax : ∀ X Y, Fam G U W Z 12 2 X Y → #X + #Y ≤ #XT + #YT) {X Y : Finset V}
    (hQ : Fam G U W Z 14 2 X Y) {y : V} (hy : y ∈ Y) (hyT : y ∉ YT) :
    Fam G U W Z 14 2 (XT ∪ X) (YT ∪ Y) := by
  obtain ⟨hlt, hgu, hgi, hsum⟩ := lattice hS hT hQ (by norm_num)
  obtain ⟨hXT, hYT, hZT, -, -, hkT⟩ := hT
  obtain ⟨hX, hY, -, -, -, hk⟩ := hQ
  have hXu := card_union_add_card_inter XT X
  have hYu := card_union_add_card_inter YT Y
  have hκu := hS.six_mul_le_gv (union_subset hXT hX) (union_subset hYT hY)
  have hκi := hS.six_mul_le_gv ((inter_subset_left : XT ∩ X ⊆ XT).trans hXT)
    ((inter_subset_left : YT ∩ Y ⊆ YT).trans hYT)
  obtain ⟨r, hr⟩ := even_gv (G := G) (XT ∪ X) (YT ∪ Y)
  have hk2 : #(XT ∪ X) = #(YT ∪ Y) + 2 := by omega
  rcases (by omega : gv G (XT ∪ X) (YT ∪ Y) = 12 ∨ gv G (XT ∪ X) (YT ∪ Y) = 14) with h12 | h14
  · exact (not_above hmax ⟨union_subset hXT hX, union_subset hYT hY, hZT.trans subset_union_left,
      hlt, h12, hk2⟩ subset_union_left subset_union_left (mem_union_right _ hy) hyT).elim
  · exact ⟨union_subset hXT hX, union_subset hYT hY, hZT.trans subset_union_left, hlt, h14, hk2⟩

/-! ### How the parts meet -/

/-- **Two members of `𝒜`.** For two members of `𝒜` above `T`, either their `W`-sides meet
exactly in `YT`, or their union is in `𝒜`: by `lattice` the union and the intersection have
`g = 12` and their `κ` sum to `2`; `κ(∪) = 2` gives a `W`-small 2-block strictly above `T`, and
`κ(∩) = 2` gives a `W`-small 2-block above `T`, which is `T` by maximality. -/
private lemma closure (hS : Setting G U W Z)
    (hmax : ∀ X Y, Fam G U W Z 12 2 X Y → #X + #Y ≤ #XT + #YT) (hkT : #XT = #YT + 2)
    {X Y X' Y' : Finset V} (hR : Fam G U W Z 12 1 X Y) (hR' : Fam G U W Z 12 1 X' Y')
    (hTX : XT ⊆ X) (hTY : YT ⊆ Y) (hTX' : XT ⊆ X') (hTY' : YT ⊆ Y') :
    Y ∩ Y' ⊆ YT ∨ Fam G U W Z 12 1 (X ∪ X') (Y ∪ Y') := by
  obtain ⟨hlt, hgu, hgi, hsum⟩ := lattice hS hR hR' (by norm_num)
  obtain ⟨hX, hY, hZ, hltR, -, hk⟩ := hR
  obtain ⟨hX', hY', hZ', -, -, hk'⟩ := hR'
  have hXu := card_union_add_card_inter X X'
  have hYu := card_union_add_card_inter Y Y'
  have hXU : X ∪ X' ⊆ U := union_subset hX hX'
  have hYW : Y ∪ Y' ⊆ W := union_subset hY hY'
  have hXi : X ∩ X' ⊆ U := inter_subset_left.trans hX
  have hYi : Y ∩ Y' ⊆ W := inter_subset_left.trans hY
  have hκu := hS.six_mul_le_gv hXU hYW
  have hκi := hS.six_mul_le_gv hXi hYi
  have hgu' : gv G (X ∪ X') (Y ∪ Y') = 12 := by linarith
  have hgi' : gv G (X ∩ X') (Y ∩ Y') = 12 := by linarith
  have hli : #(X ∩ X') + #(Y ∩ Y') < #U + #W := by
    have := card_le_card (inter_subset_left : X ∩ X' ⊆ X)
    have := card_le_card (inter_subset_left : Y ∩ Y' ⊆ Y)
    omega
  rcases (by omega : #(X ∪ X') + 0 = #(Y ∪ Y') ∨ #(X ∪ X') = #(Y ∪ Y') + 1 ∨
      #(X ∪ X') = #(Y ∪ Y') + 2) with h0 | h1 | h2
  · left
    exact subset_of_above hmax ⟨hXi, hYi, subset_inter hZ hZ', hli, hgi', by omega⟩
      (subset_inter hTX hTX') (subset_inter hTY hTY')
  · exact Or.inr ⟨hXU, hYW, hZ.trans subset_union_left, hlt, hgu', h1⟩
  · exfalso
    have h3 := hmax _ _ ⟨hXU, hYW, hZ.trans subset_union_left, hlt, hgu', h2⟩
    have h4 := card_le_card (subset_union_left : X ⊆ X ∪ X')
    have h5 := card_le_card (subset_union_left : Y ⊆ Y ∪ Y')
    have h6 := card_le_card hTX
    have h7 := card_le_card hTY
    omega

/-- **Two members of `Fam 14 2`.** If two members of `Fam 14 2` above `T` contain distinct
ports, their `W`-sides meet exactly in `YT`: by `lattice` the union and the intersection have
`g ≤ 16`, so both `κ` are `2`; `g(∪) = 12` is a `W`-small 2-block strictly above `T`, and
`g(∪) = 14` has `h = 1` and two ports, so `g(∪) = 16` and `g(∩) = 12`. -/
private lemma beta_beta (hS : Setting G U W Z) (hT : Fam G U W Z 12 2 XT YT)
    (hmax : ∀ X Y, Fam G U W Z 12 2 X Y → #X + #Y ≤ #XT + #YT)
    {X Y X' Y' : Finset V} (hR : Fam G U W Z 14 2 X Y) (hR' : Fam G U W Z 14 2 X' Y')
    (hTX : XT ⊆ X) (hTY : YT ⊆ Y) (hTX' : XT ⊆ X') (hTY' : YT ⊆ Y') {y y' : V} (hy : y ∈ Y)
    (hy' : y' ∈ Y') (hne : y ≠ y') (hp : dg G U y ≤ 5) (hp' : dg G U y' ≤ 5) : Y ∩ Y' ⊆ YT := by
  obtain ⟨hlt, hgu, hgi, hsum⟩ := lattice hS hR hR' (by norm_num)
  obtain ⟨hX, hY, hZ, hltR, -, hk⟩ := hR
  obtain ⟨hX', hY', hZ', -, -, hk'⟩ := hR'
  have hXu := card_union_add_card_inter X X'
  have hYu := card_union_add_card_inter Y Y'
  have hXU : X ∪ X' ⊆ U := union_subset hX hX'
  have hYW : Y ∪ Y' ⊆ W := union_subset hY hY'
  have hXi : X ∩ X' ⊆ U := inter_subset_left.trans hX
  have hYi : Y ∩ Y' ⊆ W := inter_subset_left.trans hY
  have hκu := hS.six_mul_le_gv hXU hYW
  have hκi := hS.six_mul_le_gv hXi hYi
  have hli : #(X ∩ X') + #(Y ∩ Y') < #U + #W := by
    have := card_le_card (inter_subset_left : X ∩ X' ⊆ X)
    have := card_le_card (inter_subset_left : Y ∩ Y' ⊆ Y)
    omega
  obtain ⟨r, hr⟩ := even_gv (G := G) (X ∪ X') (Y ∪ Y')
  have hku : #(X ∪ X') = #(Y ∪ Y') + 2 := by omega
  have hki : #(X ∩ X') = #(Y ∩ Y') + 2 := by omega
  have hZu : Z ⊆ X ∪ X' := hZ.trans subset_union_left
  rcases (by omega : gv G (X ∪ X') (Y ∪ Y') = 12 ∨ gv G (X ∪ X') (Y ∪ Y') = 14 ∨
      gv G (X ∪ X') (Y ∪ Y') = 16) with h12 | h14 | h16
  · exact (not_above hmax ⟨hXU, hYW, hZu, hlt, h12, hku⟩ (hTX.trans subset_union_left)
      (hTY.trans subset_union_left) (mem_union_left _ hy) (notMem_of_port hS hT hp)).elim
  · exact (false_of_two_ports hS ⟨hXU, hYW, hZu, hlt, h14, hku⟩ (mem_union_left _ hy)
      (mem_union_right _ hy') hne hp hp').elim
  · exact subset_of_above hmax ⟨hXi, hYi, subset_inter hZ hZ', hli, by linarith, hki⟩
      (subset_inter hTX hTX') (subset_inter hTY hTY')

/-- **A member of `𝒜` and a member of `Fam 14 2`.** Let `R ⊇ T` be a member of `𝒜` containing a
port `y0`, and `R' ⊇ T` a member of `Fam 14 2` containing a port `y ≠ y0` that lies in no member
of `𝒜` above `T`. Then the `W`-sides of `R` and `R'` meet exactly in `YT`. By `lattice`, the
union and the intersection have `g ≤ 14`, and their `κ` sum to `3`. If
`(κ(∩), κ(∪)) = (2, 1)`: `g(∩) = 12` gives `∩ = T`, and `g(∩) = 14` puts `y` in the member
`R ∪ R'` of `𝒜`. If `(κ(∩), κ(∪)) = (1, 2)`: `g(∪) = 12` is a `W`-small 2-block strictly above
`T`, and `g(∪) = 14` has two ports. -/
private lemma alpha_beta (hS : Setting G U W Z) (hT : Fam G U W Z 12 2 XT YT)
    (hmax : ∀ X Y, Fam G U W Z 12 2 X Y → #X + #Y ≤ #XT + #YT)
    {X Y X' Y' : Finset V} (hR : Fam G U W Z 12 1 X Y) (hR' : Fam G U W Z 14 2 X' Y')
    (hTX : XT ⊆ X) (hTY : YT ⊆ Y) (hTX' : XT ⊆ X') (hTY' : YT ⊆ Y') {y0 y : V} (hy0 : y0 ∈ Y)
    (hy : y ∈ Y') (hne : y0 ≠ y) (hp0 : dg G U y0 ≤ 5) (hp : dg G U y ≤ 5)
    (hno : ∀ X'' Y'', Fam G U W Z 12 1 X'' Y'' → XT ⊆ X'' → YT ⊆ Y'' → y ∉ Y'') :
    Y ∩ Y' ⊆ YT := by
  obtain ⟨hlt, hgu, hgi, hsum⟩ := lattice hS hR hR' (by norm_num)
  obtain ⟨hX, hY, hZ, hltR, -, hk⟩ := hR
  obtain ⟨hX', hY', hZ', -, -, hk'⟩ := hR'
  have hXu := card_union_add_card_inter X X'
  have hYu := card_union_add_card_inter Y Y'
  have hXU : X ∪ X' ⊆ U := union_subset hX hX'
  have hYW : Y ∪ Y' ⊆ W := union_subset hY hY'
  have hXi : X ∩ X' ⊆ U := inter_subset_left.trans hX
  have hYi : Y ∩ Y' ⊆ W := inter_subset_left.trans hY
  have hκu := hS.six_mul_le_gv hXU hYW
  have hκi := hS.six_mul_le_gv hXi hYi
  have hli : #(X ∩ X') + #(Y ∩ Y') < #U + #W := by
    have := card_le_card (inter_subset_left : X ∩ X' ⊆ X)
    have := card_le_card (inter_subset_left : Y ∩ Y' ⊆ Y)
    omega
  obtain ⟨r, hr⟩ := even_gv (G := G) (X ∪ X') (Y ∪ Y')
  obtain ⟨r', hr'⟩ := even_gv (G := G) (X ∩ X') (Y ∩ Y')
  have hZu : Z ⊆ X ∪ X' := hZ.trans subset_union_left
  have hZi : Z ⊆ X ∩ X' := subset_inter hZ hZ'
  have hTXu : XT ⊆ X ∪ X' := hTX.trans subset_union_left
  have hTYu : YT ⊆ Y ∪ Y' := hTY.trans subset_union_left
  rcases (by omega : (#(X ∩ X') = #(Y ∩ Y') + 2 ∧ #(X ∪ X') = #(Y ∪ Y') + 1) ∨
      (#(X ∩ X') = #(Y ∩ Y') + 1 ∧ #(X ∪ X') = #(Y ∪ Y') + 2)) with ⟨hki, hku⟩ | ⟨hki, hku⟩
  · rcases (by omega : gv G (X ∩ X') (Y ∩ Y') = 12 ∨ gv G (X ∪ X') (Y ∪ Y') = 12) with h12 | h12
    · exact subset_of_above hmax ⟨hXi, hYi, hZi, hli, h12, hki⟩ (subset_inter hTX hTX')
        (subset_inter hTY hTY')
    · exact (hno _ _ ⟨hXU, hYW, hZu, hlt, h12, hku⟩ hTXu hTYu (mem_union_right _ hy)).elim
  · rcases (by omega : gv G (X ∪ X') (Y ∪ Y') = 12 ∨ gv G (X ∪ X') (Y ∪ Y') = 14) with h12 | h14
    · exact (not_above hmax ⟨hXU, hYW, hZu, hlt, h12, hku⟩ hTXu hTYu (mem_union_right _ hy)
        (notMem_of_port hS hT hp)).elim
    · exact (false_of_two_ports hS ⟨hXU, hYW, hZu, hlt, h14, hku⟩ (mem_union_left _ hy0)
        (mem_union_right _ hy) hne hp0 hp).elim

/-! ### The count -/

/-- **Some port is good.** In the setting of `C2P.Setting`, not every port carries a violated
cut: some port `y` has `4 |A| ≤ e(A, U - C) + 4 |C|` for all `A ⊆ W - y`, `C ⊆ U`. -/
theorem false_of_bad_ports (hS : Setting G U W Z)
    (hviol : ∀ y ∈ W, dg G U y ≤ 5 →
      ∃ A ⊆ W.erase y, ∃ C ⊆ U, ec G A (U \ C) + 4 * #C < 4 * #A) : False := by
  classical
  -- `T`: a `W`-small 2-block containing `Z` of maximum size
  obtain ⟨⟨XT, YT⟩, hTmem, hTmax⟩ := exists_max_image
    ((U.powerset ×ˢ W.powerset).filter fun R => Fam G U W Z 12 2 R.1 R.2)
    (fun R => #R.1 + #R.2)
    ⟨(Z, ∅), mem_filter.2 ⟨mem_product.2 ⟨mem_powerset.2 hS.subZ,
      mem_powerset.2 (empty_subset _)⟩, hS.fam_Z⟩⟩
  have hT : Fam G U W Z 12 2 XT YT := (mem_filter.1 hTmem).2
  have hmax : ∀ X Y, Fam G U W Z 12 2 X Y → #X + #Y ≤ #XT + #YT := fun X Y hF =>
    hTmax (X, Y) (mem_filter.2 ⟨mem_product.2 ⟨mem_powerset.2 hF.1, mem_powerset.2 hF.2.1⟩, hF⟩)
  have hkT : #XT = #YT + 2 := hT.2.2.2.2.2
  -- the ports
  set P := W.filter fun w => dg G U w ≤ 5 with hPdef
  -- the pair `R_y` of each port `y`
  have hpart : ∀ y ∈ P, ∃ R : Finset V × Finset V, y ∈ R.2 ∧ XT ⊆ R.1 ∧ YT ⊆ R.2 ∧
      ((Fam G U W Z 12 1 R.1 R.2 ∧ ∀ X Y, Fam G U W Z 12 1 X Y → XT ⊆ X → YT ⊆ Y → y ∈ Y →
          X ⊆ R.1 ∧ Y ⊆ R.2) ∨
        ((∀ X Y, Fam G U W Z 12 1 X Y → XT ⊆ X → YT ⊆ Y → y ∉ Y) ∧
          Fam G U W Z 14 2 R.1 R.2)) := by
    intro y hyP
    obtain ⟨hyW, hp⟩ := mem_filter.1 hyP
    have hyT : y ∉ YT := notMem_of_port hS hT hp
    by_cases hA : ∃ X Y, Fam G U W Z 12 1 X Y ∧ XT ⊆ X ∧ YT ⊆ Y ∧ y ∈ Y
    · -- the largest member of `𝒜` above `T` containing `y`
      obtain ⟨R0, hR0, hR0max⟩ := exists_max_image
        ((U.powerset ×ˢ W.powerset).filter fun R =>
          Fam G U W Z 12 1 R.1 R.2 ∧ XT ⊆ R.1 ∧ YT ⊆ R.2 ∧ y ∈ R.2)
        (fun R => #R.1 + #R.2)
        (by
          obtain ⟨X, Y, hF, h1, h2, h3⟩ := hA
          exact ⟨(X, Y), mem_filter.2 ⟨mem_product.2 ⟨mem_powerset.2 hF.1,
            mem_powerset.2 hF.2.1⟩, hF, h1, h2, h3⟩⟩)
      obtain ⟨-, hF0, hT0X, hT0Y, hy0⟩ := mem_filter.1 hR0
      refine ⟨R0, hy0, hT0X, hT0Y, Or.inl ⟨hF0, fun X Y hF hTX hTY hyY => ?_⟩⟩
      rcases closure hS hmax hkT hF hF0 hTX hTY hT0X hT0Y with hsub | hU
      · exact absurd (hsub (mem_inter.2 ⟨hyY, hy0⟩)) hyT
      · have hle := hR0max (X ∪ R0.1, Y ∪ R0.2) (mem_filter.2 ⟨mem_product.2
          ⟨mem_powerset.2 hU.1, mem_powerset.2 hU.2.1⟩, hU, hTX.trans subset_union_left,
          hTY.trans subset_union_left, mem_union_left _ hyY⟩)
        dsimp only at hle
        have h1 := card_le_card (subset_union_right : R0.1 ⊆ X ∪ R0.1)
        have h2 := card_le_card (subset_union_right : R0.2 ⊆ Y ∪ R0.2)
        have e1 : X ∪ R0.1 = R0.1 :=
          (eq_of_subset_of_card_le (subset_union_right : R0.1 ⊆ X ∪ R0.1) (by omega)).symm
        have e2 : Y ∪ R0.2 = R0.2 :=
          (eq_of_subset_of_card_le (subset_union_right : R0.2 ⊆ Y ∪ R0.2) (by omega)).symm
        exact ⟨union_eq_right.1 e1, union_eq_right.1 e2⟩
    · -- no member of `𝒜` above `T` contains `y`: its petal `Q` is a β-petal, and `R_y = T ∪ Q`
      obtain ⟨A, hA', C, hC, hv⟩ := hviol y hyW hp
      obtain ⟨hyWA, hfam⟩ := port_petal hS hyW hp hA' hC hv
      rcases hfam with hα | hβ
      · exact absurd ⟨XT ∪ (U \ C), YT ∪ (W \ A), union_alpha hS hT hmax hα hyWA hyT,
          subset_union_left, subset_union_left, mem_union_right _ hyWA⟩ hA
      · exact ⟨(XT ∪ (U \ C), YT ∪ (W \ A)), mem_union_right _ hyWA, subset_union_left,
          subset_union_left, Or.inr ⟨fun X Y hF hTX hTY hyY => hA ⟨X, Y, hF, hTX, hTY, hyY⟩,
          union_beta hS hT hmax hβ hyWA hyT⟩⟩
  choose! F hF using hpart
  have hFW : ∀ y ∈ P, (F y).2 ⊆ W := fun y hy => by
    rcases (hF y hy).2.2.2 with ⟨hA, -⟩ | ⟨-, hB⟩
    · exact hA.2.1
    · exact hB.2.1
  -- two parts are equal or disjoint
  have h2 : ∀ y ∈ P, ∀ y' ∈ P,
      (F y).2 \ YT = (F y').2 \ YT ∨ Disjoint ((F y).2 \ YT) ((F y').2 \ YT) := by
    intro y hy y' hy'
    obtain ⟨hyF, hTX, hTY, hc⟩ := hF y hy
    obtain ⟨hyF', hTX', hTY', hc'⟩ := hF y' hy'
    have hp := (mem_filter.1 hy).2
    have hp' := (mem_filter.1 hy').2
    have hdis : (F y).2 ∩ (F y').2 ⊆ YT → Disjoint ((F y).2 \ YT) ((F y').2 \ YT) := fun h => by
      rw [disjoint_left]
      intro z hz hz'
      exact (mem_sdiff.1 hz).2 (h (mem_inter.2 ⟨(mem_sdiff.1 hz).1, (mem_sdiff.1 hz').1⟩))
    rcases hc with ⟨hA, hAmax⟩ | ⟨hno, hB⟩ <;> rcases hc' with ⟨hA', hAmax'⟩ | ⟨hno', hB'⟩
    · rcases closure hS hmax hkT hA hA' hTX hTY hTX' hTY' with hsub | hU
      · exact Or.inr (hdis hsub)
      · left
        have e1 := hAmax _ _ hU (hTX.trans subset_union_left) (hTY.trans subset_union_left)
          (mem_union_left _ hyF)
        have e2 := hAmax' _ _ hU (hTX.trans subset_union_left) (hTY.trans subset_union_left)
          (mem_union_right _ hyF')
        rw [Subset.antisymm (subset_union_left.trans e2.2) (subset_union_right.trans e1.2)]
    · have hne : y ≠ y' := fun h => hno' _ _ hA hTX hTY (by rw [← h]; exact hyF)
      exact Or.inr (hdis (alpha_beta hS hT hmax hA hB' hTX hTY hTX' hTY' hyF hyF' hne hp hp' hno'))
    · have hne : y' ≠ y := fun h => hno _ _ hA' hTX' hTY' (by rw [← h]; exact hyF')
      refine Or.inr (hdis ?_)
      rw [inter_comm]
      exact alpha_beta hS hT hmax hA' hB hTX' hTY' hTX hTY hyF' hyF hne hp' hp hno
    · by_cases hne : y = y'
      · subst hne
        exact Or.inl rfl
      · exact Or.inr (hdis (beta_beta hS hT hmax hB hB' hTX hTY hTX' hTY' hyF hyF' hne hp hp'))
  -- each part has `3 D(part) ≤ 2 c(part)`
  have h4 : ∀ y ∈ P, 3 * ∑ z ∈ (F y).2 \ YT, (6 - (dg G U z : ℤ)) ≤
      2 * ∑ z ∈ (F y).2 \ YT, (dg G XT z : ℤ) := by
    intro y hy
    obtain ⟨-, hTX, hTY, hc⟩ := hF y hy
    have hR : Fam G U W Z 12 1 (F y).1 (F y).2 ∨ Fam G U W Z 14 2 (F y).1 (F y).2 := by
      rcases hc with ⟨hA, -⟩ | ⟨-, hB⟩
      · exact Or.inl hA
      · exact Or.inr hB
    have := part_bound hS hT hR hTX hTY
    unfold df ec at this
    push_cast at this
    exact this
  -- the budget: `3 D(ports) ≤ 2 e(W - YT, XT) = 20`
  have hb := budget (P := P) (B := W \ YT) (fun y => (F y).2 \ YT) (fun z => 6 - (dg G U z : ℤ))
    (fun z => (dg G XT z : ℤ))
    (fun z hz => by have := hS.degW z (mem_sdiff.1 hz).1; omega) (fun z _ => by positivity)
    (fun y hy => mem_sdiff.2 ⟨(hF y hy).1, notMem_of_port hS hT (mem_filter.1 hy).2⟩) h2
    (fun y hy => sdiff_subset_sdiff (hFW y hy) Subset.rfl) h4
  have h10 := block_boundary hS hT
  have hB10 : ∑ z ∈ W \ YT, (dg G XT z : ℤ) = 10 := by
    unfold ec at h10
    exact_mod_cast h10
  -- the ports carry `D(W) = 8`
  have hP8 : ∑ z ∈ P, (6 - (dg G U z : ℤ)) = 8 := by
    have hsplit := sum_filter_add_sum_filter_not W (fun w => dg G U w ≤ 5)
      (fun z => 6 - (dg G U z : ℤ))
    have h0 : ∑ z ∈ W.filter (fun w => ¬ dg G U w ≤ 5), (6 - (dg G U z : ℤ)) = 0 :=
      sum_eq_zero fun z hz => by
        obtain ⟨hzW, hz5⟩ := mem_filter.1 hz
        have := hS.degW z hzW
        omega
    have h8 := hS.dfW
    unfold df at h8
    rw [hPdef]
    linarith
  rw [hP8, hB10] at hb
  norm_num at hb

end C2P

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **C2 with every `U`-degree at least five**: a sparse C2 instance whose `U`-vertices all have
degree at least five (so exactly two of them have degree five) has a quartic subgraph. If not,
every port carries a violated cut (`exists_violation_erase_of_not_quartic`), which
`C2P.false_of_bad_ports` rules out. -/
theorem quartic_of_sparse_c2_ports {U W : Finset V} {s : ℕ} (h : IsC2 G U W s)
    (hsp : Sparse5 G U W) (hdeg : ∀ u ∈ U, 5 ≤ dg G W u) : Quartic G U W := by
  by_contra hq
  have hcW : #W = #U + 1 := by rw [h.cardW, h.cardU]
  have hU : U.Nonempty := card_pos.1 (by have := h.pos; rw [h.cardU]; omega)
  set Z := U.filter fun u => dg G W u ≤ 5 with hZdef
  have hdegZ : ∀ z ∈ Z, dg G W z = 5 := fun z hz => by
    obtain ⟨hzU, hz5⟩ := mem_filter.1 hz
    have := hdeg z hzU
    omega
  have hdeg6 : ∀ u ∈ U, u ∉ Z → dg G W u = 6 := fun u hu huZ => by
    have h5 : ¬ dg G W u ≤ 5 := fun h5 => huZ (mem_filter.2 ⟨hu, h5⟩)
    have := h.degU u hu
    omega
  have hcardZ : #Z = 2 := by
    have hsplit := sum_filter_add_sum_filter_not U (fun u => dg G W u ≤ 5)
      (fun u => 6 - (dg G W u : ℤ))
    have h1 : ∑ u ∈ U.filter (fun u => dg G W u ≤ 5), (6 - (dg G W u : ℤ)) = #Z := by
      rw [card_eq_sum_ones, Nat.cast_sum]
      refine sum_congr rfl fun u hu => ?_
      rw [hdegZ u hu]
      norm_num
    have h0 : ∑ u ∈ U.filter (fun u => ¬ dg G W u ≤ 5), (6 - (dg G W u : ℤ)) = 0 :=
      sum_eq_zero fun u hu => by
        obtain ⟨huU, hu5⟩ := mem_filter.1 hu
        have := h.degU u huU
        omega
    have h2 := h.defU
    unfold df at h2
    have : (#Z : ℤ) = 2 := by linarith
    exact_mod_cast this
  have hS : C2P.Setting G U W Z :=
    { degU := h.degU
      degW := h.degW
      cardW := hcW
      defU := h.defU
      sparse := hsp
      subZ := filter_subset _ _
      cardZ := hcardZ
      degZ := hdegZ
      degU6 := hdeg6 }
  exact C2P.false_of_bad_ports hS fun y hy _ =>
    exists_violation_erase_of_not_quartic hcW hU hq hy

end Erdos585.QB5
