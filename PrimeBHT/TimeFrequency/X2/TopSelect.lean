module

public import PrimeBHT.TimeFrequency.X2.EnergyTop

/-!
# X2, TB-3: the top separation lemma for the REV3 (fat, sandwich-free) top data, and V13's fatness lemma

`docs/audits/X2-TB3-check.md`, `docs/audits/X2-REV3-fat-top.md`.  Contents:

* `TopSel`, `plusShell`, the shell arithmetic (`shell_diff_bounds`, `shell_close`, `shell_order`), `zpow_gap`;
* the REV3 hull lemmas: `mem_hull_of_near` (a point within `hullDil ℓ/(2 f_k)` of the normalized centre of slot `k` is in
  `Box.hull`), `fat_icc_subset_hull` (the numerology of `hullDil = 128`, `fatRad = 24`), `isTopDatum_of_nonlacunary`
  (**the top data V13 needs are fat**: a tile `R` whose slot `k` is non-lacunary, every lattice `W ⊇ I_R`, every grid
  frequency within `6·2^{-W.1}` of `ξ_T`), `exists_grid_near`;
* the generic REV3 datum `IsTopDatumH H ρ J C W ξ` (`IsTopDatum = IsTopDatumH Box.hull fatRad`), the maximal tree
  `maxTreeH`, the greedy selection `IsGreedyTopH` (maximal `ξ` first, remove the maximal tree at `ξ`), the order lemmas,
  the swallowing lemma `not_adm_after`, `top_separation_pair_H` (any hull `H`), and its instance `top_separation_pair`,
  `top_separation` (MTT2 shape) for the built hull.  The proof needs only field (a) of `IsRankOne`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-! ## Data -/

/-- A selected top datum: the interval `W`, the centre `ξ` of the top multiplier, and the removal point `ζ`
(the tree removed is `maxTree C W ζ`). -/
structure TopSel where
  W : ℤ × ℤ
  ξ : ℝ
  ζ : ℝ

/-- The `+` shell of the top multiplier at `(W, ξ)` in the slot of direction `f = freqDir k`, in the raw frequency
variable `η`: `η - ξ f ∈ [¼ 2^{-W.1}, 12·2^{-W.1}]` (above the hole, inside the support). -/
def plusShell (f : ℝ) (W : ℤ × ℤ) (ξ : ℝ) : Set ℝ :=
  Set.Icc (ξ * f + topHole * (2 : ℝ) ^ (-W.1)) (ξ * f + topRad * (2 : ℝ) ^ (-W.1))

/-! ## Scale arithmetic -/

theorem zpow_gap {J : ℕ} (hJ : 16 ≤ J) {a b : ℤ} (hdvd : (J : ℤ) ∣ a - b) (hlt : b < a) :
    65536 * (2 : ℝ) ^ (-a) ≤ (2 : ℝ) ^ (-b) := by
  have h1 : (J : ℤ) ≤ a - b := Int.le_of_dvd (by omega) hdvd
  have h2 : (16 : ℤ) ≤ a - b := by omega
  have h3 : (2 : ℝ) ^ (16 : ℤ) ≤ (2 : ℝ) ^ (a - b) :=
    zpow_le_zpow_right₀ (by norm_num) h2
  have h4 : (2 : ℝ) ^ (-b) = (2 : ℝ) ^ (a - b) * (2 : ℝ) ^ (-a) := by
    rw [← zpow_add₀ (by norm_num)]
    congr 1
    ring
  have h5 : (0 : ℝ) < (2 : ℝ) ^ (-a) := zpow_pos (by norm_num) _
  rw [h4]
  have h6 : (2 : ℝ) ^ (16 : ℤ) = 65536 := by norm_num
  rw [h6] at h3
  nlinarith


/-! ## Shell geometry -/

theorem shell_diff_bounds {f : ℝ} {W₀ W : ℤ × ℤ} {ξ₀ ξ : ℝ} (h : (plusShell f W₀ ξ₀ ∩ plusShell f W ξ).Nonempty) :
    topHole * (2 : ℝ) ^ (-W.1) - topRad * (2 : ℝ) ^ (-W₀.1) ≤ (ξ₀ - ξ) * f ∧
      (ξ₀ - ξ) * f ≤ topRad * (2 : ℝ) ^ (-W.1) - topHole * (2 : ℝ) ^ (-W₀.1) := by
  obtain ⟨η, ⟨h1, h2⟩, ⟨h3, h4⟩⟩ := h
  constructor <;> nlinarith

/-- Two data `a`, `b` overlapping the `+` shell of `V₀` (with `a₀ ≤ a_a ≤ a_b`, the `a`'s being `2^{-W.1}`):
`|ξ_a - ξ_b| f ≤ (47/2) a_b`. -/
theorem shell_close {f a₀ aa ab ξ₀ ξa ξb : ℝ} (hf : 1 ≤ f) (h0a : a₀ ≤ aa) (hab : aa ≤ ab)
    (hA : topHole * aa - topRad * a₀ ≤ (ξ₀ - ξa) * f ∧ (ξ₀ - ξa) * f ≤ topRad * aa - topHole * a₀)
    (hB : topHole * ab - topRad * a₀ ≤ (ξ₀ - ξb) * f ∧ (ξ₀ - ξb) * f ≤ topRad * ab - topHole * a₀) :
    |ξa - ξb| ≤ 47 / 2 * ab := by
  unfold topHole topRad at hA hB
  have h1 : (ξa - ξb) * f ≤ 47 / 2 * ab := by nlinarith [hA.1, hA.2, hB.1, hB.2]
  have h2 : -(47 / 2 * ab) ≤ (ξa - ξb) * f := by nlinarith [hA.1, hA.2, hB.1, hB.2]
  have h3 : |(ξa - ξb) * f| ≤ 47 / 2 * ab := abs_le.2 ⟨h2, h1⟩
  rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < f)] at h3
  nlinarith [abs_nonneg (ξa - ξb)]

/-- Orientation: if `a_b ≥ 2^16 a_a` then `ξ_b < ξ_a` (the datum with the larger frequency scale lies below). -/
theorem shell_order {f a₀ aa ab ξ₀ ξa ξb : ℝ} (hf : 1 ≤ f) (h0a : a₀ ≤ aa) (haa : 0 < aa)
    (hab : 65536 * aa ≤ ab)
    (hA : topHole * aa - topRad * a₀ ≤ (ξ₀ - ξa) * f ∧ (ξ₀ - ξa) * f ≤ topRad * aa - topHole * a₀)
    (hB : topHole * ab - topRad * a₀ ≤ (ξ₀ - ξb) * f ∧ (ξ₀ - ξb) * f ≤ topRad * ab - topHole * a₀) :
    ξb < ξa := by
  unfold topHole topRad at hA hB
  have h1 : 0 < (ξa - ξb) * f := by nlinarith [hA.1, hA.2, hB.1, hB.2]
  by_contra hcon
  rw [not_lt] at hcon
  nlinarith



/-! ## The REV3 hull and the fatness of V13's data -/

theorem freqDir_pos' (k : Fin 3) : 0 < freqDir k := by fin_cases k <;> simp [freqDir]
theorem freqDir_le_two' (k : Fin 3) : freqDir k ≤ 2 := by fin_cases k <;> simp [freqDir]

/-- A point within `hullDil ℓ / (2 f_k)` of the normalized centre of slot `k` is in the hull
(the analogue of the built `div_mem_hull`, which is the case `hullDil = 3`). -/
theorem mem_hull_of_near (B : Box) (k : Fin 3) {x : ℝ}
    (h : |x - B.centre k / freqDir k| ≤ hullDil * (2 : ℝ) ^ (-B.scale) / (2 * freqDir k)) :
    x ∈ B.hull := by
  have hd := freqDir_pos' k
  have hdn : freqDir k ≠ 0 := hd.ne'
  rw [abs_le] at h
  have e1 : (B.centre k - hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir k =
      B.centre k / freqDir k - hullDil * (2 : ℝ) ^ (-B.scale) / (2 * freqDir k) := by
    field_simp
  have e2 : (B.centre k + hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir k =
      B.centre k / freqDir k + hullDil * (2 : ℝ) ^ (-B.scale) / (2 * freqDir k) := by
    field_simp
  unfold Box.hull
  rw [Set.mem_Icc]
  constructor
  · have : min (min ((B.centre 0 - hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir 0)
        ((B.centre 1 - hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir 1))
        ((B.centre 2 - hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir 2) ≤
        (B.centre k - hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir k := by
      fin_cases k
      · exact (min_le_left _ _).trans (min_le_left _ _)
      · exact (min_le_left _ _).trans (min_le_right _ _)
      · exact min_le_right _ _
    rw [e1] at this
    linarith [h.1]
  · have : (B.centre k + hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir k ≤
        max (max ((B.centre 0 + hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir 0)
        ((B.centre 1 + hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir 1))
        ((B.centre 2 + hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir 2) := by
      fin_cases k
      · exact (le_max_left _ _).trans (le_max_left _ _)
      · exact (le_max_right _ _).trans (le_max_left _ _)
      · exact le_max_right _ _
    rw [e2] at this
    linarith [h.2]


/-! ## 1. Fatness of the data V13 needs (the key check of REV3) -/

/-- `ξ_T ∈ (13/4) ω̃_k(B)` (the overlapping/non-lacunary slot `k` of `V13`'s split, `ovThr = 13/4`) gives
`|ξ_T - c_k/f_k| ≤ (13/8) ℓ/f_k`. -/
theorem abs_sub_centre_le_of_mem_dilate {B : Box} {k : Fin 3} {ξT : ℝ}
    (h : ξT ∈ dilate (13 / 4) (B.ωn k)) :
    |ξT - B.centre k / freqDir k| ≤ 13 / 8 * ((2 : ℝ) ^ (-B.scale) / freqDir k) := by
  have hd := freqDir_pos' k
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
  unfold Box.ωn at h
  have hlt : (B.centre k - (2 : ℝ) ^ (-B.scale) / 2) / freqDir k <
      (B.centre k + (2 : ℝ) ^ (-B.scale) / 2) / freqDir k :=
    div_lt_div_of_pos_right (by linarith) hd
  rw [dilate_Ico hlt] at h
  obtain ⟨h1, h2⟩ := h
  have hmid : ((B.centre k - (2 : ℝ) ^ (-B.scale) / 2) / freqDir k +
      (B.centre k + (2 : ℝ) ^ (-B.scale) / 2) / freqDir k) / 2 = B.centre k / freqDir k := by
    field_simp; ring
  have hlen : (B.centre k + (2 : ℝ) ^ (-B.scale) / 2) / freqDir k -
      (B.centre k - (2 : ℝ) ^ (-B.scale) / 2) / freqDir k = (2 : ℝ) ^ (-B.scale) / freqDir k := by
    field_simp; ring
  rw [hmid, hlen] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- **The numerology of REV3**: if `ξ_T ∈ (13/4) ω̃_k(B)` and `ξ'` is within `6a` of `ξ_T` with `a ≤ ℓ_B = 2^{-scale B}`,
then the whole interval `[ξ' - 24 a, ξ' + 24 a]` lies in the hull `Box.hull B` (`hullDil = 128`).  (With the built hull,
`hullDil = 3`, this is false: `ξ_T` may sit at an endpoint of the hull.) -/
theorem fat_icc_subset_hull {B : Box} {k : Fin 3} {ξT ξ' a : ℝ} (hξT : ξT ∈ dilate (13 / 4) (B.ωn k))
    (ha : 0 < a) (haℓ : a ≤ (2 : ℝ) ^ (-B.scale)) (hξ' : |ξ' - ξT| ≤ 6 * a) :
    Set.Icc (ξ' - 24 * a) (ξ' + 24 * a) ⊆ B.hull := by
  intro x hx
  have hd := freqDir_pos' k
  have hd2 := freqDir_le_two' k
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
  have h1 := abs_sub_centre_le_of_mem_dilate hξT
  refine mem_hull_of_near B k ?_
  have hx1 := abs_le.1 (abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩ : |x - ξ'| ≤ 24 * a)
  have hx2 := abs_le.1 hξ'
  have hx3 := abs_le.1 h1
  -- `30 a + 13ℓ/(8 f) ≤ 64ℓ/f`: `30 a f ≤ 60 ℓ ≤ (64 - 13/8) ℓ`
  have hmain : 30 * a + 13 / 8 * ((2 : ℝ) ^ (-B.scale) / freqDir k) ≤
      hullDil * (2 : ℝ) ^ (-B.scale) / (2 * freqDir k) := by
    unfold hullDil
    have h60 : 30 * a * freqDir k ≤ 60 * (2 : ℝ) ^ (-B.scale) := by nlinarith
    have e : 13 / 8 * ((2 : ℝ) ^ (-B.scale) / freqDir k) * (2 * freqDir k) =
        13 / 4 * (2 : ℝ) ^ (-B.scale) := by
      field_simp; ring
    rw [le_div_iff₀ (by positivity)]
    nlinarith [e]
  rw [abs_le]
  constructor <;> linarith [hx1.1, hx1.2, hx2.1, hx2.2, hx3.1, hx3.2, hmain]


theorem round_near (m x : ℝ) (hm : 0 < m) : ∃ z : ℤ, |(z : ℝ) * m - x| ≤ m / 2 := by
  refine ⟨round (x / m), ?_⟩
  have h1 := abs_sub_round (x / m)
  rw [abs_sub_comm] at h1
  have h2 : (round (x / m) : ℝ) * m - x = ((round (x / m) : ℝ) - x / m) * m := by
    field_simp
  rw [h2, abs_mul, abs_of_pos hm]
  nlinarith

/-- Grid points are dense: every real is within `2^{-W.1}/16` of a grid frequency (so V13's `ξ_T ± 5·2^{-W.1}/f_k` is
within `6·2^{-W.1}` of `ξ_T` after rounding to the grid, and the low-pass symbol avoids the hole `1/4`: checked in the audit). -/
theorem exists_grid_near (W : ℤ × ℤ) (x : ℝ) :
    ∃ z : ℤ, |(z : ℝ) * (gridMesh * (2 : ℝ) ^ (-W.1)) - x| ≤ gridMesh * (2 : ℝ) ^ (-W.1) / 2 := by
  have hm : (0 : ℝ) < gridMesh * (2 : ℝ) ^ (-W.1) := by
    unfold gridMesh; have : (0 : ℝ) < (2 : ℝ) ^ (-W.1) := zpow_pos (by norm_num) _; positivity
  exact round_near _ x hm



/-- **V13's top data are fat** (the O-a / O-b / O2 bounds of `docs/audits/X2-V13-route-check.md` §2.6): for a tile `R` of
the part `T_A` whose slot `k` is non-lacunary (`ξ_T ∈ (13/4) ω̃_k(R)`), every lattice interval `W ⊇ I_R` (`J ∣ W.1 - R.scale`)
and every grid frequency `ξ'` within `6·2^{-W.1}` of `ξ_T` (V13 uses `ξ' ≈ ξ_T ± 5·2^{-W.1}/f_k`) give a top datum.
No scale gap `W.1 ≥ R.scale + O(1)` and no coarse partner is needed. -/
theorem isTopDatum_of_nonlacunary {J : ℕ} {Cs : Finset TriTile} {R : TriTile} (hR : R ∈ Cs) {k : Fin 3}
    {ξT : ℝ} (hξT : ξT ∈ dilate (13 / 4) (R.box.ωn k)) {W : ℤ × ℤ} (hW : R.I ⊆ dyadicInt W.1 W.2)
    (hJ : (J : ℤ) ∣ W.1 - R.box.scale) {ξ' : ℝ} (hg : ∃ z : ℤ, ξ' = z * (gridMesh * (2 : ℝ) ^ (-W.1)))
    (hξ' : |ξ' - ξT| ≤ 6 * (2 : ℝ) ^ (-W.1)) : IsTopDatum J Cs W ξ' := by
  have hle : R.box.scale ≤ W.1 := scale_le_of_dyadicInt_subset hW
  have ha : (0 : ℝ) < (2 : ℝ) ^ (-W.1) := zpow_pos (by norm_num) _
  have haℓ : (2 : ℝ) ^ (-W.1) ≤ (2 : ℝ) ^ (-R.box.scale) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  exact ⟨hg, R, hR, hW, hJ, by
    unfold fatRad
    exact fat_icc_subset_hull hξT ha haℓ hξ'⟩

/-! ## The generic datum, the greedy selection, TB-3 -/

/-- **REV3 top datum**, generic in the tree hull `H` (`H = Box.hull` is the REV3 choice): a grid frequency `ξ`, a tile
`R ∈ C` with `I_R ⊆ W`, `J ∣ W.1 - R.scale`, and the interval `[ξ ± ρ 2^{-W.1}]` inside `H R`.  (No coarse partner `R'`, no
sandwich `W ⊆ I_{R'}`: V13 needs lattice scales above every tile of the tree.) -/
def IsTopDatumH (H : Box → Set ℝ) (ρ : ℝ) (J : ℕ) (C : Finset TriTile) (W : ℤ × ℤ) (ξ : ℝ) : Prop :=
  (∃ z : ℤ, ξ = z * (gridMesh * (2 : ℝ) ^ (-W.1))) ∧
    ∃ R ∈ C, R.I ⊆ dyadicInt W.1 W.2 ∧ (J : ℤ) ∣ W.1 - R.box.scale ∧
      Set.Icc (ξ - ρ * (2 : ℝ) ^ (-W.1)) (ξ + ρ * (2 : ℝ) ^ (-W.1)) ⊆ H R.box

theorem IsTopDatumH.mono {H : Box → Set ℝ} {ρ : ℝ} {J : ℕ} {C C' : Finset TriTile} (h : C ⊆ C') {W : ℤ × ℤ}
    {ξ : ℝ} (hd : IsTopDatumH H ρ J C W ξ) : IsTopDatumH H ρ J C' W ξ := by
  obtain ⟨hg, R, hR, h1, h2, h3⟩ := hd
  exact ⟨hg, R, h hR, h1, h2, h3⟩

/-! ## 3. TB-3 for REV3 data, generic in the tree hull `H` (the proof of `TopSelect.lean`, `R'` dropped) -/

section GenericHull

/-- The maximal tree with top `(W, ξ)` for the tree hull `H` (`H = Box.hull` gives the built `maxTree`). -/
def maxTreeH (H : Box → Set ℝ) (Cs : Finset TriTile) (W : ℤ × ℤ) (ξ : ℝ) : Finset TriTile :=
  Cs.filter (fun R => R.I ⊆ dyadicInt W.1 W.2 ∧ ξ ∈ H R.box)

theorem mem_maxTreeH {H : Box → Set ℝ} {Cs : Finset TriTile} {W : ℤ × ℤ} {ξ : ℝ} {R : TriTile} :
    R ∈ maxTreeH H Cs W ξ ↔ R ∈ Cs ∧ R.I ⊆ dyadicInt W.1 W.2 ∧ ξ ∈ H R.box := by
  simp [maxTreeH]

/-- Admissibility with removal point `ξ`. -/
def AdmH (H : Box → Set ℝ) (ρ : ℝ) (J : ℕ) (C : Finset TriTile) (W : ℤ × ℤ) (ξ ζ : ℝ) : Prop :=
  ζ = ξ ∧ IsTopDatumH H ρ J C W ξ

theorem AdmH.mono {H : Box → Set ℝ} {ρ : ℝ} {J : ℕ} {C C' : Finset TriTile} (h : C ⊆ C') {W : ℤ × ℤ} {ξ ζ : ℝ}
    (hd : AdmH H ρ J C W ξ ζ) : AdmH H ρ J C' W ξ ζ := ⟨hd.1, hd.2.mono h⟩

/-- **Greedy `+`-selection of REV3 top data**: maximal `ξ` first among the candidates, remove `maxTreeH H C W ζ`. -/
inductive IsGreedyTopH (H : Box → Set ℝ) (Adm : Finset TriTile → ℤ × ℤ → ℝ → ℝ → Prop)
    (Cand : ℤ × ℤ → ℝ → Prop) : Finset TriTile → List TopSel → Prop
  | nil (C : Finset TriTile) : IsGreedyTopH H Adm Cand C []
  | cons {C : Finset TriTile} {W : ℤ × ℤ} {ξ ζ : ℝ} {ts : List TopSel} :
      Adm C W ξ ζ → Cand W ξ → (∀ W' ξ' ζ', Cand W' ξ' → Adm C W' ξ' ζ' → ξ' ≤ ξ) →
      IsGreedyTopH H Adm Cand (C \ maxTreeH H C W ζ) ts → IsGreedyTopH H Adm Cand C (⟨W, ξ, ζ⟩ :: ts)

def BeforeH (H : Box → Set ℝ) (Adm : Finset TriTile → ℤ × ℤ → ℝ → ℝ → Prop) (V V' : TopSel) : Prop :=
  V'.ξ ≤ V.ξ ∧ ∃ C₀ : Finset TriTile, Adm (C₀ \ maxTreeH H C₀ V.W V.ζ) V'.W V'.ξ V'.ζ

variable {H : Box → Set ℝ} {Adm : Finset TriTile → ℤ × ℤ → ℝ → ℝ → Prop} {Cand : ℤ × ℤ → ℝ → Prop}

theorem IsGreedyTopH.adm_cand (hmono : ∀ C C' W ξ ζ, C ⊆ C' → Adm C W ξ ζ → Adm C' W ξ ζ)
    {C : Finset TriTile} {ts : List TopSel} (h : IsGreedyTopH H Adm Cand C ts) :
    ∀ V ∈ ts, Adm C V.W V.ξ V.ζ ∧ Cand V.W V.ξ := by
  induction h with
  | nil C => intro V hV; exact absurd hV (List.not_mem_nil)
  | @cons C W ξ ζ ts hadm hcand _ _ ih =>
    intro V hV
    rcases List.mem_cons.1 hV with rfl | hV
    · exact ⟨hadm, hcand⟩
    · obtain ⟨h1, h2⟩ := ih V hV
      exact ⟨hmono _ _ _ _ _ Finset.sdiff_subset h1, h2⟩

theorem IsGreedyTopH.before (hmono : ∀ C C' W ξ ζ, C ⊆ C' → Adm C W ξ ζ → Adm C' W ξ ζ)
    {C : Finset TriTile} {ts : List TopSel} (h : IsGreedyTopH H Adm Cand C ts) :
    ∀ V ∈ ts, ∀ V' ∈ ts, V ≠ V' → BeforeH H Adm V V' ∨ BeforeH H Adm V' V := by
  induction h with
  | nil C => intro V hV; exact absurd hV (List.not_mem_nil)
  | @cons C W ξ ζ ts hadm hcand hmax htail ih =>
    have hhead : ∀ V' ∈ ts, BeforeH H Adm (TopSel.mk W ξ ζ) V' := by
      intro V' hV'
      obtain ⟨h1, h2⟩ := htail.adm_cand hmono V' hV'
      exact ⟨hmax _ _ _ h2 (hmono _ _ _ _ _ Finset.sdiff_subset h1), C, h1⟩
    intro V hV V' hV' hne
    rcases List.mem_cons.1 hV with rfl | hV
    · rcases List.mem_cons.1 hV' with rfl | hV'
      · exact absurd rfl hne
      · exact Or.inl (hhead _ hV')
    · rcases List.mem_cons.1 hV' with rfl | hV'
      · exact Or.inr (hhead _ hV)
      · exact ih V hV V' hV' hne

end GenericHull

/-- **Swallowing**: a REV3 datum `(W', ξ')` with `W' ⊆ W` and `|ξ - ξ'| ≤ ρ 2^{-W'.1}` is not admissible after
`maxTreeH H C W ξ` was removed. -/
theorem not_adm_after {H : Box → Set ℝ} {ρ : ℝ} {J : ℕ} {C : Finset TriTile} {W W' : ℤ × ℤ} {ξ ξ' ζ' : ℝ}
    (hW : dyadicInt W'.1 W'.2 ⊆ dyadicInt W.1 W.2) (hξ : |ξ - ξ'| ≤ ρ * (2 : ℝ) ^ (-W'.1))
    (hadm : AdmH H ρ J (C \ maxTreeH H C W ξ) W' ξ' ζ') : False := by
  obtain ⟨-, -, R, hR, h1, h2, h4⟩ := hadm
  rw [Finset.mem_sdiff] at hR
  refine hR.2 (mem_maxTreeH.2 ⟨hR.1, h1.trans hW, h4 ?_⟩)
  rw [abs_le] at hξ
  constructor <;> linarith [hξ.1, hξ.2]

theorem dvd_scale_diffH {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {Cs : Finset TriTile}
    (hbox : ∀ R ∈ Cs, R.box ∈ Qs) {H : Box → Set ℝ} {ρ : ℝ} {W W' : ℤ × ℤ} {ξ ξ' : ℝ}
    (h : IsTopDatumH H ρ J Cs W ξ) (h' : IsTopDatumH H ρ J Cs W' ξ') : (J : ℤ) ∣ W.1 - W'.1 := by
  obtain ⟨-, R, hR, -, h3, -⟩ := h
  obtain ⟨-, R₂, hR₂, -, h3', -⟩ := h'
  have h4 := hQ.1 R.box (hbox R hR) R₂.box (hbox R₂ hR₂)
  have : W.1 - W'.1 = (W.1 - R.box.scale) + (R.box.scale - R₂.box.scale) - (W'.1 - R₂.box.scale) := by ring
  rw [this]
  exact dvd_sub (dvd_add h3 h4) h3'

theorem sep_coreH {H : Box → Set ℝ} {ρ : ℝ} (hρ : 47 / 2 ≤ ρ) {J : ℕ} (hJ : jFloor ≤ J) {Qs : Set Box}
    (hQ : IsRankOne J Qs) {Cs : Finset TriTile} (hbox : ∀ R ∈ Cs, R.box ∈ Qs) {f : ℝ} (hf : 1 ≤ f)
    {V₀ V V' : TopSel} (hV : IsTopDatumH H ρ J Cs V.W V.ξ) (hV' : IsTopDatumH H ρ J Cs V'.W V'.ξ)
    (h0 : V.W.1 ≤ V₀.W.1) (h0' : V'.W.1 ≤ V₀.W.1)
    (hs : (plusShell f V₀.W V₀.ξ ∩ plusShell f V.W V.ξ).Nonempty)
    (hs' : (plusShell f V₀.W V₀.ξ ∩ plusShell f V'.W V'.ξ).Nonempty)
    (hmax : V'.ξ ≤ V.ξ)
    (hsw : dyadicInt V'.W.1 V'.W.2 ⊆ dyadicInt V.W.1 V.W.2 → ρ * (2 : ℝ) ^ (-V'.W.1) < |V.ξ - V'.ξ|) :
    Disjoint (dyadicInt V.W.1 V.W.2) (dyadicInt V'.W.1 V'.W.2) := by
  have hJ16 : 16 ≤ J := hJ
  have hz : ∀ a b : ℤ, a ≤ b → (2 : ℝ) ^ (-b) ≤ (2 : ℝ) ^ (-a) := fun a b hab =>
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hpos : ∀ a : ℤ, (0 : ℝ) < (2 : ℝ) ^ (-a) := fun a => zpow_pos (by norm_num) _
  have h0a : (2 : ℝ) ^ (-V₀.W.1) ≤ (2 : ℝ) ^ (-V.W.1) := hz _ _ h0
  have h0a' : (2 : ℝ) ^ (-V₀.W.1) ≤ (2 : ℝ) ^ (-V'.W.1) := hz _ _ h0'
  have caseI : dyadicInt V'.W.1 V'.W.2 ⊆ dyadicInt V.W.1 V.W.2 → False := by
    intro hsub
    have hle : V'.W.1 ≤ V.W.1 := scale_le_of_dyadicInt_subset hsub
    have haa : (2 : ℝ) ^ (-V.W.1) ≤ (2 : ℝ) ^ (-V'.W.1) := hz _ _ hle
    have hclose := shell_close hf h0a haa (shell_diff_bounds hs) (shell_diff_bounds hs')
    have h1 := hsw hsub
    have h2 := hpos V'.W.1
    nlinarith
  rcases dyadicInt_nested_or_disjoint V.W.1 V.W.2 V'.W.1 V'.W.2 with hVV' | hV'V | hd
  · exfalso
    have hle : V.W.1 ≤ V'.W.1 := scale_le_of_dyadicInt_subset hVV'
    rcases hle.lt_or_eq with hlt | heq
    · have hdvd := dvd_scale_diffH hQ hbox hV' hV
      have hgap := zpow_gap hJ16 hdvd hlt
      have := shell_order hf h0a' (hpos V'.W.1) hgap (shell_diff_bounds hs') (shell_diff_bounds hs)
      linarith
    · have hv := index_eq_of_dyadicInt_subset heq hVV'
      have hW : V'.W = V.W := Prod.ext heq.symm hv.symm
      exact caseI (by rw [hW])
  · exact (caseI hV'V).elim
  · exact hd

/-- **TB-3 for REV3 data (pair form), any tree hull `H`** (`H = Box.hull`): in a greedy `+`-selection of top data
(`ρ ≥ 47/2`) of a collection whose boxes lie in a rank-1 set (only field (a) is used), two distinct selected data whose
`+` shells overlap that of `V₀` (with `|W₀| ≥ |W|, |W'|`) have disjoint time intervals. -/
theorem top_separation_pair_H {H : Box → Set ℝ} {ρ : ℝ} (hρ : 47 / 2 ≤ ρ) {J : ℕ} (hJ : jFloor ≤ J)
    {Qs : Set Box} (hQ : IsRankOne J Qs) {Cs : Finset TriTile} (hbox : ∀ R ∈ Cs, R.box ∈ Qs)
    {Cand : ℤ × ℤ → ℝ → Prop} {ts : List TopSel} (hsel : IsGreedyTopH H (AdmH H ρ J) Cand Cs ts)
    {f : ℝ} (hf : 1 ≤ f) (V₀ : TopSel) {V V' : TopSel} (hV : V ∈ ts) (hV' : V' ∈ ts) (hne : V ≠ V')
    (h0 : V.W.1 ≤ V₀.W.1) (h0' : V'.W.1 ≤ V₀.W.1)
    (hs : (plusShell f V₀.W V₀.ξ ∩ plusShell f V.W V.ξ).Nonempty)
    (hs' : (plusShell f V₀.W V₀.ξ ∩ plusShell f V'.W V'.ξ).Nonempty) :
    Disjoint (dyadicInt V.W.1 V.W.2) (dyadicInt V'.W.1 V'.W.2) := by
  have hmono : ∀ C C' W ξ ζ, C ⊆ C' → AdmH H ρ J C W ξ ζ → AdmH H ρ J C' W ξ ζ :=
    fun C C' W ξ ζ h hd => hd.mono h
  obtain ⟨hadmV, -⟩ := hsel.adm_cand hmono V hV
  obtain ⟨hadmV', -⟩ := hsel.adm_cand hmono V' hV'
  rcases hsel.before hmono V hV V' hV' hne with ⟨hmax, C₀, hC₀⟩ | ⟨hmax, C₀, hC₀⟩
  · rw [hadmV.1] at hC₀
    exact sep_coreH hρ hJ hQ hbox hf hadmV.2 hadmV'.2 h0 h0' hs hs' hmax
      (fun hsub => lt_of_not_ge fun hle => not_adm_after hsub hle hC₀)
  · rw [hadmV'.1] at hC₀
    exact (sep_coreH hρ hJ hQ hbox hf hadmV'.2 hadmV.2 h0' h0 hs' hs hmax
      (fun hsub => lt_of_not_ge fun hle => not_adm_after hsub hle hC₀)).symm

/-- **TB-3 for the built top data (pair form)**: in a greedy `+`-selection of top data (`IsTopDatum`: grid, fat radius
`fatRad = 24 ≥ 47/2`; maximal `ξ` first; remove `maxTree C W ξ`) of a collection whose boxes lie in a rank-1 set (only
field (a) is used), two distinct selected data whose `+` shells overlap that of `V₀` (with `|W₀| ≥ |W|, |W'|`) have
disjoint time intervals. -/
theorem top_separation_pair {J : ℕ} (hJ : jFloor ≤ J) {Qs : Set Box} (hQ : IsRankOne J Qs)
    {Cs : Finset TriTile} (hbox : ∀ R ∈ Cs, R.box ∈ Qs) {Cand : ℤ × ℤ → ℝ → Prop} {ts : List TopSel}
    (hsel : IsGreedyTopH Box.hull (AdmH Box.hull fatRad J) Cand Cs ts) {f : ℝ} (hf : 1 ≤ f) (V₀ : TopSel)
    {V V' : TopSel} (hV : V ∈ ts) (hV' : V' ∈ ts) (hne : V ≠ V') (h0 : V.W.1 ≤ V₀.W.1) (h0' : V'.W.1 ≤ V₀.W.1)
    (hs : (plusShell f V₀.W V₀.ξ ∩ plusShell f V.W V.ξ).Nonempty)
    (hs' : (plusShell f V₀.W V₀.ξ ∩ plusShell f V'.W V'.ξ).Nonempty) :
    Disjoint (dyadicInt V.W.1 V.W.2) (dyadicInt V'.W.1 V'.W.2) :=
  top_separation_pair_H (by unfold fatRad; norm_num) hJ hQ hbox hsel hf V₀ hV hV' hne h0 h0' hs hs'

end PrimeBHT.TimeFrequency.X2
