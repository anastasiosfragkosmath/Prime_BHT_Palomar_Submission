module

public import PrimeBHT.TimeFrequency.X2.Psp.Defs
public import PrimeBHT.TimeFrequency.X2.TopSelect
public import PrimeBHT.TimeFrequency.X2.GoodTree

/-!
# X2, V13: the lacunary split of a good tree (S-1 .. S-4)

`docs/audits/X2-V13-route-check.md` §2.4 / §3 with the REV3 constants (`hullDil = 128`, `hullConst = 256`, `ovThr = 13/4`,
`jFloor = 16`, `β ≤ 11/4`).

* `two_le_card_slotType` (S-1): at least two slots of a box are lacunary (field (g));
* `isGoodTree_treePart`, `isGoodTree_filter_box` (G-7, MTT2 Lemma 4.14 "heritage");
* `isLacunary_treePart` (S-2): the part `T_A` is `k`-lacunary for `k ∈ A` (fields (a), (e), (h); `2^J > 4108`);
* S-3: `lacSym_eq_one_of_piece` (the Fourier support of a lacunary piece lies in the annulus
  `{1/4 - δ ≤ |ξ - θ_k|/ℓ ≤ 2 hullConst + β/2 + δ}` where `lacSym = 1`) and `lacSym_disjoint` (supports of `lacSym` of
  scales `J` apart are disjoint, `2^J > 4(2 hullConst + 3)`);
* S-4: `lowSym_eq_one_of_piece` (the Fourier support of an overlapping piece lies in `{|ξ - θ_k| ≤ (3 + δ)ℓ}` where
  `lowSym = 1`).

**Corrections to the route check** (none changes `IsRankOne`, `hullDil`, `ovThr` or `jFloor`): (i) `two_le_card_slotType`
needs only `B ∈ Qs` (field (g)), not `t.2 ∈ B.hull`; (ii) with `hullConst = 256` the numerology is S-2: `ℓ'/ℓ < 4108 <
2^J` (the route check's `16 H` with `H = 128`); S-3 upper edge `2 hullConst + 4 = 516`, lower edge `3/16`;
`jFloor = 16` suffices everywhere (`2^J > 4108`, `2^J > 8·517`), `jFloor ≥ 13` would do.
-/

@[expose] public noncomputable section

open MeasureTheory
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-! ## Membership in dilates of the slot intervals -/

theorem mem_dilate_ω_iff (B : Box) (k : Fin 3) (C x : ℝ) :
    x ∈ dilate C (B.ω k) ↔
      B.centre k - C * (2 : ℝ) ^ (-B.scale) / 2 ≤ x ∧ x < B.centre k + C * (2 : ℝ) ^ (-B.scale) / 2 := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
  have hlt : B.centre k - (2 : ℝ) ^ (-B.scale) / 2 < B.centre k + (2 : ℝ) ^ (-B.scale) / 2 := by linarith
  unfold Box.ω
  rw [dilate_Ico hlt, Set.mem_Ico]
  have e1 : (B.centre k - (2 : ℝ) ^ (-B.scale) / 2 + (B.centre k + (2 : ℝ) ^ (-B.scale) / 2)) / 2 =
      B.centre k := by ring
  have e2 : (B.centre k + (2 : ℝ) ^ (-B.scale) / 2) - (B.centre k - (2 : ℝ) ^ (-B.scale) / 2) =
      (2 : ℝ) ^ (-B.scale) := by ring
  rw [e1, e2]

theorem ωn_lt (B : Box) (k : Fin 3) :
    (B.centre k - (2 : ℝ) ^ (-B.scale) / 2) / freqDir k < (B.centre k + (2 : ℝ) ^ (-B.scale) / 2) / freqDir k :=
  div_lt_div_of_pos_right (by have : (0 : ℝ) < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _; linarith)
    (freqDir_pos' k)

theorem mem_dilate_ωn_iff (B : Box) (k : Fin 3) (C x : ℝ) :
    x ∈ dilate C (B.ωn k) ↔
      B.centre k / freqDir k - C * (2 : ℝ) ^ (-B.scale) / (2 * freqDir k) ≤ x ∧
        x < B.centre k / freqDir k + C * (2 : ℝ) ^ (-B.scale) / (2 * freqDir k) := by
  have hd := freqDir_pos' k
  have hdn : freqDir k ≠ 0 := hd.ne'
  unfold Box.ωn
  rw [dilate_Ico (ωn_lt B k), Set.mem_Ico]
  have e1 : ((B.centre k - (2 : ℝ) ^ (-B.scale) / 2) / freqDir k +
      (B.centre k + (2 : ℝ) ^ (-B.scale) / 2) / freqDir k) / 2 = B.centre k / freqDir k := by
    field_simp; ring
  have e2 : (B.centre k + (2 : ℝ) ^ (-B.scale) / 2) / freqDir k -
      (B.centre k - (2 : ℝ) ^ (-B.scale) / 2) / freqDir k = (2 : ℝ) ^ (-B.scale) / freqDir k := by
    field_simp; ring
  have e3 : C * ((2 : ℝ) ^ (-B.scale) / freqDir k) / 2 = C * (2 : ℝ) ^ (-B.scale) / (2 * freqDir k) := by
    field_simp
  rw [e1, e2, e3]

theorem ωn_dilate_mono {C C' : ℝ} (h : C ≤ C') (B : Box) (k : Fin 3) :
    dilate C (B.ωn k) ⊆ dilate C' (B.ωn k) := by
  unfold Box.ωn
  exact dilate_Ico_mono (ωn_lt B k) h

/-! ## S-1: at least two lacunary slots -/

/-- **S-1**: a box of a rank-1 set has at least two lacunary slots, for every top frequency (the normalized
`4`-dilates of the three slot intervals are pairwise disjoint, field (g), and `(13/4) ⊆ 4`). -/
theorem two_le_card_slotType {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {B : Box} (hB : B ∈ Qs) (t : Top) :
    2 ≤ (slotType t B).card := by
  obtain ⟨-, -, -, -, -, -, -, hg, -⟩ := hQ
  have hO : ∀ k k' : Fin 3, IsOvSlot t k B → IsOvSlot t k' B → k = k' := by
    intro k k' hk hk'
    by_contra hne
    have h4 : ∀ j, IsOvSlot t j B → t.2 ∈ dilate 4 (B.ωn j) := fun j hj =>
      ωn_dilate_mono (by unfold ovThr; norm_num) B j hj
    exact Set.disjoint_left.1 (hg B hB k k' hne) (h4 k hk) (h4 k' hk')
  have hcard : (Finset.univ.filter (fun k => IsOvSlot t k B)).card ≤ 1 :=
    Finset.card_le_one.2 fun a ha b hb => hO a b (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2
  have h3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 3)))
    (fun k => IsOvSlot t k B)
  simp only [Finset.card_univ, Fintype.card_fin] at h3
  unfold slotType
  omega

/-! ## G-7: heritage -/

/-- A sub-collection defined by a property of the BOX is good again (`E_{Q, T'} = E_{Q, T}` for its boxes). -/
theorem isGoodTree_filter_box {Tr : Finset TriTile} {t : Top} (h : IsGoodTree Tr t) (P : Box → Prop) :
    IsGoodTree (Tr.filter (fun R => P R.box)) t := by
  obtain ⟨hT, hb, hc⟩ := h
  have hmem : ∀ R, R ∈ Tr.filter (fun R => P R.box) → R ∈ Tr ∧ P R.box := fun R hR => Finset.mem_filter.1 hR
  refine ⟨fun R hR => hT R (hmem R hR).1, fun R hR R' hR' hs => hb R (hmem R hR).1 R' (hmem R' hR').1 hs, ?_⟩
  intro R hR R' hR' hsc
  have e : ∀ R₀ ∈ Tr.filter (fun R => P R.box),
      (Tr.filter (fun R => P R.box)).filter (fun R'' => R''.box = R₀.box) =
        Tr.filter (fun R'' => R''.box = R₀.box) := by
    intro R₀ hR₀
    ext R''
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, h3 ▸ (hmem R₀ hR₀).2⟩, h3⟩
  rw [e R hR, e R' hR']
  exact hc R (hmem R hR).1 R' (hmem R' hR').1 hsc

/-- **G-7 (`heritage`, MTT2 Lemma 4.14)**: every part `T_A` of a good tree is good (same top, same `E_{Q,T}`). -/
theorem isGoodTree_treePart {Tr : Finset TriTile} {t : Top} (h : IsGoodTree Tr t) (A : Finset (Fin 3)) :
    IsGoodTree (treePart Tr t A) t := by
  have := isGoodTree_filter_box h (fun B => slotType t B = A)
  unfold treePart
  convert this

/-! ## Hull bounds -/

theorem psp_centre_mem_hull (B : Box) (k : Fin 3) : B.centre k / freqDir k ∈ B.hull := by
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
  refine mem_hull_of_near B k ?_
  rw [sub_self, abs_zero]
  have := freqDir_pos' k
  unfold hullDil
  positivity

/-- For `ξ ∈ hull B` (field (h)): `|ξ - c_k/f_k| ≤ hullConst ℓ`. -/
theorem psp_hull_pt_bound {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {B : Box} (hB : B ∈ Qs) (k : Fin 3)
    {x : ℝ} (hx : x ∈ B.hull) : |x - B.centre k / freqDir k| ≤ hullConst * (2 : ℝ) ^ (-B.scale) := by
  obtain ⟨-, -, -, -, -, -, -, -, hh⟩ := hQ
  exact hh B hB x hx _ (psp_centre_mem_hull B k)

/-- `|θ_k - c_k| ≤ 2 hullConst ℓ` for the slot frequency `θ_k = ξ_T f_k` of `ξ_T ∈ hull B`. -/
theorem abs_theta_sub_centre_le {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {B : Box} (hB : B ∈ Qs) (k : Fin 3)
    {ξ : ℝ} (hξ : ξ ∈ B.hull) :
    |ξ * freqDir k - B.centre k| ≤ 2 * hullConst * (2 : ℝ) ^ (-B.scale) := by
  have hd := freqDir_pos' k
  have hd2 := freqDir_le_two' k
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
  have h := psp_hull_pt_bound hQ hB k hξ
  have e : ξ * freqDir k - B.centre k = freqDir k * (ξ - B.centre k / freqDir k) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hd]
  have hH : (0 : ℝ) ≤ hullConst := by unfold hullConst; norm_num
  calc freqDir k * |ξ - B.centre k / freqDir k| ≤ 2 * (hullConst * (2 : ℝ) ^ (-B.scale)) :=
        mul_le_mul hd2 h (abs_nonneg _) (by norm_num)
    _ = _ := by ring

/-- The overlapping slot: `|θ_k - c_k| ≤ (13/8) ℓ`. -/
theorem abs_theta_sub_centre_le_of_ov {B : Box} {k : Fin 3} {t : Top} (h : IsOvSlot t k B) :
    |t.2 * freqDir k - B.centre k| ≤ 13 / 8 * (2 : ℝ) ^ (-B.scale) := by
  have hd := freqDir_pos' k
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
  have h1 := abs_sub_centre_le_of_mem_dilate h
  have e : t.2 * freqDir k - B.centre k = freqDir k * (t.2 - B.centre k / freqDir k) := by field_simp
  rw [e, abs_mul, abs_of_pos hd]
  calc freqDir k * |t.2 - B.centre k / freqDir k| ≤ freqDir k * (13 / 8 * ((2 : ℝ) ^ (-B.scale) / freqDir k)) :=
        mul_le_mul_of_nonneg_left h1 hd.le
    _ = _ := by field_simp

/-- The lacunary slot: `|θ_k - c_k| ≥ (13/8) ℓ`. -/
theorem le_abs_theta_sub_centre_of_not_ov {B : Box} {k : Fin 3} {t : Top} (h : ¬ IsOvSlot t k B) :
    13 / 8 * (2 : ℝ) ^ (-B.scale) ≤ |t.2 * freqDir k - B.centre k| := by
  have hd := freqDir_pos' k
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
  unfold IsOvSlot ovThr at h
  rw [mem_dilate_ωn_iff, not_and_or, not_le, not_lt] at h
  rw [le_abs]
  rcases h with h | h
  · right
    have h2 : t.2 * freqDir k < B.centre k - 13 / 8 * (2 : ℝ) ^ (-B.scale) := by
      have e : (B.centre k / freqDir k - 13 / 4 * (2 : ℝ) ^ (-B.scale) / (2 * freqDir k)) * freqDir k =
          B.centre k - 13 / 8 * (2 : ℝ) ^ (-B.scale) := by field_simp; ring
      rw [← e]
      exact mul_lt_mul_of_pos_right h hd
    linarith
  · left
    have h2 : B.centre k + 13 / 8 * (2 : ℝ) ^ (-B.scale) ≤ t.2 * freqDir k := by
      have e : (B.centre k / freqDir k + 13 / 4 * (2 : ℝ) ^ (-B.scale) / (2 * freqDir k)) * freqDir k =
          B.centre k + 13 / 8 * (2 : ℝ) ^ (-B.scale) := by field_simp; ring
      rw [← e]
      exact mul_le_mul_of_nonneg_right h hd.le
    linarith

/-! ## S-2: the part `T_A` is `k`-lacunary -/

theorem two_pow_J_le {J : ℕ} (hJ : jFloor ≤ J) : (65536 : ℝ) ≤ (2 : ℝ) ^ J := by
  have h16 : 16 ≤ J := hJ
  calc (65536 : ℝ) = 2 ^ 16 := by norm_num
    _ ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) h16

theorem zpow_gap_le' {J : ℕ} {a b : ℤ} (h : b + (J : ℤ) ≤ a) :
    (2 : ℝ) ^ J * (2 : ℝ) ^ (-a) ≤ (2 : ℝ) ^ (-b) := by
  have h1 : (J : ℤ) ≤ a - b := by omega
  have h4 : (2 : ℝ) ^ (-b) = (2 : ℝ) ^ (a - b) * (2 : ℝ) ^ (-a) := by
    rw [← zpow_add₀ (by norm_num)]; congr 1; ring
  have h3 : (2 : ℝ) ^ J ≤ (2 : ℝ) ^ (a - b) := by
    rw [← zpow_natCast]
    exact zpow_le_zpow_right₀ (by norm_num) h1
  rw [h4]
  have : (0 : ℝ) < (2 : ℝ) ^ (-a) := zpow_pos (by norm_num) _
  nlinarith

theorem zpow_gap_le {J : ℕ} {a b : ℤ} (hdvd : (J : ℤ) ∣ a - b) (hlt : b < a) :
    (2 : ℝ) ^ J * (2 : ℝ) ^ (-a) ≤ (2 : ℝ) ^ (-b) :=
  zpow_gap_le' (by have := Int.le_of_dvd (by omega) hdvd; omega)

/-- A finer box `B` (`ξ ∈ hull B`) and a coarser box `B'` (`ξ_T` lacunary for `B'` in slot `k`) have disjoint
`3ω_k`: otherwise `ℓ'/8 < |z - θ_k| ≤ 513.5 ℓ`, i.e. `ℓ'/ℓ < 4108 < 2^J`. -/
theorem not_mem_both_dilate {J : ℕ} (hJ : jFloor ≤ J) {Qs : Set Box} (hQ : IsRankOne J Qs) {B B' : Box}
    (hB : B ∈ Qs) (hB' : B' ∈ Qs) (hlt : B'.scale < B.scale) {t : Top} (hξ : t.2 ∈ B.hull) {k : Fin 3}
    (hk' : ¬ IsOvSlot t k B') {z : ℝ} (hz : z ∈ dilate 3 (B.ω k)) (hz' : z ∈ dilate 3 (B'.ω k)) : False := by
  have hdvd := hQ.1 B hB B' hB'
  have hgap := zpow_gap_le hdvd hlt
  have hJ2 := two_pow_J_le hJ
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
  have h1 := abs_theta_sub_centre_le hQ hB k hξ
  have h2 := le_abs_theta_sub_centre_of_not_ov hk'
  rw [mem_dilate_ω_iff] at hz hz'
  have hH : hullConst = 256 := by unfold hullConst; norm_num
  rw [hH] at h1
  set ℓ : ℝ := (2 : ℝ) ^ (-B.scale)
  set ℓ' : ℝ := (2 : ℝ) ^ (-B'.scale)
  set θ : ℝ := t.2 * freqDir k
  rw [abs_le] at h1
  have h3 : ℓ' / 8 ≤ |z - θ| := by
    rcases le_abs.1 h2 with h | h
    · -- `13/8 ℓ' ≤ θ - c'`
      rw [le_abs]; right; linarith [hz'.2]
    · rw [le_abs]; left; linarith [hz'.1]
  have h4 : |z - θ| ≤ 513.5 * ℓ := by
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2, h1.1, h1.2]
  have h5 : ℓ' ≤ 4108 * ℓ := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hJ2 hl.le]

/-- **S-2**: for `k ∈ A` the part `T_A` of a tree of rank-1 boxes is `k`-lacunary.  (Fields (a), (e), (h) of
`IsRankOne`, `jFloor ≤ J`.) -/
theorem isLacunary_treePart {J : ℕ} (hJ : jFloor ≤ J) {Qs : Set Box} (hQ : IsRankOne J Qs)
    {Tr : Finset TriTile} {t : Top} (hT : IsTree Tr t) (hbox : ∀ R ∈ Tr, R.box ∈ Qs)
    {A : Finset (Fin 3)} {k : Fin 3} (hk : k ∈ A) : IsLacunary k (treePart Tr t A) := by
  intro R hR R' hR' hne
  obtain ⟨hRT, hRA⟩ := mem_treePart.1 hR
  obtain ⟨hR'T, hR'A⟩ := mem_treePart.1 hR'
  have hk1 : ¬ IsOvSlot t k R.box := mem_slotType.1 (hRA ▸ hk)
  have hk2 : ¬ IsOvSlot t k R'.box := mem_slotType.1 (hR'A ▸ hk)
  rcases lt_trichotomy R.box.scale R'.box.scale with hlt | heq | hgt
  · exact Set.disjoint_left.2 fun z hz hz' =>
      not_mem_both_dilate hJ hQ (hbox R' hR'T) (hbox R hRT) hlt (hT R' hR'T).2 hk1 hz' hz
  · exact absurd (by rw [IsTree.box_eq_of_scale_eq hQ hT hbox R hRT R' hR'T heq]) hne
  · exact Set.disjoint_left.2 fun z hz hz' =>
      not_mem_both_dilate hJ hQ (hbox R hRT) (hbox R' hR'T) hgt (hT R hRT).2 hk2 hz hz'

/-! ## S-3, S-4: the symbols are `1` on the Fourier supports -/

theorem Params.Admissible.delta_le_sixteenth {𝔭 : Params} (h : 𝔭.Admissible) : 𝔭.δ ≤ 1 / 16 := by
  obtain ⟨hJ, -, -, -, hδ, -⟩ := h
  have h16 : (16 : ℝ) ≤ 𝔭.J := by exact_mod_cast hJ
  refine hδ.trans ?_
  have : (2 : ℝ) ^ (-(3 * (𝔭.J : ℝ) / 2)) ≤ (2 : ℝ) ^ (-(4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  refine this.trans (le_of_eq ?_)
  rw [Real.rpow_neg (by norm_num)]
  norm_num

theorem Params.Admissible.beta_le {𝔭 : Params} (h : 𝔭.Admissible) : 𝔭.β ≤ 11 / 4 := h.2.2.2.2.2.2.1

/-- **S-3 (annulus)**: for `k` lacunary at the box `B` (`ξ_T ∈ hull B`) and a frequency `ζ` within `(β/2 + δ)ℓ` of the
centre `c_k` (the Fourier support of a piece `ψ T_m F`, `m ∈ M_{ω_k}(𝔭)`), `3/16 ℓ ≤ |ζ - θ_k| ≤ lacHi ℓ`, hence
`lacSym θ_k s ζ = 1` at the box scale `s = B.scale`. -/
theorem lacSym_eq_one_of_piece {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {B : Box} (hB : B ∈ Qs) {t : Top}
    (hξ : t.2 ∈ B.hull) {k : Fin 3} (hk : ¬ IsOvSlot t k B) {𝔭 : Params} (h𝔭 : 𝔭.Admissible) {ζ : ℝ}
    (hζ : |ζ - B.centre k| ≤ (𝔭.β / 2 + 𝔭.δ) * (2 : ℝ) ^ (-B.scale)) :
    lacSym (t.2 * freqDir k) B.scale ζ = 1 := by
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
  have h1 := abs_theta_sub_centre_le hQ hB k hξ
  have h2 := le_abs_theta_sub_centre_of_not_ov hk
  have hδ := h𝔭.delta_le_sixteenth
  have hβ := h𝔭.beta_le
  have hH : hullConst = 256 := by unfold hullConst; norm_num
  rw [hH] at h1
  set ℓ : ℝ := (2 : ℝ) ^ (-B.scale)
  apply lacSym_eq_one
  · -- lower edge
    have : 3 / 16 * ℓ ≤ |ζ - t.2 * freqDir k| := by
      have h3 : |t.2 * freqDir k - B.centre k| ≤ |ζ - t.2 * freqDir k| + |ζ - B.centre k| := by
        calc |t.2 * freqDir k - B.centre k| = |(ζ - B.centre k) - (ζ - t.2 * freqDir k)| := by ring_nf
          _ ≤ |ζ - B.centre k| + |ζ - t.2 * freqDir k| := abs_sub _ _
          _ = _ := add_comm _ _
      nlinarith
    exact this
  · -- upper edge
    rw [lacHi_eq]
    have h3 : |ζ - t.2 * freqDir k| ≤ |ζ - B.centre k| + |t.2 * freqDir k - B.centre k| := by
      calc |ζ - t.2 * freqDir k| = |(ζ - B.centre k) - (t.2 * freqDir k - B.centre k)| := by ring_nf
        _ ≤ _ := abs_sub _ _
    nlinarith

/-- **S-3 (disjoint supports)**: for scales `σ + J ≤ σ'` the supports of `lacSym θ σ` and `lacSym θ σ'` are disjoint
(`2^J > 8 lacHi0`, i.e. `2^J > 4136`). -/
theorem lacSym_disjoint {J : ℕ} (hJ : jFloor ≤ J) {θ : ℝ} {σ σ' : ℤ} (h : σ + (J : ℤ) ≤ σ') (ξ : ℝ) :
    lacSym θ σ ξ = 0 ∨ lacSym θ σ' ξ = 0 := by
  have hgap := zpow_gap_le' (J := J) (a := σ') (b := σ) h
  have hJ2 := two_pow_J_le hJ
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-σ) := zpow_pos (by norm_num) _
  have hl' : (0 : ℝ) < (2 : ℝ) ^ (-σ') := zpow_pos (by norm_num) _
  by_cases hge : lacHi0 * (2 : ℝ) ^ (-σ') ≤ |ξ - θ|
  · exact Or.inr (lacSym_eq_zero_of_ge hge)
  · left
    apply lacSym_eq_zero_of_le
    rw [not_le, lacHi0_eq] at hge
    nlinarith

/-- Distinct scales of boxes of a rank-1 set differ by at least `J`: the supports of `lacSym` at two different box
scales are disjoint. -/
theorem lacSym_disjoint_scales {J : ℕ} (hJ : jFloor ≤ J) {Qs : Set Box} (hQ : IsRankOne J Qs) {B B' : Box}
    (hB : B ∈ Qs) (hB' : B' ∈ Qs) (hne : B.scale ≠ B'.scale) (θ ξ : ℝ) :
    lacSym θ B.scale ξ = 0 ∨ lacSym θ B'.scale ξ = 0 := by
  have hdvd := hQ.1 B hB B' hB'
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact lacSym_disjoint hJ (by have := Int.le_of_dvd (by omega) (by simpa using hdvd.neg_right : (J : ℤ) ∣ B'.scale - B.scale)
                                 omega) ξ
  · exact (lacSym_disjoint hJ (by have := Int.le_of_dvd (by omega) hdvd; omega) ξ).symm

end PrimeBHT.TimeFrequency.X2
