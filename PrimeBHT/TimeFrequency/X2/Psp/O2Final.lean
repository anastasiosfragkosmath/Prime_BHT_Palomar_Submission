module

public import PrimeBHT.TimeFrequency.X2.Psp.O2Weight
public import PrimeBHT.TimeFrequency.X2.Psp.O2bWeight
public import PrimeBHT.TimeFrequency.X2.Psp.TreeConv

/-!
# X2, V13 O2 (j): assembly (fine part with the energy `engTop`, the split `T_m(F - G)`, ...)

* `endpoint_estimates`: for an endpoint `x ∈ ∂Ẽ_τ` of a part of a good tree (overlapping in the slot `k`), the growth
  `‖S_τ F(b)‖ ≤ polyS e ⟨(b - x)/2^τ⟩^{N'}` and the coefficient bound `‖c_τ(x)‖ ≤ coefConst e`, `e = engTop` (`poly_growth_S`, `yNorm_ovCoef_le`);
* `fine_bound_ovG`: the fine part `D_fine` of `T_σ F - ovG F` against the layer kernel is `≤ C e a` (`fine_bound_abstract`, `sum_endpoint_le_ovFactor`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform ContDiff Real Convolution
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-- a tile near an endpoint of `Ẽ_τ` -/
theorem endpoint_tile {J : ℕ} (hJ2 : 2 ≤ J) {TA : Finset TriTile} {W : ℤ × ℤ} {τ : ℤ}
    (hlat : ∀ R ∈ TA, (J : ℤ) ∣ R.box.scale - τ) {x : ℝ} (hx : x ∈ bdryEnds TA W τ) :
    ∃ R ∈ TA, R.box.scale ≤ τ ∧ (J : ℤ) ∣ τ - R.box.scale ∧ ∃ z ∈ R.I, |x - z| ≤ 3 * (2 : ℝ) ^ τ := by
  have hp := zpow_two_pos τ
  obtain ⟨v, hv, hxv⟩ : ∃ v : ℤ, v ∈ eTilKeys TA W τ ∧ (x = (2 : ℝ) ^ τ * v ∨ x = (2 : ℝ) ^ τ * ((v : ℝ) + 1)) := by
    rcases Finset.mem_union.1 hx with h1 | h1
    · obtain ⟨v, hv, -, hve⟩ := mem_leftEndsOf.1 h1
      exact ⟨v, mem_eTilKeysF.1 hv, Or.inl hve.symm⟩
    · obtain ⟨v, hv, -, hve⟩ := mem_rightEndsOf.1 h1
      exact ⟨v, mem_eTilKeysF.1 hv, Or.inr hve.symm⟩
  have hne : (dilate 3 (dyadicInt τ v) ∩ eTil TA W τ).Nonempty := by
    refine ⟨(2 : ℝ) ^ τ * v, dyadicInt_subset_dilate (by norm_num) τ v (mem_dyadicInt_left τ v), ?_⟩
    unfold eTil
    exact Set.mem_biUnion hv (mem_dyadicInt_left τ v)
  obtain ⟨R, hR, hRs, hRI⟩ := exists_tile_near hJ2 hlat hne
  have hz : (2 : ℝ) ^ R.box.scale * R.pos ∈ R.I := by unfold TriTile.I; exact mem_dyadicInt_left _ _
  have hz5 := (mem_dilate_dyadicInt_iff 5 τ v _).1 (hRI hz)
  obtain ⟨hz1, hz2⟩ := hz5
  have hxz : |x - (2 : ℝ) ^ R.box.scale * R.pos| ≤ 3 * (2 : ℝ) ^ τ := by
    rw [abs_le]
    rcases hxv with rfl | rfl <;> constructor <;> nlinarith
  have hJ' : (J : ℤ) ∣ τ - R.box.scale := by
    have := dvd_neg.2 (hlat R hR)
    simpa using this
  exact ⟨R, hR, hRs, hJ', _, hz, hxz⟩

section Estimates

variable {P : ℕ} [NeZero P]

/-- **Growth and coefficient at an endpoint, from the energy.** -/
theorem endpoint_estimates {𝔭 : Params} (h𝔭 : 𝔭.Admissible) {η' : ℝ → ℝ} (hη' : IsEtaCut 𝔭 η') {k : Fin 3}
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) {TA Cs : Finset TriTile}
    (hsub : TA ⊆ Cs) {t : Top} (hov : ∀ R ∈ TA, IsOvSlot t k R.box) {τ : ℤ}
    (hlat : ∀ R ∈ TA, (𝔭.J : ℤ) ∣ R.box.scale - τ) {x : ℝ} (hx : x ∈ bdryEnds TA t.1 τ) {e : ℝ}
    (he : engTop 𝔭 2 k F Cs 2 = ENNReal.ofReal e) (he0 : 0 ≤ e) :
    (∀ b, yNorm 2 (ovS 𝔭.J (t.2 * freqDir k) τ F b) ≤ (polyS 𝔭 2 * e) * jb ((b - x) / (2 : ℝ) ^ τ) ^ (𝔭.N : ℝ)) ∧
      yNorm 2 (ovCoef 𝔭.J (t.2 * freqDir k) F τ x) ≤ coefConst 𝔭 2 * e := by
  have hJ2 : 2 ≤ 𝔭.J := by have := h𝔭.1; unfold jFloor at this; omega
  obtain ⟨R, hR, hRs, hJ', z, hz, hxz⟩ := endpoint_tile hJ2 hlat hx
  refine ⟨fun b => ?_, ?_⟩
  · have := poly_growth_S h𝔭 hη' (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 : ℝ) < 2) hF hFb (hsub hR)
      (hov R hR) hRs hJ' (Nat.zero_le _) hz hxz he he0 b
    rw [Real.rpow_natCast]
    linarith
  · exact yNorm_ovCoef_le h𝔭 hη' (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 : ℝ) < 2) hF hFb (hsub hR)
      (hov R hR) hRs hJ' hz hxz he he0

/-- The constant of the fine part. -/
def Cfine (𝔭 : Params) : ℝ :=
  endC3 𝔭.D 𝔭.C * 2 ^ 𝔭.D *
      (2 * endQ 𝔭.J 𝔭.D (𝔭.tree.N + 2 * (𝔭.D + 3)) (𝔭.tree.N : ℝ) * ((2 : ℝ) ^ ((𝔭.J : ℤ) + 1)) ^ 2 + 1) *
    (polyS 𝔭.tree 2 + coefConst 𝔭.tree 2) * ((2 : ℝ) ^ 101 * (3 / 2) ^ 𝔭.D)

/-- **The fine part of `T_σ F - ovG F` against the layer kernel** (MTT2 (d5), (d6)): `≤ C e a`. -/
theorem fine_bound_ovG {𝔭 : Params} (h𝔭 : 𝔭.Admissible) (h𝔭t : 𝔭.tree.Admissible) {η' : ℝ → ℝ}
    (hη' : IsEtaCut 𝔭.tree η') {k : Fin 3} {F : ℝ → ZMod P → ℂ} (hF : Measurable F)
    (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) {Tr TA : Finset TriTile} (hsub : TA ⊆ Tr) {t : Top}
    (hov : ∀ R ∈ TA, IsOvSlot t k R.box) {s₀ : ℤ} (hs₀ : ∀ R ∈ TA, (𝔭.J : ℤ) ∣ R.box.scale - s₀) {σ : ℤ}
    {c : ℝ} {m : ℝ → ℂ} (hm : InMult 𝔭 σ c m) (hθ : |t.2 * freqDir k - c| ≤ 13 / 8 * (2 : ℝ) ^ (-σ))
    (hσL : σ ∈ ovScales 𝔭.J s₀ (-((TA.sup (fun R => R.box.scale.natAbs) : ℕ) : ℤ) - 1) t.1.1) {e : ℝ}
    (he : engTop 𝔭.tree 2 k F Tr 2 = ENNReal.ofReal e) (he0 : 0 ≤ e) {v : ℤ} {S : Finset ℤ}
    (_hS1 : ∀ σ' ∈ S, (𝔭.J : ℤ) ∣ σ' - σ)
    (hS2 : ∀ σ' : ℤ, (𝔭.J : ℤ) ∣ σ' - σ → (bdryEnds TA t.1 σ').Nonempty → σ' ∈ S) {x₀ : ℝ}
    (hx₀ : x₀ ∈ dyadicInt σ v) :
    yNorm 2 (fun y => ∫ z, 𝓕⁻ m (x₀ - z) *
        Dfine 𝔭.J s₀ (-((TA.sup (fun R => R.box.scale.natAbs) : ℕ) : ℤ) - 1) TA t.1 (t.2 * freqDir k) F
          (fun τ x => ovCoef 𝔭.J (t.2 * freqDir k) F τ x) (fun τ x => -ovCoef 𝔭.J (t.2 * freqDir k) F τ x) σ z y) ≤
      Cfine 𝔭 * e * (((2 : ℝ) ^ σ)⁻¹ * ∫ y, ovWeight 2 σ v y * muW 𝔭.J S (bdryEnds TA t.1) σ y) := by
  obtain ⟨hD, hβ, hC⟩ : 400 ≤ 𝔭.D ∧ 𝔭.β ≤ 11 / 4 ∧ 1 ≤ 𝔭.C := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h𝔭
    exact ⟨by unfold classFloor at h3; omega, h7, h8⟩
  have hJ : 0 < 𝔭.J := by have := h𝔭.1; unfold jFloor at this; omega
  have hC0 : 0 ≤ 𝔭.C := by linarith
  set lo : ℤ := -((TA.sup (fun R => R.box.scale.natAbs) : ℕ) : ℤ) - 1 with hlo
  set θ : ℝ := t.2 * freqDir k with hθdef
  set Lm := (ovScales 𝔭.J s₀ lo t.1.1).filter (fun τ => τ < σ) with hLm
  have hsym := sym0_of_inMult hm hβ hθ
  obtain ⟨B, hB⟩ := hFb
  have hBF : ∀ z y, ‖F z y‖ ≤ (P : ℝ) ^ (2 : ℝ)⁻¹ * B := fun z y => coord_bound_o2 hB z y
  set M := 𝔭.D with hM
  set q : ℕ := 𝔭.tree.N + 2 * (𝔭.D + 3) with hq
  have hqN : (𝔭.tree.N : ℝ) + 2 * ((M : ℝ) + 3) ≤ (q : ℝ) := by rw [hq]; push_cast; linarith
  have hτ : ∀ τ ∈ Lm, (𝔭.J : ℤ) ∣ τ - s₀ ∧ τ < σ := fun τ hτ => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hτ
    exact ⟨(mem_ovScales.1 h1).2, h2⟩
  have hσd : (𝔭.J : ℤ) ∣ σ - s₀ := (mem_ovScales.1 hσL).2
  have hτσ : ∀ τ ∈ Lm, τ + (𝔭.J : ℤ) ≤ σ := fun τ hτ' => by
    obtain ⟨hd, hlt⟩ := hτ τ hτ'
    have : (𝔭.J : ℤ) ∣ σ - τ := by
      have : σ - τ = (σ - s₀) - (τ - s₀) := by ring
      rw [this]; exact dvd_sub hσd hd
    obtain ⟨i, hi⟩ := this
    have hJ' : (0 : ℤ) < 𝔭.J := by exact_mod_cast hJ
    have hi0 : 0 < i := by by_contra h; push Not at h; nlinarith
    nlinarith
  have hτσd : ∀ τ ∈ Lm, (𝔭.J : ℤ) ∣ τ - σ := fun τ hτ' => by
    have h1 := (hτ τ hτ').1
    have h2 : τ - σ = (τ - s₀) - (σ - s₀) := by ring
    rw [h2]; exact dvd_sub h1 hσd
  have hlatτ : ∀ τ ∈ Lm, ∀ R ∈ TA, (𝔭.tree.J : ℤ) ∣ R.box.scale - τ := fun τ hτ' R hR => by
    obtain ⟨hd, -⟩ := hτ τ hτ'
    rw [Params.tree_J]
    have : R.box.scale - τ = (R.box.scale - s₀) - (τ - s₀) := by ring
    rw [this]; exact dvd_sub (hs₀ R hR) hd
  have hest := fun τ (hτ' : τ ∈ Lm) x (hx : x ∈ bdryEnds TA t.1 τ) =>
    endpoint_estimates h𝔭t hη' hF ⟨B, hB⟩ hsub hov (hlatτ τ hτ') hx he he0
  have hfine := fine_bound_abstract (J := 𝔭.J) hJ (s₀ := s₀) (lo := lo) TA t.1 (θ := θ) hF hBF (σ := σ) (M := M)
    (C₀ := 𝔭.C) (m := m) hsym (Ag := polyS 𝔭.tree 2 * e) (N := (𝔭.tree.N : ℝ)) (A₁ := coefConst 𝔭.tree 2 * e)
    (by have := polyS_nonneg 𝔭.tree 2; positivity) (by positivity)
    (by have := coefConst_nonneg 𝔭.tree 2; positivity) (q := q) hqN hτσ
    (fun τ hτ' x hx => by
      have := (hest τ hτ' x hx).1
      simpa [Params.tree_J] using this)
    (fun τ hτ' x hx => by
      have := (hest τ hτ' x hx).2
      simpa [Params.tree_J] using this) x₀
  refine hfine.trans ?_
  -- compare with `a`
  set Cend := endC3 M 𝔭.C * 2 ^ M * (2 * endQ 𝔭.J M q (𝔭.tree.N : ℝ) * ((2 : ℝ) ^ ((𝔭.J : ℤ) + 1)) ^ 2 + 1) with hCend
  have hCend0 : 0 ≤ Cend := by
    have := endC3_nonneg M hC0
    have := endQ_nonneg 𝔭.J M q (N := (𝔭.tree.N : ℝ))
    rw [hCend]; positivity
  have hsum := fine_sum_le (J := 𝔭.J) hJ S (bdryEnds TA t.1) σ v Lm hτσ
    (fun τ hτ' hne => hS2 τ (hτσd τ hτ') hne)
    (M := M) (by omega) hx₀ (Cc := Cend * (polyS 𝔭.tree 2 * e + coefConst 𝔭.tree 2 * e)) (by
      have := polyS_nonneg 𝔭.tree 2; have := coefConst_nonneg 𝔭.tree 2; positivity)
  refine le_of_eq_of_le ?_ (hsum.trans (le_of_eq ?_))
  · refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  · unfold Cfine
    rw [← hM, ← hq]
    ring

end Estimates

/-! ## The cutoff `χ̃_σ` -/

theorem measurable_layerCut {𝔭 : Params} {η : ℝ → ℝ} (hη : IsEtaCut 𝔭 η) (TA : Finset TriTile) (σ : ℤ) :
    Measurable (layerCut η TA σ) := by
  unfold layerCut
  exact Finset.measurable_sum _ fun R _ => (continuous_tileCutoff hη σ R.pos).measurable

end PrimeBHT.TimeFrequency.X2
