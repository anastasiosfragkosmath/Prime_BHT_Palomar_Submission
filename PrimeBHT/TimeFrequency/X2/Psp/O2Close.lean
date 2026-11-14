module

public import PrimeBHT.TimeFrequency.X2.Psp.O2Final

/-!
# X2, V13 O2 (k): closing the O2 estimate for `ovG`

`tmult_split`: `T_m(F - G)(x₀) = ∫ K(x₀ - z) (T_σ F - G)(z) dz` (`m · lowSym θ σ = m`); `OutBound 𝔭 C_out`: the exact statement of the OUTSIDE part
(MTT2 (d1)–(d4), `D_out`) still to be proved; `overlap_O2_of_out`: `OutBound ⇒ OverlapO2Ovg` (the fine part is `fine_bound_ovG`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform ContDiff Real Convolution
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

section Close

variable {P : ℕ} [NeZero P]

omit [NeZero P] in
theorem tmult_split {m : ℝ → ℂ} (hm : ContDiff ℝ ∞ m) (hmc : HasCompactSupport m) {θ : ℝ} {σ : ℤ}
    (hmul : ∀ ξ, m ξ * lowSym θ σ ξ = m ξ) {F G : ℝ → ZMod P → ℂ} (hF : Measurable F) {BF : ℝ}
    (hBF : ∀ z y, ‖F z y‖ ≤ BF) (hG : Measurable G) {BG : ℝ} (hBG : ∀ z y, ‖G z y‖ ≤ BG) (x₀ : ℝ)
    (y : ZMod P) :
    tmult m (F - G) x₀ y = ∫ z, 𝓕⁻ m (x₀ - z) * (tmult (lowSym θ σ) F z y - G z y) := by
  have hLc := contDiff_lowSym θ σ
  have hLs : HasCompactSupport (lowSym θ σ) :=
    hasCompactSupport_of_far (c := θ) (r := 17 / 4 * (2 : ℝ) ^ (-σ)) fun ξ hξ => lowSym_eq_zero hξ.le
  have hFy := measurable_pi_iff.1 hF y
  have hGy := measurable_pi_iff.1 hG y
  have h1 : tmult m (F - G) x₀ y = tm m (fun z => F z y - G z y) x₀ := rfl
  rw [h1, tm_sub hm hmc hFy hGy (fun z => hBF z y) (fun z => hBG z y) x₀]
  have h2 : (∫ z, 𝓕⁻ m (x₀ - z) * (tmult (lowSym θ σ) F z y - G z y)) =
      tm m (fun z => tm (lowSym θ σ) (fun w => F w y) z - G z y) x₀ := rfl
  rw [h2, tm_sub hm hmc (measurable_tm hLc hLs hFy) hGy
    (fun z => norm_tm_le_gen hLc hLs hFy (fun w => hBF w y) z) (fun z => hBG z y) x₀]
  congr 1
  rw [tm_comp hm hmc hLc hLs hFy (fun w => hBF w y) x₀]
  have : (fun ξ => m ξ * lowSym θ σ ξ) = m := funext hmul
  rw [this]

end Close

/-- `∂Ẽ_σ ≠ ∅` for a tree scale `σ` of a part of a tree. -/
theorem bdryEnds_nonempty_of_layer {TA : Finset TriTile} {t : Top} (hT : IsTree TA t) {σ : ℤ} {R₀ : TriTile}
    (hR₀ : R₀ ∈ layer' TA σ) : (bdryEnds TA t.1 σ).Nonempty := by
  obtain ⟨hRT, hs⟩ := mem_layer'_iff.1 hR₀
  have hI : dyadicInt σ R₀.pos ⊆ dyadicInt t.1.1 t.1.2 := by
    have := (hT R₀ hRT).1
    unfold TriTile.I at this
    rwa [hs] at this
  have hkey : R₀.pos ∈ eTilKeys TA t.1 σ := by
    refine mem_eTilKeys.2 ⟨hI, R₀, hRT, ?_⟩
    unfold TriTile.I
    rw [hs]
    exact dyadicInt_subset_dilate (by norm_num) σ R₀.pos
  have hV : (eTilKeysF TA t.1 σ).Nonempty := ⟨R₀.pos, mem_eTilKeysF.2 hkey⟩
  set v₀ := (eTilKeysF TA t.1 σ).min' hV with hv₀
  have hv₀m : v₀ ∈ eTilKeysF TA t.1 σ := Finset.min'_mem _ hV
  have hnot : v₀ - 1 ∉ eTilKeysF TA t.1 σ := fun h => by
    have := Finset.min'_le _ _ h
    omega
  refine ⟨(2 : ℝ) ^ σ * (v₀ : ℝ), Finset.mem_union_left _ ?_⟩
  exact mem_leftEndsOf.2 ⟨v₀, hv₀m, hnot, rfl⟩

/-- **The OUTSIDE part of the O2 estimate (MTT2 (d1)–(d4)): the exact statement still to be proved** (see `docs/audits/X2-O2-overlap.md`).
`D_out = 1_{ℝ∖Ẽ_σ}(T_σ F - Π̃ F) + Σ_{τ ≥ σ} bumps_τ`; for `x₀ ∈ I₀` and `E = engTop = ofReal e`:
`χ̃_σ(x₀) ‖∫ K(x₀ - z) D_out(z) dz‖_{L²(Y)} ≤ C_out e a`. -/
def OutBound (𝔭 : Params) (Cout : ℝ) : Prop :=
  𝔭.N / 8 + 3 ≤ 𝔭.D → ∀ (P : ℕ) [NeZero P] (Qs : Set Box) (Tr TA : Finset TriTile) (t : Top) (k : Fin 3) (η : ℝ → ℝ)
    (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ) (s₀ : ℤ),
    k ≠ 2 → 𝔭.Admissible → 𝔭.tree.Admissible → IsEtaCut 𝔭 η → (∃ η' : ℝ → ℝ, IsEtaCut 𝔭.tree η') → IsRankOne 𝔭.J Qs →
    TA ⊆ Tr → (∀ R ∈ Tr, R.box ∈ Qs) → IsGoodTree TA t → (∀ R ∈ TA, IsOvSlot t k R.box) → LacData 𝔭 TA k η χ m →
    (∀ R ∈ TA, (𝔭.J : ℤ) ∣ R.box.scale - s₀) →
    ∀ F : ℝ → ZMod P → ℂ, Measurable F → (∃ B, ∀ x, yNorm 2 (F x) ≤ B) →
      ∀ (σ : ℤ) (R₀ : TriTile), R₀ ∈ layer' TA σ → ∀ (v : ℤ) (S : Finset ℤ),
        (∀ σ' ∈ S, (𝔭.J : ℤ) ∣ σ' - σ) →
        (∀ σ' : ℤ, (𝔭.J : ℤ) ∣ σ' - σ → (bdryEnds TA t.1 σ').Nonempty → σ' ∈ S) →
        ∀ e : ℝ, engTop 𝔭.tree 2 k F Tr 2 = ENNReal.ofReal e → 0 ≤ e → ∀ x₀ ∈ dyadicInt σ v,
          |layerCut η TA σ x₀| * yNorm 2 (fun y => ∫ z, 𝓕⁻ (m R₀ k) (x₀ - z) *
            Dout 𝔭.J s₀ (-((TA.sup (fun R => R.box.scale.natAbs) : ℕ) : ℤ) - 1) TA t.1 (t.2 * freqDir k) F
              (fun τ x => ovCoef 𝔭.J (t.2 * freqDir k) F τ x) (fun τ x => -ovCoef 𝔭.J (t.2 * freqDir k) F τ x) σ z y) ≤
            Cout * e * (((2 : ℝ) ^ σ)⁻¹ * ∫ y, ovWeight 2 σ v y * muW 𝔭.J S (bdryEnds TA t.1) σ y)

/-- **O2 from the outside bound.** -/
theorem overlap_O2_of_out {𝔭 : Params} {Cout : ℝ} (hCout : 0 ≤ Cout) (hout : OutBound 𝔭 Cout) :
    OverlapO2Ovg 𝔭 := by
  intro hND
  have hCpos : 0 < Cout + |Cfine 𝔭| + 1 := by positivity
  refine ⟨Cout + |Cfine 𝔭| + 1, hCpos.le, ?_⟩
  intro P _ Qs Tr TA t k η χ m s₀ hk h𝔭 h𝔭t hη hη'ex hQ hsub hTr hgood hov hlac hlat F hF hFb σ R₀ hR₀ v S hS1 hS2
  obtain ⟨η', hη'⟩ := hη'ex
  have hout' := hout hND P Qs Tr TA t k η χ m s₀ hk h𝔭 h𝔭t hη ⟨η', hη'⟩ hQ hsub hTr hgood hov hlac hlat F hF hFb σ R₀
    hR₀ v S hS1 hS2
  obtain ⟨hR₀T, hσ⟩ := mem_layer'_iff.1 hR₀
  have hJ : 0 < 𝔭.J := by have := h𝔭.1; unfold jFloor at this; omega
  have hJ2 : 2 ≤ 𝔭.J := by have := h𝔭.1; unfold jFloor at this; omega
  have hbd : (bdryEnds TA t.1 σ).Nonempty := bdryEnds_nonempty_of_layer hgood.1 hR₀
  have hσS : σ ∈ S := hS2 σ (by simp) hbd
  have ha_pos : 0 < ovFactor 𝔭.J S (bdryEnds TA t.1) σ v := ovFactor_pos 𝔭.J hσS hbd
  set a : ℝ := ((2 : ℝ) ^ σ)⁻¹ * ∫ y, ovWeight 2 σ v y * muW 𝔭.J S (bdryEnds TA t.1) σ y with ha
  have ha_pos' : 0 < a := ha_pos
  set lo : ℤ := -((TA.sup (fun R => R.box.scale.natAbs) : ℕ) : ℤ) - 1 with hlo
  set θ : ℝ := t.2 * freqDir k with hθdef
  -- the layer multiplier
  have hmIn : InMult 𝔭 σ (R₀.box.centre k) (m R₀ k) := by
    have := hlac.mult R₀ hR₀T; rwa [hσ] at this
  have hθ : |θ - R₀.box.centre k| ≤ 13 / 8 * (2 : ℝ) ^ (-σ) := by
    have := abs_theta_sub_centre_le_of_ov (hov R₀ hR₀T); rwa [hσ] at this
  have hβ : 𝔭.β ≤ 11 / 4 := by obtain ⟨-, -, -, -, -, -, h7, -⟩ := h𝔭; exact h7
  have hmcd : ContDiff ℝ ∞ (m R₀ k) := hmIn.1
  have hmcs : HasCompactSupport (m R₀ k) := hasCompactSupport_of_far (c := R₀.box.centre k) hmIn.2.1
  have hmul : ∀ ξ, m R₀ k ξ * lowSym θ σ ξ = m R₀ k ξ := by
    intro ξ
    by_cases h : 3 * (2 : ℝ) ^ (-σ) < |ξ - θ|
    · rw [inMult_supp_theta hmIn hβ hθ h, zero_mul]
    · push Not at h
      have hp := zpow_two_pos (-σ)
      rw [lowSym_eq_one (by linarith), mul_one]
  have hσL : σ ∈ ovScales 𝔭.J s₀ lo t.1.1 := by
    rw [mem_ovScales]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have h1 : (R₀.box.scale.natAbs : ℕ) ≤ TA.sup (fun R => R.box.scale.natAbs) :=
        Finset.le_sup (f := fun R : TriTile => R.box.scale.natAbs) hR₀T
      rw [← hσ]; omega
    · have := (hgood.1 R₀ hR₀T).1
      unfold TriTile.I at this
      rw [hσ] at this
      exact scale_le_of_dyadicInt_subset this
    · have := hlat R₀ hR₀T; rwa [hσ] at this
  have hlatT : ∀ R ∈ TA, (𝔭.tree.J : ℤ) ∣ R.box.scale - s₀ := by simpa using hlat
  -- the function `G`
  have hO1 := ovG_O1 (𝔭 := 𝔭.tree) h𝔭t (by simpa using hJ2) hη' (s := 2) (q := 2) (by norm_num) (by norm_num) hF hFb
    (Cs := Tr) hsub hov (s₀ := s₀) hlatT
  set G : ℝ → ZMod P → ℂ := ovG 𝔭.J TA t k s₀ F with hG
  have hGm : Measurable G := by simpa using hO1.1
  have hUm : Measurable (fun x => (((layerCut η TA σ x : ℝ) : ℂ)) • tmult (m R₀ k) (F - G) x) := by
    refine measurable_pi_iff.2 fun y => ?_
    have h1 : Measurable (fun x => ((layerCut η TA σ x : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (measurable_layerCut hη TA σ)
    have h2 : Measurable (tmult (m R₀ k) (F - G)) :=
      measurable_tmult_of_cont_kernel (kernel_facts hmcd hmcs).1 (hF.sub hGm)
    have h3 := (measurable_pi_iff.1 h2) y
    have h4 : Measurable (fun x => ((layerCut η TA σ x : ℝ) : ℂ) * tmult (m R₀ k) (F - G) x y) := h1.mul h3
    exact h4
  have hmeasU : Measurable (fun x => yNorm 2 ((((layerCut η TA σ x : ℝ) : ℂ)) • tmult (m R₀ k) (F - G) x)) :=
    (measurable_yNorm_fun 2).comp hUm
  by_cases hE : engTop 𝔭.tree 2 k F Tr 2 = ⊤
  · rw [hE]
    exact ovBound_of_sup (by norm_num) hCpos.le ha_pos'.le hmeasU (ovSup_trivial_top hCpos ha_pos')
  · set e : ℝ := (engTop 𝔭.tree 2 k F Tr 2).toReal with he
    have hE' : engTop 𝔭.tree 2 k F Tr 2 = ENNReal.ofReal e := (ENNReal.ofReal_toReal hE).symm
    have he0 : 0 ≤ e := ENNReal.toReal_nonneg
    obtain ⟨B, hB⟩ := hFb
    have hBF : ∀ z y, ‖F z y‖ ≤ (P : ℝ) ^ (2 : ℝ)⁻¹ * B := fun z y => coord_bound_o2 hB z y
    obtain ⟨C₁, hC₁0, hGbound⟩ : ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ y, ENNReal.ofReal (yNorm 2 (G y)) ≤
        ENNReal.ofReal C₁ * engTop 𝔭.tree 2 k F Tr 2 :=
      ⟨_, by have := le_max_right (oaConst 𝔭.tree 2) 0; have := coefConst_nonneg 𝔭.tree 2; linarith, hO1.2.1⟩
    have hGb : ∀ y, yNorm 2 (G y) ≤ C₁ * e := by
      intro y
      have h := hGbound y
      rw [hE', ← ENNReal.ofReal_mul hC₁0] at h
      exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC₁0 he0)).1 h
    have hBG : ∀ z y, ‖G z y‖ ≤ (P : ℝ) ^ (2 : ℝ)⁻¹ * (C₁ * e) := fun z y =>
      (norm_apply_le_rpow_mul_yNorm (s := 2) (by norm_num) (G z) y).trans
        (mul_le_mul_of_nonneg_left (hGb z) (by positivity))
    obtain ⟨hkc, hki⟩ := kernel_facts hmcd hmcs
    have hLc := contDiff_lowSym θ σ
    have hLs : HasCompactSupport (lowSym θ σ) :=
      hasCompactSupport_of_far (c := θ) (r := 17 / 4 * (2 : ℝ) ^ (-σ)) fun ξ hξ => lowSym_eq_zero hξ.le
    set cL : ℤ → ℝ → ZMod P → ℂ := fun τ x => ovCoef 𝔭.J θ F τ x with hcL
    set cR : ℤ → ℝ → ZMod P → ℂ := fun τ x => -ovCoef 𝔭.J θ F τ x with hcR
    have hpt : ∀ x₀ ∈ dyadicInt σ v, yNorm 2 ((((layerCut η TA σ x₀ : ℝ) : ℂ)) • tmult (m R₀ k) (F - G) x₀) ≤
        (Cout + |Cfine 𝔭| + 1) * a * e := by
      intro x₀ hx₀
      rw [yNorm_real_smul_le (by norm_num)]
      have hTb : ∀ z y, ‖tmult (lowSym θ σ) F z y‖ ≤ ((P : ℝ) ^ (2 : ℝ)⁻¹ * B) * ∫ w, ‖𝓕⁻ (lowSym θ σ) w‖ := fun z y =>
        norm_tm_le_gen hLc hLs (measurable_pi_iff.1 hF y) (fun w => by
          have := coord_bound_o2 hB w y; exact this) z
      have hTm : ∀ y, Measurable (fun z => tmult (lowSym θ σ) F z y) := fun y =>
        measurable_tm hLc hLs (measurable_pi_iff.1 hF y)
      have hD_int : ∀ y, Integrable (fun z => 𝓕⁻ (m R₀ k) (x₀ - z) * (tmult (lowSym θ σ) F z y - G z y)) := by
        intro y
        exact integrable_kmul hki (f := fun z => tmult (lowSym θ σ) F z y - G z y)
          ((hTm y).sub ((measurable_pi_apply y).comp hGm))
          (B := ((P : ℝ) ^ (2 : ℝ)⁻¹ * B) * (∫ w, ‖𝓕⁻ (lowSym θ σ) w‖) + (P : ℝ) ^ (2 : ℝ)⁻¹ * (C₁ * e))
          (fun z => (norm_sub_le _ _).trans (add_le_add (hTb z y) (hBG z y))) x₀ hkc
      have hFine_int : ∀ y, Integrable (fun z => 𝓕⁻ (m R₀ k) (x₀ - z) *
          Dfine 𝔭.J s₀ lo TA t.1 θ F cL cR σ z y) :=
        fun y => integrable_K_Dfine hmcd hmcs 𝔭.J s₀ lo TA t.1 θ hF hBF σ x₀ y
      have hdecy : ∀ z y, tmult (lowSym θ σ) F z y - G z y = Dout 𝔭.J s₀ lo TA t.1 θ F cL cR σ z y +
          Dfine 𝔭.J s₀ lo TA t.1 θ F cL cR σ z y := by
        intro z y
        have h := congrFun (decomp hJ TA t.1 θ F cL cR hσL z) y
        have e1 : (tmult (lowSym θ σ) F z - overlapG TA t.1 (ovScales 𝔭.J s₀ lo t.1.1) θ F cL cR z) y =
            tmult (lowSym θ σ) F z y - G z y := rfl
        rw [e1] at h
        exact h
      have hDout_int : ∀ y, Integrable (fun z => 𝓕⁻ (m R₀ k) (x₀ - z) *
          Dout 𝔭.J s₀ lo TA t.1 θ F cL cR σ z y) := fun y => by
        have h := (hD_int y).sub (hFine_int y)
        refine h.congr (Filter.Eventually.of_forall fun z => ?_)
        simp only [Pi.sub_apply]
        rw [hdecy z y]; ring
      have hfun : tmult (m R₀ k) (F - G) x₀ =
          (fun y => ∫ z, 𝓕⁻ (m R₀ k) (x₀ - z) * Dout 𝔭.J s₀ lo TA t.1 θ F cL cR σ z y) +
            (fun y => ∫ z, 𝓕⁻ (m R₀ k) (x₀ - z) * Dfine 𝔭.J s₀ lo TA t.1 θ F cL cR σ z y) := by
        funext y
        rw [tmult_split hmcd hmcs hmul hF (fun z y => hBF z y) hGm hBG x₀ y]
        simp only [Pi.add_apply]
        rw [← integral_add (hDout_int y) (hFine_int y)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        beta_reduce
        rw [hdecy z y, mul_add]
      rw [hfun]
      have hA := hout' e hE' he0 x₀ hx₀
      have hB' := fine_bound_ovG h𝔭 h𝔭t hη' hF ⟨B, hB⟩ hsub hov hlat hmIn hθ hσL hE' he0 hS1 hS2 hx₀
      have hN2 : 2 ≤ 𝔭.N := by
        obtain ⟨-, h2, -⟩ := h𝔭
        unfold classFloor at h2; omega
      have habs1 : |layerCut η TA σ x₀| ≤ 1 := by
        rw [abs_of_nonneg (layerCut_nonneg hη TA σ x₀)]
        exact layerCut_le_one hη hN2 hgood.2.1 σ x₀
      have hyA := yNorm_nonneg' (P := P) 2 (fun y => ∫ z, 𝓕⁻ (m R₀ k) (x₀ - z) *
        Dout 𝔭.J s₀ lo TA t.1 θ F cL cR σ z y)
      have hyB := yNorm_nonneg' (P := P) 2 (fun y => ∫ z, 𝓕⁻ (m R₀ k) (x₀ - z) *
        Dfine 𝔭.J s₀ lo TA t.1 θ F cL cR σ z y)
      have hae : 0 ≤ a * e := mul_nonneg ha_pos'.le he0
      calc |layerCut η TA σ x₀| * yNorm 2 ((fun y => ∫ z, 𝓕⁻ (m R₀ k) (x₀ - z) *
            Dout 𝔭.J s₀ lo TA t.1 θ F cL cR σ z y) + (fun y => ∫ z, 𝓕⁻ (m R₀ k) (x₀ - z) *
            Dfine 𝔭.J s₀ lo TA t.1 θ F cL cR σ z y))
          ≤ |layerCut η TA σ x₀| * (yNorm 2 (fun y => ∫ z, 𝓕⁻ (m R₀ k) (x₀ - z) *
            Dout 𝔭.J s₀ lo TA t.1 θ F cL cR σ z y) + yNorm 2 (fun y => ∫ z, 𝓕⁻ (m R₀ k) (x₀ - z) *
            Dfine 𝔭.J s₀ lo TA t.1 θ F cL cR σ z y)) :=
            mul_le_mul_of_nonneg_left (CZ.yNorm_add_le (by norm_num) _ _) (abs_nonneg _)
        _ = |layerCut η TA σ x₀| * yNorm 2 (fun y => ∫ z, 𝓕⁻ (m R₀ k) (x₀ - z) *
              Dout 𝔭.J s₀ lo TA t.1 θ F cL cR σ z y) +
            |layerCut η TA σ x₀| * yNorm 2 (fun y => ∫ z, 𝓕⁻ (m R₀ k) (x₀ - z) *
              Dfine 𝔭.J s₀ lo TA t.1 θ F cL cR σ z y) := by ring
        _ ≤ Cout * e * a + 1 * (Cfine 𝔭 * e * a) :=
            add_le_add hA (mul_le_mul habs1 hB' hyB zero_le_one)
        _ ≤ (Cout + |Cfine 𝔭| + 1) * a * e := by
            have h1 : Cfine 𝔭 * e * a ≤ |Cfine 𝔭| * (a * e) := by
              have := le_abs_self (Cfine 𝔭)
              nlinarith [mul_nonneg ha_pos'.le he0]
            nlinarith [mul_nonneg hCout hae]
    have hsup : ∀ x ∈ dyadicInt σ v, ENNReal.ofReal (yNorm 2 ((((layerCut η TA σ x : ℝ) : ℂ)) • tmult (m R₀ k) (F - G) x)) ≤
        ENNReal.ofReal ((Cout + |Cfine 𝔭| + 1) * a) * engTop 𝔭.tree 2 k F Tr 2 := by
      intro x hx
      rw [hE', ← ENNReal.ofReal_mul (mul_pos hCpos ha_pos').le]
      exact ENNReal.ofReal_le_ofReal (by have := hpt x hx; linarith)
    exact ovBound_of_sup (by norm_num) hCpos.le ha_pos'.le hmeasU hsup

end PrimeBHT.TimeFrequency.X2
