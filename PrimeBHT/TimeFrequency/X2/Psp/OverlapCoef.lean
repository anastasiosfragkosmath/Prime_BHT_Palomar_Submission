module

public import PrimeBHT.TimeFrequency.X2.Psp.OverlapConstruct
public import PrimeBHT.TimeFrequency.X2.Ortho.Kernel

/-!
# X2, V13 part 4 (B): the coefficients `c^{ℓ,r}` of the overlapping projection and the coefficient bound O-b

`docs/audits/X2-V13-route-check.md` §2.6, MTT2 Lemma `clij-est`.  Everything is in the FRAME CENTRED AT `θ = ξ_T f_k`
(MTT2 normalises `ξ_T = 0` by modulation): `S_σ = T_σ - T_{σ+J}` has symbol `lowSym θ σ - lowSym θ (σ + J)`, which vanishes on
`{|ξ - θ| ≤ 4 · 2^{-σ-J}}`, so the modulated function `e(-θ·) S_σ F` has a Fourier support away from `0`; the bumps of the
correction `Σ cφ` are modulated, `e(θ y) φ(y)`.

* `tilSym J σ`: the symbol of the projection `S̃_σ` (centred at `0`): `lowSym 0 (σ-1) - lowSym 0 (σ+J+1)`; it is `1` on the
  support of the symbol of `S_σ` and vanishes at `0` (so `∫ 𝓕⁻ tilSym = 0`);
* `tilPhi J σ a = ∫_{w ≥ a} 𝓕⁻ tilSym (w) dw`, the dual Heaviside function `S̃_σ^T H(· - x)(z) = tilPhi (x - z)`;
* `ovCoef`: `c_{σ,x} = 2^{-σ} ∫ tilPhi(x - y) e(-θ y) (S_σF)(y) dy`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-! ## The symbol of `S̃_σ` and its kernel -/

/-- The symbol of the Littlewood-Paley projection `S̃_σ` (frame centred at `0`). -/
def tilSym (J : ℕ) (σ : ℤ) (ξ : ℝ) : ℂ := lowSym 0 (σ - 1) ξ - lowSym 0 (σ + (J : ℤ) + 1) ξ

theorem contDiff_tilSym (J : ℕ) (σ : ℤ) : ContDiff ℝ ∞ (tilSym J σ) :=
  (contDiff_lowSym 0 _).sub (contDiff_lowSym 0 _)

theorem tilSym_zero (J : ℕ) (σ : ℤ) : tilSym J σ 0 = 0 := by
  unfold tilSym
  rw [lowSym_eq_one (by simpa using (zpow_two_pos (-(σ - 1))).le.trans' (by norm_num : (0 : ℝ) ≤ 0)),
    lowSym_eq_one (by simpa using (zpow_two_pos (-(σ + (J : ℤ) + 1))).le.trans' (by norm_num : (0 : ℝ) ≤ 0)), sub_self]

theorem tilSym_eq_zero_of_far (J : ℕ) (σ : ℤ) {ξ : ℝ} (h : 9 * (2 : ℝ) ^ (-σ) < |ξ|) : tilSym J σ ξ = 0 := by
  unfold tilSym
  have hp := zpow_two_pos (-σ)
  have e1 : (2 : ℝ) ^ (-(σ - 1)) = 2 * (2 : ℝ) ^ (-σ) := by
    rw [show -(σ - 1) = -σ + 1 by ring, zpow_add₀ (by norm_num)]; simp [mul_comm]
  have h2 : (2 : ℝ) ^ (-(σ + (J : ℤ) + 1)) ≤ (2 : ℝ) ^ (-σ) := by
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  rw [lowSym_eq_zero (σ := σ - 1) (θ := 0) (by rw [sub_zero, e1]; linarith),
    lowSym_eq_zero (σ := σ + (J : ℤ) + 1) (θ := 0) (by rw [sub_zero]; linarith), sub_self]

theorem norm_tilSym_le (J : ℕ) (σ : ℤ) (ξ : ℝ) : ‖tilSym J σ ξ‖ ≤ 2 := by
  unfold tilSym
  have h : ∀ τ : ℤ, ‖lowSym 0 τ ξ‖ ≤ 1 := fun τ => by
    unfold lowSym
    rw [Complex.norm_real, Real.norm_of_nonneg (lowProfile_nonneg _)]
    exact lowProfile_le_one _
  calc ‖lowSym 0 (σ - 1) ξ - lowSym 0 (σ + (J : ℤ) + 1) ξ‖ ≤ ‖lowSym 0 (σ - 1) ξ‖ + ‖lowSym 0 (σ + (J : ℤ) + 1) ξ‖ :=
        norm_sub_le _ _
    _ ≤ 2 := by linarith [h (σ - 1), h (σ + (J : ℤ) + 1)]

theorem norm_iteratedDeriv_tilSym_le {M : ℕ} {Λ : ℝ}
    (hΛ : ∀ a ≤ M, ∀ u : ℝ, ‖iteratedDeriv a (fun u : ℝ => ((lowProfile u : ℝ) : ℂ)) u‖ ≤ Λ)
    (J : ℕ) (σ : ℤ) (ξ : ℝ) :
    ‖iteratedDeriv M (tilSym J σ) ξ‖ ≤ 2 * Λ * ((2 : ℝ) ^ (σ + (J : ℤ) + 1)) ^ M := by
  have h1 := norm_iteratedDeriv_lowSym_le hΛ 0 (σ - 1) (le_refl M) ξ
  have h2 := norm_iteratedDeriv_lowSym_le hΛ 0 (σ + (J : ℤ) + 1) (le_refl M) ξ
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0 (Nat.zero_le _) 0)
  have e : iteratedDeriv M (tilSym J σ) ξ =
      iteratedDeriv M (lowSym 0 (σ - 1)) ξ - iteratedDeriv M (lowSym 0 (σ + (J : ℤ) + 1)) ξ := by
    unfold tilSym
    exact iteratedDeriv_sub ((contDiff_lowSym 0 _).contDiffAt.of_le (by exact_mod_cast le_top))
      ((contDiff_lowSym 0 _).contDiffAt.of_le (by exact_mod_cast le_top))
  have h3 : ((2 : ℝ) ^ (σ - 1)) ^ M ≤ ((2 : ℝ) ^ (σ + (J : ℤ) + 1)) ^ M :=
    pow_le_pow_left₀ (zpow_two_pos _).le (zpow_le_zpow_right₀ (by norm_num) (by omega)) M
  rw [e]
  calc ‖iteratedDeriv M (lowSym 0 (σ - 1)) ξ - iteratedDeriv M (lowSym 0 (σ + (J : ℤ) + 1)) ξ‖
      ≤ ‖iteratedDeriv M (lowSym 0 (σ - 1)) ξ‖ + ‖iteratedDeriv M (lowSym 0 (σ + (J : ℤ) + 1)) ξ‖ := norm_sub_le _ _
    _ ≤ ((2 : ℝ) ^ (σ - 1)) ^ M * Λ + ((2 : ℝ) ^ (σ + (J : ℤ) + 1)) ^ M * Λ := add_le_add h1 h2
    _ ≤ 2 * Λ * ((2 : ℝ) ^ (σ + (J : ℤ) + 1)) ^ M := by nlinarith [mul_le_mul_of_nonneg_right h3 hΛ0]

/-- The kernel of `S̃_σ` (frame centred at `0`). -/
def tilKer (J : ℕ) (σ : ℤ) : ℝ → ℂ := 𝓕⁻ (tilSym J σ)

/-- The constant of the kernel decay of order `M`. -/
def tilConst (M : ℕ) : ℝ := 2 ^ (M + 1) * 18 * max 2 (2 * Classical.choose (exists_lowProfile_deriv_bound M))

theorem tilConst_pos (M : ℕ) : 0 < tilConst M := by
  unfold tilConst
  have : (2 : ℝ) ≤ max 2 (2 * Classical.choose (exists_lowProfile_deriv_bound M)) := le_max_left _ _
  positivity

/-- **Kernel decay of `S̃_σ`**: `‖𝓕⁻ tilSym (w)‖ ≤ C_M 2^{-σ} (1 + 2^{-(σ+J+1)} |w|)^{-M}`. -/
theorem norm_tilKer_le (M : ℕ) (J : ℕ) (σ : ℤ) (w : ℝ) :
    ‖tilKer J σ w‖ ≤ tilConst M * (2 : ℝ) ^ (-σ) * ((1 + (2 : ℝ) ^ (-(σ + (J : ℤ) + 1)) * |w|)⁻¹) ^ M := by
  obtain ⟨hΛ0, hΛ⟩ := Classical.choose_spec (exists_lowProfile_deriv_bound M)
  set Λ := Classical.choose (exists_lowProfile_deriv_bound M) with hΛdef
  set A : ℝ := max 2 (2 * Λ) with hA
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-(σ + (J : ℤ) + 1)) := zpow_two_pos _
  have hp := zpow_two_pos (-σ)
  have h := norm_fourierInv_le_pow (n := tilSym J σ) (c := 0) (r := 9 * (2 : ℝ) ^ (-σ)) (A := A)
    (l := (2 : ℝ) ^ (-(σ + (J : ℤ) + 1))) M (by positivity) hl
    ((contDiff_tilSym J σ).of_le (by exact_mod_cast le_top))
    (fun ξ hξ => tilSym_eq_zero_of_far J σ (by simpa using hξ))
    (fun ξ => (norm_tilSym_le J σ ξ).trans (le_max_left _ _))
    (fun ξ => by
      refine (norm_iteratedDeriv_tilSym_le hΛ J σ ξ).trans ?_
      have : ((2 : ℝ) ^ (-(σ + (J : ℤ) + 1)))⁻¹ = (2 : ℝ) ^ (σ + (J : ℤ) + 1) := by
        rw [← zpow_neg, neg_neg]
      rw [this]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) w
  refine h.trans (le_of_eq ?_)
  unfold tilConst
  rw [← hΛdef, ← hA]
  ring

/-! ## The dual Heaviside function `tilPhi` -/

theorem inv_pow_eq_jb {l : ℝ} (hl : 0 < l) (M : ℕ) (w : ℝ) :
    ((1 + l * |w|)⁻¹) ^ M = jb (w / l⁻¹) ^ (-(M : ℝ)) := by
  unfold jb
  rw [div_inv_eq_mul, abs_mul, abs_of_pos hl, Real.rpow_neg (by positivity), Real.rpow_natCast, inv_pow, mul_comm |w|]

theorem continuous_tilKer (J : ℕ) (σ : ℤ) : Continuous (tilKer J σ) :=
  continuous_fourierInv_of_integrable'
    (integrable_of_far (contDiff_tilSym J σ).continuous (c := 0) (r := 9 * (2 : ℝ) ^ (-σ))
      (fun ξ hξ => tilSym_eq_zero_of_far J σ (by simpa using hξ)))

theorem integrable_tilKer (J : ℕ) (σ : ℤ) : Integrable (tilKer J σ) := by
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-(σ + (J : ℤ) + 1)) := zpow_two_pos _
  have hint := integrable_jb_rpow (c := 0) (L := ((2 : ℝ) ^ (-(σ + (J : ℤ) + 1)))⁻¹) (inv_pos.2 hl) (r := 2)
    (by norm_num)
  refine (hint.const_mul (tilConst 2 * (2 : ℝ) ^ (-σ))).mono' (continuous_tilKer J σ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  refine (norm_tilKer_le 2 J σ w).trans (le_of_eq ?_)
  rw [inv_pow_eq_jb hl 2 w]
  simp

theorem integral_tilKer (J : ℕ) (σ : ℤ) : ∫ w, tilKer J σ w = 0 := by
  have h1 : Integrable (tilSym J σ) :=
    integrable_of_far (contDiff_tilSym J σ).continuous (c := 0) (r := 9 * (2 : ℝ) ^ (-σ))
      (fun ξ hξ => tilSym_eq_zero_of_far J σ (by simpa using hξ))
  have hF : 𝓕 (tilSym J σ) = fun w => tilKer J σ (-w) := by
    funext w
    have := Real.fourierInv_eq_fourier_neg (tilSym J σ) (-w)
    rw [neg_neg] at this
    exact this.symm
  have h2' : Integrable (𝓕 (tilSym J σ)) := by
    rw [hF]; exact (integrable_tilKer J σ).comp_neg
  have h2 := h1.fourier_fourierInv_eq h2' (v := 0) (contDiff_tilSym J σ).continuous.continuousAt
  have h3 : 𝓕 (tilKer J σ) 0 = ∫ w, tilKer J σ w := by
    simp [Real.fourier_real_eq_integral_exp_smul]
  have h4 : 𝓕 (tilKer J σ) 0 = tilSym J σ 0 := h2
  rw [← h3, h4, tilSym_zero]

/-- The dual Heaviside function: `S̃_σ^T H(· - x) (z) = tilPhi (x - z)`, `tilPhi a = ∫_{w ≥ a} 𝓕⁻ tilSym (w) dw`. -/
def tilPhi (J : ℕ) (σ : ℤ) (a : ℝ) : ℂ := ∫ w in Set.Ici a, tilKer J σ w

theorem norm_setIntegral_tilKer_le (M : ℕ) (hM : 2 ≤ M) (J : ℕ) (σ : ℤ) {S : Set ℝ} (hS : MeasurableSet S) (a : ℝ)
    (hSa : ∀ w ∈ S, |a| ≤ |w|) :
    ‖∫ w in S, tilKer J σ w‖ ≤
      tilConst M * (2 : ℝ) ^ (J + 2 : ℤ) * ((1 + (2 : ℝ) ^ (-(σ + (J : ℤ) + 1)) * |a|)⁻¹) ^ (M - 2) := by
  set l : ℝ := (2 : ℝ) ^ (-(σ + (J : ℤ) + 1)) with hl
  have hl0 : 0 < l := zpow_two_pos _
  have hp := zpow_two_pos (-σ)
  have hct := tilConst_pos M
  set g : ℝ → ℝ := fun w => tilConst M * (2 : ℝ) ^ (-σ) * ((1 + l * |a|)⁻¹) ^ (M - 2) * ((1 + l * |w|)⁻¹) ^ 2 with hg
  have hgint : Integrable g := by
    have hint := integrable_jb_rpow (c := 0) (L := l⁻¹) (inv_pos.2 hl0) (r := 2) (by norm_num)
    refine (hint.const_mul (tilConst M * (2 : ℝ) ^ (-σ) * ((1 + l * |a|)⁻¹) ^ (M - 2))).congr
      (Filter.Eventually.of_forall fun w => ?_)
    simp only [hg]
    rw [inv_pow_eq_jb hl0 2 w]
    simp
  have hbound : ∀ w ∈ S, ‖tilKer J σ w‖ ≤ g w := by
    intro w hw
    refine (norm_tilKer_le M J σ w).trans ?_
    simp only [hg]
    have hle : (1 + l * |w|)⁻¹ ≤ (1 + l * |a|)⁻¹ :=
      inv_anti₀ (by positivity) (by nlinarith [hSa w hw])
    have : ((1 + l * |w|)⁻¹) ^ M = ((1 + l * |w|)⁻¹) ^ (M - 2) * ((1 + l * |w|)⁻¹) ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    have hc : 0 ≤ tilConst M * (2 : ℝ) ^ (-σ) := (mul_pos (tilConst_pos M) hp).le
    calc tilConst M * (2 : ℝ) ^ (-σ) * (((1 + l * |w|)⁻¹) ^ (M - 2) * ((1 + l * |w|)⁻¹) ^ 2)
        ≤ tilConst M * (2 : ℝ) ^ (-σ) * (((1 + l * |a|)⁻¹) ^ (M - 2) * ((1 + l * |w|)⁻¹) ^ 2) := by
          gcongr
      _ = _ := by ring
  have h1 : ‖∫ w in S, tilKer J σ w‖ ≤ ∫ w in S, g w := by
    refine norm_integral_le_of_norm_le hgint.integrableOn ?_
    exact (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall hbound)
  have h2 : ∫ w in S, g w ≤ ∫ w, g w :=
    setIntegral_le_integral hgint (Filter.Eventually.of_forall fun w => by
      simp only [hg]; positivity)
  have h3 : ∫ w, g w = tilConst M * (2 : ℝ) ^ (-σ) * ((1 + l * |a|)⁻¹) ^ (M - 2) * (2 * l⁻¹) := by
    simp only [hg]
    rw [integral_const_mul]
    congr 1
    have := integral_one_add_abs_sub_div_rpow (p := 2) (by norm_num) 0 (L := l⁻¹) (inv_pos.2 hl0)
    have e : ∀ w : ℝ, ((1 + l * |w|)⁻¹) ^ 2 = (1 + |w - 0| / l⁻¹) ^ (-(2 : ℝ)) := by
      intro w
      rw [sub_zero, div_inv_eq_mul, Real.rpow_neg (by positivity)]
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow, mul_comm |w|]
    simp_rw [e]
    rw [this]; norm_num
  have h4 : tilConst M * (2 : ℝ) ^ (-σ) * ((1 + l * |a|)⁻¹) ^ (M - 2) * (2 * l⁻¹) =
      tilConst M * (2 : ℝ) ^ (J + 2 : ℤ) * ((1 + l * |a|)⁻¹) ^ (M - 2) := by
    have : (2 : ℝ) ^ (-σ) * (2 * l⁻¹) = (2 : ℝ) ^ (J + 2 : ℤ) := by
      rw [hl, ← zpow_neg, neg_neg, ← zpow_one_add₀ (by norm_num : (2 : ℝ) ≠ 0),
        ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1; ring
    rw [← this]; ring
  linarith [h1, h2, h3, h4]

/-- **(b) Tail decay of `S̃_σ^T H`**: `|tilPhi (a)| ≤ C_M 2^{J+2} (1 + 2^{-(σ+J+1)} |a|)^{-(M-2)}`.  Uses `∫ 𝓕⁻ tilSym = tilSym 0 = 0`
for `a < 0`. -/
theorem norm_tilPhi_le (M : ℕ) (hM : 2 ≤ M) (J : ℕ) (σ : ℤ) (a : ℝ) :
    ‖tilPhi J σ a‖ ≤
      tilConst M * (2 : ℝ) ^ (J + 2 : ℤ) * ((1 + (2 : ℝ) ^ (-(σ + (J : ℤ) + 1)) * |a|)⁻¹) ^ (M - 2) := by
  unfold tilPhi
  rcases le_or_gt 0 a with ha | ha
  · exact norm_setIntegral_tilKer_le M hM J σ measurableSet_Ici a (fun w hw => by
      rw [abs_of_nonneg ha, abs_of_nonneg (ha.trans hw)]; exact hw)
  · have h := integral_add_compl (measurableSet_Ici (a := a)) (integrable_tilKer J σ) (μ := volume)
    rw [integral_tilKer, Set.compl_Ici] at h
    have e : ∫ w in Set.Ici a, tilKer J σ w = -∫ w in Set.Iio a, tilKer J σ w := by
      rw [eq_neg_iff_add_eq_zero]; exact h
    rw [e, norm_neg]
    exact norm_setIntegral_tilKer_le M hM J σ measurableSet_Iio a (fun w hw => by
      have hw' : w < a := hw
      rw [abs_of_neg ha, abs_of_neg (hw'.trans ha)]; linarith)

/-! ## (c) Polynomial growth of `T_τ F` -/

/-- The constant of `poly_growth`. -/
def polyC (𝔭 : Params) (q : ℝ) : ℝ := ((cutScale 𝔭 * (cutK 𝔭)⁻¹)⁻¹ * (4 : ℝ) ^ 𝔭.N) * lowSupConst 𝔭 q

/-- **(c) Polynomial growth of the low-pass operator** (MTT2 `unsigned-est-sup` + `bernstein`, with the cutoff `θ'_W` of
`lowpass_sup_le` bounded below by `⟨(y - c_W)/2^τ⟩^{-N}`): for a lattice interval `W = (τ, v) ⊇ I_R` of a tile `R ∈ Cs`
overlapping in slot `k`, and `x₀` with `|x₀ - c_W| ≤ 3 · 2^τ`, for ALL `y`:
`‖T_τ F(y)‖_{L^s(Y)} ≤ C ⟨(y - x₀)/2^τ⟩^N engTop`. -/
theorem poly_growth {𝔭 : Params} (h𝔭 : 𝔭.Admissible) {η' : ℝ → ℝ} (hη' : IsEtaCut 𝔭 η')
    {P : ℕ} [NeZero P] {s q : ℝ} (hs : 1 ≤ s) (hq : 1 < q) {k : Fin 3} {F : ℝ → ZMod P → ℂ} (hF : Measurable F)
    (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) {Cs : Finset TriTile} {R : TriTile} (hR : R ∈ Cs) {t : Top}
    (hov : IsOvSlot t k R.box) {τ v : ℤ} (hW : R.I ⊆ dyadicInt τ v) (hJ : (𝔭.J : ℤ) ∣ τ - R.box.scale) {x₀ : ℝ}
    (hx₀ : |x₀ - dyCentre τ v| ≤ 3 * (2 : ℝ) ^ τ) (y : ℝ) :
    ENNReal.ofReal (yNorm s (tmult (lowSym (t.2 * freqDir k) τ) F y)) ≤
      ENNReal.ofReal (polyC 𝔭 q) * ENNReal.ofReal (jb ((y - x₀) / (2 : ℝ) ^ τ) ^ 𝔭.N) * engTop 𝔭 s k F Cs q := by
  obtain ⟨hN, hD, hβ, hC⟩ := h𝔭.bounds
  have hCpos : 0 < 𝔭.C := by linarith
  have hp := zpow_two_pos τ
  have hmain := lowpass_sup_le h𝔭 hη' hs hq hF hFb hR hov (W := (τ, v)) hW hJ y
  set Y := yNorm s (tmult (lowSym (t.2 * freqDir k) τ) F y) with hY
  have hY0 : 0 ≤ Y := yNorm_nonneg' s _
  set A := ‖cutoffPsi 𝔭 η' τ v y‖ with hA
  set u : ℝ := (y - dyCentre τ v) / (2 : ℝ) ^ τ with hu
  have hκ : 0 < cutScale 𝔭 * (cutK 𝔭)⁻¹ := mul_pos (cutScale_pos 𝔭) (inv_pos.2 (cutK_pos hCpos))
  have hjb : 0 < jb u := jb_pos u
  -- lower bound of `A`
  have hlow : cutScale 𝔭 * (cutK 𝔭)⁻¹ * jb u ^ (-(𝔭.N : ℝ)) ≤ A := by
    have h1 := le_tileCutoff hη' hCpos τ v y
    rw [hA]
    unfold cutoffPsi
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (cutScale_pos 𝔭).le (tileCutoff_nonneg hη' τ v y))]
    calc cutScale 𝔭 * (cutK 𝔭)⁻¹ * jb u ^ (-(𝔭.N : ℝ)) = cutScale 𝔭 * ((cutK 𝔭)⁻¹ * jb u ^ (-(𝔭.N : ℝ))) := by ring
      _ ≤ cutScale 𝔭 * tileCutoff η' τ v y := mul_le_mul_of_nonneg_left h1 (cutScale_pos 𝔭).le
  have hrp : jb u ^ (-(𝔭.N : ℝ)) = (jb u ^ 𝔭.N)⁻¹ := by
    rw [Real.rpow_neg hjb.le, Real.rpow_natCast]
  rw [hrp] at hlow
  have hjN : 0 < jb u ^ 𝔭.N := pow_pos hjb _
  -- `Y ≤ κ⁻¹ jb^N (A Y)`
  have hle : Y ≤ (cutScale 𝔭 * (cutK 𝔭)⁻¹)⁻¹ * jb u ^ 𝔭.N * (A * Y) := by
    have h1 : 1 ≤ (cutScale 𝔭 * (cutK 𝔭)⁻¹)⁻¹ * jb u ^ 𝔭.N * A := by
      have : cutScale 𝔭 * (cutK 𝔭)⁻¹ ≤ A * jb u ^ 𝔭.N := by
        have := mul_le_mul_of_nonneg_right hlow hjN.le
        rwa [mul_assoc, inv_mul_cancel₀ hjN.ne', mul_one] at this
      calc (1 : ℝ) = (cutScale 𝔭 * (cutK 𝔭)⁻¹)⁻¹ * (cutScale 𝔭 * (cutK 𝔭)⁻¹) := (inv_mul_cancel₀ hκ.ne').symm
        _ ≤ (cutScale 𝔭 * (cutK 𝔭)⁻¹)⁻¹ * (A * jb u ^ 𝔭.N) := mul_le_mul_of_nonneg_left this (inv_pos.2 hκ).le
        _ = _ := by ring
    nlinarith [mul_nonneg hY0 (sub_nonneg.2 h1)]
  -- `jb u ≤ 4 jb((y - x₀)/2^τ)`
  have hjb4 : jb u ≤ 4 * jb ((y - x₀) / (2 : ℝ) ^ τ) := by
    have e : u = (y - x₀) / (2 : ℝ) ^ τ + (x₀ - dyCentre τ v) / (2 : ℝ) ^ τ := by
      rw [hu]; field_simp; ring
    have h1 := jb_add_le ((y - x₀) / (2 : ℝ) ^ τ) ((x₀ - dyCentre τ v) / (2 : ℝ) ^ τ)
    rw [← e] at h1
    have h2 : jb ((x₀ - dyCentre τ v) / (2 : ℝ) ^ τ) ≤ 4 := by
      unfold jb
      have : |(x₀ - dyCentre τ v) / (2 : ℝ) ^ τ| ≤ 3 := by
        rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]; exact hx₀
      linarith
    nlinarith [jb_pos ((y - x₀) / (2 : ℝ) ^ τ)]
  have hjN4 : jb u ^ 𝔭.N ≤ (4 : ℝ) ^ 𝔭.N * jb ((y - x₀) / (2 : ℝ) ^ τ) ^ 𝔭.N := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hjb.le hjb4 _
  have hK0 : 0 ≤ (cutScale 𝔭 * (cutK 𝔭)⁻¹)⁻¹ := (inv_pos.2 hκ).le
  calc ENNReal.ofReal Y ≤ ENNReal.ofReal ((cutScale 𝔭 * (cutK 𝔭)⁻¹)⁻¹ * jb u ^ 𝔭.N * (A * Y)) :=
        ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal ((cutScale 𝔭 * (cutK 𝔭)⁻¹)⁻¹ * jb u ^ 𝔭.N) * ENNReal.ofReal (A * Y) :=
        ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal ((cutScale 𝔭 * (cutK 𝔭)⁻¹)⁻¹ * ((4 : ℝ) ^ 𝔭.N * jb ((y - x₀) / (2 : ℝ) ^ τ) ^ 𝔭.N)) *
          (ENNReal.ofReal (lowSupConst 𝔭 q) * engTop 𝔭 s k F Cs q) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hjN4 hK0)) hmain
    _ = ENNReal.ofReal (polyC 𝔭 q) * ENNReal.ofReal (jb ((y - x₀) / (2 : ℝ) ^ τ) ^ 𝔭.N) * engTop 𝔭 s k F Cs q := by
        have hK4 : 0 ≤ (cutScale 𝔭 * (cutK 𝔭)⁻¹)⁻¹ * (4 : ℝ) ^ 𝔭.N := by positivity
        have e1 : (cutScale 𝔭 * (cutK 𝔭)⁻¹)⁻¹ * ((4 : ℝ) ^ 𝔭.N * jb ((y - x₀) / (2 : ℝ) ^ τ) ^ 𝔭.N) =
            ((cutScale 𝔭 * (cutK 𝔭)⁻¹)⁻¹ * (4 : ℝ) ^ 𝔭.N) * jb ((y - x₀) / (2 : ℝ) ^ τ) ^ 𝔭.N := by ring
        rw [e1, ENNReal.ofReal_mul hK4]
        unfold polyC
        rw [ENNReal.ofReal_mul hK4]
        ring

/-! ## The function `S_σ F` and polynomial growth at an endpoint -/

section Coef

variable {P : ℕ} [NeZero P]

/-- `S_σ F = T_σ F - T_{σ+J} F` (`σ + J` the next coarser lattice scale). -/
def ovS (J : ℕ) (θ : ℝ) (σ : ℤ) (F : ℝ → ZMod P → ℂ) : ℝ → ZMod P → ℂ :=
  fun y => tmult (lowSym θ σ) F y - tmult (lowSym θ (σ + (J : ℤ)) ) F y

theorem measurable_ovS (J : ℕ) (θ : ℝ) (σ : ℤ) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) :
    Measurable (ovS J θ σ F) :=
  (measurable_tmult_lowSym θ σ hF).sub (measurable_tmult_lowSym θ _ hF)

theorem jb_div_le (a : ℝ) {c : ℝ} (hc : 1 ≤ c) : jb (a / c) ≤ jb a := by
  unfold jb
  have hc0 : 0 < c := by linarith
  have : |a / c| ≤ |a| := by
    rw [abs_div, abs_of_pos hc0, div_le_iff₀ hc0]
    nlinarith [abs_nonneg a]
  linarith

/-- The constant of `poly_growth_S`. -/
def polyS (𝔭 : Params) (q : ℝ) : ℝ := 2 * (4 : ℝ) ^ 𝔭.N * max (polyC 𝔭 q) 0

theorem polyS_nonneg (𝔭 : Params) (q : ℝ) : 0 ≤ polyS 𝔭 q := by
  unfold polyS; have := le_max_right (polyC 𝔭 q) 0; positivity

/-- **(c) for `S_σ = T_σ - T_{σ+J}` at an endpoint**: if `R ∈ Cs` is overlapping in slot `k`, `R.I ∋ z`, `|x - z| ≤ 3 · 2^σ`,
`R.scale ≤ σ`, `J ∣ σ - R.scale`, then for all `y`: `‖S_σF(y)‖_{L^s(Y)} ≤ C ⟨(y - x)/2^σ⟩^N e` where `e = engTop` (finite). -/
theorem poly_growth_S {𝔭 : Params} (h𝔭 : 𝔭.Admissible) {η' : ℝ → ℝ} (hη' : IsEtaCut 𝔭 η')
    {s q : ℝ} (hs : 1 ≤ s) (hq : 1 < q) {k : Fin 3} {F : ℝ → ZMod P → ℂ} (hF : Measurable F)
    (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) {Cs : Finset TriTile} {R : TriTile} (hR : R ∈ Cs) {t : Top}
    (hov : IsOvSlot t k R.box) {σ : ℤ} (hRs : R.box.scale ≤ σ) (hJ : (𝔭.J : ℤ) ∣ σ - R.box.scale) (hJ0 : 0 ≤ 𝔭.J)
    {z x : ℝ} (hz : z ∈ R.I) (hxz : |x - z| ≤ 3 * (2 : ℝ) ^ σ) {e : ℝ} (he : engTop 𝔭 s k F Cs q = ENNReal.ofReal e)
    (he0 : 0 ≤ e) (y : ℝ) :
    yNorm s (ovS 𝔭.J (t.2 * freqDir k) σ F y) ≤ polyS 𝔭 q * jb ((y - x) / (2 : ℝ) ^ σ) ^ 𝔭.N * e := by
  have hp := zpow_two_pos σ
  set θ := t.2 * freqDir k with hθ
  -- the bound at a scale `τ ∈ {σ, σ+J}`
  have key : ∀ τ : ℤ, R.box.scale ≤ τ → (𝔭.J : ℤ) ∣ τ - R.box.scale → σ ≤ τ →
      yNorm s (tmult (lowSym θ τ) F y) ≤ max (polyC 𝔭 q) 0 * (4 * jb ((y - x) / (2 : ℝ) ^ σ)) ^ 𝔭.N * e := by
    intro τ hτ hJτ hστ
    obtain ⟨v, hv⟩ := exists_dyadicInt_superset R.box.scale R.pos hτ
    have hzv : z ∈ dyadicInt τ v := hv hz
    have hpτ := zpow_two_pos τ
    have hx₀ : |z - dyCentre τ v| ≤ 3 * (2 : ℝ) ^ τ := by
      obtain ⟨h1, h2⟩ := hzv
      unfold dyCentre
      rw [abs_le]; constructor <;> nlinarith
    have hg := poly_growth h𝔭 hη' hs hq hF hFb hR hov hv hJτ hx₀ y
    rw [he] at hg
    have hC0 : (0 : ℝ) ≤ max (polyC 𝔭 q) 0 := le_max_right _ _
    have hg2 : ENNReal.ofReal (yNorm s (tmult (lowSym θ τ) F y)) ≤
        ENNReal.ofReal (max (polyC 𝔭 q) 0 * jb ((y - z) / (2 : ℝ) ^ τ) ^ 𝔭.N * e) := by
      refine hg.trans ?_
      rw [ENNReal.ofReal_mul (mul_nonneg hC0 (pow_nonneg (jb_pos _).le _)), ENNReal.ofReal_mul hC0]
      gcongr
      exact le_max_left _ _
    have hg3 := (ENNReal.ofReal_le_ofReal_iff (by have := jb_pos ((y - z) / (2 : ℝ) ^ τ); positivity)).1 hg2
    refine hg3.trans ?_
    -- `jb((y - z)/2^τ) ≤ 4 jb((y - x)/2^σ)`
    have hjz : jb ((y - z) / (2 : ℝ) ^ τ) ≤ 4 * jb ((y - x) / (2 : ℝ) ^ σ) := by
      have hc : (1 : ℝ) ≤ (2 : ℝ) ^ τ / (2 : ℝ) ^ σ := by
        rw [le_div_iff₀ hp, one_mul]; exact zpow_le_zpow_right₀ (by norm_num) hστ
      have e1 : (y - z) / (2 : ℝ) ^ τ = ((y - z) / (2 : ℝ) ^ σ) / ((2 : ℝ) ^ τ / (2 : ℝ) ^ σ) := by
        field_simp
      rw [e1]
      refine (jb_div_le _ hc).trans ?_
      have e2 : (y - z) / (2 : ℝ) ^ σ = (y - x) / (2 : ℝ) ^ σ + (x - z) / (2 : ℝ) ^ σ := by field_simp; ring
      rw [e2]
      refine (jb_add_le _ _).trans ?_
      have h4 : jb ((x - z) / (2 : ℝ) ^ σ) ≤ 4 := by
        unfold jb
        have : |(x - z) / (2 : ℝ) ^ σ| ≤ 3 := by
          rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]; exact hxz
        linarith
      nlinarith [jb_pos ((y - x) / (2 : ℝ) ^ σ)]
    have := pow_le_pow_left₀ (jb_pos _).le hjz 𝔭.N
    gcongr
  have h1 := key σ hRs hJ le_rfl
  have h2 := key (σ + (𝔭.J : ℤ)) (by omega) (by
    have : σ + (𝔭.J : ℤ) - R.box.scale = (σ - R.box.scale) + (𝔭.J : ℤ) := by ring
    rw [this]; exact dvd_add (by simpa using hJ) dvd_rfl) (by omega)
  unfold ovS
  refine (yNorm_sub_ov hs _ _).trans ?_
  unfold polyS
  have e4 : (4 * jb ((y - x) / (2 : ℝ) ^ σ)) ^ 𝔭.N = 4 ^ 𝔭.N * jb ((y - x) / (2 : ℝ) ^ σ) ^ 𝔭.N := mul_pow _ _ _
  rw [e4] at h1 h2
  linarith

/-! ## The coefficients -/

theorem measurable_tilPhi (J : ℕ) (σ : ℤ) : Measurable (tilPhi J σ) := by
  have h : tilPhi J σ = fun a => ∫ w, (Set.Ici a).indicator (tilKer J σ) w := by
    funext a; unfold tilPhi; rw [integral_indicator measurableSet_Ici]
  rw [h]
  have hm : Measurable (Function.uncurry fun (a w : ℝ) => (Set.Ici a).indicator (tilKer J σ) w) := by
    have : (Function.uncurry fun (a w : ℝ) => (Set.Ici a).indicator (tilKer J σ) w) =
        fun p : ℝ × ℝ => if p.1 ≤ p.2 then tilKer J σ p.2 else 0 := by
      funext p; simp [Function.uncurry, Set.indicator_apply]
    rw [this]
    exact Measurable.ite (measurableSet_le measurable_fst measurable_snd)
      ((continuous_tilKer J σ).measurable.comp measurable_snd) measurable_const
  exact hm.stronglyMeasurable.integral_prod_right.measurable

/-- **The coefficient `c_{σ,x}`** (MTT2 (cl-def), left endpoint): `2^{-σ} ∫ (S̃_σ^T H(· - x)) · e(-θ ·) S_σ F`,
with `(S̃_σ^T H(· - x))(a) = tilPhi (x - a)`.  The right endpoint coefficient is `-ovCoef` (`H^r = -H`). -/
def ovCoef (J : ℕ) (θ : ℝ) (F : ℝ → ZMod P → ℂ) (σ : ℤ) (x : ℝ) : ZMod P → ℂ :=
  fun y' => ((((2 : ℝ) ^ σ)⁻¹ : ℝ) : ℂ) * ∫ a, (tilPhi J σ (x - a) * ovPhase (-θ) a) * ovS J θ σ F a y'

/-- The constant of the coefficient bound O-b: `C = C_M 2^{2J+4+(J+1)N} polyS`, `M = N + 4`. -/
def coefConst (𝔭 : Params) (q : ℝ) : ℝ :=
  tilConst (𝔭.N + 4) * (2 : ℝ) ^ (𝔭.J + 2 : ℤ) * polyS 𝔭 q * (2 : ℝ) ^ ((𝔭.J + 1) * 𝔭.N) * (2 : ℝ) ^ (𝔭.J + 2 : ℤ)

theorem coefConst_nonneg (𝔭 : Params) (q : ℝ) : 0 ≤ coefConst 𝔭 q := by
  have := tilConst_pos (𝔭.N + 4)
  have := polyS_nonneg 𝔭 q
  unfold coefConst; positivity

/-- **O-b (real form): the coefficient bound** `‖c_{σ,x}‖_{L^s(Y)} ≤ C engTop` (MTT2 `clij-est`, `e:coeff2`), for an endpoint `x`
with a tile `R ∈ Cs` overlapping in slot `k`, `z ∈ R.I`, `|x - z| ≤ 3 · 2^σ`, `R.scale ≤ σ`, `J ∣ σ - R.scale`; `engTop = e`
finite. -/
theorem yNorm_ovCoef_le {𝔭 : Params} (h𝔭 : 𝔭.Admissible) {η' : ℝ → ℝ} (hη' : IsEtaCut 𝔭 η')
    {s q : ℝ} (hs : 1 ≤ s) (hq : 1 < q) {k : Fin 3} {F : ℝ → ZMod P → ℂ} (hF : Measurable F)
    (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) {Cs : Finset TriTile} {R : TriTile} (hR : R ∈ Cs) {t : Top}
    (hov : IsOvSlot t k R.box) {σ : ℤ} (hRs : R.box.scale ≤ σ) (hJ : (𝔭.J : ℤ) ∣ σ - R.box.scale)
    {z x : ℝ} (hz : z ∈ R.I) (hxz : |x - z| ≤ 3 * (2 : ℝ) ^ σ) {e : ℝ}
    (he : engTop 𝔭 s k F Cs q = ENNReal.ofReal e) (he0 : 0 ≤ e) :
    yNorm s (ovCoef 𝔭.J (t.2 * freqDir k) F σ x) ≤ coefConst 𝔭 q * e := by
  have hs0 : 0 < s := by linarith
  set J := 𝔭.J with hJdef
  set N := 𝔭.N with hNdef
  set θ := t.2 * freqDir k with hθ
  set l : ℝ := (2 : ℝ) ^ (-(σ + (J : ℤ) + 1)) with hl
  have hl0 : 0 < l := zpow_two_pos _
  have hp := zpow_two_pos σ
  have hct := tilConst_pos (N + 4)
  have hps := polyS_nonneg 𝔭 q
  have hpow : (0 : ℝ) < (2 : ℝ) ^ ((J + 1) * N) := by positivity
  have hBφ : (0 : ℝ) < tilConst (N + 4) * (2 : ℝ) ^ (J + 2 : ℤ) := mul_pos hct (zpow_two_pos _)
  set c1 : ℝ := tilConst (N + 4) * (2 : ℝ) ^ (J + 2 : ℤ) * polyS 𝔭 q * e * (2 : ℝ) ^ ((J + 1) * N) with hc1
  have hc10 : 0 ≤ c1 := by positivity
  set V : ℝ → ZMod P → ℂ := fun a y' => (tilPhi J σ (x - a) * ovPhase (-θ) a) * ovS J θ σ F a y' with hV
  set G : ℝ → ℝ := fun a => c1 * ((1 + l * |a - x|)⁻¹) ^ 2 with hG
  -- Step 1: pointwise bound
  have hstep1 : ∀ a, yNorm s (V a) ≤ G a := by
    intro a
    have hVa : yNorm s (V a) = ‖tilPhi J σ (x - a)‖ * yNorm s (ovS J θ σ F a) := by
      have : V a = fun y' => (tilPhi J σ (x - a) * ovPhase (-θ) a) * ovS J θ σ F a y' := rfl
      rw [this, yNorm_fun_const_mul hs0, norm_mul, norm_ovPhase, mul_one]
    have hΦ := norm_tilPhi_le (N + 4) (by omega) J σ (x - a)
    have e1 : N + 4 - 2 = N + 2 := by omega
    rw [e1, abs_sub_comm] at hΦ
    have hSa := poly_growth_S h𝔭 hη' hs hq hF hFb hR hov hRs hJ (Nat.zero_le _) hz hxz he he0 a
    have hw : 0 < 1 + l * |a - x| := by positivity
    have hjbN : jb ((a - x) / (2 : ℝ) ^ σ) ^ N ≤ (2 : ℝ) ^ ((J + 1) * N) * (1 + l * |a - x|) ^ N := by
      rw [pow_mul, ← mul_pow]
      refine pow_le_pow_left₀ (jb_pos _).le ?_ N
      unfold jb
      rw [abs_div, abs_of_pos hp]
      have e2 : |a - x| / (2 : ℝ) ^ σ = (2 : ℝ) ^ (J + 1) * (l * |a - x|) := by
        rw [hl, div_eq_iff hp.ne']
        have : (2 : ℝ) ^ (J + 1) * ((2 : ℝ) ^ (-(σ + (J : ℤ) + 1)) * |a - x|) * (2 : ℝ) ^ σ = |a - x| := by
          have h1 : (2 : ℝ) ^ (J + 1) = (2 : ℝ) ^ ((J : ℤ) + 1) := by
            rw [← zpow_natCast]; push_cast; rfl
          rw [h1]
          have h2 : (2 : ℝ) ^ ((J : ℤ) + 1) * (2 : ℝ) ^ (-(σ + (J : ℤ) + 1)) * (2 : ℝ) ^ σ = 1 := by
            rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
            have : (J : ℤ) + 1 + -(σ + (J : ℤ) + 1) + σ = 0 := by ring
            rw [this, zpow_zero]
          calc (2 : ℝ) ^ ((J : ℤ) + 1) * ((2 : ℝ) ^ (-(σ + (J : ℤ) + 1)) * |a - x|) * (2 : ℝ) ^ σ
              = ((2 : ℝ) ^ ((J : ℤ) + 1) * (2 : ℝ) ^ (-(σ + (J : ℤ) + 1)) * (2 : ℝ) ^ σ) * |a - x| := by ring
            _ = |a - x| := by rw [h2, one_mul]
        exact this.symm
      rw [e2]
      have h2J : (1 : ℝ) ≤ (2 : ℝ) ^ (J + 1) := one_le_pow₀ (by norm_num)
      have hnn : 0 ≤ l * |a - x| := by positivity
      nlinarith
    have hwN : ((1 + l * |a - x|)⁻¹) ^ (N + 2) * (1 + l * |a - x|) ^ N = ((1 + l * |a - x|)⁻¹) ^ 2 := by
      have : ((1 + l * |a - x|)⁻¹) ^ (N + 2) = ((1 + l * |a - x|)⁻¹) ^ 2 * ((1 + l * |a - x|)⁻¹) ^ N := by
        rw [pow_add, mul_comm]
      rw [this, mul_assoc, ← mul_pow, inv_mul_cancel₀ hw.ne', one_pow, mul_one]
    rw [hVa]
    calc ‖tilPhi J σ (x - a)‖ * yNorm s (ovS J θ σ F a)
        ≤ (tilConst (N + 4) * (2 : ℝ) ^ (J + 2 : ℤ) * ((1 + l * |a - x|)⁻¹) ^ (N + 2)) *
            (polyS 𝔭 q * jb ((a - x) / (2 : ℝ) ^ σ) ^ N * e) :=
          mul_le_mul hΦ hSa (yNorm_nonneg' _ _) (by positivity)
      _ ≤ (tilConst (N + 4) * (2 : ℝ) ^ (J + 2 : ℤ) * ((1 + l * |a - x|)⁻¹) ^ (N + 2)) *
            (polyS 𝔭 q * ((2 : ℝ) ^ ((J + 1) * N) * (1 + l * |a - x|) ^ N) * e) := by
          gcongr
      _ = c1 * (((1 + l * |a - x|)⁻¹) ^ (N + 2) * (1 + l * |a - x|) ^ N) := by rw [hc1]; ring
      _ = G a := by rw [hwN]
  -- Step 2: integrability of `G`
  have hGint : Integrable G := by
    have hint := integrable_jb_rpow (c := x) (L := l⁻¹) (inv_pos.2 hl0) (r := 2) (by norm_num)
    refine (hint.const_mul c1).congr (Filter.Eventually.of_forall fun a => ?_)
    simp only [hG]
    rw [inv_pow_eq_jb hl0 2 (a - x)]
    simp
  have hGint2 : ∫ a, G a = c1 * (2 * l⁻¹) := by
    simp only [hG]
    rw [integral_const_mul]
    congr 1
    have := integral_one_add_abs_sub_div_rpow (p := 2) (by norm_num) x (L := l⁻¹) (inv_pos.2 hl0)
    have e : ∀ a : ℝ, ((1 + l * |a - x|)⁻¹) ^ 2 = (1 + |a - x| / l⁻¹) ^ (-(2 : ℝ)) := by
      intro a
      rw [div_inv_eq_mul, Real.rpow_neg (by positivity)]
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow, mul_comm |a - x|]
    simp_rw [e]
    rw [this]; norm_num
  -- Step 3: coordinate integrability
  have hcoord : ∀ y', Integrable (fun a => V a y') := by
    intro y'
    have hmeas : AEStronglyMeasurable (fun a => V a y') volume := by
      refine Measurable.aestronglyMeasurable ?_
      have h1 : Measurable (fun a => tilPhi J σ (x - a)) := (measurable_tilPhi J σ).comp (measurable_const.sub measurable_id)
      have h2 : Measurable (fun a => ovPhase (-θ) a) := (continuous_ovPhase (-θ)).measurable
      have h3 : Measurable (fun a => ovS J θ σ F a y') := (measurable_pi_apply y').comp (measurable_ovS J θ σ hF)
      exact (h1.mul h2).mul h3
    refine (hGint.const_mul ((P : ℝ) ^ s⁻¹)).mono' hmeas (Filter.Eventually.of_forall fun a => ?_)
    have h1 := norm_apply_le_rpow_mul_yNorm hs0 (V a) y'
    exact h1.trans (mul_le_mul_of_nonneg_left (hstep1 a) (by positivity))
  -- Step 4: Minkowski
  have hmink := yNorm_integral_le_of_one_le hs V hcoord
  have hint2 : ∫ a, yNorm s (V a) ≤ ∫ a, G a :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun a => yNorm_nonneg' s _) hGint
      (Filter.Eventually.of_forall hstep1)
  -- Step 5: assemble
  have hcoef : yNorm s (ovCoef J θ F σ x) =
      ((2 : ℝ) ^ σ)⁻¹ * yNorm s (fun y' => ∫ a, V a y') := by
    have : ovCoef J θ F σ x = fun y' => ((((2 : ℝ) ^ σ)⁻¹ : ℝ) : ℂ) * ∫ a, V a y' := rfl
    rw [this, yNorm_fun_const_mul hs0, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hp).le]
  rw [hcoef]
  have hfin : ((2 : ℝ) ^ σ)⁻¹ * (c1 * (2 * l⁻¹)) = coefConst 𝔭 q * e := by
    have : ((2 : ℝ) ^ σ)⁻¹ * (2 * l⁻¹) = (2 : ℝ) ^ (J + 2 : ℤ) := by
      have e1 : ((2 : ℝ) ^ σ)⁻¹ = (2 : ℝ) ^ (-σ) := (zpow_neg _ _).symm
      have e2 : l⁻¹ = (2 : ℝ) ^ (σ + (J : ℤ) + 1) := by rw [hl, ← zpow_neg, neg_neg]
      rw [e1, e2, ← zpow_one_add₀ (by norm_num : (2 : ℝ) ≠ 0), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1; ring
    unfold coefConst
    rw [hc1]
    calc ((2 : ℝ) ^ σ)⁻¹ * (tilConst (N + 4) * (2 : ℝ) ^ (J + 2 : ℤ) * polyS 𝔭 q * e * (2 : ℝ) ^ ((J + 1) * N) * (2 * l⁻¹))
        = tilConst (N + 4) * (2 : ℝ) ^ (J + 2 : ℤ) * polyS 𝔭 q * e * (2 : ℝ) ^ ((J + 1) * N) *
            (((2 : ℝ) ^ σ)⁻¹ * (2 * l⁻¹)) := by ring
      _ = _ := by rw [this]; ring
  calc ((2 : ℝ) ^ σ)⁻¹ * yNorm s (fun y' => ∫ a, V a y')
      ≤ ((2 : ℝ) ^ σ)⁻¹ * (c1 * (2 * l⁻¹)) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hp).le
        rw [← hGint2]; exact hmink.trans hint2
    _ = _ := hfin

/-- **O-b (ENNReal form, endpoints)**: for a key `v ∈ eTilKeys` and `x ∈ {2^σ v, 2^σ (v+1)}` (an endpoint of `Ẽ_σ`),
`‖c_{σ,x}‖_{L^s(Y)} ≤ (C + 1) engTop`. -/
theorem ovCoef_bound_end {𝔭 : Params} (h𝔭 : 𝔭.Admissible) (hJ2 : 2 ≤ 𝔭.J) {η' : ℝ → ℝ} (hη' : IsEtaCut 𝔭 η')
    {s q : ℝ} (hs : 1 ≤ s) (hq : 1 < q) {k : Fin 3} {F : ℝ → ZMod P → ℂ} (hF : Measurable F)
    (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) {TA Cs : Finset TriTile} (hsub : TA ⊆ Cs) {t : Top}
    (hov : ∀ R ∈ TA, IsOvSlot t k R.box) {σ : ℤ} (hlat : ∀ R ∈ TA, (𝔭.J : ℤ) ∣ R.box.scale - σ) {v : ℤ}
    (hv : v ∈ eTilKeys TA t.1 σ) {x : ℝ} (hx : x = (2 : ℝ) ^ σ * v ∨ x = (2 : ℝ) ^ σ * ((v : ℝ) + 1)) :
    ENNReal.ofReal (yNorm s (ovCoef 𝔭.J (t.2 * freqDir k) F σ x)) ≤
      ENNReal.ofReal (coefConst 𝔭 q + 1) * engTop 𝔭 s k F Cs q := by
  have hp := zpow_two_pos σ
  have hpos : 0 < coefConst 𝔭 q + 1 := by have := coefConst_nonneg 𝔭 q; linarith
  by_cases hE : engTop 𝔭 s k F Cs q = ⊤
  · rw [hE, ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
    exact le_top
  · -- the tile near the endpoint
    have hne : (dilate 3 (dyadicInt σ v) ∩ eTil TA t.1 σ).Nonempty := by
      refine ⟨(2 : ℝ) ^ σ * v, dyadicInt_subset_dilate (by norm_num) σ v (mem_dyadicInt_left σ v), ?_⟩
      unfold eTil
      exact Set.mem_biUnion hv (mem_dyadicInt_left σ v)
    obtain ⟨R, hR, hRs, hRI⟩ := exists_tile_near hJ2 hlat hne
    have hz : (2 : ℝ) ^ R.box.scale * R.pos ∈ R.I := by unfold TriTile.I; exact mem_dyadicInt_left _ _
    have hz5 := (mem_dilate_dyadicInt_iff 5 σ v _).1 (hRI hz)
    obtain ⟨hz1, hz2⟩ := hz5
    have hxz : |x - (2 : ℝ) ^ R.box.scale * R.pos| ≤ 3 * (2 : ℝ) ^ σ := by
      rw [abs_le]
      rcases hx with rfl | rfl <;> constructor <;> nlinarith
    have hJ' : (𝔭.J : ℤ) ∣ σ - R.box.scale := by
      have := dvd_neg.2 (hlat R hR)
      simpa using this
    set E := engTop 𝔭 s k F Cs q with hEdef
    have hE' : E = ENNReal.ofReal E.toReal := (ENNReal.ofReal_toReal hE).symm
    have hb := yNorm_ovCoef_le h𝔭 hη' hs hq hF hFb (hsub hR) (hov R hR) hRs hJ' hz hxz
      (he := hE') ENNReal.toReal_nonneg
    rw [hE']
    calc ENNReal.ofReal (yNorm s (ovCoef 𝔭.J (t.2 * freqDir k) F σ x))
        ≤ ENNReal.ofReal (coefConst 𝔭 q * E.toReal) := ENNReal.ofReal_le_ofReal hb
      _ ≤ ENNReal.ofReal ((coefConst 𝔭 q + 1) * E.toReal) :=
          ENNReal.ofReal_le_ofReal (by nlinarith [ENNReal.toReal_nonneg (a := E)])
      _ = ENNReal.ofReal (coefConst 𝔭 q + 1) * ENNReal.ofReal E.toReal := ENNReal.ofReal_mul hpos.le

/-! ## The concrete `G` and its (O1) -/

theorem yNorm_neg_ov {s : ℝ} (hs : 0 < s) (v : ZMod P → ℂ) : yNorm s (-v) = yNorm s v := by
  have : -v = (((-1 : ℝ) : ℂ)) • v := by funext y; simp
  rw [this, yNorm_csmul hs]; simp

/-- The finite set of lattice scales `σ ∈ [lo, hi]` with `J ∣ σ - s₀`. -/
def ovScales (J : ℕ) (s₀ lo hi : ℤ) : Finset ℤ := (Finset.Icc lo hi).filter (fun σ => (J : ℤ) ∣ σ - s₀)

/-- **THE CONCRETE `G = Π̃F - Σ c φ`** of the overlapping projection (MTT2 `pif-def`): lattice scales `σ ≡ s₀ (mod J)` between
`-(max |scale|) - 1` and the top scale; coefficients `c^ℓ = ovCoef`, `c^r = -ovCoef` (`H^r = -H`); bumps modulated by `e(θ y)`. -/
def ovG (J : ℕ) (TA : Finset TriTile) (t : Top) (k : Fin 3) (s₀ : ℤ) (F : ℝ → ZMod P → ℂ) : ℝ → ZMod P → ℂ :=
  overlapG TA t.1 (ovScales J s₀ (-((TA.sup (fun R => R.box.scale.natAbs) : ℕ) : ℤ) - 1) t.1.1) (t.2 * freqDir k) F
    (fun σ x => ovCoef J (t.2 * freqDir k) F σ x) (fun σ x => -ovCoef J (t.2 * freqDir k) F σ x)

/-- **(O1) for the concrete `G`**: measurable, `‖G(y)‖_{L^s(Y)} ≤ C engTop` for all `y`, `G = 0` off `3 I_t`
(`C = max(C_oa, 0) + 16 (C_coef + 1) + 1`). -/
theorem ovG_O1 {𝔭 : Params} (h𝔭 : 𝔭.Admissible) (hJ2 : 2 ≤ 𝔭.J) {η' : ℝ → ℝ} (hη' : IsEtaCut 𝔭 η')
    {s q : ℝ} (hs : 1 ≤ s) (hq : 1 < q) {k : Fin 3} {F : ℝ → ZMod P → ℂ} (hF : Measurable F)
    (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) {TA Cs : Finset TriTile} (hsub : TA ⊆ Cs) {t : Top}
    (hov : ∀ R ∈ TA, IsOvSlot t k R.box) {s₀ : ℤ} (hs₀ : ∀ R ∈ TA, (𝔭.J : ℤ) ∣ R.box.scale - s₀) :
    Measurable (ovG 𝔭.J TA t k s₀ F) ∧
      (∀ y, ENNReal.ofReal (yNorm s (ovG 𝔭.J TA t k s₀ F y)) ≤
        ENNReal.ofReal (max (oaConst 𝔭 q) 0 + 16 * (coefConst 𝔭 q + 1) + 1) * engTop 𝔭 s k F Cs q) ∧
      ∀ y, y ∉ dilate 3 (dyadicInt t.1.1 t.1.2) → ovG 𝔭.J TA t k s₀ F y = 0 := by
  have hs0 : 0 < s := by linarith
  set L := ovScales 𝔭.J s₀ (-((TA.sup (fun R => R.box.scale.natAbs) : ℕ) : ℤ) - 1) t.1.1 with hL
  have hlat : ∀ σ ∈ L, ∀ R ∈ TA, (𝔭.J : ℤ) ∣ R.box.scale - σ := by
    intro σ hσ R hR
    have h1 := (Finset.mem_filter.1 hσ).2
    have : R.box.scale - σ = (R.box.scale - s₀) - (σ - s₀) := by ring
    rw [this]; exact dvd_sub (hs₀ R hR) h1
  have hB : (0 : ℝ) ≤ coefConst 𝔭 q + 1 := by have := coefConst_nonneg 𝔭 q; linarith
  have hcL : ∀ σ ∈ L, ∀ x ∈ leftEnds TA t.1 σ, ENNReal.ofReal (yNorm s (ovCoef 𝔭.J (t.2 * freqDir k) F σ x)) ≤
      ENNReal.ofReal (coefConst 𝔭 q + 1) * engTop 𝔭 s k F Cs q := by
    intro σ hσ x hx
    obtain ⟨v, hv, -, rfl⟩ := mem_leftEndsOf.1 hx
    exact ovCoef_bound_end h𝔭 hJ2 hη' hs hq hF hFb hsub hov (hlat σ hσ) (mem_eTilKeysF.1 hv) (Or.inl rfl)
  have hcR : ∀ σ ∈ L, ∀ x ∈ rightEnds TA t.1 σ, ENNReal.ofReal (yNorm s (-ovCoef 𝔭.J (t.2 * freqDir k) F σ x)) ≤
      ENNReal.ofReal (coefConst 𝔭 q + 1) * engTop 𝔭 s k F Cs q := by
    intro σ hσ x hx
    obtain ⟨v, hv, -, rfl⟩ := mem_rightEndsOf.1 hx
    rw [yNorm_neg_ov hs0]
    exact ovCoef_bound_end h𝔭 hJ2 hη' hs hq hF hFb hsub hov (hlat σ hσ) (mem_eTilKeysF.1 hv) (Or.inr rfl)
  exact overlap_O1_of_coeff h𝔭 hJ2 hη' hs hq hF hFb hsub hov hlat (cL := fun σ x => ovCoef 𝔭.J (t.2 * freqDir k) F σ x)
    (cR := fun σ x => -ovCoef 𝔭.J (t.2 * freqDir k) F σ x) hB hcL hcR

end Coef

end PrimeBHT.TimeFrequency.X2
