module

public import PrimeBHT.TimeFrequency.X1.RealLine.LittlewoodPaley.Decay

/-!
# Reconstruction of `ψ^{[c]}` from the pieces `ψ_k^±` (blueprint node R3, steps 2-3)

`psiPlus χ c k y = λ_k g_{c,k}(λ_k y)` is the piece `ψ_k^+ = 𝓕⁻(ψ̂ β_k)` and `ψ_k^- = conj ψ_k^+`. We prove
`𝓕 g_{c,k}` is supported in `[8, 9]`, `g_{c,k}` is a Schwartz function, and for every `y`
`∑_{|k| ≤ K} (ψ_k^+ + ψ_k^-)(y) → ψ^{[c]}(y)` (this uses `ψ̂(0) = 0`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped FourierTransform ContDiff ENNReal Real
open PrimeBHT.Statements

namespace PrimeBHT.TimeFrequency.RealLine

/-- The piece `ψ_k^+(y) = λ_k g_{c,k}(λ_k y)`. -/
def psiPlus (χ : ℝ → ℝ) (c : ℝ) (k : ℤ) (y : ℝ) : ℂ := (lpLam k : ℂ) * gPiece χ c k (lpLam k * y)

/-! ## `g_{c,k}` is a Schwartz function with Fourier support in `[8, 9]` -/

/-- `h_{c,k}` as a Schwartz map. -/
def hSchwartz {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2) (k : ℤ) :
    SchwartzMap ℝ ℂ :=
  (hasCompactSupport_hFun k).toSchwartzMap (contDiff_hFun hχ hc k)

/-- `g_{c,k}` as a Schwartz map. -/
def gSchwartz {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2) (k : ℤ) :
    SchwartzMap ℝ ℂ :=
  𝓕⁻ (hSchwartz hχ hc k)

theorem coe_gSchwartz {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2) (k : ℤ) :
    ⇑(gSchwartz hχ hc k) = gPiece χ c k := by
  unfold gSchwartz gPiece
  rw [SchwartzMap.fourierInv_coe]; rfl

theorem fourier_gPiece {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2) (k : ℤ) :
    𝓕 (gPiece χ c k) = hFun χ c k := by
  have hS := hSchwartz hχ hc k
  have h1 : Continuous (hFun χ c k) := (contDiff_hFun hχ hc k).continuous
  have h2 : Integrable (hFun χ c k) := (hSchwartz hχ hc k).integrable
  have h3 : Integrable (𝓕 (hFun χ c k)) :=
    (SchwartzMap.fourierTransformCLM ℂ (hSchwartz hχ hc k)).integrable
  exact h1.fourier_fourierInv_eq h2 h3

theorem fourier_gPiece_eq_zero {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (k : ℤ) {ξ : ℝ} (hξ : ξ ∉ Set.Icc (8 : ℝ) 9) : 𝓕 (gPiece χ c k) ξ = 0 := by
  rw [fourier_gPiece hχ hc k]
  exact hFun_eq_zero_of_notMem k hξ

theorem continuous_gPiece {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2) (k : ℤ) :
    Continuous (gPiece χ c k) := by
  rw [← coe_gSchwartz hχ hc k]; exact (gSchwartz hχ hc k).continuous

theorem integrable_gPiece {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2) (k : ℤ) :
    Integrable (gPiece χ c k) := by
  rw [← coe_gSchwartz hχ hc k]; exact (gSchwartz hχ hc k).integrable

/-! ## Integral formula for the pieces -/

theorem fourierInv_real_eq_exp (f : ℝ → ℂ) (x : ℝ) :
    𝓕⁻ f x = ∫ v : ℝ, Complex.exp (↑(2 * π * v * x) * Complex.I) * f v := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]
  congr 3
  push_cast
  ring

theorem psiPlus_eq_integral {χ : ℝ → ℝ} (_hχ : IsCutoff χ) {c : ℝ} (_hc : c ∈ Set.Icc (1 : ℝ) 2)
    (k : ℤ) (y : ℝ) :
    psiPlus χ c k y = ∫ ζ : ℝ, Complex.exp (↑(2 * π * ζ * y) * Complex.I) *
      (𝓕 (psiCC χ c) ζ * (lpBump (ζ / lpLam k) : ℂ)) := by
  have hl := lpLam_ne_zero k
  have hlp := lpLam_pos k
  unfold psiPlus gPiece
  rw [fourierInv_real_eq_exp]
  set G : ℝ → ℂ := fun ζ => Complex.exp (↑(2 * π * ζ * y) * Complex.I) *
      (𝓕 (psiCC χ c) ζ * (lpBump (ζ / lpLam k) : ℂ)) with hG
  have h1 : ∀ η : ℝ, Complex.exp (↑(2 * π * η * (lpLam k * y)) * Complex.I) * hFun χ c k η =
      G (lpLam k * η) := by
    intro η
    simp only [hFun, hG, mul_div_cancel_left₀ _ hl]
    congr 3
    push_cast; ring
  simp_rw [h1]
  rw [Measure.integral_comp_mul_left G (lpLam k), abs_of_pos (inv_pos.2 hlp), Complex.real_smul,
    ← mul_assoc]
  have : (lpLam k : ℂ) * ((lpLam k)⁻¹ : ℝ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hl, Complex.ofReal_one]
  rw [this, one_mul]

theorem conj_exp_ofReal_mul_I (a : ℝ) :
    (starRingEnd ℂ) (Complex.exp (↑a * Complex.I)) = Complex.exp (↑(-a) * Complex.I) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem conj_fourier_psiCC_neg {χ : ℝ → ℝ} (c ζ : ℝ) :
    (starRingEnd ℂ) (𝓕 (psiCC χ c) (-ζ)) = 𝓕 (psiCC χ c) ζ := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul, map_mul, conj_exp_ofReal_mul_I, psiCC, Complex.conj_ofReal]
  congr 3
  ring

theorem conj_psiPlus_eq_integral {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (k : ℤ) (y : ℝ) :
    (starRingEnd ℂ) (psiPlus χ c k y) = ∫ ζ : ℝ, Complex.exp (↑(2 * π * ζ * y) * Complex.I) *
      (𝓕 (psiCC χ c) ζ * (lpBump (-ζ / lpLam k) : ℂ)) := by
  rw [psiPlus_eq_integral hχ hc, ← integral_conj, ← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
  simp only [map_mul, conj_exp_ofReal_mul_I, Complex.conj_ofReal, conj_fourier_psiCC_neg]
  congr 3
  ring

/-! ## Partial sums and the limit -/

theorem lpBump_bounded : ∃ B : ℝ, ∀ x, |lpBump x| ≤ B := by
  obtain ⟨B, hB⟩ := contDiff_lpBump.continuous.bounded_above_of_compact_support
    hasCompactSupport_lpBump
  exact ⟨B, fun x => by simpa using hB x⟩

/-- `𝓕 ψ^{[c]}` is integrable (Schwartz). -/
theorem integrable_fourier_psiCC {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2) :
    Integrable (𝓕 (psiCC χ c)) :=
  (SchwartzMap.fourierTransformCLM ℂ
    ((hasCompactSupport_psiCC hχ hc.1).toSchwartzMap (contDiff_psiCC hχ hc))).integrable

theorem continuous_fourier_psiCC {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2) :
    Continuous (𝓕 (psiCC χ c)) :=
  (contDiff_fourier_psiCC hχ hc).continuous

theorem integrable_fourier_mul {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (y : ℝ) {m : ℝ → ℝ} (hm : Continuous m) {B : ℝ} (hB : ∀ x, |m x| ≤ B) :
    Integrable (fun ζ : ℝ => Complex.exp (↑(2 * π * ζ * y) * Complex.I) *
      (𝓕 (psiCC χ c) ζ * (m ζ : ℂ))) := by
  refine Integrable.mono' ((integrable_fourier_psiCC hχ hc).norm.const_mul B) ?_
    (Eventually.of_forall fun ζ => ?_)
  · have h1 := continuous_fourier_psiCC hχ hc
    exact (by fun_prop : Continuous fun ζ : ℝ => Complex.exp (↑(2 * π * ζ * y) * Complex.I) *
      (𝓕 (psiCC χ c) ζ * (m ζ : ℂ))).aestronglyMeasurable
  · rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      mul_comm]
    exact mul_le_mul_of_nonneg_right (hB ζ) (norm_nonneg _)

/-- The partial sums of the partition of unity (both signs). -/
def mK (K : ℕ) (ζ : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(K : ℤ)) K, (lpBump (ζ / lpLam k) + lpBump (-ζ / lpLam k))

@[fun_prop]
theorem continuous_mK (K : ℕ) : Continuous (mK K) := by
  unfold mK
  refine continuous_finsetSum _ fun k _ => ?_
  exact (contDiff_lpBump.continuous.comp (continuous_id.div_const _)).add
    (contDiff_lpBump.continuous.comp (continuous_neg.div_const _))

theorem abs_mK_le (K : ℕ) (ζ : ℝ) : |mK K ζ| ≤ 2 := by
  rw [mK, Finset.sum_add_distrib]
  exact (abs_add_le _ _).trans (by linarith [abs_sum_lpBump_Icc_le ζ K, abs_sum_lpBump_Icc_le (-ζ) K])

theorem tendsto_mK {ζ : ℝ} (hζ : ζ ≠ 0) : Tendsto (fun K : ℕ => mK K ζ) atTop (𝓝 1) := by
  have e : ∀ K : ℕ, mK K ζ = ∑ k ∈ Finset.Icc (-(K : ℤ)) K, lpBump (ζ / lpLam k) +
      ∑ k ∈ Finset.Icc (-(K : ℤ)) K, lpBump (-ζ / lpLam k) := fun K => by
    rw [mK, Finset.sum_add_distrib]
  simp_rw [e]
  rcases lt_or_gt_of_ne hζ with h | h
  · have h0 : ∀ K : ℕ, ∑ k ∈ Finset.Icc (-(K : ℤ)) K, lpBump (ζ / lpLam k) = 0 :=
      fun K => sum_lpBump_Icc_nonpos h.le K
    simp_rw [h0, zero_add]
    exact tendsto_sum_lpBump_Icc (neg_pos.2 h)
  · have h0 : ∀ K : ℕ, ∑ k ∈ Finset.Icc (-(K : ℤ)) K, lpBump (-ζ / lpLam k) = 0 :=
      fun K => sum_lpBump_Icc_nonpos (by linarith) K
    simp_rw [h0, add_zero]
    exact tendsto_sum_lpBump_Icc h

theorem sum_psiPlus_add_conj {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (K : ℕ) (y : ℝ) :
    ∑ k ∈ Finset.Icc (-(K : ℤ)) K, (psiPlus χ c k y + (starRingEnd ℂ) (psiPlus χ c k y)) =
      ∫ ζ : ℝ, Complex.exp (↑(2 * π * ζ * y) * Complex.I) * (𝓕 (psiCC χ c) ζ * (mK K ζ : ℂ)) := by
  obtain ⟨B, hB⟩ := lpBump_bounded
  have hl := fun k => lpLam_pos k
  have hI1 : ∀ k : ℤ, Integrable (fun ζ : ℝ => Complex.exp (↑(2 * π * ζ * y) * Complex.I) *
      (𝓕 (psiCC χ c) ζ * (lpBump (ζ / lpLam k) : ℂ))) := fun k =>
    integrable_fourier_mul hχ hc y (contDiff_lpBump.continuous.comp (continuous_id.div_const _))
      (B := B) (fun x => hB _)
  have hI2 : ∀ k : ℤ, Integrable (fun ζ : ℝ => Complex.exp (↑(2 * π * ζ * y) * Complex.I) *
      (𝓕 (psiCC χ c) ζ * (lpBump (-ζ / lpLam k) : ℂ))) := fun k =>
    integrable_fourier_mul hχ hc y
      (contDiff_lpBump.continuous.comp (continuous_neg.div_const _)) (B := B) (fun x => hB _)
  have h2 : ∀ k : ℤ, (starRingEnd ℂ) (psiPlus χ c k y) = ∫ ζ : ℝ, Complex.exp (↑(2 * π * ζ * y) * Complex.I) *
      (𝓕 (psiCC χ c) ζ * (lpBump (-ζ / lpLam k) : ℂ)) := fun k => conj_psiPlus_eq_integral hχ hc k y
  have h1 : ∀ k : ℤ, psiPlus χ c k y = ∫ ζ : ℝ, Complex.exp (↑(2 * π * ζ * y) * Complex.I) *
      (𝓕 (psiCC χ c) ζ * (lpBump (ζ / lpLam k) : ℂ)) := fun k => psiPlus_eq_integral hχ hc k y
  simp_rw [h2, h1]
  have hI3 : ∀ k : ℤ, Integrable (fun ζ : ℝ => Complex.exp (↑(2 * π * ζ * y) * Complex.I) *
      (𝓕 (psiCC χ c) ζ * (lpBump (ζ / lpLam k) : ℂ)) +
      Complex.exp (↑(2 * π * ζ * y) * Complex.I) *
      (𝓕 (psiCC χ c) ζ * (lpBump (-ζ / lpLam k) : ℂ))) := fun k => (hI1 k).add (hI2 k)
  have h3 : ∀ k ∈ Finset.Icc (-(K : ℤ)) K,
      ((∫ ζ : ℝ, Complex.exp (↑(2 * π * ζ * y) * Complex.I) *
        (𝓕 (psiCC χ c) ζ * (lpBump (ζ / lpLam k) : ℂ))) +
      ∫ ζ : ℝ, Complex.exp (↑(2 * π * ζ * y) * Complex.I) *
        (𝓕 (psiCC χ c) ζ * (lpBump (-ζ / lpLam k) : ℂ))) =
      ∫ ζ : ℝ, (Complex.exp (↑(2 * π * ζ * y) * Complex.I) *
        (𝓕 (psiCC χ c) ζ * (lpBump (ζ / lpLam k) : ℂ)) +
        Complex.exp (↑(2 * π * ζ * y) * Complex.I) *
        (𝓕 (psiCC χ c) ζ * (lpBump (-ζ / lpLam k) : ℂ))) :=
    fun k _ => (integral_add (hI1 k) (hI2 k)).symm
  rw [Finset.sum_congr rfl h3, ← integral_finsetSum _ (fun k _ => hI3 k)]
  refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
  simp only [mK, Complex.ofReal_sum, Complex.ofReal_add, Finset.mul_sum, mul_add]

theorem fourier_psiCC_zero {χ : ℝ → ℝ} (hχ : IsCutoff χ) (c : ℝ) : 𝓕 (psiCC χ c) 0 = 0 := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simpa using integral_psiCC hχ c

theorem psiCC_eq_integral_fourier {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (y : ℝ) :
    psiCC χ c y = ∫ ζ : ℝ, Complex.exp (↑(2 * π * ζ * y) * Complex.I) * 𝓕 (psiCC χ c) ζ := by
  have hc1 := (contDiff_psiCC hχ hc).continuous
  have hint : Integrable (psiCC χ c) := hc1.integrable_of_hasCompactSupport (hasCompactSupport_psiCC hχ hc.1)
  have h := congrFun (hc1.fourierInv_fourier_eq hint (integrable_fourier_psiCC hχ hc)) y
  rw [← h, fourierInv_real_eq_exp]

/-- **Pointwise reconstruction.** For every `y`, `∑_{|k| ≤ K} (ψ_k^+ + ψ_k^-)(y) → ψ^{[c]}(y)`. -/
theorem tendsto_sum_psiPlus_add_conj {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ}
    (hc : c ∈ Set.Icc (1 : ℝ) 2) (y : ℝ) :
    Tendsto (fun K : ℕ => ∑ k ∈ Finset.Icc (-(K : ℤ)) K,
      (psiPlus χ c k y + (starRingEnd ℂ) (psiPlus χ c k y))) atTop (𝓝 (psiCC χ c y)) := by
  simp_rw [sum_psiPlus_add_conj hχ hc]
  rw [psiCC_eq_integral_fourier hχ hc y]
  have hF := continuous_fourier_psiCC hχ hc
  refine tendsto_integral_of_dominated_convergence (fun ζ => 2 * ‖𝓕 (psiCC χ c) ζ‖) (fun K => ?_)
    ((integrable_fourier_psiCC hχ hc).norm.const_mul 2) (fun K => Eventually.of_forall fun ζ => ?_)
    (Eventually.of_forall fun ζ => ?_)
  · exact (by fun_prop : Continuous fun ζ : ℝ => Complex.exp (↑(2 * π * ζ * y) * Complex.I) *
      (𝓕 (psiCC χ c) ζ * (mK K ζ : ℂ))).aestronglyMeasurable
  · rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_mK_le K ζ) (norm_nonneg _)
  · by_cases hζ : ζ = 0
    · subst hζ
      simp only [fourier_psiCC_zero hχ, zero_mul, mul_zero]
      exact tendsto_const_nhds
    · have h1 : Tendsto (fun K : ℕ => ((mK K ζ : ℝ) : ℂ)) atTop (𝓝 ((1 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 1).comp (tendsto_mK hζ)
      have h2 := (h1.const_mul (𝓕 (psiCC χ c) ζ)).const_mul
        (Complex.exp (↑(2 * π * ζ * y) * Complex.I))
      simpa using h2

end PrimeBHT.TimeFrequency.RealLine

end
