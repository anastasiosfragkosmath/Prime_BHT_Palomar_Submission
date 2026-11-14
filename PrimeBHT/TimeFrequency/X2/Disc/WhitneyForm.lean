module

public import PrimeBHT.TimeFrequency.X2.Disc.WhitneyScalar
public import PrimeBHT.TimeFrequency.X2.SymbolForm

/-!
# X2, node V05-3c (R1): V04 (iii) with the tensor Whitney cutoff

`whitneyW k ξ = wcut 62 258 (2^{7-k} ξ₁, 2^{7-k} ξ₂)` (`b_k = 2^{k-7}`) replaces `ρ̃(2^{-k}(ξ₂ - ξ₁))`:
`wPieceForm T f₁ f₂ f₃ (k, n) = ∫ whitneyW k ξ · Π(F̂₁(τ_a ·), F̂₂(τ_{-a} ·), F̂₃)` and
`hasSum_mul_wPieceForm`: `Σ_{(k,n)} c_{k,n} wPieceForm (k,n) = multiplierForm m T f₁ f₂ f₃`
(unconditionally convergent; `c = symbolCoeff m` of V04).
-/

@[expose] public noncomputable section

open MeasureTheory Complex
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate ContDiff Real
open PrimeBHT.Statements (yNorm tensorFun tensorFourier multiplierForm)

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Disc

/-- The Whitney weight of scale `k`: `wcut(ξ / b_k)`, `b_k = 2^{k-7}`. -/
def whitneyW (k : ℤ) (ξ : ℝ × ℝ) : ℝ := wcut 62 258 ((2 : ℝ) ^ (7 - k) * ξ.1, (2 : ℝ) ^ (7 - k) * ξ.2)

theorem continuous_whitneyW (k : ℤ) : Continuous (whitneyW k) := by
  unfold whitneyW
  exact (continuous_wcut 62 258).comp ((continuous_const.mul continuous_fst).prodMk
    (continuous_const.mul continuous_snd))

theorem abs_whitneyW_le (k : ℤ) (ξ : ℝ × ℝ) : |whitneyW k ξ| ≤ 1 := by
  unfold whitneyW
  rw [abs_of_nonneg (wcut_nonneg _ _ _)]; exact wcut_le_one _ _ _

/-- The three properties of the weights needed for the decomposition, at `t = ξ₂ - ξ₁`. -/
theorem whitneyW_props (ξ : ℝ × ℝ) (k : ℤ) :
    (whitneyW k ξ ≠ 0 → 3 / 10 < |(2 : ℝ) ^ (-k) * (ξ.2 - ξ.1)| ∧ |(2 : ℝ) ^ (-k) * (ξ.2 - ξ.1)| < 5 / 2) ∧
    (rho ((2 : ℝ) ^ (-k) * (ξ.2 - ξ.1)) ≠ 0 → whitneyW k ξ = 1) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-k) := zpow_pos (by norm_num) _
  have hy : |(2 : ℝ) ^ (7 - k) * ξ.2 - (2 : ℝ) ^ (7 - k) * ξ.1| = 128 * |(2 : ℝ) ^ (-k) * (ξ.2 - ξ.1)| := by
    have : (2 : ℝ) ^ (7 - k) * ξ.2 - (2 : ℝ) ^ (7 - k) * ξ.1 = 128 * ((2 : ℝ) ^ (-k) * (ξ.2 - ξ.1)) := by
      have h7 : (2 : ℝ) ^ (7 - k) = 128 * (2 : ℝ) ^ (-k) := by
        rw [show (7 - k : ℤ) = 7 + -k by ring, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; norm_num
      rw [h7]; ring
    rw [this, abs_mul]; norm_num
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := wcut_ne_zero_bounds h
    simp only at h1 h2
    rw [hy] at h1 h2
    constructor <;> push_cast at h1 h2 <;> linarith
  · intro h
    obtain ⟨h1, h2⟩ := abs_lt_of_rho_ne_zero h
    unfold whitneyW
    apply wcut_eq_one <;> simp only <;> rw [hy] <;> push_cast <;> linarith

/-- The Whitney piece of the form (the cutoff `ρ̃(2^{-k}(ξ₂-ξ₁))` of `pieceForm` replaced by `whitneyW k ξ`). -/
def wPieceForm {P : ℕ} [NeZero P] (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
    (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) (p : ℤ × ℤ) : ℂ :=
  ∫ ξ : ℝ × ℝ, (whitneyW p.1 ξ : ℂ) *
    T (tensorFourier (fun A => schwartzTranslate (symbolShift p) (f₁ A)) ξ.1)
      (tensorFourier (fun A => schwartzTranslate (-symbolShift p) (f₂ A)) ξ.2)
      (tensorFourier f₃ (ξ.1 + ξ.2))

theorem wPieceForm_integrand {P : ℕ} [NeZero P]
    (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
    (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) (c : ℤ → ℤ → ℂ) (p : ℤ × ℤ) (ξ : ℝ × ℝ) :
    c p.1 p.2 * ((whitneyW p.1 ξ : ℂ) *
      T (tensorFourier (fun A => schwartzTranslate (symbolShift p) (f₁ A)) ξ.1)
        (tensorFourier (fun A => schwartzTranslate (-symbolShift p) (f₂ A)) ξ.2)
        (tensorFourier f₃ (ξ.1 + ξ.2))) =
      gTerm c (fun k => whitneyW k ξ) (ξ.2 - ξ.1) p * formKernel T f₁ f₂ f₃ ξ := by
  rw [tensorFourier_schwartzTranslate, tensorFourier_schwartzTranslate]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, formKernel, gTerm]
  have h : Complex.exp (((-2 * π * symbolShift p * ξ.1 : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((-2 * π * (-symbolShift p) * ξ.2 : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((π * p.2 * (2 : ℝ) ^ (-p.1) * (ξ.2 - ξ.1) / 4 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [symbolShift]
    push_cast
    ring
  linear_combination (c p.1 p.2 * (whitneyW p.1 ξ : ℂ) *
    T (tensorFourier f₁ ξ.1) (tensorFourier f₂ ξ.2) (tensorFourier f₃ (ξ.1 + ξ.2))) * h

theorem mul_wPieceForm_eq_integral {P : ℕ} [NeZero P]
    (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
    (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) (c : ℤ → ℤ → ℂ) (p : ℤ × ℤ) :
    c p.1 p.2 * wPieceForm T f₁ f₂ f₃ p =
      ∫ ξ : ℝ × ℝ, gTerm c (fun k => whitneyW k ξ) (ξ.2 - ξ.1) p * formKernel T f₁ f₂ f₃ ξ := by
  unfold wPieceForm
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => wPieceForm_integrand T f₁ f₂ f₃ c p ξ)

theorem gTerm_zero_of_eq (c : ℤ → ℤ → ℂ) (ξ : ℝ × ℝ) (h : ξ.2 - ξ.1 = 0) (p : ℤ × ℤ) :
    gTerm c (fun k => whitneyW k ξ) (ξ.2 - ξ.1) p = 0 := by
  have hw : whitneyW p.1 ξ = 0 := by
    by_contra hne
    have := (whitneyW_props ξ p.1).1 hne
    rw [h, mul_zero, abs_zero] at this
    linarith [this.1]
  simp [gTerm, hw]

/-- **R1: V04 (iii) with the Whitney cutoff.**  Same hypotheses as `hasSum_mul_pieceForm` for `c = symbolCoeff m`. -/
theorem hasSum_mul_wPieceForm {m : ℝ → ℂ} (hm : ContDiffOn ℝ ∞ m {0}ᶜ) {b : ℤ → ℝ} (hb : Summable b)
    (hcb : ∀ k n, ‖symbolCoeff m k n‖ ≤ b n) {P : ℕ} [NeZero P]
    (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
    (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) :
    HasSum (fun p : ℤ × ℤ => symbolCoeff m p.1 p.2 * wPieceForm T f₁ f₂ f₃ p)
      (multiplierForm m T f₁ f₂ f₃) := by
  set c := symbolCoeff m with hcdef
  have hτ := integrable_formKernel T f₁ f₂ f₃
  have hb0 : ∀ n, 0 ≤ b n := fun n => (norm_nonneg _).trans (hcb 0 n)
  set B : ℝ := 4 * ∑' n, b n with hB
  set term : ℤ × ℤ → ℝ × ℝ → ℂ := fun p ξ =>
    gTerm c (fun k => whitneyW k ξ) (ξ.2 - ξ.1) p * formKernel T f₁ f₂ f₃ ξ with hterm
  have hwc : ∀ p : ℤ × ℤ, Continuous fun ξ : ℝ × ℝ => gTerm c (fun k => whitneyW k ξ) (ξ.2 - ξ.1) p := by
    intro p
    have := continuous_whitneyW p.1
    unfold gTerm
    fun_prop
  have hint : ∀ p, Integrable (term p) volume := fun p =>
    hτ.bdd_mul (c := ‖c p.1 p.2‖) (hwc p).aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => by
      rw [norm_gTerm]
      calc ‖c p.1 p.2‖ * |whitneyW p.1 ξ| ≤ ‖c p.1 p.2‖ * 1 :=
            mul_le_mul_of_nonneg_left (abs_whitneyW_le _ _) (norm_nonneg _)
        _ = ‖c p.1 p.2‖ := mul_one _)
  have hpt : ∀ (s : Finset (ℤ × ℤ)) (ξ : ℝ × ℝ), ∑ p ∈ s, ‖term p ξ‖ ≤ B * ‖formKernel T f₁ f₂ f₃ ξ‖ := by
    intro s ξ
    have h1 : ∑ p ∈ s, ‖term p ξ‖ = (∑ p ∈ s, ‖gTerm c (fun k => whitneyW k ξ) (ξ.2 - ξ.1) p‖) *
        ‖formKernel T f₁ f₂ f₃ ξ‖ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun p _ => by simp only [hterm, norm_mul]
    rw [h1]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    by_cases ht : ξ.2 - ξ.1 = 0
    · simp only [gTerm_zero_of_eq c ξ ht, norm_zero, Finset.sum_const_zero]
      rw [hB]
      exact mul_nonneg (by norm_num) (tsum_nonneg hb0)
    · obtain ⟨hs1, hs2⟩ := summable_norm_gTerm hb hcb ht (fun k => whitneyW k ξ)
        (fun k => abs_whitneyW_le k ξ) (fun k => (whitneyW_props ξ k).1)
      exact (hs1.sum_le_tsum s (fun p _ => norm_nonneg _)).trans hs2
  have hsumint : Summable (fun p : ℤ × ℤ => ∫ ξ, ‖term p ξ‖) := by
    refine summable_of_sum_le (c := B * ∫ ξ, ‖formKernel T f₁ f₂ f₃ ξ‖)
      (fun p => integral_nonneg fun ξ => norm_nonneg _) fun s => ?_
    rw [← integral_finsetSum _ (fun p _ => (hint p).norm), ← integral_const_mul]
    exact integral_mono (integrable_finsetSum _ fun p _ => (hint p).norm) (hτ.norm.const_mul B)
      (fun ξ => hpt s ξ)
  have hH := hasSum_integral_of_summable_integral_norm hint hsumint
  have hfun : (fun p : ℤ × ℤ => c p.1 p.2 * wPieceForm T f₁ f₂ f₃ p) = fun p => ∫ ξ, term p ξ :=
    funext fun p => mul_wPieceForm_eq_integral T f₁ f₂ f₃ c p
  rw [hfun]
  convert hH using 1
  unfold multiplierForm
  refine integral_congr_ae ?_
  filter_upwards [volume_diagonal_null] with ξ hξ
  have h1 : ∑' p, term p ξ = (∑' p, gTerm c (fun k => whitneyW k ξ) (ξ.2 - ξ.1) p) * formKernel T f₁ f₂ f₃ ξ :=
    tsum_mul_right
  rw [h1, (hasSum_gTerm hm hb hcb hξ (fun k => whitneyW k ξ) (fun k => abs_whitneyW_le k ξ)
    (fun k => (whitneyW_props ξ k).1) (fun k => (whitneyW_props ξ k).2)).tsum_eq]
  rfl

/-- **V04 (i) + R1 together**: constants `C_N` and for each admissible symbol the coefficients `c_{k,n}` with decay
and the Whitney-form decomposition. -/
theorem exists_whitney_decomposition_form :
    ∃ C : ℕ → ℝ, (∀ N, 0 ≤ C N) ∧ ∀ {m : ℝ → ℂ}, ContDiffOn ℝ ∞ m {0}ᶜ → ∀ {A : ℕ → ℝ},
      (∀ j : ℕ, ∀ t : ℝ, t ≠ 0 → |t| ^ j * ‖iteratedDeriv j m t‖ ≤ A j) →
      ∃ c : ℤ → ℤ → ℂ,
        (∀ (N : ℕ) (k n : ℤ), (1 + |(n : ℝ)|) ^ N * ‖c k n‖ ≤ C N * ∑ j ∈ Finset.range (N + 1), A j) ∧
        ∀ {P : ℕ} [NeZero P] (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
          (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)),
          HasSum (fun p : ℤ × ℤ => c p.1 p.2 * wPieceForm T f₁ f₂ f₃ p) (multiplierForm m T f₁ f₂ f₃) := by
  obtain ⟨C, hC0, hC⟩ := exists_decay_symbolCoeff
  refine ⟨C, hC0, fun {m} hm {A} hA => ⟨symbolCoeff m, hC hm hA, fun {P} _ T f₁ f₂ f₃ => ?_⟩⟩
  set b : ℤ → ℝ := fun n => C 2 * (∑ j ∈ Finset.range 3, A j) * ((1 + |(n : ℝ)|) ^ 2)⁻¹ with hb
  have hbs : Summable b := (summable_inv_one_add_abs_pow (le_refl 2)).mul_left _
  have hcb : ∀ k n, ‖symbolCoeff m k n‖ ≤ b n := by
    intro k n
    have := hC hm hA 2 k n
    have hpos : 0 < (1 + |(n : ℝ)|) ^ 2 := by positivity
    simp only [hb]
    rw [← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
    exact this
  exact hasSum_mul_wPieceForm hm hbs hcb T f₁ f₂ f₃

end PrimeBHT.TimeFrequency.X2.Disc
