module

public import PrimeBHT.TimeFrequency.X2.Disc.PairTerm

/-!
# X2, node V05 (R4-4a): `wPieceForm (k, n)` is the sum of the Whitney pair terms

`hasSum_pairTerm`: for every `(k, n)`, `Σ_{(n₁,n₂): 62 ≤ |n₂ - n₁| ≤ 258} pairTerm k n n₁ (n₂ - n₁) = wPieceForm (k, n)`
(unconditionally convergent), because `Σ_{(n₁,n₂)} φ(x₁ - n₁) φ(x₂ - n₂) 1_{D} = wcut(x) ≤ 1`.
-/

@[expose] public noncomputable section

open MeasureTheory Complex
open scoped FourierTransform SchwartzMap ComplexConjugate Real ContDiff
open PrimeBHT.Statements (yNorm tensorFun tensorFourier multiplierForm)

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Disc

variable {P : ℕ} [NeZero P]

/-- The shifted Fourier-side form integrand. -/
def Tsh (T : Form P) (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) (k n : ℤ) (ξ : ℝ × ℝ) : ℂ :=
  T (tensorFourier (fun A => schwartzTranslate (symbolShift (k, n)) (f₁ A)) ξ.1)
    (tensorFourier (fun A => schwartzTranslate (-symbolShift (k, n)) (f₂ A)) ξ.2)
    (tensorFourier f₃ (ξ.1 + ξ.2))

theorem Tsh_eq (T : Form P) (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) (k n : ℤ) (ξ : ℝ × ℝ) :
    Tsh T f₁ f₂ f₃ k n ξ = Complex.exp (((π * n * (2 : ℝ) ^ (-k) * (ξ.2 - ξ.1) / 4 : ℝ) : ℂ) * Complex.I) *
      formKernel T f₁ f₂ f₃ ξ := by
  unfold Tsh
  rw [tensorFourier_schwartzTranslate, tensorFourier_schwartzTranslate]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, formKernel]
  have h : Complex.exp (((-2 * π * symbolShift (k, n) * ξ.1 : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((-2 * π * (-symbolShift (k, n)) * ξ.2 : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((π * n * (2 : ℝ) ^ (-k) * (ξ.2 - ξ.1) / 4 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [symbolShift]
    push_cast
    ring
  linear_combination (T (tensorFourier f₁ ξ.1) (tensorFourier f₂ ξ.2) (tensorFourier f₃ (ξ.1 + ξ.2))) * h

theorem norm_Tsh (T : Form P) (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) (k n : ℤ) (ξ : ℝ × ℝ) :
    ‖Tsh T f₁ f₂ f₃ k n ξ‖ = ‖formKernel T f₁ f₂ f₃ ξ‖ := by
  rw [Tsh_eq, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem continuous_Tsh_phase (k n : ℤ) :
    Continuous fun ξ : ℝ × ℝ => Complex.exp (((π * n * (2 : ℝ) ^ (-k) * (ξ.2 - ξ.1) / 4 : ℝ) : ℂ) * Complex.I) := by
  fun_prop

/-- The Whitney weight of the pair `p = (n₁, n₂)` at scale `k` restricted to `62 ≤ |n₂ - n₁| ≤ 258`. -/
def pairW (k : ℤ) (p : ℤ × ℤ) (ξ : ℝ × ℝ) : ℝ :=
  if 62 ≤ |p.2 - p.1| ∧ |p.2 - p.1| ≤ 258 then
    wphi ((2 : ℝ) ^ (7 - k) * ξ.1 - p.1) * wphi ((2 : ℝ) ^ (7 - k) * ξ.2 - p.2) else 0

theorem pairW_nonneg (k : ℤ) (p : ℤ × ℤ) (ξ : ℝ × ℝ) : 0 ≤ pairW k p ξ := by
  unfold pairW; split_ifs
  · exact mul_nonneg (wphi_nonneg _) (wphi_nonneg _)
  · exact le_rfl

theorem pairW_le_one (k : ℤ) (p : ℤ × ℤ) (ξ : ℝ × ℝ) : pairW k p ξ ≤ 1 := by
  unfold pairW; split_ifs
  · calc _ ≤ 1 * 1 := mul_le_mul (wphi_le_one _) (wphi_le_one _) (wphi_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · exact zero_le_one

theorem continuous_pairW (k : ℤ) (p : ℤ × ℤ) : Continuous (pairW k p) := by
  have := contDiff_wphi.continuous
  unfold pairW
  split_ifs
  · fun_prop
  · exact continuous_const

theorem summable_wcutTerm (lo hi : ℤ) (x : ℝ × ℝ) :
    Summable fun p : ℤ × ℤ =>
      (if lo ≤ |p.2 - p.1| ∧ |p.2 - p.1| ≤ hi then wphi (x.1 - p.1) * wphi (x.2 - p.2) else 0) := by
  have hs : Summable fun p : ℤ × ℤ => wphi (x.1 - p.1) * wphi (x.2 - p.2) :=
    Summable.mul_of_nonneg (f := fun n : ℤ => wphi (x.1 - n)) (g := fun n : ℤ => wphi (x.2 - n))
      (hasSum_wphi x.1).summable (hasSum_wphi x.2).summable
      (fun n => wphi_nonneg _) (fun n => wphi_nonneg _)
  refine Summable.of_nonneg_of_le (wcut_term_nonneg lo hi x) (fun p => ?_) hs
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (wphi_nonneg _) (wphi_nonneg _)

theorem hasSum_pairW (k : ℤ) (ξ : ℝ × ℝ) : HasSum (fun p => pairW k p ξ) (whitneyW k ξ) := by
  unfold pairW whitneyW wcut
  exact (summable_wcutTerm 62 258 ((2 : ℝ) ^ (7 - k) * ξ.1, (2 : ℝ) ^ (7 - k) * ξ.2)).hasSum

/-- The pair term in the `(n₁, n₂)` indexing (weights as in `wcut`). -/
def pairTermP (T : Form P) (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) (k n : ℤ) (p : ℤ × ℤ) : ℂ :=
  ∫ ξ : ℝ × ℝ, ((wphi ((2 : ℝ) ^ (7 - k) * ξ.1 - p.1) * wphi ((2 : ℝ) ^ (7 - k) * ξ.2 - p.2) : ℝ) : ℂ) *
    Tsh T f₁ f₂ f₃ k n ξ

theorem div_bk (k : ℤ) (x : ℝ) : x / bk k = (2 : ℝ) ^ (7 - k) * x := by
  unfold bk
  rw [div_eq_mul_inv, ← zpow_neg, show -(k - 7) = 7 - k by ring, mul_comm]

theorem pairTerm_eq_pairTermP (T : Form P) (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) (k n : ℤ) (p : ℤ × ℤ) :
    pairTerm T f₁ f₂ f₃ k n p.1 (p.2 - p.1) = pairTermP T f₁ f₂ f₃ k n p := by
  unfold pairTerm pairTermP Tsh
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [div_bk, show p.1 + (p.2 - p.1) = p.2 by ring]

/-- **R4-4a.**  `wPieceForm (k, n) = Σ_{(n₁,n₂)} 1_D pairTerm k n n₁ (n₂ - n₁)`. -/
theorem hasSum_pairTerm (T : Form P) (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) (k n : ℤ) :
    HasSum (fun p : ℤ × ℤ => if 62 ≤ |p.2 - p.1| ∧ |p.2 - p.1| ≤ 258 then
      pairTerm T f₁ f₂ f₃ k n p.1 (p.2 - p.1) else 0) (wPieceForm T f₁ f₂ f₃ (k, n)) := by
  have hτ := integrable_formKernel T f₁ f₂ f₃
  set term : ℤ × ℤ → ℝ × ℝ → ℂ := fun p ξ => (pairW k p ξ : ℂ) * Tsh T f₁ f₂ f₃ k n ξ with hterm
  have hint : ∀ p, Integrable (term p) volume := by
    intro p
    have hc : Continuous fun ξ : ℝ × ℝ => (pairW k p ξ : ℂ) * Complex.exp (((π * n * (2 : ℝ) ^ (-k) *
        (ξ.2 - ξ.1) / 4 : ℝ) : ℂ) * Complex.I) :=
      (Complex.continuous_ofReal.comp (continuous_pairW k p)).mul (continuous_Tsh_phase k n)
    refine (hτ.bdd_mul (c := 1) hc.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)).congr
      (Filter.Eventually.of_forall fun ξ => ?_)
    · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (pairW_nonneg _ _ _)]
      exact pairW_le_one _ _ _
    · simp only [hterm, Tsh_eq]; ring
  have hpt : ∀ (s : Finset (ℤ × ℤ)) (ξ : ℝ × ℝ), ∑ p ∈ s, ‖term p ξ‖ ≤ ‖formKernel T f₁ f₂ f₃ ξ‖ := by
    intro s ξ
    have h1 : ∑ p ∈ s, ‖term p ξ‖ = (∑ p ∈ s, pairW k p ξ) * ‖formKernel T f₁ f₂ f₃ ξ‖ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [hterm, norm_mul, norm_Tsh, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (pairW_nonneg _ _ _)]
    rw [h1]
    have h2 : ∑ p ∈ s, pairW k p ξ ≤ 1 := by
      have := sum_le_hasSum s (fun p _ => pairW_nonneg k p ξ) (hasSum_pairW k ξ)
      refine this.trans ?_
      unfold whitneyW; exact wcut_le_one _ _ _
    calc (∑ p ∈ s, pairW k p ξ) * ‖formKernel T f₁ f₂ f₃ ξ‖ ≤ 1 * ‖formKernel T f₁ f₂ f₃ ξ‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = _ := one_mul _
  have hsumint : Summable (fun p : ℤ × ℤ => ∫ ξ, ‖term p ξ‖) := by
    refine summable_of_sum_le (c := ∫ ξ, ‖formKernel T f₁ f₂ f₃ ξ‖)
      (fun p => integral_nonneg fun ξ => norm_nonneg _) fun s => ?_
    rw [← integral_finsetSum _ (fun p _ => (hint p).norm)]
    exact integral_mono (integrable_finsetSum _ fun p _ => (hint p).norm) hτ.norm (fun ξ => hpt s ξ)
  have hH := hasSum_integral_of_summable_integral_norm hint hsumint
  have e1 : (fun p : ℤ × ℤ => if 62 ≤ |p.2 - p.1| ∧ |p.2 - p.1| ≤ 258 then
      pairTerm T f₁ f₂ f₃ k n p.1 (p.2 - p.1) else 0) = fun p => ∫ ξ, term p ξ := by
    funext p
    by_cases hc : 62 ≤ |p.2 - p.1| ∧ |p.2 - p.1| ≤ 258
    · rw [ite_eq_left hc, pairTerm_eq_pairTermP]
      unfold pairTermP
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      simp only [hterm, pairW, ite_eq_left hc]
    · rw [ite_eq_right hc]
      have : ∀ ξ, term p ξ = 0 := fun ξ => by simp only [hterm, pairW, ite_eq_right hc]; simp
      simp [this]
  rw [e1]
  convert hH using 1
  unfold wPieceForm
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  have h2 : HasSum (fun p => term p ξ) ((whitneyW k ξ : ℂ) * Tsh T f₁ f₂ f₃ k n ξ) :=
    ((Complex.hasSum_ofReal.2 (hasSum_pairW k ξ)).mul_right (Tsh T f₁ f₂ f₃ k n ξ))
  dsimp only
  rw [h2.tsum_eq]
  rfl

end PrimeBHT.TimeFrequency.X2.Disc
