module

public import PrimeBHT.TimeFrequency.X1.RealLine.KernelDecomposition
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Uniform Fourier bounds for the profiles `ψ^{[c]}` (blueprint node R3, step 4)

`psiCC χ c` is `ψ^{[c]}` as a complex-valued function. For `c ∈ [1, 2]`, uniformly in `c`:

* `exists_bound_iteratedFDeriv_fourier_psiCC`: `|ξ|^L ‖D^i 𝓕ψ^{[c]}(ξ)‖ ≤ A_{i,L}`;
* `norm_fourier_psiCC_le`: `‖𝓕ψ^{[c]}(ξ)‖ ≤ A |ξ|` (this uses `∫ψ^{[c]} = 0`, i.e. `ψ̂(0) = 0`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped FourierTransform ContDiff ENNReal Real
open PrimeBHT.Statements

namespace PrimeBHT.TimeFrequency.RealLine

/-- `ψ^{[c]}` as a complex-valued function. -/
def psiCC (χ : ℝ → ℝ) (c : ℝ) (y : ℝ) : ℂ := (psiC χ c y : ℂ)

theorem contDiff_psiCC {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2) :
    ContDiff ℝ ∞ (psiCC χ c) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_psiC hχ hc)

theorem psiCC_eq_zero_of_one_lt_abs {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : 1 ≤ c) {y : ℝ}
    (hy : 1 < |y|) : psiCC χ c y = 0 := by
  simp [psiCC, psiC_eq_zero_of_one_le_abs hχ hc hy.le]

theorem hasCompactSupport_psiCC {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : 1 ≤ c) :
    HasCompactSupport (psiCC χ c) :=
  (hasCompactSupport_psiC hχ hc).comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero

theorem iteratedFDeriv_psiCC_eq_zero {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : 1 ≤ c) (n : ℕ)
    {y : ℝ} (hy : 1 < |y|) : iteratedFDeriv ℝ n (psiCC χ c) y = 0 := by
  have hev : psiCC χ c =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    have hopen : IsOpen {z : ℝ | 1 < |z|} := isOpen_lt continuous_const continuous_abs
    filter_upwards [hopen.mem_nhds hy] with z hz
    exact psiCC_eq_zero_of_one_lt_abs hχ hc hz
  rw [(hev.iteratedFDeriv ℝ n).self_of_nhds]
  exact congrFun iteratedFDeriv_fun_zero y

theorem exists_bound_iteratedFDeriv_psiCC {χ : ℝ → ℝ} (hχ : IsCutoff χ) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ c ∈ Set.Icc (1 : ℝ) 2, ∀ y, ‖iteratedFDeriv ℝ n (psiCC χ c) y‖ ≤ A := by
  obtain ⟨A, hA⟩ := exists_bound_iteratedDeriv_psiC hχ n
  refine ⟨max A 0, le_max_right _ _, fun c hc y => ?_⟩
  have h1 : iteratedFDeriv ℝ n (psiCC χ c) y = iteratedFDeriv ℝ n (Complex.ofRealLI ∘ psiC χ c) y :=
    rfl
  rw [h1, Complex.ofRealLI.norm_iteratedFDeriv_comp_left (contDiff_psiC hχ hc).contDiffAt
    (by exact_mod_cast le_top), norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact (hA c hc y).trans (le_max_left _ _)

/-- An integral of a function vanishing off `[a, b]` and bounded by `B` on `[a, b]`. -/
theorem norm_integral_le_of_forall_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) {a b B : ℝ} (hab : a ≤ b) (hz : ∀ v, v ∉ Set.Icc a b → F v = 0)
    (hB : ∀ v ∈ Set.Icc a b, ‖F v‖ ≤ B) : ‖∫ v, F v‖ ≤ B * (b - a) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc a b) (fun v hv => hz v hv)]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc a b) (C := B)
    (by simp) hB
  rwa [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)] at this

theorem integral_pow_mul_iteratedFDeriv_psiCC_le {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ}
    (hc : c ∈ Set.Icc (1 : ℝ) 2) (a b : ℕ) {A : ℝ}
    (hA : ∀ y, ‖iteratedFDeriv ℝ b (psiCC χ c) y‖ ≤ A) :
    ∫ v, ‖v‖ ^ a * ‖iteratedFDeriv ℝ b (psiCC χ c) v‖ ≤ A * 2 := by
  have h := norm_integral_le_of_forall_Icc (fun v : ℝ => ‖v‖ ^ a * ‖iteratedFDeriv ℝ b (psiCC χ c) v‖)
    (a := -1) (b := 1) (B := A) (by norm_num)
    (fun v hv => by
      have hv' : 1 < |v| := by
        by_contra h'
        exact hv ⟨by linarith [abs_le.1 (not_lt.1 h')], by linarith [abs_le.1 (not_lt.1 h')]⟩
      simp [iteratedFDeriv_psiCC_eq_zero hχ hc.1 b hv'])
    (fun v hv => by
      have hv' : |v| ≤ 1 := abs_le.2 ⟨hv.1, hv.2⟩
      have h1 : ‖v‖ ^ a ≤ 1 := pow_le_one₀ (norm_nonneg _) (by simpa using hv')
      have h2 := hA v
      have h3 : 0 ≤ ‖iteratedFDeriv ℝ b (psiCC χ c) v‖ := norm_nonneg _
      calc ‖(‖v‖ ^ a * ‖iteratedFDeriv ℝ b (psiCC χ c) v‖)‖
          = ‖v‖ ^ a * ‖iteratedFDeriv ℝ b (psiCC χ c) v‖ := by
            rw [Real.norm_of_nonneg (by positivity)]
        _ ≤ 1 * A := mul_le_mul h1 h2 h3 zero_le_one
        _ = A := one_mul A)
  have h' : (∫ v, ‖v‖ ^ a * ‖iteratedFDeriv ℝ b (psiCC χ c) v‖) ≤
      ‖∫ v, ‖v‖ ^ a * ‖iteratedFDeriv ℝ b (psiCC χ c) v‖‖ := Real.le_norm_self _
  have h2 : A * (1 - -1) = A * 2 := by norm_num
  linarith

/-- **Uniform Schwartz bounds for `𝓕ψ^{[c]}`**, `c ∈ [1, 2]`. -/
theorem exists_bound_iteratedFDeriv_fourier_psiCC {χ : ℝ → ℝ} (hχ : IsCutoff χ) (i L : ℕ) :
    ∃ A : ℝ, ∀ c ∈ Set.Icc (1 : ℝ) 2, ∀ ξ : ℝ,
      ‖ξ‖ ^ L * ‖iteratedFDeriv ℝ i (𝓕 (psiCC χ c)) ξ‖ ≤ A := by
  choose A hA0 hA using exists_bound_iteratedFDeriv_psiCC hχ
  refine ⟨(2 * π) ^ i * (2 * i + 2) ^ L *
    ∑ p ∈ Finset.range (i + 1) ×ˢ Finset.range (L + 1), A p.2 * 2, fun c hc ξ => ?_⟩
  have hcd := contDiff_psiCC hχ hc
  have hint : ∀ (k n : ℕ), (k : ℕ∞) ≤ (⊤ : ℕ∞) → (n : ℕ∞) ≤ (⊤ : ℕ∞) →
      Integrable (fun v : ℝ => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (psiCC χ c) v‖) := by
    intro k n _ _
    have hc1 : Continuous (fun v : ℝ => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (psiCC χ c) v‖) := by
      apply Continuous.mul (by fun_prop)
      exact (hcd.of_le (mod_cast le_top)).continuous_iteratedFDeriv'.norm
    refine hc1.integrable_of_hasCompactSupport ?_
    exact ((hasCompactSupport_psiCC hχ hc.1).iteratedFDeriv _).norm.mul_left
  have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := ⊤) (N := ⊤) (f := psiCC χ c) hcd hint
    (k := i) (n := L) le_top le_top ξ
  refine h.trans ?_
  gcongr with p hp
  exact integral_pow_mul_iteratedFDeriv_psiCC_le hχ hc _ _ (hA _ c hc)

theorem integral_psiCC {χ : ℝ → ℝ} (hχ : IsCutoff χ) (c : ℝ) : ∫ y, psiCC χ c y = 0 := by
  have h : ∫ y, psiCC χ c y = ((∫ y, psiC χ c y : ℝ) : ℂ) := by
    exact integral_ofReal
  rw [h, integral_psiC hχ, Complex.ofReal_zero]

/-- **`ψ̂(0) = 0` quantitatively:** `‖𝓕ψ^{[c]}(ξ)‖ ≤ A |ξ|` for `c ∈ [1, 2]`. -/
theorem exists_norm_fourier_psiCC_le {χ : ℝ → ℝ} (hχ : IsCutoff χ) :
    ∃ A : ℝ, ∀ c ∈ Set.Icc (1 : ℝ) 2, ∀ ξ : ℝ, ‖𝓕 (psiCC χ c) ξ‖ ≤ A * |ξ| := by
  obtain ⟨A0, hA00, hA0⟩ := exists_bound_iteratedFDeriv_psiCC hχ 0
  refine ⟨4 * π * A0, fun c hc ξ => ?_⟩
  have hcd := contDiff_psiCC hχ hc
  have hint : Integrable (psiCC χ c) :=
    (hcd.continuous).integrable_of_hasCompactSupport (hasCompactSupport_psiCC hχ hc.1)
  have hexp : Continuous (fun v : ℝ => Complex.exp (↑(-2 * π * v * ξ) * Complex.I)) := by fun_prop
  have hint2 : Integrable (fun v : ℝ => Complex.exp (↑(-2 * π * v * ξ) * Complex.I) • psiCC χ c v) :=
    (hexp.mul hcd.continuous).integrable_of_hasCompactSupport
      ((hasCompactSupport_psiCC hχ hc.1).mul_left)
  have hF : 𝓕 (psiCC χ c) ξ =
      ∫ v : ℝ, (Complex.exp (↑(-2 * π * v * ξ) * Complex.I) - 1) * psiCC χ c v := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    have : ∫ v : ℝ, (Complex.exp (↑(-2 * π * v * ξ) * Complex.I) - 1) * psiCC χ c v =
        (∫ v : ℝ, Complex.exp (↑(-2 * π * v * ξ) * Complex.I) • psiCC χ c v) -
          ∫ v : ℝ, psiCC χ c v := by
      rw [← integral_sub hint2 hint]
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      simp only [smul_eq_mul]; ring
    rw [this, integral_psiCC hχ, sub_zero]
  rw [hF]
  have hb := norm_integral_le_of_forall_Icc (fun v : ℝ =>
    (Complex.exp (↑(-2 * π * v * ξ) * Complex.I) - 1) * psiCC χ c v) (a := -1) (b := 1)
    (B := 2 * π * |ξ| * A0) (by norm_num)
    (fun v hv => by
      have hv' : 1 < |v| := by
        by_contra h'
        exact hv ⟨by linarith [abs_le.1 (not_lt.1 h')], by linarith [abs_le.1 (not_lt.1 h')]⟩
      simp [psiCC_eq_zero_of_one_lt_abs hχ hc.1 hv'])
    (fun v hv => by
      have hv' : |v| ≤ 1 := abs_le.2 ⟨hv.1, hv.2⟩
      have h1 : ‖Complex.exp (↑(-2 * π * v * ξ) * Complex.I) - 1‖ ≤ 2 * π * |ξ| := by
        have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -2 * π * v * ξ)
        rw [mul_comm Complex.I] at this
        refine this.trans ?_
        rw [Real.norm_eq_abs]
        simp only [abs_mul, abs_neg, abs_two, abs_of_pos Real.pi_pos]
        have : 2 * π * |v| * |ξ| ≤ 2 * π * 1 * |ξ| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv' (by positivity)) (abs_nonneg _)
        linarith
      have h2 : ‖psiCC χ c v‖ ≤ A0 := by simpa using hA0 c hc v
      rw [norm_mul]
      exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity))
  calc ‖∫ v : ℝ, (Complex.exp (↑(-2 * π * v * ξ) * Complex.I) - 1) * psiCC χ c v‖
      ≤ 2 * π * |ξ| * A0 * (1 - -1) := hb
    _ = 4 * π * A0 * |ξ| := by ring

end PrimeBHT.TimeFrequency.RealLine

end
