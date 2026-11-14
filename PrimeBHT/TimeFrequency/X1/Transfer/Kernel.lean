module

public import PrimeBHT.Frozen.BhtKernelR
public import PrimeBHT.Frozen.IsCutoff
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Support

/-!
# Part Z2 of `docs/x1-blueprint.md`: kernel bounds, uniform in the two scales

For a cutoff `χ` (`PrimeBHT.Statements.IsCutoff`) and `0 < λ ≤ μ` the frozen kernel
`PrimeBHT.Statements.bhtKernelR χ λ μ y = (χ(λ y) - χ(μ y)) / y` (`K_{λ,μ}`, with `λ = 1/L₂`, `μ = 1/L₁`)
satisfies, with a constant depending on `χ` only:

* `K = 0` for `|y| ≤ 1/(2μ)` and for `|y| ≥ 1/λ` (`bhtKernelR_eq_zero_of_abs_le`,
  `bhtKernelR_eq_zero_of_inv_le_abs`), `K` is `C^∞` (`contDiff_bhtKernelR`), continuous with compact support;
* `|y| |K(y)| ≤ C` and `y² |K'(y)| ≤ C` (`exists_kernel_bounds`).

The evenness of `χ` is not used. (Blueprint corrections: `K = 0` already for `|y| ≤ L₁/2` (closed), and in
the derivative bound the correct inequality is `λ|y| < 1` whenever `χ'(λ y) ≠ 0`, i.e. `λ ≤ 1/|y|`, not
`1/L ≤ 2/|y|` from `|y|/L ≥ 1/2`.)
-/

@[expose] public noncomputable section

open Filter Topology
open scoped ContDiff

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Transfer

open PrimeBHT.Statements

/-! ## The cutoff API -/

theorem cutoff_eq_one_of_abs_le {χ : ℝ → ℝ} (hχ : IsCutoff χ) {t : ℝ} (ht : |t| ≤ 1 / 2) : χ t = 1 :=
  hχ.2.2.2 t (by rw [Set.mem_Icc]; constructor <;> linarith [abs_le.1 ht])

theorem cutoff_eq_zero_of_one_le_abs {χ : ℝ → ℝ} (hχ : IsCutoff χ) {t : ℝ} (ht : 1 ≤ |t|) : χ t = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  rcases hχ.2.2.1 h with ⟨h1, h2⟩
  rcases le_abs'.1 ht with h | h <;> linarith

theorem cutoff_continuous {χ : ℝ → ℝ} (hχ : IsCutoff χ) : Continuous χ := hχ.1.continuous

theorem cutoff_hasCompactSupport {χ : ℝ → ℝ} (hχ : IsCutoff χ) : HasCompactSupport χ := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro t ht
  apply cutoff_eq_zero_of_one_le_abs hχ
  by_contra h
  rw [not_le, abs_lt] at h
  exact ht ⟨h.1.le, h.2.le⟩

/-- A cutoff is bounded. -/
theorem cutoff_exists_bound {χ : ℝ → ℝ} (hχ : IsCutoff χ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |χ t| ≤ B := by
  obtain ⟨C, hC⟩ := (cutoff_continuous hχ).bounded_above_of_compact_support (cutoff_hasCompactSupport hχ)
  exact ⟨max C 0, le_max_right _ _,
    fun t => (le_of_eq_of_le (Real.norm_eq_abs _).symm (hC t)).trans (le_max_left _ _)⟩

/-- The derivative of a cutoff is bounded. -/
theorem cutoff_exists_deriv_bound {χ : ℝ → ℝ} (hχ : IsCutoff χ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |deriv χ t| ≤ B := by
  have hc : HasCompactSupport (deriv χ) := (cutoff_hasCompactSupport hχ).deriv
  have hcont : Continuous (deriv χ) := hχ.1.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hc
  exact ⟨max C 0, le_max_right _ _,
    fun t => (le_of_eq_of_le (Real.norm_eq_abs _).symm (hC t)).trans (le_max_left _ _)⟩

/-- `χ' (t) ≠ 0` forces `|t| < 1` (`tsupport χ ⊆ (-1, 1)`). -/
theorem cutoff_abs_lt_one_of_deriv_ne_zero {χ : ℝ → ℝ} (hχ : IsCutoff χ) {t : ℝ}
    (ht : deriv χ t ≠ 0) : |t| < 1 := by
  have h1 : t ∈ tsupport (deriv χ) := subset_tsupport _ ht
  have h2 := hχ.2.2.1 (tsupport_deriv_subset h1)
  rw [abs_lt]
  exact ⟨h2.1, h2.2⟩

/-! ## Value, support, continuity -/

theorem bhtKernelR_zero (χ : ℝ → ℝ) (lam mu : ℝ) : bhtKernelR χ lam mu 0 = 0 := by
  simp [bhtKernelR]

/-- For a cutoff and `0 < λ ≤ μ`: `K_{λ,μ}(y) = 0` for `|y| ≤ 1/(2μ)`. -/
theorem bhtKernelR_eq_zero_of_abs_le {χ : ℝ → ℝ} (hχ : IsCutoff χ) {lam mu : ℝ} (hlam : 0 < lam)
    (hlm : lam ≤ mu) {y : ℝ} (hy : |y| ≤ 1 / (2 * mu)) : bhtKernelR χ lam mu y = 0 := by
  have hmu : 0 < mu := hlam.trans_le hlm
  have hy' : mu * |y| ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity)] at hy
    linarith
  have h1 : χ (mu * y) = 1 := by
    apply cutoff_eq_one_of_abs_le hχ
    rw [abs_mul, abs_of_pos hmu]; exact hy'
  have h2 : χ (lam * y) = 1 := by
    apply cutoff_eq_one_of_abs_le hχ
    rw [abs_mul, abs_of_pos hlam]
    exact (mul_le_mul_of_nonneg_right hlm (abs_nonneg y)).trans hy'
  simp [bhtKernelR, h1, h2]

/-- For a cutoff and `0 < λ ≤ μ`: `K_{λ,μ}(y) = 0` for `|y| ≥ 1/λ`. -/
theorem bhtKernelR_eq_zero_of_inv_le_abs {χ : ℝ → ℝ} (hχ : IsCutoff χ) {lam mu : ℝ}
    (hlam : 0 < lam) (hlm : lam ≤ mu) {y : ℝ} (hy : 1 / lam ≤ |y|) :
    bhtKernelR χ lam mu y = 0 := by
  have hmu : 0 < mu := hlam.trans_le hlm
  have hy' : 1 ≤ lam * |y| := by
    rw [div_le_iff₀ hlam] at hy
    linarith
  have h1 : χ (lam * y) = 0 := by
    apply cutoff_eq_zero_of_one_le_abs hχ
    rw [abs_mul, abs_of_pos hlam]; exact hy'
  have h2 : χ (mu * y) = 0 := by
    apply cutoff_eq_zero_of_one_le_abs hχ
    rw [abs_mul, abs_of_pos hmu]
    exact hy'.trans (mul_le_mul_of_nonneg_right hlm (abs_nonneg y))
  simp [bhtKernelR, h1, h2]

theorem bhtKernelR_eq_zero_of_notMem_Icc {χ : ℝ → ℝ} (hχ : IsCutoff χ) {lam mu : ℝ}
    (hlam : 0 < lam) (hlm : lam ≤ mu) {y : ℝ} (hy : y ∉ Set.Icc (-(1 / lam)) (1 / lam)) :
    bhtKernelR χ lam mu y = 0 := by
  apply bhtKernelR_eq_zero_of_inv_le_abs hχ hlam hlm
  by_contra h
  rw [not_le, abs_lt] at h
  exact hy ⟨h.1.le, h.2.le⟩

/-- `K_{λ,μ}` is continuous (`K = 0` near `0`, a quotient of continuous functions elsewhere). -/
theorem continuous_bhtKernelR {χ : ℝ → ℝ} (hχ : IsCutoff χ) {lam mu : ℝ} (hlam : 0 < lam)
    (hlm : lam ≤ mu) : Continuous (bhtKernelR χ lam mu) := by
  have hmu : 0 < mu := hlam.trans_le hlm
  refine continuous_iff_continuousAt.2 fun y => ?_
  by_cases hy : y = 0
  · subst hy
    have hev : bhtKernelR χ lam mu =ᶠ[𝓝 (0 : ℝ)] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < 1 / (2 * mu))]
        with z hz
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hz
      exact bhtKernelR_eq_zero_of_abs_le hχ hlam hlm hz.le
    exact continuousAt_const.congr hev.symm
  · have h1 : Continuous fun z : ℝ => χ (lam * z) :=
      (cutoff_continuous hχ).comp (continuous_const.mul continuous_id)
    have h2 : Continuous fun z : ℝ => χ (mu * z) :=
      (cutoff_continuous hχ).comp (continuous_const.mul continuous_id)
    exact (h1.sub h2).continuousAt.div continuousAt_id hy

/-- `K_{λ,μ}` is `C^∞`. -/
theorem contDiff_bhtKernelR {χ : ℝ → ℝ} (hχ : IsCutoff χ) {lam mu : ℝ} (hlam : 0 < lam)
    (hlm : lam ≤ mu) : ContDiff ℝ ∞ (bhtKernelR χ lam mu) := by
  have hmu : 0 < mu := hlam.trans_le hlm
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = 0
  · subst hy
    have hev : bhtKernelR χ lam mu =ᶠ[𝓝 (0 : ℝ)] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < 1 / (2 * mu))]
        with z hz
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hz
      exact bhtKernelR_eq_zero_of_abs_le hχ hlam hlm hz.le
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
  · have h1 : ContDiff ℝ ∞ fun z : ℝ => χ (lam * z) := hχ.1.comp (contDiff_const.mul contDiff_id)
    have h2 : ContDiff ℝ ∞ fun z : ℝ => χ (mu * z) := hχ.1.comp (contDiff_const.mul contDiff_id)
    exact (h1.sub h2).contDiffAt.div contDiffAt_id hy

/-! ## Size and derivative bounds -/

/-- `|y K_{λ,μ}(y)| ≤ 2B` where `B` bounds `|χ|`. -/
theorem abs_mul_bhtKernelR_le {χ : ℝ → ℝ} {B : ℝ} (hB : ∀ t, |χ t| ≤ B) (lam mu y : ℝ) :
    |y| * |bhtKernelR χ lam mu y| ≤ 2 * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  by_cases hy : y = 0
  · subst hy; simp only [abs_zero, zero_mul]; positivity
  · have : y * bhtKernelR χ lam mu y = χ (lam * y) - χ (mu * y) := by
      unfold bhtKernelR; field_simp
    rw [← abs_mul, this]
    calc |χ (lam * y) - χ (mu * y)| ≤ |χ (lam * y)| + |χ (mu * y)| := abs_sub _ _
      _ ≤ B + B := add_le_add (hB _) (hB _)
      _ = 2 * B := by ring

theorem hasDerivAt_bhtKernelR {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (lam mu : ℝ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (bhtKernelR χ lam mu)
      (((deriv χ (lam * y) * lam - deriv χ (mu * y) * mu) * y - (χ (lam * y) - χ (mu * y)) * 1) /
        y ^ 2) y := by
  have hd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have h1 : HasDerivAt (fun z => χ (lam * z)) (deriv χ (lam * y) * lam) y := by
    have := (hd (lam * y)).hasDerivAt.comp y ((hasDerivAt_id' y).const_mul lam)
    exact this.congr_deriv (by ring)
  have h2 : HasDerivAt (fun z => χ (mu * z)) (deriv χ (mu * y) * mu) y := by
    have := (hd (mu * y)).hasDerivAt.comp y ((hasDerivAt_id' y).const_mul mu)
    exact this.congr_deriv (by ring)
  exact HasDerivAt.fun_div (HasDerivAt.sub h1 h2) (hasDerivAt_id' y) hy

/-- `|c χ'(c y) y| ≤ B'` when `|χ'| ≤ B'` and `χ'(t) ≠ 0 → |t| < 1`. -/
theorem abs_mul_deriv_le {χ : ℝ → ℝ} (hχ : IsCutoff χ) {B' : ℝ} (hB'0 : 0 ≤ B')
    (hB' : ∀ t, |deriv χ t| ≤ B') (c y : ℝ) : |deriv χ (c * y) * c * y| ≤ B' := by
  by_cases h : deriv χ (c * y) = 0
  · simp [h, hB'0]
  · have h1 := cutoff_abs_lt_one_of_deriv_ne_zero hχ h
    rw [abs_mul c y] at h1
    calc |deriv χ (c * y) * c * y| = |deriv χ (c * y)| * (|c| * |y|) := by
          rw [mul_assoc, abs_mul, abs_mul]
      _ ≤ B' * 1 := mul_le_mul (hB' _) h1.le (by positivity) hB'0
      _ = B' := mul_one _

/-- **Z2 (b), uniform in the two scales.** For a cutoff there is `C ≥ 0` such that for all `0 < λ ≤ μ`
the kernel `K = K_{λ,μ}` is `C^∞`, `|y| |K(y)| ≤ C` and `y² |K'(y)| ≤ C` for all `y` (at `y = 0`
trivially). -/
theorem exists_kernel_bounds {χ : ℝ → ℝ} (hχ : IsCutoff χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam mu : ℝ, 0 < lam → lam ≤ mu →
      ContDiff ℝ ∞ (bhtKernelR χ lam mu) ∧
      (∀ y, |y| * |bhtKernelR χ lam mu y| ≤ C) ∧
      (∀ y, y ^ 2 * |deriv (bhtKernelR χ lam mu) y| ≤ C) := by
  obtain ⟨B, hB0, hB⟩ := cutoff_exists_bound hχ
  obtain ⟨B', hB'0, hB'⟩ := cutoff_exists_deriv_bound hχ
  refine ⟨2 * B + 2 * B', by positivity, fun lam mu hlam hlm => ⟨contDiff_bhtKernelR hχ hlam hlm,
    fun y => ?_, fun y => ?_⟩⟩
  · linarith [abs_mul_bhtKernelR_le hB lam mu y]
  · by_cases hy : y = 0
    · subst hy; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]; positivity
    · rw [(hasDerivAt_bhtKernelR hχ.1 lam mu hy).deriv, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ y ^ 2),
        ← mul_div_assoc, mul_div_cancel_left₀ _ (by positivity : y ^ 2 ≠ 0)]
      have e : (deriv χ (lam * y) * lam - deriv χ (mu * y) * mu) * y - (χ (lam * y) - χ (mu * y)) * 1 =
          (deriv χ (lam * y) * lam * y - deriv χ (mu * y) * mu * y) - (χ (lam * y) - χ (mu * y)) := by
        ring
      rw [e]
      have h1 := abs_mul_deriv_le hχ hB'0 hB' lam y
      have h2 := abs_mul_deriv_le hχ hB'0 hB' mu y
      have h3 : |χ (lam * y) - χ (mu * y)| ≤ 2 * B := by
        have := abs_sub (χ (lam * y)) (χ (mu * y))
        linarith [hB (lam * y), hB (mu * y)]
      have h4 := abs_sub (deriv χ (lam * y) * lam * y - deriv χ (mu * y) * mu * y)
        (χ (lam * y) - χ (mu * y))
      have h5 := abs_sub (deriv χ (lam * y) * lam * y) (deriv χ (mu * y) * mu * y)
      linarith

end PrimeBHT.TimeFrequency.Transfer

end
