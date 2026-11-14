module

public import PrimeBHT.TimeFrequency.X1.RealLine.Dilation
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Kernel decomposition (blueprint node R2, `docs/x1-blueprint.md` section 4)

For a cutoff `χ` (`PrimeBHT.Statements.IsCutoff`, frozen) and `c ∈ [1, 2]` put
`ψ^{[c]}(y) := (χ(y) - χ(c y)) / y` (`psiC χ c`).

* (a) `ψ^{[c]}` is `C^∞`, odd, vanishes for `|y| ≤ 1/(2c)` and for `|y| ≥ 1`, has integral `0`, and
  `‖iteratedDeriv n ψ^{[c]} y‖ ≤ A_n` uniformly in `c ∈ [1, 2]` and `y` (`A_n` depends on `χ`, `n` only).
* (b) Telescoping: for `0 < λ < μ`, `J := ⌈log₂(μ/λ)⌉₊`, `c_j := 2` for `j + 1 < J`,
  `c_{J-1} := μ / (λ 2^{J-1})`: `K_{λ,μ}(y) = ∑_{j<J} (λ 2^j) ψ^{[c_j]}(λ 2^j y)` for EVERY real `y`
  (also `y = 0`, where both sides are `0`).
* (c) For continuous (e.g. Schwartz) `f, g`: `T_{K_{λ,μ}}(f, g) = ∑_{j<J} B_{(λ 2^j)⁻¹}(ψ^{[c_j]}, f, g)`, and
  `TheoremB χ p q r C ⟹` the bound of M2 with the same `C` (`theoremB_implies_M2`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal ContDiff
open PrimeBHT.Statements

namespace PrimeBHT.TimeFrequency.RealLine

/-! ## Cutoff API (over the FROZEN predicate `IsCutoff`) -/

theorem cutoff_eq_one_of_abs_le {χ : ℝ → ℝ} (hχ : IsCutoff χ) {t : ℝ} (ht : |t| ≤ 1 / 2) :
    χ t = 1 :=
  hχ.2.2.2 t (by rw [Set.mem_Icc]; constructor <;> linarith [abs_le.1 ht])

theorem cutoff_eq_zero_of_one_le_abs {χ : ℝ → ℝ} (hχ : IsCutoff χ) {t : ℝ} (ht : 1 ≤ |t|) :
    χ t = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  rcases hχ.2.2.1 h with ⟨h1, h2⟩
  rcases le_abs'.1 ht with h | h <;> linarith

theorem cutoff_hasCompactSupport {χ : ℝ → ℝ} (hχ : IsCutoff χ) : HasCompactSupport χ := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro t ht
  apply cutoff_eq_zero_of_one_le_abs hχ
  by_contra h
  rw [not_le, abs_lt] at h
  exact ht ⟨h.1.le, h.2.le⟩

/-! ## The profiles `ψ^{[c]}` -/

/-- `ψ^{[c]}(y) = (χ(y) - χ(c y)) / y` (blueprint R2; `ψ^{[c]}(0) = 0` by Lean's `x / 0 = 0`, which
is also the value of the numerator quotient limit: the numerator vanishes near `0`). -/
def psiC (χ : ℝ → ℝ) (c : ℝ) (y : ℝ) : ℝ := (χ y - χ (c * y)) / y

/-- `ψ^{[c]}` vanishes for `|y| ≤ 1/(2c)` (`1 ≤ c`): at the boundary `|y| = 1/(2c)` both `χ(y)` and
`χ(c y)` are `1`. -/
theorem psiC_eq_zero_of_abs_le {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : 1 ≤ c) {y : ℝ}
    (hy : |y| ≤ 1 / (2 * c)) : psiC χ c y = 0 := by
  have hc0 : 0 < c := by linarith
  have h1 : |y| * (2 * c) ≤ 1 := (le_div_iff₀ (by positivity)).1 hy
  have h2 : |c * y| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hc0]; linarith
  have h3 : |y| ≤ 1 / 2 := by
    have : 0 ≤ |y| := abs_nonneg y
    nlinarith
  simp only [psiC, cutoff_eq_one_of_abs_le hχ h2, cutoff_eq_one_of_abs_le hχ h3, sub_self, zero_div]

/-- `ψ^{[c]}` vanishes for `|y| ≥ 1` (`1 ≤ c`). -/
theorem psiC_eq_zero_of_one_le_abs {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : 1 ≤ c) {y : ℝ}
    (hy : 1 ≤ |y|) : psiC χ c y = 0 := by
  have h2 : 1 ≤ |c * y| := by
    rw [abs_mul, abs_of_pos (by linarith : 0 < c)]
    nlinarith
  simp only [psiC, cutoff_eq_zero_of_one_le_abs hχ hy, cutoff_eq_zero_of_one_le_abs hχ h2, sub_self,
    zero_div]

/-- `ψ^{[c]}` is odd (`χ` is even). -/
theorem psiC_neg {χ : ℝ → ℝ} (hχ : IsCutoff χ) (c y : ℝ) : psiC χ c (-y) = -psiC χ c y := by
  simp only [psiC, mul_neg, hχ.2.1, div_neg]

/-- `ψ^{[c]}` has integral zero (odd; no integrability hypothesis needed). -/
theorem integral_psiC {χ : ℝ → ℝ} (hχ : IsCutoff χ) (c : ℝ) : ∫ y, psiC χ c y = 0 := by
  have h := integral_neg_eq_self (psiC χ c) (volume : Measure ℝ)
  simp only [psiC_neg hχ, integral_neg] at h
  linarith

/-- `ψ^{[c]}` is supported in `[-1, 1]`, hence has compact support (`1 ≤ c`). -/
theorem hasCompactSupport_psiC {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : 1 ≤ c) :
    HasCompactSupport (psiC χ c) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro y hy
  apply psiC_eq_zero_of_one_le_abs hχ hc
  by_contra h
  rw [not_le, abs_lt] at h
  exact hy ⟨h.1.le, h.2.le⟩

/-! ## Smoothness and uniform derivative bounds -/

/-- The smooth regularisation `y ↦ (1 - χ(4 y)) / y` of `1 / y`: it vanishes for `|y| ≤ 1/8` and equals
`1 / y` for `|y| ≥ 1/4`. -/
def invCutoff (χ : ℝ → ℝ) (y : ℝ) : ℝ := (1 - χ (4 * y)) / y

theorem invCutoff_eq_zero_of_abs_le {χ : ℝ → ℝ} (hχ : IsCutoff χ) {y : ℝ} (hy : |y| ≤ 1 / 8) :
    invCutoff χ y = 0 := by
  have h : |4 * y| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]; linarith
  simp only [invCutoff, cutoff_eq_one_of_abs_le hχ h, sub_self, zero_div]

theorem invCutoff_eq_inv_of_one_le_abs {χ : ℝ → ℝ} (hχ : IsCutoff χ) {y : ℝ} (hy : 1 / 4 ≤ |y|) :
    invCutoff χ y = 1 / y := by
  have h : 1 ≤ |4 * y| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]; linarith
  simp only [invCutoff, cutoff_eq_zero_of_one_le_abs hχ h, sub_zero]

theorem contDiff_invCutoff {χ : ℝ → ℝ} (hχ : IsCutoff χ) : ContDiff ℝ ∞ (invCutoff χ) := by
  have hχd : ContDiff ℝ ∞ χ := hχ.1
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  by_cases hy : y = 0
  · subst hy
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 (0 : ℝ)] invCutoff χ := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 8)] with z hz
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hz
      exact (invCutoff_eq_zero_of_abs_le hχ hz.le).symm
    exact contDiffAt_const.congr_of_eventuallyEq hev.symm
  · have h1 : ContDiffAt ℝ ∞ (fun z : ℝ => 1 - χ (4 * z)) y :=
      (contDiffAt_const.sub ((hχd.comp (contDiff_const.mul contDiff_id)).contDiffAt))
    exact h1.div contDiffAt_id hy

/-- For `c ∈ [1, 2]`: `ψ^{[c]} = (χ - χ(c ·)) · invCutoff χ` everywhere. -/
theorem psiC_eq_mul {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2) (y : ℝ) :
    psiC χ c y = (χ y - χ (c * y)) * invCutoff χ y := by
  obtain ⟨hc1, hc2⟩ := hc
  by_cases hy : 1 / 4 ≤ |y|
  · rw [invCutoff_eq_inv_of_one_le_abs hχ hy, psiC, mul_one_div]
  · rw [not_le] at hy
    have h1 : psiC χ c y = 0 := by
      apply psiC_eq_zero_of_abs_le hχ hc1
      refine hy.le.trans ?_
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      linarith
    have h2 : |c * y| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos (by linarith : 0 < c)]
      nlinarith [abs_nonneg y]
    have h3 : |y| ≤ 1 / 2 := by linarith
    rw [h1, cutoff_eq_one_of_abs_le hχ h2, cutoff_eq_one_of_abs_le hχ h3]
    simp

/-- **R2 (a), smoothness.** `ψ^{[c]}` is `C^∞` for `c ∈ [1, 2]`. -/
theorem contDiff_psiC {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2) :
    ContDiff ℝ ∞ (psiC χ c) := by
  have hχd : ContDiff ℝ ∞ χ := hχ.1
  have : psiC χ c = fun y => (χ y - χ (c * y)) * invCutoff χ y := funext (psiC_eq_mul hχ hc)
  rw [this]
  exact (hχd.sub (hχd.comp (contDiff_const.mul contDiff_id))).mul (contDiff_invCutoff hχ)

theorem continuous_psiC {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2) :
    Continuous (psiC χ c) :=
  (contDiff_psiC hχ hc).continuous

/-- Derivatives of `χ`: each `iteratedDeriv i χ` is bounded (`χ` is smooth with compact support). -/
theorem exists_bound_iteratedDeriv_cutoff {χ : ℝ → ℝ} (hχ : IsCutoff χ) (i : ℕ) :
    ∃ B : ℝ, ∀ y, |iteratedDeriv i χ y| ≤ B := by
  obtain ⟨C, -, hC⟩ := (cutoff_hasCompactSupport hχ).exists_bound_iteratedFDeriv
    (hχ.1 : ContDiff ℝ ∞ χ) i
  refine ⟨C, fun y => ?_⟩
  have := hC i le_rfl y
  rwa [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at this

/-- Derivatives of `invCutoff χ` are bounded on `[-1, 1]` (continuity on a compact set). -/
theorem exists_bound_iteratedDeriv_invCutoff {χ : ℝ → ℝ} (hχ : IsCutoff χ) (m : ℕ) :
    ∃ I : ℝ, ∀ y ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv m (invCutoff χ) y| ≤ I := by
  obtain ⟨I, hI⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    ((contDiff_invCutoff hχ).continuous_iteratedDeriv m (by exact_mod_cast le_top)).continuousOn
  exact ⟨I, fun y hy => by simpa only [Real.norm_eq_abs] using hI y hy⟩

/-- `iteratedDeriv i (χ - χ(c ·))` for `1 ≤ c ≤ 2`, bounded by `(1 + 2^i) B`. -/
theorem abs_iteratedDeriv_sub_comp_le {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ}
    (hc : c ∈ Set.Icc (1 : ℝ) 2) (i : ℕ) {B : ℝ} (hB : ∀ y, |iteratedDeriv i χ y| ≤ B) (y : ℝ) :
    |iteratedDeriv i (fun z => χ z - χ (c * z)) y| ≤ (1 + 2 ^ i) * B := by
  have hχd : ContDiff ℝ ∞ χ := hχ.1
  have hcomp : ContDiff ℝ ∞ (fun z => χ (c * z)) := hχd.comp (contDiff_const.mul contDiff_id)
  have h1 : iteratedDeriv i (fun z => χ z - χ (c * z)) y =
      iteratedDeriv i χ y - c ^ i * iteratedDeriv i χ (c * y) := by
    rw [iteratedDeriv_fun_sub (hχd.contDiffAt.of_le (by exact_mod_cast le_top))
      (hcomp.contDiffAt.of_le (by exact_mod_cast le_top)), iteratedDeriv_comp_const_mul (hχd.of_le (by exact_mod_cast le_top)) c]
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hci : c ^ i ≤ 2 ^ i := pow_le_pow_left₀ (by linarith [hc.1]) hc.2 i
  rw [h1]
  calc |iteratedDeriv i χ y - c ^ i * iteratedDeriv i χ (c * y)|
      ≤ |iteratedDeriv i χ y| + |c ^ i * iteratedDeriv i χ (c * y)| := abs_sub _ _
    _ ≤ B + 2 ^ i * B := by
        refine add_le_add (hB y) ?_
        rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith [hc.1]) i)]
        exact mul_le_mul hci (hB _) (abs_nonneg _) (by positivity)
    _ = (1 + 2 ^ i) * B := by ring

/-- For `|y| > 1` the derivatives of `χ - χ(c ·)` vanish. -/
theorem iteratedDeriv_sub_comp_eq_zero {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : 1 ≤ c) (i : ℕ)
    {y : ℝ} (hy : 1 < |y|) : iteratedDeriv i (fun z => χ z - χ (c * z)) y = 0 := by
  have hev : (fun z => χ z - χ (c * z)) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    have hopen : IsOpen {z : ℝ | 1 < |z|} := isOpen_lt continuous_const continuous_abs
    filter_upwards [hopen.mem_nhds hy] with z hz
    have hz' : 1 ≤ |z| := hz.le
    have h2 : 1 ≤ |c * z| := by
      rw [abs_mul, abs_of_pos (by linarith : 0 < c)]; nlinarith
    simp only [cutoff_eq_zero_of_one_le_abs hχ hz', cutoff_eq_zero_of_one_le_abs hχ h2, sub_self]
  rw [hev.iteratedDeriv_eq i]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · simp

/-- **R2 (a), uniform bounds.** For every `n` there is `A_n` (depending on `χ` and `n` only) such that
`‖iteratedDeriv n ψ^{[c]} y‖ ≤ A_n` for all `c ∈ [1, 2]` and all `y`. -/
theorem exists_bound_iteratedDeriv_psiC {χ : ℝ → ℝ} (hχ : IsCutoff χ) (n : ℕ) :
    ∃ A : ℝ, ∀ c ∈ Set.Icc (1 : ℝ) 2, ∀ y : ℝ, ‖iteratedDeriv n (psiC χ c) y‖ ≤ A := by
  have hχd : ContDiff ℝ ∞ χ := hχ.1
  choose B hB using exists_bound_iteratedDeriv_cutoff hχ
  choose I hI using exists_bound_iteratedDeriv_invCutoff hχ
  refine ⟨∑ i ∈ range (n + 1), (n.choose i : ℝ) * ((1 + 2 ^ i) * B i) * I (n - i), ?_⟩
  have hB0 : ∀ i, 0 ≤ B i := fun i => (abs_nonneg _).trans (hB i 0)
  have hI0 : ∀ m, 0 ≤ I m := fun m =>
    (abs_nonneg _).trans (hI m 0 (by simp))
  have hA0 : 0 ≤ ∑ i ∈ range (n + 1), (n.choose i : ℝ) * ((1 + 2 ^ i) * B i) * I (n - i) :=
    Finset.sum_nonneg fun i _ => by have := hB0 i; have := hI0 (n - i); positivity
  intro c hc y
  rw [Real.norm_eq_abs]
  have hfun : psiC χ c = fun z => (χ z - χ (c * z)) * invCutoff χ z := funext (psiC_eq_mul hχ hc)
  have hu : ContDiff ℝ ∞ (fun z => χ z - χ (c * z)) :=
    hχd.sub (hχd.comp (contDiff_const.mul contDiff_id))
  rw [hfun, iteratedDeriv_fun_mul (hu.contDiffAt.of_le (by exact_mod_cast le_top))
    ((contDiff_invCutoff hχ).contDiffAt.of_le (by exact_mod_cast le_top))]
  by_cases hy : |y| ≤ 1
  · have hyI : y ∈ Set.Icc (-1 : ℝ) 1 := abs_le.1 hy
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_mul, Nat.abs_cast]
    have h1 := abs_iteratedDeriv_sub_comp_le hχ hc i (hB i) y
    have h2 := hI (n - i) y hyI
    have h3 : 0 ≤ (1 + 2 ^ i) * B i := by have := hB0 i; positivity
    have h4 : (n.choose i : ℝ) * |iteratedDeriv i (fun z => χ z - χ (c * z)) y| ≤
        (n.choose i : ℝ) * ((1 + 2 ^ i) * B i) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
    exact mul_le_mul h4 h2 (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) h3)
  · rw [not_le] at hy
    have : ∀ i ∈ range (n + 1), (n.choose i : ℝ) * iteratedDeriv i (fun z => χ z - χ (c * z)) y *
        iteratedDeriv (n - i) (invCutoff χ) y = 0 := by
      intro i _
      rw [iteratedDeriv_sub_comp_eq_zero hχ hc.1 i hy]
      simp
    rw [Finset.sum_eq_zero this, abs_zero]
    exact hA0

/-! ## R2 (b): the telescoping identity -/

/-- The number of dyadic scales `J = ⌈log₂(μ/λ)⌉₊` of the decomposition of `K_{λ,μ}` (blueprint R2(b)). -/
def numScales (lam mu : ℝ) : ℕ := ⌈Real.logb 2 (mu / lam)⌉₊

/-- The ratios `c_j`: `c_j = 2` for `j + 1 < J` and `c_{J-1} = μ / (λ 2^{J-1})` (blueprint R2(b)). For `j ≥ J`
the value is irrelevant (it is `μ / (λ 2^j)`). -/
def scaleRatio (lam mu : ℝ) (j : ℕ) : ℝ :=
  if j + 1 < numScales lam mu then 2 else mu / (lam * 2 ^ j)

theorem one_le_numScales {lam mu : ℝ} (hlam : 0 < lam) (hlm : lam < mu) : 1 ≤ numScales lam mu := by
  have h : 1 < mu / lam := (one_lt_div hlam).2 hlm
  exact Nat.ceil_pos.2 (Real.logb_pos (by norm_num) h)

theorem div_le_two_pow_numScales {lam mu : ℝ} (hlam : 0 < lam) (hlm : lam < mu) :
    mu / lam ≤ 2 ^ numScales lam mu := by
  have hpos : 0 < mu / lam := div_pos (hlam.trans hlm) hlam
  have h := Nat.le_ceil (Real.logb 2 (mu / lam))
  rw [Real.logb_le_iff_le_rpow (by norm_num) hpos, Real.rpow_natCast] at h
  exact h

theorem two_pow_lt_div_of_lt_numScales {lam mu : ℝ} (hlam : 0 < lam) (hlm : lam < mu) {j : ℕ}
    (hj : j < numScales lam mu) : (2 : ℝ) ^ j < mu / lam := by
  have hpos : 0 < mu / lam := div_pos (hlam.trans hlm) hlam
  have h := Nat.lt_ceil.1 hj
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) hpos, Real.rpow_natCast] at h
  exact h

/-- The ratios `c_j` lie in `[1, 2]` for `j < J`. -/
theorem scaleRatio_mem_Icc {lam mu : ℝ} (hlam : 0 < lam) (hlm : lam < mu) {j : ℕ}
    (hj : j < numScales lam mu) : scaleRatio lam mu j ∈ Set.Icc (1 : ℝ) 2 := by
  unfold scaleRatio
  split_ifs with h
  · exact ⟨by norm_num, le_rfl⟩
  · have hj1 : j + 1 = numScales lam mu := by omega
    have h1 := two_pow_lt_div_of_lt_numScales hlam hlm hj
    have h2 := div_le_two_pow_numScales hlam hlm
    rw [← hj1, pow_succ] at h2
    have hk : 0 < lam * 2 ^ j := by positivity
    rw [lt_div_iff₀ hlam] at h1
    rw [div_le_iff₀ hlam] at h2
    constructor
    · rw [le_div_iff₀ hk]; linarith
    · rw [div_le_iff₀ hk]; linarith

/-- One term of the decomposition: `k ψ^{[c]}(k y) = (χ(k y) - χ(c k y)) / y` for `k ≠ 0`. -/
theorem mul_psiC_mul (χ : ℝ → ℝ) (c : ℝ) {k : ℝ} (hk : k ≠ 0) (y : ℝ) :
    k * psiC χ c (k * y) = (χ (k * y) - χ (c * k * y)) / y := by
  by_cases hy : y = 0
  · simp [psiC, hy]
  · have : c * (k * y) = c * k * y := by ring
    simp only [psiC, this]
    field_simp

/-- **R2 (b), telescoping.** For `0 < λ < μ`, `J = ⌈log₂(μ/λ)⌉₊`, `c_j` as above and EVERY real `y`
(not only `y ≠ 0`; at `y = 0` both sides are `0`):
`K_{λ,μ}(y) = ∑_{j<J} (λ 2^j) ψ^{[c_j]}(λ 2^j y)`. No hypothesis on `χ` is needed. -/
theorem bhtKernelR_eq_sum_psiC (χ : ℝ → ℝ) {lam mu : ℝ} (hlam : 0 < lam) (hlm : lam < mu) (y : ℝ) :
    bhtKernelR χ lam mu y =
      ∑ j ∈ range (numScales lam mu),
        (lam * 2 ^ j) * psiC χ (scaleRatio lam mu j) (lam * 2 ^ j * y) := by
  obtain ⟨J, hJ⟩ : ∃ J, numScales lam mu = J + 1 :=
    ⟨numScales lam mu - 1, by have := one_le_numScales hlam hlm; omega⟩
  have hk : ∀ j : ℕ, lam * 2 ^ j ≠ 0 := fun j => by positivity
  have hc : ∀ j ∈ range J, scaleRatio lam mu j = 2 := fun j hj => by
    have : j + 1 < J + 1 := Nat.add_lt_add_right (Finset.mem_range.1 hj) 1
    simp only [scaleRatio, hJ, this, ite_true]
  have hlast : scaleRatio lam mu J = mu / (lam * 2 ^ J) := by
    simp only [scaleRatio, hJ, lt_irrefl, ite_false]
  rw [hJ, Finset.sum_range_succ,
    Finset.sum_congr rfl (fun j hj => by rw [hc j hj, mul_psiC_mul χ 2 (hk j) y]),
    hlast, mul_psiC_mul χ _ (hk J) y]
  have h1 : ∀ j : ℕ, 2 * (lam * 2 ^ j) * y = lam * 2 ^ (j + 1) * y := fun j => by ring
  have h2 : mu / (lam * 2 ^ J) * (lam * 2 ^ J) = mu := div_mul_cancel₀ _ (hk J)
  simp only [h1, h2, ← Finset.sum_div]
  rw [Finset.sum_range_sub' (fun j => χ (lam * 2 ^ j * y)), ← add_div]
  simp only [bhtKernelR, pow_zero, mul_one]
  congr 1
  ring

/-! ## R2 (c): the operator-level decomposition -/

/-- The integrand of `dilAvg φ t f g x` is integrable for continuous `f, g` and a continuous
compactly supported profile `φ` (`t ≠ 0`). -/
theorem integrable_dilAvg_integrand {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {t : ℝ} (ht : t ≠ 0) {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (x : ℝ) :
    Integrable (fun y => f (x - y) * g (x + y) * ((t⁻¹ * φ (y / t) : ℝ) : ℂ)) := by
  have hcont : Continuous fun y : ℝ => f (x - y) * g (x + y) * ((t⁻¹ * φ (y / t) : ℝ) : ℂ) :=
    ((hf.comp (continuous_const.sub continuous_id)).mul
      (hg.comp (continuous_const.add continuous_id))).mul
      (Complex.continuous_ofReal.comp (continuous_const.mul (hφ.comp (continuous_id.div_const t))))
  refine hcont.integrable_of_hasCompactSupport ?_
  have h1 : HasCompactSupport fun y : ℝ => φ (t⁻¹ * y) :=
    hφc.comp_homeomorph (Homeomorph.mulLeft₀ t⁻¹ (inv_ne_zero ht))
  have h2 : HasCompactSupport (fun y : ℝ => t⁻¹ * φ (t⁻¹ * y)) :=
    HasCompactSupport.mul_left (f := fun _ : ℝ => t⁻¹) h1
  have h3 : HasCompactSupport fun y : ℝ => ((t⁻¹ * φ (t⁻¹ * y) : ℝ) : ℂ) :=
    h2.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have e : (fun y : ℝ => ((t⁻¹ * φ (t⁻¹ * y) : ℝ) : ℂ)) =
      fun y : ℝ => ((t⁻¹ * φ (y / t) : ℝ) : ℂ) := by
    funext y; rw [div_eq_inv_mul]
  rw [e] at h3
  exact HasCompactSupport.mul_left (f := fun y : ℝ => f (x - y) * g (x + y)) h3

/-- **R2 (c).** For continuous (in particular Schwartz) `f, g`, `0 < λ < μ` and a cutoff `χ`:
`T_{K_{λ,μ}}(f, g) = ∑_{j<J} B_{(λ 2^j)⁻¹}(ψ^{[c_j]}, f, g)`. -/
theorem bhtOpR_eq_sum_dilAvg {χ : ℝ → ℝ} (hχ : IsCutoff χ) {lam mu : ℝ} (hlam : 0 < lam)
    (hlm : lam < mu) {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    bhtOpR χ lam mu f g =
      ∑ j ∈ range (numScales lam mu), dilAvg (psiC χ (scaleRatio lam mu j)) (lam * 2 ^ j)⁻¹ f g := by
  funext x
  rw [Finset.sum_apply]
  have hint : ∀ j ∈ range (numScales lam mu), Integrable (fun y : ℝ => f (x - y) * g (x + y) *
      ((((lam * 2 ^ j)⁻¹)⁻¹ * psiC χ (scaleRatio lam mu j) (y / (lam * 2 ^ j)⁻¹) : ℝ) : ℂ)) :=
    fun j hj => by
      have hc := scaleRatio_mem_Icc hlam hlm (Finset.mem_range.1 hj)
      exact integrable_dilAvg_integrand (continuous_psiC hχ hc) (hasCompactSupport_psiC hχ hc.1)
        (inv_ne_zero (by positivity)) hf hg x
  unfold bhtOpR dilAvg
  rw [← integral_finsetSum _ hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [bhtKernelR_eq_sum_psiC χ hlam hlm y, Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inv_inv, div_inv_eq_mul, mul_comm y]

/-- **R2 (c), Schwartz form.** -/
theorem bhtOpR_eq_sum_dilAvg_schwartz {χ : ℝ → ℝ} (hχ : IsCutoff χ) {lam mu : ℝ} (hlam : 0 < lam)
    (hlm : lam < mu) (f g : SchwartzMap ℝ ℂ) :
    bhtOpR χ lam mu f g =
      ∑ j ∈ range (numScales lam mu), dilAvg (psiC χ (scaleRatio lam mu j)) (lam * 2 ^ j)⁻¹ f g :=
  bhtOpR_eq_sum_dilAvg hχ hlam hlm f.continuous g.continuous

/-! ## Theorem B and its implication M2 -/

/-- **Theorem B** (blueprint R2(c)): for every `J` and every sequence of profiles `g j = ψ^{[c_j]}` with
`c_j ∈ [1, 2]` (`j < J`) and all Schwartz `f₁, f₂`,
`‖∑_{j<J} B_{2^{-j}}(g_j, f₁, f₂)‖_{L^r} ≤ C ‖f₁‖_{L^p} ‖f₂‖_{L^q}`. The exponents `p, q, r` and the constant
`C` are parameters (the constant is independent of `J` and of the `c_j`); the relation `1/r = 1/p + 1/q` is a
hypothesis of the consumer `theoremB_implies_M2`. -/
def TheoremB (χ : ℝ → ℝ) (p q r C : ℝ) : Prop :=
  ∀ (J : ℕ) (g : ℕ → ℝ → ℝ), (∀ j < J, ∃ c ∈ Set.Icc (1 : ℝ) 2, g j = psiC χ c) →
    ∀ f₁ f₂ : SchwartzMap ℝ ℂ,
      eLpNorm (∑ j ∈ range J, dilAvg (g j) ((2 : ℝ) ^ j)⁻¹ f₁ f₂) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal C * eLpNorm f₁ (ENNReal.ofReal p) volume *
          eLpNorm f₂ (ENNReal.ofReal q) volume

/-- Theorem B gives the M2 bound at `(λ, μ) = (1, μ)` (`μ > 1`), with the same constant. -/
theorem bhtOpR_one_bound_of_theoremB {χ : ℝ → ℝ} (hχ : IsCutoff χ) {p q r C : ℝ}
    (hB : TheoremB χ p q r C) {mu : ℝ} (hmu : 1 < mu) (f g : SchwartzMap ℝ ℂ) :
    eLpNorm (bhtOpR χ 1 mu f g) (ENNReal.ofReal r) volume ≤
      ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume *
        eLpNorm g (ENNReal.ofReal q) volume := by
  have h := hB (numScales 1 mu) (fun j => psiC χ (scaleRatio 1 mu j))
    (fun j hj => ⟨_, scaleRatio_mem_Icc one_pos hmu hj, rfl⟩) f g
  rw [bhtOpR_eq_sum_dilAvg_schwartz hχ one_pos hmu f g]
  simpa only [one_mul] using h

/-- **R2 (c): Theorem B implies M2.** If `TheoremB χ p q r C` holds (`1/r = 1/p + 1/q`, `p, q > 0`), then for
all real `0 < λ < μ` and all Schwartz `f, g`,
`‖T_{K_{λ,μ}}(f, g)‖_{L^r} ≤ C ‖f‖_{L^p} ‖g‖_{L^q}` with the same `C` (by the telescoping decomposition at
`λ = 1` and the dilation invariance `bhtOpR_bound_dilate_iff` with `s = λ`). -/
theorem theoremB_implies_M2 {χ : ℝ → ℝ} (hχ : IsCutoff χ) {p q r C : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpqr : 1 / r = 1 / p + 1 / q) (hB : TheoremB χ p q r C) :
    ∀ lam mu : ℝ, 0 < lam → lam < mu → ∀ f g : SchwartzMap ℝ ℂ,
      eLpNorm (bhtOpR χ lam mu f g) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume *
          eLpNorm g (ENNReal.ofReal q) volume := by
  intro lam mu hlam hlm
  have hr : 0 < r := by
    have : 0 < 1 / r := by rw [hpqr]; positivity
    exact one_div_pos.1 this
  have h1 : ∀ f g : SchwartzMap ℝ ℂ,
      eLpNorm (bhtOpR χ 1 (mu / lam) f g) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume *
          eLpNorm g (ENNReal.ofReal q) volume :=
    fun f g => bhtOpR_one_bound_of_theoremB hχ hB ((one_lt_div hlam).2 hlm) f g
  have e : lam / lam = 1 := div_self hlam.ne'
  rw [← e] at h1
  exact (bhtOpR_bound_dilate_iff χ lam mu hlam hp hq hr hpqr).2 h1

/-- The shape of the candidate statement M2 (`drafts/M2Statement.lean.txt`, `bht_real_smooth`) follows
from Theorem B for all cutoffs and all exponents in the bilinear-Hilbert-transform range. -/
theorem m2_of_theoremB
    (hB : ∀ χ : ℝ → ℝ, IsCutoff χ → ∀ p q r : ℝ, 1 < p → 1 < q → 1 / r = 1 / p + 1 / q →
      2 / 3 < r → ∃ C : ℝ, TheoremB χ p q r C) :
    ∀ χ : ℝ → ℝ, IsCutoff χ → ∀ p q r : ℝ, 1 < p → 1 < q → 1 / r = 1 / p + 1 / q → 2 / 3 < r →
      ∃ C : ℝ, ∀ lam mu : ℝ, 0 < lam → lam < mu → ∀ f g : SchwartzMap ℝ ℂ,
        eLpNorm (bhtOpR χ lam mu f g) (ENNReal.ofReal r) volume ≤
          ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume *
            eLpNorm g (ENNReal.ofReal q) volume := by
  intro χ hχ p q r hp hq hpqr hr
  obtain ⟨C, hC⟩ := hB χ hχ p q r hp hq hpqr hr
  exact ⟨C, theoremB_implies_M2 hχ (by linarith) (by linarith) hpqr hC⟩

end PrimeBHT.TimeFrequency.RealLine

end
