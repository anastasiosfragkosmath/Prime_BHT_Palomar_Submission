module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The `r_*`-triangle inequality and Fatou for series (blueprint node R3, step 6)

For `0 < r` and `r_* = min r 1`: `‖F + G‖_r^{r_*} ≤ ‖F‖_r^{r_*} + ‖G‖_r^{r_*}`, hence for finite sums,
and (by lower semicontinuity of the `L^r` norm along a.e. convergence, `eLpNorm_le_of_ae_tendsto`) for the
series `S = ∑_{k ∈ ℤ} F_k` whose symmetric partial sums converge pointwise to `S`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PrimeBHT.TimeFrequency.RealLine

variable {α E : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]

/-- `‖F‖_r^r = ∫⁻ ‖F‖ₑ^r` for real `r > 0`. -/
theorem eLpNorm_rpow_eq_lintegral {F : α → E} {r : ℝ} (hr : 0 < r) (hF : AEStronglyMeasurable F μ) :
    eLpNorm F (ENNReal.ofReal r) μ ^ r = ∫⁻ x, ‖F x‖ₑ ^ r ∂μ := by
  have h0 : ENNReal.ofReal r ≠ 0 := by simpa using hr
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h0 ENNReal.ofReal_ne_top hF, ENNReal.toReal_ofReal hr.le,
    ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hr.ne', ENNReal.rpow_one]

/-- The `r_*`-triangle inequality, `r_* = min r 1`. -/
theorem eLpNorm_add_rpow_le {F G : α → E} {r : ℝ} (hr : 0 < r) (hF : AEStronglyMeasurable F μ)
    (hG : AEStronglyMeasurable G μ) :
    eLpNorm (F + G) (ENNReal.ofReal r) μ ^ min r 1 ≤
      eLpNorm F (ENNReal.ofReal r) μ ^ min r 1 + eLpNorm G (ENNReal.ofReal r) μ ^ min r 1 := by
  rcases le_total 1 r with h1 | h1
  · rw [min_eq_right h1, ENNReal.rpow_one, ENNReal.rpow_one, ENNReal.rpow_one]
    exact eLpNorm_add_le (by simpa using h1)
  · rw [min_eq_left h1, eLpNorm_rpow_eq_lintegral hr (hF.add hG), eLpNorm_rpow_eq_lintegral hr hF,
      eLpNorm_rpow_eq_lintegral hr hG, ← lintegral_add_left' (hF.enorm.pow_const r)]
    refine lintegral_mono fun x => ?_
    refine le_trans ?_ (ENNReal.rpow_add_le_add_rpow _ _ hr.le h1)
    exact ENNReal.rpow_le_rpow (enorm_add_le _ _) hr.le

/-- The `r_*`-triangle inequality for finite sums. -/
theorem eLpNorm_sum_rpow_le {ι : Type*} (s : Finset ι) {F : ι → α → E} {r : ℝ} (hr : 0 < r)
    (hF : ∀ i ∈ s, AEStronglyMeasurable (F i) μ) :
    eLpNorm (∑ i ∈ s, F i) (ENNReal.ofReal r) μ ^ min r 1 ≤
      ∑ i ∈ s, eLpNorm (F i) (ENNReal.ofReal r) μ ^ min r 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, eLpNorm_zero]
    rw [ENNReal.zero_rpow_of_pos (lt_min hr one_pos)]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine (eLpNorm_add_rpow_le hr (hF a (Finset.mem_insert_self a s))
      (Finset.aestronglyMeasurable_sum _ fun i hi => hF i (Finset.mem_insert_of_mem hi))).trans ?_
    gcongr
    exact ih fun i hi => hF i (Finset.mem_insert_of_mem hi)

/-- **Fatou for series.** If `S` is the pointwise limit of the symmetric partial sums of `∑_k F_k` and the
`r_*`-th powers of the `L^r` norms of the partial sums are bounded by `B`, then `‖S‖_r^{r_*} ≤ B`. -/
theorem eLpNorm_rpow_le_of_tendsto_sum {F : ℤ → ℝ → E} {S : ℝ → E} {r : ℝ} (hr : 0 < r)
    (hF : ∀ k, AEStronglyMeasurable (F k) volume)
    (hS : ∀ x, Tendsto (fun K : ℕ => ∑ k ∈ Finset.Icc (-(K : ℤ)) K, F k x) atTop (𝓝 (S x)))
    {B : ℝ≥0∞}
    (hB : ∀ K : ℕ, ∑ k ∈ Finset.Icc (-(K : ℤ)) K, eLpNorm (F k) (ENNReal.ofReal r) volume ^ min r 1 ≤ B) :
    eLpNorm S (ENNReal.ofReal r) volume ^ min r 1 ≤ B := by
  have hs : 0 < min r 1 := lt_min hr one_pos
  have hmeas : ∀ K : ℕ, AEStronglyMeasurable (fun x => ∑ k ∈ Finset.Icc (-(K : ℤ)) K, F k x) volume :=
    fun K => by
      have := Finset.aestronglyMeasurable_sum (Finset.Icc (-(K : ℤ)) K) (fun k _ => hF k)
      convert this using 1
      ext x
      simp
  have hSm : AEStronglyMeasurable S volume :=
    aestronglyMeasurable_of_tendsto_ae atTop hmeas (Eventually.of_forall hS)
  have hle : eLpNorm S (ENNReal.ofReal r) volume ≤ B ^ (1 / min r 1) := by
    refine Lp.eLpNorm_le_of_ae_tendsto (ι := ℕ) (u := atTop) (f := fun (K : ℕ) x => ∑ k ∈ Finset.Icc (-(K : ℤ)) K, F k x)
      (Eventually.of_forall fun K => ?_) hmeas hSm (Eventually.of_forall hS)
    have h1 := eLpNorm_sum_rpow_le (Finset.Icc (-(K : ℤ)) K) hr (fun k _ => hF k) (μ := volume)
    have h2 := h1.trans (hB K)
    have h3 : (eLpNorm (fun x => ∑ k ∈ Finset.Icc (-(K : ℤ)) K, F k x) (ENNReal.ofReal r) volume) ^ min r 1
        ≤ B := by
      convert h2 using 3
      ext x
      simp
    rw [← ENNReal.rpow_le_rpow_iff hs, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hs.ne',
      ENNReal.rpow_one]
    exact h3
  rw [← ENNReal.rpow_le_rpow_iff (z := min r 1) hs] at hle
  rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hs.ne', ENNReal.rpow_one] at hle

end PrimeBHT.TimeFrequency.RealLine

end
