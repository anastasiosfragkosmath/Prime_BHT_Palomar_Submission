module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Part Z1 of `docs/x1-blueprint.md`: the smooth lift `ℤ → ℝ` and the window identity

Fix the smooth step bump `b = stepBump` (`ContDiffBump (0:ℝ)` with radii `1/6`, `1/3`): `0 ≤ b ≤ 1`,
`b = 1` on `[-1/6, 1/6]`, `b = 0` for `|x| ≥ 1/3`. For `f g : ℤ → ℂ` put
`F = liftC (-1/2) f`, `F(x) = ∑_k f(k) b(x - k + 1/2)` and `G = liftC (1/2) g`,
`G(x) = ∑_l g(l) b(x - l - 1/2)` (`f` in the `x - y` slot, `g` in the `x + y` slot).

* (a) `exists_schwartz_liftC` (finitely supported `f`: `F` is a Schwartz function), `eLpNorm_liftC_le`
  (`‖F‖_{L^p(ℝ)} ≤ ‖f‖_{ℓ^p}`, all `p > 0`; the blueprint's `β_p ∈ [1/3, 2/3]` is not needed).
* (b) `integral_lift_eq` (`n ∈ ℤ`, `|u| ≤ 1/12`, `x = n + u`, `K` continuous):
  `∫ F(x - y) G(x + y) K(y) dy = ∑_m f(n - m) g(n + m) κ_m(u)`, `κ_m(u) = ∫ w_u(s) K(m + 1/2 + s) ds`,
  `w_u(s) = b(u - s) b(u + s)` (`winW`).
* (c) `winW_nonneg`, `winW_le_one`, `abs_lt_of_winW_ne_zero` (`w_u(s) ≠ 0 → |s| < 1/3 - |u|`),
  `winMass_le` (`W(u) ≤ 2/3`), `le_winMass` (`1/6 ≤ W(u)` for `|u| ≤ 1/12`).

Blueprint check: the supports are strict (`|s| < 1/3 - |u|`, since `b = 0` for `|x| ≥ 1/3`), the diagonal
is forced by `|2n - k - l| < 2/3 + 2|u| ≤ 5/6 < 1`; both as in the blueprint.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Transfer

/-! ## Two `eLpNorm` formulas -/

theorem eLpNorm_count_eq (f : ℤ → ℂ) {r : ℝ} (hr : 0 < r) :
    eLpNorm f (ENNReal.ofReal r) Measure.count = (∑' x, ‖f x‖ₑ ^ r) ^ (1 / r) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr) ENNReal.ofReal_ne_top
    (measurable_of_countable f).aestronglyMeasurable, lintegral_count,
    ENNReal.toReal_ofReal hr.le]

theorem eLpNorm_volume_eq {F : ℝ → ℂ} (hF : AEStronglyMeasurable F volume) {r : ℝ} (hr : 0 < r) :
    eLpNorm F (ENNReal.ofReal r) volume = (∫⁻ x, ‖F x‖ₑ ^ r) ^ (1 / r) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr) ENNReal.ofReal_ne_top hF,
    ENNReal.toReal_ofReal hr.le]

/-! ## The step bump -/

/-- The smooth step bump `b`: `0 ≤ b ≤ 1`, `b = 1` on `[-1/6, 1/6]`, `support b = (-1/3, 1/3)`. -/
def stepBump : ContDiffBump (0 : ℝ) := ⟨1 / 6, 1 / 3, by norm_num, by norm_num⟩

theorem stepBump_nonneg (x : ℝ) : 0 ≤ stepBump x := stepBump.nonneg

theorem stepBump_le_one (x : ℝ) : stepBump x ≤ 1 := stepBump.le_one

theorem stepBump_eq_one {x : ℝ} (hx : |x| ≤ 1 / 6) : stepBump x = 1 :=
  stepBump.one_of_mem_closedBall (by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hx)

theorem stepBump_eq_zero {x : ℝ} (hx : 1 / 3 ≤ |x|) : stepBump x = 0 :=
  stepBump.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hx)

theorem abs_lt_of_stepBump_ne_zero {x : ℝ} (h : stepBump x ≠ 0) : |x| < 1 / 3 := by
  by_contra hx
  exact h (stepBump_eq_zero (not_lt.1 hx))

theorem continuous_stepBump : Continuous (stepBump : ℝ → ℝ) := stepBump.continuous

theorem contDiff_stepBump : ContDiff ℝ ∞ (stepBump : ℝ → ℝ) := stepBump.contDiff

/-- A continuous function supported in a bounded interval is integrable. -/
theorem integrable_of_forall_abs_sub_le {E : Type*} [NormedAddCommGroup E] {h : ℝ → E}
    (hh : Continuous h) {a R : ℝ} (hs : ∀ y, h y ≠ 0 → |y - a| ≤ R) : Integrable h := by
  refine hh.integrable_of_hasCompactSupport ?_
  apply HasCompactSupport.intro (isCompact_Icc (a := a - R) (b := a + R))
  intro y hy
  by_contra hne
  have := abs_le.1 (hs y hne)
  exact hy ⟨by linarith [this.1], by linarith [this.2]⟩

/-! ## The lift -/

/-- `liftC c f (x) = ∑_k f(k) b(x - k - c)`. The windows `{|x - k - c| < 1/3}` are pairwise disjoint,
so at most one summand is nonzero. -/
def liftC (c : ℝ) (f : ℤ → ℂ) (x : ℝ) : ℂ := ∑' k : ℤ, f k * (stepBump (x - k - c) : ℂ)

theorem liftC_eq_sum (c : ℝ) {f : ℤ → ℂ} (S : Finset ℤ) (hS : ∀ k ∉ S, f k = 0) (x : ℝ) :
    liftC c f x = ∑ k ∈ S, f k * (stepBump (x - k - c) : ℂ) :=
  tsum_eq_sum fun k hk => by simp [hS k hk]

theorem liftC_eq_single (c : ℝ) (f : ℤ → ℂ) {x : ℝ} {k₀ : ℤ} (hk : |x - k₀ - c| < 1 / 3) :
    liftC c f x = f k₀ * (stepBump (x - k₀ - c) : ℂ) := by
  refine tsum_eq_single k₀ fun k hk' => ?_
  have : stepBump (x - k - c) = 0 := by
    apply stepBump_eq_zero
    by_contra h
    rw [not_le] at h
    have h2 : (1 : ℝ) ≤ |(k : ℝ) - k₀| := by
      have : (1 : ℤ) ≤ |k - k₀| := Int.one_le_abs (sub_ne_zero.2 hk')
      exact_mod_cast this
    have h3 : |(k : ℝ) - k₀| ≤ |x - k₀ - c| + |x - k - c| := by
      calc |(k : ℝ) - k₀| = |(x - k₀ - c) - (x - k - c)| := by ring_nf
        _ ≤ _ := abs_sub _ _
    linarith
  simp [this]

theorem liftC_eq_zero (c : ℝ) (f : ℤ → ℂ) {x : ℝ} (hx : ∀ k : ℤ, 1 / 3 ≤ |x - k - c|) :
    liftC c f x = 0 := by
  unfold liftC
  simp [stepBump_eq_zero (hx _)]

theorem contDiff_liftC (c : ℝ) {f : ℤ → ℂ} (hf : (Function.support f).Finite) :
    ContDiff ℝ ∞ (liftC c f) := by
  have : liftC c f = fun x => ∑ k ∈ hf.toFinset, f k * (stepBump (x - k - c) : ℂ) := by
    funext x
    exact liftC_eq_sum c hf.toFinset (fun k hk => by simpa using hk) x
  rw [this]
  refine ContDiff.sum fun k _ => contDiff_const.mul ?_
  exact Complex.ofRealCLM.contDiff.comp (contDiff_stepBump.comp (by fun_prop))

theorem continuous_liftC (c : ℝ) {f : ℤ → ℂ} (hf : (Function.support f).Finite) :
    Continuous (liftC c f) :=
  (contDiff_liftC c hf).continuous

theorem hasCompactSupport_liftC (c : ℝ) {f : ℤ → ℂ} (hf : (Function.support f).Finite) :
    HasCompactSupport (liftC c f) := by
  set S := hf.toFinset with hSdef
  have hS : ∀ k ∉ S, f k = 0 := fun k hk => by simpa [hSdef] using hk
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (∑ k ∈ S, (|(k : ℝ)| + |c| + 1)))
  intro x hx
  rw [mem_closedBall_zero_iff, not_le, Real.norm_eq_abs] at hx
  rw [liftC_eq_sum c S hS]
  refine Finset.sum_eq_zero fun k hk => ?_
  have h1 : |(k : ℝ)| + |c| + 1 ≤ ∑ k ∈ S, (|(k : ℝ)| + |c| + 1) :=
    Finset.single_le_sum (f := fun k : ℤ => |(k : ℝ)| + |c| + 1) (fun j _ => by positivity) hk
  have h2 : |x| - |(k : ℝ)| - |c| ≤ |x - k - c| := by
    have := abs_sub_abs_le_abs_sub x ((k : ℝ) + c)
    have h3 := abs_add_le (k : ℝ) c
    rw [show x - k - c = x - ((k : ℝ) + c) by ring]
    linarith
  rw [stepBump_eq_zero (by linarith), Complex.ofReal_zero, mul_zero]

/-- **Z1 (a).** For finitely supported `f` the lift is a Schwartz function. -/
theorem exists_schwartz_liftC (c : ℝ) {f : ℤ → ℂ} (hf : (Function.support f).Finite) :
    ∃ F : SchwartzMap ℝ ℂ, ∀ x, F x = liftC c f x :=
  ⟨(hasCompactSupport_liftC c hf).toSchwartzMap (contDiff_liftC c hf), fun _ => rfl⟩

/-- **Z1 (a), norm.** `‖liftC c f‖_{L^p(ℝ)} ≤ ‖f‖_{ℓ^p}` for `p > 0` (the windows are disjoint of
length `2/3` and `0 ≤ b ≤ 1`). -/
theorem eLpNorm_liftC_le (c : ℝ) {f : ℤ → ℂ} (hf : (Function.support f).Finite) {p : ℝ} (hp : 0 < p) :
    eLpNorm (liftC c f) (ENNReal.ofReal p) volume ≤ eLpNorm f (ENNReal.ofReal p) Measure.count := by
  rw [eLpNorm_volume_eq (continuous_liftC c hf).aestronglyMeasurable hp, eLpNorm_count_eq f hp]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  have hpt : ∀ x : ℝ, ‖liftC c f x‖ₑ ^ p ≤
      ∑' k : ℤ, Set.indicator (Metric.ball ((k : ℝ) + c) (1 / 3)) (fun _ => ‖f k‖ₑ ^ p) x := by
    intro x
    by_cases h : ∃ k₀ : ℤ, |x - k₀ - c| < 1 / 3
    · obtain ⟨k₀, hk₀⟩ := h
      rw [liftC_eq_single c f hk₀]
      refine le_trans ?_ (ENNReal.le_tsum k₀)
      have hx : x ∈ Metric.ball ((k₀ : ℝ) + c) (1 / 3) := by
        rw [Metric.mem_ball, Real.dist_eq, show x - ((k₀ : ℝ) + c) = x - k₀ - c by ring]; exact hk₀
      rw [Set.indicator_of_mem hx]
      refine ENNReal.rpow_le_rpow ?_ hp.le
      rw [enorm_mul]
      have : ‖((stepBump (x - k₀ - c) : ℝ) : ℂ)‖ₑ ≤ 1 := by
        rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (stepBump_nonneg _)]
        exact ENNReal.ofReal_le_one.2 (stepBump_le_one _)
      calc ‖f k₀‖ₑ * ‖((stepBump (x - k₀ - c) : ℝ) : ℂ)‖ₑ ≤ ‖f k₀‖ₑ * 1 := by gcongr
        _ = ‖f k₀‖ₑ := mul_one _
    · push Not at h
      rw [liftC_eq_zero c f (fun k => h k), enorm_zero, ENNReal.zero_rpow_of_pos hp]
      exact zero_le
  calc ∫⁻ x, ‖liftC c f x‖ₑ ^ p
      ≤ ∫⁻ x, ∑' k : ℤ, Set.indicator (Metric.ball ((k : ℝ) + c) (1 / 3)) (fun _ => ‖f k‖ₑ ^ p) x :=
        lintegral_mono hpt
    _ = ∑' k : ℤ, ∫⁻ x, Set.indicator (Metric.ball ((k : ℝ) + c) (1 / 3)) (fun _ => ‖f k‖ₑ ^ p) x := by
        refine lintegral_tsum fun k => ?_
        exact (measurable_const.indicator Metric.isOpen_ball.measurableSet).aemeasurable
    _ ≤ ∑' k : ℤ, ‖f k‖ₑ ^ p := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [lintegral_indicator_const Metric.isOpen_ball.measurableSet, Real.volume_ball]
        calc ‖f k‖ₑ ^ p * ENNReal.ofReal (2 * (1 / 3)) ≤ ‖f k‖ₑ ^ p * 1 := by
              gcongr
              exact ENNReal.ofReal_le_one.2 (by norm_num)
          _ = ‖f k‖ₑ ^ p := mul_one _

/-! ## The window weight -/

/-- `w_u(s) = b(u - s) b(u + s)`. -/
def winW (u s : ℝ) : ℝ := stepBump (u - s) * stepBump (u + s)

/-- `κ_m(u) = ∫ w_u(s) K(m + 1/2 + s) ds`. -/
def kappa (K : ℝ → ℝ) (m : ℤ) (u : ℝ) : ℝ := ∫ s, winW u s * K (m + 1 / 2 + s)

/-- `W(u) = ∫ w_u`. -/
def winMass (u : ℝ) : ℝ := ∫ s, winW u s

theorem winW_nonneg (u s : ℝ) : 0 ≤ winW u s := mul_nonneg (stepBump_nonneg _) (stepBump_nonneg _)

theorem winW_le_one (u s : ℝ) : winW u s ≤ 1 :=
  (mul_le_mul (stepBump_le_one _) (stepBump_le_one _) (stepBump_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

theorem continuous_winW (u : ℝ) : Continuous (winW u) := by
  unfold winW
  exact (continuous_stepBump.comp (continuous_const.sub continuous_id)).mul
    (continuous_stepBump.comp (continuous_const.add continuous_id))

/-- **Z1 (c).** `w_u(s) ≠ 0` forces `|s| < 1/3 - |u|`. -/
theorem abs_lt_of_winW_ne_zero {u s : ℝ} (h : winW u s ≠ 0) : |s| < 1 / 3 - |u| := by
  have h1 := abs_lt_of_stepBump_ne_zero (left_ne_zero_of_mul h)
  have h2 := abs_lt_of_stepBump_ne_zero (right_ne_zero_of_mul h)
  rw [abs_lt] at h1 h2
  rcases abs_cases s with ⟨hs, _⟩ | ⟨hs, _⟩ <;> rcases abs_cases u with ⟨hu, _⟩ | ⟨hu, _⟩ <;>
    rw [hs, hu] <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem winW_eq_one {u s : ℝ} (h : |s| ≤ 1 / 6 - |u|) : winW u s = 1 := by
  have h1 : |u - s| ≤ 1 / 6 := by
    calc |u - s| ≤ |u| + |s| := abs_sub _ _
      _ ≤ 1 / 6 := by linarith
  have h2 : |u + s| ≤ 1 / 6 := by
    calc |u + s| ≤ |u| + |s| := abs_add_le _ _
      _ ≤ 1 / 6 := by linarith
  simp [winW, stepBump_eq_one h1, stepBump_eq_one h2]

theorem integrable_winW_mul {K : ℝ → ℝ} (hK : Continuous K) (u c : ℝ) :
    Integrable (fun s => winW u s * K (c + s)) := by
  refine integrable_of_forall_abs_sub_le (a := 0) (R := 1 / 3)
    (((continuous_winW u).mul (hK.comp (continuous_const.add continuous_id)))) fun s hs => ?_
  have := abs_lt_of_winW_ne_zero (left_ne_zero_of_mul hs)
  rw [sub_zero]
  linarith [abs_nonneg u]

theorem integrable_winW (u : ℝ) : Integrable (winW u) := by
  have := integrable_winW_mul (K := fun _ => 1) continuous_const u 0
  simpa using this

theorem winMass_nonneg (u : ℝ) : 0 ≤ winMass u := integral_nonneg (winW_nonneg u)

/-- **Z1 (c).** `W(u) ≤ 2/3`. -/
theorem winMass_le (u : ℝ) : winMass u ≤ 2 / 3 := by
  have h1 : ∫ s, winW u s ≤ ∫ s, Set.indicator (Set.Ioo (-(1 / 3 : ℝ)) (1 / 3)) (fun _ => (1 : ℝ)) s := by
    refine integral_mono (integrable_winW u) ?_ ?_
    · exact (integrable_indicator_iff measurableSet_Ioo).2 (integrableOn_const (by simp))
    · intro s
      by_cases h : winW u s = 0
      · rw [h]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) s
      · have := abs_lt_of_winW_ne_zero h
        rw [Set.indicator_of_mem]
        · exact winW_le_one u s
        · rw [Set.mem_Ioo, ← abs_lt]; linarith [abs_nonneg u]
  refine h1.trans (le_of_eq ?_)
  rw [integral_indicator_const _ measurableSet_Ioo]
  simp only [Real.volume_real_Ioo, smul_eq_mul, mul_one]
  norm_num

/-- **Z1 (c).** `W(u) ≥ 1/6` for `|u| ≤ 1/12`. -/
theorem le_winMass {u : ℝ} (hu : |u| ≤ 1 / 12) : 1 / 6 ≤ winMass u := by
  set a : ℝ := 1 / 6 - |u| with ha
  have ha0 : 1 / 12 ≤ a := by rw [ha]; linarith
  have h1 : ∫ s in Set.Icc (-a) a, winW u s ≤ ∫ s, winW u s :=
    setIntegral_le_integral (integrable_winW u) (Eventually.of_forall (winW_nonneg u))
  have h2 : ∫ s in Set.Icc (-a) a, winW u s = ∫ s in Set.Icc (-a) a, (1 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    exact winW_eq_one (abs_le.2 hs)
  rw [h2, setIntegral_const, Real.volume_real_Icc_of_le (by linarith)] at h1
  simp only [smul_eq_mul, mul_one] at h1
  unfold winMass
  linarith

/-! ## The window identity -/

theorem int_eq_of_abs_lt {n k l : ℤ} {u a b : ℝ} (hu : |u| ≤ 1 / 12) (ha : |a| < 1 / 3)
    (hb : |b| < 1 / 3) (hab : a + b = 2 * n + 2 * u - k - l) : l = 2 * n - k := by
  rw [abs_lt] at ha hb
  have hu' := abs_le.1 hu
  have h1 : ((2 * n - k - l : ℤ) : ℝ) < 1 := by push_cast; linarith [ha.1, ha.2, hb.1, hb.2]
  have h2 : (-1 : ℝ) < ((2 * n - k - l : ℤ) : ℝ) := by
    push_cast; linarith [ha.1, ha.2, hb.1, hb.2]
  have h1' : 2 * n - k - l < 1 := by exact_mod_cast h1
  have h2' : -1 < 2 * n - k - l := by exact_mod_cast h2
  omega

/-- The product of the two windows, as a function of `y`, for the pair `(k, 2n - k)`. -/
theorem lift_mul_lift_eq {f g : ℤ → ℂ} (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) (n : ℤ) {u : ℝ} (hu : |u| ≤ 1 / 12) (y : ℝ) :
    liftC (-1 / 2) f (n + u - y) * liftC (1 / 2) g (n + u + y) =
      ∑ k ∈ hf.toFinset, f k * g (2 * n - k) *
        ((stepBump (u + ((n - k : ℤ) : ℝ) + 1 / 2 - y) *
          stepBump (u + y - ((n - k : ℤ) : ℝ) - 1 / 2) : ℝ) : ℂ) := by
  have hS : ∀ k ∉ hf.toFinset, f k = 0 := fun k hk => by simpa using hk
  have hT : ∀ k ∉ hg.toFinset, g k = 0 := fun k hk => by simpa using hk
  rw [liftC_eq_sum (-1 / 2) hf.toFinset hS, liftC_eq_sum (1 / 2) hg.toFinset hT, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_eq_single (2 * n - k)]
  · have e1 : (n : ℝ) + u - y - k - (-1 / 2) = u + ((n - k : ℤ) : ℝ) + 1 / 2 - y := by
      push_cast; ring
    have e2 : (n : ℝ) + u + y - ((2 * n - k : ℤ) : ℝ) - 1 / 2 = u + y - ((n - k : ℤ) : ℝ) - 1 / 2 := by
      push_cast; ring
    rw [e1, e2]
    push_cast
    ring
  · intro l _ hl
    by_cases h1 : stepBump ((n : ℝ) + u - y - k - (-1 / 2)) = 0
    · simp only [h1, Complex.ofReal_zero, mul_zero, zero_mul]
    by_cases h2 : stepBump ((n : ℝ) + u + y - l - 1 / 2) = 0
    · simp only [h2, Complex.ofReal_zero, mul_zero]
    exact absurd (int_eq_of_abs_lt hu (abs_lt_of_stepBump_ne_zero h1) (abs_lt_of_stepBump_ne_zero h2)
      (by ring)) hl
  · intro h
    have : g (2 * n - k) = 0 := hT _ h
    simp [this]

theorem integral_window_term {K : ℝ → ℝ} (m : ℤ) (u : ℝ) :
    ∫ y, stepBump (u + (m : ℝ) + 1 / 2 - y) * stepBump (u + y - (m : ℝ) - 1 / 2) * K y =
      kappa K m u := by
  unfold kappa winW
  rw [← integral_add_left_eq_self (fun y => stepBump (u + (m : ℝ) + 1 / 2 - y) *
    stepBump (u + y - (m : ℝ) - 1 / 2) * K y) ((m : ℝ) + 1 / 2)]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  have e1 : u + (m : ℝ) + 1 / 2 - ((m : ℝ) + 1 / 2 + s) = u - s := by ring
  have e2 : u + ((m : ℝ) + 1 / 2 + s) - (m : ℝ) - 1 / 2 = u + s := by ring
  simp only [e1, e2]

/-- **Z1 (b).** For `n ∈ ℤ`, `|u| ≤ 1/12` and a continuous kernel `K`:
`∫ F(n + u - y) G(n + u + y) K(y) dy = ∑_m f(n - m) g(n + m) κ_m(u)`
with `F = liftC (-1/2) f`, `G = liftC (1/2) g`. -/
theorem integral_lift_eq {K : ℝ → ℝ} (hK : Continuous K) {f g : ℤ → ℂ}
    (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) (n : ℤ) {u : ℝ}
    (hu : |u| ≤ 1 / 12) :
    ∫ y, liftC (-1 / 2) f (n + u - y) * liftC (1 / 2) g (n + u + y) * (K y : ℂ) =
      ∑' m : ℤ, f (n - m) * g (n + m) * (kappa K m u : ℂ) := by
  have hint : ∀ k ∈ hf.toFinset, Integrable (fun y : ℝ => f k * g (2 * n - k) *
      ((stepBump (u + ((n - k : ℤ) : ℝ) + 1 / 2 - y) *
        stepBump (u + y - ((n - k : ℤ) : ℝ) - 1 / 2) * K y : ℝ) : ℂ)) := by
    intro k _
    refine Integrable.const_mul ?_ _
    refine integrable_of_forall_abs_sub_le (a := u + ((n - k : ℤ) : ℝ) + 1 / 2) (R := 1 / 3) ?_ ?_
    · have hc : Continuous fun y : ℝ => (stepBump (u + ((n - k : ℤ) : ℝ) + 1 / 2 - y) *
          stepBump (u + y - ((n - k : ℤ) : ℝ) - 1 / 2) * K y : ℝ) := by
        have := continuous_stepBump
        fun_prop
      exact Complex.continuous_ofReal.comp hc
    · intro y hy
      have h1 : stepBump (u + ((n - k : ℤ) : ℝ) + 1 / 2 - y) ≠ 0 := by
        intro h0
        exact hy (by rw [h0, zero_mul, zero_mul, Complex.ofReal_zero])
      have := abs_lt_of_stepBump_ne_zero h1
      rw [abs_sub_comm]
      exact this.le
  have step1 : ∀ y : ℝ, liftC (-1 / 2) f (n + u - y) * liftC (1 / 2) g (n + u + y) * (K y : ℂ) =
      ∑ k ∈ hf.toFinset, f k * g (2 * n - k) *
        ((stepBump (u + ((n - k : ℤ) : ℝ) + 1 / 2 - y) *
          stepBump (u + y - ((n - k : ℤ) : ℝ) - 1 / 2) * K y : ℝ) : ℂ) := by
    intro y
    rw [lift_mul_lift_eq hf hg n hu y, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  simp_rw [step1]
  rw [integral_finsetSum _ hint]
  have step2 : ∀ k ∈ hf.toFinset, ∫ y : ℝ, f k * g (2 * n - k) *
      ((stepBump (u + ((n - k : ℤ) : ℝ) + 1 / 2 - y) *
        stepBump (u + y - ((n - k : ℤ) : ℝ) - 1 / 2) * K y : ℝ) : ℂ) =
      f k * g (2 * n - k) * (kappa K (n - k) u : ℂ) := by
    intro k _
    rw [integral_const_mul, integral_complex_ofReal, integral_window_term]
  rw [Finset.sum_congr rfl step2]
  have hsupp : ∀ k ∉ hf.toFinset, f (n - (n - k)) * g (n + (n - k)) * (kappa K (n - k) u : ℂ) = 0 := by
    intro k hk
    have : f k = 0 := by simpa using hk
    simp [this]
  rw [← (Equiv.subLeft n).tsum_eq]
  simp only [Equiv.subLeft_apply]
  rw [tsum_eq_sum hsupp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sub_sub_cancel, show n + (n - k) = 2 * n - k by ring]

end PrimeBHT.TimeFrequency.Transfer

end
