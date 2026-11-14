module

public import PrimeBHT.TimeFrequency.X2.Pint.OscInterp
public import PrimeBHT.TimeFrequency.X2.Pint.FeffermanStein

/-!
# X2, V11 (Theorem II), part 2: auxiliary lemmas

* `minkowski_sq`: Minkowski's integral inequality in `L²(ν)` (lower Lebesgue integrals);
* `avgOn`, `yNorm_avgOn_le` (Jensen for the vector average on `[a, b)`);
* the coefficients `coefK K E x k = ∫_{E k} K x` of a kernel operator on step functions: measurability, bounds,
  `L¹`-integrability from the column bound.
-/

@[expose] public noncomputable section

open MeasureTheory Set Complex
open scoped ENNReal
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Pint

/-- **Minkowski's integral inequality** (`L²(ν)` of an integral), lower Lebesgue integrals. -/
theorem minkowski_sq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [SFinite μ] [IsFiniteMeasure ν] {f : α → β → ℝ≥0∞} (hf : Measurable (Function.uncurry f)) {Cf : ℝ≥0∞}
    (hCf : Cf ≠ ⊤) (hG : ∀ t, ∫⁻ x, f x t ∂μ ≤ Cf) :
    ∫⁻ t, (∫⁻ x, f x t ∂μ) ^ (2 : ℝ) ∂ν ≤ (∫⁻ x, (∫⁻ t, f x t ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) ∂μ) ^ (2 : ℝ) := by
  set G : β → ℝ≥0∞ := fun t => ∫⁻ x, f x t ∂μ with hGdef
  have hGm : Measurable G := hf.lintegral_prod_left'
  have hfx : ∀ t, Measurable fun x => f x t := fun t => hf.comp (measurable_prodMk_right (y := t))
  have hft : ∀ x, Measurable fun t => f x t := fun x => hf.comp (measurable_prodMk_left (x := x))
  set a := ∫⁻ t, G t ^ (2 : ℝ) ∂ν with ha
  set W := ∫⁻ x, (∫⁻ t, f x t ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) ∂μ with hW
  have hafin : a ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _t, Cf ^ (2 : ℝ) ∂ν) ?_ (lintegral_mono fun t => ?_)
    · rw [lintegral_const]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCf) (measure_ne_top _ _)
    · exact ENNReal.rpow_le_rpow (hG t) (by norm_num)
  have key : a ≤ a ^ (1 / 2 : ℝ) * W := by
    calc a = ∫⁻ t, ∫⁻ x, G t * f x t ∂μ ∂ν := by
          refine lintegral_congr fun t => ?_
          rw [ENNReal.rpow_two, sq, lintegral_const_mul _ (hfx t)]
      _ = ∫⁻ x, ∫⁻ t, G t * f x t ∂ν ∂μ :=
          (lintegral_lintegral_swap ((hGm.comp measurable_snd).mul hf).aemeasurable).symm
      _ ≤ ∫⁻ x, a ^ (1 / 2 : ℝ) * (∫⁻ t, f x t ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) ∂μ := by
          refine lintegral_mono fun x => ?_
          exact ENNReal.lintegral_mul_le_Lp_mul_Lq ν holder_two hGm.aemeasurable (hft x).aemeasurable
      _ = a ^ (1 / 2 : ℝ) * W := by
          rw [lintegral_const_mul]
          exact (Measurable.lintegral_prod_right' (hf.pow_const 2)).pow_const _
  by_cases ha0 : a = 0
  · rw [ha0]; exact zero_le
  have hr0 : a ^ (1 / 2 : ℝ) ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, ha0]
  have hrt : a ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hafin
  have hsplit : a = a ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_add _ _ ha0 hafin]; norm_num
  have hle : a ^ (1 / 2 : ℝ) ≤ W := by
    nth_rewrite 1 [hsplit] at key
    exact (ENNReal.mul_le_mul_iff_right hr0 hrt).1 key
  calc a = (a ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by rw [← ENNReal.rpow_mul]; norm_num
    _ ≤ W ^ (2 : ℝ) := ENNReal.rpow_le_rpow hle (by norm_num)

variable {P : ℕ} [NeZero P]

/-- The vector average of `G` over `[a, b)`. -/
def avgOn (a b : ℝ) (G : ℝ → ZMod P → ℂ) : ZMod P → ℂ :=
  fun y => (((b - a)⁻¹ : ℝ) : ℂ) * ∫ x in Ico a b, G x y

theorem yNorm_neg (p : ℝ) (w : ZMod P → ℂ) : yNorm p (-w) = yNorm p w := by
  simp [yNorm]

theorem yNorm_sub_le {p : ℝ} (hp : 1 ≤ p) (u w : ZMod P → ℂ) : yNorm p (u - w) ≤ yNorm p u + yNorm p w := by
  rw [sub_eq_add_neg]
  exact (CZ.yNorm_add_le hp u (-w)).trans_eq (by rw [yNorm_neg])

theorem abs_yNorm_sub_le {p : ℝ} (hp : 1 ≤ p) (u w : ZMod P → ℂ) :
    |yNorm p u - yNorm p w| ≤ yNorm p (u - w) := by
  have h1 : yNorm p u ≤ yNorm p (u - w) + yNorm p w := by
    have := CZ.yNorm_add_le hp (u - w) w; rwa [sub_add_cancel] at this
  have h2 : yNorm p w ≤ yNorm p (u - w) + yNorm p u := by
    have := CZ.yNorm_add_le hp (w - u) u
    rw [sub_add_cancel] at this
    have e : w - u = -(u - w) := by abel
    rwa [e, yNorm_neg] at this
  rw [abs_le]; constructor <;> linarith

/-- **Jensen for the vector average**. -/
theorem yNorm_avgOn_le {p : ℝ} (hp : 1 < p) {a b : ℝ} (hab : a < b) {G : ℝ → ZMod P → ℂ}
    (hGi : ∀ y, IntegrableOn (fun x => G x y) (Ico a b)) (hGn : IntegrableOn (fun x => yNorm p (G x)) (Ico a b)) :
    yNorm p (avgOn a b G) ≤ (b - a)⁻¹ * ∫ x in Ico a b, yNorm p (G x) := by
  have hba : 0 < b - a := sub_pos.2 hab
  have e : avgOn a b G = fun y => ∫ x in Ico a b, (((b - a)⁻¹ : ℝ) : ℂ) * G x y := by
    funext y; rw [avgOn, integral_const_mul]
  have hV : ∀ y, Integrable (fun x => (((b - a)⁻¹ : ℝ) : ℂ) * G x y) (volume.restrict (Ico a b)) :=
    fun y => (hGi y).const_mul _
  have hn : ∀ x, yNorm p (fun y => (((b - a)⁻¹ : ℝ) : ℂ) * G x y) = (b - a)⁻¹ * yNorm p (G x) := fun x => by
    rw [yNorm_fun_const_mul (by linarith), Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [e]
  refine (CZ.yNorm_integral_le hp _ hV ?_).trans (le_of_eq ?_)
  · simp_rw [hn]; exact hGn.const_mul _
  · simp_rw [hn]; rw [integral_const_mul]

/-! ## Coefficients of a kernel operator on step functions -/

/-- `∫_{E k} K x`. -/
def coefK (K : ℝ → ℝ → ℂ) {κ : Type*} (E : κ → Set ℝ) (x : ℝ) (k : κ) : ℂ := ∫ w, (E k).indicator (K x) w

section Coef

variable {K : ℝ → ℝ → ℂ} (hKm : StronglyMeasurable (Function.uncurry K)) {Cloc : ℝ}
  (hKr : ∀ x, ∫⁻ w, ‖K x w‖ₑ ≤ ENNReal.ofReal Cloc) {κ : Type*} [Fintype κ] {E : κ → Set ℝ}
  (hEd : IsStepData E)

include hKm hKr in
theorem integrable_kernel_row (x : ℝ) : Integrable (K x) :=
  ⟨(hKm.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
    (hKr x).trans_lt ENNReal.ofReal_lt_top⟩

include hKm hKr hEd in
theorem kernelOp_stepFun' (v : κ → ZMod P → ℂ) (x : ℝ) :
    kernelOp K (stepFun E v) x = ∑ k, coefK K E x k • v k :=
  kernelOp_stepFun (integrable_kernel_row hKm hKr x) hEd.1 v

include hKm hEd in
theorem measurable_coefK (k : κ) : Measurable fun x => coefK K E x k := by
  have h1 : (Function.uncurry fun x w => (E k).indicator (K x) w) =
      (Prod.snd ⁻¹' E k).indicator (Function.uncurry K) := by
    funext p
    show (E k).indicator (K p.1) p.2 = (Prod.snd ⁻¹' E k).indicator (Function.uncurry K) p
    by_cases hp : p.2 ∈ E k
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show p ∈ Prod.snd ⁻¹' E k from hp)]; rfl
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (show p ∉ Prod.snd ⁻¹' E k from hp)]
  have h2 : StronglyMeasurable (Function.uncurry fun x w => (E k).indicator (K x) w) := by
    rw [h1]; exact hKm.indicator (measurable_snd (hEd.1 k))
  exact (h2.integral_prod_right (ν := volume)).measurable

include hKr hEd in
theorem norm_coefK_le (hCloc : 0 ≤ Cloc) (x : ℝ) (k : κ) : ‖coefK K E x k‖ ≤ Cloc :=
  (Finset.single_le_sum (f := fun k => ‖coefK K E x k‖) (fun _k _ => norm_nonneg _) (Finset.mem_univ k)).trans
    (sum_norm_coeff_le hCloc (hKr x) hEd)

include hKm hEd in
/-- The column bound gives integrable coefficients. -/
theorem integrable_coefK (hKc : ∀ w, ∫⁻ x, ‖K x w‖ₑ ≤ ENNReal.ofReal Cloc) (k : κ) :
    Integrable fun x => coefK K E x k := by
  refine ⟨(measurable_coefK hKm hEd k).aestronglyMeasurable, ?_⟩
  have hm : Measurable (Function.uncurry fun x w => ‖(E k).indicator (K x) w‖ₑ) := by
    have : (Function.uncurry fun x w => ‖(E k).indicator (K x) w‖ₑ) =
        fun p : ℝ × ℝ => (Prod.snd ⁻¹' E k).indicator (fun p => ‖Function.uncurry K p‖ₑ) p := by
      funext p
      show ‖(E k).indicator (K p.1) p.2‖ₑ = _
      by_cases hp : p.2 ∈ E k
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show p ∈ Prod.snd ⁻¹' E k from hp)]; rfl
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (show p ∉ Prod.snd ⁻¹' E k from hp)]; simp
    rw [this]
    exact (hKm.measurable.enorm).indicator (measurable_snd (hEd.1 k))
  show ∫⁻ x, ‖coefK K E x k‖ₑ < ⊤
  calc ∫⁻ x, ‖coefK K E x k‖ₑ ≤ ∫⁻ x, ∫⁻ w, ‖(E k).indicator (K x) w‖ₑ :=
        lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ w, ∫⁻ x, ‖(E k).indicator (K x) w‖ₑ := lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ w, (E k).indicator (fun w => ∫⁻ x, ‖K x w‖ₑ) w := by
        refine lintegral_congr fun w => ?_
        by_cases hw : w ∈ E k <;> simp [hw]
    _ = ∫⁻ w in E k, ∫⁻ x, ‖K x w‖ₑ := lintegral_indicator (hEd.1 k) _
    _ ≤ ∫⁻ _w in E k, ENNReal.ofReal Cloc := setLIntegral_mono' (hEd.1 k) fun w _ => hKc w
    _ < ⊤ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hEd.2.1 k)

end Coef

end PrimeBHT.TimeFrequency.X2.Pint
