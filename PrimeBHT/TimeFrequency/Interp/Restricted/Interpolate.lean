module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Layer-cake interpolation: from two weak-type tail bounds to an `L^r` bound

The analytic engine of R6b, (RS) from (RWT) (blueprint `docs/x1-blueprint.md`, node R6b,
"(RS) from (RWT)").  Independent of the form `Λ` and the operator `T`.

* `lintegral_enorm_rpow_le_of_weak`: if `μ{‖f‖ > t} ≤ D₀ t^{-p₀}` and `≤ D₁ t^{-p₁}` for all
  `t > 0` with `0 < p₀ < r < p₁`, then for every `L > 0`,
  `∫⁻ ‖f‖^r ≤ ofReal (r (D₀ L^{r-p₀}/(r-p₀) + D₁ L^{r-p₁}/(p₁-r)))`.
* `eLpNorm_le_of_weak_pair`: the weak bounds `t μ{‖F‖>t}^{s±ε} ≤ K± x₁^{a₁±ε} x₂^{a₂}`
  (`s = a₁+a₂`) give `‖F‖_{L^{1/s}} ≤ rsConst s ε Kp Km · x₁^{a₁} x₂^{a₂}`; the crossing point
  `L = x₁^{-a₂} x₂^{a₂}` makes the `x₁^{±ε}`-terms cancel (the blueprint's
  `2 rp rm - r (rp + rm) = 0`; here `κ = s/ε`).
-/

@[expose] public section

namespace PrimeBHT.TimeFrequency.Interp.Restricted

open MeasureTheory Set
open scoped ENNReal

section LayerCake

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Layer-cake formula for `∫⁻ ‖f‖ₑ ^ r` with `r > 0`. -/
lemma lintegral_enorm_rpow_eq_lintegral_meas_lt {E : Type*} [NormedAddCommGroup E] {f : α → E}
    (hf : AEMeasurable (fun x => ‖f x‖) μ) {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, ‖f x‖ₑ ^ r ∂μ =
      ∫⁻ t in Ioi (0 : ℝ), μ {x | t < ‖f x‖} * ENNReal.ofReal (r * t ^ (r - 1)) := by
  have hg : ∀ t > (0 : ℝ), IntervalIntegrable (fun s : ℝ => r * s ^ (r - 1)) volume 0 t :=
    fun t _ => (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul r
  have hnn : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ r * t ^ (r - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg hr.le (Real.rpow_nonneg (le_of_lt ht) _)
  have key := lintegral_comp_eq_lintegral_meas_lt_mul μ (f := fun x => ‖f x‖)
    (Filter.Eventually.of_forall fun x => norm_nonneg _) hf hg hnn
  rw [← key]
  refine lintegral_congr fun x => ?_
  have hint : ∫ s in (0 : ℝ)..‖f x‖, r * s ^ (r - 1) = ‖f x‖ ^ r := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
    have : r - 1 + 1 = r := by ring
    rw [this, Real.zero_rpow hr.ne']
    field_simp
    ring
  rw [hint, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr.le]

/-- Pointwise bound on the integrand of the layer cake formula from a weak-type tail bound. -/
lemma meas_mul_ofReal_le {m : ℝ≥0∞} {D p r t : ℝ} (hD : 0 ≤ D) (ht : 0 < t)
    (hm : m ≤ ENNReal.ofReal (D * t ^ (-p))) :
    m * ENNReal.ofReal (r * t ^ (r - 1)) ≤ ENNReal.ofReal (r * D * t ^ (r - 1 - p)) := by
  calc m * ENNReal.ofReal (r * t ^ (r - 1))
      ≤ ENNReal.ofReal (D * t ^ (-p)) * ENNReal.ofReal (r * t ^ (r - 1)) := by gcongr
    _ = ENNReal.ofReal (D * t ^ (-p) * (r * t ^ (r - 1))) :=
        (ENNReal.ofReal_mul (mul_nonneg hD (Real.rpow_nonneg ht.le _))).symm
    _ = ENNReal.ofReal (r * D * t ^ (r - 1 - p)) := by
        congr 1
        have : t ^ (r - 1 - p) = t ^ (-p) * t ^ (r - 1) := by
          rw [← Real.rpow_add ht]; congr 1; ring
        rw [this]; ring

/-- The `Ioc` piece. -/
lemma lintegral_Ioc_rpow {r p L D : ℝ} (hr : 0 < r) (hpr : p < r) (hL : 0 < L) (hD : 0 ≤ D) :
    ∫⁻ t in Ioc (0 : ℝ) L, ENNReal.ofReal (r * D * t ^ (r - 1 - p)) =
      ENNReal.ofReal (r * D * L ^ (r - p) / (r - p)) := by
  have hint : IntervalIntegrable (fun t : ℝ => r * D * t ^ (r - 1 - p)) volume 0 L :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul (r * D)
  have hval : ∫ t in Ioc (0 : ℝ) L, r * D * t ^ (r - 1 - p) = r * D * L ^ (r - p) / (r - p) := by
    rw [← intervalIntegral.integral_of_le hL.le, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith))]
    have h1 : r - 1 - p + 1 = r - p := by ring
    rw [h1, Real.zero_rpow (by linarith)]
    ring
  rw [← hval, ofReal_integral_eq_lintegral_ofReal]
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).1 hint
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (mul_nonneg hr.le hD) (Real.rpow_nonneg ht.1.le _)

/-- The `Ioi` piece. -/
lemma lintegral_Ioi_rpow {r p L D : ℝ} (hr : 0 < r) (hpr : r < p) (hL : 0 < L) (hD : 0 ≤ D) :
    ∫⁻ t in Ioi L, ENNReal.ofReal (r * D * t ^ (r - 1 - p)) =
      ENNReal.ofReal (r * D * L ^ (r - p) / (p - r)) := by
  have hint : IntegrableOn (fun t : ℝ => r * D * t ^ (r - 1 - p)) (Ioi L) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hL).const_mul (r * D)
  have hval : ∫ t in Ioi L, r * D * t ^ (r - 1 - p) = r * D * L ^ (r - p) / (p - r) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hL]
    have h1 : r - 1 - p + 1 = r - p := by ring
    rw [h1]
    have : p - r ≠ 0 := by linarith
    have : r - p ≠ 0 := by linarith
    field_simp
    ring
  rw [← hval, ofReal_integral_eq_lintegral_ofReal hint]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (mul_nonneg hr.le hD) (Real.rpow_nonneg (hL.trans ht).le _)

/-- **Layer-cake interpolation.** Two weak-type tail bounds `p₀ < r < p₁` give an `L^r` bound. -/
theorem lintegral_enorm_rpow_le_of_weak {E : Type*} [NormedAddCommGroup E] {f : α → E}
    (hf : AEMeasurable (fun x => ‖f x‖) μ)
    {p₀ p₁ r D₀ D₁ L : ℝ} (hp₀ : 0 < p₀) (h₀r : p₀ < r) (hr₁ : r < p₁)
    (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁) (hL : 0 < L)
    (h₀ : ∀ t : ℝ, 0 < t → μ {x | t < ‖f x‖} ≤ ENNReal.ofReal (D₀ * t ^ (-p₀)))
    (h₁ : ∀ t : ℝ, 0 < t → μ {x | t < ‖f x‖} ≤ ENNReal.ofReal (D₁ * t ^ (-p₁))) :
    ∫⁻ x, ‖f x‖ₑ ^ r ∂μ ≤
      ENNReal.ofReal (r * (D₀ * L ^ (r - p₀) / (r - p₀) + D₁ * L ^ (r - p₁) / (p₁ - r))) := by
  have hr : 0 < r := hp₀.trans h₀r
  rw [lintegral_enorm_rpow_eq_lintegral_meas_lt hf hr,
    ← Ioc_union_Ioi_eq_Ioi hL.le,
    lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
  have e1 : ∫⁻ t in Ioc (0 : ℝ) L, μ {x | t < ‖f x‖} * ENNReal.ofReal (r * t ^ (r - 1)) ≤
      ENNReal.ofReal (r * D₀ * L ^ (r - p₀) / (r - p₀)) := by
    rw [← lintegral_Ioc_rpow hr h₀r hL hD₀]
    exact setLIntegral_mono' measurableSet_Ioc fun t ht =>
      meas_mul_ofReal_le hD₀ ht.1 (h₀ t ht.1)
  have e2 : ∫⁻ t in Ioi L, μ {x | t < ‖f x‖} * ENNReal.ofReal (r * t ^ (r - 1)) ≤
      ENNReal.ofReal (r * D₁ * L ^ (r - p₁) / (p₁ - r)) := by
    rw [← lintegral_Ioi_rpow hr hr₁ hL hD₁]
    exact setLIntegral_mono' measurableSet_Ioi fun t ht =>
      meas_mul_ofReal_le hD₁ (hL.trans ht) (h₁ t (hL.trans ht))
  calc _ ≤ ENNReal.ofReal (r * D₀ * L ^ (r - p₀) / (r - p₀)) +
        ENNReal.ofReal (r * D₁ * L ^ (r - p₁) / (p₁ - r)) := add_le_add e1 e2
    _ = ENNReal.ofReal (r * D₀ * L ^ (r - p₀) / (r - p₀) + r * D₁ * L ^ (r - p₁) / (p₁ - r)) := by
        rw [ENNReal.ofReal_add]
        · have := Real.rpow_nonneg hL.le (r - p₀)
          have : 0 < r - p₀ := by linarith
          positivity
        · have := Real.rpow_nonneg hL.le (r - p₁)
          have : 0 < p₁ - r := by linarith
          positivity
    _ = _ := by congr 1; ring


/-- A weak-type bound `t · m^q ≤ B` gives `m ≤ B^{1/q} t^{-1/q}`. -/
lemma meas_le_of_weak {m : ℝ≥0∞} {t B q : ℝ} (ht : 0 < t) (hB : 0 ≤ B) (hq : 0 < q)
    (h : ENNReal.ofReal t * m ^ q ≤ ENNReal.ofReal B) :
    m ≤ ENNReal.ofReal (B ^ (1 / q) * t ^ (-(1 / q))) := by
  have h1 : m ^ q ≤ ENNReal.ofReal (B / t) := by
    rw [ENNReal.ofReal_div_of_pos ht]
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using ht)) (Or.inl (by simp))]
    rwa [mul_comm]
  have h2 : m = (m ^ q) ^ q⁻¹ := (ENNReal.rpow_rpow_inv hq.ne' m).symm
  calc m = (m ^ q) ^ q⁻¹ := h2
    _ ≤ (ENNReal.ofReal (B / t)) ^ q⁻¹ := ENNReal.rpow_le_rpow h1 (inv_nonneg.2 hq.le)
    _ = ENNReal.ofReal ((B / t) ^ q⁻¹) :=
        ENNReal.ofReal_rpow_of_nonneg (div_nonneg hB ht.le) (inv_nonneg.2 hq.le)
    _ = _ := by
        congr 1
        rw [Real.div_rpow hB ht.le, one_div, Real.rpow_neg ht.le, div_eq_mul_inv]

/-- The exponent identity behind the cancellation of the `x₁^{±ε}`-terms. -/
lemma interp_identity {x₁ x₂ K a₁ a₂ e : ℝ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hK : 0 ≤ K)
    (hs : 0 < a₁ + a₂) (hq : 0 < a₁ + a₂ + e) :
    (K * x₁ ^ (a₁ + e) * x₂ ^ a₂) ^ (1 / (a₁ + a₂ + e)) *
        (x₁ ^ (-a₂) * x₂ ^ a₂) ^ (1 / (a₁ + a₂) - 1 / (a₁ + a₂ + e)) =
      K ^ (1 / (a₁ + a₂ + e)) * (x₁ ^ a₁ * x₂ ^ a₂) ^ (1 / (a₁ + a₂)) := by
  rw [mul_assoc, Real.mul_rpow hK (mul_nonneg (Real.rpow_nonneg hx₁.le _)
    (Real.rpow_nonneg hx₂.le _)), mul_assoc]
  congr 1
  obtain ⟨l₁, rfl⟩ : ∃ l, x₁ = Real.exp l := ⟨Real.log x₁, (Real.exp_log hx₁).symm⟩
  obtain ⟨l₂, rfl⟩ : ∃ l, x₂ = Real.exp l := ⟨Real.log x₂, (Real.exp_log hx₂).symm⟩
  simp only [← Real.exp_mul, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- The constant of the interpolated bound. -/
noncomputable def rsConst (s ε Kp Km : ℝ) : ℝ :=
  (1 / s * (Kp ^ (1 / (s + ε)) / (1 / s - 1 / (s + ε)) +
    Km ^ (1 / (s - ε)) / (1 / (s - ε) - 1 / s))) ^ s

lemma rsConst_nonneg {s ε Kp Km : ℝ} (hs : 0 < s) (hε : 0 < ε) (hεs : ε < s) (hKp : 0 ≤ Kp)
    (hKm : 0 ≤ Km) : 0 ≤ rsConst s ε Kp Km := by
  have hd₀ : 0 < 1 / s - 1 / (s + ε) := by
    have := one_div_lt_one_div_of_lt hs (show s < s + ε by linarith)
    linarith
  have hd₁ : 0 < 1 / (s - ε) - 1 / s := by
    have := one_div_lt_one_div_of_lt (show 0 < s - ε by linarith) (show s - ε < s by linarith)
    linarith
  unfold rsConst
  refine Real.rpow_nonneg ?_ _
  have := Real.rpow_nonneg hKp (1 / (s + ε))
  have := Real.rpow_nonneg hKm (1 / (s - ε))
  positivity

lemma rsConst_mono {s ε Kp Km Kp' Km' : ℝ} (hs : 0 < s) (hε : 0 < ε) (hεs : ε < s)
    (hKp : 0 ≤ Kp) (hKm : 0 ≤ Km) (hp : Kp ≤ Kp') (hm : Km ≤ Km') :
    rsConst s ε Kp Km ≤ rsConst s ε Kp' Km' := by
  have hd₀ : 0 < 1 / s - 1 / (s + ε) := by
    have := one_div_lt_one_div_of_lt hs (show s < s + ε by linarith)
    linarith
  have hd₁ : 0 < 1 / (s - ε) - 1 / s := by
    have := one_div_lt_one_div_of_lt (show 0 < s - ε by linarith) (show s - ε < s by linarith)
    linarith
  have e₀ : 0 ≤ 1 / (s + ε) := by positivity
  have e₁ : 0 ≤ 1 / (s - ε) := by
    have : 0 < s - ε := by linarith
    positivity
  have h1 : Kp ^ (1 / (s + ε)) ≤ Kp' ^ (1 / (s + ε)) := Real.rpow_le_rpow hKp hp e₀
  have h2 : Km ^ (1 / (s - ε)) ≤ Km' ^ (1 / (s - ε)) := Real.rpow_le_rpow hKm hm e₁
  have hn1 := Real.rpow_nonneg hKp (1 / (s + ε))
  have hn2 := Real.rpow_nonneg hKm (1 / (s - ε))
  unfold rsConst
  refine Real.rpow_le_rpow ?_ ?_ hs.le
  · positivity
  · have hs' : 0 < 1 / s := one_div_pos.2 hs
    refine mul_le_mul_of_nonneg_left ?_ hs'.le
    exact add_le_add (div_le_div_of_nonneg_right h1 hd₀.le) (div_le_div_of_nonneg_right h2 hd₁.le)

/-- **(RS) from two weak-type bounds.**  With `s = a₁ + a₂`, `0 < ε < a₁`, positive `x₁ x₂`: the weak
bounds `t μ{‖F‖ > t}^{s ± ε} ≤ K± x₁^{a₁ ± ε} x₂^{a₂}` give
`‖F‖_{L^{1/s}} ≤ rsConst s ε Kp Km · x₁^{a₁} x₂^{a₂}`. -/
theorem eLpNorm_le_of_weak_pair {E : Type*} [NormedAddCommGroup E] {F : α → E}
    (hF : AEStronglyMeasurable F μ) {a₁ a₂ ε x₁ x₂ Kp Km : ℝ}
    (ha₁ : ε < a₁) (ha₂ : 0 < a₂) (hε : 0 < ε) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (hKp : 0 ≤ Kp) (hKm : 0 ≤ Km)
    (hwp : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {x | t < ‖F x‖} ^ (a₁ + a₂ + ε) ≤
      ENNReal.ofReal (Kp * x₁ ^ (a₁ + ε) * x₂ ^ a₂))
    (hwm : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {x | t < ‖F x‖} ^ (a₁ + a₂ - ε) ≤
      ENNReal.ofReal (Km * x₁ ^ (a₁ - ε) * x₂ ^ a₂)) :
    eLpNorm F (ENNReal.ofReal (1 / (a₁ + a₂))) μ ≤
      ENNReal.ofReal (rsConst (a₁ + a₂) ε Kp Km * (x₁ ^ a₁ * x₂ ^ a₂)) := by
  have hs : 0 < a₁ + a₂ := by linarith
  have hqp : 0 < a₁ + a₂ + ε := by linarith
  have hqm : 0 < a₁ + a₂ + -ε := by linarith
  have hr : 0 < 1 / (a₁ + a₂) := one_div_pos.2 hs
  have hp₀ : 0 < 1 / (a₁ + a₂ + ε) := one_div_pos.2 hqp
  have hp₀r : 1 / (a₁ + a₂ + ε) < 1 / (a₁ + a₂) := one_div_lt_one_div_of_lt hs (by linarith)
  have hrp₁ : 1 / (a₁ + a₂) < 1 / (a₁ + a₂ + -ε) := one_div_lt_one_div_of_lt hqm (by linarith)
  have hwm' : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {x | t < ‖F x‖} ^ (a₁ + a₂ + -ε) ≤
      ENNReal.ofReal (Km * x₁ ^ (a₁ + -ε) * x₂ ^ a₂) := by
    simpa only [← sub_eq_add_neg] using hwm
  have hBp : 0 ≤ Kp * x₁ ^ (a₁ + ε) * x₂ ^ a₂ :=
    mul_nonneg (mul_nonneg hKp (Real.rpow_nonneg hx₁.le _)) (Real.rpow_nonneg hx₂.le _)
  have hBm : 0 ≤ Km * x₁ ^ (a₁ + -ε) * x₂ ^ a₂ :=
    mul_nonneg (mul_nonneg hKm (Real.rpow_nonneg hx₁.le _)) (Real.rpow_nonneg hx₂.le _)
  have hL : 0 < x₁ ^ (-a₂) * x₂ ^ a₂ :=
    mul_pos (Real.rpow_pos_of_pos hx₁ _) (Real.rpow_pos_of_pos hx₂ _)
  have key := lintegral_enorm_rpow_le_of_weak hF.norm.aemeasurable hp₀ hp₀r hrp₁
    (Real.rpow_nonneg hBp _) (Real.rpow_nonneg hBm _) hL
    (fun t ht => meas_le_of_weak ht hBp hqp (hwp t ht))
    (fun t ht => meas_le_of_weak ht hBm hqm (hwm' t ht))
  rw [interp_identity hx₁ hx₂ hKp hs hqp, interp_identity hx₁ hx₂ hKm hs hqm] at key
  simp only [← sub_eq_add_neg] at key
  set s := a₁ + a₂ with hs_def
  simp only [← sub_eq_add_neg] at hrp₁ hqm
  set X := x₁ ^ a₁ * x₂ ^ a₂ with hX
  have hX0 : 0 < X := mul_pos (Real.rpow_pos_of_pos hx₁ _) (Real.rpow_pos_of_pos hx₂ _)
  have hd₀ : 0 < 1 / s - 1 / (s + ε) := by linarith
  have hd₁ : 0 < 1 / (s - ε) - 1 / s := by linarith
  have hinner : 0 ≤ 1 / s * (Kp ^ (1 / (s + ε)) / (1 / s - 1 / (s + ε)) +
      Km ^ (1 / (s - ε)) / (1 / (s - ε) - 1 / s)) := by
    have := Real.rpow_nonneg hKp (1 / (s + ε))
    have := Real.rpow_nonneg hKm (1 / (s - ε))
    positivity
  have hrs : rsConst s ε Kp Km ^ (1 / s) = 1 / s * (Kp ^ (1 / (s + ε)) / (1 / s - 1 / (s + ε)) +
      Km ^ (1 / (s - ε)) / (1 / (s - ε) - 1 / s)) := by
    unfold rsConst
    rw [← Real.rpow_mul hinner, mul_one_div_cancel hs.ne', Real.rpow_one]
  have hrs0 : 0 ≤ rsConst s ε Kp Km := Real.rpow_nonneg hinner _
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr) (by simp) hF,
    ENNReal.toReal_ofReal hr.le]
  calc (∫⁻ x, ‖F x‖ₑ ^ (1 / s) ∂μ) ^ (1 / (1 / s))
      ≤ (ENNReal.ofReal ((rsConst s ε Kp Km * X) ^ (1 / s))) ^ (1 / (1 / s)) := by
        refine ENNReal.rpow_le_rpow (key.trans (le_of_eq ?_)) (by positivity)
        congr 1
        rw [Real.mul_rpow hrs0 hX0.le, hrs]
        ring
    _ = ENNReal.ofReal (rsConst s ε Kp Km * X) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), one_div_one_div,
          ← Real.rpow_mul (by positivity), one_div_mul_cancel hs.ne', Real.rpow_one]

end LayerCake

end PrimeBHT.TimeFrequency.Interp.Restricted
