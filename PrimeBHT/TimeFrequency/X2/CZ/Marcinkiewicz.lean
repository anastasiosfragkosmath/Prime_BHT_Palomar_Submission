module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# V08 phase 3: the analytic core of the Marcinkiewicz interpolation theorem

`marcinkiewicz_aux`: let `U, G ≥ 0` be measurable and `1 < q < s`.  If for every `λ > 0`
`|{U > 2λ}| ≤ (c₀/λ) ∫_{G > λ} G + (c₁/λ)^s ∫_{G ≤ λ} G^s`
(the distribution inequality that follows from weak `(1,1)` applied to the part of the function where
`G > λ` and strong `(s,s)` applied to the rest), then
`∫ U^q ≤ q 2^q (c₀/(q-1) + c₁^s/(s-q)) ∫ G^q`.

Proved from the layer cake formula and two Tonelli computations
(`lintegral_tail_mass`: `∫_0^∞ t^{q-2} ∫_{G > t} G = (q-1)^{-1} ∫ G^q`;
`lintegral_cutoff_mass`: `∫_0^∞ t^{q-1-s} ∫_{G ≤ t} G^s = (s-q)^{-1} ∫ G^q`).  Pure measure theory, no
operator and no normed space: the operator-level statements (`MarcinkiewiczKernel.lean`) feed it with
`U = ‖T F‖_{L^s(Y)}` and `G = ‖F‖_{L^s(Y)}`, which is why the `L^s(Y)`-valued case needs no instance of a
normed space on `ZMod P → ℂ`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

theorem lintegral_Ioo_rpow {r g : ℝ} (hr : -1 < r) (hg : 0 ≤ g) :
    ∫⁻ t in Ioo 0 g, ENNReal.ofReal (t ^ r) = ENNReal.ofReal (g ^ (r + 1) / (r + 1)) := by
  rcases hg.eq_or_lt with h0 | hpos
  · subst h0
    simp [Real.zero_rpow (by linarith : r + 1 ≠ 0)]
  · rw [setLIntegral_congr Ioo_ae_eq_Ioc]
    have hint : IntegrableOn (fun t : ℝ => t ^ r) (Ioc 0 g) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := g) hr)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hpos.le).1 this
    rw [← ofReal_integral_eq_lintegral_ofReal hint]
    · congr 1
      rw [← intervalIntegral.integral_of_le hpos.le, integral_rpow (Or.inl hr)]
      simp [Real.zero_rpow (by linarith : r + 1 ≠ 0)]
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact Real.rpow_nonneg ht.1.le _

theorem lintegral_Ioi_rpow' {r g : ℝ} (hr : r < -1) (hg : 0 < g) :
    ∫⁻ t in Ioi g, ENNReal.ofReal (t ^ r) = ENNReal.ofReal (g ^ (r + 1) / (-(r + 1))) := by
  have hint : IntegrableOn (fun t : ℝ => t ^ r) (Ioi g) := integrableOn_Ioi_rpow_of_lt hr hg
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [integral_Ioi_rpow_of_lt hr hg]
    have : r + 1 ≠ 0 := by linarith
    field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hg.le.trans (le_of_lt ht)) _

section Fub
variable {G : ℝ → ℝ}

theorem lintegral_tail_mass (hGm : Measurable G) (hG0 : ∀ x, 0 ≤ G x) {q : ℝ} (hq : 1 < q) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 2)) * ∫⁻ x in {x | t < G x}, ENNReal.ofReal (G x) =
      ENNReal.ofReal (1 / (q - 1)) * ∫⁻ x, ENNReal.ofReal (G x) ^ q := by
  set φ : ℝ → ℝ → ℝ≥0∞ := fun t x =>
    ENNReal.ofReal (t ^ (q - 2)) * ({x | t < G x}.indicator (fun x => ENNReal.ofReal (G x)) x)
    with hφ
  have h1 : ∀ t, ENNReal.ofReal (t ^ (q - 2)) * ∫⁻ x in {x | t < G x}, ENNReal.ofReal (G x) =
      ∫⁻ x, φ t x := by
    intro t
    rw [← lintegral_indicator (measurableSet_lt measurable_const hGm),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp_rw [h1]
  have hmeas : Measurable (Function.uncurry φ) := by
    have : Function.uncurry φ = fun p : ℝ × ℝ => ENNReal.ofReal (p.1 ^ (q - 2)) *
        (if p.1 < G p.2 then ENNReal.ofReal (G p.2) else 0) := by
      ext p; simp only [Function.uncurry, hφ, indicator, mem_ofPred_eq]
    rw [this]
    refine Measurable.mul ((measurable_fst.pow_const _).ennreal_ofReal) ?_
    exact Measurable.ite (measurableSet_lt measurable_fst (hGm.comp measurable_snd))
      ((hGm.comp measurable_snd).ennreal_ofReal) measurable_const
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have h2 : ∀ x, ∫⁻ t in Ioi (0 : ℝ), φ t x =
      ENNReal.ofReal (G x) * ENNReal.ofReal (G x ^ (q - 1) / (q - 1)) := by
    intro x
    have hind : (fun t => (Ioi (0 : ℝ)).indicator (fun t => φ t x) t) =
        (Ioo 0 (G x)).indicator (fun t => ENNReal.ofReal (G x) * ENNReal.ofReal (t ^ (q - 2))) := by
      ext t
      by_cases ht : 0 < t
      · by_cases hlt : t < G x
        · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht),
            indicator_of_mem (show t ∈ Ioo 0 (G x) from ⟨ht, hlt⟩)]
          simp only [hφ, indicator, mem_ofPred_eq, hlt, ite_true]; ring
        · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht),
            indicator_of_notMem (show t ∉ Ioo 0 (G x) from fun h => hlt h.2)]
          simp [hφ, hlt]
      · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht),
          indicator_of_notMem (show t ∉ Ioo 0 (G x) from fun h => ht h.1)]
    rw [← lintegral_indicator measurableSet_Ioi, hind, lintegral_indicator measurableSet_Ioo,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_Ioo_rpow (by linarith : -1 < q - 2) (hG0 x)]
    congr 2
    rw [show q - 2 + 1 = q - 1 by ring]
  simp_rw [h2]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.ofReal_mul (hG0 x), ENNReal.ofReal_rpow_of_nonneg (hG0 x) (by linarith),
    ← ENNReal.ofReal_mul (by positivity)]
  rcases (hG0 x).eq_or_lt with h0 | hpos
  · rw [← h0]; simp [Real.zero_rpow (by linarith : q ≠ 0), Real.zero_rpow (by linarith : q - 1 ≠ 0)]
  · congr 1
    rw [show G x ^ q = G x * G x ^ (q - 1) by rw [← Real.rpow_one_add' hpos.le (by linarith)]; congr 1; ring]
    field_simp

theorem lintegral_cutoff_mass (hGm : Measurable G) (hG0 : ∀ x, 0 ≤ G x) {q s : ℝ} (hq : 1 < q)
    (hqs : q < s) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1 - s)) *
        ∫⁻ x in {x | G x ≤ t}, ENNReal.ofReal (G x) ^ s =
      ENNReal.ofReal (1 / (s - q)) * ∫⁻ x, ENNReal.ofReal (G x) ^ q := by
  set ψ : ℝ → ℝ → ℝ≥0∞ := fun t x =>
    ENNReal.ofReal (t ^ (q - 1 - s)) *
      ({x | G x ≤ t}.indicator (fun x => ENNReal.ofReal (G x) ^ s) x) with hψ
  have h1 : ∀ t, ENNReal.ofReal (t ^ (q - 1 - s)) *
      ∫⁻ x in {x | G x ≤ t}, ENNReal.ofReal (G x) ^ s = ∫⁻ x, ψ t x := by
    intro t
    rw [← lintegral_indicator (measurableSet_le hGm measurable_const),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp_rw [h1]
  have hmeas : Measurable (Function.uncurry ψ) := by
    have : Function.uncurry ψ = fun p : ℝ × ℝ => ENNReal.ofReal (p.1 ^ (q - 1 - s)) *
        (if G p.2 ≤ p.1 then ENNReal.ofReal (G p.2) ^ s else 0) := by
      ext p; simp only [Function.uncurry, hψ, indicator, mem_ofPred_eq]
    rw [this]
    refine Measurable.mul ((measurable_fst.pow_const _).ennreal_ofReal) ?_
    exact Measurable.ite (measurableSet_le (hGm.comp measurable_snd) measurable_fst)
      (((hGm.comp measurable_snd).ennreal_ofReal).pow_const _) measurable_const
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have h2 : ∀ x, ∫⁻ t in Ioi (0 : ℝ), ψ t x =
      ENNReal.ofReal (G x) ^ s * ENNReal.ofReal (G x ^ (q - s) / (s - q)) := by
    intro x
    rcases (hG0 x).eq_or_lt with h0 | hpos
    · have : ∀ t, ψ t x = 0 := by
        intro t; simp [hψ, ← h0, ENNReal.zero_rpow_of_pos (by linarith : 0 < s)]
      simp [this, ← h0, ENNReal.zero_rpow_of_pos (by linarith : 0 < s)]
    · have hind : (fun t => (Ioi (0 : ℝ)).indicator (fun t => ψ t x) t) =
          (Ici (G x)).indicator (fun t => ENNReal.ofReal (G x) ^ s * ENNReal.ofReal (t ^ (q - 1 - s))) := by
        ext t
        by_cases ht : G x ≤ t
        · have ht0 : t ∈ Ioi (0 : ℝ) := lt_of_lt_of_le hpos ht
          rw [indicator_of_mem ht0, indicator_of_mem (show t ∈ Ici (G x) from ht)]
          simp only [hψ, indicator, mem_ofPred_eq, ht, ite_true]; ring
        · rw [indicator_of_notMem (show t ∉ Ici (G x) from ht)]
          by_cases ht0 : t ∈ Ioi (0 : ℝ)
          · rw [indicator_of_mem ht0]; simp [hψ, ht]
          · rw [indicator_of_notMem ht0]
      rw [← lintegral_indicator measurableSet_Ioi, hind, lintegral_indicator measurableSet_Ici,
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top),
        setLIntegral_congr Ioi_ae_eq_Ici.symm,
        lintegral_Ioi_rpow' (by linarith : q - 1 - s < -1) hpos]
      congr 2
      rw [show q - 1 - s + 1 = q - s by ring, show -(q - s) = s - q by ring]
  simp_rw [h2]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x => ?_
  rcases (hG0 x).eq_or_lt with h0 | hpos
  · rw [← h0]
    simp [ENNReal.zero_rpow_of_pos (by linarith : 0 < s), ENNReal.zero_rpow_of_pos (by linarith : 0 < q)]
  · rw [ENNReal.ofReal_rpow_of_nonneg hpos.le (by linarith : 0 ≤ s),
      ENNReal.ofReal_rpow_of_nonneg hpos.le (by linarith : 0 ≤ q),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hpos.le _), ← ENNReal.ofReal_mul (by
        have : 0 < s - q := by linarith
        positivity)]
    congr 1
    rw [mul_comm (1 / (s - q)), mul_div_assoc', ← mul_div_assoc, ← Real.rpow_add hpos]
    congr 2; ring

/-- **Marcinkiewicz, the analytic core.**  If the distribution function of `U` satisfies, for every
`λ > 0`, `|{U > 2λ}| ≤ (c₀/λ) ∫_{G>λ} G + (c₁/λ)^s ∫_{G≤λ} G^s`, then `‖U‖_q ≲ ‖G‖_q` for `1 < q < s`,
with the explicit constant `q 2^q (c₀/(q-1) + c₁^s/(s-q))`. -/
theorem marcinkiewicz_aux {U : ℝ → ℝ} (hUm : Measurable U) (hGm : Measurable G)
    (hU0 : ∀ x, 0 ≤ U x) (hG0 : ∀ x, 0 ≤ G x)
    {q s c₀ c₁ : ℝ} (hq : 1 < q) (hqs : q < s) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hdist : ∀ lam : ℝ, 0 < lam → volume {x | 2 * lam < U x} ≤
      ENNReal.ofReal (c₀ / lam) * (∫⁻ x in {x | lam < G x}, ENNReal.ofReal (G x)) +
        ENNReal.ofReal ((c₁ / lam) ^ s) * (∫⁻ x in {x | G x ≤ lam}, ENNReal.ofReal (G x) ^ s)) :
    ∫⁻ x, ENNReal.ofReal (U x) ^ q ≤
      ENNReal.ofReal (q * 2 ^ q * (c₀ / (q - 1) + c₁ ^ s / (s - q))) *
        ∫⁻ x, ENNReal.ofReal (G x) ^ q := by
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < s := by linarith
  set I₁ : ℝ → ℝ≥0∞ := fun t => ∫⁻ x in {x | t < G x}, ENNReal.ofReal (G x) with hI₁
  set I₂ : ℝ → ℝ≥0∞ := fun t => ∫⁻ x in {x | G x ≤ t}, ENNReal.ofReal (G x) ^ s with hI₂
  have hI₁m : Measurable I₁ := by
    have : I₁ = fun t => ∫⁻ x, (if t < G x then ENNReal.ofReal (G x) else 0) := by
      ext t; simp only [hI₁]
      rw [← lintegral_indicator (measurableSet_lt measurable_const hGm)]
      congr 1
    rw [this]
    refine Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ =>
      if p.1 < G p.2 then ENNReal.ofReal (G p.2) else 0) ?_
    exact Measurable.ite (measurableSet_lt measurable_fst (hGm.comp measurable_snd))
      ((hGm.comp measurable_snd).ennreal_ofReal) measurable_const
  have hI₂m : Measurable I₂ := by
    have : I₂ = fun t => ∫⁻ x, (if G x ≤ t then ENNReal.ofReal (G x) ^ s else 0) := by
      ext t; simp only [hI₂]
      rw [← lintegral_indicator (measurableSet_le hGm measurable_const)]
      congr 1
    rw [this]
    refine Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ =>
      if G p.2 ≤ p.1 then ENNReal.ofReal (G p.2) ^ s else 0) ?_
    exact Measurable.ite (measurableSet_le (hGm.comp measurable_snd) measurable_fst)
      (((hGm.comp measurable_snd).ennreal_ofReal).pow_const _) measurable_const
  -- layer cake for `U / 2`
  have hlc := lintegral_rpow_eq_lintegral_meas_lt_mul (μ := volume) (f := fun x => U x / 2)
    (Eventually.of_forall fun x => by have := hU0 x; positivity) (hUm.div_const 2).aemeasurable hq0
  have hset : ∀ t : ℝ, {a : ℝ | t < U a / 2} = {x | 2 * t < U x} := by
    intro t; ext x; simp only [mem_ofPred_eq]; constructor <;> intro h <;> linarith
  simp_rw [hset] at hlc
  have hbound : ∫⁻ t in Ioi (0 : ℝ), volume {x | 2 * t < U x} * ENNReal.ofReal (t ^ (q - 1)) ≤
      ∫⁻ t in Ioi (0 : ℝ), (ENNReal.ofReal c₀ * (ENNReal.ofReal (t ^ (q - 2)) * I₁ t) +
        ENNReal.ofReal (c₁ ^ s) * (ENNReal.ofReal (t ^ (q - 1 - s)) * I₂ t)) := by
    refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    refine (mul_le_mul' (hdist t ht0) le_rfl).trans (le_of_eq ?_)
    rw [add_mul]
    have e1 : ENNReal.ofReal (c₀ / t) * ENNReal.ofReal (t ^ (q - 1)) =
        ENNReal.ofReal c₀ * ENNReal.ofReal (t ^ (q - 2)) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hc₀]
      congr 1
      rw [div_mul_eq_mul_div, show t ^ (q - 1) = t * t ^ (q - 2) by
        rw [← Real.rpow_one_add' ht0.le (by linarith)]; congr 1; ring]
      field_simp
    have e2 : ENNReal.ofReal ((c₁ / t) ^ s) * ENNReal.ofReal (t ^ (q - 1)) =
        ENNReal.ofReal (c₁ ^ s) * ENNReal.ofReal (t ^ (q - 1 - s)) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hc₁ _)]
      congr 1
      rw [Real.div_rpow hc₁ ht0.le, show t ^ (q - 1 - s) = t ^ (q - 1) / t ^ s by
        rw [Real.rpow_sub ht0]]
      ring
    calc ENNReal.ofReal (c₀ / t) * I₁ t * ENNReal.ofReal (t ^ (q - 1)) +
          ENNReal.ofReal ((c₁ / t) ^ s) * I₂ t * ENNReal.ofReal (t ^ (q - 1))
        = (ENNReal.ofReal (c₀ / t) * ENNReal.ofReal (t ^ (q - 1))) * I₁ t +
          (ENNReal.ofReal ((c₁ / t) ^ s) * ENNReal.ofReal (t ^ (q - 1))) * I₂ t := by ring
      _ = _ := by rw [e1, e2]; ring
  have hsum : ∫⁻ t in Ioi (0 : ℝ), (ENNReal.ofReal c₀ * (ENNReal.ofReal (t ^ (q - 2)) * I₁ t) +
        ENNReal.ofReal (c₁ ^ s) * (ENNReal.ofReal (t ^ (q - 1 - s)) * I₂ t)) =
      ENNReal.ofReal c₀ * (ENNReal.ofReal (1 / (q - 1)) * ∫⁻ x, ENNReal.ofReal (G x) ^ q) +
        ENNReal.ofReal (c₁ ^ s) * (ENNReal.ofReal (1 / (s - q)) * ∫⁻ x, ENNReal.ofReal (G x) ^ q) := by
    have hm1 : Measurable fun t : ℝ => ENNReal.ofReal c₀ * (ENNReal.ofReal (t ^ (q - 2)) * I₁ t) :=
      measurable_const.mul (((measurable_id.pow_const _).ennreal_ofReal).mul hI₁m)
    rw [lintegral_add_left hm1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_tail_mass hGm hG0 hq, lintegral_cutoff_mass hGm hG0 hq hqs]
  -- assemble
  have hU2 : ∀ x, ENNReal.ofReal (U x) ^ q = ENNReal.ofReal (2 ^ q) * ENNReal.ofReal (U x / 2) ^ q := by
    intro x
    have : ENNReal.ofReal (U x) = ENNReal.ofReal 2 * ENNReal.ofReal (U x / 2) := by
      rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
    rw [this, ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
      ENNReal.ofReal_rpow_of_nonneg (by norm_num) hq0.le]
  set J : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (G x) ^ q with hJ
  calc ∫⁻ x, ENNReal.ofReal (U x) ^ q
      = ENNReal.ofReal (2 ^ q) * ∫⁻ x, ENNReal.ofReal (U x / 2) ^ q := by
        simp_rw [hU2]; rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (2 ^ q) * ∫⁻ x, ENNReal.ofReal ((U x / 2) ^ q) := by
        congr 1; refine lintegral_congr fun x => ?_
        rw [ENNReal.ofReal_rpow_of_nonneg (by have := hU0 x; positivity) hq0.le]
    _ = ENNReal.ofReal (2 ^ q) * (ENNReal.ofReal q * ∫⁻ t in Ioi (0 : ℝ),
          volume {x | 2 * t < U x} * ENNReal.ofReal (t ^ (q - 1))) := by rw [hlc]
    _ ≤ ENNReal.ofReal (2 ^ q) * (ENNReal.ofReal q * (ENNReal.ofReal c₀ *
          (ENNReal.ofReal (1 / (q - 1)) * J) + ENNReal.ofReal (c₁ ^ s) *
          (ENNReal.ofReal (1 / (s - q)) * J))) := by
        refine mul_le_mul' le_rfl (mul_le_mul' le_rfl (hbound.trans (le_of_eq hsum)))
    _ = ENNReal.ofReal (q * 2 ^ q * (c₀ / (q - 1) + c₁ ^ s / (s - q))) * J := by
        have hq1 : 0 < q - 1 := by linarith
        have hsq : 0 < s - q := by linarith
        have e : ENNReal.ofReal (2 ^ q) * (ENNReal.ofReal q * (ENNReal.ofReal c₀ *
            (ENNReal.ofReal (1 / (q - 1)) * J) + ENNReal.ofReal (c₁ ^ s) *
            (ENNReal.ofReal (1 / (s - q)) * J))) =
            (ENNReal.ofReal (2 ^ q) * (ENNReal.ofReal q * (ENNReal.ofReal c₀ *
            ENNReal.ofReal (1 / (q - 1)) + ENNReal.ofReal (c₁ ^ s) *
            ENNReal.ofReal (1 / (s - q))))) * J := by ring
        rw [e, ← ENNReal.ofReal_mul hc₀, ← ENNReal.ofReal_mul (Real.rpow_nonneg hc₁ _),
          ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hq0.le,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp
end Fub

end PrimeBHT.TimeFrequency.X2.CZ
