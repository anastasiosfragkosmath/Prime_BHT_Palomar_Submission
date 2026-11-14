module

public import PrimeBHT.TimeFrequency.X2.CZ.Hormander

/-!
# V08 addendum: the Hörmander integral condition from pointwise Calderón-Zygmund bounds

For a kernel `Φ(x, u)` with `|Φ(x, u)| ≤ 1/|x - u|` and the smoothness bound
`|Φ(x, u) - Φ(x, c)| ≤ |u - c| / |x - u|²` whenever `2|u - c| ≤ |x - u|` (`CZBounds`), the integral
Hörmander condition `∫_{|x - c| > ℓ} |Φ(x, u) - Φ(x, c)| dx ≤ 13` holds for `|u - c| ≤ ℓ/2`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

/-- Pointwise Calderón-Zygmund bounds with constant `1` in the variable `u` (size and smoothness). -/
structure CZBounds (Φ : ℝ → ℝ → ℂ) : Prop where
  size : ∀ x u : ℝ, x ≠ u → ‖Φ x u‖ ≤ 1 / |x - u|
  smooth : ∀ x u c : ℝ, 2 * |u - c| ≤ |x - u| → ‖Φ x u - Φ x c‖ ≤ |u - c| / |x - u| ^ 2

theorem lintegral_tail_inv_sq_shift {ℓ : ℝ} (hℓ : 0 < ℓ) (c : ℝ) :
    ∫⁻ x in {x : ℝ | ℓ < |x - c|}, ENNReal.ofReal (1 / (x - c) ^ 2) = ENNReal.ofReal (2 / ℓ) := by
  have hS0 : MeasurableSet {z : ℝ | ℓ < |z|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hSc : MeasurableSet {x : ℝ | ℓ < |x - c|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (measurable_id.sub_const _))
  rw [← lintegral_tail_inv_sq hℓ, ← lintegral_indicator hSc, ← lintegral_indicator hS0]
  have e : ∀ x, Set.indicator {x : ℝ | ℓ < |x - c|} (fun x => ENNReal.ofReal (1 / (x - c) ^ 2)) x =
      Set.indicator {z : ℝ | ℓ < |z|} (fun z => ENNReal.ofReal (1 / z ^ 2)) (x - c) := by
    intro x
    by_cases hx : ℓ < |x - c|
    · rw [indicator_of_mem (show x ∈ {x : ℝ | ℓ < |x - c|} from hx),
        indicator_of_mem (show x - c ∈ {z : ℝ | ℓ < |z|} from hx)]
    · rw [indicator_of_notMem (show x ∉ {x : ℝ | ℓ < |x - c|} from hx),
        indicator_of_notMem (show x - c ∉ {z : ℝ | ℓ < |z|} from hx)]
  rw [lintegral_congr e]
  exact lintegral_sub_right_eq_self (fun z => Set.indicator {z : ℝ | ℓ < |z|}
    (fun z => ENNReal.ofReal (1 / z ^ 2)) z) c

/-- **Hörmander from CZ bounds**. -/
theorem hH_of_czBounds {Φ : ℝ → ℝ → ℂ} (h : CZBounds Φ) (c u ℓ : ℝ) (hu : |u - c| ≤ ℓ / 2) :
    ∫⁻ x in {x : ℝ | ℓ < |x - c|}, ‖Φ x u - Φ x c‖ₑ ≤ ENNReal.ofReal 13 := by
  have hd0 : 0 ≤ |u - c| := abs_nonneg _
  have hℓ0 : 0 ≤ ℓ := by linarith
  rcases hℓ0.eq_or_lt with hℓ | hℓ
  · subst hℓ
    have : u = c := by
      have : |u - c| = 0 := le_antisymm (by simpa using hu) hd0
      linarith [abs_eq_zero.1 this]
    subst this
    simp
  have hSc : MeasurableSet {x : ℝ | ℓ < |x - c|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (measurable_id.sub_const _))
  set d := |u - c| with hd
  set g1 : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (2 * ℓ) * ENNReal.ofReal (1 / (x - c) ^ 2) with hg1
  set g2 : ℝ → ℝ≥0∞ := Set.indicator (Ioo (c - 3 * ℓ / 2) (c + 3 * ℓ / 2))
    (fun _ => ENNReal.ofReal (3 / ℓ)) with hg2
  have hg2m : Measurable g2 := measurable_const.indicator measurableSet_Ioo
  have hpt : ∀ x ∈ {x : ℝ | ℓ < |x - c|}, ‖Φ x u - Φ x c‖ₑ ≤ g1 x + g2 x := by
    intro x hx
    have hx' : ℓ < |x - c| := hx
    have hxu : ℓ / 2 < |x - u| := by
      have : |x - c| ≤ |x - u| + |u - c| := by
        calc |x - c| = |(x - u) + (u - c)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      linarith
    have hxu0 : x ≠ u := by
      intro h0; rw [h0, sub_self, abs_zero] at hxu; linarith
    have hxc0 : x ≠ c := by
      intro h0; rw [h0, sub_self, abs_zero] at hx'; linarith
    by_cases hA : 2 * d ≤ |x - u|
    · -- smoothness region
      have hs := h.smooth x u c hA
      have h4 : |x - c| ≤ 2 * |x - u| := by
        have : |x - c| ≤ |x - u| + |u - c| := by
          calc |x - c| = |(x - u) + (u - c)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
        linarith
      have hxu_pos : 0 < |x - u| := abs_pos.2 (sub_ne_zero.2 hxu0)
      have hxc_pos : 0 < |x - c| := abs_pos.2 (sub_ne_zero.2 hxc0)
      have h5 : d / |x - u| ^ 2 ≤ 2 * ℓ * (1 / (x - c) ^ 2) := by
        have hsq : (x - c) ^ 2 = |x - c| ^ 2 := (sq_abs _).symm
        rw [hsq]
        have h6 : |x - c| ^ 2 ≤ 4 * |x - u| ^ 2 := by nlinarith
        rw [div_le_iff₀ (by positivity)]
        have : 2 * ℓ * (1 / |x - c| ^ 2) * |x - u| ^ 2 ≥ 2 * ℓ * (1 / (4 * |x - u| ^ 2)) * |x - u| ^ 2 := by
          gcongr
        calc d = 2 * ℓ * (1 / (4 * |x - u| ^ 2)) * |x - u| ^ 2 * (2 * d / ℓ) := by
              field_simp; ring
          _ ≤ 2 * ℓ * (1 / (4 * |x - u| ^ 2)) * |x - u| ^ 2 * 1 := by
              gcongr
              rw [div_le_one hℓ]; linarith
          _ ≤ _ := by linarith
      calc ‖Φ x u - Φ x c‖ₑ ≤ ENNReal.ofReal (2 * ℓ * (1 / (x - c) ^ 2)) := by
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hs.trans h5)
        _ = g1 x := by rw [hg1, ENNReal.ofReal_mul (by positivity)]
        _ ≤ g1 x + g2 x := le_self_add
    · -- near region
      push Not at hA
      have hxc_lt : |x - c| < 3 * ℓ / 2 := by
        have : |x - c| ≤ |x - u| + |u - c| := by
          calc |x - c| = |(x - u) + (u - c)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
        linarith
      have hxI : x ∈ Ioo (c - 3 * ℓ / 2) (c + 3 * ℓ / 2) := by
        rw [abs_lt] at hxc_lt
        constructor <;> linarith [hxc_lt.1, hxc_lt.2]
      have hsz1 := h.size x u hxu0
      have hsz2 := h.size x c hxc0
      have hxu_pos : 0 < |x - u| := abs_pos.2 (sub_ne_zero.2 hxu0)
      have hxc_pos : 0 < |x - c| := abs_pos.2 (sub_ne_zero.2 hxc0)
      have e1 : 1 / |x - u| ≤ 2 / ℓ := by
        rw [div_le_div_iff₀ hxu_pos hℓ]; linarith
      have e2 : 1 / |x - c| ≤ 1 / ℓ := one_div_le_one_div_of_le hℓ hx'.le
      calc ‖Φ x u - Φ x c‖ₑ ≤ ENNReal.ofReal (3 / ℓ) := by
            rw [← ofReal_norm]
            refine ENNReal.ofReal_le_ofReal ((norm_sub_le _ _).trans ?_)
            have : 3 / ℓ = 2 / ℓ + 1 / ℓ := by ring
            linarith
        _ = g2 x := by rw [hg2, indicator_of_mem hxI]
        _ ≤ g1 x + g2 x := le_add_self
  calc ∫⁻ x in {x : ℝ | ℓ < |x - c|}, ‖Φ x u - Φ x c‖ₑ
      ≤ ∫⁻ x in {x : ℝ | ℓ < |x - c|}, (g1 x + g2 x) := setLIntegral_mono' hSc hpt
    _ = (∫⁻ x in {x : ℝ | ℓ < |x - c|}, g1 x) + (∫⁻ x in {x : ℝ | ℓ < |x - c|}, g2 x) :=
        lintegral_add_right _ hg2m
    _ ≤ ENNReal.ofReal 4 + ENNReal.ofReal 9 := by
        refine add_le_add ?_ ?_
        · rw [hg1]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_tail_inv_sq_shift hℓ c,
            ← ENNReal.ofReal_mul (by positivity)]
          refine le_of_eq ?_
          congr 1; field_simp; norm_num
        · calc ∫⁻ x in {x : ℝ | ℓ < |x - c|}, g2 x ≤ ∫⁻ x, g2 x := setLIntegral_le_lintegral _ _
            _ = ENNReal.ofReal (3 / ℓ) * volume (Ioo (c - 3 * ℓ / 2) (c + 3 * ℓ / 2)) := by
                rw [hg2, lintegral_indicator measurableSet_Ioo, setLIntegral_const]
            _ = ENNReal.ofReal 9 := by
                rw [Real.volume_Ioo, ← ENNReal.ofReal_mul (by positivity)]
                congr 1; field_simp; ring
    _ = ENNReal.ofReal 13 := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num

end PrimeBHT.TimeFrequency.X2.CZ
