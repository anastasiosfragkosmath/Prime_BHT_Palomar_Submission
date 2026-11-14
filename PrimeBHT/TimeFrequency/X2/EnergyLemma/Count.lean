module

public import PrimeBHT.TimeFrequency.X2.EnergyLemma.Defs

/-!
# X2, node V12: the count (DPLMV L1347-1366, HLC energy lemma)

From `pint` for a strongly disjoint family with `topNorm ≥ ε`, `ε ≤ C₀`, to the count
`(∑ |I_t|) ε^q ≤ C' ‖F‖_{qX}^{qX}` (`q = qX/α`): the case split "first term dominates / second term dominates".
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- The real-variable case analysis. -/
theorem count_real {p q α C C₀ ε x a : ℝ} (hp : 0 < p) (hpq : p < q) (hα : α = p / q) (hε : 0 < ε)
    (hεC : ε ≤ C₀) (hx : 0 ≤ x) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (h : ε ^ p * x ≤ C * (a + x ^ (1 - α) * a ^ α)) :
    ε ^ q * x ≤ (2 * C * C₀ ^ (q - p) + (2 * C) ^ (1 / α)) * a := by
  have hq : 0 < q := by linarith
  have hα0 : 0 < α := by rw [hα]; positivity
  have hα1 : α < 1 := by rw [hα, div_lt_one hq]; exact hpq
  have hC₀ : 0 ≤ C₀ := hε.le.trans hεC
  have hK : 0 ≤ (2 * C) ^ (1 / α) * a := mul_nonneg (Real.rpow_nonneg (by positivity) _) ha
  rcases hx.eq_or_lt with hx0 | hxpos
  · rw [← hx0, mul_zero]
    have : 0 ≤ 2 * C * C₀ ^ (q - p) * a := by positivity
    nlinarith
  have hrq : ε ^ q = ε ^ (q - p) * ε ^ p := by
    rw [← Real.rpow_add hε]; ring_nf
  by_cases hcase : x ^ (1 - α) * a ^ α ≤ a
  · have h1 : ε ^ p * x ≤ 2 * C * a := by
      calc ε ^ p * x ≤ C * (a + x ^ (1 - α) * a ^ α) := h
        _ ≤ C * (a + a) := mul_le_mul_of_nonneg_left (by linarith) hC
        _ = 2 * C * a := by ring
    have h3 : ε ^ (q - p) ≤ C₀ ^ (q - p) := Real.rpow_le_rpow hε.le hεC (by linarith)
    calc ε ^ q * x = ε ^ (q - p) * (ε ^ p * x) := by rw [hrq]; ring
      _ ≤ C₀ ^ (q - p) * (2 * C * a) :=
          mul_le_mul h3 h1 (by positivity) (by positivity)
      _ ≤ (2 * C * C₀ ^ (q - p) + (2 * C) ^ (1 / α)) * a := by nlinarith
  · push Not at hcase
    have hy : 0 < x ^ (1 - α) * a ^ α := lt_of_le_of_lt ha hcase
    have hx1 : 0 < x ^ (1 - α) := Real.rpow_pos_of_pos hxpos _
    have h1 : ε ^ p * x ≤ 2 * C * (x ^ (1 - α) * a ^ α) := by
      calc ε ^ p * x ≤ C * (a + x ^ (1 - α) * a ^ α) := h
        _ ≤ C * (x ^ (1 - α) * a ^ α + x ^ (1 - α) * a ^ α) :=
            mul_le_mul_of_nonneg_left (by linarith) hC
        _ = 2 * C * (x ^ (1 - α) * a ^ α) := by ring
    have hsplit : x = x ^ (1 - α) * x ^ α := by
      rw [← Real.rpow_add hxpos]; simp
    have h2 : ε ^ p * x ^ α ≤ 2 * C * a ^ α := by
      refine le_of_mul_le_mul_left ?_ hx1
      calc x ^ (1 - α) * (ε ^ p * x ^ α) = ε ^ p * (x ^ (1 - α) * x ^ α) := by ring
        _ = ε ^ p * x := by rw [← hsplit]
        _ ≤ 2 * C * (x ^ (1 - α) * a ^ α) := h1
        _ = x ^ (1 - α) * (2 * C * a ^ α) := by ring
    have hαinv : 0 ≤ 1 / α := by positivity
    have h3 := Real.rpow_le_rpow (by positivity) h2 hαinv
    have hpa : p * (1 / α) = q := by rw [hα]; field_simp
    have hαα : α * (1 / α) = 1 := by field_simp
    rw [Real.mul_rpow (Real.rpow_nonneg hε.le _) (Real.rpow_nonneg hxpos.le _), ← Real.rpow_mul hε.le,
      ← Real.rpow_mul hxpos.le, hpa, hαα, Real.rpow_one,
      Real.mul_rpow (by positivity) (Real.rpow_nonneg ha _), ← Real.rpow_mul ha, hαα,
      Real.rpow_one] at h3
    have : 0 ≤ 2 * C * C₀ ^ (q - p) * a := by positivity
    nlinarith

/-- From a `pint`-type inequality to the count, in `ℝ≥0∞`. -/
theorem count_family {p q α C C₀ ε : ℝ} (hp : 0 < p) (hpq : p < q) (hα : α = p / q) (hC : 0 ≤ C)
    (hε : 0 < ε) (hεC : ε ≤ C₀) (𝒯 : List (Finset TriTile × Top)) (G : Finset TriTile → Top → ℝ≥0∞)
    (A : ℝ≥0∞) (hlow : ∀ T ∈ 𝒯, ENNReal.ofReal ε ≤ G T.1 T.2)
    (hP : (𝒯.map (fun T => ENNReal.ofReal ((2 : ℝ) ^ T.2.1.1) * G T.1 T.2 ^ p)).sum ≤
      ENNReal.ofReal C * (A + (ENNReal.ofReal ((1 : ℝ) ^ p) * topSum 𝒯) ^ (1 - α) * A ^ α)) :
    topSum 𝒯 * ENNReal.ofReal (ε ^ q) ≤
      ENNReal.ofReal (2 * C * C₀ ^ (q - p) + (2 * C) ^ (1 / α) + 1) * A := by
  have hq : 0 < q := by linarith
  have hα0 : 0 < α := by rw [hα]; positivity
  have hα1 : α < 1 := by rw [hα, div_lt_one hq]; exact hpq
  have hC₀ : 0 ≤ C₀ := hε.le.trans hεC
  have hK : 0 ≤ 2 * C * C₀ ^ (q - p) + (2 * C) ^ (1 / α) := by positivity
  by_cases hA : A = ⊤
  · rw [hA, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by linarith)).ne']
    exact le_top
  -- the lower bound of the left side
  have hlow' : topSum 𝒯 * ENNReal.ofReal ε ^ p ≤
      (𝒯.map (fun T => ENNReal.ofReal ((2 : ℝ) ^ T.2.1.1) * G T.1 T.2 ^ p)).sum := by
    have h1 : (𝒯.map (fun T => ENNReal.ofReal ((2 : ℝ) ^ T.2.1.1) * ENNReal.ofReal ε ^ p)).sum ≤
        (𝒯.map (fun T => ENNReal.ofReal ((2 : ℝ) ^ T.2.1.1) * G T.1 T.2 ^ p)).sum :=
      List.sum_le_sum fun T hT => by
        gcongr
        exact hlow T hT
    refine le_trans (le_of_eq ?_) h1
    unfold topSum
    rw [List.sum_map_mul_right]
  have h2 := hlow'.trans hP
  set x := (topSum 𝒯).toReal with hx
  set a := A.toReal with ha
  have hx0 : 0 ≤ x := ENNReal.toReal_nonneg
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hxe : topSum 𝒯 = ENNReal.ofReal x := (ENNReal.ofReal_toReal (topSum_ne_top 𝒯)).symm
  have hae : A = ENNReal.ofReal a := (ENNReal.ofReal_toReal hA).symm
  have hαp : 0 ≤ α := hα0.le
  have h1α : 0 ≤ 1 - α := by linarith
  rw [hxe, ENNReal.ofReal_rpow_of_nonneg hε.le hp.le, ← ENNReal.ofReal_mul hx0] at h2
  rw [hae] at h2
  rw [hxe, hae]
  rw [ENNReal.ofReal_rpow_of_nonneg ha0 hαp,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 ^ p),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) h1α, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add ha0 (by positivity), ← ENNReal.ofReal_mul hC] at h2
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  have h3 := count_real hp hpq hα hε hεC hx0 ha0 hC (by rw [mul_comm] at h2; simpa using h2)
  rw [← ENNReal.ofReal_mul hx0, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith

end PrimeBHT.TimeFrequency.X2
