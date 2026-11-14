module

public import PrimeBHT.TimeFrequency.Tile.Gram.Pair
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Weighted sums over disjoint intervals (blueprint C4, step 5 (iv))

If the half-open intervals `[l_i, ρ_i)`, `i ∈ Q`, are pairwise disjoint, of length at most `L`, and
lie in `{x : r < |x - c|}`, then
`∑_i (ρ_i - l_i) (1 + |c - m_i|/L)^{-p} ≤ (3/2)^p · 2L (1 + r/L)^{1-p}/(p-1)`,
where `m_i` is the midpoint (Peetre's inequality for the weight, then comparison of the sum with the
integral of the weight over the union).
-/

public section

open MeasureTheory Set

namespace PrimeBHT.TimeFrequency.Tile.Bessel

/-- Peetre for the weight: on an interval of length `≤ L` with midpoint `m` the weight is comparable
to its value at `m`. -/
theorem weight_midpoint_le {c L p x l ρ : ℝ} (hL : 0 < L) (hp : 0 ≤ p) (hlen : ρ - l ≤ L)
    (hx : x ∈ Ico l ρ) :
    (1 + |c - (l + ρ) / 2| / L) ^ (-p) ≤ (3 / 2) ^ p * (1 + |x - c| / L) ^ (-p) := by
  have h1 : |x - c| ≤ |c - (l + ρ) / 2| + L / 2 := by
    have : |x - c| ≤ |x - (l + ρ) / 2| + |(l + ρ) / 2 - c| := abs_sub_le _ _ _
    have h2 : |x - (l + ρ) / 2| ≤ L / 2 := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
    rw [abs_sub_comm c] 
    linarith
  have hA : 0 < 1 + |c - (l + ρ) / 2| / L := by positivity
  have h3 : 1 + |x - c| / L ≤ 3 / 2 * (1 + |c - (l + ρ) / 2| / L) := by
    have : |x - c| / L ≤ |c - (l + ρ) / 2| / L + 1 / 2 := by
      rw [div_le_iff₀ hL]
      have : (|c - (l + ρ) / 2| / L + 1 / 2) * L = |c - (l + ρ) / 2| + L / 2 := by
        field_simp
      linarith
    have h4 : 0 ≤ |c - (l + ρ) / 2| / L := by positivity
    linarith
  have hB : 0 < 1 + |x - c| / L := by positivity
  -- `(1 + |x-c|/L)^p ≤ (3/2)^p (1 + |c-m|/L)^p`
  have h5 : (1 + |x - c| / L) ^ p ≤ (3 / 2 * (1 + |c - (l + ρ) / 2| / L)) ^ p :=
    Real.rpow_le_rpow hB.le h3 hp
  rw [Real.mul_rpow (by norm_num) hA.le] at h5
  rw [Real.rpow_neg hA.le, Real.rpow_neg hB.le]
  have h6 : 0 < (1 + |c - (l + ρ) / 2| / L) ^ p := Real.rpow_pos_of_pos hA _
  have h7 : 0 < (1 + |x - c| / L) ^ p := Real.rpow_pos_of_pos hB _
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ h6 h7]
  linarith [h5]

/-- **Sum over disjoint intervals.** -/
theorem sum_len_mul_weight_le {ι : Type*} (Q : Finset ι) (l ρ : ι → ℝ) {c L r p : ℝ} (hL : 0 < L)
    (hp : 1 < p) (hr : 0 ≤ r) (hlt : ∀ i ∈ Q, l i < ρ i) (hlen : ∀ i ∈ Q, ρ i - l i ≤ L)
    (hdisj : ∀ i ∈ Q, ∀ j ∈ Q, i ≠ j → Disjoint (Ico (l i) (ρ i)) (Ico (l j) (ρ j)))
    (hfar : ∀ i ∈ Q, ∀ x ∈ Ico (l i) (ρ i), r < |x - c|) :
    ∑ i ∈ Q, (ρ i - l i) * (1 + |c - (l i + ρ i) / 2| / L) ^ (-p) ≤
      (3 / 2) ^ p * (2 * L * ((1 + r / L) ^ (1 - p) / (p - 1))) := by
  classical
  set w : ℝ → ℝ := fun x => (1 + |x - c| / L) ^ (-p) with hw
  have hwint : Integrable w := integrable_one_add_abs_sub_div_rpow hp c hL
  have hwnn : ∀ x, 0 ≤ w x := fun x => by positivity
  have hp0 : 0 ≤ p := by linarith
  -- termwise: length × weight at the midpoint ≤ (3/2)^p ∫ over the interval
  have hterm : ∀ i ∈ Q, (ρ i - l i) * (1 + |c - (l i + ρ i) / 2| / L) ^ (-p) ≤
      (3 / 2) ^ p * ∫ x in Ico (l i) (ρ i), w x := by
    intro i hi
    have hint : (ρ i - l i) * ((3 / 2) ^ (-p) * (1 + |c - (l i + ρ i) / 2| / L) ^ (-p)) ≤
        ∫ x in Ico (l i) (ρ i), w x := by
      have h1 : ∫ x in Ico (l i) (ρ i), (3 / 2) ^ (-p) * (1 + |c - (l i + ρ i) / 2| / L) ^ (-p) ≤
          ∫ x in Ico (l i) (ρ i), w x := by
        refine setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Ico])) hwint.integrableOn
          measurableSet_Ico fun x hx => ?_
        have := weight_midpoint_le (c := c) hL hp0 (hlen i hi) hx
        have h3 : (0 : ℝ) < (3 / 2) ^ p := by positivity
        simp only [hw]
        have e : ((3 : ℝ) / 2) ^ (-p) = ((3 / 2) ^ p)⁻¹ := Real.rpow_neg (by norm_num) p
        rw [e, ← div_eq_inv_mul, div_le_iff₀ h3]
        linarith
      rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ico,
        ENNReal.toReal_ofReal (sub_nonneg.2 (hlt i hi).le)] at h1
      exact h1
    have h3 : (0 : ℝ) < (3 / 2) ^ p := by positivity
    have e : ((3 : ℝ) / 2) ^ (-p) = ((3 / 2) ^ p)⁻¹ := Real.rpow_neg (by norm_num) p
    rw [e] at hint
    have : (ρ i - l i) * (1 + |c - (l i + ρ i) / 2| / L) ^ (-p) =
        (3 / 2) ^ p * ((ρ i - l i) * (((3 / 2) ^ p)⁻¹ * (1 + |c - (l i + ρ i) / 2| / L) ^ (-p))) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hint h3.le
  -- the integral over the union
  have hU : ∑ i ∈ Q, ∫ x in Ico (l i) (ρ i), w x = ∫ x in ⋃ i ∈ Q, Ico (l i) (ρ i), w x := by
    rw [integral_biUnion_finset Q (fun i _ => measurableSet_Ico)]
    · intro i hi j hj hij
      exact hdisj i hi j hj hij
    · intro i _
      exact hwint.integrableOn
  have hS : MeasurableSet {x : ℝ | r < |x - c|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hsub : (⋃ i ∈ Q, Ico (l i) (ρ i)) ⊆ {x : ℝ | r < |x - c|} := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
    exact hfar i hi x hxi
  have hle : ∫ x in ⋃ i ∈ Q, Ico (l i) (ρ i), w x ≤ ∫ x in {x : ℝ | r < |x - c|}, w x :=
    setIntegral_mono_set hwint.integrableOn (ae_of_all _ hwnn) (Filter.Eventually.of_forall hsub)
  have htail : ∫ x in {x : ℝ | r < |x - c|}, w x = 2 * L * ((1 + r / L) ^ (1 - p) / (p - 1)) := by
    rw [← integral_indicator hS]
    exact integral_indicator_one_add_abs_sub_div_rpow hp c hL hr
  calc ∑ i ∈ Q, (ρ i - l i) * (1 + |c - (l i + ρ i) / 2| / L) ^ (-p)
      ≤ ∑ i ∈ Q, (3 / 2) ^ p * ∫ x in Ico (l i) (ρ i), w x := Finset.sum_le_sum hterm
    _ = (3 / 2) ^ p * ∑ i ∈ Q, ∫ x in Ico (l i) (ρ i), w x := by rw [Finset.mul_sum]
    _ ≤ (3 / 2) ^ p * (2 * L * ((1 + r / L) ^ (1 - p) / (p - 1))) := by
        rw [hU, ← htail]
        exact mul_le_mul_of_nonneg_left hle (by positivity)

end PrimeBHT.TimeFrequency.Tile.Bessel
