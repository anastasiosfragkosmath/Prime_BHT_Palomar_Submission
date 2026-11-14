module

public import PrimeBHT.U3MaxMod.Chain
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Integral Minkowski inequality in `ℓ²` of a finite set, by duality

If `Ψ(x) = ∫ a(ξ) H(ξ, x) dξ` with `a` integrable and `(∑_{x ∈ X} ‖H ξ x‖²)^{1/2} ≤ K`, then
`(∑_{x ∈ X} ‖Ψ x‖²)^{1/2} ≤ K ∫ ‖a‖`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeBHT.U3MaxMod

theorem l2_integral_le {X : Finset ℤ} (a : ℝ → ℂ) (H : ℝ → ℤ → ℂ) (K : ℝ)
    (ha : Integrable a) (hH : ∀ x ∈ X, Integrable (fun ξ => a ξ * H ξ x))
    (hK : ∀ ξ, ∑ x ∈ X, ‖H ξ x‖ ^ 2 ≤ K ^ 2) (hK0 : 0 ≤ K) :
    Real.sqrt (∑ x ∈ X, ‖∫ ξ, a ξ * H ξ x‖ ^ 2) ≤ K * ∫ ξ, ‖a ξ‖ := by
  set Ψ : ℤ → ℂ := fun x => ∫ ξ, a ξ * H ξ x with hΨ
  set P : ℝ := ∑ x ∈ X, ‖Ψ x‖ ^ 2 with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun x _ => by positivity
  set s : ℝ := Real.sqrt P with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = P := Real.sq_sqrt hP0
  set A : ℝ := ∫ ξ, ‖a ξ‖ with hA
  have hA0 : 0 ≤ A := integral_nonneg fun ξ => norm_nonneg _
  have hPc : (P : ℂ) = ∫ ξ, a ξ * ∑ x ∈ X, H ξ x * conj (Ψ x) := by
    have e1 : (P : ℂ) = ∑ x ∈ X, Ψ x * conj (Ψ x) := by
      rw [hP]; push_cast
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Complex.mul_conj']
    rw [e1]
    have e2 : ∀ x ∈ X, Ψ x * conj (Ψ x) = ∫ ξ, a ξ * H ξ x * conj (Ψ x) := fun x _ => by
      rw [integral_mul_const]
    rw [Finset.sum_congr rfl e2, ← integral_finsetSum _ (fun x hx => (hH x hx).mul_const _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [Finset.mul_sum, mul_assoc]
  have hpt : ∀ ξ, ‖a ξ * ∑ x ∈ X, H ξ x * conj (Ψ x)‖ ≤ ‖a ξ‖ * (K * s) := by
    intro ξ
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h1 : ‖∑ x ∈ X, H ξ x * conj (Ψ x)‖ ≤ ∑ x ∈ X, ‖H ξ x‖ * ‖Ψ x‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      simp
    have h2 : (∑ x ∈ X, ‖H ξ x‖ * ‖Ψ x‖) ^ 2 ≤ (K * s) ^ 2 := by
      calc (∑ x ∈ X, ‖H ξ x‖ * ‖Ψ x‖) ^ 2
          ≤ (∑ x ∈ X, ‖H ξ x‖ ^ 2) * ∑ x ∈ X, ‖Ψ x‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        _ ≤ K ^ 2 * P := mul_le_mul (hK ξ) le_rfl hP0 (sq_nonneg K)
        _ = (K * s) ^ 2 := by rw [mul_pow, hs2]
    exact h1.trans ((pow_le_pow_iff_left₀ (Finset.sum_nonneg fun x _ => by positivity)
      (by positivity) (by norm_num)).1 h2)
  have hint : Integrable (fun ξ => ‖a ξ‖ * (K * s)) := ha.norm.mul_const _
  have hPle : P ≤ A * (K * s) := by
    have : ‖(P : ℂ)‖ = P := by rw [Complex.norm_real, Real.norm_of_nonneg hP0]
    rw [← this, hPc]
    refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hpt)).trans (le_of_eq ?_)
    rw [integral_mul_const]
  rw [← hs2] at hPle
  by_cases hs00 : s = 0
  · rw [hs00]; positivity
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs00)
    have : s * s ≤ (K * A) * s := by nlinarith
    exact le_of_mul_le_mul_right this hspos

end PrimeBHT.U3MaxMod
