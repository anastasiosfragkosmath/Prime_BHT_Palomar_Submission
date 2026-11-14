module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A geometric (dyadic) summation lemma for the symbol bounds of N25 (b)

`∑_{k = a}^{b} min(2^k s, (2^k s)⁻¹) ≤ 6`, uniformly in `s > 0` and `a, b`.
-/

@[expose] public section

namespace PrimeBHT.KernelFourier

theorem min_le_telescope {x : ℝ} (hx : 0 < x) :
    min x x⁻¹ ≤ 6 / (1 + x) - 6 / (1 + 2 * x) := by
  have h12 : 6 / (1 + x) - 6 / (1 + 2 * x) = 6 * x / ((1 + x) * (1 + 2 * x)) := by
    field_simp; ring
  rw [h12, le_div_iff₀ (by positivity)]
  rcases le_total x 1 with h | h
  · calc min x x⁻¹ * ((1 + x) * (1 + 2 * x)) ≤ x * ((1 + x) * (1 + 2 * x)) := by
          gcongr; exact min_le_left _ _
      _ ≤ x * 6 := by
          apply mul_le_mul_of_nonneg_left _ hx.le
          nlinarith
      _ = 6 * x := by ring
  · calc min x x⁻¹ * ((1 + x) * (1 + 2 * x)) ≤ x⁻¹ * ((1 + x) * (1 + 2 * x)) := by
          gcongr; exact min_le_right _ _
      _ ≤ 6 * x := by rw [inv_mul_le_iff₀ hx]; nlinarith

theorem sum_min_dyadic_le_aux {s : ℝ} (hs : 0 < s) (a : ℕ) : ∀ b : ℕ,
    ∑ k ∈ Finset.Icc a b, min (2 ^ k * s) (2 ^ k * s)⁻¹ ≤ 6 - 6 / (1 + 2 ^ (b + 1) * s) := by
  have hh : ∀ x : ℝ, 0 < x → 6 / (1 + x) ≤ 6 := fun x hx => by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  intro b
  induction b with
  | zero =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · have h1 := min_le_telescope (x := 2 ^ 0 * s) (by positivity)
      have h2 := hh (2 ^ 0 * s) (by positivity)
      simp only [Finset.Icc_self, Finset.sum_singleton, zero_add, pow_zero, one_mul, pow_one] at h1 h2 ⊢
      linarith
    · have : Finset.Icc a 0 = ∅ := Finset.Icc_eq_empty (by omega)
      rw [this, Finset.sum_empty]
      have := hh (2 ^ (0 + 1) * s) (by positivity)
      linarith
  | succ b ih =>
    by_cases hab : a ≤ b + 1
    · rw [Finset.sum_Icc_succ_top hab]
      have h1 := min_le_telescope (x := 2 ^ (b + 1) * s) (by positivity)
      have e : 2 * (2 ^ (b + 1) * s) = 2 ^ (b + 1 + 1) * s := by ring
      rw [e] at h1
      linarith
    · have : Finset.Icc a (b + 1) = ∅ := Finset.Icc_eq_empty (by omega)
      rw [this, Finset.sum_empty]
      have := hh (2 ^ (b + 1 + 1) * s) (by positivity)
      linarith

/-- `∑_{k=a}^{b} min(2^k s, (2^k s)⁻¹) ≤ 6`, uniformly in `a, b` and `s > 0`. -/
theorem sum_min_dyadic_le {s : ℝ} (hs : 0 < s) (a b : ℕ) :
    ∑ k ∈ Finset.Icc a b, min (2 ^ k * s) (2 ^ k * s)⁻¹ ≤ 6 := by
  have := sum_min_dyadic_le_aux hs a b
  have h : 0 < 6 / (1 + 2 ^ (b + 1) * s) := by positivity
  linarith

end PrimeBHT.KernelFourier
