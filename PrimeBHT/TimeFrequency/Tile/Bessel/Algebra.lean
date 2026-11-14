module

public import PrimeBHT.TimeFrequency.Tile.Gram.Pair
public import PrimeBHT.TimeFrequency.Tile.Bessel.Cauchy
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Bookkeeping for the double sum of the weak Bessel inequality (blueprint C4, steps 3-4)

Splitting a symmetric double sum over tiles by comparing scales, and the same-scale estimate
`∑_t ∑_{t' : s(t') = s(t)} |a_t| |a_{t'}| |⟨φ_t, φ_{t'}⟩| ≤ C ∑_t |a_t|²` from (G3).
-/

public section

open MeasureTheory
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Tile.Bessel

/-- A symmetric double sum over tiles splits as twice the part with `s(t') < s(t)` plus the part
with `s(t') = s(t)`. -/
theorem double_sum_split (U : Finset (ℤ × ℤ × ℤ)) (F : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) → ℝ)
    (hF : ∀ t t', F t t' = F t' t) :
    ∑ t ∈ U, ∑ t' ∈ U, F t t' =
      2 * ∑ t ∈ U, ∑ t' ∈ U with t'.1 < t.1, F t t' +
        ∑ t ∈ U, ∑ t' ∈ U with t'.1 = t.1, F t t' := by
  classical
  have h1 : ∀ t ∈ U, ∑ t' ∈ U, F t t' = (∑ t' ∈ U with t'.1 < t.1, F t t') +
      (∑ t' ∈ U with t'.1 = t.1, F t t') + ∑ t' ∈ U, (if t.1 < t'.1 then F t t' else 0) := by
    intro t _
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t' _ => ?_
    rcases lt_trichotomy t'.1 t.1 with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h2 : ∑ t ∈ U, ∑ t' ∈ U, (if t.1 < t'.1 then F t t' else 0) =
      ∑ t ∈ U, ∑ t' ∈ U with t'.1 < t.1, F t t' := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun t' _ => ?_
    rw [hF t' t]
  rw [h2]
  ring

/-- Exchanging the order of summation in a same-scale double sum. -/
theorem double_sum_comm_scale (U : Finset (ℤ × ℤ × ℤ)) (F : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) → ℝ) :
    ∑ t ∈ U, ∑ t' ∈ U with t'.1 = t.1, F t t' =
      ∑ t' ∈ U, ∑ t ∈ U with t.1 = t'.1, F t t' := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => if_congr eq_comm rfl rfl

/-- **Same-scale pairs** (steps 3 of C4): from (G3),
`∑_t ∑_{t' ∈ U, s(t') = s(t)} a_t a_{t'} |⟨φ_t, φ_{t'}⟩| ≤ C₃ ∑_t a_t²`. -/
theorem sum_sameScale_le {N : ℕ} (hN : 3 ≤ N) {a b s' α : ℤ} (k : Fin 3)
    (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (P : Finset (ℤ × ℤ × ℤ)) (hP : ∀ t ∈ P, t ∈ triIdx s' α)
    (hφ : ∀ t ∈ P, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k))
    {U : Finset (ℤ × ℤ × ℤ)} (hUP : U ⊆ P) (A : ℤ × ℤ × ℤ → ℝ) :
    ∑ t ∈ U, ∑ t' ∈ U with t'.1 = t.1, A t * A t' * ‖pairing (φ t k) (φ t' k)‖ ≤
      sameScaleConst N * ∑ t ∈ U, A t ^ 2 := by
  classical
  set G : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) → ℝ := fun t t' => ‖pairing (φ t k) (φ t' k)‖ with hG
  have hG0 : ∀ t t', 0 ≤ G t t' := fun _ _ => norm_nonneg _
  have hGs : ∀ t t', G t t' = G t' t := fun t t' => by
    simp only [hG]; exact norm_pairing_comm _ _
  -- row sums
  have hrow : ∀ t ∈ U, ∑ t' ∈ U with t'.1 = t.1, G t t' ≤ sameScaleConst N := by
    intro t ht
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hG0 _ _))
      (sum_norm_pairing_sameScale_le hN k φ P hP hφ (hUP ht))
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hUP hx.1, hx.2⟩
  calc ∑ t ∈ U, ∑ t' ∈ U with t'.1 = t.1, A t * A t' * G t t'
      ≤ ∑ t ∈ U, ∑ t' ∈ U with t'.1 = t.1, ((A t ^ 2 * G t t') / 2 + (A t' ^ 2 * G t t') / 2) := by
        refine Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun t' _ => ?_
        have := hG0 t t'
        nlinarith [sq_nonneg (A t - A t'), mul_nonneg (sq_nonneg (A t - A t')) this]
    _ = (∑ t ∈ U, A t ^ 2 * ∑ t' ∈ U with t'.1 = t.1, G t t') / 2 +
        (∑ t ∈ U, ∑ t' ∈ U with t'.1 = t.1, A t' ^ 2 * G t t') / 2 := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_div, Finset.mul_sum]
    _ ≤ (∑ t ∈ U, A t ^ 2 * sameScaleConst N) / 2 +
        (∑ t' ∈ U, A t' ^ 2 * sameScaleConst N) / 2 := by
        have e1 : ∑ t ∈ U, A t ^ 2 * ∑ t' ∈ U with t'.1 = t.1, G t t' ≤
            ∑ t ∈ U, A t ^ 2 * sameScaleConst N :=
          Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (hrow t ht) (sq_nonneg _)
        have e2 : ∑ t ∈ U, ∑ t' ∈ U with t'.1 = t.1, A t' ^ 2 * G t t' ≤
            ∑ t' ∈ U, A t' ^ 2 * sameScaleConst N := by
          rw [double_sum_comm_scale U (fun t t' => A t' ^ 2 * G t t')]
          refine Finset.sum_le_sum fun t' ht' => ?_
          rw [← Finset.mul_sum]
          have : ∑ t ∈ U with t.1 = t'.1, G t t' = ∑ t ∈ U with t.1 = t'.1, G t' t :=
            Finset.sum_congr rfl fun t _ => hGs t t'
          rw [this]
          exact mul_le_mul_of_nonneg_left (hrow t' ht') (sq_nonneg _)
        linarith
    _ = sameScaleConst N * ∑ t ∈ U, A t ^ 2 := by
        rw [← Finset.sum_mul]
        ring

end PrimeBHT.TimeFrequency.Tile.Bessel
