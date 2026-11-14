module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The single-tree estimate in abstract form (blueprint node C3, `TT.tree1`)

For an `i`-tree `T` and `f₁, f₂, f₃ ∈ L²` the blueprint states

`∑_{t ∈ T} |I_t|^{-1/2} ∏_{k=1}^3 |⟨f_k, φ_{t,k}⟩| ≤ |I_T| ∏_{k=1}^3 size_{i,k}(f_k, P_T)`.

The proof is pure Cauchy-Schwarz and is independent of every tile definition. Write
`A k t := |⟨f_k, φ_{t,k}⟩|`, `w t := |I_t|^{-1/2}` and `L := |I_T|`. The only three facts used are

* slot `i` is bounded termwise: `w t * A i t ≤ s i` (`s i = size_{i,i}`, a sup over single tiles);
* slots `k ≠ i` are bounded in `ℓ²`: `∑_{t ∈ T} A k t ^ 2 ≤ s k ^ 2 * L` (`s k = size_{i,k}`, because
  `T` is itself an `i`-tree contained in `P_T`).

## Main results

* `sum_mul_mul_le_sqrt_mul_sqrt` (real, general `ℓ²` budgets `B`, `C`), and
  `sum_mul_mul_le_of_sq_le` (real, budgets `s₂² L` and `s₃² L`);
* `ennreal_sum_mul_mul_le_of_sq_le` (same, in `ℝ≥0∞`);
* `sum_weight_mul_prod_le` and `ennreal_sum_weight_mul_prod_le`: the blueprint form over `Fin 3`,
  for an arbitrary slot `i : Fin 3` bounded termwise (all three slot choices at once).
-/

public section

open Finset
open scoped ENNReal

namespace PrimeBHT.TimeFrequency.Tile

variable {ι : Type*}

/-! ### Real-valued versions -/

/-- Cauchy-Schwarz for a triple sum: one factor bounded termwise by `s₁`, the other two with
`ℓ²`-budgets `B` and `C`. -/
theorem sum_mul_mul_le_sqrt_mul_sqrt (T : Finset ι) {a b c : ι → ℝ} {s₁ B C : ℝ} (hs : 0 ≤ s₁)
    (ha : ∀ t ∈ T, a t ≤ s₁) (hb : ∀ t ∈ T, 0 ≤ b t) (hc : ∀ t ∈ T, 0 ≤ c t)
    (hB : ∑ t ∈ T, b t ^ 2 ≤ B) (hC : ∑ t ∈ T, c t ^ 2 ≤ C) :
    ∑ t ∈ T, a t * b t * c t ≤ s₁ * (√B * √C) := by
  have h1 : ∑ t ∈ T, a t * b t * c t ≤ ∑ t ∈ T, s₁ * (b t * c t) := by
    refine sum_le_sum fun t ht => ?_
    have h2 : 0 ≤ b t * c t := mul_nonneg (hb t ht) (hc t ht)
    calc a t * b t * c t = a t * (b t * c t) := by ring
      _ ≤ s₁ * (b t * c t) := mul_le_mul_of_nonneg_right (ha t ht) h2
  rw [← mul_sum] at h1
  have h3 : ∑ t ∈ T, b t * c t ≤ √B * √C :=
    (Real.sum_mul_le_sqrt_mul_sqrt T b c).trans
      (mul_le_mul (Real.sqrt_le_sqrt hB) (Real.sqrt_le_sqrt hC) (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _))
  exact h1.trans (mul_le_mul_of_nonneg_left h3 hs)

/-- The three-factor estimate with budgets `s₂² L` and `s₃² L`, i.e. the blueprint's C3 after the
substitution `a = w * A i`, `b, c = A k` for `k ≠ i`:
`∑ a b c ≤ s₁ s₂ s₃ L`. -/
theorem sum_mul_mul_le_of_sq_le (T : Finset ι) {a b c : ι → ℝ} {s₁ s₂ s₃ L : ℝ} (hs₁ : 0 ≤ s₁)
    (hs₂ : 0 ≤ s₂) (hs₃ : 0 ≤ s₃) (hL : 0 ≤ L) (ha : ∀ t ∈ T, a t ≤ s₁)
    (hb : ∀ t ∈ T, 0 ≤ b t) (hc : ∀ t ∈ T, 0 ≤ c t)
    (hB : ∑ t ∈ T, b t ^ 2 ≤ s₂ ^ 2 * L) (hC : ∑ t ∈ T, c t ^ 2 ≤ s₃ ^ 2 * L) :
    ∑ t ∈ T, a t * b t * c t ≤ s₁ * s₂ * s₃ * L := by
  refine (sum_mul_mul_le_sqrt_mul_sqrt T hs₁ ha hb hc hB hC).trans (le_of_eq ?_)
  have h2 : √(s₂ ^ 2 * L) = s₂ * √L := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hs₂]
  have h3 : √(s₃ ^ 2 * L) = s₃ * √L := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hs₃]
  have h4 : √L * √L = L := Real.mul_self_sqrt hL
  rw [h2, h3]
  calc s₁ * (s₂ * √L * (s₃ * √L)) = s₁ * s₂ * s₃ * (√L * √L) := by ring
    _ = s₁ * s₂ * s₃ * L := by rw [h4]

/-- The blueprint's C3 over `Fin 3`: for an arbitrary slot `i`, with weights `w` (`|I_t|^{-1/2}`)
and `A k t ≥ 0` (`|⟨f_k, φ_{t,k}⟩|`), if `w t * A i t ≤ s i` termwise and
`∑_t A k t ^ 2 ≤ s k ^ 2 * L` for `k ≠ i`, then
`∑_t w t * ∏_k A k t ≤ L * ∏_k s k`. -/
theorem sum_weight_mul_prod_le (T : Finset ι) (w : ι → ℝ) (A : Fin 3 → ι → ℝ) (s : Fin 3 → ℝ)
    {L : ℝ} (i : Fin 3) (hL : 0 ≤ L) (hs : ∀ k, 0 ≤ s k)
    (hA : ∀ k, ∀ t ∈ T, 0 ≤ A k t) (hi : ∀ t ∈ T, w t * A i t ≤ s i)
    (hk : ∀ k, k ≠ i → ∑ t ∈ T, A k t ^ 2 ≤ s k ^ 2 * L) :
    ∑ t ∈ T, w t * ∏ k, A k t ≤ L * ∏ k, s k := by
  fin_cases i
  · have h := sum_mul_mul_le_of_sq_le T (a := fun t => w t * A 0 t) (b := A 1) (c := A 2)
      (hs 0) (hs 1) (hs 2) hL hi (hA 1) (hA 2)
      (hk 1 (by decide)) (hk 2 (by decide))
    simp only [Fin.prod_univ_three]
    calc ∑ t ∈ T, w t * (A 0 t * A 1 t * A 2 t) = ∑ t ∈ T, w t * A 0 t * A 1 t * A 2 t :=
          sum_congr rfl fun t _ => by ring
      _ ≤ s 0 * s 1 * s 2 * L := h
      _ = L * (s 0 * s 1 * s 2) := by ring
  · have h := sum_mul_mul_le_of_sq_le T (a := fun t => w t * A 1 t) (b := A 0) (c := A 2)
      (hs 1) (hs 0) (hs 2) hL hi (hA 0) (hA 2)
      (hk 0 (by decide)) (hk 2 (by decide))
    simp only [Fin.prod_univ_three]
    calc ∑ t ∈ T, w t * (A 0 t * A 1 t * A 2 t) = ∑ t ∈ T, w t * A 1 t * A 0 t * A 2 t :=
          sum_congr rfl fun t _ => by ring
      _ ≤ s 1 * s 0 * s 2 * L := h
      _ = L * (s 0 * s 1 * s 2) := by ring
  · have h := sum_mul_mul_le_of_sq_le T (a := fun t => w t * A 2 t) (b := A 0) (c := A 1)
      (hs 2) (hs 0) (hs 1) hL hi (hA 0) (hA 1)
      (hk 0 (by decide)) (hk 1 (by decide))
    simp only [Fin.prod_univ_three]
    calc ∑ t ∈ T, w t * (A 0 t * A 1 t * A 2 t) = ∑ t ∈ T, w t * A 2 t * A 0 t * A 1 t :=
          sum_congr rfl fun t _ => by ring
      _ ≤ s 2 * s 0 * s 1 * L := h
      _ = L * (s 0 * s 1 * s 2) := by ring

/-! ### Versions in `ℝ≥0∞` -/

end PrimeBHT.TimeFrequency.Tile
