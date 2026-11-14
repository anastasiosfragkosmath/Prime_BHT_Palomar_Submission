module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Exponent bookkeeping for the tile core (blueprint node C10, steps C10a.5 and C10b.3-4)

Pure real arithmetic behind the restricted-type proposition. Throughout `x = |E₁|^{1/2} ∈ (0, 1]`.

* `sum_range_min_geom_le` (C10b, steps 3-4): for `N ≥ 3`,
  `∑_{d<D} min(2^{-(N-2)d}, x 2^d) ≤ 4 x^{1 - 1/(N-1)}` for every `D`, hence also for the full series
  (`tsum_min_geom_le`); the constant `4` does not depend on `N`.
* `sum_range_min_two_pow_le` (C10a, step 5): `∑_{ℓ<L} min(x, 2^{-ℓ}) ≤ x (log₂(1/x) + 3)`.
* `mul_logb_add_three_le`: `x (log₂(1/x) + 3) ≤ (3 + 1/ε) x^{1-2ε}`, i.e. `C_ε |E₁|^{1/2-ε}`.
* `rpow_one_sub_inv_le`: `x^{1-1/(N-1)} ≤ x^{1-2ε}` as soon as `1/(2ε) ≤ N - 1`, with the
  `N_ε = ⌈1/(2ε)⌉ + 11` version `natCeil_inv_le_sub_one`.
* Versions in the variable `E = |E₁|` (`x = E^{1/2}`): `sum_range_min_sqrt_geom_le`,
  `sum_range_min_sqrt_two_pow_le`.
-/

public section

open Finset

namespace PrimeBHT.TimeFrequency.Tile

/-! ### The two-geometric-series minimum (C10b, step 3) -/

/-- **`geom_min_sum`.** For `N ≥ 3`, `0 < x ≤ 1` and every `D`,
`∑_{d<D} min(2^{-(N-2)d}, x 2^d) ≤ 4 x^{1 - 1/(N-1)}`. -/
theorem sum_range_min_geom_le {N x : ℝ} (hN : 3 ≤ N) (hx0 : 0 < x) (hx1 : x ≤ 1) (D : ℕ) :
    ∑ d ∈ range D, min ((2 : ℝ) ^ (-(N - 2) * (d : ℝ))) (x * 2 ^ d) ≤
      4 * x ^ (1 - 1 / (N - 1)) := by
  have hN1 : 0 < N - 1 := by linarith
  have hr1 : 1 ≤ N - 2 := by linarith
  set κ : ℝ := 1 / (N - 1) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set ρ : ℝ := x ^ (-κ) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hx0 _
  have hρ1 : 1 ≤ ρ := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx0 hx1 (by linarith)
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near hρ1 (one_lt_two : (1 : ℝ) < 2)
  set θ : ℝ := (2 : ℝ) ^ (-(N - 2)) with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 / 2 := by
    calc θ ≤ (2 : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 2 := by norm_num
  have hθpow : ∀ d : ℕ, (2 : ℝ) ^ (-(N - 2) * (d : ℝ)) = θ ^ d := by
    intro d
    rw [hθ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have hg : ∀ d ∈ range D, 0 ≤ min ((2 : ℝ) ^ (-(N - 2) * (d : ℝ))) (x * 2 ^ d) :=
    fun d _ => le_min (by positivity) (by positivity)
  have hsub : range D ⊆ range (k + 1) ∪ Ico (k + 1) D := by
    intro d hd
    rw [mem_union, mem_range, mem_Ico]
    rw [mem_range] at hd
    by_cases h : d < k + 1
    · exact Or.inl h
    · exact Or.inr ⟨not_lt.mp h, hd⟩
  have hdisj : Disjoint (range (k + 1)) (Ico (k + 1) D) := by
    rw [disjoint_left]
    intro d hd hd'
    rw [mem_range] at hd
    rw [mem_Ico] at hd'
    omega
  -- first piece
  have P1 : ∑ d ∈ range (k + 1), min ((2 : ℝ) ^ (-(N - 2) * (d : ℝ))) (x * 2 ^ d) ≤ 2 * x * ρ := by
    calc ∑ d ∈ range (k + 1), min ((2 : ℝ) ^ (-(N - 2) * (d : ℝ))) (x * 2 ^ d)
        ≤ ∑ d ∈ range (k + 1), x * 2 ^ d := sum_le_sum fun d _ => min_le_right _ _
      _ = x * ∑ d ∈ range (k + 1), (2 : ℝ) ^ d := by rw [mul_sum]
      _ = x * (2 ^ (k + 1) - 1) := by
          rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
          norm_num
      _ ≤ x * (2 * 2 ^ k) := by
          refine mul_le_mul_of_nonneg_left ?_ hx0.le
          rw [pow_succ]
          linarith
      _ ≤ x * (2 * ρ) := by
          refine mul_le_mul_of_nonneg_left ?_ hx0.le
          linarith
      _ = 2 * x * ρ := by ring
  -- second piece
  have P2 : ∑ d ∈ Ico (k + 1) D, min ((2 : ℝ) ^ (-(N - 2) * (d : ℝ))) (x * 2 ^ d) ≤
      2 * ρ ^ (-(N - 2)) := by
    have h1 : ∑ d ∈ Ico (k + 1) D, min ((2 : ℝ) ^ (-(N - 2) * (d : ℝ))) (x * 2 ^ d) ≤
        ∑ d ∈ Ico (k + 1) D, θ ^ d :=
      sum_le_sum fun d _ => (min_le_left _ _).trans_eq (hθpow d)
    have h2 : ∑ d ∈ Ico (k + 1) D, θ ^ d ≤ θ ^ (k + 1) / (1 - θ) :=
      geom_sum_Ico_le_of_lt_one hθ0.le (by linarith)
    have h3 : θ ^ (k + 1) / (1 - θ) ≤ 2 * θ ^ (k + 1) := by
      rw [div_le_iff₀ (by linarith)]
      have : 0 ≤ θ ^ (k + 1) := by positivity
      nlinarith
    have h4 : θ ^ (k + 1) ≤ ρ ^ (-(N - 2)) := by
      rw [hθ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      have : (2 : ℝ) ^ ((k + 1 : ℕ) : ℝ) = 2 ^ (k + 1) := by
        rw [Real.rpow_natCast]
      calc (2 : ℝ) ^ (-(N - 2) * ((k + 1 : ℕ) : ℝ)) = ((2 : ℝ) ^ ((k + 1 : ℕ) : ℝ)) ^ (-(N - 2)) := by
            rw [← Real.rpow_mul (by norm_num), mul_comm]
        _ = ((2 : ℝ) ^ (k + 1)) ^ (-(N - 2)) := by rw [this]
        _ ≤ ρ ^ (-(N - 2)) :=
            Real.rpow_le_rpow_of_nonpos hρ0 hk2.le (by linarith)
    linarith
  have hE1 : x * ρ = x ^ (1 - κ) := by
    rw [hρ, sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
  have hE2 : ρ ^ (-(N - 2)) = x ^ (1 - κ) := by
    rw [hρ, ← Real.rpow_mul hx0.le]
    congr 1
    rw [hκ]
    field_simp
    ring
  calc ∑ d ∈ range D, min ((2 : ℝ) ^ (-(N - 2) * (d : ℝ))) (x * 2 ^ d)
      ≤ ∑ d ∈ range (k + 1) ∪ Ico (k + 1) D,
          min ((2 : ℝ) ^ (-(N - 2) * (d : ℝ))) (x * 2 ^ d) :=
        sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => by positivity
    _ = ∑ d ∈ range (k + 1), min ((2 : ℝ) ^ (-(N - 2) * (d : ℝ))) (x * 2 ^ d) +
        ∑ d ∈ Ico (k + 1) D, min ((2 : ℝ) ^ (-(N - 2) * (d : ℝ))) (x * 2 ^ d) :=
        sum_union hdisj
    _ ≤ 2 * x * ρ + 2 * ρ ^ (-(N - 2)) := add_le_add P1 P2
    _ = 4 * x ^ (1 - κ) := by rw [mul_assoc, hE1, hE2]; ring

/-! ### The sum outside the exceptional set (C10a, step 5) -/

/-- **C10a, step 5.** For `0 < x ≤ 1` and every `L`,
`∑_{ℓ<L} min(x, 2^{-ℓ}) ≤ x (log₂(1/x) + 3)`. -/
theorem sum_range_min_two_pow_le {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (L : ℕ) :
    ∑ ℓ ∈ range L, min x ((1 / 2 : ℝ) ^ ℓ) ≤ x * (Real.logb 2 (1 / x) + 3) := by
  have hx1' : 1 ≤ 1 / x := by rw [le_div_iff₀ hx0]; linarith
  have hlb0 : 0 ≤ Real.logb 2 (1 / x) := Real.logb_nonneg (by norm_num) hx1'
  set k : ℕ := ⌈Real.logb 2 (1 / x)⌉₊ with hk
  have hk1 : 1 / x ≤ 2 ^ k := by
    have h1 : Real.logb 2 (1 / x) ≤ k := Nat.le_ceil _
    have h2 := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (by positivity)).mp h1
    rwa [Real.rpow_natCast] at h2
  have hk2 : (k : ℝ) < Real.logb 2 (1 / x) + 1 := Nat.ceil_lt_add_one hlb0
  have hpowk : (1 / 2 : ℝ) ^ k ≤ x := by
    rw [one_div, inv_pow]
    have h2k : 0 < (2 : ℝ) ^ k := by positivity
    rw [inv_le_comm₀ h2k hx0]
    simpa [one_div] using hk1
  have hsub : range L ⊆ range (k + 1) ∪ Ico (k + 1) L := by
    intro d hd
    rw [mem_union, mem_range, mem_Ico]
    rw [mem_range] at hd
    by_cases h : d < k + 1
    · exact Or.inl h
    · exact Or.inr ⟨not_lt.mp h, hd⟩
  have hdisj : Disjoint (range (k + 1)) (Ico (k + 1) L) := by
    rw [disjoint_left]
    intro d hd hd'
    rw [mem_range] at hd
    rw [mem_Ico] at hd'
    omega
  have P1 : ∑ ℓ ∈ range (k + 1), min x ((1 / 2 : ℝ) ^ ℓ) ≤ (k + 1) * x := by
    calc ∑ ℓ ∈ range (k + 1), min x ((1 / 2 : ℝ) ^ ℓ) ≤ ∑ ℓ ∈ range (k + 1), x :=
          sum_le_sum fun ℓ _ => min_le_left _ _
      _ = (k + 1) * x := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  have P2 : ∑ ℓ ∈ Ico (k + 1) L, min x ((1 / 2 : ℝ) ^ ℓ) ≤ x := by
    have h1 : ∑ ℓ ∈ Ico (k + 1) L, min x ((1 / 2 : ℝ) ^ ℓ) ≤ ∑ ℓ ∈ Ico (k + 1) L, (1 / 2 : ℝ) ^ ℓ :=
      sum_le_sum fun ℓ _ => min_le_right _ _
    have h2 : ∑ ℓ ∈ Ico (k + 1) L, (1 / 2 : ℝ) ^ ℓ ≤ (1 / 2 : ℝ) ^ (k + 1) / (1 - 1 / 2) :=
      geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
    have h3 : (1 / 2 : ℝ) ^ (k + 1) / (1 - 1 / 2) = (1 / 2 : ℝ) ^ k := by
      rw [pow_succ]; ring
    linarith
  calc ∑ ℓ ∈ range L, min x ((1 / 2 : ℝ) ^ ℓ)
      ≤ ∑ ℓ ∈ range (k + 1) ∪ Ico (k + 1) L, min x ((1 / 2 : ℝ) ^ ℓ) :=
        sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => le_min hx0.le (by positivity)
    _ = ∑ ℓ ∈ range (k + 1), min x ((1 / 2 : ℝ) ^ ℓ) + ∑ ℓ ∈ Ico (k + 1) L, min x ((1 / 2 : ℝ) ^ ℓ) :=
        sum_union hdisj
    _ ≤ (k + 1) * x + x := add_le_add P1 P2
    _ ≤ x * (Real.logb 2 (1 / x) + 3) := by nlinarith

/-! ### From `x (log₂(1/x) + 3)` to a power of `x` -/

/-- `x (log₂(1/x) + 3) ≤ (3 + 1/ε) x^{1-2ε}` for `0 < x ≤ 1`, `ε > 0`; with `x = |E₁|^{1/2}`
this is `C_ε |E₁|^{1/2-ε}`, `C_ε = 3 + 1/ε`. -/
theorem mul_logb_add_three_le {x ε : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hε : 0 < ε) :
    x * (Real.logb 2 (1 / x) + 3) ≤ (3 + 1 / ε) * x ^ (1 - 2 * ε) := by
  have h2ε : 0 < 2 * ε := by positivity
  set a : ℝ := x ^ (2 * ε) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hx0 _
  have ha1 : a ≤ 1 := Real.rpow_le_one hx0.le hx1 h2ε.le
  have hxe : x = x ^ (1 - 2 * ε) * a := by
    rw [ha, ← Real.rpow_add hx0]
    simp
  have hl0 : 0 ≤ Real.log (1 / x) := Real.log_nonneg (by rw [le_div_iff₀ hx0]; linarith)
  -- `2 ε log (1/x) = log a⁻¹ ≤ a⁻¹ - 1`
  have hlog : 2 * ε * Real.log (1 / x) ≤ a⁻¹ := by
    have h1 : Real.log a⁻¹ ≤ a⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr ha0)
    have h2 : Real.log a⁻¹ = 2 * ε * Real.log (1 / x) := by
      rw [Real.log_inv, ha, Real.log_rpow hx0, one_div, Real.log_inv]
      ring
    linarith
  have hlog' : a * Real.log (1 / x) ≤ 1 / (2 * ε) := by
    rw [le_div_iff₀ h2ε]
    have := mul_le_mul_of_nonneg_left hlog ha0.le
    rw [mul_inv_cancel₀ ha0.ne'] at this
    linarith
  have hlog2 : (2 : ℝ) / 3 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlb : Real.logb 2 (1 / x) ≤ 3 / 2 * Real.log (1 / x) := by
    rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
    nlinarith
  have hal : a * Real.logb 2 (1 / x) ≤ 1 / ε := by
    calc a * Real.logb 2 (1 / x) ≤ a * (3 / 2 * Real.log (1 / x)) :=
          mul_le_mul_of_nonneg_left hlb ha0.le
      _ = 3 / 2 * (a * Real.log (1 / x)) := by ring
      _ ≤ 3 / 2 * (1 / (2 * ε)) := by gcongr
      _ = 3 / 4 * (1 / ε) := by field_simp; ring
      _ ≤ 1 / ε := by
          have : 0 < 1 / ε := by positivity
          linarith
  have hpos : 0 ≤ x ^ (1 - 2 * ε) := Real.rpow_nonneg hx0.le _
  calc x * (Real.logb 2 (1 / x) + 3) = x ^ (1 - 2 * ε) * (a * Real.logb 2 (1 / x) + 3 * a) := by
        rw [hxe]
        have : x ^ (1 - 2 * ε) * a = x := hxe.symm
        nth_rewrite 1 [hxe]
        ring
    _ ≤ x ^ (1 - 2 * ε) * (1 / ε + 3) := by
        refine mul_le_mul_of_nonneg_left ?_ hpos
        linarith
    _ = (3 + 1 / ε) * x ^ (1 - 2 * ε) := by ring

/-! ### Exponent comparisons -/

/-- For `N ≥ N_ε := ⌈1/(2ε)⌉ + 11` we have `1/(2ε) ≤ N - 1` and `12 ≤ N`. -/
theorem natCeil_inv_le_sub_one {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : ⌈1 / (2 * ε)⌉₊ + 11 ≤ N) :
    1 / (2 * ε) ≤ (N : ℝ) - 1 ∧ (12 : ℝ) ≤ N := by
  have h1 : 1 / (2 * ε) ≤ (⌈1 / (2 * ε)⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : ((⌈1 / (2 * ε)⌉₊ + 11 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
  push_cast at h2
  have h3 : (1 : ℝ) ≤ ⌈1 / (2 * ε)⌉₊ := by
    have : 1 ≤ ⌈1 / (2 * ε)⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
    exact_mod_cast this
  constructor <;> linarith

/-- The blueprint's exponent comparison in the variable `E = |E₁| ∈ (0, 1]`:
`E^{1/2 - 1/(2(N-1))} ≤ E^{1/2-ε}` when `1/(2(N-1)) ≤ ε`. -/
theorem rpow_half_sub_le {E N ε : ℝ} (hE0 : 0 < E) (hE1 : E ≤ 1)
    (h : 1 / (2 * (N - 1)) ≤ ε) : E ^ (1 / 2 - 1 / (2 * (N - 1))) ≤ E ^ (1 / 2 - ε) :=
  Real.rpow_le_rpow_of_exponent_ge hE0 hE1 (by linarith)

/-! ### The two sums in the variable `E = |E₁|` -/

theorem sqrt_rpow_one_sub_inv {E N : ℝ} (hE0 : 0 < E) :
    (E ^ (1 / 2 : ℝ)) ^ (1 - 1 / (N - 1)) = E ^ (1 / 2 - 1 / (2 * (N - 1))) := by
  rw [← Real.rpow_mul hE0.le]
  congr 1
  rcases eq_or_ne (N - 1) 0 with h | h
  · simp [h]
  · field_simp

theorem sqrt_rpow_one_sub_two_mul {E ε : ℝ} (hE0 : 0 < E) :
    (E ^ (1 / 2 : ℝ)) ^ (1 - 2 * ε) = E ^ (1 / 2 - ε) := by
  rw [← Real.rpow_mul hE0.le]
  congr 1
  ring

/-! ### Absorbing constants -/

end PrimeBHT.TimeFrequency.Tile
