module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# V08: the dyadic sum `∑_{j ∈ ℤ} min(a 2^j, b 2^{-j}) ≤ 4 √(ab)`

The elementary summation lemma behind the kernel estimates of Mikhlin multipliers: a dyadic piece of
frequency scale `2^j` contributes `min(a 2^j, b 2^{-j})` (`a 2^j` by the trivial bound, `b 2^{-j}` by
integration by parts), and the sum over all scales is `O(√(ab))`.  Used with `a = A`, `b = A'/x²`
(`|K(x)| ≲ 1/|x|`) and with `a = |y|`, `b = 1/|y|` (the Hörmander integral condition).
-/

@[expose] public section

open scoped Topology

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

/-- The crossover index: `a 4^n ≤ b < a 4^(n+1)`. -/
theorem exists_crossover {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ n : ℤ, a * (4 : ℝ) ^ n ≤ b ∧ b < a * (4 : ℝ) ^ (n + 1) := by
  obtain ⟨n, hn⟩ := exists_mem_Ico_zpow (div_pos hb ha) (by norm_num : (1 : ℝ) < 4)
  refine ⟨n, ?_, ?_⟩
  · have := hn.1
    rw [le_div_iff₀ ha] at this
    linarith
  · have := hn.2
    rw [div_lt_iff₀ ha] at this
    linarith

/-- **The dyadic sum lemma**: the family `j ↦ min(a 2^j, b 2^{-j})` is summable over `ℤ` with sum at
most `4 √(ab)`. -/
theorem hasSum_le_min_two_zpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Summable (fun j : ℤ => min (a * (2 : ℝ) ^ j) (b * (2 : ℝ) ^ (-j))) ∧
      ∑' j : ℤ, min (a * (2 : ℝ) ^ j) (b * (2 : ℝ) ^ (-j)) ≤ 4 * Real.sqrt (a * b) := by
  obtain ⟨n, hn1, hn2⟩ := exists_crossover ha hb
  -- the majorant
  set f₁ : ℤ → ℝ := fun j => if j ≤ n then a * (2 : ℝ) ^ j else 0 with hf₁
  set f₂ : ℤ → ℝ := fun j => if n < j then b * (2 : ℝ) ^ (-j) else 0 with hf₂
  have h2pos : (0 : ℝ) < 2 ^ n := zpow_pos (by norm_num) n
  have hS₁ : HasSum f₁ (2 * (a * (2 : ℝ) ^ n)) := by
    have hinj : Function.Injective (fun k : ℕ => n - (k : ℤ)) := fun x y h => by
      simp only at h; omega
    rw [← hinj.hasSum_iff (f := f₁)]
    · have : (f₁ ∘ fun k : ℕ => n - (k : ℤ)) = fun k : ℕ => a * (2 : ℝ) ^ n * ((1 : ℝ) / 2) ^ k := by
        ext k
        simp only [Function.comp, hf₁]
        rw [ite_eq_left (by omega), zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, one_div,
          inv_pow]
        field_simp
      rw [this]
      simpa [mul_comm] using (hasSum_geometric_two).mul_left (a * (2 : ℝ) ^ n)
    · intro j hj
      simp only [hf₁]
      rw [ite_eq_right]
      intro hjn
      apply hj
      exact ⟨(n - j).toNat, by simp only; omega⟩
  have hS₂ : HasSum f₂ (2 * (b * (2 : ℝ) ^ (-(n + 1)))) := by
    have hinj : Function.Injective (fun k : ℕ => n + 1 + (k : ℤ)) := fun x y h => by
      simp only at h; omega
    rw [← hinj.hasSum_iff (f := f₂)]
    · have : (f₂ ∘ fun k : ℕ => n + 1 + (k : ℤ)) =
          fun k : ℕ => b * (2 : ℝ) ^ (-(n + 1)) * ((1 : ℝ) / 2) ^ k := by
        ext k
        simp only [Function.comp, hf₂]
        rw [ite_eq_left (by omega)]
        have h2 : (2 : ℝ) ^ (-(n + 1 + (k : ℤ))) = (2 : ℝ) ^ (-(n + 1)) * ((1 : ℝ) / 2) ^ k := by
          rw [show -(n + 1 + (k : ℤ)) = -(n + 1) + (-(k : ℤ)) by ring,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          simp only [zpow_neg (2 : ℝ) (k : ℤ), zpow_natCast, one_div, inv_pow]
        rw [h2]
        ring
      rw [this]
      simpa [mul_comm] using (hasSum_geometric_two).mul_left (b * (2 : ℝ) ^ (-(n + 1)))
    · intro j hj
      simp only [hf₂]
      rw [ite_eq_right]
      intro hjn
      apply hj
      exact ⟨(j - (n + 1)).toNat, by simp only; omega⟩
  have hS : HasSum (f₁ + f₂) (2 * (a * (2 : ℝ) ^ n) + 2 * (b * (2 : ℝ) ^ (-(n + 1)))) :=
    hS₁.add hS₂
  -- pointwise domination
  have hdom : ∀ j : ℤ, min (a * (2 : ℝ) ^ j) (b * (2 : ℝ) ^ (-j)) ≤ (f₁ + f₂) j := by
    intro j
    by_cases hj : j ≤ n
    · simp only [Pi.add_apply, hf₁, hf₂, ite_eq_left hj, ite_eq_right (not_lt.2 hj), add_zero]
      exact min_le_left _ _
    · have hj' : n < j := lt_of_not_ge hj
      simp only [Pi.add_apply, hf₁, hf₂, ite_eq_right hj, ite_eq_left hj', zero_add]
      exact min_le_right _ _
  have hnonneg : ∀ j : ℤ, 0 ≤ min (a * (2 : ℝ) ^ j) (b * (2 : ℝ) ^ (-j)) := fun j =>
    le_min (by positivity) (by positivity)
  have hsum : Summable (fun j : ℤ => min (a * (2 : ℝ) ^ j) (b * (2 : ℝ) ^ (-j))) :=
    Summable.of_nonneg_of_le hnonneg hdom hS.summable
  refine ⟨hsum, ?_⟩
  have hle := hsum.tsum_le_tsum hdom hS.summable
  rw [hS.tsum_eq] at hle
  refine hle.trans ?_
  -- `2 a 2^n + 2 b 2^{-(n+1)} ≤ 4 √(ab)`
  set u : ℝ := a * (2 : ℝ) ^ n with hu
  set v : ℝ := b * (2 : ℝ) ^ (-n) with hv
  have huv : u * v = a * b := by
    rw [hu, hv]
    have : (2 : ℝ) ^ n * (2 : ℝ) ^ (-n) = 1 := by rw [zpow_neg, mul_inv_cancel₀ h2pos.ne']
    calc a * 2 ^ n * (b * 2 ^ (-n)) = a * b * (2 ^ n * 2 ^ (-n)) := by ring
      _ = a * b := by rw [this, mul_one]
  have h4 : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]; norm_num
  have h41 : (4 : ℝ) ^ (n + 1) = 4 * ((2 : ℝ) ^ n) ^ 2 := by
    rw [zpow_add₀ (by norm_num : (4 : ℝ) ≠ 0), zpow_one, h4]; ring
  have hvpos : 0 < v := by positivity
  have hupos : 0 < u := by positivity
  -- `u ≤ v` and `v < 4u`
  have huv1 : u ≤ v := by
    have : a * (2 : ℝ) ^ n * (2 : ℝ) ^ n ≤ b := by
      calc a * 2 ^ n * 2 ^ n = a * (2 ^ n) ^ 2 := by ring
        _ = a * 4 ^ n := by rw [h4]
        _ ≤ b := hn1
    rw [hu, hv, zpow_neg]
    rw [le_mul_inv_iff₀ h2pos]
    exact this
  have huv2 : v < 4 * u := by
    have : b < 4 * (a * (2 : ℝ) ^ n * (2 : ℝ) ^ n) := by
      calc b < a * 4 ^ (n + 1) := hn2
        _ = 4 * (a * 2 ^ n * 2 ^ n) := by rw [h41]; ring
    rw [hu, hv, zpow_neg]
    rw [mul_inv_lt_iff₀ h2pos]
    nlinarith
  have hu_le : u ≤ Real.sqrt (a * b) := by
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith
  have hv_le : v ≤ 2 * Real.sqrt (a * b) := by
    have h2 : v / 2 ≤ Real.sqrt (a * b) := by
      refine Real.le_sqrt_of_sq_le ?_
      have := mul_le_mul_of_nonneg_left huv2.le hvpos.le
      nlinarith
    linarith
  have hexp : (2 : ℝ) ^ (-(n + 1)) = (2 : ℝ) ^ (-n) / 2 := by
    rw [neg_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_neg_one]; ring
  rw [hexp]
  calc 2 * (a * (2 : ℝ) ^ n) + 2 * (b * ((2 : ℝ) ^ (-n) / 2)) = 2 * u + v := by
        rw [hu, hv]; ring
    _ ≤ 4 * Real.sqrt (a * b) := by linarith

end PrimeBHT.TimeFrequency.X2.CZ
