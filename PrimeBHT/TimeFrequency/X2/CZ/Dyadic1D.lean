module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Interval.Set.Basic

/-!
# V08 phase 2: dyadic intervals on `ℝ`

`dyI k n = [n 2^k, (n+1) 2^k)` (`k, n ∈ ℤ`) and `dyIdx k x = ⌊x / 2^k⌋` (the index of the level-`k` interval
containing `x`).  The only combinatorial facts needed by the Calderón-Zygmund decomposition
(`CZDecomp.lean`):

* `mem_dyI_dyIdx`, `dyIdx_eq_of_mem`: `x ∈ dyI k (dyIdx k x)` and `x ∈ dyI k n ⇒ dyIdx k x = n`;
* `dyI_subset_of_inter`: two dyadic intervals which meet are nested (the coarser contains the finer);
* `dyI_eq_of_inter_same`: two level-`k` dyadic intervals which meet are equal;
* `volume_dyI`: `|dyI k n| = 2^k`.
-/

@[expose] public section

open MeasureTheory Set

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

/-- The dyadic interval `[n 2^k, (n+1) 2^k)`. -/
noncomputable def dyI (k n : ℤ) : Set ℝ := Ico ((n : ℝ) * (2 : ℝ) ^ k) (((n : ℝ) + 1) * (2 : ℝ) ^ k)

/-- The index of the level-`k` dyadic interval containing `x`. -/
noncomputable def dyIdx (k : ℤ) (x : ℝ) : ℤ := ⌊x / (2 : ℝ) ^ k⌋

theorem two_zpow_pos (k : ℤ) : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k

theorem measurableSet_dyI (k n : ℤ) : MeasurableSet (dyI k n) := measurableSet_Ico

theorem mem_dyI {k n : ℤ} {x : ℝ} :
    x ∈ dyI k n ↔ (n : ℝ) * (2 : ℝ) ^ k ≤ x ∧ x < ((n : ℝ) + 1) * (2 : ℝ) ^ k := Iff.rfl

theorem mem_dyI_dyIdx (k : ℤ) (x : ℝ) : x ∈ dyI k (dyIdx k x) := by
  have hp := two_zpow_pos k
  unfold dyIdx
  rw [mem_dyI]
  constructor
  · have := Int.floor_le (x / (2 : ℝ) ^ k)
    rw [le_div_iff₀ hp] at this
    exact this
  · have := Int.lt_floor_add_one (x / (2 : ℝ) ^ k)
    rw [div_lt_iff₀ hp] at this
    exact this

theorem dyIdx_eq_of_mem {k n : ℤ} {x : ℝ} (h : x ∈ dyI k n) : dyIdx k x = n := by
  have hp := two_zpow_pos k
  rw [mem_dyI] at h
  unfold dyIdx
  rw [Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ hp]; exact h.1
  · rw [div_lt_iff₀ hp]; exact h.2

/-- Two dyadic intervals which meet are nested: the coarser one contains the finer one. -/
theorem dyI_subset_of_inter {k k' n n' : ℤ} (hk : k ≤ k') (h : (dyI k n ∩ dyI k' n').Nonempty) :
    dyI k n ⊆ dyI k' n' := by
  obtain ⟨z, hz1, hz2⟩ := h
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, k' = k + d := ⟨(k' - k).toNat, by omega⟩
  have hp := two_zpow_pos k
  have hM : (2 : ℝ) ^ (k + (d : ℤ)) = (2 : ℝ) ^ k * (2 : ℝ) ^ d := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
  rw [mem_dyI] at hz1 hz2
  rw [hM] at hz2
  set M : ℤ := (2 : ℤ) ^ d with hMdef
  have hMr : ((M : ℤ) : ℝ) = (2 : ℝ) ^ d := by simp [hMdef]
  -- integer inequalities `n' M ≤ n` and `n + 1 ≤ (n' + 1) M`
  have h1 : (n' * M : ℤ) < n + 1 := by
    have : ((n' * M : ℤ) : ℝ) * (2 : ℝ) ^ k < ((n + 1 : ℤ) : ℝ) * (2 : ℝ) ^ k := by
      push_cast
      rw [hMr]
      nlinarith [hz2.1, hz1.2]
    have := lt_of_mul_lt_mul_right this hp.le
    exact_mod_cast this
  have h2 : n < (n' + 1) * M := by
    have : (n : ℝ) * (2 : ℝ) ^ k < (((n' + 1) * M : ℤ) : ℝ) * (2 : ℝ) ^ k := by
      push_cast
      rw [hMr]
      nlinarith [hz1.1, hz2.2]
    have := lt_of_mul_lt_mul_right this hp.le
    exact_mod_cast this
  intro w hw
  rw [mem_dyI] at hw ⊢
  rw [hM]
  constructor
  · have : ((n' * M : ℤ) : ℝ) ≤ n := by exact_mod_cast (by omega : n' * M ≤ n)
    push_cast at this
    rw [hMr] at this
    nlinarith [hw.1]
  · have : ((n + 1 : ℤ) : ℝ) ≤ (((n' + 1) * M : ℤ) : ℝ) := by exact_mod_cast (by omega : n + 1 ≤ (n' + 1) * M)
    push_cast at this
    rw [hMr] at this
    nlinarith [hw.2]

theorem dyI_eq_of_inter_same {k n n' : ℤ} (h : (dyI k n ∩ dyI k n').Nonempty) : n = n' := by
  obtain ⟨z, hz1, hz2⟩ := h
  rw [← dyIdx_eq_of_mem hz1, ← dyIdx_eq_of_mem hz2]

end PrimeBHT.TimeFrequency.X2.CZ
