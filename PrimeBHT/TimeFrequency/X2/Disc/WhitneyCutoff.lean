module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!
# X2, node V05-3a: the Whitney partition `wphi` and the tensor Whitney cutoff `wcut`

`wphi x = Γ(x) - Γ(x - 1)`, `Γ(x) = smoothTransition(x + 1/2)`: smooth, `≥ 0`, supported in `(-1/2, 3/2)`, and
`Σ_{n ∈ ℤ} wphi(x - n) = 1` (telescoping).  `wcut lo hi (x₁, x₂) = Σ_{(n₁,n₂), lo ≤ |n₂ - n₁| ≤ hi} wphi(x₁ - n₁) wphi(x₂ - n₂)`
equals `1` when `lo + 2 ≤ |x₂ - x₁| ≤ hi - 2` and vanishes when `|x₂ - x₁| ≥ hi + 2` (for the Whitney exponent `a = 7`:
`lo = 62`, `hi = 258`, `b = 2^{k-7}`: `wcut = 1` where `2^{k-1} ≤ |ξ₂ - ξ₁| ≤ 2^{k+1}` and `= 0` where `|ξ₂ - ξ₁| ≥ 260 b`).
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Disc

/-- Smooth monotone step: `0` on `(-∞, -1/2]`, `1` on `[1/2, ∞)`. -/
def stepG (x : ℝ) : ℝ := Real.smoothTransition (x + 1 / 2)

theorem stepG_monotone : Monotone stepG := fun x y h => Real.smoothTransition.monotone (by linarith)

theorem stepG_eq_zero {x : ℝ} (h : x ≤ -1 / 2) : stepG x = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)

theorem stepG_eq_one {x : ℝ} (h : 1 / 2 ≤ x) : stepG x = 1 := Real.smoothTransition.one_of_one_le (by linarith)

/-- The Whitney bump `φ`. -/
def wphi (x : ℝ) : ℝ := stepG x - stepG (x - 1)

theorem contDiff_wphi : ContDiff ℝ ∞ wphi := by
  unfold wphi stepG
  have := Real.smoothTransition.contDiff (n := ⊤)
  exact (this.comp (contDiff_id.add contDiff_const)).sub (this.comp ((contDiff_id.sub contDiff_const).add contDiff_const))

theorem wphi_nonneg (x : ℝ) : 0 ≤ wphi x := by
  unfold wphi; linarith [stepG_monotone (show x - 1 ≤ x by linarith)]

theorem wphi_eq_zero {x : ℝ} (h : x ≤ -1 / 2 ∨ 3 / 2 ≤ x) : wphi x = 0 := by
  unfold wphi
  rcases h with h | h
  · rw [stepG_eq_zero h, stepG_eq_zero (by linarith)]; ring
  · rw [stepG_eq_one (by linarith), stepG_eq_one (by linarith)]; ring

theorem wphi_ne_zero {x : ℝ} (h : wphi x ≠ 0) : -1 / 2 < x ∧ x < 3 / 2 := by
  by_contra hc
  apply h
  apply wphi_eq_zero
  by_cases h1 : x ≤ -1 / 2
  · exact Or.inl h1
  · right; by_contra h2; exact hc ⟨by linarith, by linarith⟩

theorem wphi_le_one (x : ℝ) : wphi x ≤ 1 := by
  unfold wphi stepG
  linarith [Real.smoothTransition.le_one (x + 1 / 2), Real.smoothTransition.nonneg (x - 1 + 1 / 2)]

/-- `Σ_n φ(x - n) = 1`. -/
theorem hasSum_wphi (x : ℝ) : HasSum (fun n : ℤ => wphi (x - n)) 1 := by
  set m : ℤ := ⌊x⌋ with hm
  have h1 : (m : ℝ) ≤ x := Int.floor_le x
  have h2 : x < m + 1 := Int.lt_floor_add_one x
  have hfin : ∀ n : ℤ, n ∉ Finset.Icc (m - 1) (m + 1) → wphi (x - n) = 0 := by
    intro n hn
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    apply wphi_eq_zero
    rcases hn with h | h
    · right
      have : n + 1 ≤ m - 1 := by omega
      have : (n : ℝ) + 1 ≤ m - 1 := by exact_mod_cast this
      linarith
    · left
      have : m + 1 + 1 ≤ n := by omega
      have : (m : ℝ) + 1 + 1 ≤ n := by exact_mod_cast this
      linarith
  have hsum : ∑ n ∈ Finset.Icc (m - 1) (m + 1), wphi (x - n) = 1 := by
    have e : Finset.Icc (m - 1) (m + 1) = {m - 1, m, m + 1} := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    rw [e, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), Finset.sum_singleton]
    unfold wphi
    push_cast
    have a1 : stepG (x - ((m : ℝ) - 1)) = 1 := stepG_eq_one (by linarith)
    have a2 : stepG (x - ((m : ℝ) + 1) - 1) = 0 := stepG_eq_zero (by linarith)
    have b1 : stepG (x - ((m : ℝ) - 1) - 1) = stepG (x - m) := by congr 1; ring
    have b2 : stepG (x - (m : ℝ) - 1) = stepG (x - ((m : ℝ) + 1)) := by congr 1; ring
    linarith
  have h : HasSum (fun n : ℤ => wphi (x - n)) (∑ n ∈ Finset.Icc (m - 1) (m + 1), wphi (x - n)) :=
    hasSum_sum_of_ne_finset_zero hfin
  rwa [hsum] at h

/-- The tensor Whitney cutoff `Σ_{(n₁,n₂): lo ≤ |n₂ - n₁| ≤ hi} φ(x₁ - n₁) φ(x₂ - n₂)`. -/
def wcut (lo hi : ℤ) (x : ℝ × ℝ) : ℝ :=
  ∑' p : ℤ × ℤ, if lo ≤ |p.2 - p.1| ∧ |p.2 - p.1| ≤ hi then wphi (x.1 - p.1) * wphi (x.2 - p.2) else 0

/-- A nonzero term has `|(n₂ - n₁) - (x₂ - x₁)| < 2`. -/
theorem abs_sub_lt_of_ne_zero {x : ℝ × ℝ} {p : ℤ × ℤ} (h : wphi (x.1 - p.1) * wphi (x.2 - p.2) ≠ 0) :
    |((p.2 - p.1 : ℤ) : ℝ) - (x.2 - x.1)| < 2 := by
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  obtain ⟨a1, a2⟩ := wphi_ne_zero h1
  obtain ⟨b1, b2⟩ := wphi_ne_zero h2
  rw [abs_lt]
  push_cast
  constructor <;> linarith

theorem abs_close {d y : ℝ} (h : |d - y| < 2) : |y| - 2 < |d| ∧ |d| < |y| + 2 := by
  have h1 := abs_sub_abs_le_abs_sub d y
  have h2 := abs_sub_abs_le_abs_sub y d
  rw [abs_sub_comm y d] at h2
  constructor <;> linarith

theorem wcut_eq_one {lo hi : ℤ} {x : ℝ × ℝ} (hlo : (lo : ℝ) + 2 ≤ |x.2 - x.1|)
    (hhi : |x.2 - x.1| ≤ (hi : ℝ) - 2) : wcut lo hi x = 1 := by
  have hterm : ∀ p : ℤ × ℤ, (if lo ≤ |p.2 - p.1| ∧ |p.2 - p.1| ≤ hi then wphi (x.1 - p.1) * wphi (x.2 - p.2) else 0) =
      wphi (x.1 - p.1) * wphi (x.2 - p.2) := by
    intro p
    by_cases h0 : wphi (x.1 - p.1) * wphi (x.2 - p.2) = 0
    · simp [h0]
    · obtain ⟨c1, c2⟩ := abs_close (abs_sub_lt_of_ne_zero h0)
      rw [ite_eq_left]
      constructor
      · have : (lo : ℝ) ≤ ((|p.2 - p.1| : ℤ) : ℝ) := by rw [Int.cast_abs]; linarith
        exact_mod_cast this
      · have : ((|p.2 - p.1| : ℤ) : ℝ) ≤ hi := by rw [Int.cast_abs]; linarith
        exact_mod_cast this
  unfold wcut
  rw [tsum_congr hterm]
  have hs : Summable fun p : ℤ × ℤ => wphi (x.1 - p.1) * wphi (x.2 - p.2) :=
    Summable.mul_of_nonneg (f := fun n : ℤ => wphi (x.1 - n)) (g := fun n : ℤ => wphi (x.2 - n))
      (hasSum_wphi x.1).summable (hasSum_wphi x.2).summable
      (fun n => wphi_nonneg _) (fun n => wphi_nonneg _)
  have := (hasSum_wphi x.1).mul (hasSum_wphi x.2) hs
  rw [mul_one] at this
  exact this.tsum_eq

end PrimeBHT.TimeFrequency.X2.Disc
