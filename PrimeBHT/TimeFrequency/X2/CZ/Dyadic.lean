module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# V08: the dyadic partition of unity on `ℝ ∖ {0}`

`dyadicPsi ξ = b(ξ) - b(2ξ)` with `b` the smooth bump equal to `1` on `[-1, 1]` and supported in
`(-2, 2)`.  Then (all with explicit statements, no constants depending on anything but the fixed bump)

* `contDiff_dyadicPsi`: `ψ` is smooth;
* `dyadicPsi_eq_zero_of_abs_le`, `dyadicPsi_eq_zero_of_two_le_abs`: `ψ` vanishes for `|ξ| ≤ 1/2` and
  for `|ξ| ≥ 2` (so `ψ(2^{-j}·)` lives on the annulus `2^{j-1} ≤ |ξ| ≤ 2^{j+1}`);
* `exists_bound_iteratedDeriv_dyadicPsi`: every derivative of `ψ` is bounded;
* `hasSum_dyadicPsi_scaled`: `∑_{j ∈ ℤ} ψ(2^{-j} ξ) = 1` for `ξ ≠ 0` (finitely many nonzero terms).

This is the partition of unity of the Mikhlin-Hörmander kernel estimates of
`Pieces.lean` (blueprint V08, scalar input of (f)); it is the same mechanism as the dyadic
decomposition of X1's R3 (`X1/RealLine/LittlewoodPaley*`), but for the standard dyadic bump with no
reference to the paper's cutoff.
-/

@[expose] public section

open Set
open scoped ContDiff

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

/-- The smooth bump `b`: `1` on `[-1, 1]`, `0` outside `(-2, 2)`, `0 ≤ b ≤ 1`. -/
noncomputable def dyadicBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The dyadic bump `ψ(ξ) = b(ξ) - b(2ξ)`. -/
noncomputable def dyadicPsi (ξ : ℝ) : ℝ := dyadicBump ξ - dyadicBump (2 * ξ)

theorem contDiff_dyadicPsi : ContDiff ℝ ∞ dyadicPsi :=
  dyadicBump.contDiff.sub (dyadicBump.contDiff.comp (contDiff_const.mul contDiff_id))

theorem dyadicBump_eq_one {ξ : ℝ} (h : |ξ| ≤ 1) : dyadicBump ξ = 1 := by
  refine dyadicBump.one_of_mem_closedBall ?_
  simpa [Metric.mem_closedBall, dyadicBump] using h

theorem dyadicBump_eq_zero {ξ : ℝ} (h : 2 ≤ |ξ|) : dyadicBump ξ = 0 := by
  refine dyadicBump.zero_of_le_dist ?_
  simpa [dyadicBump, Real.dist_eq] using h

theorem dyadicPsi_eq_zero_of_abs_le {ξ : ℝ} (h : |ξ| ≤ 1 / 2) : dyadicPsi ξ = 0 := by
  have h1 : |ξ| ≤ 1 := by linarith
  have h2 : |2 * ξ| ≤ 1 := by rw [abs_mul]; norm_num; linarith
  simp [dyadicPsi, dyadicBump_eq_one h1, dyadicBump_eq_one h2]

theorem dyadicPsi_eq_zero_of_two_le_abs {ξ : ℝ} (h : 2 ≤ |ξ|) : dyadicPsi ξ = 0 := by
  have h2 : 2 ≤ |2 * ξ| := by rw [abs_mul]; norm_num; linarith
  simp [dyadicPsi, dyadicBump_eq_zero h, dyadicBump_eq_zero h2]

theorem dyadicPsi_eq_zero_iff_mem {ξ : ℝ} (h : dyadicPsi ξ ≠ 0) : 1 / 2 < |ξ| ∧ |ξ| < 2 := by
  by_contra hc
  rw [not_and_or, not_lt, not_lt] at hc
  rcases hc with hc | hc
  · exact h (dyadicPsi_eq_zero_of_abs_le hc)
  · exact h (dyadicPsi_eq_zero_of_two_le_abs hc)

theorem dyadicPsi_scaled_eq (ξ : ℝ) (j : ℤ) :
    dyadicPsi ((2 : ℝ) ^ (-j) * ξ) =
      dyadicBump ((2 : ℝ) ^ (-j) * ξ) - dyadicBump ((2 : ℝ) ^ (-(j - 1)) * ξ) := by
  have : (2 : ℝ) ^ (-(j - 1)) = 2 * (2 : ℝ) ^ (-j) := by
    rw [neg_sub, sub_eq_add_neg, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, mul_comm]
  rw [dyadicPsi, this, mul_assoc]

/-- The dyadic partition of unity: `∑_{j ∈ ℤ} ψ(2^{-j} ξ) = 1` for `ξ ≠ 0`. -/
theorem hasSum_dyadicPsi_scaled {ξ : ℝ} (hξ : ξ ≠ 0) :
    HasSum (fun j : ℤ => dyadicPsi ((2 : ℝ) ^ (-j) * ξ)) 1 := by
  set c : ℤ → ℝ := fun j => dyadicBump ((2 : ℝ) ^ (-j) * ξ) with hc
  have hf : ∀ j : ℤ, dyadicPsi ((2 : ℝ) ^ (-j) * ξ) = c j - c (j - 1) := fun j =>
    dyadicPsi_scaled_eq ξ j
  have hξpos : 0 < |ξ| := abs_pos.2 hξ
  -- large `j`: `c j = 1`
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt |ξ| (by norm_num : (1 : ℝ) < 2)
  have hcN : ∀ j : ℤ, (N : ℤ) ≤ j → c j = 1 := by
    intro j hj
    refine dyadicBump_eq_one ?_
    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
    have h1 : (2 : ℝ) ^ (-j) ≤ (2 : ℝ) ^ (-(N : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (-(N : ℤ)) * |ξ| ≤ 1 := by
      rw [zpow_neg, zpow_natCast]
      rw [inv_mul_le_iff₀ (by positivity)]
      linarith
    calc (2 : ℝ) ^ (-j) * |ξ| ≤ (2 : ℝ) ^ (-(N : ℤ)) * |ξ| := by gcongr
      _ ≤ 1 := h2
  -- small `j`: `c j = 0`
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (2 / |ξ|) (by norm_num : (1 : ℝ) < 2)
  have hcm : ∀ j : ℤ, j ≤ -(m : ℤ) → c j = 0 := by
    intro j hj
    refine dyadicBump_eq_zero ?_
    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
    have h1 : (2 : ℝ) ^ (m : ℤ) ≤ (2 : ℝ) ^ (-j) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [zpow_natCast] at h1
    have h2 : 2 ≤ (2 : ℝ) ^ m * |ξ| := by
      rw [div_lt_iff₀ hξpos] at hm
      linarith
    calc (2 : ℝ) ≤ (2 : ℝ) ^ m * |ξ| := h2
      _ ≤ (2 : ℝ) ^ (-j) * |ξ| := by gcongr
  -- finite support
  set n : ℕ := (N + m : ℤ).toNat with hn
  have hnN : -(m : ℤ) + n = N := by omega
  let e : ℕ → ℤ := fun k => -(m : ℤ) + 1 + k
  have hsupp : ∀ j : ℤ, j ∉ (Finset.range n).image e → dyadicPsi ((2 : ℝ) ^ (-j) * ξ) = 0 := by
    intro j hj
    rw [hf]
    by_cases h1 : j ≤ -(m : ℤ)
    · rw [hcm j h1, hcm (j - 1) (by omega)]; simp
    · by_cases h2 : (N : ℤ) < j
      · rw [hcN j (by omega), hcN (j - 1) (by omega)]; simp
      · exfalso
        apply hj
        rw [Finset.mem_image]
        refine ⟨(j - (-(m : ℤ) + 1)).toNat, ?_, ?_⟩
        · rw [Finset.mem_range]; omega
        · simp only [e]; omega
  have hsum : ∑ j ∈ (Finset.range n).image e, dyadicPsi ((2 : ℝ) ^ (-j) * ξ) = 1 := by
    rw [Finset.sum_image (fun a _ b _ hab => by simp only [e] at hab; omega)]
    have : ∀ k : ℕ, dyadicPsi ((2 : ℝ) ^ (-(e k)) * ξ) =
        c (-(m : ℤ) + (k + 1 : ℕ)) - c (-(m : ℤ) + k) := by
      intro k
      rw [hf]
      congr 2 <;> simp [e] <;> ring
    simp_rw [this]
    rw [Finset.sum_range_sub (fun k : ℕ => c (-(m : ℤ) + k)) n]
    simp only [Nat.cast_zero, add_zero, hnN]
    rw [hcN N le_rfl, hcm (-(m : ℤ)) le_rfl]
    simp
  have h : HasSum (fun j : ℤ => dyadicPsi ((2 : ℝ) ^ (-j) * ξ))
      (∑ j ∈ (Finset.range n).image e, dyadicPsi ((2 : ℝ) ^ (-j) * ξ)) :=
    hasSum_sum_of_ne_finset_zero hsupp
  rwa [hsum] at h

end PrimeBHT.TimeFrequency.X2.CZ
