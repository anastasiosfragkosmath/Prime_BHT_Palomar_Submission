module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.Algebra.Support

/-!
# The Littlewood-Paley bump (blueprint node R3, step 1)

`ϱ(x) = s(x) - s(x - 1)` (`s = Real.smoothTransition`) is a smooth function supported in `[0, 2]` with
`∑_k ϱ(x - k) = 1`. With `γ = 9/8`, `β(ζ) = ϱ(2 log_γ ζ)` (`ζ > 0`, `0` otherwise) is smooth, supported in
`[1, γ]`, and `∑_k β(ζ / μ^k) = 1` for `ζ > 0`, `μ = γ^{1/2}`. The bump `b(η) = β(η / 8)` is supported
in `[8, 9]` and `λ_k = μ^k / 8` satisfies `b(ζ / λ_k) = β(ζ / μ^k)`.
-/

@[expose] public noncomputable section

open Filter Topology
open scoped ContDiff

namespace PrimeBHT.TimeFrequency.RealLine

/-- The smooth bump `ϱ(x) = s(x) - s(x-1)` supported in `[0, 2]`. -/
def lpRho (x : ℝ) : ℝ := Real.smoothTransition x - Real.smoothTransition (x - 1)

theorem contDiff_lpRho : ContDiff ℝ ∞ lpRho :=
  Real.smoothTransition.contDiff.sub
    (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

theorem lpRho_eq_zero_of_nonpos {x : ℝ} (h : x ≤ 0) : lpRho x = 0 := by
  simp [lpRho, Real.smoothTransition.zero_of_nonpos h,
    Real.smoothTransition.zero_of_nonpos (by linarith : x - 1 ≤ 0)]

theorem lpRho_eq_zero_of_two_le {x : ℝ} (h : 2 ≤ x) : lpRho x = 0 := by
  simp [lpRho, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x - 1)]

theorem lpRho_pos_imp {x : ℝ} (h : lpRho x ≠ 0) : 0 < x ∧ x < 2 := by
  refine ⟨?_, ?_⟩
  · by_contra h'; exact h (lpRho_eq_zero_of_nonpos (not_lt.1 h'))
  · by_contra h'; exact h (lpRho_eq_zero_of_two_le (not_lt.1 h'))

/-- Telescoping: `∑_{|k| ≤ K} ϱ(x - k) = s(x + K) - s(x - K - 1)`. -/
theorem sum_lpRho_Icc (x : ℝ) (K : ℕ) :
    ∑ k ∈ Finset.Icc (-(K : ℤ)) K, lpRho (x - k) =
      Real.smoothTransition (x + K) - Real.smoothTransition (x - K - 1) := by
  induction K with
  | zero => simp [lpRho]
  | succ K ih =>
    have hset : Finset.Icc (-((K + 1 : ℕ) : ℤ)) ((K + 1 : ℕ) : ℤ) =
        insert (-((K + 1 : ℕ) : ℤ)) (insert ((K + 1 : ℕ) : ℤ) (Finset.Icc (-(K : ℤ)) K)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hset, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih]
    simp only [lpRho]
    push_cast
    ring_nf

/-- `β(ζ) = ϱ(2 log ζ / log (9/8))` for `ζ > 0`, `0` otherwise. -/
def lpBeta (ζ : ℝ) : ℝ := if 0 < ζ then lpRho (2 * Real.log ζ / Real.log (9 / 8)) else 0

theorem log_nine_eighths_pos : 0 < Real.log (9 / 8 : ℝ) := Real.log_pos (by norm_num)

theorem lpBeta_eq_zero_of_lt_one {ζ : ℝ} (h : ζ < 1) : lpBeta ζ = 0 := by
  unfold lpBeta
  split_ifs with h0
  · apply lpRho_eq_zero_of_nonpos
    have : Real.log ζ < 0 := Real.log_neg h0 h
    have h2 : 2 * Real.log ζ < 0 := by linarith
    exact (div_neg_of_neg_of_pos h2 log_nine_eighths_pos).le
  · rfl

theorem lpBeta_ne_zero_imp {ζ : ℝ} (h : lpBeta ζ ≠ 0) : 1 < ζ ∧ ζ < 9 / 8 := by
  have h0 : 0 < ζ := by by_contra h'; exact h (by simp [lpBeta, h'])
  have h1 : lpRho (2 * Real.log ζ / Real.log (9 / 8)) ≠ 0 := by simpa [lpBeta, h0] using h
  obtain ⟨ha, hb⟩ := lpRho_pos_imp h1
  have hl := log_nine_eighths_pos
  rw [div_pos_iff_of_pos_right hl] at ha
  rw [div_lt_iff₀ hl] at hb
  refine ⟨?_, ?_⟩
  · by_contra h'; have := Real.log_nonpos h0.le (not_lt.1 h'); linarith
  · by_contra h'
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 9 / 8) (not_lt.1 h')
    linarith

theorem contDiff_lpBeta : ContDiff ℝ ∞ lpBeta := by
  refine contDiff_iff_contDiffAt.2 fun ζ => ?_
  by_cases hζ : ζ < 1
  · have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 ζ] lpBeta := by
      filter_upwards [Iio_mem_nhds hζ] with z hz
      exact (lpBeta_eq_zero_of_lt_one hz).symm
    exact contDiffAt_const.congr_of_eventuallyEq hev.symm
  · rw [not_lt] at hζ
    have hpos : 0 < ζ := by linarith
    have hev : (fun z : ℝ => lpRho (2 * Real.log z / Real.log (9 / 8))) =ᶠ[𝓝 ζ] lpBeta := by
      filter_upwards [Ioi_mem_nhds hpos] with z hz
      simp [lpBeta, Set.mem_Ioi.1 hz]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev.symm
    refine (contDiff_lpRho.contDiffAt).comp ζ ?_
    exact ((contDiffAt_const.mul (Real.contDiffAt_log.2 hpos.ne')).div_const _)

/-- The bump `b(η) = β(η / 8)`, supported in `[8, 9]`. -/
def lpBump (η : ℝ) : ℝ := lpBeta (η / 8)

theorem contDiff_lpBump : ContDiff ℝ ∞ lpBump :=
  contDiff_lpBeta.comp (contDiff_id.div_const 8)

theorem lpBump_eq_zero_of_notMem {η : ℝ} (h : η ∉ Set.Icc (8 : ℝ) 9) : lpBump η = 0 := by
  by_contra h0
  obtain ⟨h1, h2⟩ := lpBeta_ne_zero_imp h0
  exact h ⟨by linarith, by linarith⟩

theorem hasCompactSupport_lpBump : HasCompactSupport lpBump := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (8 : ℝ)) (b := 9)) fun η hη => ?_
  exact lpBump_eq_zero_of_notMem hη

/-- `μ = (9/8)^{1/2}`. -/
def lpMu : ℝ := Real.exp (Real.log (9 / 8) / 2)

theorem lpMu_pos : 0 < lpMu := Real.exp_pos _

theorem one_lt_lpMu : 1 < lpMu := Real.one_lt_exp_iff.2 (by have := log_nine_eighths_pos; linarith)

/-- `λ_k = μ^k / 8`. -/
def lpLam (k : ℤ) : ℝ := lpMu ^ k / 8

theorem lpLam_pos (k : ℤ) : 0 < lpLam k := div_pos (zpow_pos lpMu_pos k) (by norm_num)

theorem lpLam_ne_zero (k : ℤ) : lpLam k ≠ 0 := (lpLam_pos k).ne'

/-- `b(ζ / λ_k) = ϱ(2 log ζ / log(9/8) - k)` for `ζ > 0`. -/
theorem lpBump_div_lpLam {ζ : ℝ} (hζ : 0 < ζ) (k : ℤ) :
    lpBump (ζ / lpLam k) = lpRho (2 * Real.log ζ / Real.log (9 / 8) - k) := by
  have hmu : 0 < lpMu ^ k := zpow_pos lpMu_pos k
  have h1 : ζ / lpLam k / 8 = ζ / lpMu ^ k := by
    unfold lpLam; field_simp
  have hpos : 0 < ζ / lpMu ^ k := div_pos hζ hmu
  have hl := log_nine_eighths_pos
  have hlog : Real.log (lpMu ^ k) = k * (Real.log (9 / 8) / 2) := by
    rw [Real.log_zpow]; unfold lpMu; rw [Real.log_exp]
  simp only [lpBump, h1, lpBeta, hpos, ite_true]
  congr 1
  rw [Real.log_div hζ.ne' hmu.ne', hlog]
  field_simp

/-- Partial sums of the partition of unity in the multiplicative variable. -/
theorem sum_lpBump_Icc {ζ : ℝ} (hζ : 0 < ζ) (K : ℕ) :
    ∑ k ∈ Finset.Icc (-(K : ℤ)) K, lpBump (ζ / lpLam k) =
      Real.smoothTransition (2 * Real.log ζ / Real.log (9 / 8) + K) -
        Real.smoothTransition (2 * Real.log ζ / Real.log (9 / 8) - K - 1) := by
  rw [← sum_lpRho_Icc]
  exact Finset.sum_congr rfl fun k _ => lpBump_div_lpLam hζ k

theorem sum_lpBump_Icc_nonpos {ζ : ℝ} (hζ : ζ ≤ 0) (K : ℕ) :
    ∑ k ∈ Finset.Icc (-(K : ℤ)) K, lpBump (ζ / lpLam k) = 0 := by
  refine Finset.sum_eq_zero fun k _ => lpBump_eq_zero_of_notMem fun h => ?_
  have : ζ / lpLam k ≤ 0 := div_nonpos_of_nonpos_of_nonneg hζ (lpLam_pos k).le
  linarith [h.1]

theorem abs_sum_lpBump_Icc_le (ζ : ℝ) (K : ℕ) :
    |∑ k ∈ Finset.Icc (-(K : ℤ)) K, lpBump (ζ / lpLam k)| ≤ 1 := by
  by_cases hζ : 0 < ζ
  · rw [sum_lpBump_Icc hζ]
    have h1 := Real.smoothTransition.nonneg (2 * Real.log ζ / Real.log (9 / 8) + K)
    have h2 := Real.smoothTransition.le_one (2 * Real.log ζ / Real.log (9 / 8) + K)
    have h3 := Real.smoothTransition.nonneg (2 * Real.log ζ / Real.log (9 / 8) - K - 1)
    have h4 := Real.smoothTransition.le_one (2 * Real.log ζ / Real.log (9 / 8) - K - 1)
    rw [abs_le]; constructor <;> linarith
  · rw [sum_lpBump_Icc_nonpos (not_lt.1 hζ)]; simp

theorem tendsto_sum_lpBump_Icc {ζ : ℝ} (hζ : 0 < ζ) :
    Tendsto (fun K : ℕ => ∑ k ∈ Finset.Icc (-(K : ℤ)) K, lpBump (ζ / lpLam k)) atTop (𝓝 1) := by
  set a := 2 * Real.log ζ / Real.log (9 / 8)
  have hev : ∀ᶠ K : ℕ in atTop, ∑ k ∈ Finset.Icc (-(K : ℤ)) K, lpBump (ζ / lpLam k) = 1 := by
    filter_upwards [eventually_ge_atTop ⌈|a| + 1⌉₊] with K hK
    rw [sum_lpBump_Icc hζ]
    have hK' : |a| + 1 ≤ K := (Nat.le_ceil _).trans (by exact_mod_cast hK)
    have h1 := le_abs_self a
    have h2 := neg_abs_le a
    rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]
    norm_num
  exact tendsto_const_nhds.congr' (hev.mono fun K h => h.symm)

end PrimeBHT.TimeFrequency.RealLine

end
