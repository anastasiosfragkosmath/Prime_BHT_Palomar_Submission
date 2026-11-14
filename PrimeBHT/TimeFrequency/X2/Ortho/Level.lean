module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-!
# X2, node V10: the energy-level argument (real-number part)

The abstract real-number core of HLC Proposition `HilbertTileType` (L770-846): from the *basic estimate* for every
sub-collection (the form `∑ ℓ c² ≤ K (F2 + (μ² min(L, ∑ℓ))^{1/3} F2^{2/3})`, HLC `HilbertBasicEst` L599-611)
one deduces the `(1-α)`-form

  `∑ ℓ c² ≤ C_α (F2 + (μ₀² L)^{1-α} F2^α)`

by splitting the index set into dyadic energy levels `2^n λ < c ≤ 2^{n+1} λ`, `λ² L = F2` (HLC L797-830: weak type
from the basic estimate applied to the level, `1 + log` levels, `log ≤ (1-α)⁻¹ r^{1-α}`).
Here `ℓ i` is `|I_i|`, `c i` the single-tile energy, `F2 = ‖F‖₂²`, `L = ∑_T |I_T|`, `μ₀` a bound for the `c i`.
-/

public section

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

open Finset

/-- The closing algebra of the weak-type step: `σ ≤ K (f³ + m f²)`, `m³ ≤ 4 σ` imply `σ ≤ 6 K² f³`. -/
theorem weak_algebra {σ K f m : ℝ} (hK : 1 ≤ K) (hσ : 0 ≤ σ) (hf : 0 ≤ f) (_hm : 0 ≤ m)
    (h1 : σ ≤ K * (f ^ 3 + m * f ^ 2)) (h2 : m ^ 3 ≤ 4 * σ) : σ ≤ 6 * K ^ 2 * f ^ 3 := by
  have hK0 : 0 < K := by linarith
  have hf3 : 0 ≤ f ^ 3 := by positivity
  by_cases hs : σ ≤ 2 * K * f ^ 3
  · nlinarith [mul_nonneg hf3 (sub_nonneg.2 hK), mul_nonneg hf3 (mul_nonneg hK0.le (sub_nonneg.2 hK))]
  · have hs := not_le.1 hs
    have hσpos : 0 < σ := by nlinarith
    have h3 : σ / 2 < K * m * f ^ 2 := by nlinarith
    have h4 : (σ / 2) ^ 3 < (K * m * f ^ 2) ^ 3 := by
      apply pow_lt_pow_left₀ h3 (by positivity) (by norm_num)
    have h5 : (K * m * f ^ 2) ^ 3 ≤ K ^ 3 * (4 * σ) * f ^ 6 := by
      have : (K * m * f ^ 2) ^ 3 = K ^ 3 * m ^ 3 * f ^ 6 := by ring
      rw [this]
      have : 0 ≤ K ^ 3 * f ^ 6 := by positivity
      nlinarith
    have h6 : σ ^ 2 < 32 * K ^ 3 * f ^ 6 := by
      have h7 : σ * (σ ^ 2) < σ * (32 * K ^ 3 * f ^ 6) := by nlinarith
      exact lt_of_mul_lt_mul_left h7 hσpos.le
    have h8 : σ ^ 2 ≤ (6 * K ^ 2 * f ^ 3) ^ 2 := by
      have : 32 * K ^ 3 * f ^ 6 ≤ (6 * K ^ 2 * f ^ 3) ^ 2 := by
        have : (6 * K ^ 2 * f ^ 3) ^ 2 = 36 * K ^ 4 * f ^ 6 := by ring
        rw [this]
        have hf6 : 0 ≤ f ^ 6 := by positivity
        have : 32 * K ^ 3 ≤ 36 * K ^ 4 := by nlinarith [pow_pos hK0 3]
        nlinarith
      linarith
    exact (pow_le_pow_iff_left₀ hσ (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).1 h8

/-- `(x^{1/3})^3 = x` for `x ≥ 0`. -/
theorem rpow_third_cube {x : ℝ} (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- `x^{2/3} = (x^{1/3})^2`. -/
theorem rpow_two_thirds_eq {x : ℝ} (hx : 0 ≤ x) : x ^ ((2 : ℝ) / 3) = (x ^ ((1 : ℝ) / 3)) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

section Level

variable {ι : Type*}

/-- The weak-type step for one dyadic level `a < c ≤ 2 a`. -/
theorem level_weak {𝒬 : Finset ι} {ℓ c : ι → ℝ} {K F2 L a : ℝ} (hK : 1 ≤ K) (hF2 : 0 ≤ F2)
    (hL : 0 ≤ L) (ha : 0 < a) (hℓ : ∀ i ∈ 𝒬, 0 < ℓ i) (hc1 : ∀ i ∈ 𝒬, a < c i)
    (hbasic : ∑ i ∈ 𝒬, ℓ i * c i ^ 2 ≤
      K * (F2 + ((2 * a) ^ 2 * min L (∑ i ∈ 𝒬, ℓ i)) ^ ((1 : ℝ) / 3) * F2 ^ ((2 : ℝ) / 3))) :
    ∑ i ∈ 𝒬, ℓ i * c i ^ 2 ≤ 6 * K ^ 2 * F2 := by
  set σ := ∑ i ∈ 𝒬, ℓ i * c i ^ 2 with hσ
  set X := ∑ i ∈ 𝒬, ℓ i with hX
  have hX0 : 0 ≤ X := sum_nonneg fun i hi => (hℓ i hi).le
  have hσ0 : 0 ≤ σ := sum_nonneg fun i hi => mul_nonneg (hℓ i hi).le (sq_nonneg _)
  have hσX : a ^ 2 * X ≤ σ := by
    rw [hX, mul_sum]
    refine sum_le_sum fun i hi => ?_
    have h1 := hc1 i hi
    have h2 : a ^ 2 ≤ c i ^ 2 := by nlinarith
    nlinarith [hℓ i hi, mul_le_mul_of_nonneg_left h2 (hℓ i hi).le]
  set Λ := min L X with hΛ
  have hΛ0 : 0 ≤ Λ := le_min hL hX0
  have hΛX : Λ ≤ X := min_le_right _ _
  set m := ((2 * a) ^ 2 * Λ) ^ ((1 : ℝ) / 3) with hm
  set f := F2 ^ ((1 : ℝ) / 3) with hf
  have hm0 : 0 ≤ m := Real.rpow_nonneg (by positivity) _
  have hf0 : 0 ≤ f := Real.rpow_nonneg hF2 _
  have hm3 : m ^ 3 = (2 * a) ^ 2 * Λ := rpow_third_cube (by positivity)
  have hf3 : f ^ 3 = F2 := rpow_third_cube hF2
  have hf2 : F2 ^ ((2 : ℝ) / 3) = f ^ 2 := rpow_two_thirds_eq hF2
  refine le_trans ?_ (le_of_eq (by rw [← hf3] : 6 * K ^ 2 * f ^ 3 = 6 * K ^ 2 * F2))
  refine weak_algebra hK hσ0 hf0 hm0 ?_ ?_
  · rw [hf3, ← hf2]; exact hbasic
  · rw [hm3]; nlinarith [mul_le_mul_of_nonneg_left hΛX (sq_nonneg (2 * a))]

/-- The level-zero step: `c ≤ λ`, `λ² L ≤ F2`. -/
theorem level_zero {𝒬 : Finset ι} {ℓ c : ι → ℝ} {K F2 L lam : ℝ} (hK : 1 ≤ K) (hF2 : 0 ≤ F2)
    (hL : 0 ≤ L) (hlamF : lam ^ 2 * L ≤ F2) (hℓ : ∀ i ∈ 𝒬, 0 < ℓ i)
    (hbasic : ∑ i ∈ 𝒬, ℓ i * c i ^ 2 ≤
      K * (F2 + (lam ^ 2 * min L (∑ i ∈ 𝒬, ℓ i)) ^ ((1 : ℝ) / 3) * F2 ^ ((2 : ℝ) / 3))) :
    ∑ i ∈ 𝒬, ℓ i * c i ^ 2 ≤ 2 * K * F2 := by
  set X := ∑ i ∈ 𝒬, ℓ i with hX
  have hX0 : 0 ≤ X := sum_nonneg fun i hi => (hℓ i hi).le
  have hΛ : lam ^ 2 * min L X ≤ F2 :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) (sq_nonneg lam)).trans hlamF
  have h1 : (lam ^ 2 * min L X) ^ ((1 : ℝ) / 3) ≤ F2 ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow (by positivity [le_min hL hX0]) hΛ (by norm_num)
  have h2 : F2 ^ ((1 : ℝ) / 3) * F2 ^ ((2 : ℝ) / 3) = F2 := by
    rw [← Real.rpow_add' hF2 (by norm_num)]; norm_num
  have h3 : 0 ≤ F2 ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hF2 _
  calc ∑ i ∈ 𝒬, ℓ i * c i ^ 2 ≤ K * (F2 + (lam ^ 2 * min L X) ^ ((1 : ℝ) / 3) * F2 ^ ((2 : ℝ) / 3)) :=
        hbasic
    _ ≤ K * (F2 + F2 ^ ((1 : ℝ) / 3) * F2 ^ ((2 : ℝ) / 3)) := by
        gcongr
    _ = 2 * K * F2 := by rw [h2]; ring

/-- Induction over dyadic levels: `c ≤ 2^n λ` on `𝒬` gives `∑_𝒬 ℓ c² ≤ 6 K² (n + 2) F2`. -/
theorem level_induction [DecidableEq ι] {𝒮 : Finset ι} {ℓ c : ι → ℝ} {K F2 L lam : ℝ} (hK : 1 ≤ K)
    (hF2 : 0 ≤ F2) (hL : 0 ≤ L) (hlam : 0 < lam) (hlamF : lam ^ 2 * L ≤ F2)
    (hℓ : ∀ i ∈ 𝒮, 0 < ℓ i)
    (hbasic : ∀ 𝒬 ⊆ 𝒮, ∀ μ : ℝ, 0 ≤ μ → (∀ i ∈ 𝒬, c i ≤ μ) →
      ∑ i ∈ 𝒬, ℓ i * c i ^ 2 ≤
        K * (F2 + (μ ^ 2 * min L (∑ i ∈ 𝒬, ℓ i)) ^ ((1 : ℝ) / 3) * F2 ^ ((2 : ℝ) / 3))) :
    ∀ n : ℕ, ∀ 𝒬 ⊆ 𝒮, (∀ i ∈ 𝒬, c i ≤ 2 ^ n * lam) →
      ∑ i ∈ 𝒬, ℓ i * c i ^ 2 ≤ 6 * K ^ 2 * ((n : ℝ) + 2) * F2 := by
  intro n
  induction n with
  | zero =>
    intro 𝒬 h𝒬 hc
    have h := level_zero hK hF2 hL hlamF (fun i hi => hℓ i (h𝒬 hi))
      (hbasic 𝒬 h𝒬 lam hlam.le (fun i hi => by simpa using hc i hi))
    have : 2 * K * F2 ≤ 6 * K ^ 2 * (((0 : ℕ) : ℝ) + 2) * F2 := by
      push_cast
      nlinarith [mul_nonneg hF2 (sub_nonneg.2 hK), mul_nonneg hF2 (mul_nonneg (by linarith : (0 : ℝ) ≤ K)
        (sub_nonneg.2 hK))]
    exact h.trans this
  | succ n ih =>
    intro 𝒬 h𝒬 hc
    have ha : 0 < (2 : ℝ) ^ n * lam := by positivity
    set 𝒬₁ := 𝒬.filter (fun i => c i ≤ 2 ^ n * lam) with h1
    set 𝒬₂ := 𝒬.filter (fun i => ¬ c i ≤ 2 ^ n * lam) with h2
    have hsum := sum_filter_add_sum_filter_not 𝒬 (fun i => c i ≤ 2 ^ n * lam)
      (fun i => ℓ i * c i ^ 2)
    have hA := ih 𝒬₁ ((filter_subset _ _).trans h𝒬) (fun i hi => (mem_filter.1 hi).2)
    have hB : ∑ i ∈ 𝒬₂, ℓ i * c i ^ 2 ≤ 6 * K ^ 2 * F2 := by
      refine level_weak hK hF2 hL ha (fun i hi => hℓ i (h𝒬 (mem_filter.1 hi).1))
        (fun i hi => not_le.1 (mem_filter.1 hi).2) ?_
      refine hbasic 𝒬₂ ((filter_subset _ _).trans h𝒬) (2 * (2 ^ n * lam)) (by positivity) ?_
      intro i hi
      have := hc i (mem_filter.1 hi).1
      calc c i ≤ 2 ^ (n + 1) * lam := this
        _ = 2 * (2 ^ n * lam) := by ring
    rw [← hsum]
    push_cast
    nlinarith [hA, hB]

/-- **The level lemma** (HLC `HilbertTileType`, real-number form).  If the basic estimate holds for every
sub-collection `𝒬 ⊆ 𝒮`, with any bound `μ` of the `c i` on `𝒬`, then
`∑_𝒮 ℓ c² ≤ C_α (F2 + (μ₀² L)^{1-α} F2^α)` for every `0 < α < 1`, `C_α = 6 K² (3 + 1/((1-α) log 2))`. -/
theorem level_lemma [DecidableEq ι] {𝒮 : Finset ι} {ℓ c : ι → ℝ} {K F2 L μ₀ α : ℝ} (hK : 1 ≤ K)
    (hF2 : 0 < F2) (hL : 0 < L) (hμ₀ : 0 ≤ μ₀) (hα0 : 0 < α) (hα1 : α < 1)
    (hℓ : ∀ i ∈ 𝒮, 0 < ℓ i) (hcμ : ∀ i ∈ 𝒮, c i ≤ μ₀)
    (hbasic : ∀ 𝒬 ⊆ 𝒮, ∀ μ : ℝ, 0 ≤ μ → (∀ i ∈ 𝒬, c i ≤ μ) →
      ∑ i ∈ 𝒬, ℓ i * c i ^ 2 ≤
        K * (F2 + (μ ^ 2 * min L (∑ i ∈ 𝒬, ℓ i)) ^ ((1 : ℝ) / 3) * F2 ^ ((2 : ℝ) / 3))) :
    ∑ i ∈ 𝒮, ℓ i * c i ^ 2 ≤
      6 * K ^ 2 * (3 + 1 / ((1 - α) * Real.log 2)) * (F2 + (μ₀ ^ 2 * L) ^ (1 - α) * F2 ^ α) := by
  set lam := Real.sqrt (F2 / L) with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.2 (div_pos hF2 hL)
  have hlam2 : lam ^ 2 * L = F2 := by
    rw [hlam, Real.sq_sqrt (div_pos hF2 hL).le]; field_simp
  set x := μ₀ / lam with hx
  have hx0 : 0 ≤ x := div_nonneg hμ₀ hlam0.le
  set n := ⌈Real.logb 2 x⌉₊ with hn
  have hμn : μ₀ ≤ 2 ^ n * lam := by
    rcases hx0.eq_or_lt with h0 | hpos
    · have : μ₀ = 0 := by
        have : μ₀ / lam = 0 := h0.symm
        rcases div_eq_zero_iff.1 this with h | h
        · exact h
        · exact absurd h hlam0.ne'
      rw [this]; positivity
    · have h1 : x = (2 : ℝ) ^ Real.logb 2 x := (Real.rpow_logb (by norm_num) (by norm_num) hpos).symm
      have h2 : (2 : ℝ) ^ Real.logb 2 x ≤ (2 : ℝ) ^ (n : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
      rw [Real.rpow_natCast] at h2
      have : μ₀ = x * lam := by rw [hx]; field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right (h1.le.trans h2) hlam0.le
  have hmain := level_induction hK hF2.le hL.le hlam0 hlam2.le hℓ hbasic n 𝒮 (subset_refl _)
    (fun i hi => (hcμ i hi).trans hμn)
  -- bound on `n + 2`
  set ε := 1 - α with hε
  have hε0 : 0 < ε := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set r := μ₀ ^ 2 * L / F2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hxr : x ^ 2 = r := by
    rw [hx, hr, div_pow, hlam, Real.sq_sqrt (div_pos hF2 hL).le]; field_simp
  have hrε : 0 ≤ r ^ ε := Real.rpow_nonneg hr0 _
  have hn2 : (n : ℝ) + 2 ≤ 3 + r ^ ε / (2 * (ε * Real.log 2)) := by
    have hnn : 0 ≤ r ^ ε / (2 * (ε * Real.log 2)) := by positivity
    by_cases hx1 : x ≤ 1
    · have : n = 0 := by
        rw [hn, Nat.ceil_eq_zero]
        exact Real.logb_nonpos (by norm_num) hx0 hx1
      rw [this]; push_cast; linarith
    · have hx1 := not_le.1 hx1
      have hlb : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx1.le
      have h1 : (n : ℝ) < Real.logb 2 x + 1 := Nat.ceil_lt_add_one hlb
      have h2 : Real.log x ≤ r ^ ε / (2 * ε) := by
        have h3 := Real.log_le_rpow_div hr0 hε0
        have h4 : Real.log r = 2 * Real.log x := by
          rw [← hxr, Real.log_pow]; norm_num
        rw [h4] at h3
        rw [le_div_iff₀ (by positivity)]
        have : r ^ ε / ε * (2 * ε) / 2 = r ^ ε := by field_simp
        nlinarith [div_mul_cancel₀ (r ^ ε) hε0.ne']
      have h5 : Real.logb 2 x ≤ r ^ ε / (2 * (ε * Real.log 2)) := by
        rw [Real.logb, div_le_iff₀ hlog2]
        calc Real.log x ≤ r ^ ε / (2 * ε) := h2
          _ = r ^ ε / (2 * (ε * Real.log 2)) * Real.log 2 := by field_simp
      linarith
  -- assemble
  have hC : 0 ≤ 6 * K ^ 2 := by positivity
  have hstep : (n : ℝ) + 2 ≤ (3 + 1 / (ε * Real.log 2)) * (1 + r ^ ε) := by
    have h1 : r ^ ε / (2 * (ε * Real.log 2)) ≤ 1 / (ε * Real.log 2) * r ^ ε := by
      have : 0 < ε * Real.log 2 := by positivity
      rw [div_le_iff₀ (by positivity)]
      field_simp
      nlinarith [hrε]
    have h2 : 0 ≤ 1 / (ε * Real.log 2) := by positivity
    nlinarith [hn2, h1, mul_nonneg h2 hrε]
  have hrF : r ^ ε * F2 = (μ₀ ^ 2 * L) ^ ε * F2 ^ α := by
    have hF2ε : F2 ^ ε ≠ 0 := (Real.rpow_pos_of_pos hF2 ε).ne'
    have hα' : F2 ^ α * F2 ^ ε = F2 := by
      rw [← Real.rpow_add hF2, hε]; simp
    rw [hr, Real.div_rpow (by positivity) hF2.le, div_mul_eq_mul_div, div_eq_iff hF2ε]
    rw [mul_assoc, hα']
  calc ∑ i ∈ 𝒮, ℓ i * c i ^ 2 ≤ 6 * K ^ 2 * ((n : ℝ) + 2) * F2 := hmain
    _ ≤ 6 * K ^ 2 * ((3 + 1 / (ε * Real.log 2)) * (1 + r ^ ε)) * F2 := by
        gcongr
    _ = 6 * K ^ 2 * (3 + 1 / (ε * Real.log 2)) * (F2 + r ^ ε * F2) := by ring
    _ = _ := by rw [hrF]

end Level

end PrimeBHT.TimeFrequency.X2
