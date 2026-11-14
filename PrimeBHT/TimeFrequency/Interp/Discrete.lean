module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Int.Log

/-!
# R6c, discrete part: the window lemmas D1 and D2

Blueprint `docs/x1-blueprint.md`, node R6c (lemmas D1, D2). Independent re-derivation:
`docs/audits/R6c-rederivation.md` (verdict: the argument is correct; corrections are cosmetic).

## Conventions (differences from the blueprint text, all harmless)

* The window of `μ > 0` is `Int.log 2 μ` (`= ⌊log₂ μ⌋`, i.e. `2 ^ w ≤ μ < 2 ^ (w + 1)`).
* The weights are `pairWeight a b = min (a/b) (b/a)` and `tripleWeight a b c = min/max`, defined
  to be `0` as soon as one argument is not positive; entries `μ = 0` therefore contribute `0`.
* D1 and D2 are stated in homogeneous form (no normalization `Σ x ≤ 1`):
  `Σ ≤ C · (Σ x)^θ (Σ y)^(1-θ)` resp. `Σ ≤ C · Π (Σ x_i)^(θ_i)`.
* `x_n = 2^(p n) μ_n` is written with a real power `(2:ℝ) ^ (p * n)`.
* The geometric bound inside a window (`sum_window_geometric`) needs only `p > 0`, `θ > 0`
  (comparison with the *last index* of the window), not `p > 1`.

## Main statements

* `sum_window_geometric`: `Σ_{n ∈ window} x_n^θ ≤ 2^θ (1 - 2^(-pθ))⁻¹ (Σ_{n ∈ window} x_n)^θ`.
* `pairWeight_rpow_le`: `min(a/b,b/a)^γ ≤ 2^γ (2^(-γ))^|log₂a - log₂b|` (windows).
* `sum_sum_mul_rpow_le`, `sum_sum_sum_mul_rpow_le`: Hölder against a kernel with bounded
  row and column sums (two and three factors).
* `d1`: the pair lemma D1.  `d2`: the triple lemma D2, with the weight
  `pairWeight(μ₁,μ₂)^γ · pairWeight(μ₁,μ₃)^γ`; it dominates the blueprint's
  `(μ_min/μ_max)^(2γ)` (`tripleWeight_le_pairWeight`), so the blueprint's D2 follows.
-/

@[expose] public section

namespace PrimeBHT.TimeFrequency.Interp

open Finset

/-! ### Geometric sums -/

lemma sum_pow_le_inv_one_sub {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (s : Finset ℕ) :
    ∑ k ∈ s, ρ ^ k ≤ (1 - ρ)⁻¹ := by
  rw [← tsum_geometric_of_lt_one h0 h1]
  exact (summable_geometric_of_lt_one h0 h1).sum_le_tsum s (fun k _ => pow_nonneg h0 k)

/-- `Σ_{j ∈ J} ρ^|j| ≤ 2 (1 - ρ)⁻¹` for every finite set of integers. -/
lemma sum_pow_natAbs_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (J : Finset ℤ) :
    ∑ j ∈ J, ρ ^ j.natAbs ≤ 2 * (1 - ρ)⁻¹ := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not J (fun j => 0 ≤ j)]
  have hA : ∑ j ∈ J.filter (fun j => 0 ≤ j), ρ ^ j.natAbs ≤ (1 - ρ)⁻¹ := by
    rw [← Finset.sum_image (f := fun k => ρ ^ k) (g := Int.natAbs)]
    · exact sum_pow_le_inv_one_sub h0 h1 _
    · intro a ha b hb hab
      simp only [coe_filter, Set.mem_ofPred_eq] at ha hb
      omega
  have hB : ∑ j ∈ J.filter (fun j => ¬ 0 ≤ j), ρ ^ j.natAbs ≤ (1 - ρ)⁻¹ := by
    rw [← Finset.sum_image (f := fun k => ρ ^ k) (g := Int.natAbs)]
    · exact sum_pow_le_inv_one_sub h0 h1 _
    · intro a ha b hb hab
      simp only [coe_filter, Set.mem_ofPred_eq] at ha hb
      omega
  linarith

/-- Row sums of the kernel `ρ^|a - b|` over a finite set. -/
lemma sum_pow_natAbs_sub_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (a : ℤ) (B : Finset ℤ) :
    ∑ b ∈ B, ρ ^ (a - b).natAbs ≤ 2 * (1 - ρ)⁻¹ := by
  classical
  rw [← Finset.sum_image (f := fun j : ℤ => ρ ^ j.natAbs) (g := fun b => a - b)]
  · exact sum_pow_natAbs_le h0 h1 _
  · intro x _ y _ hxy
    simp only at hxy
    omega

/-! ### Hölder against a kernel -/

/-- Two-factor Hölder against a kernel whose row and column sums are bounded by `c`. -/
theorem sum_sum_mul_rpow_le {ι κ : Type*} (A : Finset ι) (B : Finset κ) (k : ι → κ → ℝ)
    (X : ι → ℝ) (Y : κ → ℝ) {θ c : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hc : 0 ≤ c)
    (hk : ∀ a b, 0 ≤ k a b) (hX : ∀ a, 0 ≤ X a) (hY : ∀ b, 0 ≤ Y b)
    (hrow : ∀ a ∈ A, ∑ b ∈ B, k a b ≤ c) (hcol : ∀ b ∈ B, ∑ a ∈ A, k a b ≤ c) :
    ∑ a ∈ A, ∑ b ∈ B, k a b * (X a ^ θ * Y b ^ (1 - θ)) ≤
      c * ((∑ a ∈ A, X a) ^ θ * (∑ b ∈ B, Y b) ^ (1 - θ)) := by
  set SX := ∑ a ∈ A, X a
  set SY := ∑ b ∈ B, Y b
  have hSX : 0 ≤ SX := sum_nonneg fun a _ => hX a
  have hSY : 0 ≤ SY := sum_nonneg fun b _ => hY b
  have hθ' : 0 < 1 - θ := by linarith
  have hR : 0 ≤ c * (SX ^ θ * SY ^ (1 - θ)) := by positivity
  rcases hSX.eq_or_lt with hSX0 | hSX0
  · have h0 : ∀ a ∈ A, X a = 0 := (sum_eq_zero_iff_of_nonneg fun a _ => hX a).1 hSX0.symm
    refine le_trans (le_of_eq ?_) hR
    refine sum_eq_zero fun a ha => sum_eq_zero fun b _ => ?_
    rw [h0 a ha, Real.zero_rpow hθ₀.ne']
    ring
  rcases hSY.eq_or_lt with hSY0 | hSY0
  · have h0 : ∀ b ∈ B, Y b = 0 := (sum_eq_zero_iff_of_nonneg fun b _ => hY b).1 hSY0.symm
    refine le_trans (le_of_eq ?_) hR
    refine sum_eq_zero fun a _ => sum_eq_zero fun b hb => ?_
    rw [h0 b hb, Real.zero_rpow hθ'.ne']
    ring
  set P := SX ^ θ * SY ^ (1 - θ)
  have hP : 0 < P := by positivity
  -- pointwise weighted AM-GM
  have hpt : ∀ a b, X a ^ θ * Y b ^ (1 - θ) ≤
      P * (θ * (X a / SX) + (1 - θ) * (Y b / SY)) := by
    intro a b
    have h := Real.geom_mean_le_arith_mean2_weighted hθ₀.le hθ'.le
      (div_nonneg (hX a) hSX) (div_nonneg (hY b) hSY) (by ring : θ + (1 - θ) = 1)
    rw [Real.div_rpow (hX a) hSX, Real.div_rpow (hY b) hSY] at h
    have hXθ : 0 < SX ^ θ := by positivity
    have hYθ : 0 < SY ^ (1 - θ) := by positivity
    calc X a ^ θ * Y b ^ (1 - θ)
        = P * (X a ^ θ / SX ^ θ * (Y b ^ (1 - θ) / SY ^ (1 - θ))) := by
          simp only [P]; field_simp
      _ ≤ P * (θ * (X a / SX) + (1 - θ) * (Y b / SY)) := by gcongr
  calc ∑ a ∈ A, ∑ b ∈ B, k a b * (X a ^ θ * Y b ^ (1 - θ))
      ≤ ∑ a ∈ A, ∑ b ∈ B, k a b * (P * (θ * (X a / SX) + (1 - θ) * (Y b / SY))) := by
        exact sum_le_sum fun a _ => sum_le_sum fun b _ =>
          mul_le_mul_of_nonneg_left (hpt a b) (hk a b)
    _ = P * (θ / SX * ∑ a ∈ A, X a * ∑ b ∈ B, k a b) +
          P * ((1 - θ) / SY * ∑ b ∈ B, Y b * ∑ a ∈ A, k a b) := by
        simp only [mul_add, sum_add_distrib, mul_sum]
        rw [sum_comm (s := A) (t := B)
          (f := fun a b => k a b * (P * ((1 - θ) * (Y b / SY))))]
        congr 1
        · refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
          ring
        · refine sum_congr rfl fun b _ => sum_congr rfl fun a _ => ?_
          ring
    _ ≤ P * (θ / SX * ∑ a ∈ A, X a * c) + P * ((1 - θ) / SY * ∑ b ∈ B, Y b * c) := by
        gcongr with a ha b hb
        · exact hX a
        · exact hrow a ha
        · exact hY b
        · exact hcol b hb
    _ = c * P := by
        rw [← sum_mul, ← sum_mul]
        field_simp
        ring

/-! ### Windows -/

/-- Inside one window, `x_n = 2^(s n) μ_n` is dominated by a geometric sequence ending at the
largest index, so the `θ`-th powers sum to at most a constant times the `θ`-th power of the sum. -/
theorem sum_window_geometric {s θ : ℝ} (hs : 0 < s) (hθ : 0 < θ) (μ : ℤ → ℝ) (S : Finset ℤ)
    (w : ℤ) (hS : ∀ n ∈ S, 0 < μ n ∧ Int.log 2 (μ n) = w) :
    ∑ n ∈ S, ((2 : ℝ) ^ (s * n) * μ n) ^ θ ≤
      2 ^ θ * (1 - (2 : ℝ) ^ (-(s * θ)))⁻¹ * (∑ n ∈ S, (2 : ℝ) ^ (s * n) * μ n) ^ θ := by
  classical
  set ρ : ℝ := (2 : ℝ) ^ (-(s * θ))
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith)
  have hx : ∀ n, 0 ≤ μ n → 0 ≤ (2 : ℝ) ^ (s * n) * μ n := fun n h => by positivity
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [sum_empty]
    rw [Real.zero_rpow hθ.ne']
    simp
  set n₀ := S.max' hne
  have hn₀ : n₀ ∈ S := S.max'_mem hne
  set x₀ := (2 : ℝ) ^ (s * n₀) * μ n₀
  have hx₀ : 0 ≤ x₀ := hx n₀ (hS n₀ hn₀).1.le
  -- comparison with the last index
  have hcmp : ∀ n ∈ S, ((2 : ℝ) ^ (s * n) * μ n) ^ θ ≤ 2 ^ θ * x₀ ^ θ * ρ ^ (n₀ - n).toNat := by
    intro n hn
    obtain ⟨hμn, hwn⟩ := hS n hn
    obtain ⟨hμ0, hw0⟩ := hS n₀ hn₀
    have hle : n ≤ n₀ := S.le_max' n hn
    have h1 : μ n < 2 * μ n₀ := by
      have a1 := Int.lt_zpow_succ_log_self (R := ℝ) (b := 2) (by norm_num) (μ n)
      have a2 := Int.zpow_log_le_self (R := ℝ) (b := 2) (by norm_num) hμ0
      push_cast at a1 a2
      rw [hwn, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one] at a1
      rw [hw0] at a2
      linarith
    have hk : ((n₀ - n).toNat : ℝ) = (n₀ : ℝ) - n := by
      have : ((n₀ - n).toNat : ℤ) = n₀ - n := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    have h2 : (2 : ℝ) ^ (s * n) * μ n ≤ 2 * x₀ * (2 : ℝ) ^ (-(s * (n₀ - n).toNat)) := by
      have e : (2 : ℝ) ^ (s * n) = (2 : ℝ) ^ (s * n₀) * (2 : ℝ) ^ (-(s * (n₀ - n).toNat)) := by
        rw [← Real.rpow_add (by norm_num), hk]
        congr 1
        ring
      rw [e]
      have : 0 < (2 : ℝ) ^ (s * n₀) * (2 : ℝ) ^ (-(s * (n₀ - n).toNat)) := by positivity
      calc (2 : ℝ) ^ (s * n₀) * (2 : ℝ) ^ (-(s * (n₀ - n).toNat)) * μ n
          ≤ (2 : ℝ) ^ (s * n₀) * (2 : ℝ) ^ (-(s * (n₀ - n).toNat)) * (2 * μ n₀) := by gcongr
        _ = 2 * x₀ * (2 : ℝ) ^ (-(s * (n₀ - n).toNat)) := by simp only [x₀]; ring
    calc ((2 : ℝ) ^ (s * n) * μ n) ^ θ
        ≤ (2 * x₀ * (2 : ℝ) ^ (-(s * (n₀ - n).toNat))) ^ θ := by
          gcongr
      _ = 2 ^ θ * x₀ ^ θ * ρ ^ (n₀ - n).toNat := by
          rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num) hx₀,
            ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          congr 2
          ring
  have hinj : Set.InjOn (fun n => (n₀ - n).toNat) S := by
    intro a ha b hb hab
    have := S.le_max' a ha
    have := S.le_max' b hb
    simp only at hab
    omega
  calc ∑ n ∈ S, ((2 : ℝ) ^ (s * n) * μ n) ^ θ
      ≤ ∑ n ∈ S, 2 ^ θ * x₀ ^ θ * ρ ^ (n₀ - n).toNat := sum_le_sum hcmp
    _ = 2 ^ θ * x₀ ^ θ * ∑ k ∈ S.image (fun n => (n₀ - n).toNat), ρ ^ k := by
        rw [← mul_sum, sum_image hinj]
    _ ≤ 2 ^ θ * x₀ ^ θ * (1 - ρ)⁻¹ := by
        gcongr
        exact sum_pow_le_inv_one_sub hρ0 hρ1 _
    _ ≤ 2 ^ θ * (∑ n ∈ S, (2 : ℝ) ^ (s * n) * μ n) ^ θ * (1 - ρ)⁻¹ := by
        have : 0 ≤ (1 - ρ)⁻¹ := inv_nonneg.2 (by linarith)
        gcongr
        exact single_le_sum (f := fun n : ℤ => (2 : ℝ) ^ (s * n) * μ n)
          (fun n hn => hx n (hS n hn).1.le) hn₀
    _ = _ := by ring

/-! ### Weights -/

/-- The pair weight `min(a/b, b/a)`, set to `0` unless both arguments are positive. -/
noncomputable def pairWeight (a b : ℝ) : ℝ := if 0 < a ∧ 0 < b then min (a / b) (b / a) else 0

lemma pairWeight_nonneg (a b : ℝ) : 0 ≤ pairWeight a b := by
  unfold pairWeight
  split_ifs with h
  · exact le_min (div_nonneg h.1.le h.2.le) (div_nonneg h.2.le h.1.le)
  · exact le_rfl

lemma pairWeight_comm (a b : ℝ) : pairWeight a b = pairWeight b a := by
  unfold pairWeight
  simp only [and_comm, min_comm]

private lemma pairWeight_rpow_le_of_le {γ : ℝ} (hγ : 0 < γ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) :
    pairWeight a b ^ γ ≤ 2 ^ γ * ((2 : ℝ) ^ (-γ)) ^ (Int.log 2 a - Int.log 2 b).natAbs := by
  have hw : Int.log 2 a ≤ Int.log 2 b := Int.log_mono_right ha hab
  have hj : (((Int.log 2 a - Int.log 2 b).natAbs : ℕ) : ℝ) = (Int.log 2 b : ℝ) - Int.log 2 a := by
    rw [Nat.cast_natAbs, abs_of_nonpos (by omega : Int.log 2 a - Int.log 2 b ≤ 0)]
    push_cast
    ring
  have h1 : a < (2 : ℝ) ^ (Int.log 2 a + 1) := Int.lt_zpow_succ_log_self (by norm_num) a
  have h2 : (2 : ℝ) ^ Int.log 2 b ≤ b := Int.zpow_log_le_self (by norm_num) hb
  have hpw : pairWeight a b ≤ a / b := by
    unfold pairWeight
    simp only [ha, hb, and_self, ↓reduceIte]
    exact min_le_left _ _
  have hab' : a / b ≤ (2 : ℝ) ^ ((Int.log 2 a + 1 - Int.log 2 b : ℤ) : ℝ) := by
    rw [Real.rpow_intCast, zpow_sub₀ (by norm_num)]
    have : (0 : ℝ) < 2 ^ Int.log 2 b := by positivity
    rw [div_le_div_iff₀ hb this]
    calc a * 2 ^ Int.log 2 b ≤ 2 ^ (Int.log 2 a + 1) * 2 ^ Int.log 2 b := by gcongr
      _ ≤ 2 ^ (Int.log 2 a + 1) * b := by gcongr
  calc pairWeight a b ^ γ ≤ (a / b) ^ γ := by
        gcongr
        exact pairWeight_nonneg a b
    _ ≤ ((2 : ℝ) ^ ((Int.log 2 a + 1 - Int.log 2 b : ℤ) : ℝ)) ^ γ := by
        gcongr
    _ = 2 ^ γ * ((2 : ℝ) ^ (-γ)) ^ (Int.log 2 a - Int.log 2 b).natAbs := by
        rw [← Real.rpow_mul (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_add (by norm_num), hj]
        congr 1
        push_cast
        ring

/-- Windows control the pair weight: `min(a/b,b/a)^γ ≤ 2^γ (2^(-γ))^|w(a) - w(b)|`. -/
theorem pairWeight_rpow_le {γ : ℝ} (hγ : 0 < γ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    pairWeight a b ^ γ ≤ 2 ^ γ * ((2 : ℝ) ^ (-γ)) ^ (Int.log 2 a - Int.log 2 b).natAbs := by
  rcases le_total a b with hab | hab
  · exact pairWeight_rpow_le_of_le hγ ha hb hab
  · rw [pairWeight_comm, ← Int.natAbs_neg, neg_sub]
    exact pairWeight_rpow_le_of_le hγ hb ha hab

/-! ### Regrouping by windows -/

/-- Regroup a double sum whose kernel depends only on the windows `f n`, `g m`. -/
lemma sum_sum_eq_sum_sum_fiberwise (S T : Finset ℤ) (f g : ℤ → ℤ) (G : ℤ → ℤ → ℝ)
    (u v : ℤ → ℝ) :
    ∑ n ∈ S, ∑ m ∈ T, G (f n) (g m) * (u n * v m) =
      ∑ a ∈ S.image f, ∑ b ∈ T.image g,
        G a b * ((∑ n ∈ S with f n = a, u n) * (∑ m ∈ T with g m = b, v m)) := by
  classical
  calc ∑ n ∈ S, ∑ m ∈ T, G (f n) (g m) * (u n * v m)
      = ∑ n ∈ S, ∑ b ∈ T.image g, ∑ m ∈ T with g m = b, G (f n) (g m) * (u n * v m) := by
        refine sum_congr rfl fun n _ => ?_
        rw [sum_fiberwise_of_maps_to (fun m hm => mem_image_of_mem g hm)]
    _ = ∑ a ∈ S.image f, ∑ n ∈ S with f n = a, ∑ b ∈ T.image g, ∑ m ∈ T with g m = b,
          G (f n) (g m) * (u n * v m) :=
        (sum_fiberwise_of_maps_to (fun n hn => mem_image_of_mem f hn) _).symm
    _ = ∑ a ∈ S.image f, ∑ b ∈ T.image g, ∑ n ∈ S with f n = a, ∑ m ∈ T with g m = b,
          G a b * (u n * v m) := by
        refine sum_congr rfl fun a _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun b _ => sum_congr rfl fun n hn => sum_congr rfl fun m hm => ?_
        rw [(mem_filter.1 hn).2, (mem_filter.1 hm).2]
    _ = _ := by
        refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
        rw [sum_mul_sum, mul_sum]
        refine sum_congr rfl fun n _ => ?_
        rw [mul_sum]

/-! ### D1 -/

/-- The constant of D1. -/
noncomputable def d1Const (p₁ p₂ θ γ : ℝ) : ℝ :=
  2 ^ γ * (2 ^ θ * (1 - (2 : ℝ) ^ (-(p₁ * θ)))⁻¹) *
    (2 ^ (1 - θ) * (1 - (2 : ℝ) ^ (-(p₂ * (1 - θ))))⁻¹) * (2 * (1 - (2 : ℝ) ^ (-γ))⁻¹)

lemma two_rpow_neg_lt_one {t : ℝ} (ht : 0 < t) : (2 : ℝ) ^ (-t) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

lemma d1Const_nonneg {p₁ p₂ θ γ : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hγ : 0 < γ) : 0 ≤ d1Const p₁ p₂ θ γ := by
  have h1 := two_rpow_neg_lt_one (mul_pos hp₁ hθ₀)
  have h2 := two_rpow_neg_lt_one (mul_pos hp₂ (sub_pos.2 hθ₁))
  have h3 := two_rpow_neg_lt_one hγ
  unfold d1Const
  have : 0 ≤ (1 - (2 : ℝ) ^ (-(p₁ * θ)))⁻¹ := inv_nonneg.2 (by linarith)
  have : 0 ≤ (1 - (2 : ℝ) ^ (-(p₂ * (1 - θ))))⁻¹ := inv_nonneg.2 (by linarith)
  have : 0 ≤ (1 - (2 : ℝ) ^ (-γ))⁻¹ := inv_nonneg.2 (by linarith)
  positivity

/-- **D1** (pair lemma). With `x_n = 2^(p₁ n) μ₁(n)`, `y_m = 2^(p₂ m) μ₂(m)`, `0 < θ < 1`, `γ > 0`:
`Σ_{n,m} x_n^θ y_m^(1-θ) min(μ₁(n)/μ₂(m), μ₂(m)/μ₁(n))^γ ≤ C (Σ x_n)^θ (Σ y_m)^(1-θ)`. -/
theorem d1 {p₁ p₂ θ γ : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hγ : 0 < γ) (μ₁ μ₂ : ℤ → ℝ) (hμ₁ : ∀ n, 0 ≤ μ₁ n) (hμ₂ : ∀ m, 0 ≤ μ₂ m)
    (S T : Finset ℤ) :
    ∑ n ∈ S, ∑ m ∈ T, ((2 : ℝ) ^ (p₁ * n) * μ₁ n) ^ θ * ((2 : ℝ) ^ (p₂ * m) * μ₂ m) ^ (1 - θ) *
        pairWeight (μ₁ n) (μ₂ m) ^ γ ≤
      d1Const p₁ p₂ θ γ * ((∑ n ∈ S, (2 : ℝ) ^ (p₁ * n) * μ₁ n) ^ θ *
        (∑ m ∈ T, (2 : ℝ) ^ (p₂ * m) * μ₂ m) ^ (1 - θ)) := by
  classical
  set x : ℤ → ℝ := fun n => (2 : ℝ) ^ (p₁ * n) * μ₁ n with hxdef
  set y : ℤ → ℝ := fun m => (2 : ℝ) ^ (p₂ * m) * μ₂ m with hydef
  have hx : ∀ n, 0 ≤ x n := fun n => by simp only [x]; exact mul_nonneg (by positivity) (hμ₁ n)
  have hy : ∀ m, 0 ≤ y m := fun m => by simp only [y]; exact mul_nonneg (by positivity) (hμ₂ m)
  have hθ' : 0 < 1 - θ := sub_pos.2 hθ₁
  set ρ : ℝ := (2 : ℝ) ^ (-γ)
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := two_rpow_neg_lt_one hγ
  set w₁ : ℤ → ℤ := fun n => Int.log 2 (μ₁ n)
  set w₂ : ℤ → ℤ := fun m => Int.log 2 (μ₂ m)
  set S' := S.filter (fun n => 0 < μ₁ n)
  set T' := T.filter (fun m => 0 < μ₂ m)
  set c₁ : ℝ := 2 ^ θ * (1 - (2 : ℝ) ^ (-(p₁ * θ)))⁻¹
  set c₂ : ℝ := 2 ^ (1 - θ) * (1 - (2 : ℝ) ^ (-(p₂ * (1 - θ))))⁻¹
  have hc₁ : 0 ≤ c₁ := by
    have := two_rpow_neg_lt_one (mul_pos hp₁ hθ₀)
    have : 0 ≤ (1 - (2 : ℝ) ^ (-(p₁ * θ)))⁻¹ := inv_nonneg.2 (by linarith)
    positivity
  have hc₂ : 0 ≤ c₂ := by
    have := two_rpow_neg_lt_one (mul_pos hp₂ hθ')
    have : 0 ≤ (1 - (2 : ℝ) ^ (-(p₂ * (1 - θ))))⁻¹ := inv_nonneg.2 (by linarith)
    positivity
  set κ : ℝ := 2 * (1 - ρ)⁻¹
  have hκ : 0 ≤ κ := by have : 0 ≤ (1 - ρ)⁻¹ := inv_nonneg.2 (by linarith); positivity
  -- Step 1: only positive entries contribute.
  have hzero : ∀ n m, ¬ (0 < μ₁ n ∧ 0 < μ₂ m) →
      x n ^ θ * y m ^ (1 - θ) * pairWeight (μ₁ n) (μ₂ m) ^ γ = 0 := by
    intro n m h
    unfold pairWeight
    simp only [h, ↓reduceIte, Real.zero_rpow hγ.ne', mul_zero]
  have step1 : ∑ n ∈ S, ∑ m ∈ T, x n ^ θ * y m ^ (1 - θ) * pairWeight (μ₁ n) (μ₂ m) ^ γ =
      ∑ n ∈ S', ∑ m ∈ T', x n ^ θ * y m ^ (1 - θ) * pairWeight (μ₁ n) (μ₂ m) ^ γ := by
    rw [sum_filter_of_ne]
    · refine sum_congr rfl fun n hn => ?_
      rw [sum_filter_of_ne]
      intro m _ hne
      by_contra hm
      exact hne (hzero n m fun h => hm h.2)
    · intro n _ hne
      by_contra hn
      exact hne (sum_eq_zero fun m _ => hzero n m fun h => hn h.1)
  -- Step 2: windows.
  have step2 : ∑ n ∈ S', ∑ m ∈ T', x n ^ θ * y m ^ (1 - θ) * pairWeight (μ₁ n) (μ₂ m) ^ γ ≤
      2 ^ γ * ∑ n ∈ S', ∑ m ∈ T', ρ ^ (w₁ n - w₂ m).natAbs * (x n ^ θ * y m ^ (1 - θ)) := by
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    rw [mul_sum]
    refine sum_le_sum fun m hm => ?_
    have h := pairWeight_rpow_le hγ (mem_filter.1 hn).2 (mem_filter.1 hm).2
    have : 0 ≤ x n ^ θ * y m ^ (1 - θ) := by
      have := hx n; have := hy m; positivity
    calc x n ^ θ * y m ^ (1 - θ) * pairWeight (μ₁ n) (μ₂ m) ^ γ
        ≤ x n ^ θ * y m ^ (1 - θ) * (2 ^ γ * ρ ^ (w₁ n - w₂ m).natAbs) :=
          mul_le_mul_of_nonneg_left h this
      _ = _ := by ring
  -- Step 3: regroup and use the geometric bound in each window.
  set X : ℤ → ℝ := fun a => ∑ n ∈ S' with w₁ n = a, x n
  set Y : ℤ → ℝ := fun b => ∑ m ∈ T' with w₂ m = b, y m
  have hX : ∀ a, 0 ≤ X a := fun a => sum_nonneg fun n _ => hx n
  have hY : ∀ b, 0 ≤ Y b := fun b => sum_nonneg fun m _ => hy m
  have hwin₁ : ∀ a, ∑ n ∈ S' with w₁ n = a, x n ^ θ ≤ c₁ * X a ^ θ := by
    intro a
    exact sum_window_geometric hp₁ hθ₀ μ₁ _ a fun n hn =>
      ⟨(mem_filter.1 (mem_filter.1 hn).1).2, (mem_filter.1 hn).2⟩
  have hwin₂ : ∀ b, ∑ m ∈ T' with w₂ m = b, y m ^ (1 - θ) ≤ c₂ * Y b ^ (1 - θ) := by
    intro b
    exact sum_window_geometric hp₂ hθ' μ₂ _ b fun m hm =>
      ⟨(mem_filter.1 (mem_filter.1 hm).1).2, (mem_filter.1 hm).2⟩
  have step3 : ∑ n ∈ S', ∑ m ∈ T', ρ ^ (w₁ n - w₂ m).natAbs * (x n ^ θ * y m ^ (1 - θ)) ≤
      c₁ * c₂ * (κ * ((∑ a ∈ S'.image w₁, X a) ^ θ * (∑ b ∈ T'.image w₂, Y b) ^ (1 - θ))) := by
    rw [sum_sum_eq_sum_sum_fiberwise S' T' w₁ w₂ (fun a b => ρ ^ (a - b).natAbs)
      (fun n => x n ^ θ) (fun m => y m ^ (1 - θ))]
    calc ∑ a ∈ S'.image w₁, ∑ b ∈ T'.image w₂, ρ ^ (a - b).natAbs *
          ((∑ n ∈ S' with w₁ n = a, x n ^ θ) * (∑ m ∈ T' with w₂ m = b, y m ^ (1 - θ)))
        ≤ ∑ a ∈ S'.image w₁, ∑ b ∈ T'.image w₂, ρ ^ (a - b).natAbs *
          ((c₁ * X a ^ θ) * (c₂ * Y b ^ (1 - θ))) := by
          refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hρ0 _)
          exact mul_le_mul (hwin₁ a) (hwin₂ b) (sum_nonneg fun m _ => by have := hy m; positivity)
            (by have := hX a; positivity)
      _ = c₁ * c₂ * ∑ a ∈ S'.image w₁, ∑ b ∈ T'.image w₂, ρ ^ (a - b).natAbs *
          (X a ^ θ * Y b ^ (1 - θ)) := by
          rw [mul_sum]
          refine sum_congr rfl fun a _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun b _ => ?_
          ring
      _ ≤ _ := by
          gcongr
          refine sum_sum_mul_rpow_le _ _ _ X Y hθ₀ hθ₁ hκ (fun a b => pow_nonneg hρ0 _) hX hY
            (fun a _ => sum_pow_natAbs_sub_le hρ0 hρ1 a _) (fun b _ => ?_)
          calc ∑ a ∈ S'.image w₁, ρ ^ (a - b).natAbs
              = ∑ a ∈ S'.image w₁, ρ ^ (b - a).natAbs := by
                refine sum_congr rfl fun a _ => ?_
                rw [← Int.natAbs_neg, neg_sub]
            _ ≤ κ := sum_pow_natAbs_sub_le hρ0 hρ1 b _
  -- Step 4: the window sums add up to at most the full sums.
  have hsumX : ∑ a ∈ S'.image w₁, X a ≤ ∑ n ∈ S, x n := by
    rw [sum_fiberwise_of_maps_to (fun n hn => mem_image_of_mem w₁ hn)]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n _ _ => hx n
  have hsumY : ∑ b ∈ T'.image w₂, Y b ≤ ∑ m ∈ T, y m := by
    rw [sum_fiberwise_of_maps_to (fun m hm => mem_image_of_mem w₂ hm)]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun m _ _ => hy m
  have hX0 : 0 ≤ ∑ a ∈ S'.image w₁, X a := sum_nonneg fun a _ => hX a
  have hY0 : 0 ≤ ∑ b ∈ T'.image w₂, Y b := sum_nonneg fun b _ => hY b
  calc ∑ n ∈ S, ∑ m ∈ T, x n ^ θ * y m ^ (1 - θ) * pairWeight (μ₁ n) (μ₂ m) ^ γ
      ≤ 2 ^ γ * (c₁ * c₂ * (κ * ((∑ a ∈ S'.image w₁, X a) ^ θ *
          (∑ b ∈ T'.image w₂, Y b) ^ (1 - θ)))) := by
        rw [step1]
        refine step2.trans ?_
        gcongr
    _ ≤ 2 ^ γ * (c₁ * c₂ * (κ * ((∑ n ∈ S, x n) ^ θ * (∑ m ∈ T, y m) ^ (1 - θ)))) := by
        have : 0 ≤ (∑ n ∈ S, x n) ^ θ := Real.rpow_nonneg (sum_nonneg fun n _ => hx n) _
        gcongr
    _ = _ := by
        simp only [d1Const, c₁, c₂, κ, ρ, x, y]
        ring

/-! ### D2 -/

/-- Three-factor Hölder against a kernel whose three "row sums" are bounded by `c`. -/
theorem sum_sum_sum_mul_rpow_le {ι κ ι' : Type*} (A : Finset ι) (B : Finset κ) (C : Finset ι')
    (k : ι → κ → ι' → ℝ) (X : ι → ℝ) (Y : κ → ℝ) (Z : ι' → ℝ) {θ₁ θ₂ θ₃ c : ℝ}
    (h₁ : 0 < θ₁) (h₂ : 0 < θ₂) (h₃ : 0 < θ₃) (hθ : θ₁ + θ₂ + θ₃ = 1) (hc : 0 ≤ c)
    (hk : ∀ a b d, 0 ≤ k a b d) (hX : ∀ a, 0 ≤ X a) (hY : ∀ b, 0 ≤ Y b) (hZ : ∀ d, 0 ≤ Z d)
    (hrow₁ : ∀ a ∈ A, ∑ b ∈ B, ∑ d ∈ C, k a b d ≤ c)
    (hrow₂ : ∀ b ∈ B, ∑ a ∈ A, ∑ d ∈ C, k a b d ≤ c)
    (hrow₃ : ∀ d ∈ C, ∑ a ∈ A, ∑ b ∈ B, k a b d ≤ c) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ d ∈ C, k a b d * (X a ^ θ₁ * Y b ^ θ₂ * Z d ^ θ₃) ≤
      c * ((∑ a ∈ A, X a) ^ θ₁ * (∑ b ∈ B, Y b) ^ θ₂ * (∑ d ∈ C, Z d) ^ θ₃) := by
  set SX := ∑ a ∈ A, X a
  set SY := ∑ b ∈ B, Y b
  set SZ := ∑ d ∈ C, Z d
  have hSX : 0 ≤ SX := sum_nonneg fun a _ => hX a
  have hSY : 0 ≤ SY := sum_nonneg fun b _ => hY b
  have hSZ : 0 ≤ SZ := sum_nonneg fun d _ => hZ d
  have hR : 0 ≤ c * (SX ^ θ₁ * SY ^ θ₂ * SZ ^ θ₃) := by positivity
  rcases hSX.eq_or_lt with h0 | hSX0
  · have h0 : ∀ a ∈ A, X a = 0 := (sum_eq_zero_iff_of_nonneg fun a _ => hX a).1 h0.symm
    refine le_trans (le_of_eq ?_) hR
    refine sum_eq_zero fun a ha => sum_eq_zero fun b _ => sum_eq_zero fun d _ => ?_
    rw [h0 a ha, Real.zero_rpow h₁.ne']
    ring
  rcases hSY.eq_or_lt with h0 | hSY0
  · have h0 : ∀ b ∈ B, Y b = 0 := (sum_eq_zero_iff_of_nonneg fun b _ => hY b).1 h0.symm
    refine le_trans (le_of_eq ?_) hR
    refine sum_eq_zero fun a _ => sum_eq_zero fun b hb => sum_eq_zero fun d _ => ?_
    rw [h0 b hb, Real.zero_rpow h₂.ne']
    ring
  rcases hSZ.eq_or_lt with h0 | hSZ0
  · have h0 : ∀ d ∈ C, Z d = 0 := (sum_eq_zero_iff_of_nonneg fun d _ => hZ d).1 h0.symm
    refine le_trans (le_of_eq ?_) hR
    refine sum_eq_zero fun a _ => sum_eq_zero fun b _ => sum_eq_zero fun d hd => ?_
    rw [h0 d hd, Real.zero_rpow h₃.ne']
    ring
  set P := SX ^ θ₁ * SY ^ θ₂ * SZ ^ θ₃
  have hP : 0 < P := by positivity
  have hpt : ∀ a b d, X a ^ θ₁ * Y b ^ θ₂ * Z d ^ θ₃ ≤
      P * (θ₁ * (X a / SX)) + P * (θ₂ * (Y b / SY)) + P * (θ₃ * (Z d / SZ)) := by
    intro a b d
    have h := Real.geom_mean_le_arith_mean3_weighted h₁.le h₂.le h₃.le
      (div_nonneg (hX a) hSX) (div_nonneg (hY b) hSY) (div_nonneg (hZ d) hSZ) hθ
    rw [Real.div_rpow (hX a) hSX, Real.div_rpow (hY b) hSY, Real.div_rpow (hZ d) hSZ] at h
    have : 0 < SX ^ θ₁ := by positivity
    have : 0 < SY ^ θ₂ := by positivity
    have : 0 < SZ ^ θ₃ := by positivity
    calc X a ^ θ₁ * Y b ^ θ₂ * Z d ^ θ₃
        = P * (X a ^ θ₁ / SX ^ θ₁ * (Y b ^ θ₂ / SY ^ θ₂) * (Z d ^ θ₃ / SZ ^ θ₃)) := by
          simp only [P]; field_simp
      _ ≤ P * (θ₁ * (X a / SX) + θ₂ * (Y b / SY) + θ₃ * (Z d / SZ)) := by gcongr
      _ = _ := by ring
  -- the three pieces
  have hS1 : ∑ a ∈ A, ∑ b ∈ B, ∑ d ∈ C, k a b d * (P * (θ₁ * (X a / SX))) ≤ P * (c * θ₁) := by
    simp_rw [← sum_mul]
    calc ∑ a ∈ A, (∑ b ∈ B, ∑ d ∈ C, k a b d) * (P * (θ₁ * (X a / SX)))
        ≤ ∑ a ∈ A, c * (P * (θ₁ * (X a / SX))) := by
          refine sum_le_sum fun a ha => ?_
          have := hX a
          gcongr
          exact hrow₁ a ha
      _ = P * (c * θ₁) := by
          rw [← mul_sum, ← mul_sum, ← mul_sum, ← sum_div]
          field_simp
          rfl
  have hS2 : ∑ a ∈ A, ∑ b ∈ B, ∑ d ∈ C, k a b d * (P * (θ₂ * (Y b / SY))) ≤ P * (c * θ₂) := by
    simp_rw [← sum_mul]
    rw [sum_comm]
    simp_rw [← sum_mul]
    calc ∑ b ∈ B, (∑ a ∈ A, ∑ d ∈ C, k a b d) * (P * (θ₂ * (Y b / SY)))
        ≤ ∑ b ∈ B, c * (P * (θ₂ * (Y b / SY))) := by
          refine sum_le_sum fun b hb => ?_
          have := hY b
          gcongr
          exact hrow₂ b hb
      _ = P * (c * θ₂) := by
          rw [← mul_sum, ← mul_sum, ← mul_sum, ← sum_div]
          field_simp
          rfl
  have hS3 : ∑ a ∈ A, ∑ b ∈ B, ∑ d ∈ C, k a b d * (P * (θ₃ * (Z d / SZ))) ≤ P * (c * θ₃) := by
    have e : ∑ a ∈ A, ∑ b ∈ B, ∑ d ∈ C, k a b d * (P * (θ₃ * (Z d / SZ))) =
        ∑ d ∈ C, (∑ a ∈ A, ∑ b ∈ B, k a b d) * (P * (θ₃ * (Z d / SZ))) := by
      calc ∑ a ∈ A, ∑ b ∈ B, ∑ d ∈ C, k a b d * (P * (θ₃ * (Z d / SZ)))
          = ∑ a ∈ A, ∑ d ∈ C, ∑ b ∈ B, k a b d * (P * (θ₃ * (Z d / SZ))) :=
            sum_congr rfl fun a _ => sum_comm
        _ = ∑ d ∈ C, ∑ a ∈ A, ∑ b ∈ B, k a b d * (P * (θ₃ * (Z d / SZ))) := sum_comm
        _ = _ := by
            refine sum_congr rfl fun d _ => ?_
            rw [sum_mul]
            refine sum_congr rfl fun a _ => ?_
            rw [sum_mul]
    rw [e]
    calc ∑ d ∈ C, (∑ a ∈ A, ∑ b ∈ B, k a b d) * (P * (θ₃ * (Z d / SZ)))
        ≤ ∑ d ∈ C, c * (P * (θ₃ * (Z d / SZ))) := by
          refine sum_le_sum fun d hd => ?_
          have := hZ d
          gcongr
          exact hrow₃ d hd
      _ = P * (c * θ₃) := by
          rw [← mul_sum, ← mul_sum, ← mul_sum, ← sum_div]
          field_simp
          rfl
  calc ∑ a ∈ A, ∑ b ∈ B, ∑ d ∈ C, k a b d * (X a ^ θ₁ * Y b ^ θ₂ * Z d ^ θ₃)
      ≤ ∑ a ∈ A, ∑ b ∈ B, ∑ d ∈ C, k a b d *
          (P * (θ₁ * (X a / SX)) + P * (θ₂ * (Y b / SY)) + P * (θ₃ * (Z d / SZ))) :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => sum_le_sum fun d _ =>
          mul_le_mul_of_nonneg_left (hpt a b d) (hk a b d)
    _ = ∑ a ∈ A, ∑ b ∈ B, ∑ d ∈ C, k a b d * (P * (θ₁ * (X a / SX))) +
          ∑ a ∈ A, ∑ b ∈ B, ∑ d ∈ C, k a b d * (P * (θ₂ * (Y b / SY))) +
          ∑ a ∈ A, ∑ b ∈ B, ∑ d ∈ C, k a b d * (P * (θ₃ * (Z d / SZ))) := by
        simp only [mul_add, sum_add_distrib]
    _ ≤ P * (c * θ₁) + P * (c * θ₂) + P * (c * θ₃) := by gcongr
    _ = c * P := by
        have : P * (c * θ₁) + P * (c * θ₂) + P * (c * θ₃) = c * P * (θ₁ + θ₂ + θ₃) := by ring
        rw [this, hθ, mul_one]

/-- Regroup a triple sum whose kernel depends only on the windows. -/
lemma sum_sum_sum_eq_fiberwise (S T U : Finset ℤ) (f g h : ℤ → ℤ) (G : ℤ → ℤ → ℤ → ℝ)
    (u v z : ℤ → ℝ) :
    ∑ n ∈ S, ∑ m ∈ T, ∑ k ∈ U, G (f n) (g m) (h k) * (u n * v m * z k) =
      ∑ a ∈ S.image f, ∑ b ∈ T.image g, ∑ c ∈ U.image h,
        G a b c * ((∑ n ∈ S with f n = a, u n) * (∑ m ∈ T with g m = b, v m) *
          (∑ k ∈ U with h k = c, z k)) := by
  classical
  set Φ : ℤ → ℝ := fun a => ∑ b ∈ T.image g, ∑ c ∈ U.image h,
    G a b c * ((∑ m ∈ T with g m = b, v m) * (∑ k ∈ U with h k = c, z k))
  calc ∑ n ∈ S, ∑ m ∈ T, ∑ k ∈ U, G (f n) (g m) (h k) * (u n * v m * z k)
      = ∑ n ∈ S, u n * Φ (f n) := by
        refine sum_congr rfl fun n _ => ?_
        simp only [Φ]
        rw [← sum_sum_eq_sum_sum_fiberwise T U g h (G (f n)) v z, mul_sum]
        refine sum_congr rfl fun m _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun k _ => ?_
        ring
    _ = ∑ a ∈ S.image f, (∑ n ∈ S with f n = a, u n) * Φ a := by
        rw [← sum_fiberwise_of_maps_to (fun n hn => mem_image_of_mem f hn)]
        refine sum_congr rfl fun a _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun n hn => ?_
        rw [(mem_filter.1 hn).2]
    _ = _ := by
        refine sum_congr rfl fun a _ => ?_
        simp only [Φ]
        rw [mul_sum]
        refine sum_congr rfl fun b _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun c _ => ?_
        ring

/-- The constant of D2. -/
noncomputable def d2Const (p₁ p₂ p₃ γ : ℝ) : ℝ :=
  2 ^ γ * 2 ^ γ * (2 ^ (1 / p₁) * (1 - (2 : ℝ) ^ (-(p₁ * (1 / p₁))))⁻¹) *
    (2 ^ (1 / p₂) * (1 - (2 : ℝ) ^ (-(p₂ * (1 / p₂))))⁻¹) *
    (2 ^ (1 / p₃) * (1 - (2 : ℝ) ^ (-(p₃ * (1 / p₃))))⁻¹) *
    ((2 * (1 - (2 : ℝ) ^ (-γ))⁻¹) * (2 * (1 - (2 : ℝ) ^ (-γ))⁻¹))

lemma d2Const_nonneg {p₁ p₂ p₃ γ : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hp₃ : 0 < p₃)
    (hγ : 0 < γ) : 0 ≤ d2Const p₁ p₂ p₃ γ := by
  have h1 := two_rpow_neg_lt_one (mul_pos hp₁ (one_div_pos.2 hp₁))
  have h2 := two_rpow_neg_lt_one (mul_pos hp₂ (one_div_pos.2 hp₂))
  have h3 := two_rpow_neg_lt_one (mul_pos hp₃ (one_div_pos.2 hp₃))
  have h4 := two_rpow_neg_lt_one hγ
  have : 0 ≤ (1 - (2 : ℝ) ^ (-(p₁ * (1 / p₁))))⁻¹ := inv_nonneg.2 (by linarith)
  have : 0 ≤ (1 - (2 : ℝ) ^ (-(p₂ * (1 / p₂))))⁻¹ := inv_nonneg.2 (by linarith)
  have : 0 ≤ (1 - (2 : ℝ) ^ (-(p₃ * (1 / p₃))))⁻¹ := inv_nonneg.2 (by linarith)
  have : 0 ≤ (1 - (2 : ℝ) ^ (-γ))⁻¹ := inv_nonneg.2 (by linarith)
  unfold d2Const
  positivity

/-- **D2** (triple lemma), with the weight `pairWeight(μ₁,μ₂)^γ · pairWeight(μ₁,μ₃)^γ`
(this dominates the blueprint's `(μ_min/μ_max)^(2γ)`, see `tripleWeight_le_pairWeight`). With
`x_n = 2^(p₁ n) μ₁(n)` etc. and `Σ 1/p_i = 1`:
`Σ x_n^(1/p₁) y_m^(1/p₂) z_k^(1/p₃) W ≤ C (Σ x)^(1/p₁) (Σ y)^(1/p₂) (Σ z)^(1/p₃)`. -/
theorem d2 {p₁ p₂ p₃ γ : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hp₃ : 0 < p₃)
    (hp : 1 / p₁ + 1 / p₂ + 1 / p₃ = 1) (hγ : 0 < γ) (μ₁ μ₂ μ₃ : ℤ → ℝ)
    (hμ₁ : ∀ n, 0 ≤ μ₁ n) (hμ₂ : ∀ m, 0 ≤ μ₂ m) (hμ₃ : ∀ k, 0 ≤ μ₃ k) (S T U : Finset ℤ) :
    ∑ n ∈ S, ∑ m ∈ T, ∑ k ∈ U, ((2 : ℝ) ^ (p₁ * n) * μ₁ n) ^ (1 / p₁) *
        ((2 : ℝ) ^ (p₂ * m) * μ₂ m) ^ (1 / p₂) * ((2 : ℝ) ^ (p₃ * k) * μ₃ k) ^ (1 / p₃) *
        (pairWeight (μ₁ n) (μ₂ m) ^ γ * pairWeight (μ₁ n) (μ₃ k) ^ γ) ≤
      d2Const p₁ p₂ p₃ γ * ((∑ n ∈ S, (2 : ℝ) ^ (p₁ * n) * μ₁ n) ^ (1 / p₁) *
        (∑ m ∈ T, (2 : ℝ) ^ (p₂ * m) * μ₂ m) ^ (1 / p₂) *
        (∑ k ∈ U, (2 : ℝ) ^ (p₃ * k) * μ₃ k) ^ (1 / p₃)) := by
  classical
  set x : ℤ → ℝ := fun n => (2 : ℝ) ^ (p₁ * n) * μ₁ n
  set y : ℤ → ℝ := fun m => (2 : ℝ) ^ (p₂ * m) * μ₂ m
  set z : ℤ → ℝ := fun k => (2 : ℝ) ^ (p₃ * k) * μ₃ k
  have hx : ∀ n, 0 ≤ x n := fun n => mul_nonneg (by positivity) (hμ₁ n)
  have hy : ∀ m, 0 ≤ y m := fun m => mul_nonneg (by positivity) (hμ₂ m)
  have hz : ∀ k, 0 ≤ z k := fun k => mul_nonneg (by positivity) (hμ₃ k)
  have hq₁ : 0 < 1 / p₁ := one_div_pos.2 hp₁
  have hq₂ : 0 < 1 / p₂ := one_div_pos.2 hp₂
  have hq₃ : 0 < 1 / p₃ := one_div_pos.2 hp₃
  set ρ : ℝ := (2 : ℝ) ^ (-γ)
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := two_rpow_neg_lt_one hγ
  set w₁ : ℤ → ℤ := fun n => Int.log 2 (μ₁ n)
  set w₂ : ℤ → ℤ := fun m => Int.log 2 (μ₂ m)
  set w₃ : ℤ → ℤ := fun k => Int.log 2 (μ₃ k)
  set S' := S.filter (fun n => 0 < μ₁ n)
  set T' := T.filter (fun m => 0 < μ₂ m)
  set U' := U.filter (fun k => 0 < μ₃ k)
  set c₁ : ℝ := 2 ^ (1 / p₁) * (1 - (2 : ℝ) ^ (-(p₁ * (1 / p₁))))⁻¹
  set c₂ : ℝ := 2 ^ (1 / p₂) * (1 - (2 : ℝ) ^ (-(p₂ * (1 / p₂))))⁻¹
  set c₃ : ℝ := 2 ^ (1 / p₃) * (1 - (2 : ℝ) ^ (-(p₃ * (1 / p₃))))⁻¹
  have hc : ∀ q : ℝ, 0 < q → 0 ≤ 2 ^ (1 / q) * (1 - (2 : ℝ) ^ (-(q * (1 / q))))⁻¹ := by
    intro q hq
    have := two_rpow_neg_lt_one (mul_pos hq (one_div_pos.2 hq))
    have : 0 ≤ (1 - (2 : ℝ) ^ (-(q * (1 / q))))⁻¹ := inv_nonneg.2 (by linarith)
    positivity
  have hc₁ : 0 ≤ c₁ := hc p₁ hp₁
  have hc₂ : 0 ≤ c₂ := hc p₂ hp₂
  have hc₃ : 0 ≤ c₃ := hc p₃ hp₃
  set κ : ℝ := 2 * (1 - ρ)⁻¹
  have hκ : 0 ≤ κ := by have : 0 ≤ (1 - ρ)⁻¹ := inv_nonneg.2 (by linarith); positivity
  set W : ℤ → ℤ → ℤ → ℝ := fun n m k => pairWeight (μ₁ n) (μ₂ m) ^ γ * pairWeight (μ₁ n) (μ₃ k) ^ γ
  have hzero : ∀ n m k, ¬ (0 < μ₁ n ∧ 0 < μ₂ m ∧ 0 < μ₃ k) →
      x n ^ (1 / p₁) * y m ^ (1 / p₂) * z k ^ (1 / p₃) * W n m k = 0 := by
    intro n m k h
    have : pairWeight (μ₁ n) (μ₂ m) = 0 ∨ pairWeight (μ₁ n) (μ₃ k) = 0 := by
      unfold pairWeight
      by_cases h1 : 0 < μ₁ n
      · by_cases h2 : 0 < μ₂ m
        · right; simp only [show ¬ (0 < μ₁ n ∧ 0 < μ₃ k) from fun h' => h ⟨h1, h2, h'.2⟩,
            ↓reduceIte]
        · left; simp only [h2, and_false, ↓reduceIte]
      · left; simp only [h1, false_and, ↓reduceIte]
    simp only [W]
    rcases this with h' | h' <;> rw [h', Real.zero_rpow hγ.ne'] <;> ring
  have step1 : ∑ n ∈ S, ∑ m ∈ T, ∑ k ∈ U, x n ^ (1 / p₁) * y m ^ (1 / p₂) * z k ^ (1 / p₃) *
      W n m k = ∑ n ∈ S', ∑ m ∈ T', ∑ k ∈ U',
        x n ^ (1 / p₁) * y m ^ (1 / p₂) * z k ^ (1 / p₃) * W n m k := by
    rw [sum_filter_of_ne]
    · refine sum_congr rfl fun n _ => ?_
      rw [sum_filter_of_ne]
      · refine sum_congr rfl fun m _ => ?_
        rw [sum_filter_of_ne]
        intro k _ hne
        by_contra hk
        exact hne (hzero n m k fun h => hk h.2.2)
      · intro m _ hne
        by_contra hm
        exact hne (sum_eq_zero fun k _ => hzero n m k fun h => hm h.2.1)
    · intro n _ hne
      by_contra hn
      exact hne (sum_eq_zero fun m _ => sum_eq_zero fun k _ => hzero n m k fun h => hn h.1)
  have step2 : ∑ n ∈ S', ∑ m ∈ T', ∑ k ∈ U',
      x n ^ (1 / p₁) * y m ^ (1 / p₂) * z k ^ (1 / p₃) * W n m k ≤
      2 ^ γ * 2 ^ γ * ∑ n ∈ S', ∑ m ∈ T', ∑ k ∈ U',
        (ρ ^ (w₁ n - w₂ m).natAbs * ρ ^ (w₁ n - w₃ k).natAbs) *
          (x n ^ (1 / p₁) * y m ^ (1 / p₂) * z k ^ (1 / p₃)) := by
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    rw [mul_sum]
    refine sum_le_sum fun m hm => ?_
    rw [mul_sum]
    refine sum_le_sum fun k hk => ?_
    have hn' := (mem_filter.1 hn).2
    have h12 := pairWeight_rpow_le hγ hn' (mem_filter.1 hm).2
    have h13 := pairWeight_rpow_le hγ hn' (mem_filter.1 hk).2
    have : 0 ≤ x n ^ (1 / p₁) * y m ^ (1 / p₂) * z k ^ (1 / p₃) := by
      have := hx n; have := hy m; have := hz k; positivity
    have hW : W n m k ≤ 2 ^ γ * ρ ^ (w₁ n - w₂ m).natAbs * (2 ^ γ * ρ ^ (w₁ n - w₃ k).natAbs) :=
      mul_le_mul h12 h13 (Real.rpow_nonneg (pairWeight_nonneg _ _) _) (by positivity)
    calc x n ^ (1 / p₁) * y m ^ (1 / p₂) * z k ^ (1 / p₃) * W n m k
        ≤ x n ^ (1 / p₁) * y m ^ (1 / p₂) * z k ^ (1 / p₃) *
            (2 ^ γ * ρ ^ (w₁ n - w₂ m).natAbs * (2 ^ γ * ρ ^ (w₁ n - w₃ k).natAbs)) :=
          mul_le_mul_of_nonneg_left hW this
      _ = _ := by ring
  set X : ℤ → ℝ := fun a => ∑ n ∈ S' with w₁ n = a, x n
  set Y : ℤ → ℝ := fun b => ∑ m ∈ T' with w₂ m = b, y m
  set Z : ℤ → ℝ := fun c => ∑ k ∈ U' with w₃ k = c, z k
  have hX : ∀ a, 0 ≤ X a := fun a => sum_nonneg fun n _ => hx n
  have hY : ∀ b, 0 ≤ Y b := fun b => sum_nonneg fun m _ => hy m
  have hZ : ∀ c, 0 ≤ Z c := fun c => sum_nonneg fun k _ => hz k
  have hwin₁ : ∀ a, ∑ n ∈ S' with w₁ n = a, x n ^ (1 / p₁) ≤ c₁ * X a ^ (1 / p₁) := fun a =>
    sum_window_geometric hp₁ hq₁ μ₁ _ a fun n hn =>
      ⟨(mem_filter.1 (mem_filter.1 hn).1).2, (mem_filter.1 hn).2⟩
  have hwin₂ : ∀ b, ∑ m ∈ T' with w₂ m = b, y m ^ (1 / p₂) ≤ c₂ * Y b ^ (1 / p₂) := fun b =>
    sum_window_geometric hp₂ hq₂ μ₂ _ b fun m hm =>
      ⟨(mem_filter.1 (mem_filter.1 hm).1).2, (mem_filter.1 hm).2⟩
  have hwin₃ : ∀ c, ∑ k ∈ U' with w₃ k = c, z k ^ (1 / p₃) ≤ c₃ * Z c ^ (1 / p₃) := fun c =>
    sum_window_geometric hp₃ hq₃ μ₃ _ c fun k hk =>
      ⟨(mem_filter.1 (mem_filter.1 hk).1).2, (mem_filter.1 hk).2⟩
  have hrowsum : ∀ (a : ℤ) (B : Finset ℤ), ∑ b ∈ B, ρ ^ (a - b).natAbs ≤ κ :=
    fun a B => sum_pow_natAbs_sub_le hρ0 hρ1 a B
  have hrowsum' : ∀ (b : ℤ) (A : Finset ℤ), ∑ a ∈ A, ρ ^ (a - b).natAbs ≤ κ := by
    intro b A
    calc ∑ a ∈ A, ρ ^ (a - b).natAbs = ∑ a ∈ A, ρ ^ (b - a).natAbs := by
          refine sum_congr rfl fun a _ => ?_
          rw [← Int.natAbs_neg, neg_sub]
      _ ≤ κ := hrowsum b A
  set A₀ := S'.image w₁
  set B₀ := T'.image w₂
  set C₀ := U'.image w₃
  have step3 : ∑ n ∈ S', ∑ m ∈ T', ∑ k ∈ U',
      (ρ ^ (w₁ n - w₂ m).natAbs * ρ ^ (w₁ n - w₃ k).natAbs) *
        (x n ^ (1 / p₁) * y m ^ (1 / p₂) * z k ^ (1 / p₃)) ≤
      c₁ * c₂ * c₃ * ((κ * κ) * ((∑ a ∈ A₀, X a) ^ (1 / p₁) * (∑ b ∈ B₀, Y b) ^ (1 / p₂) *
        (∑ c ∈ C₀, Z c) ^ (1 / p₃))) := by
    rw [sum_sum_sum_eq_fiberwise S' T' U' w₁ w₂ w₃
      (fun a b c => ρ ^ (a - b).natAbs * ρ ^ (a - c).natAbs)
      (fun n => x n ^ (1 / p₁)) (fun m => y m ^ (1 / p₂)) (fun k => z k ^ (1 / p₃))]
    calc ∑ a ∈ A₀, ∑ b ∈ B₀, ∑ c ∈ C₀, ρ ^ (a - b).natAbs * ρ ^ (a - c).natAbs *
          ((∑ n ∈ S' with w₁ n = a, x n ^ (1 / p₁)) * (∑ m ∈ T' with w₂ m = b, y m ^ (1 / p₂)) *
            (∑ k ∈ U' with w₃ k = c, z k ^ (1 / p₃)))
        ≤ ∑ a ∈ A₀, ∑ b ∈ B₀, ∑ c ∈ C₀, ρ ^ (a - b).natAbs * ρ ^ (a - c).natAbs *
          ((c₁ * X a ^ (1 / p₁)) * (c₂ * Y b ^ (1 / p₂)) * (c₃ * Z c ^ (1 / p₃))) := by
          refine sum_le_sum fun a _ => sum_le_sum fun b _ => sum_le_sum fun c _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := hX a; have := hY b; have := hZ c
          refine mul_le_mul (mul_le_mul (hwin₁ a) (hwin₂ b) ?_ (by positivity)) (hwin₃ c) ?_
            (by positivity)
          · exact sum_nonneg fun m _ => by have := hy m; positivity
          · exact sum_nonneg fun k _ => by have := hz k; positivity
      _ = c₁ * c₂ * c₃ * ∑ a ∈ A₀, ∑ b ∈ B₀, ∑ c ∈ C₀,
            ρ ^ (a - b).natAbs * ρ ^ (a - c).natAbs *
              (X a ^ (1 / p₁) * Y b ^ (1 / p₂) * Z c ^ (1 / p₃)) := by
          rw [mul_sum]
          refine sum_congr rfl fun a _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun b _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun c _ => ?_
          ring
      _ ≤ _ := by
          gcongr
          refine sum_sum_sum_mul_rpow_le _ _ _ _ X Y Z hq₁ hq₂ hq₃ hp (by positivity)
            (fun a b c => by positivity) hX hY hZ ?_ ?_ ?_
          · intro a _
            simp_rw [← mul_sum, ← sum_mul]
            exact mul_le_mul (hrowsum a B₀) (hrowsum a C₀) (sum_nonneg fun c _ => by positivity)
              hκ
          · intro b _
            simp_rw [← mul_sum]
            calc ∑ a ∈ A₀, ρ ^ (a - b).natAbs * ∑ c ∈ C₀, ρ ^ (a - c).natAbs
                ≤ ∑ a ∈ A₀, ρ ^ (a - b).natAbs * κ :=
                  sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hrowsum a C₀) (by positivity)
              _ ≤ κ * κ := by
                  rw [← sum_mul]
                  exact mul_le_mul_of_nonneg_right (hrowsum' b A₀) hκ
          · intro c _
            have e : ∀ a, ∑ b ∈ B₀, ρ ^ (a - b).natAbs * ρ ^ (a - c).natAbs =
                ρ ^ (a - c).natAbs * ∑ b ∈ B₀, ρ ^ (a - b).natAbs := by
              intro a
              rw [mul_sum]
              refine sum_congr rfl fun b _ => ?_
              ring
            simp_rw [e]
            calc ∑ a ∈ A₀, ρ ^ (a - c).natAbs * ∑ b ∈ B₀, ρ ^ (a - b).natAbs
                ≤ ∑ a ∈ A₀, ρ ^ (a - c).natAbs * κ :=
                  sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hrowsum a B₀) (by positivity)
              _ ≤ κ * κ := by
                  rw [← sum_mul]
                  exact mul_le_mul_of_nonneg_right (hrowsum' c A₀) hκ
  have hsumX : ∑ a ∈ A₀, X a ≤ ∑ n ∈ S, x n := by
    rw [sum_fiberwise_of_maps_to (fun n hn => mem_image_of_mem w₁ hn)]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n _ _ => hx n
  have hsumY : ∑ b ∈ B₀, Y b ≤ ∑ m ∈ T, y m := by
    rw [sum_fiberwise_of_maps_to (fun m hm => mem_image_of_mem w₂ hm)]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun m _ _ => hy m
  have hsumZ : ∑ c ∈ C₀, Z c ≤ ∑ k ∈ U, z k := by
    rw [sum_fiberwise_of_maps_to (fun k hk => mem_image_of_mem w₃ hk)]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun k _ _ => hz k
  have hX0 : 0 ≤ ∑ a ∈ A₀, X a := sum_nonneg fun a _ => hX a
  have hY0 : 0 ≤ ∑ b ∈ B₀, Y b := sum_nonneg fun b _ => hY b
  have hZ0 : 0 ≤ ∑ c ∈ C₀, Z c := sum_nonneg fun c _ => hZ c
  have : 0 ≤ (∑ n ∈ S, x n) ^ (1 / p₁) := Real.rpow_nonneg (sum_nonneg fun n _ => hx n) _
  have : 0 ≤ (∑ m ∈ T, y m) ^ (1 / p₂) := Real.rpow_nonneg (sum_nonneg fun m _ => hy m) _
  calc ∑ n ∈ S, ∑ m ∈ T, ∑ k ∈ U, x n ^ (1 / p₁) * y m ^ (1 / p₂) * z k ^ (1 / p₃) * W n m k
      ≤ 2 ^ γ * 2 ^ γ * (c₁ * c₂ * c₃ * ((κ * κ) * ((∑ a ∈ A₀, X a) ^ (1 / p₁) *
          (∑ b ∈ B₀, Y b) ^ (1 / p₂) * (∑ c ∈ C₀, Z c) ^ (1 / p₃)))) := by
        rw [step1]
        refine step2.trans ?_
        gcongr
    _ ≤ 2 ^ γ * 2 ^ γ * (c₁ * c₂ * c₃ * ((κ * κ) * ((∑ n ∈ S, x n) ^ (1 / p₁) *
          (∑ m ∈ T, y m) ^ (1 / p₂) * (∑ k ∈ U, z k) ^ (1 / p₃)))) := by
        gcongr
    _ = _ := by
        simp only [d2Const, c₁, c₂, c₃, κ, ρ, x, y, z]
        ring

end PrimeBHT.TimeFrequency.Interp
