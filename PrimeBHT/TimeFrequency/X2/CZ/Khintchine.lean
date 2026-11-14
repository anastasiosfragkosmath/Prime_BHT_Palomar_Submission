module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# V08(d): the Khintchine inequality (lower half, exponents `0 < p < 2`) for Rademacher sums of complex numbers

For `a : Fin N → ℂ` and sign vectors `ε : Fin N → Bool` (`sgn true = 1`, `sgn false = -1`), put
`S(ε) = Σ_j sgn(ε_j) a_j`.  Then (finite sums over the `2^N` sign vectors)

* `sum_normSq_rsum`: `Σ_ε |S(ε)|² = 2^N Σ_j |a_j|²` (orthogonality);
* `sum_normSq_sq_rsum_le`: `Σ_ε |S(ε)|⁴ ≤ 3 · 2^N (Σ_j |a_j|²)²` (fourth moment);
* `khintchine_lower`: `(Σ_j |a_j|²)^{1/2} ≤ 3^{(2-p)/(2p)} (2^{-N} Σ_ε |S(ε)|^p)^{1/p}` for `0 < p < 2`
  (Hölder between the exponents `p` and `4`), and with constant `1` for `p ≥ 2` (Lyapunov).

Both inductions split off the first coordinate (`Fin.cons`).
-/

@[expose] public noncomputable section

open scoped ENNReal Real ComplexConjugate

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

/-- The sign `±1` of a Boolean. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The Rademacher sum `Σ_j sgn(ε_j) a_j`. -/
def rsum {N : ℕ} (a : Fin N → ℂ) (ε : Fin N → Bool) : ℂ := ∑ j, (sgn (ε j) : ℂ) * a j

theorem sgn_true : sgn true = 1 := by simp [sgn]
theorem sgn_false : sgn false = -1 := by simp [sgn]

theorem abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> simp [sgn]

theorem sum_cons {N : ℕ} {M : Type*} [AddCommMonoid M] (F : (Fin (N + 1) → Bool) → M) :
    ∑ ε, F ε = ∑ b : Bool, ∑ ε' : Fin N → Bool, F (Fin.cons b ε') := by
  rw [← (Fin.consEquiv (fun _ : Fin (N + 1) => Bool)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem rsum_cons {N : ℕ} (a : Fin (N + 1) → ℂ) (b : Bool) (ε' : Fin N → Bool) :
    rsum a (Fin.cons b ε') = (sgn b : ℂ) * a 0 + rsum (fun j => a j.succ) ε' := by
  unfold rsum
  rw [Fin.sum_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ]

theorem normSq_pair (a0 S : ℂ) :
    Complex.normSq (a0 + S) + Complex.normSq (-a0 + S) = 2 * Complex.normSq a0 + 2 * Complex.normSq S := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]
  ring

theorem normSq_pair_sq (a0 S : ℂ) :
    Complex.normSq (a0 + S) ^ 2 + Complex.normSq (-a0 + S) ^ 2 ≤
      2 * (Complex.normSq a0 + Complex.normSq S) ^ 2 + 8 * Complex.normSq a0 * Complex.normSq S := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]
  nlinarith [sq_nonneg (a0.re * S.im - a0.im * S.re)]

theorem sum_normSq_rsum : ∀ (N : ℕ) (a : Fin N → ℂ),
    ∑ ε : Fin N → Bool, Complex.normSq (rsum a ε) = 2 ^ N * ∑ j, Complex.normSq (a j)
  | 0, a => by simp [rsum]
  | N + 1, a => by
    rw [sum_cons]
    simp_rw [rsum_cons]
    rw [Fintype.sum_bool, ← Finset.sum_add_distrib]
    simp only [sgn_true, sgn_false, Complex.ofReal_one, Complex.ofReal_neg, one_mul, neg_mul]
    simp_rw [normSq_pair]
    rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum,
      sum_normSq_rsum N (fun j => a j.succ), Fin.sum_univ_succ]
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring

theorem sum_normSq_sq_rsum_le : ∀ (N : ℕ) (a : Fin N → ℂ),
    ∑ ε : Fin N → Bool, Complex.normSq (rsum a ε) ^ 2 ≤ 3 * 2 ^ N * (∑ j, Complex.normSq (a j)) ^ 2
  | 0, a => by simp [rsum]
  | N + 1, a => by
    rw [sum_cons]
    simp_rw [rsum_cons]
    rw [Fintype.sum_bool, ← Finset.sum_add_distrib]
    simp only [sgn_true, sgn_false, Complex.ofReal_one, Complex.ofReal_neg, one_mul, neg_mul]
    have h1 : ∀ ε' : Fin N → Bool,
        Complex.normSq (a 0 + rsum (fun j => a j.succ) ε') ^ 2 +
          Complex.normSq (-a 0 + rsum (fun j => a j.succ) ε') ^ 2 ≤
        2 * (Complex.normSq (a 0) + Complex.normSq (rsum (fun j => a j.succ) ε')) ^ 2 +
          8 * Complex.normSq (a 0) * Complex.normSq (rsum (fun j => a j.succ) ε') :=
      fun ε' => normSq_pair_sq _ _
    refine (Finset.sum_le_sum fun ε' _ => h1 ε').trans ?_
    set a' : Fin N → ℂ := fun j => a j.succ with ha'
    set p : ℝ := Complex.normSq (a 0) with hp
    set σ : ℝ := ∑ j, Complex.normSq (a' j) with hσ
    have hA := sum_normSq_rsum N a'
    have hB := sum_normSq_sq_rsum_le N a'
    have e1 : ∑ ε' : Fin N → Bool, (2 * (p + Complex.normSq (rsum a' ε')) ^ 2 +
        8 * p * Complex.normSq (rsum a' ε')) =
        2 * ∑ ε' : Fin N → Bool, Complex.normSq (rsum a' ε') ^ 2 +
          12 * p * ∑ ε' : Fin N → Bool, Complex.normSq (rsum a' ε') +
          2 * p ^ 2 * (2 ^ N : ℝ) := by
      have : ∀ ε' : Fin N → Bool, 2 * (p + Complex.normSq (rsum a' ε')) ^ 2 +
          8 * p * Complex.normSq (rsum a' ε') =
          2 * Complex.normSq (rsum a' ε') ^ 2 + 12 * p * Complex.normSq (rsum a' ε') + 2 * p ^ 2 := by
        intro ε'; ring
      simp_rw [this]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        Finset.sum_const]
      simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    have hsum : ∑ j : Fin (N + 1), Complex.normSq (a j) = p + σ := by
      rw [Fin.sum_univ_succ]
    have hA' : ∑ ε' : Fin N → Bool, Complex.normSq (rsum a' ε') = 2 ^ N * σ := hA
    have hpow : (2 : ℝ) ^ (N + 1) = 2 ^ N * 2 := pow_succ _ _
    rw [e1, hA', hsum, hpow]
    have hp0 : 0 ≤ p := Complex.normSq_nonneg _
    have hσ0 : 0 ≤ σ := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
    have h2N : (0 : ℝ) < 2 ^ N := by positivity
    have : 2 * ∑ ε' : Fin N → Bool, Complex.normSq (rsum a' ε') ^ 2 ≤ 2 * (3 * 2 ^ N * σ ^ 2) := by
      have hB' : ∑ ε' : Fin N → Bool, Complex.normSq (rsum a' ε') ^ 2 ≤ 3 * 2 ^ N * σ ^ 2 := hB
      linarith
    nlinarith [mul_nonneg hp0 hσ0, mul_nonneg (mul_nonneg hp0 hp0) h2N.le, mul_nonneg (mul_nonneg hp0 hσ0) h2N.le]

section Holder

theorem key_real {t X Sp κ : ℝ} (hκ : 0 < κ) (ht : 0 < t) (hX : 0 < X) (hSp : 0 ≤ Sp)
    (h : X * t ^ (2 : ℝ) ≤ Sp ^ (1 / (1 + κ)) * (3 * X * t ^ (4 : ℝ)) ^ (κ / (1 + κ))) :
    X * t ^ (2 - 2 * κ) ≤ 3 ^ κ * Sp := by
  have hP : 0 < 1 + κ := by linarith
  have h1 := Real.rpow_le_rpow (by positivity) h hP.le
  have e1 : 1 / (1 + κ) * (1 + κ) = 1 := by field_simp
  have e2 : κ / (1 + κ) * (1 + κ) = κ := by field_simp
  have hR : (Sp ^ (1 / (1 + κ)) * (3 * X * t ^ (4 : ℝ)) ^ (κ / (1 + κ))) ^ (1 + κ) =
      Sp * (3 * X * t ^ (4 : ℝ)) ^ κ := by
    rw [Real.mul_rpow (Real.rpow_nonneg hSp _) (Real.rpow_nonneg (by positivity) _),
      ← Real.rpow_mul hSp, ← Real.rpow_mul (by positivity), e1, e2, Real.rpow_one]
  have hL : (X * t ^ (2 : ℝ)) ^ (1 + κ) = X ^ (1 + κ) * t ^ (2 * (1 + κ)) := by
    rw [Real.mul_rpow hX.le (Real.rpow_nonneg ht.le _), ← Real.rpow_mul ht.le]
  rw [hL, hR] at h1
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul ht.le] at h1
  have e3 : X ^ (1 + κ) = X * X ^ κ := by rw [Real.rpow_add hX, Real.rpow_one]
  have e4 : t ^ (2 * (1 + κ)) = t ^ (2 - 2 * κ) * t ^ (4 * κ) := by
    rw [← Real.rpow_add ht]; congr 1; ring
  rw [e3, e4] at h1
  have hpos : 0 < X ^ κ * t ^ (4 * κ) := by positivity
  have : (X * t ^ (2 - 2 * κ)) * (X ^ κ * t ^ (4 * κ)) ≤ (3 ^ κ * Sp) * (X ^ κ * t ^ (4 * κ)) := by
    calc (X * t ^ (2 - 2 * κ)) * (X ^ κ * t ^ (4 * κ))
        = X * X ^ κ * (t ^ (2 - 2 * κ) * t ^ (4 * κ)) := by ring
      _ ≤ Sp * (3 ^ κ * X ^ κ * t ^ (4 * κ)) := h1
      _ = (3 ^ κ * Sp) * (X ^ κ * t ^ (4 * κ)) := by ring
  exact le_of_mul_le_mul_right this hpos

theorem holder_three {ι : Type*} (s : Finset ι) (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) {p κ : ℝ}
    (hp : 0 < p) (hκ : 0 < κ) (hrel : p + 4 * κ = 2 * (1 + κ)) :
    ∑ i ∈ s, r i ^ (2 : ℝ) ≤
      (∑ i ∈ s, r i ^ p) ^ (1 / (1 + κ)) * (∑ i ∈ s, r i ^ (4 : ℝ)) ^ (κ / (1 + κ)) := by
  have hP : 0 < 1 + κ := by linarith
  have hconj : (1 + κ).HolderConjugate ((1 + κ) / κ) := by
    rw [Real.holderConjugate_iff]
    refine ⟨by linarith, ?_⟩
    field_simp
  have key := Real.inner_le_Lp_mul_Lq_of_nonneg s (f := fun i => r i ^ (p / (1 + κ)))
    (g := fun i => r i ^ (4 * κ / (1 + κ))) hconj (fun i _ => Real.rpow_nonneg (hr i) _)
    (fun i _ => Real.rpow_nonneg (hr i) _)
  have e1 : ∀ i, r i ^ (p / (1 + κ)) * r i ^ (4 * κ / (1 + κ)) = r i ^ (2 : ℝ) := by
    intro i
    rw [← Real.rpow_add' (hr i)]
    · congr 1; field_simp; linarith
    · have : 0 < p / (1 + κ) + 4 * κ / (1 + κ) := by positivity
      exact this.ne'
  have e2 : ∀ i, (r i ^ (p / (1 + κ))) ^ (1 + κ) = r i ^ p := by
    intro i; rw [← Real.rpow_mul (hr i)]; congr 1; field_simp
  have e3 : ∀ i, (r i ^ (4 * κ / (1 + κ))) ^ ((1 + κ) / κ) = r i ^ (4 : ℝ) := by
    intro i; rw [← Real.rpow_mul (hr i)]; congr 1; field_simp
  simp_rw [e1, e2, e3] at key
  have e4 : (1 : ℝ) / ((1 + κ) / κ) = κ / (1 + κ) := by field_simp
  rw [e4] at key
  exact key

end Holder

/-- **Khintchine, lower half, `0 < p < 2`**: `(Σ_j |a_j|²)^{1/2} ≤ 3^{(2-p)/(2p)} (2^{-N} Σ_ε |S(ε)|^p)^{1/p}`. -/
theorem khintchine_lower_lt {N : ℕ} (a : Fin N → ℂ) {p : ℝ} (hp : 0 < p) (hp2 : p < 2) :
    (∑ j, ‖a j‖ ^ 2) ^ (2 : ℝ)⁻¹ ≤
      3 ^ ((2 - p) / (2 * p)) * (((2 : ℝ) ^ N)⁻¹ * ∑ ε : Fin N → Bool, ‖rsum a ε‖ ^ p) ^ p⁻¹ := by
  set σ2 : ℝ := ∑ j, ‖a j‖ ^ 2 with hσ2
  have hσ20 : 0 ≤ σ2 := Finset.sum_nonneg fun j _ => by positivity
  set t : ℝ := σ2 ^ (2 : ℝ)⁻¹ with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hσ20 _
  have htt : t ^ (2 : ℝ) = σ2 := by
    rw [ht, ← Real.rpow_mul hσ20]; norm_num
  have hX : (0 : ℝ) < 2 ^ N := by positivity
  set Sp : ℝ := ∑ ε : Fin N → Bool, ‖rsum a ε‖ ^ p with hSp
  have hSp0 : 0 ≤ Sp := Finset.sum_nonneg fun ε _ => Real.rpow_nonneg (norm_nonneg _) _
  have hrhs0 : 0 ≤ ((2 : ℝ) ^ N)⁻¹ * Sp := by positivity
  rcases ht0.eq_or_lt with h0 | htpos
  · rw [← h0]
    positivity
  set κ : ℝ := (2 - p) / 2 with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  have hrel : p + 4 * κ = 2 * (1 + κ) := by rw [hκ]; ring
  -- the sums of powers
  have hnorm2 : ∀ z : ℂ, ‖z‖ ^ (2 : ℝ) = Complex.normSq z := fun z => by
    rw [Real.rpow_two, Complex.normSq_eq_norm_sq]
  have hnorm4 : ∀ z : ℂ, ‖z‖ ^ (4 : ℝ) = Complex.normSq z ^ 2 := fun z => by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Complex.normSq_eq_norm_sq]; ring
  have hnsa : ∀ j, Complex.normSq (a j) = ‖a j‖ ^ 2 := fun j => Complex.normSq_eq_norm_sq _
  have hS2 : ∑ ε : Fin N → Bool, ‖rsum a ε‖ ^ (2 : ℝ) = 2 ^ N * σ2 := by
    simp_rw [hnorm2]
    rw [sum_normSq_rsum]
    simp_rw [hnsa]
    rfl
  have hS4 : ∑ ε : Fin N → Bool, ‖rsum a ε‖ ^ (4 : ℝ) ≤ 3 * 2 ^ N * σ2 ^ 2 := by
    simp_rw [hnorm4]
    have := sum_normSq_sq_rsum_le N a
    simp_rw [hnsa] at this
    exact this
  have hH := holder_three Finset.univ (fun ε : Fin N → Bool => ‖rsum a ε‖) (fun ε => norm_nonneg _)
    hp hκ0 hrel
  rw [hS2] at hH
  have hS4' : (∑ ε : Fin N → Bool, ‖rsum a ε‖ ^ (4 : ℝ)) ^ (κ / (1 + κ)) ≤
      (3 * 2 ^ N * t ^ (4 : ℝ)) ^ (κ / (1 + κ)) := by
    refine Real.rpow_le_rpow (Finset.sum_nonneg fun ε _ => Real.rpow_nonneg (norm_nonneg _) _) ?_
      (by positivity)
    have : t ^ (4 : ℝ) = σ2 ^ 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.rpow_mul ht0, htt]; norm_num
    rw [this]; exact hS4
  have hkey : (2 : ℝ) ^ N * t ^ (2 : ℝ) ≤ Sp ^ (1 / (1 + κ)) * (3 * 2 ^ N * t ^ (4 : ℝ)) ^ (κ / (1 + κ)) := by
    rw [htt]
    calc (2 : ℝ) ^ N * σ2 ≤ _ := hH
      _ ≤ _ := mul_le_mul_of_nonneg_left hS4' (Real.rpow_nonneg hSp0 _)
  have hfin := key_real hκ0 htpos hX hSp0 hkey
  have e5 : 2 - 2 * κ = p := by rw [hκ]; ring
  rw [e5] at hfin
  -- `t^p ≤ 3^κ (2^{-N} Sp)`
  have hfin' : t ^ p ≤ 3 ^ κ * (((2 : ℝ) ^ N)⁻¹ * Sp) := by
    rw [← mul_assoc, mul_comm (3 ^ κ), mul_assoc, ← mul_assoc]
    have : t ^ p ≤ ((2 : ℝ) ^ N)⁻¹ * (3 ^ κ * Sp) := by
      rw [← div_eq_inv_mul, le_div_iff₀ hX]; linarith
    calc t ^ p ≤ _ := this
      _ = _ := by ring
  have h3 := Real.rpow_le_rpow (Real.rpow_nonneg ht0 _) hfin' (inv_nonneg.2 hp.le)
  rw [← Real.rpow_mul ht0, mul_inv_cancel₀ hp.ne', Real.rpow_one,
    Real.mul_rpow (by positivity) hrhs0, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)] at h3
  have e6 : κ * p⁻¹ = (2 - p) / (2 * p) := by rw [hκ]; field_simp
  rw [e6] at h3
  exact h3

/-- **Khintchine, lower half, `p ≥ 2`** (constant `1`): Lyapunov and orthogonality. -/
theorem khintchine_lower_ge {N : ℕ} (a : Fin N → ℂ) {p : ℝ} (hp : 2 ≤ p) :
    (∑ j, ‖a j‖ ^ 2) ^ (2 : ℝ)⁻¹ ≤ (((2 : ℝ) ^ N)⁻¹ * ∑ ε : Fin N → Bool, ‖rsum a ε‖ ^ p) ^ p⁻¹ := by
  set σ2 : ℝ := ∑ j, ‖a j‖ ^ 2 with hσ2
  have hσ20 : 0 ≤ σ2 := Finset.sum_nonneg fun j _ => by positivity
  have hp0 : 0 < p := by linarith
  have hX : (0 : ℝ) < 2 ^ N := by positivity
  have hw : ∑ _ε : Fin N → Bool, ((2 : ℝ) ^ N)⁻¹ = 1 := by
    rw [Finset.sum_const]
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hpm := Real.rpow_arith_mean_le_arith_mean_rpow (Finset.univ : Finset (Fin N → Bool))
    (fun _ => ((2 : ℝ) ^ N)⁻¹) (fun ε => ‖rsum a ε‖ ^ 2) (fun _ _ => by positivity) hw
    (fun ε _ => by positivity) (p := p / 2) (by linarith)
  have hS2 : ∑ ε : Fin N → Bool, ((2 : ℝ) ^ N)⁻¹ * ‖rsum a ε‖ ^ 2 = σ2 := by
    rw [← Finset.mul_sum]
    have h := sum_normSq_rsum N a
    simp_rw [Complex.normSq_eq_norm_sq] at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ hX.ne', one_mul]
  have e1 : ∀ ε : Fin N → Bool, (‖rsum a ε‖ ^ 2) ^ (p / 2) = ‖rsum a ε‖ ^ p := by
    intro ε
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1; push_cast; ring
  simp_rw [e1] at hpm
  rw [hS2, ← Finset.mul_sum] at hpm
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hσ20 _) hpm (inv_nonneg.2 hp0.le)
  rw [← Real.rpow_mul hσ20] at h2
  have e2 : p / 2 * p⁻¹ = (2 : ℝ)⁻¹ := by field_simp
  rwa [e2] at h2

/-- The Khintchine constant. -/
def khinConst (p : ℝ) : ℝ := if p < 2 then 3 ^ ((2 - p) / (2 * p)) else 1

theorem khinConst_nonneg (p : ℝ) : 0 ≤ khinConst p := by
  unfold khinConst; split_ifs <;> positivity

/-- **Khintchine, lower half, all `p > 0`**: `(Σ_j |a_j|²)^{1/2} ≤ c_p (2^{-N} Σ_ε |Σ_j ε_j a_j|^p)^{1/p}`. -/
theorem khintchine_lower {N : ℕ} (a : Fin N → ℂ) {p : ℝ} (hp : 0 < p) :
    (∑ j, ‖a j‖ ^ 2) ^ (2 : ℝ)⁻¹ ≤
      khinConst p * (((2 : ℝ) ^ N)⁻¹ * ∑ ε : Fin N → Bool, ‖rsum a ε‖ ^ p) ^ p⁻¹ := by
  unfold khinConst
  split_ifs with h
  · exact khintchine_lower_lt a hp h
  · rw [one_mul]; exact khintchine_lower_ge a (not_lt.1 h)

end PrimeBHT.TimeFrequency.X2.CZ
