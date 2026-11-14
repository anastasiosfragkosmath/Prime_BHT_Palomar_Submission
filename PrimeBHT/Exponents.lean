module

public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Range and exponent bookkeeping for the prime bilinear Hilbert transform

Pure real arithmetic (no analysis) behind `blueprint.md` section 1.2 (Lemma 1.1) and section 7
(nodes N50, N51, N52, N53, the parameter ledger of section 9).

Notation (as in the blueprint): `a = 1/p`, `b = 1/q`, `t = 1/r - 1 = a + b - 1`, and `p'` is the
Hölder conjugate of `p`, i.e. `1/p' = 1 - 1/p`.

* `InR p q r`: the region `R` of the main theorem.
* Lemma 1.1: symmetry, `R ∩ {r ≥ 1}`, the shape of `R ∩ {r < 1, p ≤ q}`, and its converse.
* N50: the window for `θ`, the auxiliary tuple `(p₀, q₀, r₀)`, the exponent `t - 3θ/8 < 0`,
  the three weights `λ₀, λ₁, λ₂`, the chain `τ₀ < ⋯ < τ_M = 3/4`, the quantities `σ_j(δ)`, the
  choice of `δ`, and the strict gap `μ`.
* N51: the Banach partner tuple in the case `r ≥ 1` and the resulting power saving.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PrimeBHT.Exponents

/-! ### The region `R` and Lemma 1.1 -/

/-- The region `R` of the main theorem in the coordinates `(p, q, r)`:
`R = {(p,q,r) ∈ (0,∞)³ : 2/p + 3/q < 3, 3/p + 2/q < 3, 1/r = 1/p + 1/q, p > 1, q > 1}`.
(`0 < p` and `0 < q` follow from `1 < p`, `1 < q`.) -/
structure InR (p q r : ℝ) : Prop where
  pos_r : 0 < r
  one_lt_p : 1 < p
  one_lt_q : 1 < q
  inv_r : 1 / r = 1 / p + 1 / q
  lt_left : 2 / p + 3 / q < 3
  lt_right : 3 / p + 2 / q < 3

variable {p q r : ℝ}

theorem InR.pos_p (h : InR p q r) : 0 < p := lt_trans zero_lt_one h.one_lt_p

theorem InR.pos_q (h : InR p q r) : 0 < q := lt_trans zero_lt_one h.one_lt_q

/-- `3/p + 2/q < 3` in the reciprocal coordinates: `3a + 2b < 3`. -/
theorem InR.lt_right' (h : InR p q r) : 3 * (1 / p) + 2 * (1 / q) < 3 := by
  have := h.lt_right
  rwa [div_eq_mul_one_div 3 p, div_eq_mul_one_div 2 q] at this

theorem InR.inv_p_lt_one (h : InR p q r) : 1 / p < 1 := (div_lt_one h.pos_p).2 h.one_lt_p

/-- Lemma 1.1.1: `R` is symmetric under `(p, q, r) ↦ (q, p, r)`. -/
theorem InR.symm (h : InR p q r) : InR q p r where
  pos_r := h.pos_r
  one_lt_p := h.one_lt_q
  one_lt_q := h.one_lt_p
  inv_r := by rw [h.inv_r, add_comm]
  lt_left := by have := h.lt_right; linarith
  lt_right := by have := h.lt_left; linarith

/-! #### Lemma 1.1.3: the shape of `R ∩ {r < 1, p ≤ q}` -/

/-- Common facts for `(p, q, r) ∈ R`, `r < 1`, `p ≤ q`: `b ≤ a`, `a + b > 1`, `3a + 2b < 3`. -/
theorem InR.aux (h : InR p q r) (hr : r < 1) (hpq : p ≤ q) :
    1 / q ≤ 1 / p ∧ 1 < 1 / p + 1 / q ∧ 3 * (1 / p) + 2 * (1 / q) < 3 := by
  refine ⟨one_div_le_one_div_of_le h.pos_p hpq, ?_, h.lt_right'⟩
  rw [← h.inv_r]
  exact one_lt_one_div h.pos_r hr

/-- Lemma 1.1.3 (i): `a > 1/2`. -/
theorem InR.half_lt_inv_p (h : InR p q r) (hr : r < 1) (hpq : p ≤ q) : 1 / 2 < 1 / p := by
  obtain ⟨h1, h2, _⟩ := h.aux hr hpq
  linarith

/-- Lemma 1.1.3 (ii): `1/p' > 2t`, i.e. `1 - 1/p > 2 (1/r - 1)` (`e:range-gaps`). -/
theorem InR.two_mul_t_lt (h : InR p q r) (hr : r < 1) (hpq : p ≤ q) :
    2 * (1 / r - 1) < 1 - 1 / p := by
  obtain ⟨h1, h2, h3⟩ := h.aux hr hpq
  rw [h.inv_r]
  linarith

/-- Lemma 1.1.3 (iii): `0 < t`. -/
theorem InR.t_pos (h : InR p q r) (hr : r < 1) : 0 < 1 / r - 1 := by
  have := one_lt_one_div h.pos_r hr
  linarith

/-- Lemma 1.1.3 (iii): `t < 1/5`. -/
theorem InR.t_lt_fifth (h : InR p q r) (hr : r < 1) (hpq : p ≤ q) : 1 / r - 1 < 1 / 5 := by
  obtain ⟨h1, h2, h3⟩ := h.aux hr hpq
  rw [h.inv_r]
  linarith

/-- Lemma 1.1.3 (iv): `b > 3t`. -/
theorem InR.three_mul_t_lt_inv_q (h : InR p q r) (hr : r < 1) (hpq : p ≤ q) :
    3 * (1 / r - 1) < 1 / q := by
  obtain ⟨h1, h2, h3⟩ := h.aux hr hpq
  rw [h.inv_r]
  linarith

/-- Lemma 1.1.3 (iv): `b > 1 - a = 1/p'`. -/
theorem InR.one_sub_inv_p_lt_inv_q (h : InR p q r) (hr : r < 1) (hpq : p ≤ q) :
    1 - 1 / p < 1 / q := by
  obtain ⟨h1, h2, h3⟩ := h.aux hr hpq
  linarith

/-! ### N50 (P2): the window for `θ` -/

/-- (P2): the interval `(8t/3, min{2/p', 1 - 2t})` is nonempty, where `1/p' = 1 - 1/p`.
(`8t/3 < 4t < 2/p'` by (P1) and `8t/3 < 1 - 2t` since `t < 1/5 < 3/14`.) -/
theorem InR.theta_window (h : InR p q r) (hr : r < 1) (hpq : p ≤ q) :
    8 * (1 / r - 1) / 3 < min (2 * (1 - 1 / p)) (1 - 2 * (1 / r - 1)) := by
  have h1 := h.t_pos hr
  have h2 := h.two_mul_t_lt hr hpq
  have h3 := h.t_lt_fifth hr hpq
  refine lt_min ?_ ?_ <;> linarith

/-- (P2): the blueprint's choice `θ = (1/2)(8t/3 + min{2/p', 1 - 2t})`. -/
noncomputable def thetaOf (p r : ℝ) : ℝ :=
  (8 * (1 / r - 1) / 3 + min (2 * (1 - 1 / p)) (1 - 2 * (1 / r - 1))) / 2

/-- (P2): `8t/3 < θ`. -/
theorem InR.lt_thetaOf (h : InR p q r) (hr : r < 1) (hpq : p ≤ q) :
    8 * (1 / r - 1) / 3 < thetaOf p r := by
  have := h.theta_window hr hpq
  unfold thetaOf
  linarith

/-- (P2): `θ < min{2/p', 1 - 2t}`. -/
theorem InR.thetaOf_lt (h : InR p q r) (hr : r < 1) (hpq : p ≤ q) :
    thetaOf p r < min (2 * (1 - 1 / p)) (1 - 2 * (1 / r - 1)) := by
  have := h.theta_window hr hpq
  unfold thetaOf
  linarith

/-- (P2): existence of `θ` with `8t/3 < θ < min{2/p', 1 - 2t}`. -/
theorem InR.exists_theta (h : InR p q r) (hr : r < 1) (hpq : p ≤ q) :
    ∃ θ : ℝ, 8 * (1 / r - 1) / 3 < θ ∧ θ < min (2 * (1 - 1 / p)) (1 - 2 * (1 / r - 1)) :=
  ⟨thetaOf p r, h.lt_thetaOf hr hpq, h.thetaOf_lt hr hpq⟩

/-! ### N50 (P3): the auxiliary tuple `(p₀, q₀, r₀)` -/

theorem mul_div_one_sub_aux (x θ : ℝ) (hD : 1 - θ ≠ 0) : (1 - θ) * (x / (1 - θ)) = x := by
  field_simp

section Tuple

variable (h : InR p q r) (hr : r < 1) (hpq : p ≤ q) {θ : ℝ}
  (hθ₁ : 8 * (1 / r - 1) / 3 < θ) (hθ₂ : θ < min (2 * (1 - 1 / p)) (1 - 2 * (1 / r - 1)))

include h hr hpq hθ₁ hθ₂

theorem theta_pos : 0 < θ := by
  have := h.t_pos hr
  linarith

theorem theta_lt_one : θ < 1 := by
  have := h.t_pos hr
  have := (lt_min_iff.1 hθ₂).2
  linarith

theorem one_sub_theta_pos : 0 < 1 - θ := by
  have := theta_lt_one h hr hpq hθ₁ hθ₂
  linarith

theorem theta_lt_two_inv_p' : θ < 2 * (1 - 1 / p) := (lt_min_iff.1 hθ₂).1

theorem theta_lt_one_sub_two_t : θ < 1 - 2 * (1 / r - 1) := (lt_min_iff.1 hθ₂).2

theorem theta_lt_two_inv_q : θ < 2 * (1 / q) := by
  have := (lt_min_iff.1 hθ₂).1
  have := h.one_sub_inv_p_lt_inv_q hr hpq
  linarith

theorem theta_lt_two_one_sub_inv_q : θ < 2 * (1 - 1 / q) := by
  have := (lt_min_iff.1 hθ₂).1
  have := (h.aux hr hpq).1
  linarith

/-- (P3): `p₀ > 1` (and `p₀ < ∞`, since `p₀` is a real number). -/
theorem one_lt_p₀ {p₀ : ℝ} (h0p : 1 / p₀ = (1 / p - θ / 2) / (1 - θ)) : 1 < p₀ := by
  have hD := one_sub_theta_pos h hr hpq hθ₁ hθ₂
  have h1 := theta_lt_two_inv_p' h hr hpq hθ₁ hθ₂
  have h2 := h.half_lt_inv_p hr hpq
  have hu0 : 0 < 1 / p₀ := by
    rw [h0p]
    exact div_pos (by linarith) hD
  have hu1 : 1 / p₀ < 1 := by
    rw [h0p, div_lt_one hD]
    linarith
  have hp₀ : 0 < p₀ := one_div_pos.1 hu0
  exact (div_lt_one hp₀).1 hu1

/-- (P3): `q₀ > 1`. -/
theorem one_lt_q₀ {q₀ : ℝ} (h0q : 1 / q₀ = (1 / q - θ / 2) / (1 - θ)) : 1 < q₀ := by
  have hD := one_sub_theta_pos h hr hpq hθ₁ hθ₂
  have h1 := theta_lt_two_inv_q h hr hpq hθ₁ hθ₂
  have h2 := theta_lt_two_one_sub_inv_q h hr hpq hθ₁ hθ₂
  have hu0 : 0 < 1 / q₀ := by
    rw [h0q]
    exact div_pos (by linarith) hD
  have hu1 : 1 / q₀ < 1 := by
    rw [h0q, div_lt_one hD]
    linarith
  have hq₀ : 0 < q₀ := one_div_pos.1 hu0
  exact (div_lt_one hq₀).1 hu1

/-- (P3): `1/r₀ = (1/r - θ)/(1-θ) = 1 + t/(1-θ)`. -/
theorem inv_r₀_eq {r₀ : ℝ} (h0r : 1 / r₀ = (1 / r - θ) / (1 - θ)) :
    1 / r₀ = 1 + (1 / r - 1) / (1 - θ) := by
  have hD := (one_sub_theta_pos h hr hpq hθ₁ hθ₂).ne'
  rw [h0r]
  field_simp
  ring

/-- (P3): `1 < 1/r₀`, i.e. `r₀ < 1`. -/
theorem r₀_lt_one {r₀ : ℝ} (h0r : 1 / r₀ = (1 / r - θ) / (1 - θ)) : r₀ < 1 := by
  have hD := one_sub_theta_pos h hr hpq hθ₁ hθ₂
  have e := inv_r₀_eq h hr hpq hθ₁ hθ₂ h0r
  have hpos : 0 < (1 / r - 1) / (1 - θ) := div_pos (h.t_pos hr) hD
  have hr₀ : 0 < r₀ := one_div_pos.1 (by linarith)
  by_contra hcon
  have h1 : 1 ≤ r₀ := not_lt.1 hcon
  have := (div_le_one hr₀).2 h1
  linarith

/-- (P3): `r₀ > 2/3`, i.e. `t/(1-θ) < 1/2`, i.e. `θ < 1 - 2t`. -/
theorem two_thirds_lt_r₀ {r₀ : ℝ} (h0r : 1 / r₀ = (1 / r - θ) / (1 - θ)) : 2 / 3 < r₀ := by
  have hD := one_sub_theta_pos h hr hpq hθ₁ hθ₂
  have e := inv_r₀_eq h hr hpq hθ₁ hθ₂ h0r
  have hpos : 0 < (1 / r - 1) / (1 - θ) := div_pos (h.t_pos hr) hD
  have hlt : (1 / r - 1) / (1 - θ) < 1 / 2 := by
    rw [div_lt_iff₀ hD]
    have := theta_lt_one_sub_two_t h hr hpq hθ₁ hθ₂
    linarith
  have hr₀ : 0 < r₀ := one_div_pos.1 (by linarith)
  by_contra hcon
  have h1 : r₀ ≤ 2 / 3 := not_lt.1 hcon
  have h2 := one_div_le_one_div_of_le hr₀ h1
  have e2 : (1 : ℝ) / (2 / 3) = 3 / 2 := by norm_num
  rw [e2] at h2
  linarith

/-- (P3): `1/p₀ + 1/q₀ = 1/r₀`. -/
theorem inv_p₀_add_inv_q₀ {p₀ q₀ r₀ : ℝ} (h0p : 1 / p₀ = (1 / p - θ / 2) / (1 - θ))
    (h0q : 1 / q₀ = (1 / q - θ / 2) / (1 - θ)) (h0r : 1 / r₀ = (1 / r - θ) / (1 - θ)) :
    1 / p₀ + 1 / q₀ = 1 / r₀ := by
  rw [h0p, h0q, h0r, ← add_div]
  congr 1
  rw [h.inv_r]
  ring

/-- (P3), interpolation identity, first coordinate: `(1-θ)/p₀ + θ/2 = 1/p`. -/
theorem interp_p₀ {p₀ : ℝ} (h0p : 1 / p₀ = (1 / p - θ / 2) / (1 - θ)) :
    (1 - θ) * (1 / p₀) + θ * (1 / 2) = 1 / p := by
  have hD := (one_sub_theta_pos h hr hpq hθ₁ hθ₂).ne'
  rw [h0p, mul_div_one_sub_aux _ _ hD]
  ring

/-- (P3), interpolation identity, second coordinate: `(1-θ)/q₀ + θ/2 = 1/q`. -/
theorem interp_q₀ {q₀ : ℝ} (h0q : 1 / q₀ = (1 / q - θ / 2) / (1 - θ)) :
    (1 - θ) * (1 / q₀) + θ * (1 / 2) = 1 / q := by
  have hD := (one_sub_theta_pos h hr hpq hθ₁ hθ₂).ne'
  rw [h0q, mul_div_one_sub_aux _ _ hD]
  ring

/-- (P3), interpolation identity, third coordinate: `(1-θ)/r₀ + θ = 1/r = 1 + t`. -/
theorem interp_r₀ {r₀ : ℝ} (h0r : 1 / r₀ = (1 / r - θ) / (1 - θ)) :
    (1 - θ) * (1 / r₀) + θ * 1 = 1 / r := by
  have hD := (one_sub_theta_pos h hr hpq hθ₁ hθ₂).ne'
  rw [h0r, mul_div_one_sub_aux _ _ hD]
  ring

/-- (P4): `E_U := t - 3θ/8 < 0`. -/
theorem E_U_neg : 1 / r - 1 - 3 * θ / 8 < 0 := by
  linarith

/-- (P5): the exponent `E₀ = τ₀/r - θ/4` is negative iff `τ₀ < r θ / 4` (for `r > 0`). -/
theorem E₀_neg_iff {τ₀ : ℝ} : τ₀ / r - θ / 4 < 0 ↔ τ₀ < r * θ / 4 := by
  have hr0 := h.pos_r
  rw [sub_neg, div_lt_iff₀ hr0]
  constructor <;> intro h' <;> linarith

end Tuple

/-- (P3), full statement: for `θ` in the window and `(p₀, q₀, r₀)` as defined by the blueprint:
`1 < p₀, q₀`, `2/3 < r₀ < 1`, `1/p₀ + 1/q₀ = 1/r₀`, and the convex-combination identity
`(1/p, 1/q, 1/r) = (1-θ)(1/p₀, 1/q₀, 1/r₀) + θ(1/2, 1/2, 1)`. -/
theorem InR.tuple_spec (h : InR p q r) (hr : r < 1) (hpq : p ≤ q) {θ p₀ q₀ r₀ : ℝ}
    (hθ₁ : 8 * (1 / r - 1) / 3 < θ)
    (hθ₂ : θ < min (2 * (1 - 1 / p)) (1 - 2 * (1 / r - 1)))
    (h0p : 1 / p₀ = (1 / p - θ / 2) / (1 - θ)) (h0q : 1 / q₀ = (1 / q - θ / 2) / (1 - θ))
    (h0r : 1 / r₀ = (1 / r - θ) / (1 - θ)) :
    1 < p₀ ∧ 1 < q₀ ∧ 2 / 3 < r₀ ∧ r₀ < 1 ∧ 1 / p₀ + 1 / q₀ = 1 / r₀ ∧
      1 / r₀ = 1 + (1 / r - 1) / (1 - θ) ∧
      (1 - θ) * (1 / p₀) + θ * (1 / 2) = 1 / p ∧ (1 - θ) * (1 / q₀) + θ * (1 / 2) = 1 / q ∧
      (1 - θ) * (1 / r₀) + θ * 1 = 1 / r :=
  ⟨one_lt_p₀ h hr hpq hθ₁ hθ₂ h0p, one_lt_q₀ h hr hpq hθ₁ hθ₂ h0q,
    two_thirds_lt_r₀ h hr hpq hθ₁ hθ₂ h0r, r₀_lt_one h hr hpq hθ₁ hθ₂ h0r,
    inv_p₀_add_inv_q₀ h hr hpq hθ₁ hθ₂ h0p h0q h0r, inv_r₀_eq h hr hpq hθ₁ hθ₂ h0r,
    interp_p₀ h hr hpq hθ₁ hθ₂ h0p, interp_q₀ h hr hpq hθ₁ hθ₂ h0q,
    interp_r₀ h hr hpq hθ₁ hθ₂ h0r⟩

/-- Existence of the auxiliary tuple: the reals `p₀, q₀, r₀` with the prescribed reciprocals. -/
theorem exists_tuple (p q r θ : ℝ) :
    ∃ p₀ q₀ r₀ : ℝ, 1 / p₀ = (1 / p - θ / 2) / (1 - θ) ∧ 1 / q₀ = (1 / q - θ / 2) / (1 - θ) ∧
      1 / r₀ = (1 / r - θ) / (1 - θ) :=
  ⟨1 / ((1 / p - θ / 2) / (1 - θ)), 1 / ((1 / q - θ / 2) / (1 - θ)),
    1 / ((1 / r - θ) / (1 - θ)), by simp, by simp, by simp⟩

/-! ### N50 (P8), (P9): the weights `λ₀, λ₁, λ₂` of the three interpolation points -/

theorem weights_sum_core (a b δ : ℝ) (hD : 1 - 2 * δ ≠ 0) :
    2 * (1 - a - δ) / (1 - 2 * δ) + (a - b) / (1 - 2 * δ) + (a + b - 1) / (1 - 2 * δ) = 1 := by
  field_simp
  ring

theorem weights_coord_one (a b δ : ℝ) (hD : 1 - 2 * δ ≠ 0) :
    2 * (1 - a - δ) / (1 - 2 * δ) * (1 / 2) + (a - b) / (1 - 2 * δ) * (1 - δ) +
      (a + b - 1) / (1 - 2 * δ) * (1 - δ) = a := by
  field_simp
  ring

theorem weights_coord_two (a b δ : ℝ) (hD : 1 - 2 * δ ≠ 0) :
    2 * (1 - a - δ) / (1 - 2 * δ) * (1 / 2) + (a - b) / (1 - 2 * δ) * δ +
      (a + b - 1) / (1 - 2 * δ) * (1 - δ) = b := by
  field_simp
  ring

theorem weights_coord_three (a b δ : ℝ) (hD : 1 - 2 * δ ≠ 0) :
    2 * (1 - a - δ) / (1 - 2 * δ) * 1 + (a - b) / (1 - 2 * δ) * 1 +
      (a + b - 1) / (1 - 2 * δ) * (2 - 2 * δ) = a + b := by
  field_simp
  ring

/-- (P8), (P9): for `0 < δ < min{1/2, 1/p'}` the weights
`λ₀ = 2(1/p' - δ)/(1-2δ)`, `λ₁ = (a - b)/(1-2δ)`, `λ₂ = t/(1-2δ)` are `≥ 0` (`λ₂ > 0`), have sum
`1`, `λ₂ < 1`, and
`(1/p, 1/q, 1/r) = λ₀ (1/2, 1/2, 1) + λ₁ (1-δ, δ, 1) + λ₂ (1-δ, 1-δ, 2-2δ)`.
(`0 < δ` is not needed; `λ₁ ≥ 0` is the use of `p ≤ q`.) -/
theorem InR.weights_spec (h : InR p q r) (hr : r < 1) (hpq : p ≤ q) {p' δ l₀ l₁ l₂ : ℝ}
    (hp' : 1 / p + 1 / p' = 1) (hδ₁ : δ < 1 / 2) (hδ₂ : δ < 1 / p')
    (hl₀ : l₀ = 2 * (1 / p' - δ) / (1 - 2 * δ)) (hl₁ : l₁ = (1 / p - 1 / q) / (1 - 2 * δ))
    (hl₂ : l₂ = (1 / r - 1) / (1 - 2 * δ)) :
    0 ≤ l₀ ∧ 0 ≤ l₁ ∧ 0 < l₂ ∧ l₀ + l₁ + l₂ = 1 ∧ l₂ < 1 ∧
      l₀ * (1 / 2) + l₁ * (1 - δ) + l₂ * (1 - δ) = 1 / p ∧
      l₀ * (1 / 2) + l₁ * δ + l₂ * (1 - δ) = 1 / q ∧
      l₀ * 1 + l₁ * 1 + l₂ * (2 - 2 * δ) = 1 / r := by
  have hg : 1 / p' = 1 - 1 / p := by linarith
  have hD : 0 < 1 - 2 * δ := by linarith
  have hD' : 1 - 2 * δ ≠ 0 := hD.ne'
  have hba := (h.aux hr hpq).1
  have ht := h.t_pos hr
  have hr' := h.inv_r
  rw [hg] at hδ₂ hl₀
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hl₀]
    exact div_nonneg (by linarith) hD.le
  · rw [hl₁]
    exact div_nonneg (by linarith) hD.le
  · rw [hl₂]
    exact div_pos ht hD
  · rw [hl₀, hl₁, hl₂, hr']
    have := weights_sum_core (1 / p) (1 / q) δ hD'
    simpa using this
  · rw [hl₂, div_lt_one hD]
    linarith
  · rw [hl₀, hl₁, hl₂, hr']
    exact weights_coord_one (1 / p) (1 / q) δ hD'
  · rw [hl₀, hl₁, hl₂, hr']
    exact weights_coord_two (1 / p) (1 / q) δ hD'
  · rw [hl₀, hl₁, hl₂, hr']
    exact weights_coord_three (1 / p) (1 / q) δ hD'

/-- Existence of the weights (as reals with the prescribed formulas). -/
theorem exists_weights (p q r p' δ : ℝ) :
    ∃ l₀ l₁ l₂ : ℝ, l₀ = 2 * (1 / p' - δ) / (1 - 2 * δ) ∧ l₁ = (1 / p - 1 / q) / (1 - 2 * δ) ∧
      l₂ = (1 / r - 1) / (1 - 2 * δ) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ### N50 (P5), (P6): the chain `τ₀ < τ₁ < ⋯ < τ_M = 3/4` -/

/-- The cutoff chain `τ_j = (3/4) ρ^(M-j)` of (P6). -/
noncomputable def tauChain (ρ : ℝ) (M j : ℕ) : ℝ := 3 / 4 * ρ ^ (M - j)

theorem tauChain_pos {ρ : ℝ} (hρ : 0 < ρ) (M j : ℕ) : 0 < tauChain ρ M j := by
  unfold tauChain
  positivity

theorem tauChain_zero (ρ : ℝ) (M : ℕ) : tauChain ρ M 0 = 3 / 4 * ρ ^ M := by
  simp [tauChain]

theorem tauChain_self (ρ : ℝ) (M : ℕ) : tauChain ρ M M = 3 / 4 := by
  simp [tauChain]

theorem tauChain_lt_succ {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) {M j : ℕ} (hj : j < M) :
    tauChain ρ M j < tauChain ρ M (j + 1) := by
  unfold tauChain
  have hlt : M - (j + 1) < M - j := by omega
  have := pow_lt_pow_right_of_lt_one₀ hρ₀ hρ₁ hlt
  linarith

/-- `τ_{j-1} = ρ τ_j` for `1 ≤ j ≤ M`. -/
theorem tauChain_pred {ρ : ℝ} {M j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ M) :
    tauChain ρ M (j - 1) = ρ * tauChain ρ M j := by
  unfold tauChain
  have e : M - (j - 1) = (M - j) + 1 := by omega
  rw [e, pow_succ]
  ring

/-- (P6): `2 τ_j t < τ_{j-1}/p'` for `1 ≤ j ≤ M`, provided `ρ > 2 t p'`. -/
theorem tauChain_group_cutoff {ρ t p' : ℝ} (hρ₀ : 0 < ρ) (hp' : 0 < p') (hρ : 2 * t * p' < ρ)
    {M j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ M) :
    2 * tauChain ρ M j * t < tauChain ρ M (j - 1) / p' := by
  have hτ := tauChain_pos hρ₀ M j
  have h2 : 2 * t < ρ / p' := (lt_div_iff₀ hp').2 hρ
  rw [tauChain_pred h1 hj]
  calc 2 * tauChain ρ M j * t = tauChain ρ M j * (2 * t) := by ring
    _ < tauChain ρ M j * (ρ / p') := mul_lt_mul_of_pos_left h2 hτ
    _ = ρ * tauChain ρ M j / p' := by ring

/-- (P5), (P6): the ratio `ρ ∈ (2 t p', 1)`, the integer `M ≥ 1` with `(3/4) ρ^M < r θ / 4`, and
the chain `τ_j = (3/4) ρ^(M-j)`: `0 < τ₀ < r θ / 4`, `τ₀ < τ₁ < ⋯ < τ_M = 3/4` and
`2 τ_j t < τ_{j-1}/p'` for `1 ≤ j ≤ M`.  Needs `2 t p' < 1`, i.e. `1/p' > 2t` (`e:range-gaps`). -/
theorem exists_tauChain {p' t r θ : ℝ} (hp' : 0 < p') (ht : 0 < t) (hr : 0 < r) (hθ : 0 < θ)
    (h2t : 2 * t * p' < 1) :
    ∃ (ρ : ℝ) (M : ℕ), 2 * t * p' < ρ ∧ ρ < 1 ∧ 1 ≤ M ∧ 3 / 4 * ρ ^ M < r * θ / 4 ∧
      0 < tauChain ρ M 0 ∧ tauChain ρ M 0 < r * θ / 4 ∧ tauChain ρ M M = 3 / 4 ∧
      (∀ j, j < M → tauChain ρ M j < tauChain ρ M (j + 1)) ∧
      (∀ j, 1 ≤ j → j ≤ M → 2 * tauChain ρ M j * t < tauChain ρ M (j - 1) / p') := by
  have h0 : 0 < 2 * t * p' := by positivity
  set ρ : ℝ := (1 + 2 * t * p') / 2 with hρdef
  have hρ₁ : 2 * t * p' < ρ := by rw [hρdef]; linarith
  have hρ₂ : ρ < 1 := by rw [hρdef]; linarith
  have hρ₀ : 0 < ρ := lt_trans h0 hρ₁
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := r * θ / 3) (by positivity) hρ₂
  have hM : ρ ^ (n + 1) < ρ ^ n := pow_lt_pow_right_of_lt_one₀ hρ₀ hρ₂ (Nat.lt_succ_self n)
  have hsmall : 3 / 4 * ρ ^ (n + 1) < r * θ / 4 := by linarith
  refine ⟨ρ, n + 1, hρ₁, hρ₂, by omega, hsmall, ?_, ?_,
    tauChain_self ρ (n + 1), fun j hj => tauChain_lt_succ hρ₀ hρ₂ hj,
    fun j h1 hj => tauChain_group_cutoff hρ₀ hp' hρ₁ h1 hj⟩
  · exact tauChain_pos hρ₀ _ _
  · rw [tauChain_zero]
    exact hsmall

/-! ### N50 (P7): the quantities `σ_j(δ)` and the choice of one small `δ` -/

/-- (P7): `σ_j(δ) = (-τ_{j-1}(1/p' - δ) + 2 τ_j (1-δ) t)/(1 - 2δ)`. -/
noncomputable def sigma (p' t : ℝ) (τ : ℕ → ℝ) (j : ℕ) (δ : ℝ) : ℝ :=
  (-τ (j - 1) * (1 / p' - δ) + 2 * τ j * (1 - δ) * t) / (1 - 2 * δ)

/-- `σ_j(0) = -τ_{j-1}/p' + 2 τ_j t`. -/
theorem sigma_zero (p' t : ℝ) (τ : ℕ → ℝ) (j : ℕ) :
    sigma p' t τ j 0 = -(τ (j - 1) / p') + 2 * τ j * t := by
  unfold sigma
  ring

/-- (P7): `σ_j(0) < 0`, from (P6). -/
theorem sigma_zero_neg {p' t : ℝ} {τ : ℕ → ℝ} {j : ℕ} (h : 2 * τ j * t < τ (j - 1) / p') :
    sigma p' t τ j 0 < 0 := by
  rw [sigma_zero]
  linarith

/-- (P7): `σ_j` is continuous in `δ` at `0`. -/
theorem sigma_continuousAt (p' t : ℝ) (τ : ℕ → ℝ) (j : ℕ) :
    ContinuousAt (fun δ : ℝ => sigma p' t τ j δ) 0 := by
  unfold sigma
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · norm_num

/-- (P7): one single small `δ ∈ (0, min{1/2, 1/p'})` makes all `σ_j(δ)`, `1 ≤ j ≤ M`, negative. -/
theorem exists_delta {p' t : ℝ} {τ : ℕ → ℝ} {M : ℕ} (hp' : 0 < p')
    (h : ∀ j, 1 ≤ j → j ≤ M → 2 * τ j * t < τ (j - 1) / p') :
    ∃ δ : ℝ, 0 < δ ∧ δ < min (1 / 2) (1 / p') ∧
      ∀ j, 1 ≤ j → j ≤ M → sigma p' t τ j δ < 0 := by
  have hev : ∀ᶠ δ in nhds (0 : ℝ), ∀ j ∈ Finset.Icc 1 M, sigma p' t τ j δ < 0 := by
    rw [Filter.eventually_all_finset]
    intro j hj
    have hj' := Finset.mem_Icc.1 hj
    have h0 : sigma p' t τ j 0 < 0 := sigma_zero_neg (h j hj'.1 hj'.2)
    exact (sigma_continuousAt p' t τ j).eventually (gt_mem_nhds h0)
  have hlt : ∀ᶠ δ in nhds (0 : ℝ), δ < min (1 / 2) (1 / p') :=
    gt_mem_nhds (lt_min (by norm_num) (one_div_pos.2 hp'))
  have hall : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), (∀ j ∈ Finset.Icc 1 M, sigma p' t τ j δ < 0) ∧
      δ < min (1 / 2) (1 / p') ∧ 0 < δ :=
    (hev.and hlt).filter_mono nhdsWithin_le_nhds |>.and self_mem_nhdsWithin
      |>.mono fun δ hδ => ⟨hδ.1.1, hδ.1.2, hδ.2⟩
  obtain ⟨δ, h1, h2, h3⟩ := hall.exists
  exact ⟨δ, h3, h2, fun j hj1 hj2 => h1 j (Finset.mem_Icc.2 ⟨hj1, hj2⟩)⟩

/-! ### N50 (P10): the strict gap `μ` -/

/-- (P10): the strict gap `μ = min{3θ/8 - t, θ/4 - τ₀/r, -σ_1(δ), …, -σ_M(δ)}`: there is `μ > 0`
which is `≤` each of the finitely many gaps and equal to one of them (so it is their minimum). -/
theorem exists_mu {p' t r θ δ : ℝ} {τ : ℕ → ℝ} {M : ℕ} (hM : 1 ≤ M)
    (hE : t < 3 * θ / 8) (hτ : τ 0 / r < θ / 4)
    (hσ : ∀ j, 1 ≤ j → j ≤ M → sigma p' t τ j δ < 0) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 3 * θ / 8 - t ∧ μ ≤ θ / 4 - τ 0 / r ∧
      (∀ j, 1 ≤ j → j ≤ M → μ ≤ -sigma p' t τ j δ) ∧
      (μ = 3 * θ / 8 - t ∨ μ = θ / 4 - τ 0 / r ∨
        ∃ j, 1 ≤ j ∧ j ≤ M ∧ μ = -sigma p' t τ j δ) := by
  obtain ⟨j₀, hj₀, hmin⟩ := Finset.exists_min_image (Finset.Icc 1 M)
    (fun j => -sigma p' t τ j δ) ⟨1, Finset.mem_Icc.2 ⟨le_refl 1, hM⟩⟩
  have hj₀' := Finset.mem_Icc.1 hj₀
  have hs : 0 < -sigma p' t τ j₀ δ := by
    have := hσ j₀ hj₀'.1 hj₀'.2
    linarith
  refine ⟨min (min (3 * θ / 8 - t) (θ / 4 - τ 0 / r)) (-sigma p' t τ j₀ δ), ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_min (lt_min (by linarith) (by linarith)) hs
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · intro j h1 h2
    exact (min_le_right _ _).trans (hmin j (Finset.mem_Icc.2 ⟨h1, h2⟩))
  · rcases min_choice (min (3 * θ / 8 - t) (θ / 4 - τ 0 / r)) (-sigma p' t τ j₀ δ) with h | h
    · rcases min_choice (3 * θ / 8 - t) (θ / 4 - τ 0 / r) with h' | h'
      · left
        rw [h, h']
      · right
        left
        rw [h, h']
    · right
      right
      exact ⟨j₀, hj₀'.1, hj₀'.2, h⟩

/-! ### N51: the case `r ≥ 1` -/

/-- N51 step 4 (the "other Banach tuple"), formulas: if `1/p + 1/q ≤ 1` and the weight
`1 - θ₁` of `c = (1/2, 1/2)` lies in `(0, 2 min{1/p, 1/q})`, then
`1/p₁ = (1/p - (1-θ₁)/2)/θ₁`, `1/q₁ = (1/q - (1-θ₁)/2)/θ₁` define a Banach tuple
(`1 < p₁, q₁`, `1/p₁ + 1/q₁ ≤ 1`) with `(1/p, 1/q) = (1-θ₁)(1/2, 1/2) + θ₁ (1/p₁, 1/q₁)`.
(In the notation of `docs/FINDINGS.md`, the weight on `(1/2,1/2)` is `1 - θ₁`.) -/
theorem banach_partner_spec (hpq : 1 / p + 1 / q ≤ 1) {θ₁ p₁ q₁ : ℝ}
    (hθp : 1 - θ₁ < 2 * (1 / p)) (hθq : 1 - θ₁ < 2 * (1 / q))
    (h1 : 1 / p₁ = (1 / p - (1 - θ₁) / 2) / θ₁) (h2 : 1 / q₁ = (1 / q - (1 - θ₁) / 2) / θ₁) :
    0 < θ₁ ∧ 1 < p₁ ∧ 1 < q₁ ∧ 1 / p₁ + 1 / q₁ ≤ 1 ∧
      (1 - θ₁) * (1 / 2) + θ₁ * (1 / p₁) = 1 / p ∧
      (1 - θ₁) * (1 / 2) + θ₁ * (1 / q₁) = 1 / q := by
  have hθ0 : 0 < θ₁ := by linarith
  have hθ' : θ₁ ≠ 0 := hθ0.ne'
  have hu0 : 0 < 1 / p₁ := by
    rw [h1]
    exact div_pos (by linarith) hθ0
  have hu1 : 1 / p₁ < 1 := by
    rw [h1, div_lt_one hθ0]
    linarith
  have hv0 : 0 < 1 / q₁ := by
    rw [h2]
    exact div_pos (by linarith) hθ0
  have hv1 : 1 / q₁ < 1 := by
    rw [h2, div_lt_one hθ0]
    linarith
  have hp₁ : 0 < p₁ := one_div_pos.1 hu0
  have hq₁ : 0 < q₁ := one_div_pos.1 hv0
  refine ⟨hθ0, (div_lt_one hp₁).1 hu1, (div_lt_one hq₁).1 hv1, ?_, ?_, ?_⟩
  · rw [h1, h2, ← add_div, div_le_one hθ0]
    linarith
  · rw [h1]
    have : θ₁ * ((1 / p - (1 - θ₁) / 2) / θ₁) = 1 / p - (1 - θ₁) / 2 := by
      field_simp
    rw [this]
    ring
  · rw [h2]
    have : θ₁ * ((1 / q - (1 - θ₁) / 2) / θ₁) = 1 / q - (1 - θ₁) / 2 := by
      field_simp
    rw [this]
    ring

/-- N51 step 4: for every `1 < p, q < ∞` with `1/p + 1/q ≤ 1` there is a Banach partner tuple
`(p₁, q₁, r₁)` (`1 < p₁, q₁`, `r₁ ≥ 1`, `1/r₁ = 1/p₁ + 1/q₁`) and a weight `θ₁ ∈ (0,1)` with
`(1/p, 1/q, 1/p + 1/q) = (1-θ₁)(1/2, 1/2, 1) + θ₁ (1/p₁, 1/q₁, 1/r₁)`. -/
theorem exists_banach_partner (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q ≤ 1) :
    ∃ θ₁ p₁ q₁ r₁ : ℝ, 0 < θ₁ ∧ θ₁ < 1 ∧ 1 < p₁ ∧ 1 < q₁ ∧ 1 ≤ r₁ ∧
      1 / r₁ = 1 / p₁ + 1 / q₁ ∧
      1 / p = (1 - θ₁) * (1 / 2) + θ₁ * (1 / p₁) ∧
      1 / q = (1 - θ₁) * (1 / 2) + θ₁ * (1 / q₁) ∧
      1 / p + 1 / q = (1 - θ₁) * 1 + θ₁ * (1 / r₁) := by
  have ha : 0 < 1 / p := one_div_pos.2 (lt_trans zero_lt_one hp)
  have hb : 0 < 1 / q := one_div_pos.2 (lt_trans zero_lt_one hq)
  set w : ℝ := min (1 / p) (1 / q) with hw
  have hw0 : 0 < w := lt_min ha hb
  have hwa : w ≤ 1 / p := min_le_left _ _
  have hwb : w ≤ 1 / q := min_le_right _ _
  have hθ₁ : 1 - w < 1 := by linarith
  obtain ⟨θ₁, hθdef⟩ : ∃ θ₁ : ℝ, θ₁ = 1 - w := ⟨_, rfl⟩
  have hθ₁ : θ₁ < 1 := by rw [hθdef]; linarith
  have hwθ : 1 - θ₁ = w := by rw [hθdef]; ring
  have hθp : 1 - θ₁ < 2 * (1 / p) := by rw [hwθ]; linarith
  have hθq : 1 - θ₁ < 2 * (1 / q) := by rw [hwθ]; linarith
  obtain ⟨p₁, h1⟩ : ∃ p₁ : ℝ, 1 / p₁ = (1 / p - (1 - θ₁) / 2) / θ₁ :=
    ⟨1 / ((1 / p - (1 - θ₁) / 2) / θ₁), by rw [one_div_one_div]⟩
  obtain ⟨q₁, h2⟩ : ∃ q₁ : ℝ, 1 / q₁ = (1 / q - (1 - θ₁) / 2) / θ₁ :=
    ⟨1 / ((1 / q - (1 - θ₁) / 2) / θ₁), by rw [one_div_one_div]⟩
  obtain ⟨hθ0, hp₁, hq₁, hsum, e1, e2⟩ := banach_partner_spec hpq hθp hθq h1 h2
  have hpos : 0 < 1 / p₁ + 1 / q₁ :=
    add_pos (one_div_pos.2 (lt_trans zero_lt_one hp₁)) (one_div_pos.2 (lt_trans zero_lt_one hq₁))
  obtain ⟨r₁, hr1def⟩ : ∃ r₁ : ℝ, 1 / r₁ = 1 / p₁ + 1 / q₁ :=
    ⟨1 / (1 / p₁ + 1 / q₁), by rw [one_div_one_div]⟩
  have hr₁pos : 0 < r₁ := one_div_pos.1 (by rw [hr1def]; exact hpos)
  have hr₁ : 1 ≤ r₁ := (div_le_one hr₁pos).1 (by rw [hr1def]; exact hsum)
  refine ⟨θ₁, p₁, q₁, r₁, hθ0, hθ₁, hp₁, hq₁, hr₁, hr1def, e1.symm, e2.symm, ?_⟩
  rw [hr1def]
  linear_combination (-1 : ℝ) * e1 + (-1 : ℝ) * e2

/-- N51, the power saving: with `ε = (1-θ₁)/(40 θ₁)` the interpolated exponent
`(-1/20)(1 - θ₁) + ε θ₁` equals `-σ` with `σ = (1 - θ₁)/40 > 0`. -/
theorem power_saving {θ₁ : ℝ} (h0 : 0 < θ₁) (h1 : θ₁ < 1) :
    0 < (1 - θ₁) / (40 * θ₁) ∧ 0 < (1 - θ₁) / 40 ∧
      -(1 / 20) * (1 - θ₁) + (1 - θ₁) / (40 * θ₁) * θ₁ = -((1 - θ₁) / 40) := by
  have h1' : 0 < 1 - θ₁ := by linarith
  refine ⟨by positivity, by positivity, ?_⟩
  field_simp
  ring

/-! ### N50: the bundled exponent data -/

/-- N50: all exponent parameters (P1)-(P10) for a target `(p, q, r) ∈ R`, `r < 1`, `p ≤ q`,
chosen in the order of the blueprint.  `p'` is the Hölder conjugate of `p`
(`1/p + 1/p' = 1`), `t = 1/r - 1`, `a = 1/p`, `b = 1/q`.  The chain is `τ_j = (3/4) ρ^(M-j)`
(`τ : ℕ → ℝ` is only constrained for `j ≤ M`, but is given by the formula everywhere). -/
structure ExponentData (p q r : ℝ) where
  p' : ℝ
  t : ℝ
  θ : ℝ
  p₀ : ℝ
  q₀ : ℝ
  r₀ : ℝ
  ρ : ℝ
  M : ℕ
  τ : ℕ → ℝ
  δ : ℝ
  l₀ : ℝ
  l₁ : ℝ
  l₂ : ℝ
  μ : ℝ
  /-- `p'` is the Hölder conjugate of `p`. -/
  conj : 1 / p + 1 / p' = 1
  -- (P1)
  t_eq : t = 1 / r - 1
  t_pos : 0 < t
  t_lt_fifth : t < 1 / 5
  two_t_lt : 2 * t < 1 / p'
  half_lt : 1 / 2 < 1 / p
  inv_p'_lt : 1 / p' < 1 / q
  three_t_lt : 3 * t < 1 / q
  -- (P2)
  θ_gt : 8 * t / 3 < θ
  θ_lt : θ < min (2 * (1 / p')) (1 - 2 * t)
  -- (P3)
  inv_p₀ : 1 / p₀ = (1 / p - θ / 2) / (1 - θ)
  inv_q₀ : 1 / q₀ = (1 / q - θ / 2) / (1 - θ)
  inv_r₀ : 1 / r₀ = (1 / r - θ) / (1 - θ)
  one_lt_p₀ : 1 < p₀
  one_lt_q₀ : 1 < q₀
  two_thirds_lt_r₀ : 2 / 3 < r₀
  r₀_lt_one : r₀ < 1
  inv_p₀_add_inv_q₀ : 1 / p₀ + 1 / q₀ = 1 / r₀
  inv_r₀_eq : 1 / r₀ = 1 + t / (1 - θ)
  interp_p : (1 - θ) * (1 / p₀) + θ * (1 / 2) = 1 / p
  interp_q : (1 - θ) * (1 / q₀) + θ * (1 / 2) = 1 / q
  interp_r : (1 - θ) * (1 / r₀) + θ * 1 = 1 + t
  -- (P4)
  E_U_neg : t - 3 * θ / 8 < 0
  -- (P5), (P6)
  ρ_gt : 2 * t * p' < ρ
  ρ_lt_one : ρ < 1
  one_le_M : 1 ≤ M
  pow_lt : 3 / 4 * ρ ^ M < r * θ / 4
  τ_def : ∀ j, τ j = 3 / 4 * ρ ^ (M - j)
  τ_zero_pos : 0 < τ 0
  τ_zero_lt : τ 0 < r * θ / 4
  E₀_neg : τ 0 / r - θ / 4 < 0
  τ_M : τ M = 3 / 4
  τ_lt_succ : ∀ j, j < M → τ j < τ (j + 1)
  group_cutoff : ∀ j, 1 ≤ j → j ≤ M → 2 * τ j * t < τ (j - 1) / p'
  -- (P7)
  δ_pos : 0 < δ
  δ_lt : δ < min (1 / 2) (1 / p')
  sigma_neg : ∀ j, 1 ≤ j → j ≤ M → sigma p' t τ j δ < 0
  -- (P8)
  l₀_eq : l₀ = 2 * (1 / p' - δ) / (1 - 2 * δ)
  l₁_eq : l₁ = (1 / p - 1 / q) / (1 - 2 * δ)
  l₂_eq : l₂ = t / (1 - 2 * δ)
  l₀_nonneg : 0 ≤ l₀
  l₁_nonneg : 0 ≤ l₁
  l₂_pos : 0 < l₂
  l_sum : l₀ + l₁ + l₂ = 1
  l₂_lt_one : l₂ < 1
  -- (P9)
  coord_p : l₀ * (1 / 2) + l₁ * (1 - δ) + l₂ * (1 - δ) = 1 / p
  coord_q : l₀ * (1 / 2) + l₁ * δ + l₂ * (1 - δ) = 1 / q
  coord_r : l₀ * 1 + l₁ * 1 + l₂ * (2 - 2 * δ) = 1 + t
  -- (P10)
  μ_pos : 0 < μ
  μ_le_E_U : μ ≤ 3 * θ / 8 - t
  μ_le_E₀ : μ ≤ θ / 4 - τ 0 / r
  μ_le_sigma : ∀ j, 1 ≤ j → j ≤ M → μ ≤ -sigma p' t τ j δ
  μ_min : μ = 3 * θ / 8 - t ∨ μ = θ / 4 - τ 0 / r ∨ ∃ j, 1 ≤ j ∧ j ≤ M ∧ μ = -sigma p' t τ j δ

/-- N50 (constructor theorem): for `(p, q, r) ∈ R`, `r < 1`, `p ≤ q` the exponent data exist. -/
theorem InR.exists_exponentData (h : InR p q r) (hr : r < 1) (hpq : p ≤ q) :
    Nonempty (ExponentData p q r) := by
  -- (P1)
  have hp1 : 0 < 1 - 1 / p := by
    have := h.inv_p_lt_one
    linarith
  obtain ⟨p', hp'def⟩ : ∃ p' : ℝ, 1 / p' = 1 - 1 / p :=
    ⟨1 / (1 - 1 / p), by rw [one_div_one_div]⟩
  have hp'pos : 0 < p' := one_div_pos.1 (by rw [hp'def]; exact hp1)
  have hconj : 1 / p + 1 / p' = 1 := by rw [hp'def]; ring
  have ht0 := h.t_pos hr
  have ht1 := h.t_lt_fifth hr hpq
  have h2t := h.two_mul_t_lt hr hpq
  have hhalf := h.half_lt_inv_p hr hpq
  have hb1 := h.one_sub_inv_p_lt_inv_q hr hpq
  have hb2 := h.three_mul_t_lt_inv_q hr hpq
  -- (P2)
  obtain ⟨θ, hθ₁, hθ₂⟩ := h.exists_theta hr hpq
  have hθ0 := theta_pos h hr hpq hθ₁ hθ₂
  -- (P3)
  obtain ⟨p₀, q₀, r₀, h0p, h0q, h0r⟩ := exists_tuple p q r θ
  obtain ⟨hp₀, hq₀, hr₀a, hr₀b, hsum, hr₀eq, ip, iq, ir⟩ :=
    h.tuple_spec hr hpq hθ₁ hθ₂ h0p h0q h0r
  have hEU := E_U_neg h hr hpq hθ₁ hθ₂
  -- (P6)
  have h2tp' : 2 * (1 / r - 1) * p' < 1 := by
    have : 2 * (1 / r - 1) < 1 / p' := by rw [hp'def]; exact h2t
    exact (lt_div_iff₀ hp'pos).1 this
  obtain ⟨ρ, M, hρ1, hρ2, hM, hpow, hτ0, hτ0lt, hτM, hτinc, hτgrp⟩ :=
    exists_tauChain hp'pos ht0 h.pos_r hθ0 h2tp'
  have hE0' : tauChain ρ M 0 / r - θ / 4 < 0 := by
    have := E₀_neg_iff h hr hpq hθ₁ hθ₂ (τ₀ := tauChain ρ M 0)
    exact this.2 hτ0lt
  -- (P7)
  obtain ⟨δ, hδ0, hδlt, hσ⟩ := exists_delta (τ := tauChain ρ M) (M := M) hp'pos hτgrp
  have hδ1 : δ < 1 / 2 := (lt_min_iff.1 hδlt).1
  have hδ2 : δ < 1 / p' := (lt_min_iff.1 hδlt).2
  -- (P8), (P9)
  obtain ⟨l₀, l₁, l₂, hl₀, hl₁, hl₂⟩ := exists_weights p q r p' δ
  obtain ⟨hl0, hl1, hl2, hlsum, hl2lt, hc1, hc2, hc3⟩ :=
    h.weights_spec hr hpq hconj hδ1 hδ2 hl₀ hl₁ hl₂
  -- (P10)
  obtain ⟨μ, hμ0, hμ1, hμ2, hμ3, hμ4⟩ := exists_mu (p' := p') (t := 1 / r - 1) (r := r) (θ := θ) (δ := δ)
    (τ := tauChain ρ M) hM (by linarith) (by linarith) hσ
  refine ⟨{
    p' := p', t := 1 / r - 1, θ := θ, p₀ := p₀, q₀ := q₀, r₀ := r₀, ρ := ρ, M := M,
    τ := tauChain ρ M, δ := δ, l₀ := l₀, l₁ := l₁, l₂ := l₂, μ := μ
    conj := hconj
    t_eq := rfl
    t_pos := ht0
    t_lt_fifth := ht1
    two_t_lt := by rw [hp'def]; exact h2t
    half_lt := hhalf
    inv_p'_lt := by rw [hp'def]; exact hb1
    three_t_lt := hb2
    θ_gt := hθ₁
    θ_lt := by rw [hp'def]; exact hθ₂
    inv_p₀ := h0p
    inv_q₀ := h0q
    inv_r₀ := h0r
    one_lt_p₀ := hp₀
    one_lt_q₀ := hq₀
    two_thirds_lt_r₀ := hr₀a
    r₀_lt_one := hr₀b
    inv_p₀_add_inv_q₀ := hsum
    inv_r₀_eq := hr₀eq
    interp_p := ip
    interp_q := iq
    interp_r := by rw [ir]; ring
    E_U_neg := by linarith
    ρ_gt := hρ1
    ρ_lt_one := hρ2
    one_le_M := hM
    pow_lt := hpow
    τ_def := fun j => rfl
    τ_zero_pos := hτ0
    τ_zero_lt := hτ0lt
    E₀_neg := hE0'
    τ_M := hτM
    τ_lt_succ := hτinc
    group_cutoff := hτgrp
    δ_pos := hδ0
    δ_lt := hδlt
    sigma_neg := hσ
    l₀_eq := hl₀
    l₁_eq := hl₁
    l₂_eq := hl₂
    l₀_nonneg := hl0
    l₁_nonneg := hl1
    l₂_pos := hl2
    l_sum := hlsum
    l₂_lt_one := hl2lt
    coord_p := hc1
    coord_q := hc2
    coord_r := by rw [hc3]; ring
    μ_pos := hμ0
    μ_le_E_U := hμ1
    μ_le_E₀ := hμ2
    μ_le_sigma := hμ3
    μ_min := hμ4 }⟩

/-! ### N53: the exponent `100 s_r > 1` -/

end PrimeBHT.Exponents
