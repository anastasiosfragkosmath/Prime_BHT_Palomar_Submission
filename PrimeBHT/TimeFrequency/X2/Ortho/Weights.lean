module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import PrimeBHT.TimeFrequency.Tile.Gram.Pair

/-!
# X2, node V10: polynomial weights and the localization of Gram integrals

`wt q c ℓ x = (1 + |x - c|/ℓ)^{-q}`.  The two facts the TT* argument needs:

* `integral_wt`: `∫ wt q c ℓ = 2 ℓ/(q - 1)`;
* `integral_wt_mul_le` (**localization**): for `0 < ℓ' ≤ ℓ`, `|y - c'| ≤ ℓ'`,
  `∫ wt q c ℓ · wt (2q) c' ℓ' ≤ (2^{q+1}/(q-1)) ℓ' · wt q c ℓ (y)`.
  (This covers the same-scale translates `|c - c'| = nℓ`, `y = c'`, and the nested tiles `ℓ' ≤ ℓ`, `y ∈ I'`.)
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- The polynomial weight `(1 + |x - c|/ℓ)^{-q}`. -/
def wt (q c ℓ x : ℝ) : ℝ := (1 + |x - c| / ℓ) ^ (-q)

theorem wt_pos (q c ℓ x : ℝ) (hℓ : 0 < ℓ) : 0 < wt q c ℓ x :=
  Real.rpow_pos_of_pos (by positivity) _

theorem wt_le_one {q : ℝ} (hq : 0 ≤ q) (c ℓ x : ℝ) (hℓ : 0 < ℓ) : wt q c ℓ x ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by have := div_nonneg (abs_nonneg (x - c)) hℓ.le; linarith)
    (by linarith)

theorem continuous_wt (q c ℓ : ℝ) (hℓ : 0 < ℓ) : Continuous (wt q c ℓ) := by
  unfold wt
  exact Continuous.rpow_const (by fun_prop) (fun x => Or.inl (by positivity))

theorem integrable_wt {q : ℝ} (hq : 1 < q) (c : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) : Integrable (wt q c ℓ) :=
  integrable_one_add_abs_sub_div_rpow hq c hℓ

theorem integral_wt {q : ℝ} (hq : 1 < q) (c : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫ x, wt q c ℓ x = 2 * ℓ / (q - 1) :=
  integral_one_add_abs_sub_div_rpow hq c hℓ

/-- Peetre: `wt q c ℓ x ≤ (1 + |x - y|/ℓ)^q wt q c ℓ y`. -/
theorem wt_peetre {q : ℝ} (hq : 0 ≤ q) (c : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (x y : ℝ) :
    wt q c ℓ x ≤ (1 + |x - y| / ℓ) ^ q * wt q c ℓ y := by
  unfold wt
  have h1 : 0 < 1 + |x - c| / ℓ := by positivity
  have h2 : 0 < 1 + |y - c| / ℓ := by positivity
  have h3 : 0 < 1 + |x - y| / ℓ := by positivity
  have hA : 1 + |y - c| / ℓ ≤ (1 + |x - y| / ℓ) * (1 + |x - c| / ℓ) := by
    have : |y - c| ≤ |x - y| + |x - c| := by
      have := abs_sub_le y x c
      rw [abs_sub_comm y x] at this; exact this
    have hd : |y - c| / ℓ ≤ |x - y| / ℓ + |x - c| / ℓ := by
      rw [← add_div]; exact div_le_div_of_nonneg_right this hℓ.le
    nlinarith [div_nonneg (abs_nonneg (x - y)) hℓ.le, div_nonneg (abs_nonneg (x - c)) hℓ.le,
      mul_nonneg (div_nonneg (abs_nonneg (x - y)) hℓ.le) (div_nonneg (abs_nonneg (x - c)) hℓ.le)]
  have hB : (1 + |y - c| / ℓ) ^ q ≤ ((1 + |x - y| / ℓ) * (1 + |x - c| / ℓ)) ^ q :=
    Real.rpow_le_rpow h2.le hA hq
  rw [Real.mul_rpow h3.le h1.le] at hB
  rw [Real.rpow_neg h1.le, Real.rpow_neg h2.le]
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, le_div_iff₀ (by positivity)]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [Real.rpow_pos_of_pos h1 q, Real.rpow_pos_of_pos h3 q, Real.rpow_pos_of_pos h2 q]

/-- **Localization of the Gram integral.** -/
theorem integral_wt_mul_le {q : ℝ} (hq : 1 < q) {c ℓ c' ℓ' : ℝ} (hℓ' : 0 < ℓ') (hle : ℓ' ≤ ℓ) {y : ℝ}
    (hy : |y - c'| ≤ ℓ') :
    ∫ x, wt q c ℓ x * wt (2 * q) c' ℓ' x ≤ 2 ^ q * (2 * ℓ' / (q - 1)) * wt q c ℓ y := by
  have hℓ : 0 < ℓ := lt_of_lt_of_le hℓ' hle
  have hq0 : 0 ≤ q := by linarith
  have hpt : ∀ x, wt q c ℓ x * wt (2 * q) c' ℓ' x ≤ (2 ^ q * wt q c ℓ y) * wt q c' ℓ' x := by
    intro x
    have h1 := wt_peetre hq0 c hℓ x y
    have hB : 1 + |x - y| / ℓ ≤ 1 + |x - y| / ℓ' := by
      have : |x - y| / ℓ ≤ |x - y| / ℓ' := div_le_div_of_nonneg_left (abs_nonneg _) hℓ' hle
      linarith
    have hC : 1 + |x - y| / ℓ' ≤ 2 * (1 + |x - c'| / ℓ') := by
      have : |x - y| ≤ |x - c'| + |c' - y| := abs_sub_le x c' y
      have h2 : |c' - y| ≤ ℓ' := by rw [abs_sub_comm]; exact hy
      have : |x - y| / ℓ' ≤ |x - c'| / ℓ' + 1 := by
        calc |x - y| / ℓ' ≤ (|x - c'| + ℓ') / ℓ' := div_le_div_of_nonneg_right (by linarith) hℓ'.le
          _ = |x - c'| / ℓ' + 1 := by field_simp
      have := div_nonneg (abs_nonneg (x - c')) hℓ'.le
      linarith
    have hD : (1 + |x - y| / ℓ) ^ q ≤ (2 * (1 + |x - c'| / ℓ')) ^ q :=
      Real.rpow_le_rpow (by positivity) (hB.trans hC) hq0
    have h3 : 0 < 1 + |x - c'| / ℓ' := by positivity
    have hw2 : wt (2 * q) c' ℓ' x = wt q c' ℓ' x * wt q c' ℓ' x := by
      unfold wt
      rw [← Real.rpow_add h3]; congr 1; ring
    have hwq : wt q c' ℓ' x * (1 + |x - c'| / ℓ') ^ q = 1 := by
      unfold wt
      rw [← Real.rpow_add h3]; simp
    calc wt q c ℓ x * wt (2 * q) c' ℓ' x ≤ ((1 + |x - y| / ℓ) ^ q * wt q c ℓ y) * wt (2 * q) c' ℓ' x :=
          mul_le_mul_of_nonneg_right h1 (wt_pos _ _ _ _ hℓ').le
      _ ≤ ((2 * (1 + |x - c'| / ℓ')) ^ q * wt q c ℓ y) * wt (2 * q) c' ℓ' x := by
          have := wt_pos q c ℓ y hℓ
          have := wt_pos (2 * q) c' ℓ' x hℓ'
          gcongr
      _ = (2 ^ q * wt q c ℓ y) * wt q c' ℓ' x := by
          rw [Real.mul_rpow (by norm_num) h3.le, hw2]
          have hE : (1 + |x - c'| / ℓ') ^ q * wt q c' ℓ' x = 1 := by rw [mul_comm]; exact hwq
          calc (2 ^ q * (1 + |x - c'| / ℓ') ^ q * wt q c ℓ y) * (wt q c' ℓ' x * wt q c' ℓ' x)
              = (2 ^ q * wt q c ℓ y) * ((1 + |x - c'| / ℓ') ^ q * wt q c' ℓ' x) * wt q c' ℓ' x := by ring
            _ = _ := by rw [hE]; ring
  have hint : Integrable (fun x => (2 ^ q * wt q c ℓ y) * wt q c' ℓ' x) :=
    (integrable_wt hq c' hℓ').const_mul _
  have hcont : Continuous fun x => wt q c ℓ x * wt (2 * q) c' ℓ' x :=
    (continuous_wt q c ℓ hℓ).mul (continuous_wt (2 * q) c' ℓ' hℓ')
  have hL : Integrable (fun x => wt q c ℓ x * wt (2 * q) c' ℓ' x) := by
    refine hint.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (wt_pos _ _ _ _ hℓ).le (wt_pos _ _ _ _ hℓ').le)]
    exact hpt x
  calc ∫ x, wt q c ℓ x * wt (2 * q) c' ℓ' x ≤ ∫ x, (2 ^ q * wt q c ℓ y) * wt q c' ℓ' x :=
        integral_mono hL hint hpt
    _ = 2 ^ q * (2 * ℓ' / (q - 1)) * wt q c ℓ y := by
        rw [integral_const_mul, integral_wt hq c' hℓ']; ring

end PrimeBHT.TimeFrequency.X2
