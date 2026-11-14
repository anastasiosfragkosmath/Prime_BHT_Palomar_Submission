module

public import PrimeBHT.TimeFrequency.X2.Psp.TreeHardMu

/-!
# X2, V15 (assembly), step 9: modulation

* `tmult_shift_hm`: `T_{μ(· + θ)} g (x) = e(-θ x) T_μ (e(θ ·) g)(x)`;
* `Form_phase3`: `Π(c₁ e(α x) A, c₂ e(β x) B, c₃ e(γ x) C) = c₁ c₂ c₃ Π(A, B, C)` when `α + β = γ` (slot 3 conjugate-linear).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

theorem ovPhase_add_hm (α β y : ℝ) : ovPhase α y * ovPhase β y = ovPhase (α + β) y := by
  unfold ovPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

theorem ovPhase_zero (y : ℝ) : ovPhase 0 y = 1 := by
  unfold ovPhase; simp

theorem conj_ovPhase (α y : ℝ) : (starRingEnd ℂ) (ovPhase α y) = ovPhase (-α) y := by
  unfold ovPhase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1; push_cast; ring

theorem fourierInv_shift_hm (μ : ℝ → ℂ) (θ w : ℝ) :
    𝓕⁻ (fun ξ => μ (ξ + θ)) w = Complex.exp (↑(-2 * π * θ * w) * Complex.I) * 𝓕⁻ μ w := by
  rw [fourierInv_eq_integral_exp, fourierInv_eq_integral_exp, ← integral_const_mul]
  rw [← integral_add_right_eq_self (fun v => Complex.exp (↑(2 * π * v * w) * Complex.I) * μ (v + θ)) (-θ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [neg_add_cancel_right]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 3
  push_cast
  ring

theorem tmult_shift_hm {P : ℕ} (μ : ℝ → ℂ) (θ : ℝ) (g : ℝ → ZMod P → ℂ) (x : ℝ) :
    tmult (fun ξ => μ (ξ + θ)) g x = ovPhase (-θ) x • tmult μ (fun z => ovPhase θ z • g z) x := by
  funext y
  simp only [tmult, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  beta_reduce
  rw [fourierInv_shift_hm]
  unfold ovPhase
  have : Complex.exp (↑(-2 * π * θ * (x - z)) * Complex.I) =
      Complex.exp (↑(2 * π * -θ * x) * Complex.I) * Complex.exp (↑(2 * π * θ * z) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [this]; ring

section Phase

variable {P : ℕ} [NeZero P]

omit [NeZero P] in
theorem Form_cc3 (T : Form P) (p q r : ℂ) (a b d : ZMod P → ℂ) :
    T (p • a) (q • b) (r • d) = p * q * (starRingEnd ℂ) r * T a b d := by
  have h1 : T (p • a) = p • T a := T.map_smul _ _
  have h2 : (T a) (q • b) = q • (T a) b := (T a).map_smul _ _
  have h3 : (T a b) (r • d) = (starRingEnd ℂ) r • (T a b) d := (T a b).map_smulₛₗ _ _
  rw [h1, LinearMap.smul_apply, LinearMap.smul_apply, h2, LinearMap.smul_apply, h3]
  simp only [smul_eq_mul]
  ring

theorem Form_phase3 (T : Form P) (c₁ c₂ c₃ : ℝ) {α β γ : ℝ} (h : α + β = γ) (y : ℝ) (a b d : ZMod P → ℂ) :
    T (((c₁ : ℂ) * ovPhase α y) • a) (((c₂ : ℂ) * ovPhase β y) • b) (((c₃ : ℂ) * ovPhase γ y) • d) =
      ((c₁ * c₂ * c₃ : ℝ) : ℂ) * T a b d := by
  rw [Form_cc3, map_mul, conj_ovPhase, Complex.conj_ofReal]
  have h1 : ovPhase α y * ovPhase β y * ovPhase (-γ) y = 1 := by
    rw [ovPhase_add_hm, ovPhase_add_hm, h, add_neg_cancel, ovPhase_zero]
  calc ((c₁ : ℂ) * ovPhase α y) * ((c₂ : ℂ) * ovPhase β y) * ((c₃ : ℂ) * ovPhase (-γ) y) * T a b d
      = ((c₁ : ℂ) * c₂ * c₃) * (ovPhase α y * ovPhase β y * ovPhase (-γ) y) * T a b d := by ring
    _ = _ := by rw [h1]; push_cast; ring

end Phase

end PrimeBHT.TimeFrequency.X2
