module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import PrimeBHT.TimeFrequency.X2.Ortho.Level
public import PrimeBHT.TimeFrequency.X2.Ortho.TreeToTile
public import PrimeBHT.TimeFrequency.X2.Basic

/-!
# X2, node V10: the closing algebra of HLC `HilbertBasicEst` and the `yInner` Cauchy-Schwarz

* `closing_algebra`: `u⁴ ≤ f C₁ u² + f C₂ g u` implies `u² ≤ 2 C₁ f` or `u³ ≤ 2 C₂ f g` (HLC L695-709);
* `basic_of_closing`: `S² ≤ f (C₁ S + C₂ μ √(S Θ))`, `S = u²` gives
  `S ≤ K (f + (μ² Θ)^{1/3} f^{2/3})`;
* `sq_le_of_forall`: `(∀ λ > 0, 2 λ S ≤ λ² A + B) → S² ≤ A B`;
* `norm_yInner_le`: `|⟨F, G⟩_Y| ≤ ‖F‖_{L²(Y)} ‖G‖_{L²(Y)}`.
-/

@[expose] public noncomputable section

open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

theorem closing_algebra {u f C₁ C₂ g : ℝ} (hu : 0 ≤ u) (hf : 0 ≤ f) (hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂)
    (_hg : 0 ≤ g) (h : u ^ 4 ≤ f * C₁ * u ^ 2 + f * C₂ * g * u) :
    u ^ 2 ≤ 2 * C₁ * f ∨ u ^ 3 ≤ 2 * f * C₂ * g := by
  rcases hu.eq_or_lt with h0 | hpos
  · left; rw [← h0]; simp; positivity
  · by_cases hcase : f * C₁ * u ^ 2 ≤ f * C₂ * g * u
    · right
      have h2 : u ^ 4 ≤ 2 * (f * C₂ * g) * u := by linarith
      have h3 : u * u ^ 3 ≤ u * (2 * f * C₂ * g) := by linarith
      exact le_of_mul_le_mul_left h3 hpos
    · left
      push Not at hcase
      have h2 : u ^ 4 ≤ 2 * (f * C₁) * u ^ 2 := by linarith
      have h3 : u ^ 2 * u ^ 2 ≤ u ^ 2 * (2 * C₁ * f) := by linarith
      exact le_of_mul_le_mul_left h3 (by positivity)

theorem basic_of_closing {S f C₁ C₂ μ Θ : ℝ} (hS : 0 ≤ S) (hf : 0 ≤ f) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hμ : 0 ≤ μ) (hΘ : 0 ≤ Θ) (h : S ^ 2 ≤ f * (C₁ * S + C₂ * (μ * Real.sqrt Θ) * Real.sqrt S)) :
    S ≤ (2 * C₁ + 4 * C₂ ^ 2 + 1) * (f + (μ ^ 2 * Θ) ^ ((1 : ℝ) / 3) * f ^ ((2 : ℝ) / 3)) := by
  set u := Real.sqrt S with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hSu : S = u ^ 2 := (Real.sq_sqrt hS).symm
  set g := μ * Real.sqrt Θ with hg
  have hg0 : 0 ≤ g := by positivity
  have h4 : u ^ 4 ≤ f * C₁ * u ^ 2 + f * C₂ * g * u := by
    have : u ^ 4 = S ^ 2 := by rw [hSu]; ring
    rw [this]
    calc S ^ 2 ≤ f * (C₁ * S + C₂ * g * u) := h
      _ = f * C₁ * u ^ 2 + f * C₂ * g * u := by rw [hSu]; ring
  set m := (μ ^ 2 * Θ) ^ ((1 : ℝ) / 3) with hm
  set φ := f ^ ((1 : ℝ) / 3) with hφ
  have hm0 : 0 ≤ m := Real.rpow_nonneg (by positivity) _
  have hφ0 : 0 ≤ φ := Real.rpow_nonneg hf _
  have hm3 : m ^ 3 = μ ^ 2 * Θ := rpow_third_cube (by positivity)
  have hφ3 : φ ^ 3 = f := rpow_third_cube hf
  have hφ2 : f ^ ((2 : ℝ) / 3) = φ ^ 2 := rpow_two_thirds_eq hf
  rw [hφ2, ← hφ3]
  have hK : 0 ≤ 2 * C₁ + 4 * C₂ ^ 2 + 1 := by positivity
  rcases closing_algebra hu0 hf hC₁ hC₂ hg0 h4 with hA | hB
  · -- `S ≤ 2 C₁ f`
    rw [hSu]
    rw [← hφ3] at hA
    have : 0 ≤ φ ^ 3 := by positivity
    have hmφ : 0 ≤ m * φ ^ 2 := by positivity
    linarith [mul_nonneg hK hmφ, mul_nonneg (sq_nonneg C₂) this]
  · -- `S³ ≤ 4 C₂² f² μ² Θ`
    have hS3 : S ^ 3 ≤ (4 * C₂ ^ 2 + 1) ^ 3 * (m * φ ^ 2) ^ 3 := by
      have h6 : u ^ 6 ≤ (2 * f * C₂ * g) ^ 2 := by
        have : u ^ 6 = (u ^ 3) ^ 2 := by ring
        rw [this]
        exact pow_le_pow_left₀ (by positivity) hB 2
      have hS3' : S ^ 3 = u ^ 6 := by rw [hSu]; ring
      rw [hS3']
      refine h6.trans ?_
      have e : (2 * f * C₂ * g) ^ 2 = 4 * C₂ ^ 2 * f ^ 2 * (μ ^ 2 * Θ) := by
        calc (2 * f * C₂ * g) ^ 2 = 4 * C₂ ^ 2 * f ^ 2 * (μ ^ 2 * (Real.sqrt Θ) ^ 2) := by rw [hg]; ring
          _ = _ := by rw [Real.sq_sqrt hΘ]
      rw [e, ← hm3, ← hφ3]
      have hκ : 4 * C₂ ^ 2 ≤ (4 * C₂ ^ 2 + 1) ^ 3 := by
        linarith [sq_nonneg (C₂ ^ 3), sq_nonneg (C₂ ^ 2), sq_nonneg C₂]
      have : 0 ≤ (m * φ ^ 2) ^ 3 := by positivity
      calc 4 * C₂ ^ 2 * (φ ^ 3) ^ 2 * m ^ 3 = 4 * C₂ ^ 2 * (m * φ ^ 2) ^ 3 := by ring
        _ ≤ (4 * C₂ ^ 2 + 1) ^ 3 * (m * φ ^ 2) ^ 3 := mul_le_mul_of_nonneg_right hκ this
    have hS' : S ≤ (4 * C₂ ^ 2 + 1) * (m * φ ^ 2) := by
      have : S ^ 3 ≤ ((4 * C₂ ^ 2 + 1) * (m * φ ^ 2)) ^ 3 := by rw [mul_pow]; exact hS3
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) this
    have : (4 * C₂ ^ 2 + 1) * (m * φ ^ 2) ≤
        (2 * C₁ + 4 * C₂ ^ 2 + 1) * (φ ^ 3 + m * φ ^ 2) := by
      have : 0 ≤ φ ^ 3 := by positivity
      have h5 : 0 ≤ m * φ ^ 2 := by positivity
      linarith [mul_nonneg hC₁ h5, mul_nonneg hC₁ this, mul_nonneg (sq_nonneg C₂) this]
    linarith

/-- `0 ≤ S`, `(∀ λ > 0, 2 λ S ≤ λ² A + B) → S² ≤ A B`. -/
theorem sq_le_of_forall {S A B : ℝ} (hS : 0 ≤ S) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ l : ℝ, 0 < l → 2 * l * S ≤ l ^ 2 * A + B) : S ^ 2 ≤ A * B := by
  rcases hS.eq_or_lt with hS0 | hSpos
  · rw [← hS0]; simp; positivity
  · rcases hA.eq_or_lt with hA0 | hApos
    · have := h ((B + 1) / S) (by positivity)
      rw [← hA0] at this
      have e : 2 * ((B + 1) / S) * S = 2 * (B + 1) := by field_simp
      rw [e] at this
      linarith
    · have := h (S / A) (by positivity)
      have e : 2 * (S / A) * S = 2 * (S ^ 2 / A) := by ring
      have e2 : (S / A) ^ 2 * A = S ^ 2 / A := by field_simp
      rw [e, e2] at this
      have h3 : S ^ 2 / A ≤ B := by linarith
      rw [div_le_iff₀ hApos] at h3
      linarith

theorem norm_yInner_le {P : ℕ} [NeZero P] (F G : ZMod P → ℂ) :
    ‖yInner F G‖ ≤ yNorm 2 F * yNorm 2 G := by
  have hP : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
  have h1 : ‖yInner F G‖ ≤ (P : ℝ)⁻¹ * ∑ y, ‖F y‖ * ‖G y‖ := by
    unfold yInner
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
    refine Finset.sum_le_sum fun y _ => ?_
    rw [norm_mul, Complex.norm_conj]
  have h2 : ((P : ℝ)⁻¹ * ∑ y, ‖F y‖ * ‖G y‖) ^ 2 ≤ (yNorm 2 F * yNorm 2 G) ^ 2 := by
    have e : (yNorm 2 F * yNorm 2 G) ^ 2 = ((P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ 2) * ((P : ℝ)⁻¹ * ∑ y, ‖G y‖ ^ 2) := by
      rw [mul_pow, yNorm_two_sq, yNorm_two_sq]
    rw [e]
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun y => ‖F y‖) (fun y => ‖G y‖)
    have hP2 : 0 ≤ ((P : ℝ)⁻¹) ^ 2 := by positivity
    calc ((P : ℝ)⁻¹ * ∑ y, ‖F y‖ * ‖G y‖) ^ 2 = ((P : ℝ)⁻¹) ^ 2 * (∑ y, ‖F y‖ * ‖G y‖) ^ 2 := by ring
      _ ≤ ((P : ℝ)⁻¹) ^ 2 * ((∑ y, ‖F y‖ ^ 2) * ∑ y, ‖G y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left this hP2
      _ = _ := by ring
  have h3 : 0 ≤ yNorm 2 F * yNorm 2 G := by unfold yNorm; positivity
  exact h1.trans (abs_le_of_sq_le_sq' h2 h3).2 |>.trans le_rfl

end PrimeBHT.TimeFrequency.X2
