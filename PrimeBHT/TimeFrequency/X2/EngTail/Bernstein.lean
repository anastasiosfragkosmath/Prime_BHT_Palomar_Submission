module

public import PrimeBHT.TimeFrequency.Tile.Gram.Bernstein
public import PrimeBHT.TimeFrequency.X2.EngTail.CZKernel
public import PrimeBHT.TimeFrequency.X2.Ortho.Fourier
public import PrimeBHT.TimeFrequency.X2.Ortho.Weights

/-!
# X2, node B5: weighted Bernstein bound for the cutoffs `ψ ∈ Ψ_I(𝔭)`

`inPsi_tileBound_φ`: for `ψ ∈ Ψ_I(𝔭)` (`I = dyadicInt s v`, `δ ≤ 1/2`) the function `ψ` is smooth and
`|ψ'(x)| ≤ C_B 2^{-s} (1 + |x - c_I|/2^s)^{-N}`.  This is the reproducing formula of X1's (G0)
(`Tile/Gram/Bernstein.lean`: `ψ = ψ * K_L`, `𝓕 K_0 = 1` on `[-1/2, 1/2]`), restated for a continuous integrable `f` with
`𝓕 f` supported in `[-1/(2L), 1/(2L)]` (the X1 statement is for `IsAdapted` data, which already contains the derivative bound).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- Reproducing formula for all derivatives (copy of `Tile.iteratedDeriv_demod_eq` for a general `f`). -/
theorem iteratedDeriv_eq_conv {f : ℝ → ℂ} (hfc : Continuous f) (hfi : Integrable f) {L : ℝ} (hL : 0 < L)
    (hψ0 : ∀ ξ, ξ ∉ Icc (-(2 * L)⁻¹) ((2 * L)⁻¹) → 𝓕 f ξ = 0) (n : ℕ) (x : ℝ) :
    iteratedDeriv n f x = ∫ y, f y * (((L ^ (-(1 : ℝ) - n) : ℝ) : ℂ) * kernelG0 n ((x - y) / L)) := by
  set ψ := 𝓕 f
  have hψc : Continuous ψ := continuous_fourier_of_integrable hfi
  have hψi : Integrable ψ := integrable_of_continuous_of_eq_zero hψc (Metric.isBounded_Icc _ _) hψ0
  set h : ℝ → ℂ := fun ξ => ψ (-ξ)
  have hinv : f = 𝓕 h := by
    have := Continuous.fourierInv_fourier_eq hfc hfi hψi
    rw [Real.fourierInv_eq_fourier_comp_neg] at this
    exact this.symm
  have hneg : ∀ ξ, ξ ∉ Icc (-(2 * L)⁻¹) ((2 * L)⁻¹) → -ξ ∉ Icc (-(2 * L)⁻¹) ((2 * L)⁻¹) := by
    intro ξ hξ hc
    apply hξ
    obtain ⟨h1, h2⟩ := hc
    constructor <;> linarith
  have hmom : ∀ m : ℕ, Integrable (fun ξ : ℝ => ξ ^ m • h ξ) := fun m =>
    integrable_of_continuous_of_eq_zero (Continuous.smul (continuous_pow m) (hψc.comp continuous_neg))
      (Metric.isBounded_Icc (-(2 * L)⁻¹) ((2 * L)⁻¹))
      (fun ξ hξ => by simp only [h, hψ0 _ (hneg ξ hξ), smul_zero])
  have hD : iteratedDeriv n f = 𝓕 (fun ξ : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * ξ) ^ n • h ξ) := by
    rw [hinv]
    exact Real.iteratedDeriv_fourier (N := (n : ℕ∞)) (fun m _ => hmom m) le_rfl
  set ρ : ℝ → ℂ := fun ξ => (-2 * (Real.pi : ℂ) * Complex.I * ξ) ^ n * ((bumpG0 (L * ξ) : ℝ) : ℂ)
  have hρi : Integrable ρ := by
    refine integrable_of_continuous_of_eq_zero (by
        have : Continuous fun ξ : ℝ => ((bumpG0 (L * ξ) : ℝ) : ℂ) :=
          Complex.continuous_ofReal.comp (bumpG0.continuous.comp (continuous_const.mul continuous_id))
        exact (by fun_prop : Continuous fun ξ : ℝ =>
          (-2 * (Real.pi : ℂ) * Complex.I * ξ) ^ n).mul this)
      (Metric.isBounded_Icc (-L⁻¹) L⁻¹) (fun ξ hξ => ?_)
    have h1 : 1 ≤ |L * ξ| := by
      by_contra hc
      push Not at hc
      apply hξ
      rw [abs_lt] at hc
      have e : L⁻¹ * L = 1 := inv_mul_cancel₀ hL.ne'
      constructor
      · rw [neg_le, ← mul_le_mul_iff_of_pos_left hL, mul_neg, ← div_eq_mul_inv, div_self hL.ne']
        linarith
      · rw [← mul_le_mul_iff_of_pos_left hL, ← div_eq_mul_inv, div_self hL.ne']
        linarith
    have : bumpG0 (L * ξ) = 0 := bumpG0.zero_of_le_dist (by
      rw [Real.dist_eq, sub_zero]
      exact h1)
    simp only [ρ, this, Complex.ofReal_zero, mul_zero]
  have hpt : ∀ ξ : ℝ, Complex.exp (↑(-2 * Real.pi * ξ * x) * Complex.I) •
      ((-2 * (Real.pi : ℂ) * Complex.I * ξ) ^ n • h ξ) =
      Complex.exp (↑(-2 * Real.pi * ξ * x) * Complex.I) * (ρ ξ * 𝓕 f (-ξ)) := by
    intro ξ
    simp only [smul_eq_mul, ρ, h]
    by_cases hξ : ξ ∈ Icc (-(2 * L)⁻¹) ((2 * L)⁻¹)
    · have hb : bumpG0 (L * ξ) = 1 := by
        apply bumpG0_eq_one
        rw [abs_mul, abs_of_pos hL]
        have h2 : |ξ| ≤ (2 * L)⁻¹ := abs_le.2 hξ
        calc L * |ξ| ≤ L * (2 * L)⁻¹ := mul_le_mul_of_nonneg_left h2 hL.le
          _ = 1 / 2 := by field_simp
      rw [hb, Complex.ofReal_one, mul_one]
    · have hz : 𝓕 f (-ξ) = 0 := hψ0 _ (hneg ξ hξ)
      rw [show ψ (-ξ) = 0 from hz, hz]
      simp
  rw [hD, Real.fourier_real_eq_integral_exp_smul]
  simp_rw [hpt]
  rw [integral_fourier_mul_fourier_neg hρi hfi x]
  congr 1
  funext y
  rw [fourier_scaled_kappa n hL]

/-- Smoothness from the Fourier support. -/
theorem contDiff_of_fourier_support {f : ℝ → ℂ} (hfc : Continuous f) (hfi : Integrable f) {L : ℝ} (_hL : 0 < L)
    (hψ0 : ∀ ξ, ξ ∉ Icc (-(2 * L)⁻¹) ((2 * L)⁻¹) → 𝓕 f ξ = 0) (m : ℕ) : ContDiff ℝ m f := by
  have hψc : Continuous (𝓕 f) := continuous_fourier_of_integrable hfi
  have hψi : Integrable (𝓕 f) :=
    integrable_of_continuous_of_eq_zero hψc (Metric.isBounded_Icc _ _) hψ0
  have hinv : f = 𝓕 (fun ξ => 𝓕 f (-ξ)) := by
    have := Continuous.fourierInv_fourier_eq hfc hfi hψi
    rw [Real.fourierInv_eq_fourier_comp_neg] at this
    exact this.symm
  rw [hinv]
  refine Real.contDiff_fourier (N := (m : ℕ∞)) (fun k _ => ?_)
  refine integrable_of_continuous_of_eq_zero (f := fun ξ : ℝ => ‖ξ‖ ^ k * ‖𝓕 f (-ξ)‖)
    ((continuous_norm.pow k).mul (hψc.comp continuous_neg).norm)
    (Metric.isBounded_Icc (-(2 * L)⁻¹) ((2 * L)⁻¹)) (fun ξ hξ => ?_)
  have : -ξ ∉ Icc (-(2 * L)⁻¹) ((2 * L)⁻¹) := by
    intro hc
    apply hξ
    obtain ⟨h1, h2⟩ := hc
    constructor <;> linarith
  simp [hψ0 _ this]


theorem InPsi.le_tw {𝔭 : Params} {s v : ℤ} {ψ : ℝ → ℂ} (hψ : InPsi 𝔭 s v ψ) (x : ℝ) :
    ‖ψ x‖ ≤ 𝔭.C * tw (𝔭.N : ℝ) s v x := by
  have h := hψ.2.1 x
  have hR : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  have e : jb ((x - dyCentre s v) / (2 : ℝ) ^ s) = 1 + |x - (2 : ℝ) ^ s * ((v : ℝ) + 1 / 2)| / (2 : ℝ) ^ s := by
    unfold jb dyCentre
    rw [abs_div, abs_of_pos hR]
  rw [e] at h
  exact h

theorem Params.Admissible.delta_le_eighth {𝔭 : Params} (h : 𝔭.Admissible) : 𝔭.δ ≤ 1 / 8 := by
  obtain ⟨hJ, -, -, -, hδ, -, -, -⟩ := h
  refine hδ.trans ?_
  have hJ' : (16 : ℝ) ≤ (𝔭.J : ℝ) := by exact_mod_cast hJ
  have h1 : (2 : ℝ) ^ (-(3 * (𝔭.J : ℝ) / 2)) ≤ (2 : ℝ) ^ (-(3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h2 : (2 : ℝ) ^ (-(3 : ℝ)) = 1 / 8 := by
    rw [Real.rpow_neg (by norm_num)]; norm_num
  linarith

theorem Params.Admissible.delta_le_half {𝔭 : Params} (h : 𝔭.Admissible) : 𝔭.δ ≤ 1 / 2 := by
  have := h.delta_le_eighth; linarith

/-- **Weighted Bernstein bound**: `|ψ'(x)| ≤ C_B 2^{-s} (1 + |x - c_I|/2^s)^{-N}` for `ψ ∈ Ψ_I(𝔭)`. -/
theorem inPsi_deriv_bound (𝔭 : Params) (hN : 2 ≤ 𝔭.N) (hδ : 𝔭.δ ≤ 1 / 2) (hC : 0 ≤ 𝔭.C) :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ (s v : ℤ) (ψ : ℝ → ℂ), InPsi 𝔭 s v ψ → Differentiable ℝ ψ ∧
      ∀ x, ‖deriv ψ x‖ ≤ CB * ((2 : ℝ) ^ s)⁻¹ * tw (𝔭.N : ℝ) s v x := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_kernelG0_le 1 (𝔭.N + 2)
  refine ⟨2 * 𝔭.C * C₁, by positivity, fun s v ψ hψ => ?_⟩
  have hL : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  set L : ℝ := (2 : ℝ) ^ s with hLdef
  have hfc : Continuous ψ := hψ.1
  have hfi : Integrable ψ := integrable_psi hN hψ
  have hψ0 : ∀ ξ, ξ ∉ Icc (-(2 * L)⁻¹) ((2 * L)⁻¹) → 𝓕 ψ ξ = 0 := by
    intro ξ hξ
    apply hψ.2.2
    have h1 : (2 * L)⁻¹ < |ξ| := by
      by_contra hc
      push Not at hc
      exact hξ (abs_le.1 hc)
    have h2 : 𝔭.δ * (2 : ℝ) ^ (-s) ≤ (2 * L)⁻¹ := by
      rw [zpow_neg, ← hLdef, mul_inv]
      have : (0 : ℝ) < L⁻¹ := inv_pos.2 hL
      nlinarith
    linarith
  refine ⟨(contDiff_of_fourier_support hfc hfi hL hψ0 1).differentiable (by norm_num), fun x => ?_⟩
  have hd : deriv ψ x = iteratedDeriv 1 ψ x := by rw [iteratedDeriv_one]
  rw [hd, iteratedDeriv_eq_conv hfc hfi hL hψ0 1 x]
  -- pointwise bound of the integrand
  set B : ℝ := 𝔭.C * C₁ * (L ^ (-(1 : ℝ) - 1)) * tw (𝔭.N : ℝ) s v x with hB
  have hLp : L ^ (-(1 : ℝ) - 1) = (L⁻¹) ^ 2 := by
    rw [show (-(1 : ℝ) - 1) = -2 by ring, Real.rpow_neg hL.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, inv_pow]
  have hpt : ∀ y, ‖ψ y * (((L ^ (-(1 : ℝ) - (1 : ℕ)) : ℝ) : ℂ) * kernelG0 1 ((x - y) / L))‖ ≤
      B * (1 + |x - y| / L) ^ (-(2 : ℝ)) := by
    intro y
    have hker := hC₁ ((x - y) / L)
    rw [abs_div, abs_of_pos hL] at hker
    have hψy := hψ.le_tw y
    have hpee : tw (𝔭.N : ℝ) s v y ≤ (1 + |y - x| / L) ^ (𝔭.N : ℝ) * tw (𝔭.N : ℝ) s v x := by
      have := wt_peetre (q := (𝔭.N : ℝ)) (by positivity) ((2 : ℝ) ^ s * ((v : ℝ) + 1 / 2)) hL y x
      exact this
    have hd0 : 0 < 1 + |x - y| / L := by positivity
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    -- combine
    have h1 : ‖ψ y‖ * ‖kernelG0 1 ((x - y) / L)‖ ≤
        (𝔭.C * ((1 + |x - y| / L) ^ (𝔭.N : ℝ) * tw (𝔭.N : ℝ) s v x)) *
          (C₁ * (1 + |x - y| / L) ^ (-((𝔭.N + 2 : ℕ) : ℝ))) := by
      have hp0 : 0 ≤ ‖kernelG0 1 ((x - y) / L)‖ := norm_nonneg _
      refine mul_le_mul ?_ hker hp0 (by have := tw_nonneg (𝔭.N : ℝ) s v x; positivity)
      calc ‖ψ y‖ ≤ 𝔭.C * tw (𝔭.N : ℝ) s v y := hψy
        _ ≤ 𝔭.C * ((1 + |y - x| / L) ^ (𝔭.N : ℝ) * tw (𝔭.N : ℝ) s v x) := mul_le_mul_of_nonneg_left hpee hC
        _ = _ := by rw [abs_sub_comm y x]
    have e : (1 + |x - y| / L) ^ (𝔭.N : ℝ) * (1 + |x - y| / L) ^ (-((𝔭.N + 2 : ℕ) : ℝ)) =
        (1 + |x - y| / L) ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add hd0]; congr 1; push_cast; ring
    calc ‖ψ y‖ * ((L ^ (-(1 : ℝ) - (1 : ℕ))) * ‖kernelG0 1 ((x - y) / L)‖)
        = (L ^ (-(1 : ℝ) - (1 : ℕ))) * (‖ψ y‖ * ‖kernelG0 1 ((x - y) / L)‖) := by ring
      _ ≤ (L ^ (-(1 : ℝ) - (1 : ℕ))) * ((𝔭.C * ((1 + |x - y| / L) ^ (𝔭.N : ℝ) * tw (𝔭.N : ℝ) s v x)) *
          (C₁ * (1 + |x - y| / L) ^ (-((𝔭.N + 2 : ℕ) : ℝ)))) := by
          gcongr
      _ = B * ((1 + |x - y| / L) ^ (𝔭.N : ℝ) * (1 + |x - y| / L) ^ (-((𝔭.N + 2 : ℕ) : ℝ))) := by
          simp only [hB]; push_cast; ring
      _ = B * (1 + |x - y| / L) ^ (-(2 : ℝ)) := by rw [e]
  have hint : Integrable (fun y => B * (1 + |x - y| / L) ^ (-(2 : ℝ))) := by
    have := integrable_one_add_abs_sub_div_rpow (p := 2) (by norm_num) x hL
    have h2 : (fun y => B * (1 + |x - y| / L) ^ (-(2 : ℝ))) = fun y => B * (1 + |y - x| / L) ^ (-(2 : ℝ)) := by
      funext y; rw [abs_sub_comm]
    rw [h2]
    exact this.const_mul B
  have hI : ∫ y, B * (1 + |x - y| / L) ^ (-(2 : ℝ)) = B * (2 * L) := by
    have h2 : (fun y => B * (1 + |x - y| / L) ^ (-(2 : ℝ))) = fun y => B * (1 + |y - x| / L) ^ (-(2 : ℝ)) := by
      funext y; rw [abs_sub_comm]
    rw [h2, integral_const_mul, integral_one_add_abs_sub_div_rpow (by norm_num : (1 : ℝ) < 2) x hL]
    norm_num
  have hB0 : 0 ≤ B := by
    have := tw_nonneg (𝔭.N : ℝ) s v x
    have : 0 ≤ L ^ (-(1 : ℝ) - 1) := by positivity
    simp only [hB]; positivity
  calc ‖∫ y, ψ y * (((L ^ (-(1 : ℝ) - ((1 : ℕ) : ℝ)) : ℝ) : ℂ) * kernelG0 1 ((x - y) / L))‖
      ≤ ∫ y, ‖ψ y * (((L ^ (-(1 : ℝ) - ((1 : ℕ) : ℝ)) : ℝ) : ℂ) * kernelG0 1 ((x - y) / L))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y, B * (1 + |x - y| / L) ^ (-(2 : ℝ)) :=
        integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _) hint (Eventually.of_forall hpt)
    _ = B * (2 * L) := hI
    _ = 2 * 𝔭.C * C₁ * L⁻¹ * tw (𝔭.N : ℝ) s v x := by
        simp only [hB, hLp]
        have : L ≠ 0 := hL.ne'
        field_simp

end PrimeBHT.TimeFrequency.X2
