module

public import PrimeBHT.TimeFrequency.X2.Ortho.Fourier
public import PrimeBHT.TimeFrequency.X2.Ortho.TreeScalar
public import PrimeBHT.TimeFrequency.X2.Ortho.Weights
public import PrimeBHT.TimeFrequency.X2.Ortho.Kernel
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Fourier.Convolution
import PrimeBHT.TimeFrequency.X2.Ortho.Closing

/-!
# X2, node V10, Layer B: the dual vectors `z_R = T_m^†(|ψ|² T_m F)`

Scalar part: `K^†(t) = conj(𝓕⁻m(-t))`, `𝓕 K^† = conj m`, `z = K^† ⋆ (|ψ|² · 𝓕⁻m * f)`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform ComplexConjugate ContDiff Real Convolution
open PrimeBHT.TimeFrequency.Tile PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- The adjoint kernel `K^†(t) = conj K(-t)` of `K = 𝓕⁻ m`. -/
def Kdag (m : ℝ → ℂ) (t : ℝ) : ℂ := (starRingEnd ℂ) (𝓕⁻ m (-t))

section Kdag

variable {𝔭 : Params} {s : ℤ} {c : ℝ} {m : ℝ → ℂ}

theorem continuous_Kdag (hm : InMult 𝔭 s c m) : Continuous (Kdag m) := by
  have hKc : Continuous (𝓕⁻ m) :=
    continuous_fourierInv_of_integrable' (integrable_of_far hm.1.continuous hm.2.1)
  exact Complex.continuous_conj.comp (hKc.comp continuous_neg)

theorem integrable_Kdag (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hm : InMult 𝔭 s c m) : Integrable (Kdag m) := by
  have hK := integrable_fourierInv_inMult hD hβ hm
  refine (hK.comp_neg.norm).mono' (continuous_Kdag hm).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  simp [Kdag]

theorem integrable_fourier_inMult (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hm : InMult 𝔭 s c m) :
    Integrable (𝓕 m) := by
  have hK := integrable_fourierInv_inMult hD hβ hm
  refine hK.comp_neg.congr (Eventually.of_forall fun w => ?_)
  simp only [Real.fourierInv_eq_fourier_neg, neg_neg]

theorem fourier_Kdag (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hm : InMult 𝔭 s c m) (ζ : ℝ) :
    𝓕 (Kdag m) ζ = (starRingEnd ℂ) (m ζ) := by
  have hK : 𝓕 (𝓕⁻ m) = m :=
    Continuous.fourier_fourierInv_eq hm.1.continuous (integrable_of_far hm.1.continuous hm.2.1)
      (integrable_fourier_inMult hD hβ hm)
  rw [← congrFun hK ζ, Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_conj]
  rw [← integral_neg_eq_self (fun s : ℝ => (starRingEnd ℂ) (Complex.exp (↑(-2 * π * s * ζ) * Complex.I) •
    𝓕⁻ m s))]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  have e : Complex.exp (↑(-2 * π * t * ζ) * Complex.I) =
      (starRingEnd ℂ) (Complex.exp (↑(-2 * π * -t * ζ) * Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  simp only [smul_eq_mul, map_mul, Kdag]
  rw [← e]

end Kdag

/-- The weighted piece `uu = |ψ|² · (𝓕⁻m * f)`. -/
def uu (ψ m f : ℝ → ℂ) (w : ℝ) : ℂ := ((‖ψ w‖ ^ 2 : ℝ) : ℂ) * tm m f w

/-- The dual `z(x) = ∫ conj K(w - x) uu(w) dw`. -/
def dual (ψ m f : ℝ → ℂ) (x : ℝ) : ℂ := ∫ w, (starRingEnd ℂ) (𝓕⁻ m (w - x)) * uu ψ m f w

section Dual

variable {𝔭 : Params} {s v : ℤ} {c : ℝ} {ψ m f : ℝ → ℂ}

theorem norm_uu_le (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ) (hm : InMult 𝔭 s c m)
    {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) (w : ℝ) :
    ‖uu ψ m f w‖ ≤ ‖ψ w‖ * (𝔭.C * (B * ∫ y, ‖𝓕⁻ m y‖)) := by
  unfold uu
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
  have h1 := norm_tm_le hD hβ hm hB w
  have h2 := norm_psi_le hψ w
  have h3 : 0 ≤ ‖ψ w‖ := norm_nonneg _
  calc ‖ψ w‖ * ‖ψ w‖ * ‖tm m f w‖ ≤ ‖ψ w‖ * 𝔭.C * (B * ∫ y, ‖𝓕⁻ m y‖) := by
        have := mul_le_mul h2 h1 (norm_nonneg _) (nonneg_C_of_inPsi hψ)
        nlinarith [mul_nonneg h3 (norm_nonneg (tm m f w))]
    _ = _ := by ring

theorem continuous_uu (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ) (hm : InMult 𝔭 s c m)
    (hf : Measurable f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) : Continuous (uu ψ m f) := by
  unfold uu
  have := continuous_tm hD hβ hm hf hB
  have h2 : Continuous fun w => ((‖ψ w‖ ^ 2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((hψ.1.norm).pow 2)
  exact h2.mul this

theorem integrable_uu (hN : 2 ≤ 𝔭.N) (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ)
    (hm : InMult 𝔭 s c m) (hf : Measurable f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) :
    Integrable (uu ψ m f) :=
  ((integrable_psi hN hψ).norm.mul_const (𝔭.C * (B * ∫ y, ‖𝓕⁻ m y‖))).mono'
    (continuous_uu hD hβ hψ hm hf hB).aestronglyMeasurable
    (Eventually.of_forall fun w => norm_uu_le hD hβ hψ hm hB w)

theorem dual_eq_conv (ψ m f : ℝ → ℂ) :
    dual ψ m f = Kdag m ⋆[ContinuousLinearMap.mul ℂ ℂ] uu ψ m f := by
  funext x
  unfold dual convolution
  simp only [ContinuousLinearMap.mul_apply']
  have := integral_sub_left_eq_self (fun t : ℝ => Kdag m t * uu ψ m f (x - t)) volume x
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [Kdag, sub_sub_cancel, neg_sub]

theorem integrable_dual (hN : 2 ≤ 𝔭.N) (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ)
    (hm : InMult 𝔭 s c m) (hf : Measurable f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) :
    Integrable (dual ψ m f) := by
  rw [dual_eq_conv]
  exact Integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) (integrable_Kdag hD hβ hm)
    (integrable_uu hN hD hβ hψ hm hf hB)

theorem continuous_dual (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ) (hm : InMult 𝔭 s c m)
    (hf : Measurable f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) : Continuous (dual ψ m f) := by
  rw [dual_eq_conv]
  refine BddAbove.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℂ ℂ) ?_ ?_
    (continuous_uu hD hβ hψ hm hf hB)
  · refine ⟨𝔭.C * (𝔭.C * (B * ∫ y, ‖𝓕⁻ m y‖)), ?_⟩
    rintro _ ⟨w, rfl⟩
    refine (norm_uu_le hD hβ hψ hm hB w).trans ?_
    have hX : 0 ≤ 𝔭.C * (B * ∫ y, ‖𝓕⁻ m y‖) := by
      have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
      have := nonneg_C_of_inPsi hψ
      positivity
    exact mul_le_mul_of_nonneg_right (norm_psi_le hψ w) hX
  · exact (integrable_Kdag hD hβ hm)

theorem fourier_dual_eq_zero (hN : 2 ≤ 𝔭.N) (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ)
    (hm : InMult 𝔭 s c m) (hf : Measurable f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) (ζ : ℝ)
    (hζ : 𝔭.β * (2 : ℝ) ^ (-s) / 2 < |ζ - c|) : 𝓕 (dual ψ m f) ζ = 0 := by
  rw [dual_eq_conv, Real.fourier_mul_convolution_eq (integrable_Kdag hD hβ hm)
    (integrable_uu hN hD hβ hψ hm hf hB), fourier_Kdag hD hβ hm, hm.2.1 ζ hζ]
  simp

/-- **(Z3)** duals with disjoint `3ω` are orthogonal (needs only `β ≤ 3`). -/
theorem dual_orthogonal {s' v' : ℤ} {c' : ℝ} {ψ' m' f' : ℝ → ℂ} (hN : 2 ≤ 𝔭.N) (hD : 2 ≤ 𝔭.D)
    (hβ : 0 ≤ 𝔭.β) (hβ3 : 𝔭.β ≤ 3) (hψ : InPsi 𝔭 s v ψ) (hψ' : InPsi 𝔭 s' v' ψ')
    (hm : InMult 𝔭 s c m) (hm' : InMult 𝔭 s' c' m') (hf : Measurable f) (hf' : Measurable f')
    {B B' : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) (hB' : ∀ z, ‖f' z‖ ≤ B')
    (hdisj : Disjoint (Set.Ico (c - 3 * (2 : ℝ) ^ (-s) / 2) (c + 3 * (2 : ℝ) ^ (-s) / 2))
      (Set.Ico (c' - 3 * (2 : ℝ) ^ (-s') / 2) (c' + 3 * (2 : ℝ) ^ (-s') / 2))) :
    ∫ x, dual ψ m f x * (starRingEnd ℂ) (dual ψ' m' f' x) = 0 := by
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-s) := zpow_pos (by norm_num) _
  have hl' : (0 : ℝ) < (2 : ℝ) ^ (-s') := zpow_pos (by norm_num) _
  refine pairing_eq_zero_of_fourier_Icc (u := dual ψ m f) (v := dual ψ' m' f')
    (integrable_dual hN hD hβ hψ hm hf hB) (continuous_dual hD hβ hψ' hm' hf' hB')
    (integrable_dual hN hD hβ hψ' hm' hf' hB')
    (a := c - 3 * (2 : ℝ) ^ (-s) / 2) (b := c + 3 * (2 : ℝ) ^ (-s) / 2)
    (a' := c' - 3 * (2 : ℝ) ^ (-s') / 2) (b' := c' + 3 * (2 : ℝ) ^ (-s') / 2)
    (fun ξ hξ => ?_) (fun ξ hξ => ?_) hdisj
  · refine fourier_dual_eq_zero hN hD hβ hψ hm hf hB ξ ?_
    have : 3 * (2 : ℝ) ^ (-s) / 2 < |ξ - c| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hξ
      rw [lt_abs]
      rcases hξ with h | h
      · right; linarith
      · left; linarith
    nlinarith
  · refine fourier_dual_eq_zero hN hD hβ hψ' hm' hf' hB' ξ ?_
    have : 3 * (2 : ℝ) ^ (-s') / 2 < |ξ - c'| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hξ
      rw [lt_abs]
      rcases hξ with h | h
      · right; linarith
      · left; linarith
    nlinarith

/-- **(Z1)**: `⟨dual, f⟩ = ∫ |ψ|² |𝓕⁻m * f|²`. -/
theorem dual_inner_f (hN : 2 ≤ 𝔭.N) (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ)
    (hm : InMult 𝔭 s c m) (hf : Measurable f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) :
    ∫ x, dual ψ m f x * (starRingEnd ℂ) (f x) = ∫ w, (((‖ψ w‖ ^ 2 * ‖tm m f w‖ ^ 2 : ℝ)) : ℂ) := by
  have hK := integrable_fourierInv_inMult hD hβ hm
  have hKc : Continuous (𝓕⁻ m) :=
    continuous_fourierInv_of_integrable' (integrable_of_far hm.1.continuous hm.2.1)
  have hu := integrable_uu hN hD hβ hψ hm hf hB
  have hucont := continuous_uu hD hβ hψ hm hf hB
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  unfold dual
  simp_rw [← integral_mul_const]
  have hb' : Integrable (fun p : ℝ × ℝ => ‖uu ψ m f p.2‖ * ‖𝓕⁻ m (-(p.1 - p.2))‖) (volume.prod volume) := by
    have := Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) (μ := volume) (ν := volume)
      hu.norm (hK.comp_neg.norm)
    simpa using this
  have hint : Integrable (Function.uncurry fun (x w : ℝ) =>
      (starRingEnd ℂ) (𝓕⁻ m (w - x)) * uu ψ m f w * (starRingEnd ℂ) (f x)) (volume.prod volume) := by
    refine (hb'.const_mul B).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have h1 : Measurable fun p : ℝ × ℝ => (starRingEnd ℂ) (𝓕⁻ m (p.2 - p.1)) := 
        Complex.continuous_conj.measurable.comp (hKc.measurable.comp (measurable_snd.sub measurable_fst))
      have h2 : Measurable fun p : ℝ × ℝ => uu ψ m f p.2 := hucont.measurable.comp measurable_snd
      have h3 : Measurable fun p : ℝ × ℝ => (starRingEnd ℂ) (f p.1) :=
        Complex.continuous_conj.measurable.comp (hf.comp measurable_fst)
      exact ((h1.mul h2).mul h3).aestronglyMeasurable
    · simp only [Function.uncurry, norm_mul, Complex.norm_conj]
      have : ‖𝓕⁻ m (-(p.1 - p.2))‖ = ‖𝓕⁻ m (p.2 - p.1)‖ := by rw [neg_sub]
      rw [this]
      calc ‖𝓕⁻ m (p.2 - p.1)‖ * ‖uu ψ m f p.2‖ * ‖f p.1‖ ≤ ‖𝓕⁻ m (p.2 - p.1)‖ * ‖uu ψ m f p.2‖ * B :=
            mul_le_mul_of_nonneg_left (hB _) (by positivity)
        _ = B * (‖uu ψ m f p.2‖ * ‖𝓕⁻ m (p.2 - p.1)‖) := by ring
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  have e : ∫ x, (starRingEnd ℂ) (𝓕⁻ m (w - x)) * uu ψ m f w * (starRingEnd ℂ) (f x) =
      uu ψ m f w * (starRingEnd ℂ) (tm m f w) := by
    unfold tm
    rw [← integral_conj, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [map_mul]; ring
  rw [e]
  unfold uu
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring

theorem peetre_aux {a b d : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : d ≤ a * b) (hd1 : 0 < d) :
    ((a ^ 12)⁻¹ * (b ^ 12)⁻¹) ^ 2 ≤ (d ^ 12)⁻¹ * (a ^ 12)⁻¹ := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have h1 : d ^ 12 ≤ (a * b) ^ 12 := pow_le_pow_left₀ hd1.le hd 12
  have hb12 : 1 ≤ b ^ 12 := one_le_pow₀ hb
  have e : ((a ^ 12)⁻¹ * (b ^ 12)⁻¹) ^ 2 = (a ^ 12)⁻¹ * (a ^ 12)⁻¹ * ((b ^ 12)⁻¹ * (b ^ 12)⁻¹) := by ring
  rw [e]
  have h2 : (b ^ 12)⁻¹ * (b ^ 12)⁻¹ ≤ (b ^ 12)⁻¹ := by
    have : (b ^ 12)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb12
    nlinarith [inv_pos.2 (pow_pos hb0 12)]
  have h3 : ((a * b) ^ 12)⁻¹ ≤ (d ^ 12)⁻¹ := inv_anti₀ (pow_pos hd1 12) h1
  have h4 : ((a * b) ^ 12)⁻¹ = (a ^ 12)⁻¹ * (b ^ 12)⁻¹ := by rw [mul_pow, mul_inv]
  calc (a ^ 12)⁻¹ * (a ^ 12)⁻¹ * ((b ^ 12)⁻¹ * (b ^ 12)⁻¹) ≤ (a ^ 12)⁻¹ * (a ^ 12)⁻¹ * (b ^ 12)⁻¹ :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ((a * b) ^ 12)⁻¹ * (a ^ 12)⁻¹ := by rw [h4]; ring
    _ ≤ (d ^ 12)⁻¹ * (a ^ 12)⁻¹ := mul_le_mul_of_nonneg_right h3 (by positivity)

/-- Pointwise bound of the integrand of `W_k`. -/
theorem kpsi_sq_le (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ)
    (hm : InMult 𝔭 s c m) (x w : ℝ) :
    ‖𝓕⁻ m (w - x)‖ ^ 2 * ‖ψ w‖ ^ 2 ≤
      (2 ^ 13 * 𝔭.β * 𝔭.C * 𝔭.C) ^ 2 * ((2 : ℝ) ^ s)⁻¹ ^ 2 *
        (((1 + |x - dyCentre s v| / (2 : ℝ) ^ s) ^ 12)⁻¹ * ((1 + |w - x| / (2 : ℝ) ^ s) ^ 12)⁻¹) := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  set L : ℝ := (2 : ℝ) ^ s with hLdef
  have hl : (2 : ℝ) ^ (-s) = L⁻¹ := zpow_neg _ _
  have hC := nonneg_C_of_inPsi hψ
  have hK := norm_fourierInv_inMult_le_pow (𝔭 := 𝔭) (M := 12) hD hβ hm (w - x)
  rw [hl] at hK
  set a : ℝ := 1 + |w - x| / L with ha
  set b : ℝ := 1 + |w - dyCentre s v| / L with hb
  set d : ℝ := 1 + |x - dyCentre s v| / L with hd
  have ha1 : 1 ≤ a := by have := div_nonneg (abs_nonneg (w - x)) hL.le; linarith
  have hb1 : 1 ≤ b := by have := div_nonneg (abs_nonneg (w - dyCentre s v)) hL.le; linarith
  have hd1 : 0 < d := by have := div_nonneg (abs_nonneg (x - dyCentre s v)) hL.le; linarith
  have hdab : d ≤ a * b := by
    have : |x - dyCentre s v| ≤ |w - x| + |w - dyCentre s v| := by
      have := abs_sub_le x w (dyCentre s v)
      rw [abs_sub_comm x w] at this; exact this
    have hd' : |x - dyCentre s v| / L ≤ |w - x| / L + |w - dyCentre s v| / L := by
      rw [← add_div]; exact div_le_div_of_nonneg_right this hL.le
    nlinarith [div_nonneg (abs_nonneg (w - x)) hL.le, div_nonneg (abs_nonneg (w - dyCentre s v)) hL.le,
      mul_nonneg (div_nonneg (abs_nonneg (w - x)) hL.le) (div_nonneg (abs_nonneg (w - dyCentre s v)) hL.le)]
  -- the two factors
  have hK' : ‖𝓕⁻ m (w - x)‖ ≤ 2 ^ 13 * 𝔭.β * 𝔭.C * (L⁻¹ * (a ^ 12)⁻¹) := by
    have e : (1 + L⁻¹ * |w - x|) = a := by rw [ha, div_eq_inv_mul]
    have := hK
    rw [e] at this
    simpa using this
  have hψ' : ‖ψ w‖ ≤ 𝔭.C * (b ^ 12)⁻¹ := by
    refine (hψ.2.1 w).trans ?_
    have hjb : jb ((w - dyCentre s v) / L) = b := by unfold jb; rw [abs_div, abs_of_pos hL]
    rw [hjb]
    have : b ^ (-(𝔭.N : ℝ)) ≤ (b ^ 12)⁻¹ := by
      have h12 : (b ^ 12)⁻¹ = b ^ (-(12 : ℝ)) := by
        rw [Real.rpow_neg (by linarith), show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [h12]
      refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
      have : (12 : ℝ) ≤ 𝔭.N := by exact_mod_cast hN
      linarith
    exact mul_le_mul_of_nonneg_left this hC
  have hA0 : 0 ≤ 2 ^ 13 * 𝔭.β * 𝔭.C * (L⁻¹ * (a ^ 12)⁻¹) := by
    have := inv_nonneg.2 hL.le
    positivity
  have hprod : ‖𝓕⁻ m (w - x)‖ * ‖ψ w‖ ≤
      (2 ^ 13 * 𝔭.β * 𝔭.C * (L⁻¹ * (a ^ 12)⁻¹)) * (𝔭.C * (b ^ 12)⁻¹) :=
    mul_le_mul hK' hψ' (norm_nonneg _) hA0
  have hsq : (‖𝓕⁻ m (w - x)‖ * ‖ψ w‖) ^ 2 ≤
      ((2 ^ 13 * 𝔭.β * 𝔭.C * (L⁻¹ * (a ^ 12)⁻¹)) * (𝔭.C * (b ^ 12)⁻¹)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hprod 2
  have e1 : ‖𝓕⁻ m (w - x)‖ ^ 2 * ‖ψ w‖ ^ 2 = (‖𝓕⁻ m (w - x)‖ * ‖ψ w‖) ^ 2 := by ring
  rw [e1]
  refine hsq.trans ?_
  have hP := peetre_aux ha1 hb1 hdab hd1
  calc ((2 ^ 13 * 𝔭.β * 𝔭.C * (L⁻¹ * (a ^ 12)⁻¹)) * (𝔭.C * (b ^ 12)⁻¹)) ^ 2
      = (2 ^ 13 * 𝔭.β * 𝔭.C * 𝔭.C) ^ 2 * L⁻¹ ^ 2 * ((a ^ 12)⁻¹ * (b ^ 12)⁻¹) ^ 2 := by ring
    _ ≤ (2 ^ 13 * 𝔭.β * 𝔭.C * 𝔭.C) ^ 2 * L⁻¹ ^ 2 * ((d ^ 12)⁻¹ * (a ^ 12)⁻¹) :=
        mul_le_mul_of_nonneg_left hP (by positivity)

theorem wt_twelve_eq (c L x : ℝ) (hL : 0 < L) : wt 12 c L x = ((1 + |x - c| / L) ^ 12)⁻¹ := by
  unfold wt
  have h : 0 < 1 + |x - c| / L := by positivity
  rw [Real.rpow_neg h.le, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem integrable_kpsi (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ)
    (hm : InMult 𝔭 s c m) (x : ℝ) : Integrable (fun w => ‖𝓕⁻ m (w - x)‖ ^ 2 * ‖ψ w‖ ^ 2) := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  have hKc : Continuous (𝓕⁻ m) :=
    continuous_fourierInv_of_integrable' (integrable_of_far hm.1.continuous hm.2.1)
  have hb : Integrable (fun w => ((2 ^ 13 * 𝔭.β * 𝔭.C * 𝔭.C) ^ 2 * ((2 : ℝ) ^ s)⁻¹ ^ 2 *
      ((1 + |x - dyCentre s v| / (2 : ℝ) ^ s) ^ 12)⁻¹) * wt 12 x ((2 : ℝ) ^ s) w) :=
    (integrable_wt (q := 12) (by norm_num) x hL).const_mul _
  refine hb.mono' ?_ (Eventually.of_forall fun w => ?_)
  · exact (((hKc.comp (continuous_id.sub continuous_const)).norm.pow 2).mul (hψ.1.norm.pow 2)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), wt_twelve_eq _ _ _ hL]
    have := kpsi_sq_le hN hD hβ hψ hm x w
    calc _ ≤ _ := this
      _ = _ := by ring

theorem integral_kpsi_le (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ)
    (hm : InMult 𝔭 s c m) (x : ℝ) :
    ∫ w, ‖𝓕⁻ m (w - x)‖ ^ 2 * ‖ψ w‖ ^ 2 ≤
      (2 ^ 13 * 𝔭.β * 𝔭.C * 𝔭.C) ^ 2 * (2 / 11) * ((2 : ℝ) ^ s)⁻¹ *
        wt 12 (dyCentre s v) ((2 : ℝ) ^ s) x := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  have hb : Integrable (fun w => ((2 ^ 13 * 𝔭.β * 𝔭.C * 𝔭.C) ^ 2 * ((2 : ℝ) ^ s)⁻¹ ^ 2 *
      ((1 + |x - dyCentre s v| / (2 : ℝ) ^ s) ^ 12)⁻¹) * wt 12 x ((2 : ℝ) ^ s) w) :=
    (integrable_wt (q := 12) (by norm_num) x hL).const_mul _
  calc ∫ w, ‖𝓕⁻ m (w - x)‖ ^ 2 * ‖ψ w‖ ^ 2 ≤ ∫ w, ((2 ^ 13 * 𝔭.β * 𝔭.C * 𝔭.C) ^ 2 * ((2 : ℝ) ^ s)⁻¹ ^ 2 *
        ((1 + |x - dyCentre s v| / (2 : ℝ) ^ s) ^ 12)⁻¹) * wt 12 x ((2 : ℝ) ^ s) w := by
        refine integral_mono (integrable_kpsi hN hD hβ hψ hm x) hb fun w => ?_
        rw [wt_twelve_eq _ _ _ hL]
        have := kpsi_sq_le hN hD hβ hψ hm x w
        calc _ ≤ _ := this
          _ = _ := by ring
    _ = (2 ^ 13 * 𝔭.β * 𝔭.C * 𝔭.C) ^ 2 * (2 / 11) * ((2 : ℝ) ^ s)⁻¹ *
        wt 12 (dyCentre s v) ((2 : ℝ) ^ s) x := by
        rw [integral_const_mul, integral_wt (q := 12) (by norm_num) x hL, wt_twelve_eq _ _ _ hL]
        field_simp
        ring

theorem cs_integral {p q : ℝ → ℝ} (hp : ∀ w, 0 ≤ p w) (hq : ∀ w, 0 ≤ q w)
    (hpm : Measurable p) (hqm : Measurable q) (hp2 : Integrable (fun w => p w ^ 2))
    (hq2 : Integrable (fun w => q w ^ 2)) :
    (∫ w, p w * q w) ^ 2 ≤ (∫ w, p w ^ 2) * ∫ w, q w ^ 2 := by
  have hpq : Integrable (fun w => p w * q w) := by
    refine ((hp2.add hq2).const_mul 1).mono' (hpm.mul hqm).aestronglyMeasurable
      (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp w) (hq w))]
    simp only [Pi.add_apply, one_mul]
    nlinarith [sq_nonneg (p w - q w)]
  refine sq_le_of_forall (integral_nonneg fun w => mul_nonneg (hp w) (hq w))
    (integral_nonneg fun w => sq_nonneg _) (integral_nonneg fun w => sq_nonneg _) fun l hl => ?_
  have h2 : 2 * l * ∫ w, p w * q w ≤ ∫ w, (l ^ 2 * p w ^ 2 + q w ^ 2) := by
    rw [← integral_const_mul]
    exact integral_mono (hpq.const_mul _) ((hp2.const_mul _).add hq2) fun w => by
      simp only
      nlinarith [sq_nonneg (l * p w - q w)]
  rw [integral_add (hp2.const_mul _) hq2, integral_const_mul] at h2
  exact h2

theorem dual_norm_sq_le (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ)
    (hm : InMult 𝔭 s c m) (hf : Measurable f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) (x : ℝ) :
    ‖dual ψ m f x‖ ^ 2 ≤ (∫ w, ‖𝓕⁻ m (w - x)‖ ^ 2 * ‖ψ w‖ ^ 2) * ∫ w, ‖gfun ψ m f w‖ ^ 2 := by
  have hKc : Continuous (𝓕⁻ m) :=
    continuous_fourierInv_of_integrable' (integrable_of_far hm.1.continuous hm.2.1)
  have hψc := hψ.1
  have hG := continuous_gfun (by omega) hβ hψ hm hf hB
  set p : ℝ → ℝ := fun w => ‖𝓕⁻ m (w - x)‖ * ‖ψ w‖ with hp
  set q : ℝ → ℝ := fun w => ‖gfun ψ m f w‖ with hq
  have hpc : Continuous p := (hKc.comp (continuous_id.sub continuous_const)).norm.mul hψc.norm
  have hqc : Continuous q := hG.norm
  have hp2 : Integrable (fun w => p w ^ 2) := by
    refine (integrable_kpsi hN hD hβ hψ hm x).congr (Eventually.of_forall fun w => ?_)
    simp only [hp]; ring
  have hq2 : Integrable (fun w => q w ^ 2) :=
    integrable_sq_gfun (by omega) (by omega) hβ hψ hm hf hB
  have hcs := cs_integral (p := p) (q := q) (fun w => by positivity) (fun w => norm_nonneg _)
    hpc.measurable hqc.measurable hp2 hq2
  have hpq : Integrable (fun w => p w * q w) := by
    refine ((hp2.add hq2).const_mul 1).mono' (hpc.mul hqc).aestronglyMeasurable
      (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
    simp only [Pi.add_apply, one_mul]
    nlinarith [sq_nonneg (p w - q w)]
  have h1 : ‖dual ψ m f x‖ ≤ ∫ w, p w * q w := by
    unfold dual
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    have habs : |‖ψ w‖ ^ 2| = ‖ψ w‖ ^ 2 := abs_of_nonneg (sq_nonneg _)
    simp only [hp, hq, gfun, uu, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, habs]
    unfold tm; ring
  have h2 : ‖dual ψ m f x‖ ^ 2 ≤ (∫ w, p w * q w) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  refine h2.trans (hcs.trans (le_of_eq ?_))
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [hp]; ring

end Dual

end PrimeBHT.TimeFrequency.X2
