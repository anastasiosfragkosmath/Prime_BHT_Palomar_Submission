module

public import PrimeBHT.TimeFrequency.X2.Classes
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# X2, node V05-1: the tile profile `η` (`IsEtaCut`)

`exists_etaCut`: for a class `𝔭` with EVEN decay order `𝔭.N = M ≥ 2`, `0 < 𝔭.δ ≤ 1/4` and
`M * (3 * M / δ) ^ M ≤ 𝔭.C` there is `η` with `IsEtaCut 𝔭 η`.

Construction (route check `docs/audits/X2-V06-V05-check.md` §2.5, V05-1): with `a = δ / m`, `M = 2m`,
`η(x) = c B_m(c x) / Y_m`, `c = π a`, `B_m(y) = sinc(y)^{2m} + sinc(y - π/2)^{2m}`, `Y_m = ∫ B_m`.
Positivity and the two-sided polynomial decay `⟨x⟩^{-M}` come from `sin² + cos² = 1`;
the Fourier support `[-δ, δ]` from `sinc(a·)^{2m} = 𝓕 (box_a^{⋆ 2m})` (`Real.fourier_mul_convolution_eq`) and Fourier
inversion.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform Convolution ContDiff Real

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2


def etaBox (a : ℝ) : ℝ → ℂ := Set.indicator (Set.Icc (-a / 2) (a / 2)) (fun _ => (1 : ℂ))

theorem integrable_etaBox (a : ℝ) : Integrable (etaBox a) := by
  unfold etaBox
  exact (integrableOn_const (μ := volume) (s := Set.Icc (-a/2) (a/2)) (C := (1:ℂ))
    (by simp) (by simp)).integrable_indicator measurableSet_Icc

theorem fourier_etaBox {a : ℝ} (ha : 0 < a) (x : ℝ) :
    𝓕 (etaBox a) x = ((a * Real.sinc (π * a * x) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have h1 : (fun v : ℝ => Complex.exp (↑(-2 * π * v * x) * Complex.I) • etaBox a v) =
      Set.indicator (Set.Icc (-a / 2) (a / 2)) (fun v : ℝ => Complex.exp (↑(-2 * π * v * x) * Complex.I)) := by
    funext v
    by_cases hv : v ∈ Set.Icc (-a / 2) (a / 2) <;> simp [etaBox, hv]
  rw [h1, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  by_cases hx : x = 0
  · subst hx
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
      mul_one, Real.sinc_zero]
    simp [Complex.real_smul]
    ring
  · have hc : (-2 * π * x : ℂ) * Complex.I ≠ 0 := by
      simp [hx, Real.pi_ne_zero, Complex.I_ne_zero]
    have e : ∀ v : ℝ, Complex.exp (↑(-2 * π * v * x) * Complex.I) =
        Complex.exp (((-2 * π * x : ℂ) * Complex.I) * (v : ℂ)) := by
      intro v; congr 1; push_cast; ring
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have hpax : π * a * x ≠ 0 := by positivity
    rw [Real.sinc_of_ne_zero hpax]
    have h2 : Complex.exp (((-2 * π * x : ℂ) * Complex.I) * ((a / 2 : ℝ) : ℂ)) =
        Complex.exp (-(↑(π * a * x) * Complex.I)) := by
      congr 1; push_cast; ring
    have h3 : Complex.exp (((-2 * π * x : ℂ) * Complex.I) * ((-a / 2 : ℝ) : ℂ)) =
        Complex.exp ((↑(π * a * x) * Complex.I)) := by
      congr 1; push_cast; ring
    rw [h2, h3]
    have h4 : Complex.exp (-(↑(π * a * x) * Complex.I)) - Complex.exp (↑(π * a * x) * Complex.I) =
        -2 * ((Real.sin (π * a * x) : ℝ) : ℂ) * Complex.I := by
      rw [show -(↑(π * a * x) * Complex.I) = ↑(-(π * a * x)) * Complex.I by push_cast; ring,
        Complex.exp_mul_I, Complex.exp_mul_I]
      simp only [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_sin,
        ← Complex.ofReal_cos]
      ring
    rw [h4]
    have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hπC : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp

/-- The `(n+1)`-fold convolution power of `etaBox a`. -/
def etaBpow (a : ℝ) : ℕ → ℝ → ℂ
  | 0 => etaBox a
  | n + 1 => etaBox a ⋆[ContinuousLinearMap.mul ℂ ℂ] etaBpow a n

theorem integrable_etaBpow (a : ℝ) (n : ℕ) : Integrable (etaBpow a n) := by
  induction n with
  | zero => exact integrable_etaBox a
  | succ n ih => exact (integrable_etaBox a).integrable_convolution _ ih

theorem support_etaBpow_subset (a : ℝ) (n : ℕ) :
    Function.support (etaBpow a n) ⊆ Set.Icc (-((n + 1) * a / 2)) ((n + 1) * a / 2) := by
  induction n with
  | zero =>
    intro x hx
    have : x ∈ Set.Icc (-a / 2) (a / 2) := by
      by_contra h
      exact hx (by simp [etaBpow, etaBox, h])
    rw [Set.mem_Icc] at this ⊢
    push_cast
    constructor <;> linarith [this.1, this.2]
  | succ n ih =>
    intro x hx
    have h := support_convolution_subset (ContinuousLinearMap.mul ℂ ℂ) (μ := volume) hx
    obtain ⟨y, hy, z, hz, rfl⟩ := h
    have hy' : y ∈ Set.Icc (-a / 2) (a / 2) := by
      by_contra h
      exact hy (by simp [etaBox, h])
    have hz' := ih hz
    simp only [Set.mem_Icc] at hy' hz' ⊢
    push_cast
    constructor <;> linarith [hy'.1, hy'.2, hz'.1, hz'.2]

theorem fourier_etaBpow {a : ℝ} (ha : 0 < a) (n : ℕ) (x : ℝ) :
    𝓕 (etaBpow a n) x = ((a * Real.sinc (π * a * x) : ℝ) : ℂ) ^ (n + 1) := by
  induction n generalizing x with
  | zero => simpa [etaBpow] using fourier_etaBox ha x
  | succ n ih =>
    simp only [etaBpow]
    rw [Real.fourier_mul_convolution_eq (integrable_etaBox a) (integrable_etaBpow a n), ih,
      fourier_etaBox ha, pow_succ' _ (n + 1)]

/-- Fourier support of the `M`-th power of the (scaled) sinc: it vanishes for `|ξ| > M a / 2`, provided
it is integrable. -/
theorem fourier_sincPow_eq_zero {a : ℝ} (ha : 0 < a) {n : ℕ}
    (hint : Integrable (fun x : ℝ => ((((a * Real.sinc (π * a * x)) ^ (n + 1) : ℝ)) : ℂ))) {ξ : ℝ}
    (hξ : ((n + 1 : ℕ) : ℝ) * a / 2 < |ξ|) :
    𝓕 (fun x : ℝ => ((((a * Real.sinc (π * a * x)) ^ (n + 1) : ℝ)) : ℂ)) ξ = 0 := by
  have hF : (fun x : ℝ => ((((a * Real.sinc (π * a * x)) ^ (n + 1) : ℝ)) : ℂ)) = 𝓕 (etaBpow a n) := by
    funext x
    rw [fourier_etaBpow ha]
    push_cast
    rfl
  rw [hF] at hint ⊢
  have hw : Integrable (etaBpow a n) := integrable_etaBpow a n
  have h1 : 𝓕 (𝓕 (etaBpow a n)) ξ = 𝓕⁻ (𝓕 (etaBpow a n)) (-ξ) := by
    rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  have hcont : ContinuousAt (etaBpow a n) (-ξ) := by
    have hopen : IsOpen (Set.Icc (-(((n : ℝ) + 1) * a / 2)) (((n : ℝ) + 1) * a / 2))ᶜ := isClosed_Icc.isOpen_compl
    have hmem : -ξ ∈ (Set.Icc (-(((n : ℝ) + 1) * a / 2)) (((n : ℝ) + 1) * a / 2))ᶜ := by
      intro h
      rw [Set.mem_Icc] at h
      push_cast at hξ
      rcases le_or_gt 0 ξ with h0 | h0
      · rw [abs_of_nonneg h0] at hξ; linarith [h.1]
      · rw [abs_of_neg h0] at hξ; linarith [h.2]
    have : etaBpow a n =ᶠ[nhds (-ξ)] fun _ => (0 : ℂ) := by
      filter_upwards [hopen.mem_nhds hmem] with y hy
      by_contra hne
      exact hy (support_etaBpow_subset a n hne)
    exact (continuousAt_const).congr this.symm
  rw [h1, hw.fourierInv_fourier_eq hint hcont]
  by_contra hne
  have := support_etaBpow_subset a n hne
  rw [Set.mem_Icc] at this
  push_cast at hξ
  rcases le_or_gt 0 ξ with h0 | h0
  · rw [abs_of_nonneg h0] at hξ; linarith [this.1]
  · rw [abs_of_neg h0] at hξ; linarith [this.2]

/-! ### Two-sided bounds for the profile -/

theorem abs_sinc_mul_le (y : ℝ) : |Real.sinc y| * (1 + |y|) ≤ 2 := by
  by_cases h : |y| ≤ 1
  · have h1 := Real.abs_sinc_le_one y
    have := mul_le_mul h1 (add_le_add_right h 1) (by positivity) zero_le_one
    linarith
  · rw [not_le] at h
    have hy : y ≠ 0 := by intro h0; simp [h0] at h; linarith
    rw [Real.sinc_of_ne_zero hy, abs_div]
    have hs := Real.abs_sin_le_one y
    have hpos : 0 < |y| := abs_pos.2 hy
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    have := mul_le_mul_of_nonneg_right hs hpos.le
    linarith

theorem abs_sinc_shift_mul_le (y : ℝ) : |Real.sinc (y - π / 2)| * (1 + |y|) ≤ 6 := by
  have h1 := abs_sinc_mul_le (y - π / 2)
  have h2 : 1 + |y| ≤ (1 + π / 2) * (1 + |y - π / 2|) := by
    have : |y| ≤ |y - π / 2| + π / 2 := by
      have := abs_sub_abs_le_abs_sub y (π / 2)
      have h3 : |π / 2| = π / 2 := abs_of_pos (by positivity)
      linarith
    linarith [mul_nonneg Real.pi_pos.le (abs_nonneg (y - π / 2))]
  have h4 := Real.pi_le_four
  have h5 : 0 ≤ |Real.sinc (y - π / 2)| := abs_nonneg _
  calc |Real.sinc (y - π / 2)| * (1 + |y|) ≤ |Real.sinc (y - π / 2)| * ((1 + π / 2) * (1 + |y - π / 2|)) :=
        mul_le_mul_of_nonneg_left h2 h5
    _ = (1 + π / 2) * (|Real.sinc (y - π / 2)| * (1 + |y - π / 2|)) := by ring
    _ ≤ 3 * 2 := by
        apply mul_le_mul (by linarith) h1 (by positivity) (by norm_num)
    _ = 6 := by norm_num

theorem sin_sq_le_sinc_sq_mul {z R : ℝ} (hz : |z| ≤ R) : Real.sin z ^ 2 ≤ Real.sinc z ^ 2 * R ^ 2 := by
  by_cases h0 : z = 0
  · subst h0; simp [sq_nonneg]
  · rw [Real.sinc_of_ne_zero h0, div_pow]
    have hz2 : z ^ 2 ≤ R ^ 2 := by
      rw [← sq_abs z]; exact pow_le_pow_left₀ (abs_nonneg z) hz 2
    have hpos : 0 < z ^ 2 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    exact mul_le_mul_of_nonneg_left hz2 (sq_nonneg _)

theorem sinc_sq_add_ge (y : ℝ) :
    1 ≤ (Real.sinc y ^ 2 + Real.sinc (y - π / 2) ^ 2) * (|y| + π / 2) ^ 2 := by
  have h1 := sin_sq_le_sinc_sq_mul (z := y) (R := |y| + π / 2) (by linarith [Real.pi_pos])
  have h2 := sin_sq_le_sinc_sq_mul (z := y - π / 2) (R := |y| + π / 2) (by
    have := abs_sub y (π / 2)
    have h3 : |π / 2| = π / 2 := abs_of_pos (by positivity)
    rw [h3] at this; exact this)
  have h3 : Real.sin (y - π / 2) = - Real.cos y := Real.sin_sub_pi_div_two y
  rw [h3] at h2
  linarith [Real.sin_sq_add_cos_sq y]

/-- The profile `B_m(y) = sinc(y)^{2m} + sinc(y - π/2)^{2m}`. -/
def etaB (m : ℕ) (y : ℝ) : ℝ := Real.sinc y ^ (2 * m) + Real.sinc (y - π / 2) ^ (2 * m)

theorem etaB_nonneg (m : ℕ) (y : ℝ) : 0 ≤ etaB m y := by
  unfold etaB
  have : Even (2 * m) := even_two_mul m
  exact add_nonneg (this.pow_nonneg _) (this.pow_nonneg _)

theorem continuous_etaB (m : ℕ) : Continuous (etaB m) := by
  unfold etaB
  have := Real.continuous_sinc
  fun_prop

theorem etaB_le {m : ℕ} (hm : 1 ≤ m) (y : ℝ) : etaB m y * (1 + |y|) ^ (2 * m) ≤ 40 ^ m := by
  unfold etaB
  have hp : (1 + |y|) ^ (2 * m) = ((1 + |y|) ^ 2) ^ m := by rw [← pow_mul]
  have e1 : Real.sinc y ^ (2 * m) * (1 + |y|) ^ (2 * m) ≤ 4 ^ m := by
    rw [hp, pow_mul, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have := abs_sinc_mul_le y
    have h0 : 0 ≤ |Real.sinc y| * (1 + |y|) := by positivity
    calc Real.sinc y ^ 2 * (1 + |y|) ^ 2 = (|Real.sinc y| * (1 + |y|)) ^ 2 := by
          rw [mul_pow, sq_abs]
      _ ≤ 2 ^ 2 := pow_le_pow_left₀ h0 this 2
      _ = 4 := by norm_num
  have e2 : Real.sinc (y - π / 2) ^ (2 * m) * (1 + |y|) ^ (2 * m) ≤ 36 ^ m := by
    rw [hp, pow_mul, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have := abs_sinc_shift_mul_le y
    have h0 : 0 ≤ |Real.sinc (y - π / 2)| * (1 + |y|) := by positivity
    calc Real.sinc (y - π / 2) ^ 2 * (1 + |y|) ^ 2 = (|Real.sinc (y - π / 2)| * (1 + |y|)) ^ 2 := by
          rw [mul_pow, sq_abs]
      _ ≤ 6 ^ 2 := pow_le_pow_left₀ h0 this 2
      _ = 36 := by norm_num
  have e3 : (4 : ℝ) ^ m + 36 ^ m ≤ 40 ^ m := by
    have := pow_add_pow_le (x := (4 : ℝ)) (y := 36) (n := m) (by norm_num) (by norm_num) (by omega)
    norm_num at this ⊢
    exact this
  rw [add_mul]
  linarith

theorem le_etaB {m : ℕ} (_hm : 1 ≤ m) (y : ℝ) : 1 ≤ 5 ^ m * (etaB m y * (1 + |y|) ^ (2 * m)) := by
  unfold etaB
  set p := Real.sinc y ^ 2 with hpdef
  set q := Real.sinc (y - π / 2) ^ 2 with hqdef
  have hp0 : 0 ≤ p := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hsum := sinc_sq_add_ge y
  have hR : (|y| + π / 2) ^ 2 ≤ (5 / 2) * (1 + |y|) ^ 2 := by
    have h4 := Real.pi_le_four
    have : |y| + π / 2 ≤ (π / 2) * (1 + |y|) := by
      linarith [mul_nonneg (sub_nonneg.2 Real.pi_gt_three.le) (abs_nonneg y), abs_nonneg y]
    have h5 : (|y| + π / 2) ^ 2 ≤ ((π / 2) * (1 + |y|)) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
    have h6 : (π / 2) ^ 2 ≤ 5 / 2 := by
      calc (π / 2) ^ 2 ≤ (63 / 40) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith [Real.pi_lt_d2]) 2
        _ ≤ 5 / 2 := by norm_num
    calc (|y| + π / 2) ^ 2 ≤ ((π / 2) * (1 + |y|)) ^ 2 := h5
      _ = (π / 2) ^ 2 * (1 + |y|) ^ 2 := by rw [mul_pow]
      _ ≤ (5 / 2) * (1 + |y|) ^ 2 := by gcongr
  have hmax : (p + q) / 2 ≤ max p q := by
    rcases le_total p q with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hpow : max p q ^ m ≤ p ^ m + q ^ m := by
    rcases le_total p q with h | h
    · rw [max_eq_right h]; have : 0 ≤ p ^ m := by positivity
      linarith
    · rw [max_eq_left h]; have : 0 ≤ q ^ m := by positivity
      linarith
  have h1 : 1 ≤ 5 * ((p + q) / 2) * (1 + |y|) ^ 2 := by
    have : 1 ≤ (p + q) * ((5 / 2) * (1 + |y|) ^ 2) :=
      hsum.trans (mul_le_mul_of_nonneg_left hR (by positivity))
    linarith
  have h2 : 1 ≤ (5 * (1 + |y|) ^ 2 * max p q) ^ m := by
    have h3 : 1 ≤ 5 * (1 + |y|) ^ 2 * max p q := by
      have : 5 * ((p + q) / 2) * (1 + |y|) ^ 2 ≤ 5 * (1 + |y|) ^ 2 * max p q := by
        have := mul_le_mul_of_nonneg_left hmax (by positivity : (0 : ℝ) ≤ 5 * (1 + |y|) ^ 2)
        linarith
      linarith
    exact one_le_pow₀ h3
  have h4 : (5 * (1 + |y|) ^ 2 * max p q) ^ m = 5 ^ m * ((1 + |y|) ^ (2 * m) * max p q ^ m) := by
    rw [mul_pow, mul_pow, ← pow_mul, mul_assoc]
  rw [h4] at h2
  have h5 : 5 ^ m * ((1 + |y|) ^ (2 * m) * max p q ^ m) ≤ 5 ^ m * ((p ^ m + q ^ m) * (1 + |y|) ^ (2 * m)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hpow (by positivity)
  have h6 : p ^ m = Real.sinc y ^ (2 * m) := by rw [hpdef, ← pow_mul]
  have h7 : q ^ m = Real.sinc (y - π / 2) ^ (2 * m) := by rw [hqdef, ← pow_mul]
  rw [h6, h7] at h5
  linarith


theorem integral_Ioi_one_add_inv_pow {M : ℕ} (hM : 2 ≤ M) :
    ∫ y in Ioi (0 : ℝ), ((1 + y) ^ M)⁻¹ = 1 / ((M : ℝ) - 1) := by
  have h1 : ∀ y : ℝ, ((1 + y) ^ M)⁻¹ = (fun t : ℝ => t ^ (-(M : ℝ))) (y + 1) := by
    intro y
    simp only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast, add_comm y 1]
  simp_rw [h1]
  have h2 : ∫ y in Ioi (0 : ℝ), (fun t : ℝ => t ^ (-(M : ℝ))) (y + 1) =
      ∫ y in Ioi (1 : ℝ), y ^ (-(M : ℝ)) := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    rw [← integral_add_right_eq_self (fun y => (Ioi (1 : ℝ)).indicator (fun t : ℝ => t ^ (-(M : ℝ))) y) 1]
    congr 1
    ext y
    by_cases hy : 0 < y
    · have : 1 < y + 1 := by linarith
      simp [Set.indicator, hy, this]
    · have : ¬ 1 < y + 1 := by linarith
      simp [Set.indicator, hy, this]
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hlt : -(M : ℝ) < -1 := by linarith
  rw [h2, integral_Ioi_rpow_of_lt hlt one_pos]
  have : (M : ℝ) - 1 ≠ 0 := by linarith
  have h3 : (-(M : ℝ) + 1) ≠ 0 := by linarith
  rw [Real.one_rpow]
  field_simp
  ring

theorem integrable_inv_one_add_abs_pow {M : ℕ} (hM : 2 ≤ M) :
    Integrable (fun y : ℝ => ((1 + |y|) ^ M)⁻¹) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := (M : ℝ))
    (by simp; exact_mod_cast (by omega : 1 < M))
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp [Real.rpow_neg_natCast, Real.norm_eq_abs]

theorem integral_inv_one_add_abs_pow {M : ℕ} (hM : 2 ≤ M) :
    ∫ y : ℝ, ((1 + |y|) ^ M)⁻¹ = 2 / ((M : ℝ) - 1) := by
  have := integral_comp_abs (f := fun y : ℝ => ((1 + y) ^ M)⁻¹)
  rw [this, integral_Ioi_one_add_inv_pow hM]
  ring


theorem etaFourier_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    𝓕 (fun x => f x + g x) ξ = 𝓕 f ξ + 𝓕 g ξ := by
  have := congrFun (VectorFourier.fourierIntegral_add (μ := volume) (L := innerₗ ℝ) Real.continuous_fourierChar
    (by fun_prop) hf hg) ξ
  exact this

theorem etaFourier_const_mul (c : ℂ) (f : ℝ → ℂ) (ξ : ℝ) : 𝓕 (fun x => c * f x) ξ = c * 𝓕 f ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  congr 1; ext x; simp only [smul_eq_mul]; ring

/-- Translation: `𝓕 (K(· - u)) α = e^{-2πiαu} 𝓕 K α`. -/
theorem etaFourier_comp_sub (K : ℝ → ℂ) (u α : ℝ) :
    𝓕 (fun y => K (y - u)) α = Complex.exp (↑(-2 * π * α * u) * Complex.I) * 𝓕 K α := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_const_mul]
  rw [← integral_add_right_eq_self (fun y => Complex.exp (↑(-2 * π * y * α) * Complex.I) • K (y - u)) u]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [smul_eq_mul, add_sub_cancel_right]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 3
  push_cast
  ring

/-! ### The normalizing integral -/

theorem etaB_le' {m : ℕ} (hm : 1 ≤ m) (y : ℝ) : etaB m y ≤ 40 ^ m * ((1 + |y|) ^ (2 * m))⁻¹ := by
  have h := etaB_le hm y
  have hp : 0 < (1 + |y|) ^ (2 * m) := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  exact h

theorem le_etaB' {m : ℕ} (hm : 1 ≤ m) (y : ℝ) : ((5 : ℝ) ^ m)⁻¹ * ((1 + |y|) ^ (2 * m))⁻¹ ≤ etaB m y := by
  have h := le_etaB hm y
  have hp : 0 < (1 + |y|) ^ (2 * m) := by positivity
  have h5 : (0 : ℝ) < 5 ^ m := by positivity
  rw [← mul_inv, inv_le_iff_one_le_mul₀ (by positivity)]
  calc (1 : ℝ) ≤ 5 ^ m * (etaB m y * (1 + |y|) ^ (2 * m)) := h
    _ = etaB m y * (5 ^ m * (1 + |y|) ^ (2 * m)) := by ring

theorem integrable_etaB {m : ℕ} (hm : 1 ≤ m) : Integrable (etaB m) := by
  have h := (integrable_inv_one_add_abs_pow (M := 2 * m) (by omega)).const_mul ((40 : ℝ) ^ m)
  refine h.mono' (continuous_etaB m).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (etaB_nonneg m y)]
  exact etaB_le' hm y

/-- The normalizing integral `Y_m = ∫ B_m`. -/
def etaY (m : ℕ) : ℝ := ∫ y, etaB m y

theorem etaY_le {m : ℕ} (hm : 1 ≤ m) : etaY m ≤ 40 ^ m * (2 / ((2 * m : ℕ) - 1 : ℝ)) := by
  unfold etaY
  have h1 := integral_mono (integrable_etaB hm)
    ((integrable_inv_one_add_abs_pow (M := 2 * m) (by omega)).const_mul ((40 : ℝ) ^ m))
    (fun y => etaB_le' hm y)
  rw [integral_const_mul, integral_inv_one_add_abs_pow (by omega)] at h1
  exact h1

theorem le_etaY {m : ℕ} (hm : 1 ≤ m) : ((5 : ℝ) ^ m)⁻¹ * (2 / ((2 * m : ℕ) - 1 : ℝ)) ≤ etaY m := by
  unfold etaY
  have h1 := integral_mono
    ((integrable_inv_one_add_abs_pow (M := 2 * m) (by omega)).const_mul (((5 : ℝ) ^ m)⁻¹))
    (integrable_etaB hm) (fun y => le_etaB' hm y)
  rw [integral_const_mul, integral_inv_one_add_abs_pow (by omega)] at h1
  exact h1

theorem etaY_pos {m : ℕ} (hm : 1 ≤ m) : 0 < etaY m := by
  refine lt_of_lt_of_le ?_ (le_etaY hm)
  have : (1 : ℝ) ≤ ((2 * m : ℕ) : ℝ) - 1 := by
    have : (2 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * m)
    linarith
  positivity

/-! ### The profile -/

/-- `η_c(x) = c B_m(c x) / Y_m` (`c = π a`). -/
def etaProf (m : ℕ) (c x : ℝ) : ℝ := c * etaB m (c * x) / etaY m

theorem continuous_etaProf (m : ℕ) (c : ℝ) : Continuous (etaProf m c) := by
  unfold etaProf
  have := continuous_etaB m
  fun_prop

theorem etaProf_nonneg {m : ℕ} (hm : 1 ≤ m) {c : ℝ} (hc : 0 ≤ c) (x : ℝ) : 0 ≤ etaProf m c x := by
  unfold etaProf
  have := etaY_pos hm
  have := etaB_nonneg m (c * x)
  positivity

theorem integral_etaProf {m : ℕ} (hm : 1 ≤ m) {c : ℝ} (hc : 0 < c) : ∫ x, etaProf m c x = 1 := by
  unfold etaProf
  have hY := (etaY_pos hm).ne'
  have h : ∫ x, etaB m (c * x) = c⁻¹ * etaY m := by
    rw [MeasureTheory.Measure.integral_comp_mul_left (fun y => etaB m y) c, abs_of_pos (inv_pos.2 hc)]
    rfl
  simp_rw [mul_div_assoc]
  rw [integral_const_mul]
  have h' : ∫ x, etaB m (c * x) / etaY m = (c⁻¹ * etaY m) / etaY m := by
    simp_rw [div_eq_mul_inv]
    rw [integral_mul_const, h]
  rw [h']
  field_simp

theorem etaProf_le {m : ℕ} (hm : 1 ≤ m) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (x : ℝ) :
    etaProf m c x ≤ (2 * m * 200 ^ m / c ^ (2 * m)) * ((1 + |x|) ^ (2 * m))⁻¹ := by
  unfold etaProf
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hY := le_etaY hm
  have hY0 := etaY_pos hm
  have hB := etaB_le' hm (c * x)
  have hcx : c * (1 + |x|) ≤ 1 + |c * x| := by
    rw [abs_mul, abs_of_pos hc0]; linarith
  have hpow : (c * (1 + |x|)) ^ (2 * m) ≤ (1 + |c * x|) ^ (2 * m) := pow_le_pow_left₀ (by positivity) hcx _
  have hJ : (0 : ℝ) < 2 / (((2 * m : ℕ) : ℝ) - 1) := by
    have : (2 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * m)
    have : (0 : ℝ) < ((2 * m : ℕ) : ℝ) - 1 := by linarith
    positivity
  set J := 2 / (((2 * m : ℕ) : ℝ) - 1) with hJdef
  have hJ1 : J ≤ 2 := by
    rw [hJdef, div_le_iff₀ (by
      have : (2 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * m)
      linarith)]
    have : (2 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * m)
    linarith
  have h1 : (1 + |c * x|) ^ (2 * m) ≥ c ^ (2 * m) * (1 + |x|) ^ (2 * m) := by
    rw [← mul_pow]; exact hpow
  have hcm : 0 < c ^ (2 * m) := by positivity
  have hxm : 0 < (1 + |x|) ^ (2 * m) := by positivity
  have h2 : ((1 + |c * x|) ^ (2 * m))⁻¹ ≤ (c ^ (2 * m) * (1 + |x|) ^ (2 * m))⁻¹ :=
    inv_anti₀ (by positivity) h1
  rw [div_le_iff₀ hY0]
  have h5 : (0 : ℝ) < 5 ^ m := by positivity
  have h6 : c * etaB m (c * x) ≤ c * (40 ^ m * ((c ^ (2 * m) * (1 + |x|) ^ (2 * m))⁻¹)) := by
    apply mul_le_mul_of_nonneg_left _ hc0.le
    exact hB.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have h7 : (2 * m * 200 ^ m / c ^ (2 * m)) * ((1 + |x|) ^ (2 * m))⁻¹ * etaY m ≥
      (2 * m * 200 ^ m / c ^ (2 * m)) * ((1 + |x|) ^ (2 * m))⁻¹ * (((5 : ℝ) ^ m)⁻¹ * J) :=
    mul_le_mul_of_nonneg_left hY (by positivity)
  refine h6.trans (le_trans ?_ h7)
  -- `c * 40^m * (c^{2m} (1+|x|)^{2m})⁻¹ ≤ 2m 200^m / c^{2m} * (1+|x|)^{-2m} * 5^{-m} J`
  have e1 : (2 * (m : ℝ) * 200 ^ m / c ^ (2 * m)) * ((1 + |x|) ^ (2 * m))⁻¹ * (((5 : ℝ) ^ m)⁻¹ * J) =
      (2 * m * 40 ^ m * J) * ((c ^ (2 * m))⁻¹ * ((1 + |x|) ^ (2 * m))⁻¹) := by
    have : (200 : ℝ) ^ m = 40 ^ m * 5 ^ m := by rw [← mul_pow]; norm_num
    rw [this]; field_simp
  rw [e1, mul_inv]
  have hJm : (2 : ℝ) / 2 ≤ J * m := by
    rw [hJdef]
    have : (2 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * m)
    have h8 : ((2 * m : ℕ) : ℝ) = 2 * m := by push_cast; ring
    rw [h8, div_mul_eq_mul_div, le_div_iff₀ (by rw [h8] at this; linarith)]
    linarith
  have hfin : c * 40 ^ m * ((c ^ (2 * m))⁻¹ * ((1 + |x|) ^ (2 * m))⁻¹) ≤
      2 * m * 40 ^ m * J * ((c ^ (2 * m))⁻¹ * ((1 + |x|) ^ (2 * m))⁻¹) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have h40 : (0 : ℝ) < 40 ^ m := by positivity
    have : c ≤ 2 * m * J := by linarith
    linarith [mul_le_mul_of_nonneg_right this h40.le]
  linarith [hfin]

theorem le_etaProf {m : ℕ} (hm : 1 ≤ m) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (x : ℝ) :
    (2 * m * 200 ^ m / c ^ (2 * m))⁻¹ * ((1 + |x|) ^ (2 * m))⁻¹ ≤ etaProf m c x := by
  unfold etaProf
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hY := etaY_le hm
  have hY0 := etaY_pos hm
  have hB := le_etaB' hm (c * x)
  have h2m : (2 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * m)
  have h8 : ((2 * m : ℕ) : ℝ) = 2 * m := by push_cast; ring
  have hJ0 : (0 : ℝ) < 2 / (((2 * m : ℕ) : ℝ) - 1) := by
    have : (0 : ℝ) < ((2 * m : ℕ) : ℝ) - 1 := by linarith
    positivity
  set J := 2 / (((2 * m : ℕ) : ℝ) - 1) with hJdef
  have hJ1 : J ≤ 2 := by
    rw [hJdef, div_le_iff₀ (by linarith)]
    linarith
  have hcx : 1 + |c * x| ≤ 1 + |x| := by
    rw [abs_mul, abs_of_pos hc0]
    have := mul_le_mul_of_nonneg_right hc1 (abs_nonneg x)
    linarith
  have hpow : ((1 + |x|) ^ (2 * m))⁻¹ ≤ ((1 + |c * x|) ^ (2 * m))⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hcx _)
  have hcm : 0 < c ^ (2 * m) := by positivity
  have hxm : 0 < (1 + |x|) ^ (2 * m) := by positivity
  have h40 : (0 : ℝ) < 40 ^ m := by positivity
  have h5 : (0 : ℝ) < 5 ^ m := by positivity
  rw [le_div_iff₀ hY0]
  have e1 : (2 * (m : ℝ) * 200 ^ m / c ^ (2 * m))⁻¹ * ((1 + |x|) ^ (2 * m))⁻¹ =
      (c ^ (2 * m) / (2 * m)) * ((200 : ℝ) ^ m)⁻¹ * ((1 + |x|) ^ (2 * m))⁻¹ := by
    field_simp
  rw [e1]
  have h6 : (((5 : ℝ) ^ m)⁻¹ * ((1 + |x|) ^ (2 * m))⁻¹) ≤ etaB m (c * x) :=
    le_trans (mul_le_mul_of_nonneg_left hpow (by positivity)) hB
  have h7 : c * (((5 : ℝ) ^ m)⁻¹ * ((1 + |x|) ^ (2 * m))⁻¹) ≤ c * etaB m (c * x) :=
    mul_le_mul_of_nonneg_left h6 hc0.le
  have h8' : (c ^ (2 * m) / (2 * m)) * ((200 : ℝ) ^ m)⁻¹ * ((1 + |x|) ^ (2 * m))⁻¹ * etaY m ≤
      (c ^ (2 * m) / (2 * m)) * ((200 : ℝ) ^ m)⁻¹ * ((1 + |x|) ^ (2 * m))⁻¹ * (40 ^ m * J) :=
    mul_le_mul_of_nonneg_left hY (by positivity)
  refine le_trans h8' (le_trans ?_ h7)
  have e2 : (c ^ (2 * m) / (2 * m)) * ((200 : ℝ) ^ m)⁻¹ * ((1 + |x|) ^ (2 * m))⁻¹ * (40 ^ m * J) =
      (c ^ (2 * m) * J / (2 * m)) * (((5 : ℝ) ^ m)⁻¹ * ((1 + |x|) ^ (2 * m))⁻¹) := by
    have : (200 : ℝ) ^ m = 40 ^ m * 5 ^ m := by rw [← mul_pow]; norm_num
    rw [this]; field_simp
  rw [e2]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hcc : c ^ (2 * m) ≤ c := by
    calc c ^ (2 * m) ≤ c ^ 1 := pow_le_pow_of_le_one hc0.le hc1 (by omega)
      _ = c := pow_one c
  rw [div_le_iff₀ (by positivity)]
  have := mul_le_mul hcc hJ1 hJ0.le hc0.le
  have := mul_le_mul_of_nonneg_left hm' hc0.le
  linarith

/-! ### Fourier support -/

theorem integrable_sincPow {m : ℕ} (hm : 1 ≤ m) {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => (a * Real.sinc (π * a * x)) ^ (2 * m)) := by
  have h := ((integrable_etaB hm).comp_mul_left' (R := π * a) (by positivity)).const_mul (a ^ (2 * m))
  refine h.mono' (by
    have := Real.continuous_sinc
    exact (by fun_prop : Continuous fun x : ℝ => (a * Real.sinc (π * a * x)) ^ (2 * m)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  have h0 : 0 ≤ (a * Real.sinc (π * a * x)) ^ (2 * m) := (even_two_mul m).pow_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg h0, mul_pow]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold etaB
  have : 0 ≤ Real.sinc (π * a * x - π / 2) ^ (2 * m) := (even_two_mul m).pow_nonneg _
  have e : π * a * x = π * a * x := rfl
  linarith [this]

theorem fourier_etaProf_eq_zero {m : ℕ} (hm : 1 ≤ m) {a : ℝ} (ha : 0 < a) {ξ : ℝ} (hξ : (m : ℝ) * a < |ξ|) :
    𝓕 (fun x => ((etaProf m (π * a) x : ℝ) : ℂ)) ξ = 0 := by
  set F : ℝ → ℂ := fun x => (((a * Real.sinc (π * a * x)) ^ (2 * m) : ℝ) : ℂ) with hF
  have hFi : Integrable F := (integrable_sincPow hm ha).ofReal
  set s : ℝ := 1 / (2 * a) with hs
  set κ : ℂ := (((π * a) / (etaY m * a ^ (2 * m)) : ℝ) : ℂ) with hκ
  have hrep : (fun x => ((etaProf m (π * a) x : ℝ) : ℂ)) = fun x => κ * (F x + F (x - s)) := by
    funext x
    have h1 : π * a * (x - s) = π * a * x - π / 2 := by
      rw [hs]; field_simp
    have hreal : etaProf m (π * a) x = (π * a) / (etaY m * a ^ (2 * m)) *
        ((a * Real.sinc (π * a * x)) ^ (2 * m) + (a * Real.sinc (π * a * (x - s))) ^ (2 * m)) := by
      unfold etaProf etaB
      rw [h1, mul_pow, mul_pow]
      have : a ^ (2 * m) ≠ 0 := by positivity
      have hY := (etaY_pos hm).ne'
      field_simp
    simp only [hF, hκ]
    rw [hreal]
    push_cast
    ring
  rw [hrep, etaFourier_const_mul, etaFourier_add hFi (hFi.comp_sub_right s), etaFourier_comp_sub]
  have hz : 𝓕 F ξ = 0 := by
    have := fourier_sincPow_eq_zero (a := a) ha (n := 2 * m - 1)
      (by
        have e : 2 * m - 1 + 1 = 2 * m := by omega
        rw [e]; exact hFi) (ξ := ξ) (by
        have e : 2 * m - 1 + 1 = 2 * m := by omega
        rw [e]; push_cast; linarith)
    have e : 2 * m - 1 + 1 = 2 * m := by omega
    rw [e] at this
    exact this
  rw [hz]; simp

/-! ### The theorem -/

theorem jb_rpow_neg_natCast (n : ℕ) (x : ℝ) : jb x ^ (-(n : ℝ)) = ((1 + |x|) ^ n)⁻¹ := by
  rw [Real.rpow_neg (jb_pos x).le, Real.rpow_natCast]
  rfl

/-- **V05-1 (`exists_eta`)**.  For a class `𝔭` with EVEN decay order `N ≥ 2`, `0 < δ ≤ 1/4` and
`N (3N/δ)^N ≤ C` there is a profile `η` with `IsEtaCut 𝔭 η`.  (The lower bound on `C` is forced up to the exponent:
`∫ η = 1`, `η ≤ C⟨x⟩^{-N}` force `C ≥ (N-1)/2`; `η(0) ≥ C⁻¹`, `η(0) ≤ ‖𝓕 η‖₁ ≤ 2δ` force `C ≥ 1/(2δ)`; the
support of `𝓕 η` in `[-δ, δ]` forces `C ≳ δ^{-(N-1)}`.) -/
theorem exists_etaCut (𝔭 : Params) (hN : Even 𝔭.N) (hN2 : 2 ≤ 𝔭.N) (hδ : 0 < 𝔭.δ) (hδ1 : 𝔭.δ ≤ 1 / 4)
    (hC : (𝔭.N : ℝ) * (3 * 𝔭.N / 𝔭.δ) ^ 𝔭.N ≤ 𝔭.C) : ∃ η : ℝ → ℝ, IsEtaCut 𝔭 η := by
  obtain ⟨m, hm⟩ := hN
  have hm1 : 1 ≤ m := by omega
  have hN' : 𝔭.N = 2 * m := by omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  set a : ℝ := 𝔭.δ / m with ha
  have ha0 : 0 < a := by positivity
  set c : ℝ := π * a with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by
    rw [hc, ha, ← mul_div_assoc, div_le_one (by positivity)]
    have := mul_le_mul_of_nonneg_right Real.pi_lt_d2.le hδ.le
    linarith
  have hmA : (m : ℝ) * a = 𝔭.δ := by rw [ha]; field_simp
  -- the constant
  have hĈ : (2 * m * 200 ^ m / c ^ (2 * m)) ≤ 𝔭.C := by
    have hcm : 0 < c ^ (2 * m) := by positivity
    rw [div_le_iff₀ hcm]
    have h1 : (𝔭.N : ℝ) * (3 * 𝔭.N / 𝔭.δ) ^ 𝔭.N ≤ 𝔭.C := hC
    rw [hN'] at h1
    push_cast at h1
    have h2 : (200 : ℝ) ^ m ≤ (3 * (2 * m) / 𝔭.δ * c) ^ (2 * m) := by
      have : 3 * (2 * (m : ℝ)) / 𝔭.δ * c = 6 * π := by
        rw [hc, ha]; field_simp; norm_num
      rw [this, pow_mul]
      apply pow_le_pow_left₀ (by norm_num)
      calc (200 : ℝ) ≤ (6 * 3) ^ 2 := by norm_num
        _ ≤ (6 * π) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_three]) 2
    calc 2 * (m : ℝ) * 200 ^ m ≤ 2 * m * (3 * (2 * m) / 𝔭.δ * c) ^ (2 * m) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (2 * m) * (3 * (2 * m) / 𝔭.δ) ^ (2 * m) * c ^ (2 * m) := by rw [mul_pow]; ring
      _ ≤ 𝔭.C * c ^ (2 * m) := mul_le_mul_of_nonneg_right h1 hcm.le
  have hĈ0 : 0 < 2 * (m : ℝ) * 200 ^ m / c ^ (2 * m) := by positivity
  refine ⟨etaProf m c, continuous_etaProf m c, etaProf_nonneg hm1 hc0.le, integral_etaProf hm1 hc0, ?_, ?_, ?_⟩
  · intro x
    rw [hN', jb_rpow_neg_natCast]
    exact (etaProf_le hm1 hc0 hc1 x).trans (mul_le_mul_of_nonneg_right hĈ (by positivity))
  · intro x
    rw [hN', jb_rpow_neg_natCast]
    refine le_trans ?_ (le_etaProf hm1 hc0 hc1 x)
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hĈ0 hĈ) (by positivity)
  · intro ξ hξ
    apply fourier_etaProf_eq_zero hm1 ha0
    rw [hmA]; exact hξ

/-- The threshold `N (3N/δ)^N` is monotone in `N` (for `δ ≤ 1/4`, `N ≥ 2`). -/
theorem etaThreshold_mono {N N' : ℕ} (h2 : 2 ≤ N') (hle : N' ≤ N) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    (N' : ℝ) * (3 * N' / δ) ^ N' ≤ (N : ℝ) * (3 * N / δ) ^ N := by
  have hN'R : (2 : ℝ) ≤ N' := by exact_mod_cast h2
  have hleR : (N' : ℝ) ≤ N := by exact_mod_cast hle
  have h1 : 1 ≤ 3 * (N' : ℝ) / δ := by
    rw [le_div_iff₀ hδ]; linarith
  have h3 : 3 * (N' : ℝ) / δ ≤ 3 * N / δ := by gcongr
  calc (N' : ℝ) * (3 * N' / δ) ^ N' ≤ (N : ℝ) * (3 * N' / δ) ^ N' := by gcongr
    _ ≤ (N : ℝ) * (3 * N / δ) ^ N' := by gcongr
    _ ≤ (N : ℝ) * (3 * N / δ) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (h1.trans h3) hle) (by linarith)

/-- **V05-1 for a lowered decay order** (the tree class `𝔭.tree`, `N := N/8`, same `δ`, `C`): the threshold of
`𝔭` suffices. -/
theorem exists_etaCut_le (𝔭 : Params) {N' : ℕ} (hN' : Even N') (hN2 : 2 ≤ N') (hle : N' ≤ 𝔭.N)
    (hδ : 0 < 𝔭.δ) (hδ1 : 𝔭.δ ≤ 1 / 4) (hC : (𝔭.N : ℝ) * (3 * 𝔭.N / 𝔭.δ) ^ 𝔭.N ≤ 𝔭.C) :
    ∃ η : ℝ → ℝ, IsEtaCut { 𝔭 with N := N' } η :=
  exists_etaCut { 𝔭 with N := N' } hN' hN2 hδ hδ1 ((etaThreshold_mono hN2 hle hδ hδ1).trans hC)

theorem exists_etaCut_tree (𝔭 : Params) (hN' : Even (𝔭.N / 8)) (hN2 : 2 ≤ 𝔭.N / 8)
    (hδ : 0 < 𝔭.δ) (hδ1 : 𝔭.δ ≤ 1 / 4) (hC : (𝔭.N : ℝ) * (3 * 𝔭.N / 𝔭.δ) ^ 𝔭.N ≤ 𝔭.C) :
    ∃ η : ℝ → ℝ, IsEtaCut 𝔭.tree η :=
  exists_etaCut_le 𝔭 hN' hN2 (Nat.div_le_self _ _) hδ hδ1 hC

end PrimeBHT.TimeFrequency.X2
