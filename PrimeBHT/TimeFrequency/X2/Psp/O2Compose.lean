module

public import PrimeBHT.TimeFrequency.X2.Psp.OverlapLean

/-!
# X2, V13 O2 (a): composition of multipliers on bounded functions

`docs/audits/X2-V13-route-check.md` §2.6, MTT2 §8.  The O2 estimate for the overlapping projection rests on the
operator identities `T_n T_m f = T_{n m} f` for smooth compactly supported symbols `n, m` and BOUNDED measurable `f`
(not band-limited: `f` is the Hilbert-space-valued test function itself), which are proved here by Fubini with the
Schwartz kernels `𝓕⁻ n`, `𝓕⁻ m`:

* `fourierInv_mul_eq`: `𝓕⁻(a b)(w) = ∫ 𝓕⁻ b y 𝓕⁻ a (w - y) dy`;
* `tm_comp`: `tm a (tm b f) = tm (a b) f`; `tm_comp_self` (`a b = b`) and `tm_comp_zero` (`a b = 0`);
* `tmult_comp`, `tmult_comp_self`, `tmult_comp_zero`: the vector versions (coordinatewise);
* `fourierInv_shift`: `𝓕⁻ (s (· - θ)) u = e(θ u) 𝓕⁻ s u` (the kernel of a modulated symbol);
* linearity of `tm` on bounded measurable inputs (`tm_add`, `tm_sub`, `tm_const_mul`, `tm_finset_sum`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-! ## The kernel of a product of symbols -/

theorem fourierInv_mul_eq {a b : ℝ → ℂ} (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (hb : ContDiff ℝ ∞ b)
    (hbc : HasCompactSupport b) (w : ℝ) :
    𝓕⁻ (fun ξ => a ξ * b ξ) w = ∫ y, 𝓕⁻ b y * 𝓕⁻ a (w - y) := by
  have hkb := kerS_apply hb hbc
  have hkbi : Integrable (𝓕⁻ b) := hkb ▸ (kerS b hb hbc).integrable
  have hkbc : Continuous (𝓕⁻ b) := hkb ▸ (kerS b hb hbc).continuous
  have hai : Integrable a := ha.continuous.integrable_of_hasCompactSupport hac
  have hbF : ∀ ξ, b ξ = ∫ y, Complex.exp (↑(-2 * π * y * ξ) * Complex.I) • 𝓕⁻ b y := by
    intro ξ
    have := fourier_kerS hb hbc ξ
    rw [hkb] at this
    rw [← this, Real.fourier_real_eq_integral_exp_smul]
  have hint : Integrable (Function.uncurry fun (ξ y : ℝ) =>
      Complex.exp (↑(2 * π * ξ * w) * Complex.I) * a ξ *
        (Complex.exp (↑(-2 * π * y * ξ) * Complex.I) * 𝓕⁻ b y)) (volume.prod volume) := by
    have h1 : Integrable (fun p : ℝ × ℝ => ‖a p.1‖ * ‖𝓕⁻ b p.2‖) (volume.prod volume) :=
      hai.norm.mul_prod hkbi.norm
    refine h1.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      have : Continuous a := ha.continuous
      fun_prop
    · obtain ⟨ξ, y⟩ := p
      simp only [Function.uncurry_apply_pair, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact le_of_eq rfl
  calc 𝓕⁻ (fun ξ => a ξ * b ξ) w
      = ∫ ξ, Complex.exp (↑(2 * π * ξ * w) * Complex.I) * a ξ * b ξ := by
        rw [Real.fourierInv_eq']
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        simp only [smul_eq_mul, inner, RCLike.re_to_real, star_trivial]
        ring_nf
    _ = ∫ ξ, ∫ y, Complex.exp (↑(2 * π * ξ * w) * Complex.I) * a ξ *
          (Complex.exp (↑(-2 * π * y * ξ) * Complex.I) * 𝓕⁻ b y) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        beta_reduce
        rw [integral_const_mul]
        congr 1
        rw [hbF ξ]
        simp only [smul_eq_mul]
    _ = ∫ y, ∫ ξ, Complex.exp (↑(2 * π * ξ * w) * Complex.I) * a ξ *
          (Complex.exp (↑(-2 * π * y * ξ) * Complex.I) * 𝓕⁻ b y) :=
        integral_integral_swap hint
    _ = ∫ y, 𝓕⁻ b y * 𝓕⁻ a (w - y) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        beta_reduce
        rw [Real.fourierInv_eq' a (w - y), ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        simp only [smul_eq_mul, inner, RCLike.re_to_real, star_trivial]
        have : Complex.exp (↑(2 * π * ξ * w) * Complex.I) * Complex.exp (↑(-2 * π * y * ξ) * Complex.I) =
            Complex.exp (↑(2 * π * (w - y) * ξ) * Complex.I) := by
          rw [← Complex.exp_add]; congr 1; push_cast; ring
        calc _ = (Complex.exp (↑(2 * π * ξ * w) * Complex.I) * Complex.exp (↑(-2 * π * y * ξ) * Complex.I)) *
              a ξ * 𝓕⁻ b y := by ring
          _ = _ := by rw [this]; ring_nf

/-- The kernel of a smooth compactly supported symbol is continuous and integrable. -/
theorem kernel_facts {a : ℝ → ℂ} (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) :
    Continuous (𝓕⁻ a) ∧ Integrable (𝓕⁻ a) := by
  have hk := kerS_apply ha hac
  exact ⟨hk ▸ (kerS a ha hac).continuous, hk ▸ (kerS a ha hac).integrable⟩

theorem integrable_dconv {φ ψ : ℝ → ℂ} (hφ : Integrable φ) (hψ : Integrable ψ) (hφm : Continuous φ)
    (hψm : Continuous ψ) {f : ℝ → ℂ} (hf : Measurable f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) :
    Integrable (Function.uncurry fun (z w : ℝ) => φ z * (ψ (z - w) * f w)) (volume.prod volume) := by
  have h1 : Integrable (fun p : ℝ × ℝ => ‖φ p.2‖ * ‖ψ (-(p.1 - p.2))‖) (volume.prod volume) :=
    Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hφ.norm hψ.comp_neg.norm
  have h2 := h1.swap.const_mul B
  refine h2.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · have : Measurable f := hf
    refine Measurable.aestronglyMeasurable ?_
    have : Measurable (Function.uncurry fun (z w : ℝ) => φ z * (ψ (z - w) * f w)) := by
      unfold Function.uncurry
      have := hφm.measurable
      have := hψm.measurable
      fun_prop
    exact this
  · obtain ⟨z, w⟩ := p
    simp only [Function.uncurry_apply_pair, Function.comp_apply, Prod.swap_prod_mk, norm_mul, neg_sub]
    have := hB w
    have h0 := norm_nonneg (φ z)
    have h0' := norm_nonneg (ψ (z - w))
    calc ‖φ z‖ * (‖ψ (z - w)‖ * ‖f w‖) ≤ ‖φ z‖ * (‖ψ (z - w)‖ * B) := by gcongr
      _ = B * (‖φ z‖ * ‖ψ (z - w)‖) := by ring

/-- **Composition of multipliers on bounded measurable functions**: `T_a (T_b f) = T_{a b} f`. -/
theorem tm_comp {a b : ℝ → ℂ} (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (hb : ContDiff ℝ ∞ b)
    (hbc : HasCompactSupport b) {f : ℝ → ℂ} (hf : Measurable f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) (x : ℝ) :
    tm a (tm b f) x = tm (fun ξ => a ξ * b ξ) f x := by
  obtain ⟨hkac, hkai⟩ := kernel_facts ha hac
  obtain ⟨hkbc, hkbi⟩ := kernel_facts hb hbc
  have hint := integrable_dconv (φ := fun z => 𝓕⁻ a (x - z)) (ψ := 𝓕⁻ b) (hkai.comp_sub_left x) hkbi
    (hkac.comp (continuous_const.sub continuous_id)) hkbc hf hB
  unfold tm
  have e1 : ∀ z, 𝓕⁻ a (x - z) * (∫ w, 𝓕⁻ b (z - w) * f w) = ∫ w, 𝓕⁻ a (x - z) * (𝓕⁻ b (z - w) * f w) :=
    fun z => (integral_const_mul _ _).symm
  simp_rw [e1]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  beta_reduce
  have e2 : ∫ z, 𝓕⁻ a (x - z) * (𝓕⁻ b (z - w) * f w) = (∫ z, 𝓕⁻ a (x - z) * 𝓕⁻ b (z - w)) * f w := by
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  rw [e2, fourierInv_mul_eq ha hac hb hbc (x - w)]
  congr 1
  have := integral_sub_right_eq_self (μ := (volume : Measure ℝ)) (fun y => 𝓕⁻ b y * 𝓕⁻ a (x - w - y)) w
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  beta_reduce
  rw [show x - w - (z - w) = x - z by ring]
  ring

/-- `T_a T_b f = T_b f` if `a b = b` (`a = 1` on the support of `b`). -/
theorem tm_comp_self {a b : ℝ → ℂ} (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (hb : ContDiff ℝ ∞ b)
    (hbc : HasCompactSupport b) (hab : ∀ ξ, a ξ * b ξ = b ξ) {f : ℝ → ℂ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ z, ‖f z‖ ≤ B) (x : ℝ) : tm a (tm b f) x = tm b f x := by
  rw [tm_comp ha hac hb hbc hf hB x]
  have : (fun ξ => a ξ * b ξ) = b := funext hab
  rw [this]

/-- `T_a T_b f = 0` if `a b = 0` (disjoint supports). -/
theorem tm_comp_zero {a b : ℝ → ℂ} (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (hb : ContDiff ℝ ∞ b)
    (hbc : HasCompactSupport b) (hab : ∀ ξ, a ξ * b ξ = 0) {f : ℝ → ℂ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ z, ‖f z‖ ≤ B) (x : ℝ) : tm a (tm b f) x = 0 := by
  rw [tm_comp ha hac hb hbc hf hB x]
  have : (fun ξ => a ξ * b ξ) = fun _ => (0 : ℂ) := funext hab
  rw [this]
  simp [tm, Real.fourierInv_eq]

/-! ## Vector versions -/

section Vector

variable {P : ℕ} [NeZero P]

/-- coordinatewise bound from the `Y`-norm bound -/
theorem coord_bound_o2 {F : ℝ → ZMod P → ℂ} {B : ℝ} (hB : ∀ x, yNorm 2 (F x) ≤ B) (z : ℝ) (y : ZMod P) :
    ‖F z y‖ ≤ (P : ℝ) ^ (2 : ℝ)⁻¹ * B := by
  have h1 := norm_apply_le_rpow_mul_yNorm (s := 2) (by norm_num) (F z) y
  have hP : (0 : ℝ) ≤ (P : ℝ) ^ (2 : ℝ)⁻¹ := by positivity
  exact h1.trans (mul_le_mul_of_nonneg_left (hB z) hP)

end Vector

/-! ## The kernel of a modulated symbol -/

/-- `𝓕⁻ (s (· - θ)) (u) = e(θ u) 𝓕⁻ s (u)`. -/
theorem fourierInv_shift (s : ℝ → ℂ) (θ u : ℝ) :
    𝓕⁻ (fun ξ => s (ξ - θ)) u = Complex.exp (↑(2 * π * θ * u) * Complex.I) * 𝓕⁻ s u := by
  rw [Real.fourierInv_eq' (fun ξ => s (ξ - θ)) u, Real.fourierInv_eq' s u]
  have := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun v : ℝ => Complex.exp (↑(2 * π * inner ℝ v u) * Complex.I) • s (v - θ)) θ
  rw [← this, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul, inner, RCLike.re_to_real, star_trivial, add_sub_cancel_right]
  have e : Complex.exp (↑(2 * π * (u * (v + θ))) * Complex.I) =
      Complex.exp (↑(2 * π * θ * u) * Complex.I) * Complex.exp (↑(2 * π * (u * v)) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e]
  ring

/-! ## Linearity of `tm` on bounded measurable inputs -/

theorem integrable_kmul {K : ℝ → ℂ} (hK : Integrable K) {f : ℝ → ℂ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ z, ‖f z‖ ≤ B) (x : ℝ) (hKm : Continuous K) : Integrable (fun z => K (x - z) * f z) := by
  have h1 : Integrable (fun z => B * ‖K (x - z)‖) := (hK.comp_sub_left x).norm.const_mul B
  refine h1.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · have := hKm.measurable
    have := hf
    exact (by fun_prop : Measurable fun z => K (x - z) * f z).aestronglyMeasurable
  · rw [norm_mul]
    have := hB z
    have h0 := norm_nonneg (K (x - z))
    calc ‖K (x - z)‖ * ‖f z‖ ≤ ‖K (x - z)‖ * B := by gcongr
      _ = B * ‖K (x - z)‖ := by ring

theorem tm_add {m : ℝ → ℂ} (hm : ContDiff ℝ ∞ m) (hmc : HasCompactSupport m) {f g : ℝ → ℂ} (hf : Measurable f)
    (hg : Measurable g) {Bf Bg : ℝ} (hBf : ∀ z, ‖f z‖ ≤ Bf) (hBg : ∀ z, ‖g z‖ ≤ Bg) (x : ℝ) :
    tm m (fun z => f z + g z) x = tm m f x + tm m g x := by
  obtain ⟨hkc, hki⟩ := kernel_facts hm hmc
  unfold tm
  rw [← integral_add (integrable_kmul hki hf hBf x hkc) (integrable_kmul hki hg hBg x hkc)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  ring

theorem tm_const_mul {m : ℝ → ℂ} (c : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    tm m (fun z => c * f z) x = c * tm m f x := by
  unfold tm
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  ring

theorem tm_neg {m : ℝ → ℂ} (f : ℝ → ℂ) (x : ℝ) : tm m (fun z => -f z) x = -tm m f x := by
  have := tm_const_mul (m := m) (-1) f x
  simpa using this

theorem tm_sub {m : ℝ → ℂ} (hm : ContDiff ℝ ∞ m) (hmc : HasCompactSupport m) {f g : ℝ → ℂ} (hf : Measurable f)
    (hg : Measurable g) {Bf Bg : ℝ} (hBf : ∀ z, ‖f z‖ ≤ Bf) (hBg : ∀ z, ‖g z‖ ≤ Bg) (x : ℝ) :
    tm m (fun z => f z - g z) x = tm m f x - tm m g x := by
  have e : (fun z => f z - g z) = fun z => f z + (-g z) := funext fun z => by ring
  rw [e, tm_add hm hmc hf (g := fun z => -g z) hg.neg hBf (fun z => by simpa using hBg z) x, tm_neg]
  ring

end PrimeBHT.TimeFrequency.X2
