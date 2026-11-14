module

public import PrimeBHT.Frozen.YNorm
public import PrimeBHT.Frozen.TensorFun
public import PrimeBHT.Frozen.TensorFourier
public import PrimeBHT.Frozen.MultiplierForm
public import PrimeBHT.TransferenceAssembly.X2
import PrimeBHT.Interface.X2Checks
import PrimeBHT.Lift
import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# X2, node V03: reduction to band-limited tensor Schwartz functions

Blueprint `docs/x2-blueprint.md`, node V03 (steps 1-4), over the FROZEN definitions
`PrimeBHT.Statements.{yNorm, tensorFun, tensorFourier, multiplierForm}`. Fully proved.

## Final signatures (namespace `PrimeBHT.TimeFrequency.X2`)

* `X2BandLimited : Prop`: the second conjunct of `PrimeBHT.TransferenceAssembly.X2Statement`
  (`∀ u > 1, ∀ A, ∃ C ≥ 0, ∀ P T m, ContDiffOn ℝ ∞ m {0}ᶜ → symbol bounds → ∀ CT, (bound on T) →
  ∀ f₁ f₂ f₃, (∀ a, HasCompactSupport (𝓕 (f_i a))) for i = 1, 2, 3 → ‖multiplierForm m T f₁ f₂ f₃‖ₑ ≤
  ofReal (C * CT) * ‖F₁‖_{L²L²} * ‖F₂‖_{L²L²} * ‖F₃‖_{L^∞L^u}`) for triples with compactly supported partial
  Fourier transforms; same quantifiers, same constant `C`.
* `x2Statement_of_bandLimited : X2BandLimited → PrimeBHT.TransferenceAssembly.X2Statement`
  (the integrability conjunct is `PrimeBHT.Interface.X2.integrable_of_hyps`).

## Proof (as in the blueprint, with one simplification)

`bandLimit g L f = 𝓕⁻(g(·/L) · 𝓕 f) = SchwartzMap.fourierMultiplierCLM ℂ (g(·/L)) f`, where `g = 𝓕 κ` is smooth with
compact support, `κ = |𝓕 ψ|² / ∫ ψ² ≥ 0`, `∫ κ = 1` (`exists_bandLimiter`: `ψ` a real `ContDiffBump`,
`g = (ψ ⋆ ψ̃)(-·)/‖ψ‖²` through Mathlib's `SchwartzMap.convolution`). Physical-side formula
(`bandLimit_apply`, Fubini): `(bandLimit g L f)(x) = ∫ κ(z) f(x - z/L) dz`. Jensen for the probability kernel `κ`
(`rpow_integral_le`, via Bernoulli's inequality) gives `‖F^{(L)}(x)‖_{L^s(Y_P)}^s ≤ ∫ κ(z) ‖F(x - z/L)‖_s^s dz`
(`yNorm_rpow_integral_le`), hence `‖F₃^{(L)}‖_{L^∞L^u} ≤ ‖F₃‖_{L^∞L^u}` and `‖F_i^{(L)}‖_{L²L²} ≤ ‖F_i‖_{L²L²}`
exactly, with no constant (`eLpNorm_top_bandLimit_le`, `eLpNorm_two_bandLimit_le`; translation invariance of
Lebesgue measure and Tonelli). Continuity of the form (`tendsto_multiplierForm_bandLimit`): the band limiter
multiplies every `f̂_{i,A}(ξ)` by the same scalar `g(ξ/L)`, so the integrand of `Λ(f^{(L)})` is the integrand of
`Λ(f)` times `g(ξ₁/L) g(ξ₂/L) conj g((ξ₁+ξ₂)/L)`, of modulus `≤ 1` and tending to `1`; dominated convergence with
the majorant of V01.

## Corrections / remarks on the blueprint

(a) Step 3 of the blueprint dominates with `A₀ CT ‖G₁‖₁‖G₂‖₁‖G₃‖_∞`; the factorisation above makes `CT` and the
Schwartz majorant unnecessary. (b) `ψ` need not be even; `χ^∨ = |ψ̂|²` already for complex `ψ`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate ContDiff Convolution Real
open PrimeBHT.Statements (yNorm tensorFun tensorFourier multiplierForm)

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- A probability kernel on `ℝ`: continuous, nonnegative, integrable, of integral one. -/
structure IsKernel (κ : ℝ → ℝ) : Prop where
  continuous : Continuous κ
  nonneg : ∀ x, 0 ≤ κ x
  integrable : Integrable κ
  integral_eq_one : ∫ x, κ x = 1


/-! ### Part A: the kernel -/

/-- `𝓕` of the reflection of a real function is the conjugate of `𝓕` of the function. -/
theorem fourier_reflect_ofReal (b : ℝ → ℝ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => ((b (-x) : ℝ) : ℂ)) ξ = conj (𝓕 (fun x : ℝ => ((b x : ℝ) : ℂ)) ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_conj]
  rw [← integral_neg_eq_self (fun v => Complex.exp (↑(-2 * π * v * ξ) * Complex.I) •
    ((b (-v) : ℝ) : ℂ)) volume]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [neg_neg, smul_eq_mul, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp

theorem fourier_fourier_schwartz (G : 𝓢(ℝ, ℂ)) (ξ : ℝ) : 𝓕 (⇑(𝓕 G : 𝓢(ℝ, ℂ))) ξ = G (-ξ) := by
  have h : (𝓕⁻ (𝓕 G : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) = G := FourierPair.fourierInv_fourier_eq G
  have h2 := congrArg (fun H : 𝓢(ℝ, ℂ) => H (-ξ)) h
  simp only [SchwartzMap.fourierInv_coe] at h2
  rw [Real.fourierInv_eq_fourier_neg, neg_neg] at h2
  rw [← h2]

theorem exists_kernel : ∃ (κ : ℝ → ℝ) (g : ℝ → ℂ), Continuous κ ∧ (∀ x, 0 ≤ κ x) ∧ Integrable κ ∧
    ∫ x, κ x = 1 ∧ ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
    ∀ ξ, g ξ = 𝓕 (fun x : ℝ => ((κ x : ℝ) : ℂ)) ξ := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hbc : HasCompactSupport (fun x : ℝ => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have hbs : ContDiff ℝ ∞ (fun x : ℝ => ((b x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hbc' : HasCompactSupport (fun x : ℝ => ((b (-x) : ℝ) : ℂ)) :=
    hbc.comp_homeomorph (Homeomorph.neg ℝ)
  have hbs' : ContDiff ℝ ∞ (fun x : ℝ => ((b (-x) : ℝ) : ℂ)) := hbs.comp contDiff_neg
  let ψ : 𝓢(ℝ, ℂ) := hbc.toSchwartzMap hbs
  let ψ' : 𝓢(ℝ, ℂ) := hbc'.toSchwartzMap hbs'
  let Gs : 𝓢(ℝ, ℂ) := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) ψ ψ'
  have hGapp : ∀ x, Gs x = ∫ z, ψ z * ψ' (x - z) := fun x => by
    rw [SchwartzMap.convolution_apply, convolution_def]
    rfl
  have hGc : HasCompactSupport (⇑Gs) := by
    have : (⇑Gs) = (⇑ψ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (⇑ψ') := funext fun x => by
      rw [SchwartzMap.convolution_apply]
    rw [this]
    exact HasCompactSupport.convolution _ hbc hbc'
  have hψ' : ∀ ξ, (𝓕 ψ' : 𝓢(ℝ, ℂ)) ξ = conj ((𝓕 ψ : 𝓢(ℝ, ℂ)) ξ) := fun ξ =>
    fourier_reflect_ofReal (fun x => b x) ξ
  have hF : ∀ ξ, (𝓕 Gs : 𝓢(ℝ, ℂ)) ξ = (𝓕 ψ : 𝓢(ℝ, ℂ)) ξ * conj ((𝓕 ψ : 𝓢(ℝ, ℂ)) ξ) := fun ξ => by
    have := congrArg (fun H : 𝓢(ℝ, ℂ) => H ξ) (SchwartzMap.fourier_convolution (𝕜 := ℂ)
      (ContinuousLinearMap.mul ℂ ℂ) ψ ψ')
    simp only [SchwartzMap.pairing_apply_apply, ContinuousLinearMap.mul_apply'] at this
    rw [this, hψ']
  -- the constant
  have hc : 0 < ∫ x, b x * b x := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) (b.continuous.mul b.continuous) ?_ ?_ ?_
    · exact b.hasCompactSupport.mul_left
    · intro x; exact mul_nonneg (b.nonneg) (b.nonneg)
    · rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]; simp
  have hG0 : Gs 0 = (((∫ x, b x * b x : ℝ)) : ℂ) := by
    rw [hGapp, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp [ψ, ψ']
  set c : ℝ := ∫ x, b x * b x with hcdef
  have hcne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hκC : ∀ x, (((‖(𝓕 ψ : 𝓢(ℝ, ℂ)) x‖ ^ 2 / c : ℝ)) : ℂ) = (c : ℂ)⁻¹ * (𝓕 Gs : 𝓢(ℝ, ℂ)) x := by
    intro x
    rw [hF, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hg : ∀ ξ, (c : ℂ)⁻¹ * Gs (-ξ) =
      𝓕 (fun x : ℝ => (((‖(𝓕 ψ : 𝓢(ℝ, ℂ)) x‖ ^ 2 / c : ℝ)) : ℂ)) ξ := by
    intro ξ
    simp only [hκC]
    rw [Real.fourier_real_eq_integral_exp_smul, ← fourier_fourier_schwartz Gs ξ,
      Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul]
    ring
  refine ⟨fun x => ‖(𝓕 ψ : 𝓢(ℝ, ℂ)) x‖ ^ 2 / c, fun ξ => (c : ℂ)⁻¹ * Gs (-ξ), ?_, ?_, ?_, ?_, ?_, ?_, hg⟩
  · exact (((𝓕 ψ : 𝓢(ℝ, ℂ)).continuous.norm).pow 2).div_const c
  · intro x; exact div_nonneg (sq_nonneg _) hc.le
  · have : Integrable (fun x : ℝ => (((‖(𝓕 ψ : 𝓢(ℝ, ℂ)) x‖ ^ 2 / c : ℝ)) : ℂ)) := by
      simp only [hκC]
      exact (𝓕 Gs : 𝓢(ℝ, ℂ)).integrable.const_mul _
    exact this.re.congr (Filter.Eventually.of_forall fun x => Complex.ofReal_re _)
  · have h0 := hg 0
    have h1 : 𝓕 (fun x : ℝ => (((‖(𝓕 ψ : 𝓢(ℝ, ℂ)) x‖ ^ 2 / c : ℝ)) : ℂ)) 0 =
        ((∫ x, ‖(𝓕 ψ : 𝓢(ℝ, ℂ)) x‖ ^ 2 / c : ℝ) : ℂ) := by
      rw [Real.fourier_real_eq, ← integral_complex_ofReal]
      simp
    have h2 : ((∫ x, ‖(𝓕 ψ : 𝓢(ℝ, ℂ)) x‖ ^ 2 / c : ℝ) : ℂ) = 1 := by
      rw [← h1, ← h0, neg_zero, hG0, inv_mul_cancel₀ hcne]
    exact_mod_cast h2
  · exact contDiff_const.mul ((Gs.smooth ⊤).comp contDiff_neg)
  · exact (hGc.comp_homeomorph (Homeomorph.neg ℝ)).mul_left

/-! ### Part B: band limiting -/

/-- The band-limiting operator `f ↦ 𝓕⁻(g(·/L) · 𝓕 f)`. -/
noncomputable def bandLimit (g : ℝ → ℂ) (L : ℝ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.fourierMultiplierCLM ℂ (fun ξ => g (ξ / L)) f

theorem hasTemperateGrowth_dilate {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    {L : ℝ} (hL : L ≠ 0) : Function.HasTemperateGrowth (fun ξ : ℝ => g (ξ / L)) := by
  have e : (fun ξ : ℝ => g (ξ / L)) = g ∘ (Homeomorph.mulLeft₀ L⁻¹ (inv_ne_zero hL)) := by
    funext ξ; simp [div_eq_inv_mul]
  rw [e]
  refine HasCompactSupport.hasTemperateGrowth (hgc.comp_homeomorph _) ?_
  exact hg.comp (contDiff_const.mul contDiff_id)

theorem fourier_bandLimit {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    {L : ℝ} (hL : L ≠ 0) (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (⇑(bandLimit g L f)) ξ = g (ξ / L) * 𝓕 (⇑f) ξ := by
  have htg := hasTemperateGrowth_dilate hg hgc hL
  have h : (𝓕 (bandLimit g L f) : 𝓢(ℝ, ℂ)) =
      SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => g (ξ / L)) (𝓕 f) := by
    unfold bandLimit
    rw [SchwartzMap.fourierMultiplierCLM_apply, FourierInvPair.fourier_fourierInv_eq]
  have := congrArg (fun H : 𝓢(ℝ, ℂ) => H ξ) h
  simp only [SchwartzMap.smulLeftCLM_apply_apply htg, smul_eq_mul] at this
  exact this

theorem schwartz_apply_eq_integral (f : 𝓢(ℝ, ℂ)) (w : ℝ) :
    f w = ∫ ξ : ℝ, Complex.exp (↑(2 * π * (w * ξ)) * Complex.I) * 𝓕 (⇑f) ξ := by
  have h0 : (𝓕⁻ (𝓕 f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) = f := FourierPair.fourierInv_fourier_eq f
  have h2 : (𝓕⁻ (𝓕 f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) w = f w := by rw [h0]
  rw [← h2, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
  rfl

theorem bandLimit_apply {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) {κ : ℝ → ℝ}
    (hκc : Continuous κ) (hκi : Integrable κ)
    (hgκ : ∀ ξ, g ξ = 𝓕 (fun x : ℝ => ((κ x : ℝ) : ℂ)) ξ)
    {L : ℝ} (hL : L ≠ 0) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    bandLimit g L f x = ∫ z, (κ z : ℂ) * f (x - z / L) := by
  rw [schwartz_apply_eq_integral]
  simp_rw [fourier_bandLimit hg hgc hL, hgκ,
    Real.fourier_real_eq_integral_exp_smul (fun x : ℝ => ((κ x : ℝ) : ℂ))]
  have hf : Integrable (𝓕 (⇑f)) := (𝓕 f : 𝓢(ℝ, ℂ)).integrable
  -- the double integrand
  set K : ℝ → ℝ → ℂ := fun ξ z => Complex.exp (↑(2 * π * (x * ξ)) * Complex.I) *
    (Complex.exp (↑(-2 * π * z * (ξ / L)) * Complex.I) * (κ z : ℂ) * 𝓕 (⇑f) ξ) with hK
  have h1 : ∀ ξ : ℝ, Complex.exp (↑(2 * π * (x * ξ)) * Complex.I) *
      ((∫ (v : ℝ), Complex.exp (↑(-2 * π * v * (ξ / L)) * Complex.I) • (κ v : ℂ)) * 𝓕 (⇑f) ξ) =
      ∫ z, K ξ z := by
    intro ξ
    rw [← integral_mul_const, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hK, smul_eq_mul]
  simp_rw [h1]
  have hKc : Continuous (Function.uncurry K) := by
    have := (𝓕 f : 𝓢(ℝ, ℂ)).continuous
    simp only [hK]
    fun_prop
  have hKi : Integrable (Function.uncurry K) (volume.prod volume) := by
    have hb : Integrable (fun p : ℝ × ℝ => ‖𝓕 (⇑f) p.1‖ * |κ p.2|) (volume.prod volume) :=
      hf.norm.mul_prod hκi.abs
    refine hb.mono' hKc.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    simp only [hK, Function.uncurry, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    rw [mul_comm]
  rw [integral_integral_swap hKi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  have hz : ∀ ξ : ℝ, K ξ z = (κ z : ℂ) * (Complex.exp (↑(2 * π * ((x - z / L) * ξ)) * Complex.I) *
      𝓕 (⇑f) ξ) := by
    intro ξ
    simp only [hK]
    have : Complex.exp (↑(2 * π * (x * ξ)) * Complex.I) *
        Complex.exp (↑(-2 * π * z * (ξ / L)) * Complex.I) =
        Complex.exp (↑(2 * π * ((x - z / L) * ξ)) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc _ = (Complex.exp (↑(2 * π * (x * ξ)) * Complex.I) *
        Complex.exp (↑(-2 * π * z * (ξ / L)) * Complex.I)) * (κ z : ℂ) * 𝓕 (⇑f) ξ := by ring
      _ = _ := by rw [this]; ring
  simp_rw [hz]
  rw [integral_const_mul, ← schwartz_apply_eq_integral]

/-! ### Part C: Jensen -/

theorem rpow_integral_le {κ b : ℝ → ℝ} {s : ℝ} (hs : 1 ≤ s) (hκ : IsKernel κ)
    (hb0 : ∀ z, 0 ≤ b z) (hκb : Integrable (fun z => κ z * b z))
    (hκbs : Integrable (fun z => κ z * b z ^ s)) :
    (∫ z, κ z * b z) ^ s ≤ ∫ z, κ z * b z ^ s := by
  set m := ∫ z, κ z * b z with hmdef
  have hm0 : 0 ≤ m := integral_nonneg fun z => mul_nonneg (hκ.nonneg z) (hb0 z)
  rcases hm0.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by linarith)]
    exact integral_nonneg fun z => mul_nonneg (hκ.nonneg z) (Real.rpow_nonneg (hb0 z) s)
  · set c₁ : ℝ := s * m ^ (s - 1) with hc₁
    have key : ∀ z, m ^ s + c₁ * (b z - m) ≤ b z ^ s := by
      intro z
      have h1 := one_add_mul_self_le_rpow_one_add (s := b z / m - 1) (by
        have : 0 ≤ b z / m := div_nonneg (hb0 z) hm0
        linarith) hs
      have h2 : (1 + (b z / m - 1)) = b z / m := by ring
      rw [h2, Real.div_rpow (hb0 z) hm0] at h1
      have h3 : 0 < m ^ s := Real.rpow_pos_of_pos hpos s
      have h4 := mul_le_mul_of_nonneg_left h1 h3.le
      have h5 : m ^ s * (b z ^ s / m ^ s) = b z ^ s := by field_simp
      have h6 : m ^ s * (1 + s * (b z / m - 1)) = m ^ s + c₁ * (b z - m) := by
        rw [hc₁, Real.rpow_sub_one hpos.ne']
        field_simp
      linarith
    have hint1 : Integrable (fun z => κ z * (m ^ s + c₁ * (b z - m))) := by
      have : (fun z => κ z * (m ^ s + c₁ * (b z - m))) =
          fun z => (m ^ s - c₁ * m) * κ z + c₁ * (κ z * b z) := by funext z; ring
      rw [this]
      exact (hκ.integrable.const_mul _).add (hκb.const_mul _)
    calc m ^ s = ∫ z, κ z * (m ^ s + c₁ * (b z - m)) := by
          have : (fun z => κ z * (m ^ s + c₁ * (b z - m))) =
              fun z => (m ^ s - c₁ * m) * κ z + c₁ * (κ z * b z) := by funext z; ring
          rw [this, integral_add (hκ.integrable.const_mul _) (hκb.const_mul _),
            integral_const_mul, integral_const_mul, hκ.integral_eq_one, ← hmdef]
          ring
      _ ≤ ∫ z, κ z * b z ^ s := integral_mono hint1 hκbs fun z =>
          mul_le_mul_of_nonneg_left (key z) (hκ.nonneg z)

/-- Jensen-Minkowski for the `L^s(Y_P)` norm and a probability kernel. -/
theorem yNorm_rpow_integral_le {P : ℕ} [NeZero P] {κ : ℝ → ℝ} {s : ℝ} (hs : 1 ≤ s)
    (hκ : IsKernel κ) (a : ℝ → ZMod P → ℂ) {B : ℝ} (ha_cont : ∀ y, Continuous fun z => a z y)
    (ha_bd : ∀ z y, ‖a z y‖ ≤ B) :
    yNorm s (fun y => ∫ z, (κ z : ℂ) * a z y) ^ s ≤ ∫ z, κ z * yNorm s (a z) ^ s := by
  have hs0 : 0 < s := by linarith
  have hB : 0 ≤ B := (norm_nonneg _).trans (ha_bd 0 0)
  -- integrability of `κ z * (‖a z y‖ ^ r)` for `r ≥ 0`
  have hint : ∀ (y : ZMod P) (r : ℝ), 0 ≤ r → Integrable (fun z => κ z * ‖a z y‖ ^ r) := by
    intro y r hr
    have hc : Continuous fun z => ‖a z y‖ ^ r :=
      (continuous_norm.comp (ha_cont y)).rpow_const fun _ => Or.inr hr
    have := hκ.integrable.mul_bdd (c := B ^ r) hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        exact Real.rpow_le_rpow (norm_nonneg _) (ha_bd z y) hr)
    exact this
  have hnorm : ∀ y : ZMod P, ‖∫ z, (κ z : ℂ) * a z y‖ ≤ ∫ z, κ z * ‖a z y‖ := by
    intro y
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show ‖(κ z : ℂ) * a z y‖ = κ z * ‖a z y‖
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hκ.nonneg z)]
  have hy : ∀ y : ZMod P, ‖∫ z, (κ z : ℂ) * a z y‖ ^ s ≤ ∫ z, κ z * ‖a z y‖ ^ s := by
    intro y
    calc ‖∫ z, (κ z : ℂ) * a z y‖ ^ s ≤ (∫ z, κ z * ‖a z y‖) ^ s :=
          Real.rpow_le_rpow (norm_nonneg _) (hnorm y) hs0.le
      _ ≤ ∫ z, κ z * ‖a z y‖ ^ s :=
          rpow_integral_le hs hκ (fun z => norm_nonneg _) (by simpa using hint y 1 zero_le_one)
            (hint y s hs0.le)
  have hP0 : (0 : ℝ) ≤ (P : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg P)
  have hr : ∀ F : ZMod P → ℂ, yNorm s F ^ s = (P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ s := fun F =>
    PrimeBHT.Lift.yNorm_rpow_self hs0.ne' F
  rw [hr]
  simp only [hr]
  calc (P : ℝ)⁻¹ * ∑ y, ‖∫ z, (κ z : ℂ) * a z y‖ ^ s
      ≤ (P : ℝ)⁻¹ * ∑ y, ∫ z, κ z * ‖a z y‖ ^ s :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hy y) hP0
    _ = (P : ℝ)⁻¹ * ∫ z, ∑ y, κ z * ‖a z y‖ ^ s := by
        rw [integral_finsetSum _ (fun y _ => hint y s hs0.le)]
    _ = ∫ z, κ z * ((P : ℝ)⁻¹ * ∑ y, ‖a z y‖ ^ s) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [← Finset.mul_sum]
        ring

theorem eLpNorm_two_rpow_two {h : ℝ → ℝ} (hh : Continuous h) (h0 : ∀ x, 0 ≤ h x) :
    eLpNorm h 2 volume ^ (2 : ℝ) = ∫⁻ x, ENNReal.ofReal (h x ^ 2) := by
  have := eLpNorm_nnreal_pow_eq_lintegral (μ := volume) (p := 2) (by norm_num) hh.aestronglyMeasurable
  simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat] at this
  rw [this]
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal (h0 x), ENNReal.ofReal_rpow_of_nonneg (h0 x) (by norm_num), Real.rpow_two]

theorem lintegral_sq_smooth_le {κ : ℝ → ℝ} (hκ : IsKernel κ) {L : ℝ} {h₁ h₂ : ℝ → ℝ}
    (hh₂c : Continuous h₂) (hh₂0 : ∀ x, 0 ≤ h₂ x) {M : ℝ} (hh₂M : ∀ x, h₂ x ≤ M)
    (hle : ∀ x, h₁ x ^ 2 ≤ ∫ z, κ z * h₂ (x - z / L) ^ 2) :
    ∫⁻ x, ENNReal.ofReal (h₁ x ^ 2) ≤ ∫⁻ x, ENNReal.ofReal (h₂ x ^ 2) := by
  have hint : ∀ x : ℝ, Integrable (fun z => κ z * h₂ (x - z / L) ^ 2) := fun x => by
    have hc : Continuous fun z : ℝ => h₂ (x - z / L) ^ 2 :=
      (hh₂c.comp (by fun_prop)).pow 2
    exact hκ.integrable.mul_bdd (c := M ^ 2) hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (hh₂0 _) (hh₂M _) 2)
  have h1 : ∀ x : ℝ, ENNReal.ofReal (∫ z, κ z * h₂ (x - z / L) ^ 2) =
      ∫⁻ z, ENNReal.ofReal (κ z * h₂ (x - z / L) ^ 2) := fun x =>
    ofReal_integral_eq_lintegral_ofReal (hint x)
      (Filter.Eventually.of_forall fun z => mul_nonneg (hκ.nonneg z) (sq_nonneg _))
  have hmeas : Measurable (Function.uncurry fun (x z : ℝ) =>
      ENNReal.ofReal (κ z * h₂ (x - z / L) ^ 2)) := by
    have : Continuous (Function.uncurry fun (x z : ℝ) => κ z * h₂ (x - z / L) ^ 2) := by
      have := hκ.continuous
      have := hh₂c
      fun_prop
    exact ENNReal.measurable_ofReal.comp this.measurable
  have hκ1 : ∫⁻ z, ENNReal.ofReal (κ z) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hκ.integrable
      (Filter.Eventually.of_forall hκ.nonneg), hκ.integral_eq_one, ENNReal.ofReal_one]
  calc ∫⁻ x, ENNReal.ofReal (h₁ x ^ 2) ≤ ∫⁻ x, ENNReal.ofReal (∫ z, κ z * h₂ (x - z / L) ^ 2) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hle x)
    _ = ∫⁻ x, ∫⁻ z, ENNReal.ofReal (κ z * h₂ (x - z / L) ^ 2) := lintegral_congr h1
    _ = ∫⁻ z, ∫⁻ x, ENNReal.ofReal (κ z * h₂ (x - z / L) ^ 2) :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ z, ENNReal.ofReal (κ z) * ∫⁻ x, ENNReal.ofReal (h₂ x ^ 2) := by
        refine lintegral_congr fun z => ?_
        have hm : Measurable fun x : ℝ => ENNReal.ofReal (h₂ (x - z / L) ^ 2) :=
          ENNReal.measurable_ofReal.comp ((hh₂c.comp (by fun_prop)).pow 2).measurable
        simp only [ENNReal.ofReal_mul (hκ.nonneg z)]
        rw [lintegral_const_mul _ hm]
        congr 1
        exact lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (h₂ x ^ 2)) (z / L)
    _ = ∫⁻ x, ENNReal.ofReal (h₂ x ^ 2) := by
        have hm : Measurable fun z : ℝ => ENNReal.ofReal (κ z) :=
          ENNReal.measurable_ofReal.comp hκ.continuous.measurable
        rw [lintegral_mul_const _ hm, hκ1, one_mul]

/-! ### Part D: the mixed norms of the band-limited approximant -/

section MixedNorms

variable {P : ℕ} [NeZero P]

theorem continuous_tensorFun_apply (f : ZMod P → 𝓢(ℝ, ℂ)) (y : ZMod P) :
    Continuous fun w : ℝ => tensorFun f w y := by
  unfold tensorFun
  exact continuous_finsetSum _ fun A _ => (f A).continuous.mul continuous_const

theorem exists_norm_tensorFun_le (f : ZMod P → 𝓢(ℝ, ℂ)) :
    ∃ B : ℝ, ∀ w y, ‖tensorFun f w y‖ ≤ B := by
  choose c hc using fun A => PrimeBHT.Interface.X2.schwartz_bounded (f A)
  exact ⟨∑ A, c A, fun w y => (PrimeBHT.Interface.X2.norm_tensorFun_le f w y).trans
    (Finset.sum_le_sum fun A _ => hc A w)⟩

theorem integrable_kernel_mul_band {κ : ℝ → ℝ} (hκ : IsKernel κ) {h : ℝ → ℂ} (hh : Continuous h)
    {C : ℝ} (hC : ∀ z, ‖h z‖ ≤ C) : Integrable (fun z => (κ z : ℂ) * h z) :=
  hκ.integrable.ofReal.mul_bdd (c := C) hh.aestronglyMeasurable (Filter.Eventually.of_forall hC)

end MixedNorms


/-! ### Part E: the band limiter -/

/-- The data of an admissible band limiter: a probability kernel `κ ≥ 0` and its Fourier transform
`g = 𝓕 κ`, which is smooth with compact support. -/
structure BandLimiter (κ : ℝ → ℝ) (g : ℝ → ℂ) : Prop where
  kernel : IsKernel κ
  contDiff : ContDiff ℝ ∞ g
  compactSupport : HasCompactSupport g
  fourier_eq : ∀ ξ, g ξ = 𝓕 (fun x : ℝ => ((κ x : ℝ) : ℂ)) ξ

theorem exists_bandLimiter : ∃ (κ : ℝ → ℝ) (g : ℝ → ℂ), BandLimiter κ g := by
  obtain ⟨κ, g, h1, h2, h3, h4, h5, h6, h7⟩ := exists_kernel
  exact ⟨κ, g, ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7⟩⟩

namespace BandLimiter

variable {κ : ℝ → ℝ} {g : ℝ → ℂ}

theorem apply_zero (h : BandLimiter κ g) : g 0 = 1 := by
  rw [h.fourier_eq, Real.fourier_real_eq]
  simp [integral_complex_ofReal, h.kernel.integral_eq_one]

theorem norm_le_one (h : BandLimiter κ g) (ξ : ℝ) : ‖g ξ‖ ≤ 1 := by
  rw [h.fourier_eq]
  refine (Real.norm_fourier_le_integral_norm _ _).trans (le_of_eq ?_)
  have : (fun v : ℝ => ‖((κ v : ℝ) : ℂ)‖) = κ := by
    funext v; rw [Complex.norm_real, Real.norm_of_nonneg (h.kernel.nonneg v)]
  rw [this, h.kernel.integral_eq_one]

theorem continuous (h : BandLimiter κ g) : Continuous g := h.contDiff.continuous

end BandLimiter

/-! ### Part F: the tensor function of the band-limited approximant -/

section Tensor

variable {P : ℕ} [NeZero P] {κ : ℝ → ℝ} {g : ℝ → ℂ}

theorem tensorFun_bandLimit (hb : BandLimiter κ g) {L : ℝ} (hL : L ≠ 0)
    (f : ZMod P → 𝓢(ℝ, ℂ)) (x : ℝ) (y : ZMod P) :
    tensorFun (fun a => bandLimit g L (f a)) x y =
      ∫ z, (κ z : ℂ) * tensorFun f (x - z / L) y := by
  have hi : ∀ a ∈ (Finset.univ : Finset (ZMod P)), Integrable
      (fun z => (κ z : ℂ) * (f a (x - z / L) * (ZMod.stdAddChar (a * y) : ℂ))) := by
    intro a _
    obtain ⟨C, hC⟩ := PrimeBHT.Interface.X2.schwartz_bounded (f a)
    refine integrable_kernel_mul_band hb.kernel (((f a).continuous.comp (by fun_prop)).mul
      continuous_const) (C := C) fun z => ?_
    have : ‖(ZMod.stdAddChar (a * y) : ℂ)‖ = 1 := by simp [ZMod.stdAddChar_apply]
    rw [norm_mul, this, mul_one]
    exact hC _
  unfold tensorFun
  simp only [bandLimit_apply hb.contDiff hb.compactSupport hb.kernel.continuous
    hb.kernel.integrable hb.fourier_eq hL]
  calc ∑ a, (∫ z, (κ z : ℂ) * f a (x - z / L)) * (ZMod.stdAddChar (a * y) : ℂ)
      = ∑ a, ∫ z, (κ z : ℂ) * (f a (x - z / L) * (ZMod.stdAddChar (a * y) : ℂ)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← integral_mul_const]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [mul_assoc]
    _ = ∫ z, ∑ a, (κ z : ℂ) * (f a (x - z / L) * (ZMod.stdAddChar (a * y) : ℂ)) :=
        (integral_finsetSum _ hi).symm
    _ = ∫ z, (κ z : ℂ) * ∑ a, f a (x - z / L) * (ZMod.stdAddChar (a * y) : ℂ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        show ∑ a, (κ z : ℂ) * (f a (x - z / L) * (ZMod.stdAddChar (a * y) : ℂ)) = _
        rw [← Finset.mul_sum]

theorem yNorm_rpow_tensorFun_bandLimit_le (hb : BandLimiter κ g) {L : ℝ} (hL : L ≠ 0) {s : ℝ}
    (hs : 1 ≤ s) (f : ZMod P → 𝓢(ℝ, ℂ)) (x : ℝ) :
    yNorm s (tensorFun (fun a => bandLimit g L (f a)) x) ^ s ≤
      ∫ z, κ z * yNorm s (tensorFun f (x - z / L)) ^ s := by
  obtain ⟨B, hB⟩ := exists_norm_tensorFun_le f
  have e : tensorFun (fun a => bandLimit g L (f a)) x =
      fun y => ∫ z, (κ z : ℂ) * tensorFun f (x - z / L) y :=
    funext (tensorFun_bandLimit hb hL f x)
  rw [e]
  exact yNorm_rpow_integral_le hs hb.kernel (fun z y => tensorFun f (x - z / L) y) (B := B)
    (fun y => (continuous_tensorFun_apply f y).comp (by fun_prop)) (fun z y => hB _ _)

theorem yNorm_tensorFun_bandLimit_le_of_bound (hb : BandLimiter κ g) {L : ℝ} (hL : L ≠ 0) {u : ℝ}
    (hu : 1 ≤ u) (f : ZMod P → 𝓢(ℝ, ℂ)) {M : ℝ} (hM : ∀ w, yNorm u (tensorFun f w) ≤ M)
    (x : ℝ) : yNorm u (tensorFun (fun a => bandLimit g L (f a)) x) ≤ M := by
  have hu0 : 0 < u := by linarith
  have hM0 : 0 ≤ M := (PrimeBHT.Interface.X2.yNorm_nonneg u _).trans (hM 0)
  have h1 := yNorm_rpow_tensorFun_bandLimit_le hb hL hu f x
  have h2 : ∫ z, κ z * yNorm u (tensorFun f (x - z / L)) ^ u ≤ ∫ z, κ z * M ^ u := by
    refine integral_mono ?_ ?_ fun z => ?_
    · have hc : Continuous fun z : ℝ => yNorm u (tensorFun f (x - z / L)) ^ u :=
        ((PrimeBHT.Interface.X2.continuous_yNorm_tensorFun hu0 f).comp (by fun_prop)).rpow_const
          (fun _ => Or.inr hu0.le)
      exact hb.kernel.integrable.mul_bdd (c := M ^ u) hc.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_of_nonneg (Real.rpow_nonneg (PrimeBHT.Interface.X2.yNorm_nonneg _ _) _)]
          exact Real.rpow_le_rpow (PrimeBHT.Interface.X2.yNorm_nonneg _ _) (hM _) hu0.le)
    · exact hb.kernel.integrable.mul_const _
    · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (PrimeBHT.Interface.X2.yNorm_nonneg _ _)
        (hM _) hu0.le) (hb.kernel.nonneg z)
  rw [integral_mul_const, hb.kernel.integral_eq_one, one_mul] at h2
  exact (Real.rpow_le_rpow_iff (PrimeBHT.Interface.X2.yNorm_nonneg _ _) hM0 hu0).1 (h1.trans h2)

theorem eLpNorm_top_bandLimit_le (hb : BandLimiter κ g) {L : ℝ} (hL : L ≠ 0) {u : ℝ} (hu : 1 ≤ u)
    (f : ZMod P → 𝓢(ℝ, ℂ)) :
    eLpNorm (fun x => yNorm u (tensorFun (fun a => bandLimit g L (f a)) x)) ⊤ volume ≤
      eLpNorm (fun x => yNorm u (tensorFun f x)) ⊤ volume := by
  have hu0 : 0 < u := by linarith
  set G : ℝ → ℝ := fun w => yNorm u (tensorFun f w) with hG
  have hGc : Continuous G := PrimeBHT.Interface.X2.continuous_yNorm_tensorFun hu0 f
  have hfin : eLpNorm G ⊤ volume < ⊤ := PrimeBHT.Interface.X2.eLpNorm_top_tensorFun_lt_top hu0 f
  have hess : ∀ w, G w ≤ (eLpNorm G ⊤ volume).toReal := by
    intro w
    by_contra hlt
    rw [not_le] at hlt
    have hopen : IsOpen {z : ℝ | (eLpNorm G ⊤ volume).toReal < G z} :=
      isOpen_lt continuous_const hGc
    have hpos : 0 < volume {z : ℝ | (eLpNorm G ⊤ volume).toReal < G z} :=
      hopen.measure_pos volume ⟨w, hlt⟩
    have hae : ∀ᵐ z ∂volume, G z ≤ (eLpNorm G ⊤ volume).toReal := by
      have := ae_le_eLpNormEssSup (f := G) (μ := volume)
      rw [← eLpNorm_exponent_top hGc.aestronglyMeasurable] at this
      filter_upwards [this] with z hz
      rw [Real.enorm_eq_ofReal (PrimeBHT.Interface.X2.yNorm_nonneg _ _)] at hz
      exact (ENNReal.ofReal_le_iff_le_toReal hfin.ne).1 hz
    have h0 : volume {z : ℝ | (eLpNorm G ⊤ volume).toReal < G z} = 0 := by
      simpa [ae_iff, not_le] using hae
    exact hpos.ne' h0
  have hbd : ∀ x, yNorm u (tensorFun (fun a => bandLimit g L (f a)) x) ≤
      (eLpNorm G ⊤ volume).toReal := yNorm_tensorFun_bandLimit_le_of_bound hb hL hu f hess
  rw [eLpNorm_exponent_top (PrimeBHT.Interface.X2.continuous_yNorm_tensorFun hu0 _).aestronglyMeasurable]
  refine (eLpNormEssSup_le_of_ae_bound (C := (eLpNorm G ⊤ volume).toReal)
    (Filter.Eventually.of_forall fun x => ?_)).trans (le_of_eq (ENNReal.ofReal_toReal hfin.ne))
  rw [Real.norm_of_nonneg (PrimeBHT.Interface.X2.yNorm_nonneg _ _)]
  exact hbd x

theorem eLpNorm_two_bandLimit_le (hb : BandLimiter κ g) {L : ℝ} (hL : L ≠ 0)
    (f : ZMod P → 𝓢(ℝ, ℂ)) :
    eLpNorm (fun x => yNorm 2 (tensorFun (fun a => bandLimit g L (f a)) x)) 2 volume ≤
      eLpNorm (fun x => yNorm 2 (tensorFun f x)) 2 volume := by
  set G : ℝ → ℝ := fun w => yNorm 2 (tensorFun f w) with hG
  set G' : ℝ → ℝ := fun x => yNorm 2 (tensorFun (fun a => bandLimit g L (f a)) x) with hG'
  have hGc : Continuous G := PrimeBHT.Interface.X2.continuous_yNorm_tensorFun two_pos f
  have hG'c : Continuous G' := PrimeBHT.Interface.X2.continuous_yNorm_tensorFun two_pos _
  obtain ⟨B, hB⟩ := exists_norm_tensorFun_le f
  have hGB : ∀ w, G w ≤ B := fun w => PrimeBHT.Interface.X2.yNorm_le two_pos _ fun y => hB w y
  have hle : ∀ x, G' x ^ 2 ≤ ∫ z, κ z * G (x - z / L) ^ 2 := by
    intro x
    have := yNorm_rpow_tensorFun_bandLimit_le hb hL (s := 2) (by norm_num) f x
    simpa only [Real.rpow_two] using this
  have hl := lintegral_sq_smooth_le (L := L) hb.kernel hGc
    (fun w => PrimeBHT.Interface.X2.yNorm_nonneg _ _) hGB hle
  have e1 := eLpNorm_two_rpow_two hG'c (fun x => PrimeBHT.Interface.X2.yNorm_nonneg _ _)
  have e2 := eLpNorm_two_rpow_two hGc (fun x => PrimeBHT.Interface.X2.yNorm_nonneg _ _)
  have h3 : eLpNorm G' 2 volume ^ (2 : ℝ) ≤ eLpNorm G 2 volume ^ (2 : ℝ) := by
    rw [e1, e2]; exact hl
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).1 h3

end Tensor


/-! ### Part G: continuity of the form under band limiting, and the reduction -/

section Form

variable {P : ℕ} [NeZero P] {κ : ℝ → ℝ} {g : ℝ → ℂ}

theorem tensorFourier_bandLimit (hb : BandLimiter κ g) {L : ℝ} (hL : L ≠ 0)
    (f : ZMod P → 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    tensorFourier (fun a => bandLimit g L (f a)) ξ = g (ξ / L) • tensorFourier f ξ := by
  funext y
  simp only [tensorFourier, fourier_bandLimit hb.contDiff hb.compactSupport hL, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem integrand_bandLimit (hb : BandLimiter κ g) {L : ℝ} (hL : L ≠ 0)
    (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ) (m : ℝ → ℂ)
    (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) (ξ : ℝ × ℝ) :
    m (ξ.2 - ξ.1) * T (tensorFourier (fun a => bandLimit g L (f₁ a)) ξ.1)
        (tensorFourier (fun a => bandLimit g L (f₂ a)) ξ.2)
        (tensorFourier (fun a => bandLimit g L (f₃ a)) (ξ.1 + ξ.2)) =
      (g (ξ.1 / L) * g (ξ.2 / L) * conj (g ((ξ.1 + ξ.2) / L))) *
        (m (ξ.2 - ξ.1) * T (tensorFourier f₁ ξ.1) (tensorFourier f₂ ξ.2)
          (tensorFourier f₃ (ξ.1 + ξ.2))) := by
  rw [tensorFourier_bandLimit hb hL, tensorFourier_bandLimit hb hL, tensorFourier_bandLimit hb hL]
  simp only [map_smul, LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul]
  ring

theorem hasCompactSupport_fourier_bandLimit (hb : BandLimiter κ g) {L : ℝ} (hL : L ≠ 0)
    (φ : 𝓢(ℝ, ℂ)) : HasCompactSupport (𝓕 (⇑(bandLimit g L φ))) := by
  have e : 𝓕 (⇑(bandLimit g L φ)) = fun ξ => g (ξ / L) * 𝓕 (⇑φ) ξ :=
    funext (fourier_bandLimit hb.contDiff hb.compactSupport hL φ)
  rw [e]
  have h1 : HasCompactSupport (fun ξ : ℝ => g (ξ / L)) := by
    have e2 : (fun ξ : ℝ => g (ξ / L)) = g ∘ (Homeomorph.mulLeft₀ L⁻¹ (inv_ne_zero hL)) := by
      funext ξ; simp [div_eq_inv_mul]
    rw [e2]
    exact hb.compactSupport.comp_homeomorph _
  exact h1.mul_right

/-- Continuity of `Λ_m^Π` under band limiting: `Λ(f^{(L)}) → Λ(f)` as `L = n + 1 → ∞`. The band limiter
multiplies every Fourier coefficient by the same scalar `g(ξ/L)`, with `|g| ≤ 1`, `g(0) = 1`, `g`
continuous, so dominated convergence applies with the integrable majorant of the integrand of `Λ(f)`. -/
theorem tendsto_multiplierForm_bandLimit (hb : BandLimiter κ g)
    (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ) (m : ℝ → ℂ)
    (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ))
    (hint : Integrable (fun ξ : ℝ × ℝ => m (ξ.2 - ξ.1) *
      T (tensorFourier f₁ ξ.1) (tensorFourier f₂ ξ.2) (tensorFourier f₃ (ξ.1 + ξ.2))) volume) :
    Filter.Tendsto (fun n : ℕ => multiplierForm m T (fun a => bandLimit g ((n : ℝ) + 1) (f₁ a))
      (fun a => bandLimit g ((n : ℝ) + 1) (f₂ a)) (fun a => bandLimit g ((n : ℝ) + 1) (f₃ a)))
      Filter.atTop (nhds (multiplierForm m T f₁ f₂ f₃)) := by
  have hL : ∀ n : ℕ, ((n : ℝ) + 1) ≠ 0 := fun n => by positivity
  set I : ℝ × ℝ → ℂ := fun ξ => m (ξ.2 - ξ.1) *
      T (tensorFourier f₁ ξ.1) (tensorFourier f₂ ξ.2) (tensorFourier f₃ (ξ.1 + ξ.2)) with hI
  set φ : ℕ → ℝ × ℝ → ℂ := fun n ξ => g (ξ.1 / ((n : ℝ) + 1)) * g (ξ.2 / ((n : ℝ) + 1)) *
    conj (g ((ξ.1 + ξ.2) / ((n : ℝ) + 1))) with hφ
  have hφc : ∀ n, Continuous (φ n) := fun n => by
    have := hb.continuous
    simp only [hφ]
    fun_prop
  have hφb : ∀ n ξ, ‖φ n ξ‖ ≤ 1 := fun n ξ => by
    simp only [hφ, norm_mul, RCLike.norm_conj]
    calc ‖g (ξ.1 / ((n : ℝ) + 1))‖ * ‖g (ξ.2 / ((n : ℝ) + 1))‖ * ‖g ((ξ.1 + ξ.2) / ((n : ℝ) + 1))‖
        ≤ 1 * 1 * 1 := by
          gcongr <;> exact hb.norm_le_one _
      _ = 1 := by norm_num
  unfold multiplierForm
  refine tendsto_integral_of_dominated_convergence (fun ξ => ‖I ξ‖) ?_ hint.norm ?_ ?_
  · intro n
    have : (fun ξ : ℝ × ℝ => m (ξ.2 - ξ.1) *
        T (tensorFourier (fun a => bandLimit g ((n : ℝ) + 1) (f₁ a)) ξ.1)
          (tensorFourier (fun a => bandLimit g ((n : ℝ) + 1) (f₂ a)) ξ.2)
          (tensorFourier (fun a => bandLimit g ((n : ℝ) + 1) (f₃ a)) (ξ.1 + ξ.2))) =
        fun ξ => φ n ξ * I ξ := funext (integrand_bandLimit hb (hL n) T m f₁ f₂ f₃)
    rw [this]
    exact (hφc n).aestronglyMeasurable.mul hint.aestronglyMeasurable
  · intro n
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [integrand_bandLimit hb (hL n) T m f₁ f₂ f₃ ξ]
    show ‖φ n ξ * I ξ‖ ≤ ‖I ξ‖
    rw [norm_mul]
    calc ‖φ n ξ‖ * ‖I ξ‖ ≤ 1 * ‖I ξ‖ := mul_le_mul_of_nonneg_right (hφb n ξ) (norm_nonneg _)
      _ = ‖I ξ‖ := one_mul _
  · refine Filter.Eventually.of_forall fun ξ => ?_
    have h0 : ∀ c : ℝ, Filter.Tendsto (fun n : ℕ => g (c / ((n : ℝ) + 1))) Filter.atTop (nhds 1) := by
      intro c
      have hdiv : Filter.Tendsto (fun n : ℕ => c / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      have := (hb.continuous.tendsto 0).comp hdiv
      rwa [hb.apply_zero] at this
    have h3 : Filter.Tendsto (fun n : ℕ => φ n ξ) Filter.atTop (nhds (1 * 1 * conj 1)) :=
      ((h0 ξ.1).mul (h0 ξ.2)).mul ((Complex.continuous_conj.tendsto 1).comp (h0 (ξ.1 + ξ.2)))
    have h4 := h3.mul_const (I ξ)
    rw [map_one, one_mul, one_mul, one_mul] at h4
    refine h4.congr fun n => ?_
    exact (integrand_bandLimit hb (hL n) T m f₁ f₂ f₃ ξ).symm

end Form


/-! ### Part H: the band-limited statement and the reduction -/

/-- **`X2BandLimited`**: the second conjunct of `PrimeBHT.TransferenceAssembly.X2Statement` for tensor
Schwartz triples whose partial Fourier transforms `𝓕 (f_{i,A})` all have compact support (same
quantifiers, same constant `C = C(u, A)`; the integrability conjunct is dropped, it holds for every
tensor Schwartz triple by `PrimeBHT.Interface.X2.integrable_of_hyps`). -/
def X2BandLimited : Prop :=
  ∀ u : ℝ, 1 < u → ∀ A : ℕ → ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℕ) [NeZero P] (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
      (m : ℝ → ℂ), ContDiffOn ℝ ∞ m {0}ᶜ →
      (∀ j : ℕ, ∀ t : ℝ, t ≠ 0 → |t| ^ j * ‖iteratedDeriv j m t‖ ≤ A j) →
      ∀ CT : ℝ, (∀ F G H : ZMod P → ℂ, ‖T F G H‖ ≤ CT * yNorm 2 F * yNorm 2 G * yNorm u H) →
      ∀ f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ),
        (∀ a, HasCompactSupport (𝓕 (⇑(f₁ a)))) → (∀ a, HasCompactSupport (𝓕 (⇑(f₂ a)))) →
        (∀ a, HasCompactSupport (𝓕 (⇑(f₃ a)))) →
        ‖multiplierForm m T f₁ f₂ f₃‖ₑ ≤ ENNReal.ofReal (C * CT) *
          eLpNorm (fun x : ℝ => yNorm 2 (tensorFun f₁ x)) 2 volume *
          eLpNorm (fun x : ℝ => yNorm 2 (tensorFun f₂ x)) 2 volume *
          eLpNorm (fun x : ℝ => yNorm u (tensorFun f₃ x)) ⊤ volume

/-- **V03.** The band-limited statement implies the frozen statement `X2Statement`, with the same
constant `C`: the integrability conjunct is `integrable_of_hyps` (V01); for the inequality, approximate
`f_i` by `f_i^{(n)} = 𝓕⁻(g(·/(n+1)) 𝓕 f_i)`, whose Fourier transforms are compactly supported, use that
the three mixed norms do not increase (Jensen for the probability kernel `κ = 𝓕⁻ g`), and that
`Λ(f^{(n)}) → Λ(f)` (dominated convergence). -/
theorem x2Statement_of_bandLimited (h : X2BandLimited) :
    PrimeBHT.TransferenceAssembly.X2Statement := by
  intro u hu A
  obtain ⟨C, hC0, hC⟩ := h u hu A
  refine ⟨C, hC0, ?_⟩
  intro P _ T m hm hA CT hT f₁ f₂ f₃
  have hint := PrimeBHT.Interface.X2.integrable_of_hyps m hm A hA T f₁ f₂ f₃
  refine ⟨hint, ?_⟩
  obtain ⟨κ, g, hb⟩ := exists_bandLimiter
  have hL : ∀ n : ℕ, ((n : ℝ) + 1) ≠ 0 := fun n => by positivity
  have hbd : ∀ n : ℕ, ‖multiplierForm m T (fun a => bandLimit g ((n : ℝ) + 1) (f₁ a))
      (fun a => bandLimit g ((n : ℝ) + 1) (f₂ a)) (fun a => bandLimit g ((n : ℝ) + 1) (f₃ a))‖ₑ ≤
      ENNReal.ofReal (C * CT) *
        eLpNorm (fun x : ℝ => yNorm 2 (tensorFun f₁ x)) 2 volume *
        eLpNorm (fun x : ℝ => yNorm 2 (tensorFun f₂ x)) 2 volume *
        eLpNorm (fun x : ℝ => yNorm u (tensorFun f₃ x)) ⊤ volume := by
    intro n
    refine (hC P T m hm hA CT hT _ _ _
      (fun a => hasCompactSupport_fourier_bandLimit hb (hL n) _)
      (fun a => hasCompactSupport_fourier_bandLimit hb (hL n) _)
      (fun a => hasCompactSupport_fourier_bandLimit hb (hL n) _)).trans ?_
    gcongr
    · exact eLpNorm_two_bandLimit_le hb (hL n) f₁
    · exact eLpNorm_two_bandLimit_le hb (hL n) f₂
    · exact eLpNorm_top_bandLimit_le hb (hL n) hu.le f₃
  exact le_of_tendsto' ((continuous_enorm.tendsto _).comp
    (tendsto_multiplierForm_bandLimit hb T m f₁ f₂ f₃ hint)) hbd

end PrimeBHT.TimeFrequency.X2

end
