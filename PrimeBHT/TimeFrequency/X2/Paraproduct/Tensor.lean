module

public import PrimeBHT.TimeFrequency.X2.Classes
public import PrimeBHT.TimeFrequency.X2.Basic
public import PrimeBHT.TimeFrequency.X2.ClassKernel
public import PrimeBHT.TimeFrequency.X2.CZ.Square
public import PrimeBHT.TimeFrequency.X2.CZ.Truncated
public import Mathlib.Analysis.Distribution.FourierMultiplier

/-!
# V14 (paraproduct), tensor Schwartz data: Fourier multipliers, the trilinear form `triL`, the Parseval step

Everything the proof of `X2/Paraproduct.lean` needs about the frozen tensor Schwartz functions
`tensorFun f`, `f : ZMod P → 𝓢(ℝ, ℂ)`:

* `multSch σ`: the Fourier multiplier on Schwartz maps (`SchwartzMap.fourierMultiplierCLM`), `multSch_sum`
  (linearity in the symbol), `fourier_multSch` (`𝓕 (multSch σ g) = σ · 𝓕 g`), `coe_multSch`
  (`multSch σ g = multOp σ g`, the operator of the V08 toolbox);
* `tmS σ f`: the coefficientwise action on `TS P = ZMod P → 𝓢(ℝ, ℂ)`, `tensorMult_eq_tensorFun`
  (`tensorMult σ f = tensorFun (tmS σ f)`, so multiplier outputs are again tensor Schwartz) and
  `tmult_tensorFun` (the convolution `tmult σ` of `X2/Classes.lean` agrees with `tensorMult σ` on tensor Schwartz data);
* `triL T`: the **trilinear form** `(F, G, H) ↦ ∫ T(F(x), G(x), H(x)) dx` on `TS P` (linear, linear,
  conjugate-linear) obtained from a frozen form `T` through the coordinate expansion
  `T(F(x), G(x), H(x)) = Σ_{a,b,c} T(e_a, e_b, e_c) F_a(x) G_b(x) conj H_c(x)` (all integrals converge:
  products of Schwartz functions);
* the **Parseval step of V14 (Step 3)**: `integral_mul_mul_conj_eq_zero` (scalar: if `𝓕 h` vanishes on `|ξ| ≤ 2R`
  and `𝓕 A`, `𝓕 B` vanish for `|ξ| > R`, then `∫ h A conj B = 0`, by Fubini twice) and `triL_tmS_eq_zero`
  (vector form).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate Real ContDiff ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.X2.CZ

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-! ## Scalar Schwartz facts -/

theorem schwartz_bdd (f : 𝓢(ℝ, ℂ)) : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C :=
  ⟨‖f.toBoundedContinuousFunction‖, fun x => f.toBoundedContinuousFunction.norm_coe_le_norm x⟩

theorem norm_exp_real_mul_I' (t : ℝ) : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp_ofReal_mul_I]

theorem integrable_schwartz (A : 𝓢(ℝ, ℂ)) : Integrable (⇑A) volume := A.integrable

theorem integrable_fourier_schwartz (A : 𝓢(ℝ, ℂ)) : Integrable (𝓕 (⇑A)) volume := by
  have := (𝓕 A : 𝓢(ℝ, ℂ)).integrable (μ := volume)
  rwa [SchwartzMap.fourier_coe] at this

/-- `x ↦ A x · conj (B x)` is integrable for Schwartz `A`, `B`. -/
theorem integrable_mul_conj (A B : 𝓢(ℝ, ℂ)) : Integrable (fun x => A x * (starRingEnd ℂ) (B x)) volume := by
  obtain ⟨C, hC⟩ := schwartz_bdd B
  refine A.integrable.mul_bdd (c := C) ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (Complex.continuous_conj.comp B.continuous).aestronglyMeasurable
  · simpa using hC x

/-- `x ↦ h x · (A x · conj (B x))` is integrable for Schwartz `h`, `A`, `B`. -/
theorem integrable_mul_mul_conj (h A B : 𝓢(ℝ, ℂ)) :
    Integrable (fun x => h x * (A x * (starRingEnd ℂ) (B x))) volume := by
  obtain ⟨C, hC⟩ := schwartz_bdd A
  obtain ⟨D, hD⟩ := schwartz_bdd B
  refine h.integrable.mul_bdd (c := C * D) ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (A.continuous.mul (Complex.continuous_conj.comp B.continuous)).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC x) (hD x) (norm_nonneg _) ((norm_nonneg _).trans (hC x))

theorem fourierInv_schwartz_apply (A : 𝓢(ℝ, ℂ)) (x : ℝ) :
    A x = ∫ ζ, Complex.exp (↑(2 * π * ζ * x) * Complex.I) * 𝓕 (⇑A) ζ := by
  have h : 𝓕⁻ (𝓕 (⇑A)) x = A x := by
    have h1 : 𝓕⁻ (𝓕 A : 𝓢(ℝ, ℂ)) = A := FourierTransform.fourierInv_fourier_eq A
    rw [← SchwartzMap.fourier_coe, ← SchwartzMap.fourierInv_coe, h1]
  rw [← h, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]
  congr 3
  push_cast
  ring

/-- The Fourier transform of a product: `𝓕 (A · conj B) (ξ) = ∫ 𝓕 A (ζ) conj (𝓕 B (ζ - ξ)) dζ`. -/
theorem fourier_mul_conj_apply (A B : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (fun x => A x * (starRingEnd ℂ) (B x)) ξ = ∫ ζ, 𝓕 (⇑A) ζ * (starRingEnd ℂ) (𝓕 (⇑B) (ζ - ξ)) := by
  set F : ℝ → ℝ → ℂ := fun x ζ => Complex.exp (↑(-2 * π * x * ξ) * Complex.I) *
    (Complex.exp (↑(2 * π * ζ * x) * Complex.I) * 𝓕 (⇑A) ζ) * (starRingEnd ℂ) (B x) with hF
  have hAf := integrable_fourier_schwartz A
  have hBf := integrable_schwartz B
  have hint : Integrable (Function.uncurry fun (ζ x : ℝ) => F x ζ) (volume.prod volume) := by
    refine (Integrable.mul_prod hAf.norm hBf.norm).mono' ?_ ?_
    · have hc : Continuous (fun p : ℝ × ℝ =>
          Complex.exp (↑(-2 * π * p.2 * ξ) * Complex.I) * Complex.exp (↑(2 * π * p.1 * p.2) * Complex.I)) := by
        fun_prop
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => 𝓕 (⇑A) p.1) (volume.prod volume) := hAf.1.comp_fst
      have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => (starRingEnd ℂ) (B p.2)) (volume.prod volume) :=
        (Complex.continuous_conj.comp B.continuous).aestronglyMeasurable.comp_snd
      have e : (Function.uncurry fun (ζ x : ℝ) => F x ζ) = fun p : ℝ × ℝ =>
          (Complex.exp (↑(-2 * π * p.2 * ξ) * Complex.I) * Complex.exp (↑(2 * π * p.1 * p.2) * Complex.I)) *
            𝓕 (⇑A) p.1 * (starRingEnd ℂ) (B p.2) := by
        ext p; simp only [hF, Function.uncurry]; ring
      rw [e]
      exact (hc.aestronglyMeasurable.mul h1).mul h2
    · refine Filter.Eventually.of_forall fun p => ?_
      simp only [Function.uncurry, hF, norm_mul, norm_exp_real_mul_I', one_mul, Complex.norm_conj]
      exact le_rfl
  have h1 : ∀ x : ℝ, Complex.exp (↑(-2 * π * x * ξ) * Complex.I) * (A x * (starRingEnd ℂ) (B x)) =
      ∫ ζ, F x ζ := by
    intro x
    simp only [hF]
    have := fourierInv_schwartz_apply A x
    rw [this, ← integral_mul_const, ← integral_const_mul]
    congr 1; ext ζ; ring
  have h2 : ∀ ζ : ℝ, ∫ x, F x ζ = 𝓕 (⇑A) ζ * (starRingEnd ℂ) (𝓕 (⇑B) (ζ - ξ)) := by
    intro ζ
    rw [Real.fourier_real_eq_integral_exp_smul (⇑B) (ζ - ξ), ← integral_conj, ← integral_const_mul]
    congr 1; ext x
    simp only [hF, smul_eq_mul, map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
    rw [← mul_assoc, ← Complex.exp_add, ← mul_assoc]
    have e : (↑(-2 * π * x * ξ) * Complex.I + ↑(2 * π * ζ * x) * Complex.I : ℂ) =
        ↑(-2 * π * x * (ζ - ξ)) * -Complex.I := by push_cast; ring
    rw [e]; ring
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul, h1]
  rw [integral_integral_swap hint.swap]
  simp only [h2]

theorem fourier_mul_conj_eq_zero (A B : 𝓢(ℝ, ℂ)) {R : ℝ} (hA : ∀ ξ, R < |ξ| → 𝓕 (⇑A) ξ = 0)
    (hB : ∀ ξ, R < |ξ| → 𝓕 (⇑B) ξ = 0) {ξ : ℝ} (hξ : 2 * R < |ξ|) :
    𝓕 (fun x => A x * (starRingEnd ℂ) (B x)) ξ = 0 := by
  rw [fourier_mul_conj_apply]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun ζ => ?_)
  by_cases hζ : R < |ζ|
  · simp [hA ζ hζ]
  · push Not at hζ
    have h1 : R < |ζ - ξ| := by
      have := abs_sub_abs_le_abs_sub ξ ζ
      rw [abs_sub_comm] at this
      linarith
    simp [hB _ h1]

/-- **The Parseval step (scalar)**: if `𝓕 h` vanishes on `{|ξ| ≤ 2R}` and `𝓕 A`, `𝓕 B` vanish on `{|ξ| > R}`, then
`∫ h A conj B = 0` (the Fourier support of `A conj B` lies in `{|ξ| ≤ 2R}`). -/
theorem integral_mul_mul_conj_eq_zero (h A B : 𝓢(ℝ, ℂ)) {R : ℝ}
    (hh : ∀ ξ, |ξ| ≤ 2 * R → 𝓕 (⇑h) ξ = 0)
    (hA : ∀ ξ, R < |ξ| → 𝓕 (⇑A) ξ = 0) (hB : ∀ ξ, R < |ξ| → 𝓕 (⇑B) ξ = 0) :
    ∫ x, h x * (A x * (starRingEnd ℂ) (B x)) = 0 := by
  set H₁ : 𝓢(ℝ, ℂ) := 𝓕⁻ h with hH₁
  have hw := integrable_mul_conj A B
  have hh1 : (⇑h : ℝ → ℂ) = 𝓕 (⇑H₁) := by
    have : 𝓕 H₁ = h := FourierTransform.fourier_fourierInv_eq h
    rw [← SchwartzMap.fourier_coe, this]
  have key : ∫ ξ, 𝓕 (⇑H₁) ξ * (A ξ * (starRingEnd ℂ) (B ξ)) =
      ∫ x, H₁ x * 𝓕 (fun x => A x * (starRingEnd ℂ) (B x)) x := by
    simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner H₁.integrable hw
  have e1 : ∫ x, h x * (A x * (starRingEnd ℂ) (B x)) =
      ∫ ξ, 𝓕 (⇑H₁) ξ * (A ξ * (starRingEnd ℂ) (B ξ)) := by
    rw [hh1]
  rw [e1, key]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : 2 * R < |x|
  · simp [fourier_mul_conj_eq_zero A B hA hB hx]
  · push Not at hx
    have : H₁ x = 0 := by
      have e : H₁ x = 𝓕 (⇑h) (-x) := by
        have := congrFun (SchwartzMap.fourierInv_coe h) x
        rw [hH₁, this, Real.fourierInv_eq_fourier_neg]
      rw [e, hh _ (by rwa [abs_neg])]
    simp [this]

/-! ## Fourier multipliers on Schwartz maps -/

/-- The Fourier multiplier `g ↦ 𝓕⁻(σ 𝓕 g)` on Schwartz maps. -/
def multSch (σ : ℝ → ℂ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.fourierMultiplierCLM ℂ σ

theorem coe_multSch {σ : ℝ → ℂ} (hσ : σ.HasTemperateGrowth) (g : 𝓢(ℝ, ℂ)) :
    ⇑(multSch σ g) = multOp σ ⇑g := by
  unfold multSch multOp
  rw [SchwartzMap.fourierMultiplierCLM_apply, SchwartzMap.fourierInv_coe]
  congr 1
  ext ξ
  rw [SchwartzMap.smulLeftCLM_apply_apply hσ, smul_eq_mul, SchwartzMap.fourier_coe]

theorem fourier_multSch {σ : ℝ → ℂ} (hσ : σ.HasTemperateGrowth) (g : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (⇑(multSch σ g)) ξ = σ ξ * 𝓕 (⇑g) ξ := by
  unfold multSch
  rw [← SchwartzMap.fourier_coe, SchwartzMap.fourierMultiplierCLM_apply,
    FourierTransform.fourier_fourierInv_eq, SchwartzMap.smulLeftCLM_apply_apply hσ, smul_eq_mul,
    SchwartzMap.fourier_coe]

theorem multSch_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (n : ι → ℝ → ℂ)
    (hn : ∀ i ∈ s, (n i).HasTemperateGrowth) (g : 𝓢(ℝ, ℂ)) :
    multSch (fun ξ => ∑ i ∈ s, c i * n i ξ) g = ∑ i ∈ s, c i • multSch (n i) g := by
  unfold multSch
  have hcn : ∀ i ∈ s, (c i • n i).HasTemperateGrowth := fun i hi =>
    (Function.HasTemperateGrowth.const (c i)).smul (hn i hi)
  have h1 : (fun ξ => ∑ i ∈ s, c i * n i ξ) = fun ξ => ∑ i ∈ s, (c i • n i) ξ := by
    ext ξ; simp
  rw [h1, SchwartzMap.fourierMultiplierCLM_sum (F := ℂ) (g := fun i => c i • n i) hcn,
    sum_apply]
  exact Finset.sum_congr rfl fun i hi => by rw [SchwartzMap.fourierMultiplierCLM_smul (hn i hi)]; rfl

theorem multSch_one (g : 𝓢(ℝ, ℂ)) : multSch (fun _ => 1) g = g := by
  unfold multSch
  rw [SchwartzMap.fourierMultiplierCLM_const]
  simp

/-! ## The trilinear form on tensor Schwartz families -/

section Vector

variable {P : ℕ} [NeZero P]

/-- Coefficient families of tensor Schwartz functions: `f ↦ tensorFun f`. -/
abbrev TS (P : ℕ) : Type := ZMod P → 𝓢(ℝ, ℂ)

/-- The coefficientwise Fourier multiplier on `TS P`. -/
def tmS (σ : ℝ → ℂ) (f : TS P) : TS P := fun A => multSch σ (f A)

theorem tensorMult_eq_tensorFun {σ : ℝ → ℂ} (hσ : σ.HasTemperateGrowth) (f : TS P) :
    tensorMult σ f = tensorFun (tmS σ f) := by
  ext x y
  simp only [tensorMult, tensorFun, tmS]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [coe_multSch hσ]

omit [NeZero P] in
theorem tmS_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (n : ι → ℝ → ℂ)
    (hn : ∀ i ∈ s, (n i).HasTemperateGrowth) (f : TS P) :
    tmS (fun ξ => ∑ i ∈ s, c i * n i ξ) f = ∑ i ∈ s, c i • tmS (n i) f := by
  funext A
  have h : (∑ i ∈ s, c i • tmS (n i) f) A = ∑ i ∈ s, c i • tmS (n i) f A := by
    simp [Finset.sum_apply]
  rw [h]
  exact multSch_sum s c n hn (f A)

omit [NeZero P] in
theorem tmS_one (f : TS P) : tmS (fun _ => 1) f = f := by
  funext A
  exact multSch_one (f A)

theorem tensorFun_eq_sum (f : TS P) (x : ℝ) : tensorFun f x = ∑ A, f A x • yChar A := by
  ext y
  simp [tensorFun, yChar, Finset.sum_apply]

/-- The coordinate expansion of a frozen form on tensor Schwartz arguments. -/
theorem T_expand (T : Form P) (u v w : ZMod P → ℂ) :
    T (∑ a, u a • yChar a) (∑ b, v b • yChar b) (∑ c, w c • yChar c) =
      ∑ c, ∑ b, ∑ a, T (yChar a) (yChar b) (yChar c) * (u a * (v b * (starRingEnd ℂ) (w c))) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, map_smulₛₗ,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

/-- The integrand `x ↦ T(F(x), G(x), H(x))`. -/
def Tfun (T : Form P) (F G H : TS P) (x : ℝ) : ℂ :=
  T (tensorFun F x) (tensorFun G x) (tensorFun H x)

theorem Tfun_eq_sum (T : Form P) (F G H : TS P) (x : ℝ) :
    Tfun T F G H x = ∑ c, ∑ b, ∑ a, T (yChar a) (yChar b) (yChar c) *
      (F a x * (G b x * (starRingEnd ℂ) (H c x))) := by
  unfold Tfun
  rw [tensorFun_eq_sum, tensorFun_eq_sum, tensorFun_eq_sum, T_expand]

theorem integrable_Tfun (T : Form P) (F G H : TS P) : Integrable (Tfun T F G H) volume := by
  have : Tfun T F G H = fun x => ∑ c, ∑ b, ∑ a, T (yChar a) (yChar b) (yChar c) *
      (F a x * (G b x * (starRingEnd ℂ) (H c x))) := funext (Tfun_eq_sum T F G H)
  rw [this]
  refine integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun b _ =>
    integrable_finsetSum _ fun a _ => ?_
  exact (integrable_mul_mul_conj (F a) (G b) (H c)).const_mul _

theorem integral_Tfun (T : Form P) (F G H : TS P) :
    ∫ x, Tfun T F G H x = ∑ c, ∑ b, ∑ a, T (yChar a) (yChar b) (yChar c) *
      ∫ x, F a x * (G b x * (starRingEnd ℂ) (H c x)) := by
  simp_rw [Tfun_eq_sum]
  rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun b _ => integrable_finsetSum _ fun a _ =>
    (integrable_mul_mul_conj (F a) (G b) (H c)).const_mul _]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_finsetSum _ fun b _ => integrable_finsetSum _ fun a _ =>
    (integrable_mul_mul_conj (F a) (G b) (H c)).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_finsetSum _ fun a _ => (integrable_mul_mul_conj (F a) (G b) (H c)).const_mul _]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_const_mul]

theorem tensorFun_add (f g : TS P) (x : ℝ) : tensorFun (f + g) x = tensorFun f x + tensorFun g x := by
  ext y
  simp [tensorFun, add_mul, Finset.sum_add_distrib]

theorem tensorFun_smul (c : ℂ) (f : TS P) (x : ℝ) : tensorFun (c • f) x = c • tensorFun f x := by
  ext y
  simp [tensorFun, Finset.mul_sum, mul_assoc]

/-- The trilinear form `(F, G, H) ↦ ∫ T(F(x), G(x), H(x)) dx` on tensor Schwartz families
(linear, linear, conjugate-linear). -/
def triL (T : Form P) : TS P →ₗ[ℂ] TS P →ₗ[ℂ] TS P →ₛₗ[starRingEnd ℂ] ℂ where
  toFun F :=
    { toFun := fun G =>
        { toFun := fun H => ∫ x, Tfun T F G H x
          map_add' := fun H H' => by
            rw [← integral_add (integrable_Tfun T F G H) (integrable_Tfun T F G H')]
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            simp [Tfun, tensorFun_add]
          map_smul' := fun c H => by
            simp only [smul_eq_mul]
            rw [← integral_const_mul]
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            simp [Tfun, tensorFun_smul] }
      map_add' := fun G G' => by
        refine LinearMap.ext fun H => ?_
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
        rw [← integral_add (integrable_Tfun T F G H) (integrable_Tfun T F G' H)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp [Tfun, tensorFun_add]
      map_smul' := fun c G => by
        refine LinearMap.ext fun H => ?_
        simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp [Tfun, tensorFun_smul] }
  map_add' := fun F F' => by
    refine LinearMap.ext fun G => LinearMap.ext fun H => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [← integral_add (integrable_Tfun T F G H) (integrable_Tfun T F' G H)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [Tfun, tensorFun_add]
  map_smul' := fun c F => by
    refine LinearMap.ext fun G => LinearMap.ext fun H => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [Tfun, tensorFun_smul]

theorem triL_apply (T : Form P) (F G H : TS P) : triL T F G H = ∫ x, Tfun T F G H x := rfl

/-- **The Parseval step (vector form)**: if the symbol `s` vanishes on `{|ξ| ≤ 2R}` and the symbols `a`, `b`
vanish on `{|ξ| > R}`, then `∫ T(T_s f₀, T_a f₁, T_b f₂) = 0`. -/
theorem triL_tmS_eq_zero (T : Form P) {s a b : ℝ → ℂ} (hs : s.HasTemperateGrowth)
    (ha : a.HasTemperateGrowth) (hb : b.HasTemperateGrowth) {R : ℝ}
    (hsR : ∀ ξ, |ξ| ≤ 2 * R → s ξ = 0) (haR : ∀ ξ, R < |ξ| → a ξ = 0) (hbR : ∀ ξ, R < |ξ| → b ξ = 0)
    (f₀ f₁ f₂ : TS P) : triL T (tmS s f₀) (tmS a f₁) (tmS b f₂) = 0 := by
  rw [triL_apply, integral_Tfun]
  refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun b' _ => Finset.sum_eq_zero fun a' _ => ?_
  rw [integral_mul_mul_conj_eq_zero (tmS s f₀ a') (tmS a f₁ b') (tmS b f₂ c) (R := R), mul_zero]
  · intro ξ hξ; simp only [tmS, fourier_multSch hs, hsR ξ hξ, zero_mul]
  · intro ξ hξ; simp only [tmS, fourier_multSch ha, haR ξ hξ, zero_mul]
  · intro ξ hξ; simp only [tmS, fourier_multSch hb, hbR ξ hξ, zero_mul]

/-- The size bound: `‖∫ T(F, G, H)‖ ≤ ∫ CT ‖F‖₂ ‖G‖₂ ‖H‖_u` in `[0, ∞]`. -/
theorem enorm_triL_le (T : Form P) {u CT : ℝ} (hT : FormBound u T CT) (F G H : TS P) :
    ‖triL T F G H‖ₑ ≤ ∫⁻ x, ENNReal.ofReal (CT * yNorm 2 (tensorFun F x) * yNorm 2 (tensorFun G x) *
      yNorm u (tensorFun H x)) := by
  rw [triL_apply]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hT _ _ _)

/-- On tensor Schwartz data the convolution `tmult σ` of `X2/Classes.lean` is `tensorMult σ` of the V08 toolbox
(for a smooth compactly supported symbol `σ`). -/
theorem tmult_tensorFun {σ : ℝ → ℂ} (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ) (f : TS P) :
    tmult σ (tensorFun f) = tensorMult σ f := by
  have hint : Integrable σ volume := hσ.continuous.integrable_of_hasCompactSupport hc
  have hker : Continuous (𝓕⁻ σ) := continuous_fourierInv_of_integrable' hint
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ w, ‖𝓕⁻ σ w‖ ≤ M :=
    ⟨∫ ξ, ‖σ ξ‖, fun w => by
      rw [Real.fourierInv_eq_fourier_neg]; exact Real.norm_fourier_le_integral_norm σ (-w)⟩
  ext x y
  simp only [tmult, tensorFun, tensorMult]
  have hA : ∀ A : ZMod P, Integrable (fun z => 𝓕⁻ σ (x - z) * (f A z * ZMod.stdAddChar (A * y))) volume := by
    intro A
    refine ((f A).integrable.mul_const _).bdd_mul (c := M) ?_ (Filter.Eventually.of_forall fun z => hM _)
    exact (hker.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun A _ => hA A]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [multOp_eq_integral_fourierInv hint (f A).integrable x, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  ring

end Vector

end PrimeBHT.TimeFrequency.X2
