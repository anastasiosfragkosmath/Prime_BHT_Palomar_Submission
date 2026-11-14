module

public import PrimeBHT.TimeFrequency.X2.CZ.MixedNorm
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# V08, base case of the multiplier theory (phase 1, file 3)

For a bounded measurable symbol `σ` (`IsBoundedSymbol B σ`, in particular `σ` in the Mikhlin class)
`(T_σ ⊗ Id)` acts fibrewise in `y` on the tensor Schwartz functions, so the vector-valued bound on
`L^s(ℝ; L^s(Y_P))` is `P⁻¹ Σ_y` of the scalar `L^s(ℝ)` bound with the same constant (Fubini).

* `eLpNorm_fourierInv_eq_of_integrable`: **Plancherel for `L¹ ∩ L²`**: the inverse Fourier transform given by
  the `L¹` integral preserves the `L²` norm.  (Mathlib has Plancherel for Schwartz functions and for the
  abstract `L²` Fourier transform, but not the identification of the two on `L¹ ∩ L²`; proved here by
  testing against smooth compactly supported functions and the Fourier multiplication formula.)
* `eLpNorm_multOp_two_le`: scalar `‖T_σ g‖_{L²} ≤ B ‖g‖_{L²}` (Plancherel), `g` Schwartz.
* `mixedENorm_tensorMult_diag_le_of_scalar`: the Fubini step: if the scalar bound holds at exponent `s`
  with constant `K`, then `‖(T_σ ⊗ Id) F‖_{L^s(ℝ; L^s(Y))} ≤ K ‖F‖_{L^s(ℝ; L^s(Y))}`, for every `P`.
* `vectorMikhlinStrong_two_two` (**unconditional**, `X = H`, `q = s = 2`, constant `1`),
  `vectorMikhlinStrong_diag_of_scalar` (conditional on `ScalarMikhlinStrong a₀ s C`, so named `…_of_scalar`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate Real ComplexInnerProductSpace

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

open PrimeBHT.Statements

/-! ## Plancherel for `L¹ ∩ L²` -/

theorem integral_sesq_fourier_eq_of_integrable (Φ : 𝓢(ℝ, ℂ)) (h : ℝ → ℂ) (h1 : Integrable h volume) :
    ∫ ξ, h ξ * conj (𝓕 (⇑Φ) ξ) = ∫ x, 𝓕⁻ h x * conj (Φ x) := by
  have := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip (innerSL ℂ : ℂ →L⋆[ℂ] ℂ →L[ℂ] ℂ)
    (e := Real.fourierChar) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner Φ.integrable h1
  simp at this
  exact this

/-- the complex conjugate of a Schwartz function -/
noncomputable def conjSchwartz (Ψ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) (E := ℝ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) Ψ

theorem conjSchwartz_apply (Ψ : 𝓢(ℝ, ℂ)) (x : ℝ) : conjSchwartz Ψ x = conj (Ψ x) := rfl

theorem integral_mul_lp_fourierInv (h : ℝ → ℂ) (h1 : Integrable h volume) (h2 : MemLp h 2 volume)
    (Ψ : 𝓢(ℝ, ℂ)) :
    ∫ x, Ψ x * ((𝓕⁻ (h2.toLp h : Lp ℂ 2 volume) : Lp ℂ 2 volume) : ℝ → ℂ) x =
      ∫ x, Ψ x * 𝓕⁻ h x := by
  set Φ := conjSchwartz Ψ with hΦ
  set h' : Lp ℂ 2 volume := h2.toLp h with hh'
  set v : Lp ℂ 2 volume := 𝓕⁻ h' with hv
  -- L² side
  have e1 : inner ℂ (Φ.toLp 2 volume) v = ∫ x, Ψ x * v x := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Φ.coeFn_toLp 2 volume] with x hx
    rw [hx, conjSchwartz_apply]
    simp [mul_comm]
  have e2 : inner ℂ (Φ.toLp 2 volume) v = inner ℂ ((𝓕 Φ : 𝓢(ℝ, ℂ)).toLp 2 volume) h' := by
    rw [← Lp.inner_fourier_eq, SchwartzMap.toLp_fourier_eq]
    rw [hv, FourierTransform.fourier_fourierInv_eq]
  have e3 : inner ℂ ((𝓕 Φ : 𝓢(ℝ, ℂ)).toLp 2 volume) h' = ∫ ξ, h ξ * conj (𝓕 (⇑Φ) ξ) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(𝓕 Φ : 𝓢(ℝ, ℂ)).coeFn_toLp 2 volume, hh' ▸ h2.coeFn_toLp] with x hx hx'
    rw [hx, hx']
    simp [SchwartzMap.fourier_coe]
  have e4 := integral_sesq_fourier_eq_of_integrable Φ h h1
  rw [← e1, e2, e3, e4]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [hΦ, conjSchwartz_apply, mul_comm]

theorem continuous_fourierInv_of_integrable (h : ℝ → ℂ) (h1 : Integrable h volume) :
    Continuous (𝓕⁻ h) := by
  have hc : Continuous (𝓕 h) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner h1
  have : 𝓕⁻ h = fun w => 𝓕 h (-w) := by
    ext w; exact Real.fourierInv_eq_fourier_neg h w
  rw [this]
  exact hc.comp continuous_neg

/-- Plancherel for `L¹ ∩ L²`: the inverse Fourier transform (defined by the `L¹` integral) preserves the
`L²` norm. -/
theorem eLpNorm_fourierInv_eq_of_integrable (h : ℝ → ℂ) (h1 : Integrable h volume)
    (h2 : MemLp h 2 volume) : eLpNorm (𝓕⁻ h) 2 volume = eLpNorm h 2 volume := by
  set h' : Lp ℂ 2 volume := h2.toLp h with hh'
  set v : Lp ℂ 2 volume := 𝓕⁻ h' with hv
  have hu := continuous_fourierInv_of_integrable h h1
  have hae : (v : ℝ → ℂ) =ᵐ[volume] 𝓕⁻ h := by
    refine ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp v).locallyIntegrable (by norm_num))
      hu.locallyIntegrable ?_
    intro ψ hψ hψs
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : 𝓢(ℝ, ℂ), ∀ x, Ψ x = (ψ x : ℂ) :=
      ⟨(show HasCompactSupport (fun x => (ψ x : ℂ)) from
        hψs.comp_left Complex.ofReal_zero).toSchwartzMap
        (Complex.ofRealCLM.contDiff.comp hψ), fun x => rfl⟩
    have key := integral_mul_lp_fourierInv h h1 h2 Ψ
    simp only [hΨ] at key
    simpa [Complex.real_smul] using key
  have hn : ‖v‖ = ‖h'‖ := (Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map h'
  rw [← eLpNorm_congr_ae hae, ← Lp.enorm_def, ← ofReal_norm, hn, ofReal_norm, Lp.enorm_def]
  exact eLpNorm_congr_ae h2.coeFn_toLp

/-! ## The scalar `L²` bound -/

/-- A Mikhlin symbol is a bounded measurable symbol with the same constant. -/
theorem IsMikhlin.isBoundedSymbol {a₀ : ℕ} {B : ℝ} {σ : ℝ → ℂ} (hσ : IsMikhlin a₀ B σ) :
    IsBoundedSymbol B σ := by
  refine ⟨?_, ?_⟩
  · have hc : ContinuousOn σ {0}ᶜ := hσ.1.continuousOn
    have h1 : AEStronglyMeasurable σ (volume.restrict ({0}ᶜ : Set ℝ)) :=
      hc.aestronglyMeasurable (measurableSet_singleton 0).compl
    have h2 : AEStronglyMeasurable σ (volume.restrict ({0} : Set ℝ)) := by
      rw [Measure.restrict_eq_zero.2 (measure_singleton (0 : ℝ))]
      exact aestronglyMeasurable_zero_measure σ
    have h3 := aestronglyMeasurable_union_iff.2 ⟨h1, h2⟩
    rwa [Set.compl_union_self, Measure.restrict_univ] at h3
  · have : ∀ᵐ ξ ∂(volume : Measure ℝ), ξ ≠ 0 := by simp [ae_iff]
    filter_upwards [this] with ξ hξ
    have h := hσ.2 0 (Nat.zero_le _) ξ hξ
    simpa [iteratedDeriv_zero] using h

/-- `T_σ g` is continuous for `σ` a bounded measurable symbol and `g` Schwartz. -/
theorem IsBoundedSymbol.continuous_multOp {B : ℝ} {σ : ℝ → ℂ} (hσ : IsBoundedSymbol B σ)
    (g : 𝓢(ℝ, ℂ)) : Continuous (multOp σ (⇑g)) :=
  continuous_fourierInv_of_integrable _ (hσ.integrable_mul_fourier g)

/-! ## The Fubini step -/

section Fubini

variable {P : ℕ} [NeZero P]

/-- The fibre of `tensorFun f` over `y` as a Schwartz function. -/
def fibreSchwartz (f : ZMod P → 𝓢(ℝ, ℂ)) (y : ZMod P) : 𝓢(ℝ, ℂ) :=
  ∑ A : ZMod P, (ZMod.stdAddChar (A * y) : ℂ) • f A

theorem fibreSchwartz_apply (f : ZMod P → 𝓢(ℝ, ℂ)) (y : ZMod P) (x : ℝ) :
    fibreSchwartz f y x = tensorFun f x y := by
  have := congrFun (tensorFun_fibre_eq_coe f y) x
  simpa [fibreSchwartz] using this.symm

theorem tensorMult_eq_multOp_fibreSchwartz {B : ℝ} {σ : ℝ → ℂ} (hσ : IsBoundedSymbol B σ)
    (f : ZMod P → 𝓢(ℝ, ℂ)) (x : ℝ) (y : ZMod P) :
    tensorMult σ f x y = multOp σ (⇑(fibreSchwartz f y)) x := by
  rw [tensorMult_eq_multOp_fibre hσ]
  congr 1
  ext x'
  exact (fibreSchwartz_apply f y x').symm

end Fubini

/-! ## Sanity check of the definitions and the base cases -/

end PrimeBHT.TimeFrequency.X2.CZ
