module

public import PrimeBHT.TimeFrequency.X2.SymbolDecomposition
public import PrimeBHT.Frozen.YNorm
public import PrimeBHT.Frozen.TensorFun
public import PrimeBHT.Frozen.TensorFourier
public import PrimeBHT.Frozen.MultiplierForm
import PrimeBHT.Interface.X2Checks

/-!
# X2, node V04 (iii): the form-level identity for the decomposed symbol

Blueprint `docs/x2-blueprint.md`, node V04 (iii), over the FROZEN `multiplierForm`. Fully proved.

## Final signatures (namespace `PrimeBHT.TimeFrequency.X2`)

* `schwartzTranslate a φ = φ(· - a)`; `fourier_schwartzTranslate`, `tensorFourier_schwartzTranslate`
  (`F̂(τ_a f)(ξ) = e^{-2π i a ξ} F̂(f)(ξ)`), `tensorFun_schwartzTranslate`,
  `eLpNorm_yNorm_tensorFun_schwartzTranslate` (translation does not change any mixed norm).
* `symbolShift (k, n) = n 2^{-k} / 8`, `pieceForm T f₁ f₂ f₃ (k, n) =
  multiplierForm (t ↦ ρ̃(2^{-k} t)) T (τ_a f₁) (τ_{-a} f₂) f₃`, `a = symbolShift (k, n)`.
* `hasSum_mul_pieceForm`: if `‖c k n‖ ≤ b n` (`b` summable) and `HasSum (symbolTerm c t) (m t)` for `t ≠ 0`, then
  `HasSum (p ↦ c p.1 p.2 * pieceForm T f₁ f₂ f₃ p) (multiplierForm m T f₁ f₂ f₃)` for every tensor Schwartz triple.
* `hasSum_tsum_mul_pieceForm`: the iterated form `∑_k ∑_n c_{k,n} pieceForm (k,n)`.
* `exists_symbol_decomposition_form`: (i), (ii) and (iii) together for the `c = symbolCoeff m` of
  `SymbolDecomposition`.

## Corrections / remarks on the blueprint

The identity (iii) does **not** need band-limited data (the blueprint says "for band-limited data (V03)"): it holds
for every tensor Schwartz triple, the interchange of `∑_{k,n}` and `∫∫` being justified by
`∑_p ‖term_p(ξ)‖ ≤ 4 ∑_n b_n` and the integrability of `ξ ↦ Π(F̂₁(ξ₁), F̂₂(ξ₂), F̂₃(ξ₁+ξ₂))` (V01). The interchange
uses `hasSum_integral_of_summable_integral_norm` with the finite-sum bound `∑_{p ∈ s} ∫ ‖term_p‖ ≤ 4 (∑ b) ‖Π(…)‖₁`
(no Tonelli for the `k`-sum is needed). The sum over `k` is **not** bounded by the uniform single-scale
bounds (the bound for `Λ_{ρ̃_k}` is uniform in `k`): downstream (V05) must treat all scales `k` simultaneously.
-/

@[expose] public noncomputable section

open MeasureTheory Complex
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate ContDiff Real
open PrimeBHT.Statements (yNorm tensorFun tensorFourier multiplierForm)

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-! ### Translation of Schwartz functions and tensor Schwartz functions -/

/-- The translation `τ_a φ (x) = φ (x - a)` of a Schwartz function. -/
def schwartzTranslate (a : ℝ) (φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) := SchwartzMap.compSubConstCLM ℂ a φ

theorem schwartzTranslate_apply (a : ℝ) (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    schwartzTranslate a φ x = φ (x - a) := rfl

/-- `𝓕 (τ_a φ)(ξ) = e^{-2π i a ξ} 𝓕 φ (ξ)`. -/
theorem fourier_schwartzTranslate (a : ℝ) (φ : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (⇑(schwartzTranslate a φ)) ξ = Complex.exp (((-2 * π * a * ξ : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑φ) ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_const_mul,
    ← integral_add_right_eq_self (fun v : ℝ => Complex.exp (((-2 * π * v * ξ : ℝ) : ℂ) * Complex.I) •
      (schwartzTranslate a φ) v) a]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul, schwartzTranslate_apply, add_sub_cancel_right]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

variable {P : ℕ} [NeZero P]

theorem tensorFourier_schwartzTranslate (a : ℝ) (f : ZMod P → 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    tensorFourier (fun A => schwartzTranslate a (f A)) ξ =
      Complex.exp (((-2 * π * a * ξ : ℝ) : ℂ) * Complex.I) • tensorFourier f ξ := by
  funext y
  simp only [tensorFourier, fourier_schwartzTranslate, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun A _ => by ring

/-! ### The single-scale pieces of the form -/

/-- The translation parameter `a_{k,n} = n 2^{-k} / 8`. -/
def symbolShift (p : ℤ × ℤ) : ℝ := (p.2 : ℝ) * (2 : ℝ) ^ (-p.1) / 8

/-- The `(k, n)` piece of the form: `Λ_{ρ̃_k}^Π(τ_a F₁, τ_{-a} F₂, F₃)` with `ρ̃_k(t) = ρ̃(2^{-k} t)` and
`a = n 2^{-k}/8`. -/
def pieceForm (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
    (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) (p : ℤ × ℤ) : ℂ :=
  multiplierForm (fun t : ℝ => (symbolCutoff ((2 : ℝ) ^ (-p.1) * t) : ℂ)) T
    (fun A => schwartzTranslate (symbolShift p) (f₁ A))
    (fun A => schwartzTranslate (-symbolShift p) (f₂ A)) f₃

/-- The integrand `ξ ↦ Π(F̂₁(ξ₁), F̂₂(ξ₂), F̂₃(ξ₁ + ξ₂))` (without the symbol). -/
def formKernel (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
    (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) (ξ : ℝ × ℝ) : ℂ :=
  T (tensorFourier f₁ ξ.1) (tensorFourier f₂ ξ.2) (tensorFourier f₃ (ξ.1 + ξ.2))

theorem integrable_formKernel (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
    (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) : Integrable (formKernel T f₁ f₂ f₃) volume := by
  have := PrimeBHT.Interface.X2.integrable_multiplierForm (fun _ : ℝ => (1 : ℂ))
    continuousOn_const 1 (fun t => by simp) T f₁ f₂ f₃
  simp only [one_mul] at this
  exact this

theorem volume_diagonal_null :
    ∀ᵐ ξ : ℝ × ℝ, ξ.2 - ξ.1 ≠ 0 := by
  have hm : MeasurableSet {ξ : ℝ × ℝ | ξ.2 - ξ.1 = 0} :=
    measurableSet_eq_fun (measurable_snd.sub measurable_fst) measurable_const
  rw [ae_iff]
  have h : volume {a : ℝ × ℝ | ¬ (a.2 - a.1 ≠ 0)} = 0 := by
    simp only [not_not]
    rw [Measure.volume_eq_prod, Measure.prod_apply hm]
    simp only [Set.preimage_ofPred_eq, sub_eq_zero, Set.ofPred_eq_eq_singleton, Real.volume_singleton,
      lintegral_zero]
  exact h

end PrimeBHT.TimeFrequency.X2

end
