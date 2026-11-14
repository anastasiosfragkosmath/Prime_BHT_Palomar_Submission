module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import PrimeBHT.Frozen.TensorFourier

/-!
# Frozen: `PrimeBHT.Statements.multiplierForm`

The definition exactly as the author approved it (ruling R11, 2026-11-09) before any proof used it.
It is the only declaration in this file, and it is not edited.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate ContDiff

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- The form `Λ_m^Π(F₁,F₂,F₃) = ∫_{ℝ²} m(ξ₂ - ξ₁) Π(F̂₁(ξ₁;·), F̂₂(ξ₂;·), F̂₃(ξ₁+ξ₂;·)) dξ₁ dξ₂`
(lines 958-965), a Bochner integral over `ℝ × ℝ` with Lebesgue measure. The form `Π` is
complex-linear in slots 1, 2 and conjugate-linear in slot 3. -/
def multiplierForm {P : ℕ} [NeZero P] (m : ℝ → ℂ)
    (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
    (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) : ℂ :=
  ∫ ξ : ℝ × ℝ, m (ξ.2 - ξ.1) *
    T (tensorFourier f₁ ξ.1) (tensorFourier f₂ ξ.2) (tensorFourier f₃ (ξ.1 + ξ.2))

end PrimeBHT.Statements
