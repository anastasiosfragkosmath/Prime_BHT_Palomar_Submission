module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Frozen: `PrimeBHT.Statements.tensorFourier`

The definition exactly as the author approved it (ruling R11, 2026-11-09) before any proof used it.
It is the only declaration in this file, and it is not edited.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate ContDiff

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- The partial Fourier transform `F̂(ξ; y) = ∑_{A ∈ Y_P} f̂_A(ξ) e(A y / P)` (line 970), where
`f̂(ξ) = ∫ f(x) e(-x ξ) dx` (the paper's convention, lines 317-318) is Mathlib's `𝓕`. -/
def tensorFourier {P : ℕ} [NeZero P] (f : ZMod P → 𝓢(ℝ, ℂ)) (ξ : ℝ) (y : ZMod P) : ℂ :=
  ∑ A : ZMod P, 𝓕 (⇑(f A)) ξ * ZMod.stdAddChar (A * y)

end PrimeBHT.Statements
