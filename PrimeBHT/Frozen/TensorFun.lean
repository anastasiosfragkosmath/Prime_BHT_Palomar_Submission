module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Frozen: `PrimeBHT.Statements.tensorFun`

The definition exactly as the author approved it (ruling R11, 2026-11-09) before any proof used it.
It is the only declaration in this file, and it is not edited.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate ContDiff

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- The tensor Schwartz function `F(x; y) = ∑_{A ∈ Y_P} f_A(x) e(A y / P)` of `e:tensor` (line 958),
given by its coefficients `f_A ∈ 𝓢(ℝ)`; `e(A y / P)` is `ZMod.stdAddChar (A * y)`. -/
def tensorFun {P : ℕ} [NeZero P] (f : ZMod P → 𝓢(ℝ, ℂ)) (x : ℝ) (y : ZMod P) : ℂ :=
  ∑ A : ZMod P, f A x * ZMod.stdAddChar (A * y)

end PrimeBHT.Statements
