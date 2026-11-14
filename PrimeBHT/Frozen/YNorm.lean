module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Frozen: `PrimeBHT.Statements.yNorm`

The definition exactly as the author approved it (ruling R11, 2026-11-09) before any proof used it.
It is the only declaration in this file, and it is not edited.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate ContDiff

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- The `L^s(Y_P)` norm of `F : Y_P → ℂ` for the *normalized* counting measure on `Y_P = ℤ/P`:
`((1/P) ∑_y ‖F y‖^s)^(1/s)` (lines 925-928: "`Y_P` carries normalized counting measure").
Used with `s = 2` for the two Hilbert slots and with `s = u` for the third slot. -/
def yNorm {P : ℕ} [NeZero P] (s : ℝ) (F : ZMod P → ℂ) : ℝ :=
  ((P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ s) ^ s⁻¹

end PrimeBHT.Statements
