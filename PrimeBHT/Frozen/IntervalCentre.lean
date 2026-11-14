module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Fin.VecNotation

/-!
# Frozen: `PrimeBHT.Statements.intervalCentre`

The definition exactly as the author approved it (ruling R16, 2026-11-09) before any proof used it.
It is the only declaration in this file, and it is not edited.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- The centre `c(S) = (inf S + sup S) / 2` of an interval `S` (BD26 L503 `c(I)`). Only used for bounded
nondegenerate intervals (`timeInt`, `freqInt`). -/
def intervalCentre (S : Set ℝ) : ℝ := (sInf S + sSup S) / 2

end PrimeBHT.Statements
