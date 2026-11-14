module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Fin.VecNotation

/-!
# Frozen: `PrimeBHT.Statements.timeInt`

The definition exactly as the author approved it (ruling R16, 2026-11-09) before any proof used it.
It is the only declaration in this file, and it is not edited.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- The common time interval `I_t = 2^s [v, v+1)` of the three tiles of the tri-tile `t = (s, v, ℓ)` (BD26
L573-579 with `τ_s = 0`: all three time intervals coincide). -/
def timeInt (t : ℤ × ℤ × ℤ) : Set ℝ :=
  Set.Ico ((2 : ℝ) ^ t.1 * t.2.1) ((2 : ℝ) ^ t.1 * (t.2.1 + 1))

end PrimeBHT.Statements
