module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Fin.VecNotation

/-!
# Frozen: `PrimeBHT.Statements.freqNum`

The definition exactly as the author approved it (ruling R16, 2026-11-09) before any proof used it.
It is the only declaration in this file, and it is not edited.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- The three numerators `ℓ`, `ℓ - a`, `2ℓ - a - b` of the frequency intervals (slot `k = 0, 1, 2` is the
source's slot `1, 2, 3`). -/
def freqNum (a b : ℤ) (t : ℤ × ℤ × ℤ) : Fin 3 → ℤ :=
  ![t.2.2, t.2.2 - a, 2 * t.2.2 - a - b]

end PrimeBHT.Statements
