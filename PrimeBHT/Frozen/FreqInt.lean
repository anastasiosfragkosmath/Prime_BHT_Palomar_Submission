module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Fin.VecNotation
public import PrimeBHT.Frozen.FreqNum

/-!
# Frozen: `PrimeBHT.Statements.freqInt`

The definition exactly as the author approved it (ruling R16, 2026-11-09) before any proof used it.
It is the only declaration in this file, and it is not edited.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- The frequency intervals `ω_{t,k} = 2^{-s} [n_k/3, n_k/3 + 1)` (half-open), with `n_0 = ℓ`, `n_1 = ℓ - a`,
`n_2 = 2ℓ - a - b` (BD26 L573-579). -/
def freqInt (a b : ℤ) (k : Fin 3) (t : ℤ × ℤ × ℤ) : Set ℝ :=
  Set.Ico ((2 : ℝ) ^ (-t.1) * ((freqNum a b t k : ℝ) / 3))
    ((2 : ℝ) ^ (-t.1) * ((freqNum a b t k : ℝ) / 3 + 1))

end PrimeBHT.Statements
