module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Fin.VecNotation

/-!
# Frozen: `PrimeBHT.Statements.pairing`

The definition exactly as the author approved it (ruling R16, 2026-11-09) before any proof used it.
It is the only declaration in this file, and it is not edited.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- The pairing `⟨h, φ⟩ = ∫ h conj(φ)` (complex-valued; the form only uses its norm). -/
def pairing (h φ : ℝ → ℂ) : ℂ := ∫ x, h x * (starRingEnd ℂ) (φ x)

end PrimeBHT.Statements
