module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Fin.VecNotation

/-!
# Frozen: `PrimeBHT.Statements.triIdx`

The definition exactly as the author approved it (ruling R16, 2026-11-09) before any proof used it.
It is the only declaration in this file, and it is not edited.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- The index set `Idx_ν = {(s, v, ℓ) ∈ ℤ³ : s ≡ s' (mod 10), ℓ ≡ α (mod 3)}` (BD26 L567-571 with all shifts
`τ_s = 0`). A triple `t = (s, v, ℓ)` is `(t.1, t.2.1, t.2.2)`. -/
def triIdx (s' α : ℤ) : Set (ℤ × ℤ × ℤ) :=
  {t | t.1 ≡ s' [ZMOD 10] ∧ t.2.2 ≡ α [ZMOD 3]}

end PrimeBHT.Statements
