module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Fin.VecNotation

/-!
# Frozen: `PrimeBHT.Statements.TriValid`

The definition exactly as the author approved it (ruling R16, 2026-11-09) before any proof used it.
It is the only declaration in this file, and it is not edited.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- The validity of the parameters `ν = (a, b, s', α)` of BD26 (L563-566): `21 ≤ a ≤ 30`, `-6 ≤ b ≤ 3`,
`0 ≤ s' ≤ 9`, `0 ≤ α ≤ 2` (`10 · 10 · 10 · 3 = 3000` values). The ranges are the source's ranges, not extra
hypotheses. -/
def TriValid (a b s' α : ℤ) : Prop :=
  (21 ≤ a ∧ a ≤ 30) ∧ (-6 ≤ b ∧ b ≤ 3) ∧ (0 ≤ s' ∧ s' ≤ 9) ∧ (0 ≤ α ∧ α ≤ 2)

end PrimeBHT.Statements
