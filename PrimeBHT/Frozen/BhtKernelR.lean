module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Frozen: `PrimeBHT.Statements.bhtKernelR`

The definition exactly as the author approved it (ruling R15, 2026-11-09) before any proof used it.
It is the only declaration in this file, and it is not edited.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- The real-line smooth-truncation kernel `K_{λ,μ}(y) = (χ(λy) - χ(μy)) / y` (the kernel of the `ℤ`-operator
`bhtTrunc` at the radii `L₂ = 1/λ`, `L₁ = 1/μ`; paper L657-661, the identity `t K_I(t) = χ(2^{-max I} t) -
χ(2^{1-min I} t)`; BD26 Theorem 1.2). At `y = 0` the numerator is `χ 0 - χ 0 = 0` for every `χ`, so the value
there (`0`, Lean's `x / 0 = 0`) is the intended `K(0) := 0` and not a junk value that matters; for a cutoff and
`0 < λ ≤ μ` the kernel vanishes on a neighbourhood of `0` and for `|y| ≥ 1/λ`. -/
def bhtKernelR (χ : ℝ → ℝ) (lam mu : ℝ) (y : ℝ) : ℝ := (χ (lam * y) - χ (mu * y)) / y

end PrimeBHT.Statements
