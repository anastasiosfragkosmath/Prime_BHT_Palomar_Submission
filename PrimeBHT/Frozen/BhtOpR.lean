module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import PrimeBHT.Frozen.BhtKernelR

/-!
# Frozen: `PrimeBHT.Statements.bhtOpR`

The definition exactly as the author approved it (ruling R15, 2026-11-09) before any proof used it.
It is the only declaration in this file, and it is not edited.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- The real-line bilinear operator with smooth truncation,
`bhtOpR χ λ μ f g (x) = ∫_ℝ f(x - y) g(x + y) K_{λ,μ}(y) dy` (BD26 Theorem 1.2: `B(K, f₁, f₂) = ∫ f₁(x-y) f₂(x+y)
K(y) dy`, with `f` in the `x - y` slot and `g` in the `x + y` slot; DPLMV L268-271). It is the Bochner integral
with respect to Lebesgue measure; for Schwartz (indeed continuous) `f, g` the integrand is continuous with
compact support, hence integrable, so it is the genuine integral and never the junk value `0`. -/
def bhtOpR (χ : ℝ → ℝ) (lam mu : ℝ) (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, f (x - y) * g (x + y) * (bhtKernelR χ lam mu y : ℂ)

end PrimeBHT.Statements
