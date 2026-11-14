module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Data.Finsupp.Indicator
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Support

/-!
# Frozen: `PrimeBHT.Statements.bhtTrunc`

The definition exactly as the author approved it (ruling R11, 2026-11-09) before any proof used it.
It is the only declaration in this file, and it is not edited.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- The discrete bilinear Hilbert transform with a smooth truncation at radii `L₁ < L₂`:
`∑_{m ≠ 0} ((χ(m/L₂) - χ(m/L₁)) / m) f(x - m) g(x + m)` (paper L261-264 for the untruncated form, L657-661 for the
kernel identity `t K_I(t) = χ(2^{-max I} t) - χ(2^{1-min I} t)` that produces these truncations). The kernel
carries the explicit guard `m = 0 → 0` (the paper's `m ≠ 0`). For finitely supported `f` the family in `m` has
finitely many nonzero terms, so the unconditional `∑'` is the genuine finite sum. -/
def bhtTrunc (χ : ℝ → ℝ) (L₁ L₂ : ℝ) (f g : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑' m : ℤ, (if m = 0 then 0 else (((χ (m / L₂) - χ (m / L₁)) / m : ℝ) : ℂ)) *
    f (x - m) * g (x + m)

end PrimeBHT.Statements
