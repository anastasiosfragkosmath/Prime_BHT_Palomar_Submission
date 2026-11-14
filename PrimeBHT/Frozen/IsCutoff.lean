module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
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
public import PrimeCarleson.Frozen.BlockWeight

/-!
# Frozen: `PrimeBHT.Statements.IsCutoff`

The definition exactly as the author approved it (ruling R10, 2026-11-09) before any proof used it.
It is the only declaration in this file, and it is not edited.
-/

@[expose] public noncomputable section

open scoped ContDiff

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- The admissible smooth cutoff of the paper (lines 372-376): an even `C^∞` function whose topological
support lies in `(-1, 1)` and which equals `1` on `[-1/2, 1/2]`. (`∞` is `C^∞` smoothness, not analytic.) -/
def IsCutoff (χ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ χ ∧ (∀ t, χ (-t) = χ t) ∧ tsupport χ ⊆ Set.Ioo (-1) 1 ∧
    ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), χ t = 1

end PrimeBHT.Statements
