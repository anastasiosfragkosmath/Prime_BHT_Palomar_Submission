module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Data.Finsupp.Indicator
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Frozen: `PrimeBHT.Statements.primeBHT`

The definition exactly as the author approved it (ruling R9, 2026-11-09) before any proof used it.
It is the only declaration in this file, and it is not edited.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- The prime bilinear Hilbert transform
`ℋ_ℙ(f, g)(x) = ∑_{n ≠ 0} (Λ(|n|) / n) f(x - n) g(x + n)` (line 172, `e:BHTdef`),
for finitely supported `f, g : ℤ → ℂ`, where `Λ = ArithmeticFunction.vonMangoldt`
(lines 342-343) and `Λ(|n|)` is `vonMangoldt n.natAbs`.

The series has finitely many nonzero terms: a term can be nonzero only if `x - n ∈ f.support`,
and `f.support` is finite (`primeBHTTerm_eq_zero` and `primeBHT_eq_sum` below), so the
unconditional sum `∑'` is the genuine finite sum and not the junk value `0` that `tsum` takes
for a non-summable family (`primeBHT_hasSum` below). The guard `n = 0 → 0` is
explicit, as in the earlier approved statements (`modulatedSum`): the term at `n = 0` is `0`
in the paper's sum because `n = 0` is excluded, and in Lean it would also be `0` by the junk
conventions `Λ 0 = 0`, `a / 0 = 0`, but the statement does not rely on them. -/
def primeBHT (f g : ℤ →₀ ℂ) (x : ℤ) : ℂ :=
  ∑' n : ℤ, if n = 0 then 0 else
    ((ArithmeticFunction.vonMangoldt n.natAbs : ℝ) : ℂ) / (n : ℂ) * f (x - n) * g (x + n)

end PrimeBHT.Statements
