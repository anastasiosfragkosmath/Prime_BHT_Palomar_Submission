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

/-- **Main theorem T0 (`t:maintheorem`, lines 175-179).** For every `(p, q, r)` in the region
`ℛ = {(p,q,r) ∈ (0,∞)³ : 2/p + 3/q < 3, 3/p + 2/q < 3, 1/r = 1/p + 1/q, p, q > 1}` there is a
constant `C = C_{p,q,r}` such that `‖ℋ_ℙ(f,g)‖_{ℓ^r} ≤ C ‖f‖_{ℓ^p} ‖g‖_{ℓ^q}` for all finitely
supported `f, g : ℤ → ℂ`. The `ℓ^s` quasi-norms are `eLpNorm` for counting measure (values in
`[0, ∞]`; for `s < 1` this is `(∑ |F x|^s)^(1/s)`, see `eLpNorm_count_eq`). Finite support is
the paper's reading of "extends to a bounded operator" (lines 149-154): the estimate on the dense
subspace, from which density extends the operator (lines 1437-1440);
`t_maintheorem_extension` is the optional pointwise extension. The memberships `0 < p, q, r`
of `(0,∞)³` are consequences of `1 < p`, `1 < q`, `1/r = 1/p + 1/q` (see `r_pos_of_region`). -/
theorem t_maintheorem :
    ∀ p q r : ℝ, 1 < p → 1 < q → 1 / r = 1 / p + 1 / q →
      2 / p + 3 / q < 3 → 3 / p + 2 / q < 3 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : ℤ →₀ ℂ,
        eLpNorm (primeBHT f g) (ENNReal.ofReal r) Measure.count ≤
          ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count *
            eLpNorm (⇑g) (ENNReal.ofReal q) Measure.count := by
  sorry

end PrimeBHT.Statements
