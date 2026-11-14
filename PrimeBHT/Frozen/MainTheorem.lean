-- FROZEN_ANCHOR_PREFIX_BEGIN
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
public import PrimeBHT.Frozen.PrimeBHT
import PrimeBHT.Proof.MainTheorem

/-!
# Frozen: `PrimeBHT.Statements.t_maintheorem`

The statement exactly as the author approved it (ruling R9, 2026-11-09) before any proof was
written. It is the only declaration in this file; only the proof between the `FROZEN_ANCHOR`
marker comments is filled in afterwards. While the state is `DRAFT_SORRY` the body is the single
authorized `by sorry`, and the statement is frozen but unproved: nothing may consume it.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.Statements

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
            eLpNorm (⇑g) (ENNReal.ofReal q) Measure.count :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact PrimeBHT.Proof.t_maintheorem
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end PrimeBHT.Statements
-- FROZEN_ANCHOR_SUFFIX_END
