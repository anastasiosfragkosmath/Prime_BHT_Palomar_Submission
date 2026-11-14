-- FROZEN_ANCHOR_PREFIX_BEGIN
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
public import PrimeBHT.Frozen.IsCutoff
public import PrimeBHT.Frozen.BhtTrunc
import PrimeBHT.Proof.X1

/-!
# Frozen: `PrimeBHT.Statements.x1_bht_smooth`

The statement exactly as the author approved it (ruling R11, 2026-11-09) before any proof was
written. It is the only declaration in this file; only the proof between the `FROZEN_ANCHOR`
marker comments is filled in afterwards. While the state is `DRAFT_SORRY` the body is the single
authorized `by sorry`, and the statement is frozen but unproved: nothing may consume it.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- **X1 (paper L261-264 and L657-671; the Lacey-Thiele bilinear Hilbert transform on `ℤ`, smooth
truncations uniform in both radii).** For every cutoff `χ` and every `1 < p, q`, `1/r = 1/p + 1/q`,
`2/3 < r` there is a constant `C` (depending on `χ, p, q, r` only) such that for all real `0 < L₁ < L₂` and all
finitely supported `f, g : ℤ → ℂ`,
`‖bhtTrunc χ L₁ L₂ f g‖_{ℓ^r} ≤ C ‖f‖_{ℓ^p} ‖g‖_{ℓ^q}`.
The `ℓ^s` quasi-norms are `eLpNorm` for counting measure. -/
theorem x1_bht_smooth : ∀ χ : ℝ → ℝ, IsCutoff χ →
    ∀ p q r : ℝ, 1 < p → 1 < q → 1 / r = 1 / p + 1 / q → 2 / 3 < r →
      ∃ C : ℝ, ∀ L₁ L₂ : ℝ, 0 < L₁ → L₁ < L₂ →
        ∀ f g : ℤ → ℂ, (Function.support f).Finite → (Function.support g).Finite →
          eLpNorm (bhtTrunc χ L₁ L₂ f g) (ENNReal.ofReal r) Measure.count ≤
            ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) Measure.count *
              eLpNorm g (ENNReal.ofReal q) Measure.count :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact PrimeBHT.Proof.x1_bht_smooth
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end PrimeBHT.Statements
-- FROZEN_ANCHOR_SUFFIX_END
