-- FROZEN_ANCHOR_PREFIX_BEGIN
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
public import PrimeBHT.Frozen.IsCutoff
public import PrimeBHT.Frozen.UOp
import PrimeBHT.Proof.Key0

/-!
# Frozen: `PrimeBHT.Statements.p_key0`

The statement exactly as the author approved it (ruling R10, 2026-11-09) before any proof was
written. It is the only declaration in this file; only the proof between the `FROZEN_ANCHOR`
marker comments is filled in afterwards. While the state is `DRAFT_SORRY` the body is the single
authorized `by sorry`, and the statement is frozen but unproved: nothing may consume it.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- **`p:key0`, corrected form (lines 705-720; the half `e:long-unsmoothed`).** For every cutoff `χ`,
every `τ ∈ (0,1)` and every `η > 0` there are `Q₀` and `C` such that for every dyadic `Q ≥ Q₀`, every
truncation `J` and all finitely supported `f, g`:
`‖U^J_{Q;τ}(f,g)‖_{ℓ¹} ≤ C Q^{-τ/2+η} ‖f‖_{ℓ²} ‖g‖_{ℓ²}`. The smoothed half `e:longgoal` of the printed
proposition is not stated (it cannot be read literally for a fixed smoothing parameter; and nothing
consumes it). -/
theorem p_key0 :
    ∀ χ : ℝ → ℝ, IsCutoff χ →
    ∀ τ : ℝ, 0 < τ → τ < 1 →
    ∀ η : ℝ, 0 < η →
      ∃ Q₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ Q : ℕ, (∃ j : ℕ, Q = 2 ^ j) → Q₀ ≤ Q →
        ∀ J : ℕ, ∀ f g : ℤ →₀ ℂ,
          eLpNorm (uOp χ Q τ J f g) 1 Measure.count ≤
            ENNReal.ofReal (C * (Q : ℝ) ^ (-τ / 2 + η)) *
              eLpNorm (⇑f) 2 Measure.count * eLpNorm (⇑g) 2 Measure.count :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact PrimeBHT.Proof.p_key0
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end PrimeBHT.Statements
-- FROZEN_ANCHOR_SUFFIX_END
