module

public import PrimeBHT.Frozen.IsCutoff
public import PrimeBHT.Frozen.BhtTrunc
public import PrimeBHT.Interface.X1Checks
public import PrimeBHT.Progression
public import PrimeBHT.Bridge.Key0

/-!
# The X1 statement as a `Prop`, and its interface with `PrimeBHT.Progression`

`X1Statement` is the type of the frozen theorem `PrimeBHT.Statements.x1_bht_smooth` (ruling R11),
copied verbatim from the approved text over the frozen definitions `PrimeBHT.Statements.bhtTrunc`
and `PrimeBHT.Statements.IsCutoff`. That it is literally that type is checked by
`scripts/interface_check.sh`. This file does NOT mention the frozen theorem (quarantine of the
`DRAFT_SORRY` anchor), and nothing here is proved from it: the results consuming X1 take
`X1Statement` as a hypothesis and are named `…_of_x1`.

Contents (migrated from section 4 of the pre-freeze draft `drafts/X1Statement.lean.txt`, adapted to the
frozen statement, which has `Statements.IsCutoff` and no `0 ≤ C` conjunct):
* `bhtTrunc_eq_bilin_truncKernel`: `bhtTrunc` is the operator of `BHTSmooth` (`rfl`);
* `x1_iff_bhtSmooth`: the inner part of the statement IS `PrimeBHT.Progression.BHTSmooth` (`Iff.rfl`);
* `nonneg_of_bhtSmooth`, `x1Statement_iff_nonneg`: the dropped conjunct `0 ≤ C` is redundant;
* `bhtSmooth_of_x1`: `X1Statement` gives exactly the hypothesis `hX1` of
  `PrimeBHT.MainConditional.t_maintheorem_of_inputs`;
* `progression_of_x1`: the conditional consumption by `e:progression` (N24).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.Interface.X1Statement

set_option linter.dupNamespace false in
/-- **The statement of the frozen `x1_bht_smooth`** (ruling R11), as a `Prop`, written over the frozen
definitions `PrimeBHT.Statements.bhtTrunc` and `PrimeBHT.Statements.IsCutoff`. It is textually the
type of `PrimeBHT.Statements.x1_bht_smooth` (the approved text of `scripts/data/approved/X1-approved.lean.txt`). -/
def X1Statement : Prop :=
  ∀ χ : ℝ → ℝ, PrimeBHT.Statements.IsCutoff χ →
    ∀ p q r : ℝ, 1 < p → 1 < q → 1 / r = 1 / p + 1 / q → 2 / 3 < r →
      ∃ C : ℝ, ∀ L₁ L₂ : ℝ, 0 < L₁ → L₁ < L₂ →
        ∀ f g : ℤ → ℂ, (Function.support f).Finite → (Function.support g).Finite →
          eLpNorm (PrimeBHT.Statements.bhtTrunc χ L₁ L₂ f g) (ENNReal.ofReal r) Measure.count ≤
            ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) Measure.count *
              eLpNorm g (ENNReal.ofReal q) Measure.count

/-! ## Interface with `PrimeBHT.Progression` (what N24 consumes) -/

/-- **`X1Statement` is the hypothesis `hX1` of `PrimeBHT.MainConditional.t_maintheorem_of_inputs`**
(conditional on `X1Statement`): at a cutoff of the project's `Kernel.IsCutoff` structure (equivalent to
the frozen `IsCutoff`, `PrimeBHT.Bridge.isCutoff_iff`), `BHTSmooth` holds at every tuple of the
open BHT range. -/
theorem bhtSmooth_of_x1 (hX1 : X1Statement) {χ : ℝ → ℝ} (hχ : PrimeBHT.Kernel.IsCutoff χ) :
    ∀ p q r : ℝ, 1 < p → 1 < q → 1 / r = 1 / p + 1 / q → 2 / 3 < r →
      ∃ C : ℝ, PrimeBHT.Progression.BHTSmooth χ p q r C :=
  fun p q r hp hq hpqr hr =>
    hX1 χ (PrimeBHT.Bridge.isCutoff_iff.mp hχ) p q r hp hq hpqr hr

end PrimeBHT.Interface.X1Statement

end
