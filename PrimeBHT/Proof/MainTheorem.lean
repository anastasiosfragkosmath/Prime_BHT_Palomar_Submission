module

public import PrimeBHT.Inputs.X3
public import PrimeBHT.MainConditional
public import PrimeBHT.Interface.X1Statement
public import PrimeBHT.Bridge.Key0
public import PrimeBHT.Frozen.PrimeBHT
public import PrimeBHT.Frozen.X1
public import PrimeBHT.Frozen.Key0

/-!
# Provider of `PrimeBHT.Statements.t_maintheorem` (the main theorem T0)

The frozen anchor `PrimeBHT/Frozen/MainTheorem.lean` is sealed with the body `by exact PrimeBHT.Proof.t_maintheorem`.
The proof is the capstone `PrimeBHT.MainConditional.t_maintheorem_of_inputs` (the inputs X3, `p:key0` and X1) applied to

* X3: `PrimeBHT.Inputs.x3_of_lf` (the sealed theorem of the earlier project, ruling R12; `PrimeBHT.Inputs.X3` is NOT
  imported by the root `PrimeBHT.lean`, so this provider is where it enters the main theorem);
* `p:key0`: the SEALED frozen theorem `PrimeBHT.Statements.p_key0` (sealed from the sealed X2), through
  `PrimeBHT.Bridge.key0Statement_iff`;
* X1: the SEALED frozen theorem `PrimeBHT.Statements.x1_bht_smooth`, through `PrimeBHT.Interface.X1Statement.bhtSmooth_of_x1`.

So the sealed X1, `p:key0` (hence X2) and X3 are all consumed through their frozen exports.  The statement below is the
frozen one (`scripts/interface_check.sh` checks them equal by `rfl`).

Alternative (not used): `PrimeBHT.Inputs.t_maintheorem_of_x1_x2 PrimeBHT.Statements.x1_bht_smooth PrimeBHT.Statements.t_finiteBV`
(same type; it rebuilds `p:key0` from X2 internally instead of consuming the sealed `p_key0`).
-/

@[expose] public section

namespace PrimeBHT.Proof

open MeasureTheory

/-- **Main theorem T0** (`t:maintheorem`), from the sealed X1, the sealed `p:key0` and X3. -/
theorem t_maintheorem :
    ∀ p q r : ℝ, 1 < p → 1 < q → 1 / r = 1 / p + 1 / q →
      2 / p + 3 / q < 3 → 3 / p + 2 / q < 3 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : ℤ →₀ ℂ,
        eLpNorm (PrimeBHT.Statements.primeBHT f g) (ENNReal.ofReal r) Measure.count ≤
          ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count *
            eLpNorm (⇑g) (ENNReal.ofReal q) Measure.count := by
  obtain ⟨χ, hχ⟩ := PrimeBHT.Kernel.exists_isCutoff
  exact PrimeBHT.MainConditional.t_maintheorem_of_inputs hχ PrimeBHT.Inputs.x3_of_lf
    (PrimeBHT.Bridge.key0Statement_iff.mpr (PrimeBHT.Statements.p_key0 χ))
    (PrimeBHT.Interface.X1Statement.bhtSmooth_of_x1 PrimeBHT.Statements.x1_bht_smooth hχ)

end PrimeBHT.Proof
