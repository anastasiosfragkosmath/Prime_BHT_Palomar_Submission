module

public import PrimeBHT.Inputs.X3
public import PrimeBHT.MainConditional
public import PrimeBHT.Interface.X1Statement
public import PrimeBHT.TransferenceAssembly.Key0OfX2

/-!
# The main theorem from X1 and X2 (X3 from the earlier project)

`t_maintheorem_of_x1_x2` has exactly the type of the frozen `PrimeBHT.Statements.t_maintheorem`
(checked by `scripts/interface_check.sh`), assuming only the two frozen interface anchors
`X1Statement` (the type of `x1_bht_smooth`) and `X2Statement` (the type of `t_finiteBV`):
X3 is `PrimeBHT.Inputs.x3_of_lf` (the sealed theorem of the earlier project, ruling R12) and `p:key0`
is `key0Statement_of_x2`. When X1 and X2 are sealed, the provider `PrimeBHT.Proof.MainTheorem` is this
theorem applied to their proofs. This module is not imported by the root `PrimeBHT.lean` (it pulls in
the 1,403-module closure of X3).
-/

@[expose] public noncomputable section

open MeasureTheory

namespace PrimeBHT.Inputs

/-- **The main theorem, conditional on X1 and X2 only.** -/
theorem t_maintheorem_of_x1_x2 (hX1 : PrimeBHT.Interface.X1Statement.X1Statement)
    (hX2 : PrimeBHT.TransferenceAssembly.X2Statement) :
    ∀ p q r : ℝ, 1 < p → 1 < q → 1 / r = 1 / p + 1 / q →
      2 / p + 3 / q < 3 → 3 / p + 2 / q < 3 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : ℤ →₀ ℂ,
        eLpNorm (PrimeBHT.Statements.primeBHT f g) (ENNReal.ofReal r) Measure.count ≤
          ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count *
            eLpNorm (⇑g) (ENNReal.ofReal q) Measure.count := by
  obtain ⟨χ, hχ⟩ := PrimeBHT.Kernel.exists_isCutoff
  exact PrimeBHT.MainConditional.t_maintheorem_of_inputs hχ x3_of_lf
    (PrimeBHT.TransferenceAssembly.key0Statement_of_x2 hX2 χ)
    (PrimeBHT.Interface.X1Statement.bhtSmooth_of_x1 hX1 hχ)

end PrimeBHT.Inputs
