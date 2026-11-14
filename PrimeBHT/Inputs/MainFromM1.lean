module

public import PrimeBHT.Inputs.Main
public import PrimeBHT.TimeFrequency.X1.FromM1

/-!
# The main theorem from M1(ε) and X2

`t_maintheorem_of_m1_x2` has exactly the type of the frozen `PrimeBHT.Statements.t_maintheorem` (checked by
`scripts/interface_check.sh`), assuming only the tri-tile estimate `M1Prop` (the type of the frozen
`tri_restricted_eps`) and `X2Statement` (the type of the frozen `t_finiteBV`). X3 comes from the earlier
project (ruling R12); X1 is `x1_of_m1`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace PrimeBHT.Inputs

/-- **The main theorem, conditional on M1(ε) and X2 only.** -/
theorem t_maintheorem_of_m1_x2 (hM1 : PrimeBHT.TimeFrequency.Interp.Hull.M1Prop)
    (hX2 : PrimeBHT.TransferenceAssembly.X2Statement) :
    ∀ p q r : ℝ, 1 < p → 1 < q → 1 / r = 1 / p + 1 / q →
      2 / p + 3 / q < 3 → 3 / p + 2 / q < 3 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : ℤ →₀ ℂ,
        eLpNorm (PrimeBHT.Statements.primeBHT f g) (ENNReal.ofReal r) Measure.count ≤
          ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count *
            eLpNorm (⇑g) (ENNReal.ofReal q) Measure.count :=
  t_maintheorem_of_x1_x2 (PrimeBHT.TimeFrequency.x1_of_m1 hM1) hX2

end PrimeBHT.Inputs
