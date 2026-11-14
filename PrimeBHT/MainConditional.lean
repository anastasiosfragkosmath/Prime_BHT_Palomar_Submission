module

public import PrimeBHT.MainBanach
public import PrimeBHT.MainQuasiBanach
public import PrimeBHT.Frozen.PrimeBHT

/-!
# The main theorem, conditional on the three named anchors

`t_maintheorem_of_inputs` has exactly the conclusion of the frozen `PrimeBHT.Statements.t_maintheorem`
(about the frozen definition `PrimeBHT.Statements.primeBHT`), assuming for a cutoff `χ`:
* `X3Statement` (the sealed [F+, Prop 3.1] statement),
* the corrected `p:key0` statement (`Key0Statement χ`),
* X1 (`BHTSmooth χ p' q' r' C'`) at every tuple with `p', q' > 1`, `1/r' = 1/p' + 1/q'`, `2/3 < r'`.

It does NOT import the frozen theorem (quarantine of the `DRAFT_SORRY` anchor). When X1 and `p:key0`
are sealed, the provider `PrimeBHT.Proof.MainTheorem` applies this theorem to the sealed anchors.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace PrimeBHT.MainConditional

open PrimeBHT.Kernel PrimeBHT.Exponents PrimeBHT.Progression

/-- The two copies of the `p:key0` statement (`MainBanach.Key0Prop`, `FinalGlue.Key0Statement`) agree. -/
theorem key0_iff {χ : ℝ → ℝ} :
    PrimeBHT.MainBanach.Key0Prop χ ↔ PrimeBHT.FinalGlue.Key0Statement χ := Iff.rfl

/-- **The main theorem, conditional on X3, `p:key0` and X1**: the conclusion is the frozen statement. -/
theorem t_maintheorem_of_inputs {χ : ℝ → ℝ} (hχ : IsCutoff χ)
    (hX3 : PrimeBHT.ErrorTerms.X3Statement) (hK : PrimeBHT.FinalGlue.Key0Statement χ)
    (hX1 : ∀ p' q' r' : ℝ, 1 < p' → 1 < q' → 1 / r' = 1 / p' + 1 / q' → 2 / 3 < r' →
      ∃ C' : ℝ, BHTSmooth χ p' q' r' C') :
    ∀ p q r : ℝ, 1 < p → 1 < q → 1 / r = 1 / p + 1 / q →
      2 / p + 3 / q < 3 → 3 / p + 2 / q < 3 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : ℤ →₀ ℂ,
        eLpNorm (PrimeBHT.Statements.primeBHT f g) (ENNReal.ofReal r) Measure.count ≤
          ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count *
            eLpNorm (⇑g) (ENNReal.ofReal q) Measure.count := by
  intro p q r hp hq hr h1 h2
  have hrpos : 0 < r := by
    have : 0 < 1 / r := by rw [hr]; positivity
    exact one_div_pos.mp this
  have hR : InR p q r := ⟨hrpos, hp, hq, hr, h1, h2⟩
  by_cases hr1 : r < 1
  · exact PrimeBHT.MainQuasiBanach.main_quasiBanach_of_inputs hχ hX3 hK hX1 hR hr1
  · exact PrimeBHT.MainBanach.main_banach_of_inputs hχ hR (not_lt.mp hr1) hX3
      (fun p' q' r' hp' hq' h' hr' => hX1 p' q' r' hp' hq' h' (by linarith)) (key0_iff.mpr hK)

end PrimeBHT.MainConditional
