module

public import PrimeBHT.FinalGlue
public import PrimeBHT.Frozen.IsCutoff
public import PrimeBHT.Frozen.UOp

/-!
# Bridge between the project's `Key0Statement` and the frozen definitions

`PrimeBHT.FinalGlue.Key0Statement χ` (used by the assembly modules) is the body of the corrected `p:key0`
written with the project's `PrimeBHT.Kernel` definitions and `uOp` on `ℤ → ℂ`. This file shows it is
exactly the body of the frozen `PrimeBHT.Statements.p_key0` at `χ`, written with the frozen definitions
`PrimeBHT.Statements.IsCutoff` and `PrimeBHT.Statements.uOp`. It does NOT mention the frozen theorem
(quarantine of the `DRAFT_SORRY` anchor): the provider applies it once the anchor is sealed.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace PrimeBHT.Bridge

/-- The project's cutoff structure is the frozen cutoff predicate. -/
theorem isCutoff_iff {χ : ℝ → ℝ} :
    PrimeBHT.Kernel.IsCutoff χ ↔ PrimeBHT.Statements.IsCutoff χ :=
  ⟨fun h => ⟨h.contDiff, h.even, h.tsupport_subset, h.eq_one⟩,
   fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

/-- The body of the frozen `p_key0` at a given cutoff `χ`, as a `Prop` (no reference to the theorem). -/
def FrozenKey0Body (χ : ℝ → ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → τ < 1 →
  ∀ η : ℝ, 0 < η →
    ∃ Q₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ Q : ℕ, (∃ j : ℕ, Q = 2 ^ j) → Q₀ ≤ Q →
      ∀ J : ℕ, ∀ f g : ℤ →₀ ℂ,
        eLpNorm (PrimeBHT.Statements.uOp χ Q τ J f g) 1 Measure.count ≤
          ENNReal.ofReal (C * (Q : ℝ) ^ (-τ / 2 + η)) *
            eLpNorm (⇑f) 2 Measure.count * eLpNorm (⇑g) 2 Measure.count

/-- `Key0Statement χ` is (an implication from the cutoff predicate to) the frozen body. -/
theorem key0Statement_iff {χ : ℝ → ℝ} :
    PrimeBHT.FinalGlue.Key0Statement χ ↔ (PrimeBHT.Statements.IsCutoff χ → FrozenKey0Body χ) := by
  unfold PrimeBHT.FinalGlue.Key0Statement FrozenKey0Body
  constructor
  · intro h hc
    exact h (isCutoff_iff.mpr hc)
  · intro h hc
    exact h (isCutoff_iff.mp hc)

end PrimeBHT.Bridge
