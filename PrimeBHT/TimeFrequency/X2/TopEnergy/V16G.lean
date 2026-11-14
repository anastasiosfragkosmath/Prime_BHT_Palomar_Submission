module

public import PrimeBHT.TimeFrequency.X2.TopEnergy.StepG
public import PrimeBHT.TimeFrequency.X2.V16.Final

/-!
# X2, node V12-top: `EnergyStepG` for the outside family of B10

B10 (`V16/Outside.lean`, `outside_le_of_energy`) uses only the halving and the GLOBAL count of `EnergyStep`.  The localized
conjunct is FALSE for the top energy (report), so the outside family needs `V16.EnergyStepG` (defined in `V16/Outside.lean`,
with `V16.EnergyStep.toG`).  `V16.energyStepG_engFamR` is `energyStep_engFamR` (`V16/Final.lean`) for it, from `engV_stepG`;
`V16/{Outside,HullBound,Final}` and `TreeS/Final` have been re-pointed accordingly (REV4).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

namespace V16

/-- B10's family: `EnergyStepG` for `engFam` from the repaired V12 and the GLOBAL V12-top. -/
theorem energyStepG_engFamR (hV12 : EnergyLemmaStatementR) (hV12t : EnergyLemmaTopGStatement) {u : ℝ}
    (hu : 1 < u) {𝔭 : Params} (h𝔭 : V16Params u 𝔭) : EnergyStepG (engFam u 𝔭) u 𝔭 := by
  have hR4 : 4 ≤ Rof u := four_le_Rof hu
  have hs := fun v : Fin 3 => engV_stepG hV12 hV12t 𝔭 (h𝔭.tree_loc_decN_admissible hu) (u := u) (R := Rof u) v
    (isEnergyExponent_slot hu v) (qX_lt_qPlus hR4 v)
  choose C hC0 hC using hs
  refine ⟨∑ v, C v, Finset.sum_nonneg fun v _ => hC0 v, ?_⟩
  intro P _ Qs hQ Cs₀ Cs hbox hTC hres h hm hbdd v
  obtain ⟨ts, h1, h2⟩ := hC v P Qs hQ Cs₀ Cs hbox hTC hres (h v) (hm v) (hbdd v)
  have hle : ENNReal.ofReal (C v) ≤ ENNReal.ofReal (∑ v, C v) :=
    ENNReal.ofReal_le_ofReal
      (Finset.single_le_sum (f := C) (fun v _ => hC0 v) (Finset.mem_univ v))
  exact ⟨ts, h1, h2.trans (mul_le_mul_left hle _)⟩

end V16

end PrimeBHT.TimeFrequency.X2
