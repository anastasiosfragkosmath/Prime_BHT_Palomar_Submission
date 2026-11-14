module

public import PrimeBHT.TimeFrequency.X2.TreeS.Main
public import PrimeBHT.TimeFrequency.X2.V16.Final
public import PrimeBHT.TimeFrequency.X2.EngTail.Tree
public import PrimeBHT.TimeFrequency.X2.EnergyLemmaO
public import PrimeBHT.TimeFrequency.X2.TopEnergy.V16G

/-!
# X2, node V16: the final theorem `V16.v16_of_hyps_rev4` (REV4; SUPERSEDED by `v16_of_hyps_rev5`)

NOTE: the current final V16 theorems are `V16.v16_of_hyps_rev5` / `V16.v16_of_hyps_rev5_nonHilbert` (`TreeS/FinalTB4.lean`),
which discharge the V12-top hypothesis below by `energyLemmaTopG_nonHilbert`; REV4 is the intermediate step they use.

`V16.v16_of_hyps_rev4 (hpint : PintStatementOFor IsEnergyExponent) (hsel : OSelectable)
  (hV12t : EnergyLemmaTopGStatementFor NonHilbertExp) (hTree : TreeLemmaStatementRev2) : V16Statement`

has EXACTLY the unproved node statements of V16:

* `PintStatementOFor IsEnergyExponent` (V11, the TRUE `pint` for `IsStronglyDisjointO`; the Hilbert case
  `(s, qX) = (2, 2)` is PROVED, `pint_two_O_statement`, so only `PintStatementOFor NonHilbertExp` is really open:
  `v16_of_hyps_rev4_nonHilbert`);
* `OSelectable` (the selection lemma of the V12 energy lemma `energyLemmaO`, open; reduced to a relational finite-family
  statement in `EnergyLemma/SelectableProof.lean`);
* `EnergyLemmaTopGStatementFor NonHilbertExp` (V12-top, GLOBAL part, slots with `s ≠ 2`: TB-4; the Hilbert case is PROVED,
  `energyLemmaTopG_two`; the localized part is false and not used);
* `TreeLemmaStatementRev2` (V15).

PROVED and discharged: B5 (`engLeTailMass`), B5-top (`engTopLeTailMass`), V15s (`treeLemmaSingleScale`), B7, B10 (with the
global step `V16.EnergyStepG`), B11, B12, the top separation TB-3 and the Hilbert top energy lemma.

The old chain `v16_of_hyps_rev3` / `v16_of_hyps_rev3_proved` (nested `PintStatement`, printed `EnergyLemmaTopStatement`) is kept
for reference only: both of its Props are unsatisfiable.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- `PintStatementOFor` for a union of exponent sets. -/
theorem PintStatementOFor.of_union {E₁ E₂ E : ℝ → ℝ → Prop} (h₁ : PintStatementOFor E₁)
    (h₂ : PintStatementOFor E₂) (hE : ∀ s qX, E s qX → E₁ s qX ∨ E₂ s qX) : PintStatementOFor E :=
  fun 𝔭 h𝔭 s qX α hX hα hα1 => by
    rcases hE s qX hX with h | h
    · exact h₁ 𝔭 h𝔭 h hα hα1
    · exact h₂ 𝔭 h𝔭 h hα hα1

namespace V16

/-- **LEGACY (superseded by `V16.v16_of_hyps_rev5`, `TreeS/FinalTB4.lean`, which discharges the hypothesis `hV12t` by
`energyLemmaTopG_nonHilbert`; `v16_of_hyps_rev5` is proved from this theorem, so it stays).**
**V16 (REV4)**: the final theorem from the four remaining node statements. -/
theorem v16_of_hyps_rev4 (hpint : PintStatementOFor IsEnergyExponent) (hsel : OSelectable)
    (hV12t : EnergyLemmaTopGStatementFor NonHilbertExp) (hTree : TreeLemmaStatementRev2) : V16Statement := by
  have hV12 : EnergyLemmaStatementR := energyLemmaO hpint (engBound_of_B5_D engLeTailMass) hsel
  have hV12tG : EnergyLemmaTopGStatement := energyLemmaTopG_of_two hV12t
  refine v16_of_energy engFam engFamI (fun _ 𝔭 => fullInts 𝔭) (fun _ _ => tileInts)
    (fun u => 33 * Rof u + 2) (fun u hu => by linarith [four_le_Rof hu]) ?_ ?_
  · intro u hu 𝔭 h𝔭
    exact ⟨fullInts_contain 𝔭, engFam_mono u 𝔭, energyTail_engFam_D engLeTailMass engTopLeTailMass hu h𝔭,
      energyStepG_engFamR hV12 hV12tG hu h𝔭, energyTree_engFam hTree hu h𝔭⟩
  · intro u hu 𝔭 h𝔭
    exact ⟨tileInts_scale, engFamI_mono u 𝔭, energyTail_engFamI_D engLeTailMass hu h𝔭,
      energyStep_engFamI hV12 hu h𝔭, energyTree_engFamI treeLemmaSingleScale hu h𝔭⟩

/-- **LEGACY (superseded by `V16.v16_of_hyps_rev5_nonHilbert`, `TreeS/FinalTB4.lean`, which also discharges `hV12t`).**
**V16 (REV4), with the Hilbert case of `pint` discharged**: only the non-Hilbert part of V11 remains. -/
theorem v16_of_hyps_rev4_nonHilbert (hpint : PintStatementOFor NonHilbertExp) (hsel : OSelectable)
    (hV12t : EnergyLemmaTopGStatementFor NonHilbertExp) (hTree : TreeLemmaStatementRev2) : V16Statement :=
  v16_of_hyps_rev4
    (PintStatementOFor.of_union pint_two_O_statement hpint fun s qX h => by
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr h)
    hsel hV12t hTree

end V16

end PrimeBHT.TimeFrequency.X2
