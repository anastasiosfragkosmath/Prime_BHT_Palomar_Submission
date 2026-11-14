module

public import PrimeBHT.TimeFrequency.X2.Disc.Final
public import PrimeBHT.TimeFrequency.X2.TreeS.Final
public import PrimeBHT.TimeFrequency.X2.TreeS.FinalTB4
public import PrimeBHT.TimeFrequency.X2.Pint.PintNH
public import PrimeBHT.TimeFrequency.X2.Psp.O2Done
public import PrimeBHT.TimeFrequency.X2.EnergyLemma.KernelInductReal
public import PrimeBHT.TimeFrequency.X2.Psp.OverlapAssemble

/-!
# X2: the final assembly `x2Statement_of_hyps`

`x2Statement_of_hyps` : `PrimeBHT.TransferenceAssembly.X2Statement` (literally the type of the frozen `t_finiteBV`) from

* `hpint : PintStatementOFor NonHilbertExp` (V11, non-Hilbert part of the true `pint`),
* `hsel : OSelectable` (the selection lemma of the V12 energy lemma),
* `hO2 : ∀ 𝔭, 𝔭.Admissible → 𝔭.tree.Admissible → OverlapO2Ovg 𝔭` (V13, the overlapping projection (O2) for the concrete `G = ovG`).

(V12-top, slot 3, is discharged by `energyLemmaTopG_nonHilbert`.)  The second profile `η'` of the tree class is carried by the parameters
(`ProfileOK 𝔭`, part of `V16Params` and of the witness of `DiscretizationStatement`; supplied by `discretization_params_good`).

Chain: `V16.v16_of_hyps_rev5_nonHilbert` (with `treeLemmaRev2_of_O2`) gives `V16Statement`, and `x2Statement_of_v16` (V05
`discretization`, V17, V03) gives the frozen statement.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- **X2 from the node statements `hpint`, `hsel`, `hO2`.** -/
theorem x2Statement_of_hyps (hpint : PintStatementOFor NonHilbertExp) (hsel : OSelectable)
    (hO2 : ∀ 𝔭 : Params, 𝔭.Admissible → 𝔭.tree.Admissible → OverlapO2Ovg 𝔭) :
    PrimeBHT.TransferenceAssembly.X2Statement :=
  x2Statement_of_v16 (V16.v16_of_hyps_rev5_nonHilbert hpint hsel (treeLemmaRev2_of_O2 hO2))

/-- **X2 from the two remaining node statements** (V11 is proved: `pint_nonHilbert_O`). -/
theorem x2Statement_of_two (hsel : OSelectable)
    (hO2 : ∀ 𝔭 : Params, 𝔭.Admissible → 𝔭.tree.Admissible → OverlapO2Ovg 𝔭) :
    PrimeBHT.TransferenceAssembly.X2Statement :=
  x2Statement_of_hyps pint_nonHilbert_O hsel hO2

/-- **X2 from the single remaining node statement `OSelectable`** (V11 and O2 are proved:
`pint_nonHilbert_O`, `overlap_O2`). -/
theorem x2Statement_of_selectable (hsel : OSelectable) :
    PrimeBHT.TransferenceAssembly.X2Statement :=
  x2Statement_of_two hsel (fun 𝔭 _ _ => overlap_O2 𝔭)

/-- **X2, UNCONDITIONAL** (`PrimeBHT.TransferenceAssembly.X2Statement` is literally the type of the frozen `t_finiteBV`):
`OSelectable` is proved by the leaf-peeling kernel theorem (`KernelInductReal.oSelectable_proved`), V11 by `pint_nonHilbert_O`,
O2 by `overlap_O2`. -/
theorem x2Statement_final : PrimeBHT.TransferenceAssembly.X2Statement :=
  x2Statement_of_selectable oSelectable_proved

end PrimeBHT.TimeFrequency.X2
