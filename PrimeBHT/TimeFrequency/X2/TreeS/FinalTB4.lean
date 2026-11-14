module

public import PrimeBHT.TimeFrequency.X2.TreeS.Final
public import PrimeBHT.TimeFrequency.X2.TopEnergy.MainNH

/-!
# X2 / V16 with TB-4 discharged

`v16_of_hyps_rev5`: the final V16 theorem `v16_of_hyps_rev4` with its hypothesis `hV12t` (TB-4, V12-top at slot 3)
discharged by `energyLemmaTopG_nonHilbert`; and the variant with the Hilbert case of `pint` discharged.  Remaining
hypotheses: `hpint` (V11, slot 3), `hsel` (`OSelectable`), `hTree` (V15).
-/

@[expose] public section

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.V16

theorem v16_of_hyps_rev5_nonHilbert (hpint : PintStatementOFor NonHilbertExp) (hsel : OSelectable)
    (hTree : TreeLemmaStatementRev2) : V16Statement :=
  v16_of_hyps_rev4_nonHilbert hpint hsel energyLemmaTopG_nonHilbert hTree

end PrimeBHT.TimeFrequency.X2.V16
