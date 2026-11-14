module

public import PrimeBHT.TimeFrequency.X1.RealLine.Theta
public import PrimeBHT.TimeFrequency.X1.RealLine.KernelDecomposition
public import PrimeBHT.TimeFrequency.X1.Transfer.Assemble

/-!
# X1 from the tri-tile estimate M1(ε)

`PrimeBHT.TimeFrequency.x1_of_m1 : M1Prop → X1Statement`: assuming M1(ε) (`M1Prop`, the type of the frozen
`tri_restricted_eps`), the frozen X1 (`x1_bht_smooth`, as the Prop `X1Statement`) holds. The chain, every link
proved in this project without further hypotheses:

`M1(ε)` ⇒ hull bound (`Interp/Hull`) ⇒ restricted type ⇒ strong type for the model sum, i.e. the model bound
(`Interp/Hull/ModelBound`) ⇒ Theorem Θ (`X1/RealLine/Theta`, with the Gabor discretization of
`X1/RealLine/{Frame,Coefficients,ModelSum}`) ⇒ Theorem B (`X1/RealLine/LittlewoodPaley`) ⇒ M2
(`X1/RealLine/KernelDecomposition`) ⇒ X1 (`X1/Transfer`).

So X1 is reduced to M1(ε): what remains of X1 is the tile core proving `tri_restricted_eps`.
-/

@[expose] public section

namespace PrimeBHT.TimeFrequency

/-- **X1 from M1(ε).** -/
theorem x1_of_m1 (hM1 : PrimeBHT.TimeFrequency.Interp.Hull.M1Prop) :
    PrimeBHT.Interface.X1Statement.X1Statement :=
  PrimeBHT.TimeFrequency.Transfer.x1_of_m2
    (PrimeBHT.TimeFrequency.RealLine.m2_of_theoremB
      (fun _ hχ _ _ _ hp hq hr hr' => PrimeBHT.TimeFrequency.RealLine.theoremB_of_m1 hM1 hχ hp hq hr hr'))

end PrimeBHT.TimeFrequency
