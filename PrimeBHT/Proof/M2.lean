module

public import PrimeBHT.TimeFrequency.X1.FromM1
public import PrimeBHT.Frozen.TriRestrictedEps

/-!
# Provider of `PrimeBHT.Statements.bht_real_smooth` (M2, the real-line smooth-truncation BHT)

The frozen anchor `PrimeBHT/Frozen/BhtRealSmooth.lean` is sealed with the body
`by exact PrimeBHT.Proof.bht_real_smooth`. The proof is the chain of `PrimeBHT/TimeFrequency/X1/RealLine`:
the sealed M1(ε) (`PrimeBHT.Statements.tri_restricted_eps`) ⇒ hull bound ⇒ restricted type ⇒ model bound ⇒
Theorem Θ ⇒ Theorem B ⇒ M2 (`m2_of_theoremB`). `Transfer.M2Prop` is, by `rfl` (`scripts/interface_check.sh`),
the type of the frozen theorem.
-/

@[expose] public section

namespace PrimeBHT.Proof

theorem bht_real_smooth : PrimeBHT.TimeFrequency.Transfer.M2Prop :=
  PrimeBHT.TimeFrequency.RealLine.m2_of_theoremB
    (fun _ hχ _ _ _ hp hq hr hr' =>
      PrimeBHT.TimeFrequency.RealLine.theoremB_of_m1 PrimeBHT.Statements.tri_restricted_eps hχ hp hq hr hr')

end PrimeBHT.Proof
