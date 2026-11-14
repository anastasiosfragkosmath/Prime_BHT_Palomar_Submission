module

public import PrimeBHT.TimeFrequency.X1.Transfer.Assemble
public import PrimeBHT.Frozen.BhtRealSmooth

/-!
# Provider of `PrimeBHT.Statements.x1_bht_smooth` (X1, the discrete smooth-truncation BHT)

The frozen anchor `PrimeBHT/Frozen/X1.lean` is sealed with the body `by exact PrimeBHT.Proof.x1_bht_smooth`.
The proof is the transference from the real line (`PrimeBHT/TimeFrequency/X1/Transfer`) applied to the sealed M2
(`PrimeBHT.Statements.bht_real_smooth`). `Interface.X1Statement.X1Statement` is, by `rfl`
(`scripts/interface_check.sh`), the type of the frozen theorem.
-/

@[expose] public section

namespace PrimeBHT.Proof

theorem x1_bht_smooth : PrimeBHT.Interface.X1Statement.X1Statement :=
  PrimeBHT.TimeFrequency.Transfer.x1_of_m2 PrimeBHT.Statements.bht_real_smooth

end PrimeBHT.Proof
