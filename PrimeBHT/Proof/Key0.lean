module

public import PrimeBHT.TransferenceAssembly.Key0OfX2
public import PrimeBHT.Bridge.Key0
public import PrimeBHT.Frozen.IsCutoff
public import PrimeBHT.Frozen.FiniteBV

/-!
# Provider of `PrimeBHT.Statements.p_key0` (the corrected `p:key0`, from the sealed X2)

The frozen anchor `PrimeBHT/Frozen/Key0.lean` is sealed with the body `by exact PrimeBHT.Proof.p_key0`.  The proof is
`PrimeBHT.TransferenceAssembly.frozen_key0_body_of_x2` (`TransferenceAssembly/Key0OfX2.lean`: smoothing function,
per-block transference, block sum) applied to the SEALED frozen theorem `PrimeBHT.Statements.t_finiteBV`
(`X2Statement` is, by `rfl`, its type).  The type of this export is the frozen type with the body written as
`PrimeBHT.Bridge.FrozenKey0Body χ` (checked equal by `rfl` in `scripts/interface_check.sh`).

This module reaches X2 only through the frozen export; it is imported only by the frozen anchor of `p_key0`.
-/

@[expose] public section

namespace PrimeBHT.Proof

/-- **`p:key0`** (corrected form), from the sealed X2. -/
theorem p_key0 : ∀ χ : ℝ → ℝ, PrimeBHT.Statements.IsCutoff χ → PrimeBHT.Bridge.FrozenKey0Body χ :=
  fun χ hχ => PrimeBHT.TransferenceAssembly.frozen_key0_body_of_x2 PrimeBHT.Statements.t_finiteBV χ hχ

end PrimeBHT.Proof
