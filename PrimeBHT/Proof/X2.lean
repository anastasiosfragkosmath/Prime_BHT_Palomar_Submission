module

public import PrimeBHT.TransferenceAssembly.X2
public import PrimeBHT.TimeFrequency.X2.Final
public import PrimeBHT.TimeFrequency.X2.EnergyLemma.KernelInductReal

/-!
# Provider of `PrimeBHT.Statements.t_finiteBV` (X2, the vector-valued BHT form on `ℝ × ℤ/P`)

The frozen anchor `PrimeBHT/Frozen/FiniteBV.lean` is sealed with the body `by exact PrimeBHT.Proof.t_finiteBV`.
The proof is `PrimeBHT.TimeFrequency.X2.x2Statement_of_selectable` (`X2/Final.lean`) applied to the proof of the selection lemma
`OSelectable` (the V12 energy lemma's selection step): V11 (`pint_nonHilbert_O`, `Pint/PintNH.lean`) and the overlapping
projection (O2) (`overlap_O2`, `Psp/O2Done.lean`) are already inside `x2Statement_of_selectable`.
`PrimeBHT.TransferenceAssembly.X2Statement` is, by `rfl` (`scripts/interface_check.sh`), the type of the frozen theorem.

This module imports the whole X2 tree (`PrimeBHT.TimeFrequency.X2.Final`; no module of that closure imports a frozen
theorem module or a `PrimeBHT.Proof.*` module), and it is imported only by the frozen anchor.
-/

@[expose] public section

namespace PrimeBHT.Proof

/-- **X2** (`t:finiteBV`): the type is `X2Statement`, literally the type of the frozen theorem.  The argument is the proof of the
last remaining hypothesis of the X2 chain: `hsel : OSelectable`, proved as `oSelectable_proved`
(`EnergyLemma/KernelInductReal.lean`: leaf-peeling induction for kernels of the destruction digraph of a product of two forests).
No placeholder, no hypothesis, no new binder. -/
theorem t_finiteBV : PrimeBHT.TransferenceAssembly.X2Statement :=
  PrimeBHT.TimeFrequency.X2.x2Statement_of_selectable
    PrimeBHT.TimeFrequency.X2.oSelectable_proved      -- hsel

end PrimeBHT.Proof
