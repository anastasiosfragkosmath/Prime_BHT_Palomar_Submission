module

public import PrimeBHT.BlockSum
public import PrimeBHT.TransferenceAssembly.BlockTransfer
public import PrimeBHT.KernelFourier
public import PrimeBHT.FinalGlue
public import PrimeBHT.Bridge.Key0

/-!
# `p:key0` from X2 (conditional)

`PrimeBHT.TransferenceAssembly.key0Statement_of_x2`: assuming `X2Statement` (the type of the frozen
`t_finiteBV`), `Key0Statement χ` holds for every `χ` (the corrected `p:key0`, blueprint N26). The chain:
a smoothing function `φ` with `∫ φ = 1` and `φ̂` supported in `[-1, 1]` (`KernelFourier.exists_isSmoother`),
the per-block transference `blockTransferBound_of_x2`, and the block sum / assembly
`BlockSum.p_key0_of_blockTransfer`.

`frozen_key0_body_of_x2` states the result in the shape of the frozen `p_key0` (via `Bridge.key0Statement_iff`),
without mentioning the quarantined frozen theorem: when X2 is proved, the provider of `p_key0` is this theorem
applied to the proof of X2. Names end in `_of_x2` because they are conditional.
-/

@[expose] public noncomputable section

namespace PrimeBHT.TransferenceAssembly

/-- **`p:key0` from X2.** -/
theorem key0Statement_of_x2 (hx2 : X2Statement) (χ : ℝ → ℝ) : PrimeBHT.FinalGlue.Key0Statement χ := by
  obtain ⟨φ, hφ⟩ := PrimeBHT.KernelFourier.exists_isSmoother (c := 1) one_pos
  have h := PrimeBHT.BlockSum.p_key0_of_blockTransfer (φ := φ) (c := 1) hφ.integral_eq_one
    hφ.fourier_eq_zero
    (fun χ hχ τ ε ps hε0 hετ _ hps1 hps2 =>
      blockTransferBound_of_x2 hx2 (by norm_num) hχ hε0 (by linarith) hps1 hps2)
  intro hχ
  exact h χ hχ

/-- **`p:key0` from X2, in the shape of the frozen theorem** (the cutoff predicate is the frozen one). -/
theorem frozen_key0_body_of_x2 (hx2 : X2Statement) (χ : ℝ → ℝ) (hχ : PrimeBHT.Statements.IsCutoff χ) :
    PrimeBHT.Bridge.FrozenKey0Body χ :=
  (PrimeBHT.Bridge.key0Statement_iff.1 (key0Statement_of_x2 hx2 χ)) hχ

end PrimeBHT.TransferenceAssembly
