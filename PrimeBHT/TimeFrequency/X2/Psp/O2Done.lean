module

public import PrimeBHT.TimeFrequency.X2.Psp.O2bOutMain

/-!
# X2, V13 O2: `overlap_O2 : OverlapO2Ovg 𝔭` for every class

The concrete overlapping projection estimate (O2) for `G = ovG` (`X2/Psp/OverlapLean.lean`), from the fine part (`O2Fine`, `O2Final`, V05) and the
outside part `outBound_main` (`O2bOutMain`, V13) via `overlap_O2_of_out` (`O2Close`).  Conditional on the margin `𝔭.N/8 + 3 ≤ 𝔭.D` (inside the statement).
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- **(O2) for the concrete `G = ovG`**, every class `𝔭` (conditional on `𝔭.N/8 + 3 ≤ 𝔭.D`). -/
theorem overlap_O2 (𝔭 : Params) : OverlapO2Ovg 𝔭 :=
  overlap_O2_of_out (outConst_nonneg 𝔭) (outBound_main 𝔭)

end PrimeBHT.TimeFrequency.X2
