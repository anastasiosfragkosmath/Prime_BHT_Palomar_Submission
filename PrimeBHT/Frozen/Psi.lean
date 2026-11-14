module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Frozen: `PrimeBHT.Statements.psi`

The definition exactly as the author approved it (ruling R10, 2026-11-09) before any proof used it.
It is the only declaration in this file, and it is not edited.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- `ψ(t) = (χ(t) - χ(2t)) / t` with `ψ(0) = 0` (line 378; Lean's `x / 0 = 0` gives `ψ(0) = 0`). -/
noncomputable def psi (χ : ℝ → ℝ) (t : ℝ) : ℝ := (χ t - χ (2 * t)) / t

end PrimeBHT.Statements
