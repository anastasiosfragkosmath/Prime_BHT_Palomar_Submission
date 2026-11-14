module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import PrimeBHT.Frozen.Psi

/-!
# Frozen: `PrimeBHT.Statements.psiK`

The definition exactly as the author approved it (ruling R10, 2026-11-09) before any proof used it.
It is the only declaration in this file, and it is not edited.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- `ψ_k(t) = 2^{-k} ψ(t 2^{-k})` (line 383). -/
noncomputable def psiK (χ : ℝ → ℝ) (k : ℕ) (t : ℝ) : ℝ := psi χ (t / 2 ^ k) / 2 ^ k

end PrimeBHT.Statements
