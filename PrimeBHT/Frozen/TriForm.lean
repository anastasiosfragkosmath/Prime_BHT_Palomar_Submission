module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Fin.VecNotation
public import PrimeBHT.Frozen.TimeInt
public import PrimeBHT.Frozen.Pairing

/-!
# Frozen: `PrimeBHT.Statements.triForm`

The definition exactly as the author approved it (ruling R16, 2026-11-09) before any proof used it.
It is the only declaration in this file, and it is not edited.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- The model form `Λ_P(h₁, h₂, h₃) = ∑_{t ∈ P} |I_t|^{-1/2} ∏_{k} |⟨h_k, φ_{t,k}⟩|` (BD26 L621; real-valued and
nonnegative). `φ t k` is the packet of the tri-tile `t` in slot `k`. -/
def triForm (P : Finset (ℤ × ℤ × ℤ)) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ)
    (h : Fin 3 → ℝ → ℂ) : ℝ :=
  ∑ t ∈ P, (volume (timeInt t)).toReal ^ (-(1 : ℝ) / 2) * ∏ k, ‖pairing (h k) (φ t k)‖

end PrimeBHT.Statements
