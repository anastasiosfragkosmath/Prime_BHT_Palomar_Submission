module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Fin.VecNotation
public import PrimeBHT.Frozen.IntervalCentre

/-!
# Frozen: `PrimeBHT.Statements.IsAdapted`

The definition exactly as the author approved it (ruling R16, 2026-11-09) before any proof used it.
It is the only declaration in this file, and it is not edited.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- `φ` is **adapted with exponent `N`** to the pair `(I, ω)` (BD26 L503-509, with the exponent `10` replaced by
`N`): `φ` is `C¹` and integrable (so that `𝓕 φ`, Mathlib's `Real.fourierIntegral` `𝓕 φ ξ = ∫ e^{-2πiξx} φ(x) dx`,
which is BD26's convention L499-501, is not a junk value), `𝓕 φ` vanishes outside `ω`, and the demodulated
function `φ̃(x) = e^{-2πi c(ω) x} φ(x)` satisfies `|φ̃^{(n)}(x)| ≤ |I|^{-n-1/2} (1 + |x - c(I)|/|I|)^{-N}` for
`n = 0, 1`, all `x`. `|I|` is the Lebesgue measure. -/
def IsAdapted (N : ℕ) (I ω : Set ℝ) (φ : ℝ → ℂ) : Prop :=
  ContDiff ℝ 1 φ ∧ Integrable φ ∧ (∀ ξ : ℝ, ξ ∉ ω → 𝓕 φ ξ = 0) ∧
  ∀ n : ℕ, n ≤ 1 → ∀ x : ℝ,
    ‖iteratedDeriv n (fun y : ℝ =>
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (intervalCentre ω : ℂ) * (y : ℂ))) * φ y) x‖ ≤
      (volume I).toReal ^ (-(n : ℝ) - 1 / 2) *
        (1 + |x - intervalCentre I| / (volume I).toReal) ^ (-(N : ℝ))

end PrimeBHT.Statements
