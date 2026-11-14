-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import PrimeBHT.Frozen.YNorm
public import PrimeBHT.Frozen.TensorFun
public import PrimeBHT.Frozen.TensorFourier
public import PrimeBHT.Frozen.MultiplierForm
import PrimeBHT.Proof.X2

/-!
# Frozen: `PrimeBHT.Statements.t_finiteBV`

The statement exactly as the author approved it (ruling R11, 2026-11-09) before any proof was
written. It is the only declaration in this file; only the proof between the `FROZEN_ANCHOR`
marker comments is filled in afterwards. While the state is `DRAFT_SORRY` the body is the single
authorized `by sorry`, and the statement is frozen but unproved: nothing may consume it.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate ContDiff

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- **`t:finiteBV` (lines 974-1020), all-multi-index form (ruling R8).**
For every `1 < u < ∞` and every sequence of bounds `A : ℕ → ℝ` there is a constant `C = C(u, A)`
(independent of `P`, of `Π`, of `m`, of the test functions) such that for all `P ≥ 1`, all
multipliers `m` smooth on `ℝ ∖ {0}` with `sup_{t ≠ 0} |t|^j |m^{(j)}(t)| ≤ A_j` for every `j`, all
forms `Π` (linear, linear, conjugate-linear) and every `CT` bounding `Π` in the sense
`|Π(F,G,H)| ≤ CT ‖F‖_{L²(Y_P)} ‖G‖_{L²(Y_P)} ‖H‖_{L^u(Y_P)}`, and all tensor Schwartz functions
`F_i = ∑_A f_{i,A}(x) e(A y/P)`: the integrand of `Λ_m^Π` is integrable and
`|Λ_m^Π(F₁,F₂,F₃)| ≤ C · CT · ‖F₁‖_{L²_x L²_y} ‖F₂‖_{L²_x L²_y} ‖F₃‖_{L^∞_x L^u_y}`.
The mixed norms are `eLpNorm` (values in `[0, ∞]`) of `x ↦ ‖F_i(x; ·)‖_{L^s_y(Y_P)}` on `ℝ` with
Lebesgue measure; `L^∞_x` is the essential supremum. -/
theorem t_finiteBV : ∀ u : ℝ, 1 < u → ∀ A : ℕ → ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℕ) [NeZero P] (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
      (m : ℝ → ℂ), ContDiffOn ℝ ∞ m {0}ᶜ →
      (∀ j : ℕ, ∀ t : ℝ, t ≠ 0 → |t| ^ j * ‖iteratedDeriv j m t‖ ≤ A j) →
      ∀ CT : ℝ, (∀ F G H : ZMod P → ℂ, ‖T F G H‖ ≤ CT * yNorm 2 F * yNorm 2 G * yNorm u H) →
      ∀ f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ),
        Integrable (fun ξ : ℝ × ℝ => m (ξ.2 - ξ.1) * T (tensorFourier f₁ ξ.1) (tensorFourier f₂ ξ.2) (tensorFourier f₃ (ξ.1 + ξ.2))) volume ∧
        ‖multiplierForm m T f₁ f₂ f₃‖ₑ ≤ ENNReal.ofReal (C * CT) *
          eLpNorm (fun x : ℝ => yNorm 2 (tensorFun f₁ x)) 2 volume *
          eLpNorm (fun x : ℝ => yNorm 2 (tensorFun f₂ x)) 2 volume *
          eLpNorm (fun x : ℝ => yNorm u (tensorFun f₃ x)) ⊤ volume :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact PrimeBHT.Proof.t_finiteBV
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end PrimeBHT.Statements
-- FROZEN_ANCHOR_SUFFIX_END
