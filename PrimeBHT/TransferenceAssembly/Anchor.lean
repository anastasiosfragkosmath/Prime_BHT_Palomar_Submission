module

public import PrimeBHT.PeriodicBlock
public import PrimeBHT.Lift
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# N40 (`t:finiteBV`): the time-frequency anchor X2, as a `Prop` (not proved)

* A tensor Schwartz function on `ℝ × Y_P` is given by coefficients `f : ZMod P → 𝓢(ℝ, ℂ)`:
  `F(x; y) = ∑_{A ∈ Y_P} f_A(x) e(A y / P)` (`tensorFun`), with partial Fourier transform
  `F̂(ξ; y) = ∑_A f̂_A(ξ) e(A y / P)` (`tensorFourier`), `f̂(ξ) = ∫ f(x) e(-xξ) dx` (Mathlib's `𝓕`).
  Here `e(A y / P) = ZMod.stdAddChar (A * y)`.
* `Π` is complex-linear in slots 1, 2 and conjugate-linear in slot 3
  (`(ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ`).
* `multiplierForm m Π f₁ f₂ f₃ = ∫∫ m(ξ₂ - ξ₁) Π(F̂₁(ξ₁;·), F̂₂(ξ₂;·), F̂₃(ξ₁+ξ₂;·)) dξ₁ dξ₂`.

`BilinearVVBound` is `t:finiteBV` (blueprint N40). The three suprema of the statement (the
operator norm `‖Π‖` on `L² × L² × L^u(Y_P)`, the seminorm `S_ν(m)`, and
`‖F₃‖_{L^∞_x(ℝ; L^u_y(Y_P))}`) are stated in the equivalent "every upper bound" form: for every
`CT`, `Sm`, `M₃` bounding them, the inequality holds with `CT`, `Sm`, `M₃` in place of the
suprema. The `L²(Y_P)` norm inside `‖Π‖` is `PeriodicBlock.l2` (`√(𝔼_y ‖F y‖²)`), the mixed
norms are `Lift.mixedNormR`, `Lift.yNorm` (normalized counting measure on `Y_P`).

The constant `C` depends only on `u`, and `ν` on nothing (`∃ ν` first): in particular `C` is
independent of `P`.

The seminorm is the blueprint's finite-order form
`S_ν(m) = max_{0 ≤ j ≤ ν} sup_{t ≠ 0} |t|^j |∂^j m(t)|`. DPLMV (Theorem 1.4) state the decay
condition for all multi-indices; that all-multi-index form is the intended frozen form of the
anchor, the finite-order form here is the quantitative version used by the source (blueprint N40,
watch item (i)).
-/

@[expose] public section

namespace PrimeBHT.TransferenceAssembly

open MeasureTheory PrimeBHT.PeriodicBlock PrimeBHT.Lift
open scoped FourierTransform SchwartzMap ComplexConjugate

/-- `F(x; y) = ∑_{A ∈ Y_P} f_A(x) e(A y / P)`. -/
noncomputable def tensorFun {P : ℕ} [NeZero P] (f : ZMod P → 𝓢(ℝ, ℂ)) (x : ℝ) (y : ZMod P) : ℂ :=
  ∑ A : ZMod P, f A x * ZMod.stdAddChar (A * y)

/-- `F̂(ξ; y) = ∑_{A ∈ Y_P} f̂_A(ξ) e(A y / P)`. -/
noncomputable def tensorFourier {P : ℕ} [NeZero P] (f : ZMod P → 𝓢(ℝ, ℂ)) (ξ : ℝ) (y : ZMod P) : ℂ :=
  ∑ A : ZMod P, 𝓕 (⇑(f A)) ξ * ZMod.stdAddChar (A * y)

/-- The form `Λ_m^Π(F₁,F₂,F₃) = ∫∫ m(ξ₂ - ξ₁) Π(F̂₁(ξ₁;·), F̂₂(ξ₂;·), F̂₃(ξ₁+ξ₂;·)) dξ₁ dξ₂`. -/
noncomputable def multiplierForm {P : ℕ} [NeZero P] (m : ℝ → ℂ)
    (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
    (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) : ℂ :=
  ∫ ξ : ℝ × ℝ, m (ξ.2 - ξ.1) *
    T (tensorFourier f₁ ξ.1) (tensorFourier f₂ ξ.2) (tensorFourier f₃ (ξ.1 + ξ.2))

end PrimeBHT.TransferenceAssembly
