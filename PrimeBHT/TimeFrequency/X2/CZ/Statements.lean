module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import PrimeBHT.Frozen.TensorFun
public import PrimeBHT.Frozen.YNorm

/-!
# V08 (f): statements for scalar Mikhlin multipliers `T_σ ⊗ Id` on `L^q(ℝ; L^s(Y_P))`

This file is the statement layer of the vector-valued Calderón-Zygmund toolbox V08 of
`docs/x2-blueprint.md`, restricted to what V14 (new route), V13 and the interpolation node V11 consume
(`docs/audits/X2-V14-route-check.md`): **a scalar Fourier multiplier `σ` of Mikhlin type acting
coefficientwise on `X`-valued functions**, `X = L^s(Y_P)` (the finite lattice `Y_P = ZMod P` with
normalized counting measure, norm `PrimeBHT.Statements.yNorm s`) or `X = H = L²(Y_P)` (`s = 2`).
Nothing in this file is proved; every `Prop` below is the statement of a theorem of the later modules of
`PrimeBHT/TimeFrequency/X2/CZ/`.  The frozen data used are `tensorFun` and `yNorm` (ruling R11); the file
does not import `PrimeBHT.Frozen.FiniteBV` nor any `PrimeBHT.Proof.*` module.

## Objects

* `multOp σ g = 𝓕⁻(σ · 𝓕 g)`: the scalar multiplier `T_σ` (Mathlib's Fourier transform
  `𝓕 g(ξ) = ∫ g(x) e^{-2πixξ} dx`; the inverse is Lean's integral).  For `g` Schwartz and `σ` bounded
  measurable `σ · 𝓕 g` is integrable, so `multOp σ g` is the honest continuous function and no value is
  an artefact of the convention "the integral of a non-integrable function is `0`".
* `tensorMult σ f` = `(T_σ ⊗ Id)(tensorFun f)`, the coefficientwise action
  `Σ_A (T_σ f_A)(x) e(Ay/P)` on the frozen tensor Schwartz functions `tensorFun f`, `f : ZMod P → 𝓢(ℝ, ℂ)`
  (the same definition as the frozen `tensorFun`, with `f A` replaced by `T_σ (f A)`).  It acts fibrewise
  in `y` (`MixedNorm.lean`: `tensorMult_eq_multOp_fibre`).
* `IsMikhlin a₀ B σ`: the Mikhlin class `σ ∈ C^{a₀}(ℝ∖{0})`, `|ξ|^a |σ^{(a)}(ξ)| ≤ B` for all `a ≤ a₀`,
  `ξ ≠ 0` (the value `σ 0` is arbitrary, a null set).  The single bound `B` stands for the blueprint's
  family `C_a`, `a ≤ a₀`: one takes `B = max_a C_a`, and the constants below are *linear* in `B` (by
  homogeneity this is the same as "constants depending only on `C_a`").
* `mixedENorm q s F = ‖x ↦ yNorm s (F x)‖_{L^q(ℝ)} ∈ [0, ∞]`, the mixed norm `‖F‖_{L^q(ℝ; L^s(Y_P))}`,
  as an `eLpNorm` (an extended real: this is deliberate, see the remark on integrability below).

## Statements (all with the quantifier order `∃ C` before `∀ P`)

* (a) `VectorMikhlinStrongStatement a₀`: for all `1 < q, s < ∞` there is `C = C(q, s)` such that for every
  `P`, every `B` and every `σ` in the Mikhlin class,
  `‖(T_σ ⊗ Id) F‖_{L^q(ℝ; L^s(Y_P))} ≤ C B ‖F‖_{L^q(ℝ; L^s(Y_P))}` for all tensor Schwartz `F`.
  The bound is in `[0, ∞]`: the output is a priori only continuous, bounded and in `L²` (not in `L^q` for
  `q < 2`), and a real-valued Bochner integral of a non-integrable function is `0`, so a bound written with
  the real-valued `Lift.mixedNormR` would be vacuous in exactly the cases where it is a theorem.
* (b) `VectorMikhlinWeakStatement a₀`: for `1 < s < ∞` there is `C = C(s)` with
  `t · |{x : |T_σ F(x)|_{L^s(Y)} > t}| ≤ C B ‖F‖_{L^1(ℝ; L^s(Y))}` for all `t > 0`.
* (d) (upper half; the equivalence, i.e. the reverse inequality, is a later phase)
  `VectorMikhlinSquareStatement a₀`: for a finite family `(n_j)_{j<N}` of symbols such that every
  unimodular combination `Σ_j η_j n_j` is in the Mikhlin class with constant `B` (this is what the
  random-phase multipliers `Σ_j η_j Ψ(2^{-Jj}·)` of V14 satisfy, with `B` independent of `N`),
  `‖(Σ_j |T_{n_j} F(x, ·)|²)^{1/2}‖_{L^q(ℝ; L^s(Y))} ≤ C B ‖F‖_{L^q(ℝ; L^s(Y))}`.  For `s = 2` this is
  V14 Step 0: `‖(Σ_j ‖T_{n_j} g‖_H²)^{1/2}‖_{L^q(ℝ)} ≲ B ‖g‖_{L^q(ℝ;H)}`.
* The scalar input `ScalarMikhlinStrong` / `ScalarMikhlinWeak` (the classical Mikhlin-Hörmander theorem
  for `L^q(ℝ)`; this is what `Basecase.lean` takes as a hypothesis (`…_of_scalar`) and what the later
  modules `Hormander.lean`, `CZDecomp.lean`, … prove).

The constants are allowed to depend on `(q, s)` (and on `a₀`, which is fixed once); blowing up as
`q, s → 1, ∞` is unavoidable.  Locally uniform dependence on `s` (needed by V11, which uses
`s ∈ {u₀, 2}` only) is not claimed: V11 needs two instances only.

## Design note (the route to these statements)

1. *Hörmander condition.* `σ ∈ IsMikhlin 3 B` ⇒ the kernel `K = 𝓕⁻σ` (a tempered distribution; a function
   away from `0`) satisfies `|K(x)| ≲ B/|x|`, `|K'(x)| ≲ B/x²`, hence `∫_{|x|>2|y|} |K(x-y) - K(x)| dx ≲ B`.
   Proof: dyadic decomposition `σ = Σ_j σ ψ(2^{-j}·)`, integration by parts in `ξ` for each dyadic piece
   (the mechanism of X1's R3, `X1/RealLine/LittlewoodPaley*`), uniformly in the symbol constants.
2. *Scalar theory.* `‖T_σ‖_{L²→L²} ≤ ‖σ‖_∞` by Plancherel (`Basecase.lean`); the Hörmander condition gives
   weak `(1,1)` (Calderón-Zygmund decomposition) and Marcinkiewicz gives `1 < q ≤ 2`; duality gives `q ≥ 2`.
3. *Base case `q = s`.* `L^s(ℝ; L^s(Y)) = L^s(ℝ × Y)` and Fubini: `T_σ ⊗ Id` acts fibrewise in `y`
   (the frozen measure on `Y_P` is `P⁻¹ Σ_y`), so the scalar bound at exponent `s` gives (a) at `q = s`
   with the same constant (`Basecase.lean`, `…_of_scalar`).  For `s = 2` the scalar bound is Plancherel
   and is proved there unconditionally.
4. *Bochner weak `(1,1)`.* CZ decomposition of `f ∈ L¹(ℝ; X)` at height `t` applied to `|f|_X`; the good
   part by the base case, the bad part by the scalar Hörmander condition and `‖∫ K f‖_X ≤ ∫ |K| |f|_X`.
5. *Marcinkiewicz* (the Carleson clone's `exists_hasStrongType_real_interpolation`) between weak `(1,1)`
   and `L^s(X)`: `1 < q ≤ s`; *duality* `L^q(ℝ; L^s(Y))' = L^{q'}(ℝ; L^{s'}(Y))` and `(T_σ ⊗ Id)^* =
   T_{σ̄(-·)} ⊗ Id` (again Mikhlin) for `q ≥ s`.
6. *Mikhlin-class bookkeeping* for `Σ_j η_j Ψ(2^{-Jj}·)` (bounded overlap, scale invariance of
   `|ξ|^a |σ^{(a)}|`): a separate statement of V14 Step 0, not of this file.

## Module inventory of `PrimeBHT/TimeFrequency/X2/CZ/` (phase 1; import order)

* `Statements.lean` (this file): definitions and the target `Prop`s, no proofs.
* `MixedNorm.lean`: mixed-norm API: `Lift.yNorm` bridge, Fubini identification `q = s`, Hilbert case
  `q = s = 2`, fibrewise action `tensorMult_eq_multOp_fibre`, Hölder half of the duality (e)
  (`ofReal_norm_mixedPairing_le`) and the norming statement `MixedNormDuality` (statement only).
* `Basecase.lean`: Plancherel for `L¹ ∩ L²` (`eLpNorm_fourierInv_eq_of_integrable`), scalar `L²` bound,
  the Fubini step (`mixedENorm_tensorMult_diag_le`), `vectorMikhlinStrong_two_two` (unconditional, `X = H`),
  `vectorMikhlinStrong_diag_of_scalar` (conditional on the scalar bound), consistency checks
  `multOp_one`, `tensorMult_one`.
* `Dyadic.lean`: smooth dyadic partition of unity `∑_{j ∈ ℤ} ψ(2^{-j}ξ) = 1`.
* `DyadicSum.lean`: `∑_{j ∈ ℤ} min(a 2^j, b 2^{-j}) ≤ 4 √(ab)`.
* `Pieces.lean`: dyadic pieces `σ ψ(r·)` of a Mikhlin symbol: Leibniz derivative bounds, `L¹` bounds,
  kernel decay `(2π|x|)^k |𝓕⁻(piece)(x)| ≲ B r^{k-1}`, derivative of the kernel of a piece.
* `Hormander.lean`: the kernel `K = ∑_j K_j`: `|K(x)| ≲ B/|x|`, `|K(x-y) - K(x)| ≲ B|y|/x²`, and the
  Hörmander integral condition `lintegral_kernelSum_sub_le` (`a₀ = 3`, constants independent of `σ`, `B`).

`a₀` is fixed once for the project; every proof above needs `a₀ = 3` at most (pointwise `|K'(x)| ≲ x⁻²`
by three integrations by parts); the proof of the Hörmander L¹ condition by Plancherel needs only `a₀ = 2`
(or `1` with fractional Sobolev norms).  The class is monotone: `IsMikhlin a₀' B σ → IsMikhlin a₀ B σ` for
`a₀ ≤ a₀'`, so the statements for `a₀ = 3` imply them for every larger `a₀` (V14 has all derivatives).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap ContDiff

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

open PrimeBHT.Statements

/-! ## Objects -/

/-- The scalar Fourier multiplier `T_σ g = 𝓕⁻(σ · 𝓕 g)` (Mathlib's convention `𝓕 g(ξ) = ∫ g(x) e^{-2πixξ}dx`,
`𝓕⁻ h(x) = ∫ h(ξ) e^{2πixξ}dξ`).  Meaningful (the integral converges) when `σ · 𝓕 g` is integrable, e.g.
`g` Schwartz and `σ` bounded measurable. -/
def multOp (σ g : ℝ → ℂ) : ℝ → ℂ :=
  𝓕⁻ (fun ξ => σ ξ * 𝓕 g ξ)

/-- `(T_σ ⊗ Id)` applied to the tensor Schwartz function `tensorFun f = Σ_A f_A ⊗ e_A`: coefficientwise,
`Σ_A (T_σ f_A)(x) e(Ay/P)`.  It equals `T_σ` applied to each fibre `x ↦ F(x, y)`
(`MixedNorm.lean`). -/
def tensorMult {P : ℕ} [NeZero P] (σ : ℝ → ℂ) (f : ZMod P → 𝓢(ℝ, ℂ)) (x : ℝ) (y : ZMod P) : ℂ :=
  ∑ A : ZMod P, multOp σ (f A) x * ZMod.stdAddChar (A * y)

/-- The Mikhlin class of order `a₀` with constant `B`: `σ` is `C^{a₀}` on `ℝ ∖ {0}` and
`|ξ|^a |σ^{(a)}(ξ)| ≤ B` for `a ≤ a₀`, `ξ ≠ 0`. -/
def IsMikhlin (a₀ : ℕ) (B : ℝ) (σ : ℝ → ℂ) : Prop :=
  ContDiffOn ℝ (a₀ : WithTop ℕ∞) σ {0}ᶜ ∧
    ∀ a : ℕ, a ≤ a₀ → ∀ ξ : ℝ, ξ ≠ 0 → |ξ| ^ a * ‖iteratedDeriv a σ ξ‖ ≤ B

/-- The mixed norm `‖F‖_{L^q(ℝ; L^s(Y_P))} = ‖x ↦ yNorm s (F x)‖_{L^q(ℝ)} ∈ [0, ∞]`. -/
def mixedENorm {P : ℕ} [NeZero P] (q s : ℝ) (F : ℝ → ZMod P → ℂ) : ℝ≥0∞ :=
  eLpNorm (fun x => yNorm s (F x)) (ENNReal.ofReal q) volume

/-- The lattice square function in `y` of a finite family `h_j : Y_P → ℂ`: `(Σ_j |h_j(y)|²)^{1/2}`. -/
def latticeSquare {P : ℕ} {N : ℕ} (h : Fin N → ZMod P → ℂ) (y : ZMod P) : ℝ :=
  (∑ j, ‖h j y‖ ^ 2) ^ (2 : ℝ)⁻¹

/-! ## The scalar input (classical Mikhlin-Hörmander theorem on `L^q(ℝ)`) -/

/-! ## The vector-valued statements -/

/-- (a) strong type `(q, s)` of `T_σ ⊗ Id` with constant `C B`, for every `P` and every Mikhlin symbol. -/
def VectorMikhlinStrong (a₀ : ℕ) (q s C : ℝ) : Prop :=
  ∀ (P : ℕ) [NeZero P] (B : ℝ) (σ : ℝ → ℂ), IsMikhlin a₀ B σ → ∀ f : ZMod P → 𝓢(ℝ, ℂ),
    mixedENorm q s (tensorMult σ f) ≤ ENNReal.ofReal (C * B) * mixedENorm q s (tensorFun f)

/-- (b) weak type `(1,1)` of `T_σ ⊗ Id` into `L^{1,∞}(ℝ; L^s(Y_P))`: with the extended-real norm
`mixedENorm 1 s (tensorFun f) = ∫ ‖F(x)‖_{L^s(Y)} dx`. -/
def VectorMikhlinWeak (a₀ : ℕ) (s C : ℝ) : Prop :=
  ∀ (P : ℕ) [NeZero P] (B : ℝ) (σ : ℝ → ℂ), IsMikhlin a₀ B σ → ∀ f : ZMod P → 𝓢(ℝ, ℂ),
    ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * volume {x : ℝ | t < yNorm s (tensorMult σ f x)} ≤
        ENNReal.ofReal (C * B) * mixedENorm 1 s (tensorFun f)

/-- (d), upper half: the lattice square function of a finite family of multipliers whose unimodular
combinations are all Mikhlin with the same constant `B` is bounded on `L^q(ℝ; L^s(Y_P))`. -/
def VectorMikhlinSquare (a₀ : ℕ) (q s C : ℝ) : Prop :=
  ∀ (P : ℕ) [NeZero P] (N : ℕ) (n : Fin N → ℝ → ℂ) (B : ℝ),
    (∀ η : Fin N → ℂ, (∀ j, ‖η j‖ = 1) → IsMikhlin a₀ B (fun ξ => ∑ j, η j * n j ξ)) →
      ∀ f : ZMod P → 𝓢(ℝ, ℂ),
        eLpNorm (fun x => yNorm s (fun y => latticeSquare (fun j => tensorMult (n j) f x) y))
            (ENNReal.ofReal q) volume ≤
          ENNReal.ofReal (C * B) * mixedENorm q s (tensorFun f)

/-- **Target (a)**: `T_σ ⊗ Id` is bounded on `L^q(ℝ; L^s(Y_P))`, `1 < q, s < ∞`, with `C = C(q, s)`
independent of `P` and of the symbol (beyond the factor `B`). -/
def VectorMikhlinStrongStatement (a₀ : ℕ) : Prop :=
  ∀ q s : ℝ, 1 < q → 1 < s → ∃ C : ℝ, VectorMikhlinStrong a₀ q s C

/-- **Target (b)**: weak `(1,1)` of `T_σ ⊗ Id` into `L^{1,∞}(ℝ; L^s(Y_P))`, `C = C(s)`. -/
def VectorMikhlinWeakStatement (a₀ : ℕ) : Prop :=
  ∀ s : ℝ, 1 < s → ∃ C : ℝ, VectorMikhlinWeak a₀ s C

/-- **Target (d), upper half** (V14 Step 0 for `s = 2`). -/
def VectorMikhlinSquareStatement (a₀ : ℕ) : Prop :=
  ∀ q s : ℝ, 1 < q → 1 < s → ∃ C : ℝ, VectorMikhlinSquare a₀ q s C

/-- **Target (f)** (blueprint V08(f)), the parts (a) and (b); (d) is `VectorMikhlinSquareStatement`. -/
def VectorMikhlinStatement (a₀ : ℕ) : Prop :=
  VectorMikhlinStrongStatement a₀ ∧ VectorMikhlinWeakStatement a₀

end PrimeBHT.TimeFrequency.X2.CZ
