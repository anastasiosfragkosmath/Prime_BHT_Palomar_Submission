module

public import PrimeBHT.TimeFrequency.X2.Pint.PowFamily
public import PrimeBHT.TimeFrequency.X2.Pint.PointwisePJ
public import PrimeBHT.TimeFrequency.X2.Classes

/-!
# X2, V11 / TB-4 shared core, part 3: Theorem I (interpolation for families of single kernel operators) — STATEMENT

`docs/audits/X2-V11-TB4-plan.md` §4c.  The objects:

* `bil a b = P⁻¹ ∑_y a y * b y`, the BILINEAR pairing on `Y_P` (holomorphic in both arguments; `yPair` is conjugate-linear in
  the second and cannot be used in an analytic family); Hölder: `‖bil a b‖ ≤ yNorm p a * yNorm p' b`;
* `stepFun E v`: the step function `w ↦ ∑_k 1_{E k}(w) • v k` (`E` pairwise disjoint measurable sets of finite measure, `v k`
  vectors of `Y_P`): the class of test functions for which the analytic family is a FINITE sum of entire functions
  (`famStep`), so that no parametric integral is differentiated;
* `kernelOp K F x y = ∫ w, K x w * F w y`: a scalar kernel operator acting fibrewise; with `∫ ‖K x w‖ dw ≤ Cinf` it is bounded
  on `L^∞(L^{s₀})` pointwise (the `re z = 0` endpoint);
* `TheoremI`: for a finite family of such operators with the Hilbert endpoint in HLC's intersection form
  `(∑_i ‖S_i G‖²_{L²(L²)})^{1/2} ≤ A ‖G‖_{L^∞(L²)} + B₂ ‖G‖_{L²(L²)}` (for all step functions `G`), the slot-3 bound
  `∑_i ‖S_i F‖^{qX}_{L^{qX}(L^s)} ≤ Cinf^{qX-2} (A B^{qX/2} + B₂ mixedPow^{1/2})²` for step functions `F` with `yNorm s (F w) ≤ B`.

The proof (plan §4c): for each `i, x` take `h` norming `S_i F x` in `L^s(Y)`, `Φ(z) := bil (S_i (famStep … z) x) (famVec s' α β 0 0 h z)`;
`Φ` is a finite sum of products of entire functions (`famStep` is a finite sum, `kernelOp` of a step function is
`∑_k (∫_{E k} K x) • famVec (v k) z`), bounded on the closed strip (`norm_famVec_apply` with `re z ∈ [0,1]`); `‖Φ(it)‖ ≤ Cinf`
(Hölder at `(s₀, s₀')` and `yNorm_famVec` on both families), `‖Φ(1+it)‖ ≤ yNorm 2 (S_i (famStep (1+it)) x)` (Hölder at `(2,2)`),
`Φ θ = yNorm s (S_i F x)` (`famVec_theta`).  `exists_pointwisePJ` gives `yNorm s (S_iF x)^{qX} ≤ Cinf^{qX-2} ∫ yNorm 2 (S_i famStep(1+it) x)² dν₁(t)`;
integrate in `x`, sum over `i`, Tonelli, the Hilbert endpoint for `G = famStep (1+it)` (a step function with
`yNorm 2 (G w) = yNorm s (F w)^{qX/2}`, `t`-independent, `yNorm_famVec`), and `∫ yNorm 2 (G w)² = mixedPow qX s F`.
NOT YET PROVED (this file: definitions and the statement only; sizes in the plan).
-/

@[expose] public noncomputable section

open MeasureTheory Complex
open scoped ENNReal
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Pint

variable {P : ℕ} [NeZero P]

/-- The bilinear pairing `P⁻¹ ∑_y a y * b y` on `Y_P` (no conjugation). -/
def bil (a b : ZMod P → ℂ) : ℂ := (P : ℂ)⁻¹ * ∑ y, a y * b y

/-- A step function `w ↦ ∑_k 1_{E k}(w) • v k`. -/
def stepFun {κ : Type*} [Fintype κ] (E : κ → Set ℝ) (v : κ → ZMod P → ℂ) : ℝ → ZMod P → ℂ :=
  fun w y => ∑ k, (E k).indicator (fun _ => (1 : ℂ)) w * v k y

/-- A scalar kernel operator acting fibrewise on `ℝ → Y_P → ℂ`. -/
def kernelOp (K : ℝ → ℝ → ℂ) (F : ℝ → ZMod P → ℂ) : ℝ → ZMod P → ℂ :=
  fun x y => ∫ w, K x w * F w y

/-- Admissible step data: pairwise disjoint measurable sets of finite measure. -/
def IsStepData {κ : Type*} [Fintype κ] (E : κ → Set ℝ) : Prop :=
  (∀ k, MeasurableSet (E k)) ∧ (∀ k, volume (E k) < ⊤) ∧ Pairwise fun k k' => Disjoint (E k) (E k')

/-- **Theorem I (statement).**  `Cinf`: the `L¹` kernel bound; `A, B₂`: the Hilbert endpoint constants (HLC intersection
form); `(s, qX)` non-Hilbert energy exponents; the conclusion is the slot-3 `pint`-form before the `ε`-optimization.

**WARNING: THIS PROP IS FALSE AS PRINTED (hand-checked counterexample, not formalized); DO NOT BUILD ON IT.**  It is stated with Bochner integrals, which are `0` for
non-integrable integrands: for `K x w = k(x) · 1_{[0,1]}(w)` with `k(x) = (1+|x|)^{-1/2}` the Hilbert hypothesis holds
with `A = B₂ = 0` (the outer `x`-integral in the hypothesis is of a non-integrable function, hence `0`) while the
left-hand side of the conclusion is positive.  Replaced by the corrected statements `Pint.theoremI` (`Pint/TheoremI.lean`) and `Pint.theoremI_meas`
(`Pint/TheoremIMeas.lean`) (operator sides as `∫⁻ ofReal`, the `L¹` bound as `∫⁻ ‖·‖ₑ`, jointly strongly measurable
kernels).  No built declaration consumes `Pint.TheoremI`; it is kept only so that old references compile. -/
def TheoremI (P : ℕ) [NeZero P] {ι κ : Type*} [Fintype ι] [Fintype κ] (K : ι → ℝ → ℝ → ℂ) (Cinf A B₂ s qX : ℝ) : Prop :=
  (∀ i x, ∫ w, ‖K i x w‖ ≤ Cinf) →
  (∀ (E : κ → Set ℝ) (v : κ → ZMod P → ℂ), IsStepData E →
    ∀ B₀ : ℝ, (∀ w, yNorm 2 (stepFun E v w) ≤ B₀) →
      (∑ i, ∫ x, yNorm 2 (kernelOp (K i) (stepFun E v) x) ^ 2) ≤
        (A * B₀ + B₂ * (∫ x, yNorm 2 (stepFun E v x) ^ 2) ^ ((1 : ℝ) / 2)) ^ 2) →
  ∀ (E : κ → Set ℝ) (v : κ → ZMod P → ℂ), IsStepData E → ∀ B : ℝ, (∀ w, yNorm s (stepFun E v w) ≤ B) →
    (∑ i, ∫ x, yNorm s (kernelOp (K i) (stepFun E v) x) ^ qX) ≤
      Cinf ^ (qX - 2) * (A * B ^ (qX / 2) + B₂ * (∫ x, yNorm s (stepFun E v x) ^ qX) ^ ((1 : ℝ) / 2)) ^ 2

end PrimeBHT.TimeFrequency.X2.Pint
