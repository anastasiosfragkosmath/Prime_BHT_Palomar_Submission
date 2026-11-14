module

public import PrimeBHT.TimeFrequency.X2.Psp.OverlapConstruct

/-!
# X2, V13 part 3 (B): the exact (O1)-(O3) contract for the overlapping projection, and what is proved

`docs/audits/X2-V13-route-check.md` §1.2, §2.6.  The overlapping projection delivered to V15 is the JOINT statement
`OverlapPsp` below: one function `G` with (O1) (`L^∞`/support bound), (O2) (the `μ_σ`-weighted error bound for `F - G`) and
(O3) (the single-scale bound for `G`).

**Remark (statement-level finding).** (O1) alone is VACUOUS: `G = 0` satisfies it (`overlapO1`, proved below).  The content is the
conjunction with (O2): `G` must approximate `F` on every tree layer.  Consumers (V15, V15s) must use `OverlapPsp`, never
`OverlapO1`.  The non-vacuous O1 is `overlap_O1_of_coeff` (`Psp/OverlapConstruct.lean`): for ANY finite set `L` of lattice scales
and ANY coefficient families with `‖c‖_{L^s(Y)} ≤ B · engTop`, the MTT2 function `G = Π̃F - Σ cφ` is measurable, bounded by
`C · engTop` and supported in `3 I_t`.

The concrete construction that proves `OverlapPsp` (NOT in Lean yet; see the report) is MTT2 §8 on the lattice: `T_σ = tmult
(lowSym θ σ)`, `S_σ = T_σ - T_{σ+J}`, `θ = ξ_T f_k`, `L` = the lattice scales `≤ top` meeting `∂Ẽ`, `Π̃F = overlapPi`, bumps
`leftPhi`/`rightPhi`, and the coefficients `c^ℓ_{σ,x} = 2^{-σ} ∫ (S̃_σ^T H(· - x)) · S_σ F`, `c^r_{σ,x} = - 2^{-σ} ∫ (S̃_σ^T H(· - x)) · S_σ F`
(`H` the Heaviside function, `S̃_σ` the Littlewood-Paley projection with symbol `lowProfile(u/2) - lowProfile(2^{J+1} u)` in
`u = (ξ - θ) 2^σ`, which is `1` on the support of the symbol of `S_σ` and `0` near `u = 0`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-- The weight `w_{I₀}(y) = ⟨(y - c_{I₀})/|I₀|⟩^{-K₀}` for `I₀ = dyadicInt σ v` (centre `2^σ (v + 1/2)`). -/
def ovWeight (K₀ : ℝ) (σ v : ℤ) (y : ℝ) : ℝ :=
  jb ((y - (2 : ℝ) ^ σ * ((v : ℝ) + 1 / 2)) / (2 : ℝ) ^ σ) ^ (-K₀)

/-- The two-exponent local bound on the dyadic interval `I₀ = dyadicInt σ v` with relative factor `a`:
`sup_{I₀} ‖U‖_{L^s(Y)} ≤ C a E` (`p = ∞`) and `‖1_{I₀} ‖U‖_{L^s(Y)}‖_{L^q} ≤ C a |I₀|^{1/q} E` (`p = q`). -/
def OvBound {P : ℕ} [NeZero P] (s q C a : ℝ) (E : ℝ≥0∞) (σ v : ℤ) (U : ℝ → ZMod P → ℂ) : Prop :=
  (∀ x ∈ dyadicInt σ v, ENNReal.ofReal (yNorm s (U x)) ≤ ENNReal.ofReal (C * a) * E) ∧
    eLpNorm (fun x => (dyadicInt σ v).indicator (fun x => yNorm s (U x)) x) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (C * a * ((2 : ℝ) ^ σ) ^ (1 / q)) * E

end PrimeBHT.TimeFrequency.X2
