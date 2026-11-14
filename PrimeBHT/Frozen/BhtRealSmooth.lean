-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import PrimeBHT.Frozen.IsCutoff
public import PrimeBHT.Frozen.BhtKernelR
public import PrimeBHT.Frozen.BhtOpR
import PrimeBHT.Proof.M2

/-!
# Frozen: `PrimeBHT.Statements.bht_real_smooth`

The statement exactly as the author approved it (ruling R15, 2026-11-09) before any proof was
written. It is the only declaration in this file; only the proof between the `FROZEN_ANCHOR`
marker comments is filled in afterwards. While the state is `DRAFT_SORRY` the body is the single
authorized `by sorry`, and the statement is frozen but unproved: nothing may consume it.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- **M2 (the real-line smooth-truncation bilinear Hilbert transform; BD26 Theorems 1.1, 1.2; LT99; DPLMV
Theorem 1.4 at scalar spaces).** For every cutoff `χ` and every `1 < p, q`, `1/r = 1/p + 1/q`, `2/3 < r` there is
a constant `C` (depending on `χ, p, q` only) such that for all real `0 < λ < μ` (uniformly in the two scales)
and all Schwartz `f, g : ℝ → ℂ`, `‖x ↦ ∫ f(x-y) g(x+y) K_{λ,μ}(y) dy‖_{L^r(ℝ)} ≤ C ‖f‖_{L^p(ℝ)} ‖g‖_{L^q(ℝ)}`.
The `L^s(ℝ)` quasi-norms are `eLpNorm` for Lebesgue measure (for `s < 1` this is `(∫ |F|^s)^(1/s)`). -/
theorem bht_real_smooth : ∀ χ : ℝ → ℝ, IsCutoff χ →
    ∀ p q r : ℝ, 1 < p → 1 < q → 1 / r = 1 / p + 1 / q → 2 / 3 < r →
      ∃ C : ℝ, ∀ lam mu : ℝ, 0 < lam → lam < mu → ∀ f g : SchwartzMap ℝ ℂ,
        eLpNorm (bhtOpR χ lam mu f g) (ENNReal.ofReal r) volume ≤
          ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume *
            eLpNorm g (ENNReal.ofReal q) volume :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact PrimeBHT.Proof.bht_real_smooth
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end PrimeBHT.Statements
-- FROZEN_ANCHOR_SUFFIX_END
