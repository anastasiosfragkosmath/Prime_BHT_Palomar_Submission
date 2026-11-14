module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Data.Finsupp.Indicator
public import PrimeBHT.Frozen.PsiK
public import PrimeCarleson.Frozen.BlockWeight

/-!
# Frozen: `PrimeBHT.Statements.uOp`

The definition exactly as the author approved it (ruling R10, 2026-11-09) before any proof used it.
It is the only declaration in this file, and it is not edited.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- The unsmoothed truncated long-scale operator (lines 625-627, with `a_Q = ⌈Q^τ⌉` of line 678)
`U^J_{Q;τ}(f, g)(x) = ∑_{Q^τ ≤ k ≤ J} ∑_n ψ_k(n) w_Q(n) f(x - n) g(x + n)` for finitely supported
`f, g`, where `w_Q(n) = Λ_Q(|n|)` is `PrimeCarleson.blockWeight (Finset.Ioc (Q / 2) Q) n` (the paper's
`Λ_Q` of line 351, even in `n`). For a cutoff `χ` the `n`-family has finite support, so `∑'` is the
genuine finite sum. -/
def uOp (χ : ℝ → ℝ) (Q : ℕ) (τ : ℝ) (J : ℕ) (f g : ℤ →₀ ℂ) (x : ℤ) : ℂ :=
  ∑ k ∈ Finset.Icc ⌈(Q : ℝ) ^ τ⌉₊ J,
    ∑' n : ℤ, ((psiK χ k (n : ℝ) : ℝ) : ℂ) *
      PrimeCarleson.blockWeight (Finset.Ioc (Q / 2) Q) n * f (x - n) * g (x + n)

end PrimeBHT.Statements
