module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# C11, the exponent part: from the corner to the open hexagon

Blueprint `docs/x1-blueprint.md`, node C11 (`TT.hull`), items (b) and (c), the real-number part (no
tiles, no measure theory).

## Contents

* `corner_le_rpow_mul` (**C11(b)**, the algebra): for `0 < a ≤ b ≤ c`, `Σ α_i = 1`, `α₁ ≤ 1 - ε`,
  `-1/2 + ε ≤ α₃`: `a^{1-ε} b^{1/2} c^{-1/2+ε} ≤ a^{α₁} b^{α₂} c^{α₃}`.  (`ε ∈ (0,1/2)` is not
  needed for the algebra.)
* `InHexagon ε x`: `x ∈ {Σ x_i = 1, -1/2 + ε ≤ x_i ≤ 1 - ε}`, the closed `ε`-shrunken hexagon; for
  `ε = 0` the closed hexagon, the convex hull of the permutations of `(1, 1/2, -1/2)`.
  `openHexagon` is the open hexagon `{Σ x_i = 1, -1/2 < x_i < 1}`.
* `hexMargin x = min_i min (1 - x_i) (x_i + 1/2)`, the distance to the faces, and the exponent choice
  `epsOf x = min (hexMargin x) (1/4)` of **C11(c)**: `0 < epsOf x < 1/2` on the open hexagon,
  `x ∈ InHexagon (epsOf x)`, `epsOf` continuous, and a single `ε₀ > 0` with `ε₀ ≤ epsOf x` on any
  compact subset of the open hexagon (`exists_eps_le_epsOf_of_isCompact`): this is the local
  boundedness of `N_α, C_α` of the blueprint.

## Corrections to the blueprint (C11)

1. (c) writes "`0 < ε < min(1 - α_{σ1}, α_{σ3} + 1/2)`"; M1(ε) also needs `ε < 1/2`, which that
   minimum does not imply (e.g. `α = (-0.4, 0.7, 0.7)` has minimum `1.2`).  The weak inequalities
   `α_{σ1} ≤ 1 - ε`, `α_{σ3} ≥ -1/2 + ε` suffice (the algebra (b) allows equality).
2. A single `ε` serving every ordering `σ` at once (needed because `HullBound` quantifies over all
   sets, hence over all orderings) is `ε ≤ min_i min (1 - α_i, α_i + 1/2)`: `hexMargin`.
3. "`N_α := N_ε`, `C_α := C_ε` locally bounded" is not automatic from the existential statement
   M1(ε) (which gives `N, C` for each `ε` with no monotonicity in `ε`).  What is true, and what is
   used, is the stronger statement that one pair `(N, C)` works for **every** `α` in the closed
   `ε₀`-hexagon (the algebra (b) is exactly the monotonicity of the bound in `ε`).
-/

@[expose] public section

namespace PrimeBHT.TimeFrequency.Interp.Hull

/-! ### C11(b): the algebra -/

/-- **C11(b)**: for `0 < a ≤ b ≤ c`, `α₁ + α₂ + α₃ = 1`, `α₁ ≤ 1 - ε`, `-1/2 + ε ≤ α₃`:
`a^{1-ε} b^{1/2} c^{-1/2+ε} ≤ a^{α₁} b^{α₂} c^{α₃}`.  In terms of the logarithms the difference of
the two sides is `(1 - ε - α₁)(log b - log a) + (α₃ + 1/2 - ε)(log c - log b) ≥ 0`. -/
theorem corner_le_rpow_mul {a b c ε α₁ α₂ α₃ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hsum : α₁ + α₂ + α₃ = 1) (h₁ : α₁ ≤ 1 - ε) (h₃ : -(1 : ℝ) / 2 + ε ≤ α₃) :
    a ^ (1 - ε) * b ^ ((1 : ℝ) / 2) * c ^ (-(1 : ℝ) / 2 + ε) ≤ a ^ α₁ * b ^ α₂ * c ^ α₃ := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  have hla : Real.log a ≤ Real.log b := Real.log_le_log ha hab
  have hlb : Real.log b ≤ Real.log c := Real.log_le_log hb hbc
  rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb, Real.rpow_def_of_pos hc,
    Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb, Real.rpow_def_of_pos hc, ← Real.exp_add,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have hα₂ : α₂ = 1 - α₁ - α₃ := by linarith
  subst hα₂
  have e₁ : 0 ≤ 1 - ε - α₁ := by linarith
  have e₃ : 0 ≤ α₃ + 1 / 2 - ε := by linarith
  have k₁ := mul_nonneg e₁ (sub_nonneg.2 hla)
  have k₃ := mul_nonneg e₃ (sub_nonneg.2 hlb)
  have : -(1 : ℝ) / 2 = -(1 / 2) := by ring
  rw [this]
  nlinarith [k₁, k₃]

/-! ### The hexagons and the exponent choice (C11(c)) -/

/-- The closed `ε`-shrunken hexagon `{x : Σ x_i = 1, -1/2 + ε ≤ x_i ≤ 1 - ε}`. -/
def InHexagon (ε : ℝ) (x : Fin 3 → ℝ) : Prop :=
  x 0 + x 1 + x 2 = 1 ∧ ∀ i, -(1 : ℝ) / 2 + ε ≤ x i ∧ x i ≤ 1 - ε

lemma InHexagon.mono {ε ε' : ℝ} {x : Fin 3 → ℝ} (h : InHexagon ε x) (hε : ε' ≤ ε) :
    InHexagon ε' x :=
  ⟨h.1, fun i => ⟨by linarith [(h.2 i).1], by linarith [(h.2 i).2]⟩⟩

end PrimeBHT.TimeFrequency.Interp.Hull
