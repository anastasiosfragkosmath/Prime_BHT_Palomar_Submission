module

public import PrimeBHT.TimeFrequency.X2.EnergyLemma.Geom

/-!
# X2, node V12: the three-phase selection (MTT02 Lemma 7.7, HLC energy lemma)

A `k`-lacunary tree with top `(W, ξ)` splits into the tiles strictly to the right of `ξ` (`PlusAt`), strictly to the
left (`MinusAt`) and the rest (`MidAt`: `ξ ∈ 3ω_k(R)`, hence a single box).  Three greedy selections remove maximal
trees in the order of

* `VPlus`  : the canonical top frequency `fupOf` (the largest feasible one) MAXIMAL first;
* `VMinus` : `fdnOf` (the smallest feasible one) MINIMAL first;
* `VZero`  : the (common) scale of the box, LARGEST (narrowest frequency interval) first,

each among the candidates `θ < topNorm` inside the current residual.  `selection`: each phase gives a nested-form
strongly disjoint family; at the end no candidate of any type is left, hence `eng ≤ 3θ` (triangle inequality of
`Split.lean`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

section Defs

variable (k : Fin 3)

end Defs

variable {k : Fin 3}

/-! ## Candidates -/

section Cand

variable {P : ℕ} [NeZero P] {𝔭 : Params} {s : ℝ} {F : ℝ → ZMod P → ℂ} {qX : ℝ} {θ : ℝ≥0∞}

/-! ## Pairs of a selection -/

/-! ## The halving -/

theorem topNorm_empty {P : ℕ} [NeZero P] (𝔭 : Params) {s : ℝ} (hs : 0 < s) (k : Fin 3)
    (F : ℝ → ZMod P → ℂ) (t : Top) (q : ℝ) : topNorm 𝔭 s k F ∅ t q = 0 := by
  refine le_antisymm (topNorm_le_of_forall fun ψ m _ => ?_) zero_le
  rw [treeOpNorm_empty s q t ψ m F hs]

end Cand

/-! ## The selection -/

end PrimeBHT.TimeFrequency.X2
