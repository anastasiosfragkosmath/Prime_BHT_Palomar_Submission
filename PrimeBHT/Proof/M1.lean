module

public import PrimeBHT.TimeFrequency.Tile.Assemble

/-!
# Provider of `PrimeBHT.Statements.tri_restricted_eps` (M1(ε), the tri-tile restricted-type estimate)

The frozen anchor `PrimeBHT/Frozen/TriRestrictedEps.lean` is sealed with the body
`by exact PrimeBHT.Proof.tri_restricted_eps`. The frozen statement has explicit binders `(ε) (hε) (hε')`, so this
export takes `ε` implicitly and the two hypotheses as `autoParam`s (`by assumption`): `exact` supplies them from
the binders of the frozen declaration, and the type of the conclusion is literally the frozen one
(`M1Statement` is its body, checked in `scripts/interface_check.sh`).

The proof is the tile core `PrimeBHT.TimeFrequency.Tile.*`: `exists_m1Statement` (assembly of the inside bound
`Inside.lean`, the outside bound `OutsideGlue.lean` and the normalization `Dilation.lean`) with
`N = ⌈1/(2ε)⌉ + 11`.

This module is imported only by the frozen anchor and by providers of sealed anchors that consume it through
the frozen export `PrimeBHT.Statements.tri_restricted_eps`.
-/

@[expose] public section

namespace PrimeBHT.Proof

theorem tri_restricted_eps {ε : ℝ} (hε : 0 < ε := by assumption) (hε' : ε < 1 / 2 := by assumption) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧ PrimeBHT.TimeFrequency.Tile.M1Statement ε N C :=
  PrimeBHT.TimeFrequency.Tile.exists_m1Statement hε (by linarith)

end PrimeBHT.Proof
