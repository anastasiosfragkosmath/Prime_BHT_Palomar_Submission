module

public import PrimeBHT.TimeFrequency.X2.V16.Hyps

/-!
# X2, node V16: the concrete energy family of REV2 and the abstract hypotheses it satisfies

Instantiation of the abstract hypotheses of `V16/Hyps.lean` (`EnergyMono`, `EnergyTailBound`, `EnergyStep`,
`EnergyTree`, `IntsContain`, `IntsScale`) by the REV2 energies:

* `engFam u 𝔭` : `e P h v S := engV 𝔭 u (Rof u) v (h v) S` (`max` of `eng` and `engTop` in the class `𝔭.tree`);
* `fullInts 𝔭` : the tile intervals together with the top intervals `W` of the top data;
* `EnergyTree` from `TreeLemmaStatementRev2` (V15);
* `EnergyStep` from `engV_step` (V12 + V12-top, `X2/EnergyTop.lean`);
* `EnergyTailBound` from `EngLeTailMassStatement` (B5) and `EngTopLeTailMassStatement` (B5-top) at `M = 33 R + 2`;
* REV3: `IntsScale` is NOT satisfied by `fullInts` (the top data are sandwich-free); B11 uses the tile family
  (`V16/Final.lean`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.V16

/-- The concrete energy family: `engV` in the class `𝔭.tree` at the exponents `(2, 2, Rof u)`. -/
def engFam (u : ℝ) (𝔭 : Params) : EnergyFamily := fun _ _ h v S => engV 𝔭 u (Rof u) v (h v) S

/-- The admissible intervals of B5 for `engV`: tile intervals and top intervals (REV3: the `W ⊇ I_R` of the fat top data). -/
def fullInts (𝔭 : Params) : IntFamily :=
  fun Cs => tileInts Cs ∪ {W | ∃ ξ, IsTopDatum 𝔭.J Cs W ξ}

theorem fullInts_contain (𝔭 : Params) : IntsContain (fullInts 𝔭) := by
  intro Cs W hW
  rcases hW with ⟨R, hR, rfl⟩ | ⟨ξ, -, R, hR, h1, -⟩
  · exact ⟨R, hR, Set.Subset.rfl⟩
  · exact ⟨R, hR, h1⟩

theorem engFam_mono (u : ℝ) (𝔭 : Params) : EnergyMono (engFam u 𝔭) := by
  intro P _ h v S S' hSS
  exact engV_mono 𝔭 u (Rof u) v (h v) hSS

theorem energyTree_engFam (hTree : TreeLemmaStatementRev2) {u : ℝ} (hu : 1 < u) {𝔭 : Params}
    (h𝔭 : V16Params u 𝔭) : EnergyTree (engFam u 𝔭) u 𝔭 := by
  have hR4 : 4 ≤ Rof u := four_le_Rof hu
  obtain ⟨C, hC0, hC⟩ := hTree 𝔭 h𝔭.1 h𝔭.tree_loc_admissible.2 h𝔭.profileOK hu (by linarith : 2 < Rof u)
  refine ⟨C, hC0, ?_⟩
  intro P _ T CT hT Qs hQ Tr t hg _ hbox χ m hmd h hm hbdd
  have hbdd2 : ∀ k, ∃ B, ∀ x, yNorm 2 (h k x) ≤ B := by
    intro k
    obtain ⟨B, hB⟩ := exists_yNorm_two_le P (slotExp_pos hu k)
    exact ⟨B, fun x => hB _ (hbdd k x)⟩
  exact hC P T CT hT Qs hQ Tr t hg hbox χ m hmd h hm hbdd2

end PrimeBHT.TimeFrequency.X2.V16
