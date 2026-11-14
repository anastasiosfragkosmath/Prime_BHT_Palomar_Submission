module

public import PrimeBHT.TimeFrequency.X2.V16.HullBound
public import PrimeBHT.TimeFrequency.X2.EngTail.Concrete
public import PrimeBHT.TimeFrequency.X2.EnergyLemma
public import PrimeBHT.TimeFrequency.X2.EnergyLemma.Defs
public import PrimeBHT.TimeFrequency.X2.EnergyLemma.B5Bridge

/-!
# X2, node V16 (REV3): the concrete instantiation and `v16_of_hyps_rev3`

**LEGACY / VACUOUS**: the theorem `v16_of_hyps_rev3` below is conditional on two FALSE Props (`PintStatement`,
`EnergyLemmaTopStatement`); the current final V16 theorems are `V16.v16_of_hyps_rev5` / `V16.v16_of_hyps_rev5_nonHilbert`
(`TreeS/FinalTB4.lean`).  The concrete instantiation of this file (`engFam`, `engFamI`, ...) is still used.

`docs/audits/X2-REV3-fat-top.md`.  The final theorem

`v16_of_hyps_rev3 (hpint : PintStatement) (hB5 : EngLeTailMassStatementD) (hV12t : EnergyLemmaTopStatement)
  (hTree : TreeLemmaStatementRev2) (hTreeS : TreeLemmaSingleScaleStatement) : V16Statement`

lists EXACTLY the unproved node statements of V16:

* `PintStatement` (V11, the nested `pint` for all energy exponents; inside V12: `energyLemma`);
* `EngLeTailMassStatementD` (B5, corrected; reduced to `TreeLqBound` by `engLeTailMass_of_treeLqBound`);
* `EnergyLemmaTopStatement` (V12-top, about the fat top energy `engTop`);
* `TreeLemmaStatementRev2` (V15, energies `engV` with the fat top energy);
* `TreeLemmaSingleScaleStatement` (V15s, single-scale trees, tile energies).

PROVED inputs: B5-top (`engTopLeTailMass`), V12 (`energyLemma`, from `PintStatement` and B5 via `engBound_of_B5_D`),
the halving step `engV_stepR`, B7 (`main_estimate`), B10, B11 (`inside_le_of_energy`, with `EnergyTreeSS`), B12
(`v16_of_energy`).  B10 runs on the family `engFam` (tile + fat top energies, `fullInts`, `IntsContain`); B11 on the family
`engFamI` (tile energies, `tileInts`, `IntsScale`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- The margin of the repaired energy lemma (`EnergyLemmaStatementR`) in the class `𝔭.tree`:
`(𝔭.tree.loc.decN 10).Admissible`. -/
theorem V16Params.tree_loc_decN_admissible {u : ℝ} (hu : 1 < u) {𝔭 : Params} (h : V16Params u 𝔭) :
    (𝔭.tree.loc.decN 10).Admissible := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, hN, hD, -⟩ := h
  have hg : 132 ≤ ⌈33 * Rof u⌉₊ := by
    have h4R : 4 ≤ Rof u := four_le_Rof hu
    have : (132 : ℝ) ≤ ⌈33 * Rof u⌉₊ := le_trans (by linarith) (Nat.le_ceil _)
    exact_mod_cast this
  have hN8 : classFloor + 2 * locLoss + 10 ≤ 𝔭.N / 8 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    unfold v16Decay at hN; omega
  have hD' : classFloor + 2 * locLoss ≤ 𝔭.D := by
    unfold v16Decay at hD; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Params.decN, Params.loc_J, Params.loc_N, Params.loc_D, Params.loc_δ, Params.loc_β, Params.loc_C,
      Params.tree_J, Params.tree_N, Params.tree_D, Params.tree_δ, Params.tree_β, Params.tree_C] <;>
    first | assumption | omega


/-- `EngBoundStatement` (the consequence `eng ≲ 1` of B5 used by the energy lemma) from the CORRECTED B5. -/
theorem engBound_of_B5_D (hB5 : EngLeTailMassStatementD) : EngBoundStatement := by
  intro 𝔭 h𝔭 s qX hX
  have hN : (3 : ℝ) + 100 ≤ 𝔭.N := by
    have h1 : 400 ≤ 𝔭.N := h𝔭.2.1
    have : (400 : ℝ) ≤ 𝔭.N := by exact_mod_cast h1
    linarith
  have hD : (3 : ℝ) + 100 ≤ 𝔭.D := by
    have h1 : 400 ≤ 𝔭.D := h𝔭.2.2.1
    have : (400 : ℝ) ≤ 𝔭.D := by exact_mod_cast h1
    linarith
  obtain ⟨C, hC0, hC⟩ := hB5 𝔭 h𝔭 hX.one_lt_s' hX.two_le_qX (le_refl 3) hN hD
  have hM : (1 : ℝ) < 3 := by norm_num
  refine ⟨C * V16.tailConst 3, mul_nonneg hC0 (V16.tailConst_pos hM).le, ?_⟩
  intro P _ Qs hQ Cs hbox k F hFm hbd
  refine (hC P Qs hQ Cs hbox k F hFm hbd).trans ?_
  rw [ENNReal.ofReal_mul hC0]
  refine mul_le_mul' le_rfl (iSup₂_le fun R _ => ENNReal.ofReal_le_ofReal ?_)
  refine V16.tailMass_le_tailConst hM ?_ fun y => ?_
  · have : (volume R.I).toReal = (2 : ℝ) ^ R.box.scale := toReal_volume_dyadicInt _ _
    rw [this]
    exact zpow_pos (by norm_num) _
  · rw [Real.norm_of_nonneg (yNorm_nonneg' _ _)]
    exact hbd y

namespace V16

/-- B11's family: `EnergyStep` for the tile family `engFamI` needs ONLY the repaired V12 (no V12-top). -/
theorem energyStep_engFamI (hV12 : EnergyLemmaStatementR) {u : ℝ} (hu : 1 < u) {𝔭 : Params}
    (h𝔭 : V16Params u 𝔭) : EnergyStep (engFamI u 𝔭) u 𝔭 := by
  have hR4 : 4 ≤ Rof u := four_le_Rof hu
  have hs := fun v : Fin 3 => hV12 𝔭.tree (h𝔭.tree_loc_decN_admissible hu) (s := slotExp u v)
    (qX := qX (Rof u) v) (q := V16.qPlus (Rof u) v) (isEnergyExponent_slot hu v) (qX_lt_qPlus hR4 v)
  choose C hC0 hC using hs
  refine ⟨∑ v, C v, Finset.sum_nonneg fun v _ => hC0 v, ?_⟩
  intro P _ Qs hQ Cs₀ Cs hbox hTC hres h hm hbdd v
  obtain ⟨ts, h1, h2, h3⟩ := hC v P Qs hQ Cs₀ Cs hbox hTC hres v (h v) (hm v) (hbdd v)
  have hle : ENNReal.ofReal (C v) ≤ ENNReal.ofReal (∑ v, C v) :=
    ENNReal.ofReal_le_ofReal
      (Finset.single_le_sum (f := C) (fun v _ => hC0 v) (Finset.mem_univ v))
  exact ⟨ts, h1, h2.trans (mul_le_mul_left hle _), fun W hW => (h3 W hW).trans (mul_le_mul_left hle _)⟩

/-- B11's family: the single-scale tree lemma V15s gives `EnergyTreeSS (engFamI u 𝔭)`. -/
theorem energyTree_engFamI (hTree : TreeLemmaSingleScaleStatement) {u : ℝ} (hu : 1 < u) {𝔭 : Params}
    (h𝔭 : V16Params u 𝔭) : EnergyTreeSS (engFamI u 𝔭) u 𝔭 := by
  have hR4 : 4 ≤ Rof u := four_le_Rof hu
  obtain ⟨C, hC0, hC⟩ := hTree 𝔭 h𝔭.1 h𝔭.tree_loc_admissible.2 hu (by linarith : 2 < Rof u)
  refine ⟨C, hC0, ?_⟩
  intro P _ T CT hT Qs hQ Tr t hg hss hbox χ m hmd h hm hbdd
  have hbdd2 : ∀ k, ∃ B, ∀ x, yNorm 2 (h k x) ≤ B := by
    intro k
    obtain ⟨B, hB⟩ := exists_yNorm_two_le P (slotExp_pos hu k)
    exact ⟨B, fun x => hB _ (hbdd k x)⟩
  exact hC P T CT hT Qs hQ Tr t hg hss hbox χ m hmd h hm hbdd2

end V16

end PrimeBHT.TimeFrequency.X2
