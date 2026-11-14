module

public import PrimeBHT.TimeFrequency.X2.EnergyLemma.Phase
public import PrimeBHT.TimeFrequency.X2.EnergyLemma.Split
public import PrimeBHT.TimeFrequency.X2.GoodTree

/-!
# X2, node V12: frequency geometry of the selection (nested strong disjointness)

Everything here uses only the fields (a), (b), (f), (h) of `IsRankOne` and `J ≥ 16`:

* `hull_nest`: `ω_k(B) ⊆ ω_k(B')`, `B ≠ B'` gives `B'.scale < B.scale` and `hull B ⊆ hull B'`
  (the common point is `c_k(B)/d_k`);
* `removal_disjoint` (MTT2 Lemma 7.7, "remove the maximal tree"): a tile `R'` of the residual, with a frequency
  interval strictly containing that of a tile `R` of the removed tree, has `I_{R'}` disjoint from the top;
* `plus_gap` / `minus_gap`: a tile `R` strictly on one side of the top frequency `ξ` (gap `3/4 ℓ_R`) and a tile `R'`
  of a later tree with `ω(R') ⊆ ω(R)` force `ξ' > ξ` (resp. `ξ' < ξ`);
* `mid_single_box`: a `k`-lacunary tree all of whose tiles have `ξ` in `3 ω_k` has a single box.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

theorem freqDir_pos (k : Fin 3) : 0 < freqDir k := by
  fin_cases k <;> simp [freqDir]

theorem freqDir_le_two (k : Fin 3) : freqDir k ≤ 2 := by
  fin_cases k <;> simp [freqDir]

/-! ## Frequency intervals -/

/-! ## The hull in normalized coordinates -/

theorem div_mem_hull (B : Box) (k : Fin 3) {x : ℝ} (h1 : B.centre k - 3 * (2 : ℝ) ^ (-B.scale) / 2 ≤ x)
    (h2 : x ≤ B.centre k + 3 * (2 : ℝ) ^ (-B.scale) / 2) : x / freqDir k ∈ B.hull := by
  have hd := freqDir_pos k
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
  have h3 : (3 : ℝ) ≤ hullDil := by unfold hullDil; norm_num
  have h1' : B.centre k - hullDil * (2 : ℝ) ^ (-B.scale) / 2 ≤ x := by nlinarith
  have h2' : x ≤ B.centre k + hullDil * (2 : ℝ) ^ (-B.scale) / 2 := by nlinarith
  unfold Box.hull
  rw [Set.mem_Icc]
  constructor
  · have : min (min ((B.centre 0 - hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir 0)
        ((B.centre 1 - hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir 1))
        ((B.centre 2 - hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir 2) ≤
        (B.centre k - hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir k := by
      fin_cases k
      · exact (min_le_left _ _).trans (min_le_left _ _)
      · exact (min_le_left _ _).trans (min_le_right _ _)
      · exact min_le_right _ _
    exact this.trans ((div_le_div_iff_of_pos_right hd).2 h1')
  · have : (B.centre k + hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir k ≤
        max (max ((B.centre 0 + hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir 0)
        ((B.centre 1 + hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir 1))
        ((B.centre 2 + hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir 2) := by
      fin_cases k
      · exact (le_max_left _ _).trans (le_max_left _ _)
      · exact (le_max_right _ _).trans (le_max_left _ _)
      · exact le_max_right _ _
    exact ((div_le_div_iff_of_pos_right hd).2 h2').trans this

theorem centre_mem_hull (B : Box) (k : Fin 3) : B.centre k / freqDir k ∈ B.hull := by
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
  exact div_mem_hull B k (by linarith) (by linarith)

/-! ## Removal of the maximal tree -/

/-! ## Sides of the top frequency -/

variable (k : Fin 3)

variable {k}

end PrimeBHT.TimeFrequency.X2
