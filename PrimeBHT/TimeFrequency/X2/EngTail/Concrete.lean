module

public import PrimeBHT.TimeFrequency.X2.EngTail.Eng
public import PrimeBHT.TimeFrequency.X2.V16.Concrete

/-!
# X2, node V16: `energyTail_engFam` with the corrected B5 / B5-top statements

`V16/Concrete.lean` derives `EnergyTailBound (engFam u 𝔭) (fullInts 𝔭) u 𝔭 (33 R + 2)` from the printed
`EngLeTailMassStatement` / `EngTopLeTailMassStatement`.  Those are false as printed (no derivative margin, see
`EngTail/Top.lean`).  This file gives the same derivation from the corrected statements `EngLeTailMassStatementD`,
`EngTopLeTailMassStatementD`; the derivative margin `v16Decay u ≤ 𝔭.D` (the class `𝔭.tree` has the same `D` as `𝔭`) is part of
`V16Params` (REV3), free for the discretization (`∀ N D ∃ 𝔭`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.V16

/-- The derivative margin of B5 at `M = 33 R + 2`: `M + 100 ≤ 𝔭.tree.D = 𝔭.D`. -/
theorem tail_derivs {u : ℝ} {𝔭 : Params} (hD : v16Decay u ≤ 𝔭.D) :
    (33 * Rof u + 2) + 100 ≤ ((𝔭.tree.D : ℕ) : ℝ) := by
  have h1 : (33 * Rof u : ℝ) ≤ ⌈33 * Rof u⌉₊ := Nat.le_ceil _
  have h2 : ((v16Decay u : ℕ) : ℝ) ≤ ((𝔭.D : ℕ) : ℝ) := by exact_mod_cast hD
  have h3 : (⌈33 * Rof u⌉₊ : ℝ) + 102 ≤ (v16Decay u : ℝ) := by
    unfold v16Decay
    have : ⌈33 * Rof u⌉₊ + 102 ≤ 8 * (classFloor + 2 * locLoss + ⌈33 * Rof u⌉₊ + 2) := by
      have : 400 ≤ classFloor := classFloor_ge
      omega
    exact_mod_cast this
  simp only [Params.tree_D]
  linarith

theorem energyTail_engFam_D (hB5 : EngLeTailMassStatementD) (hB5t : EngTopLeTailMassStatementD) {u : ℝ}
    (hu : 1 < u) {𝔭 : Params} (h𝔭 : V16Params u 𝔭) :
    EnergyTailBound (engFam u 𝔭) (fullInts 𝔭) u 𝔭 (33 * Rof u + 2) := by
  have hD : v16Decay u ≤ 𝔭.D := h𝔭.2.2.1
  have hR4 : 4 ≤ Rof u := four_le_Rof hu
  have hM3 : 3 ≤ 33 * Rof u + 2 := by linarith
  have hu1 : ∀ v : Fin 3, 1 < slotExp u v := fun v => by
    unfold slotExp; split_ifs <;> linarith
  have hDM := tail_derivs hD
  have hb := fun v : Fin 3 => hB5 𝔭.tree h𝔭.tree_loc_admissible.2 (s := slotExp u v) (q := qX (Rof u) v)
    (M := 33 * Rof u + 2) (hu1 v) (two_le_qX hR4 v) hM3 h𝔭.tail_decay hDM
  choose C₁ hC₁0 hC₁ using hb
  have hbt := fun v : Fin 3 => hB5t 𝔭.tree h𝔭.tree_loc_admissible.2 (s := slotExp u v)
    (q := qX (Rof u) v) (M := 33 * Rof u + 2) (hu1 v) (two_le_qX hR4 v) hM3 h𝔭.tail_decay
    (by linarith)
  choose C₂ hC₂0 hC₂ using hbt
  refine ⟨∑ v, (C₁ v + C₂ v), Finset.sum_nonneg fun v _ => add_nonneg (hC₁0 v) (hC₂0 v), ?_⟩
  intro P _ Qs hQ Cs hbox h hm hbdd v
  set G : ℝ≥0∞ := ⨆ W ∈ fullInts 𝔭 Cs, ENNReal.ofReal
    (tailMass (33 * Rof u + 2) (fun y => yNorm (slotExp u v) (h v y)) (dyadicInt W.1 W.2)) with hG
  have hsum : C₁ v + C₂ v ≤ ∑ v, (C₁ v + C₂ v) :=
    Finset.single_le_sum (f := fun v => C₁ v + C₂ v) (fun v _ => add_nonneg (hC₁0 v) (hC₂0 v))
      (Finset.mem_univ v)
  have h1 : ENNReal.ofReal (C₁ v) ≤ ENNReal.ofReal (∑ v, (C₁ v + C₂ v)) :=
    ENNReal.ofReal_le_ofReal (by linarith [hC₂0 v])
  have h2 : ENNReal.ofReal (C₂ v) ≤ ENNReal.ofReal (∑ v, (C₁ v + C₂ v)) :=
    ENNReal.ofReal_le_ofReal (by linarith [hC₁0 v])
  refine max_le ?_ ?_
  · refine (hC₁ v P Qs hQ Cs hbox v (h v) (hm v) (hbdd v)).trans ?_
    refine mul_le_mul h1 ?_ zero_le zero_le
    exact iSup₂_le fun R hR => le_iSup₂_of_le (R.box.scale, R.pos) (Or.inl ⟨R, hR, rfl⟩) le_rfl
  · refine (hC₂ v P Cs v (h v) (hm v) (hbdd v)).trans ?_
    refine mul_le_mul h2 ?_ zero_le zero_le
    exact iSup_le fun W => iSup_le fun ξ => iSup_le fun hd =>
      le_iSup₂_of_le W (Or.inr ⟨ξ, hd⟩) le_rfl

/-- The INSIDE family (B11, REV3): the tile energy `eng` only, in the class `𝔭.tree` at the exponents `(2, 2, Rof u)`. -/
def engFamI (u : ℝ) (𝔭 : Params) : EnergyFamily :=
  fun _ _ h v S => eng 𝔭.tree (slotExp u v) v (h v) S (qX (Rof u) v)

theorem engFamI_mono (u : ℝ) (𝔭 : Params) : EnergyMono (engFamI u 𝔭) := by
  intro P _ h v S S' hSS
  exact eng_mono _ _ _ _ hSS _

/-- B5 (corrected) for the inside family, with the tile intervals only (B11: `IntsScale tileInts`). -/
theorem energyTail_engFamI_D (hB5 : EngLeTailMassStatementD) {u : ℝ} (hu : 1 < u) {𝔭 : Params}
    (h𝔭 : V16Params u 𝔭) : EnergyTailBound (engFamI u 𝔭) tileInts u 𝔭 (33 * Rof u + 2) := by
  have hD : v16Decay u ≤ 𝔭.D := h𝔭.2.2.1
  have hR4 : 4 ≤ Rof u := four_le_Rof hu
  have hM3 : 3 ≤ 33 * Rof u + 2 := by linarith
  have hu1 : ∀ v : Fin 3, 1 < slotExp u v := fun v => by
    unfold slotExp; split_ifs <;> linarith
  have hDM := tail_derivs hD
  have hb := fun v : Fin 3 => hB5 𝔭.tree h𝔭.tree_loc_admissible.2 (s := slotExp u v) (q := qX (Rof u) v)
    (M := 33 * Rof u + 2) (hu1 v) (two_le_qX hR4 v) hM3 h𝔭.tail_decay hDM
  choose C₁ hC₁0 hC₁ using hb
  refine ⟨∑ v, C₁ v, Finset.sum_nonneg fun v _ => hC₁0 v, ?_⟩
  intro P _ Qs hQ Cs hbox h hm hbdd v
  have h1 : ENNReal.ofReal (C₁ v) ≤ ENNReal.ofReal (∑ v, C₁ v) :=
    ENNReal.ofReal_le_ofReal
      (Finset.single_le_sum (f := C₁) (fun v _ => hC₁0 v) (Finset.mem_univ v))
  refine (hC₁ v P Qs hQ Cs hbox v (h v) (hm v) (hbdd v)).trans ?_
  refine mul_le_mul h1 ?_ zero_le zero_le
  exact iSup₂_le fun R hR => le_iSup₂_of_le (R.box.scale, R.pos) ⟨R, hR, rfl⟩ le_rfl

end PrimeBHT.TimeFrequency.X2.V16
