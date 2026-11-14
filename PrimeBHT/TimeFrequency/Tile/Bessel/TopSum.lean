module

public import PrimeBHT.TimeFrequency.Tile.Trees
public import PrimeBHT.TimeFrequency.Tile.Lacunary
public import PrimeBHT.TimeFrequency.Tile.DyadicWeights
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Step 5 (v) of the claim: summing the boundary weights over the tiles of a tree

For an `i`-tree `T ⊆ Idx_ν` with top `I_T = [A, B)`, the tiles `t ∈ T` have `I_t = [l_t, ρ_t) ⊆ I_T`, at
most three tiles share a time interval, and the time intervals are among the dyadic subintervals of
`I_T`; by `sum_icoWeight_le` (dyadic geometry lemma)

`∑_{t ∈ T} |I_t| (1 + dist(I_t, I_T^c)/|I_t|)^{-q} ≤ 3 · 4q/(q-1) · |I_T|`  (`q > 1`).
-/

@[expose] public section

open MeasureTheory
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Tile

/-- The left endpoint `A = 2^s v` of the top interval of a tree. -/
noncomputable def topLeft (T : TreeData) : ℝ := (2 : ℝ) ^ T.top.1 * T.top.2

/-- The right endpoint `B = 2^s (v + 1)` of the top interval of a tree. -/
noncomputable def topRight (T : TreeData) : ℝ := (2 : ℝ) ^ T.top.1 * (T.top.2 + 1)

/-- The left endpoint `2^s v` of `I_t`. -/
noncomputable def tileLeft (t : ℤ × ℤ × ℤ) : ℝ := (2 : ℝ) ^ t.1 * t.2.1

/-- The right endpoint `2^s (v + 1)` of `I_t`. -/
noncomputable def tileRight (t : ℤ × ℤ × ℤ) : ℝ := (2 : ℝ) ^ t.1 * (t.2.1 + 1)

theorem topInt_eq_Ico (T : TreeData) : T.topInt = Set.Ico (topLeft T) (topRight T) := rfl

theorem timeInt_eq_Ico (t : ℤ × ℤ × ℤ) : timeInt t = Set.Ico (tileLeft t) (tileRight t) := rfl

theorem tileRight_sub_tileLeft (t : ℤ × ℤ × ℤ) : tileRight t - tileLeft t = (2 : ℝ) ^ t.1 := by
  unfold tileRight tileLeft; ring

theorem tileLeft_lt_tileRight (t : ℤ × ℤ × ℤ) : tileLeft t < tileRight t := by
  have := tileRight_sub_tileLeft t
  have h : (0 : ℝ) < (2 : ℝ) ^ t.1 := zpow_pos (by norm_num) _
  linarith

/-- `I_t ⊆ I_T` in terms of endpoints. -/
theorem topLeft_le_tileLeft {T : TreeData} {t : ℤ × ℤ × ℤ} (h : timeInt t ⊆ T.topInt) :
    topLeft T ≤ tileLeft t ∧ tileRight t ≤ topRight T := by
  rw [timeInt_eq_Ico, topInt_eq_Ico, Set.Ico_subset_Ico_iff (tileLeft_lt_tileRight t)] at h
  exact h

/-- For `I_t ⊆ I_T` the offset `m = v - 2^d V` (`d = S - s`) lies in `[0, 2^d)`. -/
theorem offset_bounds {T : TreeData} {t : ℤ × ℤ × ℤ} (h : timeInt t ⊆ T.topInt) :
    t.1 ≤ T.top.1 ∧ 0 ≤ t.2.1 - 2 ^ (T.top.1 - t.1).toNat * T.top.2 ∧
      t.2.1 - 2 ^ (T.top.1 - t.1).toNat * T.top.2 < 2 ^ (T.top.1 - t.1).toNat := by
  have hs : t.1 ≤ T.top.1 := scale_le_of_dyadicInt_subset h
  obtain ⟨h1, h2⟩ := topLeft_le_tileLeft h
  set d : ℕ := (T.top.1 - t.1).toNat with hd
  have hSd : T.top.1 = t.1 + (d : ℤ) := by omega
  have hpos : (0 : ℝ) < (2 : ℝ) ^ t.1 := zpow_pos (by norm_num) _
  have h2d : (2 : ℝ) ^ T.top.1 = (2 : ℝ) ^ t.1 * 2 ^ d := by
    rw [hSd, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
  unfold topLeft tileLeft at h1
  unfold topRight tileRight at h2
  rw [h2d] at h1 h2
  refine ⟨hs, ?_, ?_⟩
  · have : ((2 : ℝ) ^ d * T.top.2 : ℝ) ≤ t.2.1 := by
      have : (2 : ℝ) ^ t.1 * ((2 : ℝ) ^ d * T.top.2) ≤ (2 : ℝ) ^ t.1 * t.2.1 := by
        calc (2 : ℝ) ^ t.1 * ((2 : ℝ) ^ d * T.top.2) = (2 : ℝ) ^ t.1 * 2 ^ d * T.top.2 := by ring
          _ ≤ _ := h1
      exact le_of_mul_le_mul_left this hpos
    have : (2 ^ d * T.top.2 : ℤ) ≤ t.2.1 := by exact_mod_cast this
    omega
  · have : ((t.2.1 : ℝ) + 1) ≤ (2 : ℝ) ^ d * (T.top.2 + 1) := by
      have : (2 : ℝ) ^ t.1 * ((t.2.1 : ℝ) + 1) ≤ (2 : ℝ) ^ t.1 * ((2 : ℝ) ^ d * (T.top.2 + 1)) := by
        calc (2 : ℝ) ^ t.1 * ((t.2.1 : ℝ) + 1) ≤ (2 : ℝ) ^ t.1 * 2 ^ d * (T.top.2 + 1) := h2
          _ = _ := by ring
      exact le_of_mul_le_mul_left this hpos
    have : t.2.1 + 1 ≤ 2 ^ d * (T.top.2 + 1) := by exact_mod_cast this
    nlinarith

/-- The `(d, m)` coordinates of a tile in the dyadic grid of the top interval. -/
def tileDM (T : TreeData) (t : ℤ × ℤ × ℤ) : ℕ × ℕ :=
  ((T.top.1 - t.1).toNat, (t.2.1 - 2 ^ (T.top.1 - t.1).toNat * T.top.2).toNat)

theorem tileDM_inj {T : TreeData} {t t' : ℤ × ℤ × ℤ} (h : timeInt t ⊆ T.topInt)
    (h' : timeInt t' ⊆ T.topInt) (he : tileDM T t = tileDM T t') : timeInt t = timeInt t' := by
  obtain ⟨hs, h0, -⟩ := offset_bounds h
  obtain ⟨hs', h0', -⟩ := offset_bounds h'
  simp only [tileDM, Prod.mk.injEq] at he
  obtain ⟨hd, hm⟩ := he
  have h1 : t.1 = t'.1 := by omega
  rw [timeInt_eq_iff]
  refine ⟨h1, ?_⟩
  have hm' : t.2.1 - 2 ^ (T.top.1 - t.1).toNat * T.top.2 =
      t'.2.1 - 2 ^ (T.top.1 - t'.1).toNat * T.top.2 := by omega
  rw [hd] at hm'
  have : (2 : ℤ) ^ (T.top.1 - t'.1).toNat * T.top.2 = 2 ^ (T.top.1 - t'.1).toNat * T.top.2 := rfl
  linarith

/-- **Step 5 (v).** For an `i`-tree `T ⊆ Idx_ν` and `q > 1`:
`∑_{t ∈ T} |I_t| (1 + dist(I_t, I_T^c)/|I_t|)^{-q} ≤ 3 · 4q/(q-1) · |I_T|`. -/
theorem sum_icoWeight_tree_le {a b s' α : ℤ} {i : Fin 3} {P : Finset (ℤ × ℤ × ℤ)}
    (hP : (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α) {T : TreeData} (hT : IsTree a b i P T) {q : ℝ}
    (hq : 1 < q) :
    ∑ t ∈ T.tiles, icoWeight q (topLeft T) (topRight T) (tileLeft t) (tileRight t) ≤
      3 * (4 * (q / (q - 1)) * (2 : ℝ) ^ T.top.1) := by
  classical
  have hℓ : (0 : ℝ) < (2 : ℝ) ^ T.top.1 := zpow_pos (by norm_num) _
  have hB : topRight T = topLeft T + (2 : ℝ) ^ T.top.1 := by
    unfold topRight topLeft; ring
  rw [hB]
  refine sum_icoWeight_le (a := topLeft T) (ℓ := (2 : ℝ) ^ T.top.1) hq hℓ T.tiles
    (fun t => tileLeft t) (fun t => tileRight t) (tileDM T) 3 ?_ ?_ ?_ ?_
  · intro t ht
    obtain ⟨-, h0, h3⟩ := offset_bounds (hT.timeInt_subset ht)
    simp only [tileDM]
    have e := Int.toNat_of_nonneg h0
    have : (((t.2.1 - 2 ^ (T.top.1 - t.1).toNat * T.top.2).toNat : ℕ) : ℤ) <
        (((2 ^ (T.top.1 - t.1).toNat : ℕ)) : ℤ) := by
      rw [e]; push_cast; exact h3
    exact_mod_cast this
  · intro t ht
    obtain ⟨hs, h0, -⟩ := offset_bounds (hT.timeInt_subset ht)
    have hSd : T.top.1 = t.1 + ((T.top.1 - t.1).toNat : ℤ) := by omega
    have := subIcoLeft_two_zpow t.1 (T.top.1 - t.1).toNat
      (t.2.1 - 2 ^ (T.top.1 - t.1).toNat * T.top.2).toNat t.2.1 T.top.2 (by omega)
    rw [← hSd] at this
    unfold topLeft tileLeft
    exact this.symm
  · intro t ht
    obtain ⟨hs, h0, -⟩ := offset_bounds (hT.timeInt_subset ht)
    have hSd : T.top.1 = t.1 + ((T.top.1 - t.1).toNat : ℤ) := by omega
    have := subIcoRight_two_zpow t.1 (T.top.1 - t.1).toNat
      (t.2.1 - 2 ^ (T.top.1 - t.1).toNat * T.top.2).toNat t.2.1 T.top.2 (by omega)
    rw [← hSd] at this
    unfold topLeft tileRight
    exact this.symm
  · intro p
    by_cases hne : (T.tiles.filter fun t => tileDM T t = p).Nonempty
    · obtain ⟨t₀, ht₀⟩ := hne
      rw [Finset.mem_filter] at ht₀
      refine le_trans (Finset.card_le_card ?_) (hT.card_filter_timeInt_le_three hP (timeInt t₀))
      intro t ht
      rw [Finset.mem_filter] at ht ⊢
      refine ⟨ht.1, ?_⟩
      exact tileDM_inj (hT.timeInt_subset ht.1) (hT.timeInt_subset ht₀.1) (ht.2.trans ht₀.2.symm)
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp

end PrimeBHT.TimeFrequency.Tile
