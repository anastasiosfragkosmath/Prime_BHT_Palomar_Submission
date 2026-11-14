module

public import PrimeBHT.Frozen.TimeInt
public import PrimeBHT.Frozen.FreqNum
public import PrimeBHT.Frozen.FreqInt
public import PrimeBHT.Frozen.TriIdx
public import PrimeBHT.Frozen.TriValid
public import PrimeBHT.Frozen.IntervalCentre
public import PrimeCarleson.Proof.Oplus.Defs.Dyadic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# The tile grids (blueprint node C0, items 1, 2 and 5)

Dyadic time intervals `2^s [v, v+1)` as `Set ℝ` values given by explicit formulas (`dyadicInt`; the
frozen `timeInt t` is `dyadicInt t.1 t.2.1` by `rfl`, and also `(⟨t.1, t.2.1⟩ : Dyadic).toSet` of the
earlier project, `timeInt_eq_toSet`), nestedness, parent and children, the dilation `dilate C S`
(same centre, `C` times the length) with explicit formulas for `3J`, `2ω`, `50ω`, the frequency cells
`2^{-s}[n/3, n/3 + 1)` (`freqCell`) with the grid property for scales differing by an even number,
and the dilation symmetry `(s, v, ℓ) ↦ (s - k, v, ℓ)`.

Nothing here is bundled in a structure: the intervals are `Set ℝ` values, the facts are lemmas.
-/

@[expose] public section

open MeasureTheory
open PrimeBHT.Statements
open PrimeCarleson.Proof.Oplus renaming Dyadic → OplusDyadic

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Tile

/-! ### Dyadic time intervals -/

/-- The dyadic interval `2^s [v, v + 1)` of `𝒟_0` (BD26 L503: `2^s[v, v+1)`). -/
def dyadicInt (s v : ℤ) : Set ℝ := Set.Ico ((2 : ℝ) ^ s * v) ((2 : ℝ) ^ s * (v + 1))

/-- The common time interval `I_t` of a tri-tile is the dyadic interval of scale `t.1` and index `t.2.1`. -/
theorem timeInt_eq_dyadicInt (t : ℤ × ℤ × ℤ) : timeInt t = dyadicInt t.1 t.2.1 := rfl

theorem measurableSet_dyadicInt (s v : ℤ) : MeasurableSet (dyadicInt s v) := measurableSet_Ico

theorem volume_dyadicInt (s v : ℤ) : volume (dyadicInt s v) = ENNReal.ofReal ((2 : ℝ) ^ s) := by
  unfold dyadicInt
  rw [Real.volume_Ico]
  congr 1
  ring

theorem toReal_volume_dyadicInt (s v : ℤ) : (volume (dyadicInt s v)).toReal = (2 : ℝ) ^ s := by
  rw [volume_dyadicInt, ENNReal.toReal_ofReal (zpow_nonneg (by norm_num) _)]

/-- `|I_t| = 2^{s(t)}`. -/
theorem toReal_volume_timeInt (t : ℤ × ℤ × ℤ) : (volume (timeInt t)).toReal = (2 : ℝ) ^ t.1 :=
  toReal_volume_dyadicInt _ _

theorem toReal_volume_timeInt_pos (t : ℤ × ℤ × ℤ) : 0 < (volume (timeInt t)).toReal := by
  rw [toReal_volume_timeInt]; exact zpow_pos (by norm_num) _

/-- Two dyadic intervals are nested or disjoint (BD26: two intervals of `𝒟_0` are nested or disjoint). -/
theorem dyadicInt_nested_or_disjoint (s v s' v' : ℤ) :
    dyadicInt s v ⊆ dyadicInt s' v' ∨ dyadicInt s' v' ⊆ dyadicInt s v ∨
      Disjoint (dyadicInt s v) (dyadicInt s' v') :=
  OplusDyadic.nested_or_disjoint ⟨s, v⟩ ⟨s', v'⟩

theorem timeInt_nested_or_disjoint (t t' : ℤ × ℤ × ℤ) :
    timeInt t ⊆ timeInt t' ∨ timeInt t' ⊆ timeInt t ∨ Disjoint (timeInt t) (timeInt t') :=
  dyadicInt_nested_or_disjoint _ _ _ _

/-- A dyadic interval contained in another has a smaller (or equal) scale. -/
theorem scale_le_of_dyadicInt_subset {s v s' v' : ℤ} (h : dyadicInt s v ⊆ dyadicInt s' v') :
    s ≤ s' :=
  OplusDyadic.k_le_of_toSet_subset (I := ⟨s, v⟩) (J := ⟨s', v'⟩) h

/-- Same scale and nested implies equal. -/
theorem index_eq_of_dyadicInt_subset {s v s' v' : ℤ} (hs : s = s')
    (h : dyadicInt s v ⊆ dyadicInt s' v') : v = v' := by
  have := OplusDyadic.eq_of_toSet_subset_of_k_eq (I := ⟨s, v⟩) (J := ⟨s', v'⟩) hs h
  exact congrArg OplusDyadic.m this

theorem dyadicInt_eq_iff {s v s' v' : ℤ} : dyadicInt s v = dyadicInt s' v' ↔ s = s' ∧ v = v' := by
  constructor
  · intro h
    have h1 := scale_le_of_dyadicInt_subset h.subset
    have h2 := scale_le_of_dyadicInt_subset h.symm.subset
    have hs : s = s' := le_antisymm h1 h2
    exact ⟨hs, index_eq_of_dyadicInt_subset hs h.subset⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem timeInt_eq_iff {t t' : ℤ × ℤ × ℤ} :
    timeInt t = timeInt t' ↔ t.1 = t'.1 ∧ t.2.1 = t'.2.1 :=
  dyadicInt_eq_iff

/-- Same scale, different index: disjoint. -/
theorem disjoint_dyadicInt_of_ne {s v v' : ℤ} (h : v ≠ v') :
    Disjoint (dyadicInt s v) (dyadicInt s v') := by
  rcases dyadicInt_nested_or_disjoint s v s v' with h1 | h1 | h1
  · exact absurd (index_eq_of_dyadicInt_subset rfl h1) h
  · exact absurd (index_eq_of_dyadicInt_subset rfl h1).symm h
  · exact h1

/-- Two tiles of the same scale with different `v` have disjoint time intervals. -/
theorem disjoint_timeInt_of_scale_eq {t t' : ℤ × ℤ × ℤ} (hs : t.1 = t'.1) (hv : t.2.1 ≠ t'.2.1) :
    Disjoint (timeInt t) (timeInt t') := by
  rw [timeInt_eq_dyadicInt, timeInt_eq_dyadicInt, ← hs]
  exact disjoint_dyadicInt_of_ne hv

/-- The dyadic interval of scale `s` containing `x`. -/
theorem mem_dyadicInt_floor (s : ℤ) (x : ℝ) : x ∈ dyadicInt s ⌊x / (2 : ℝ) ^ s⌋ := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  constructor
  · have := Int.floor_le (x / (2 : ℝ) ^ s)
    rw [le_div_iff₀ hp] at this
    linarith
  · have := Int.lt_floor_add_one (x / (2 : ℝ) ^ s)
    rw [div_lt_iff₀ hp] at this
    linarith

/-! #### Parent and children -/

/-- The dyadic parent of `2^s[v, v+1)` is `2^{s+1}[⌊v/2⌋, ⌊v/2⌋ + 1)`. -/
def dyadicParent (p : ℤ × ℤ) : ℤ × ℤ := (p.1 + 1, p.2 / 2)

theorem dyadicInt_subset_parent (s v : ℤ) :
    dyadicInt s v ⊆ dyadicInt (dyadicParent (s, v)).1 (dyadicParent (s, v)).2 :=
  OplusDyadic.toSet_subset_parent ⟨s, v⟩

/-! ### Centres, lengths and dilates -/

theorem intervalCentre_Ico {x y : ℝ} (h : x < y) : intervalCentre (Set.Ico x y) = (x + y) / 2 := by
  unfold intervalCentre
  rw [csInf_Ico h, csSup_Ico h]

theorem toReal_volume_Ico {x y : ℝ} (h : x ≤ y) : (volume (Set.Ico x y)).toReal = y - x := by
  rw [Real.volume_Ico, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

/-- The dilate `C S` of an interval `S`: the half-open interval with the same centre `c(S)` and `C`
times the length `|S|` (BD26 `3ω`, `50ω`, `2ω`, `3J`). Used only for bounded nondegenerate intervals. -/
def dilate (C : ℝ) (S : Set ℝ) : Set ℝ :=
  Set.Ico (intervalCentre S - C * (volume S).toReal / 2)
    (intervalCentre S + C * (volume S).toReal / 2)

theorem dilate_Ico {x y : ℝ} (h : x < y) (C : ℝ) :
    dilate C (Set.Ico x y) =
      Set.Ico ((x + y) / 2 - C * (y - x) / 2) ((x + y) / 2 + C * (y - x) / 2) := by
  unfold dilate
  rw [intervalCentre_Ico h, toReal_volume_Ico h.le]

theorem Ico_subset_dilate {x y C : ℝ} (h : x < y) (hC : 1 ≤ C) :
    Set.Ico x y ⊆ dilate C (Set.Ico x y) := by
  rw [dilate_Ico h]
  apply Set.Ico_subset_Ico <;> nlinarith

theorem dilate_Ico_mono {x y C C' : ℝ} (h : x < y) (hC : C ≤ C') :
    dilate C (Set.Ico x y) ⊆ dilate C' (Set.Ico x y) := by
  rw [dilate_Ico h, dilate_Ico h]
  apply Set.Ico_subset_Ico <;> nlinarith

/-- If `S = [x, y) ⊆ S' = [x', y')` and `|S'| ≥ 49 |S|` then `50 S ⊆ 2 S'`
(`50 S` extends `24.5 |S|` beyond `S`, `2 S'` extends `|S'|/2` beyond `S'`). -/
theorem dilate_fifty_subset_dilate_two {x y x' y' : ℝ} (h : x < y) (h' : x' < y')
    (hsub : Set.Ico x y ⊆ Set.Ico x' y') (hlen : 49 * (y - x) ≤ y' - x') :
    dilate 50 (Set.Ico x y) ⊆ dilate 2 (Set.Ico x' y') := by
  rw [Set.Ico_subset_Ico_iff h] at hsub
  rw [dilate_Ico h, dilate_Ico h']
  apply Set.Ico_subset_Ico <;> nlinarith [hsub.1, hsub.2]

/-- Dilation is monotone in the interval (for `C ≥ 1`): `S ⊆ S'` implies `C S ⊆ C S'`. -/
theorem dilate_Ico_mono_of_subset {x y x' y' C : ℝ} (h : x < y) (hC : 1 ≤ C)
    (hsub : Set.Ico x y ⊆ Set.Ico x' y') : dilate C (Set.Ico x y) ⊆ dilate C (Set.Ico x' y') := by
  have hsub' := (Set.Ico_subset_Ico_iff h).1 hsub
  have h' : x' < y' := by linarith [hsub'.1, hsub'.2]
  rw [dilate_Ico h, dilate_Ico h']
  apply Set.Ico_subset_Ico <;> nlinarith [hsub'.1, hsub'.2]

theorem timeInt_lt (t : ℤ × ℤ × ℤ) :
    (2 : ℝ) ^ t.1 * t.2.1 < (2 : ℝ) ^ t.1 * (t.2.1 + 1) := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ t.1 := zpow_pos (by norm_num) _
  nlinarith

theorem intervalCentre_timeInt_eq (t : ℤ × ℤ × ℤ) :
    intervalCentre (timeInt t) = (2 : ℝ) ^ t.1 * ((t.2.1 : ℝ) + 1 / 2) := by
  unfold timeInt
  rw [intervalCentre_Ico (timeInt_lt t)]
  ring

/-- `3 I_t` (or `C I_t`) with explicit endpoints: `2^s [v + 1/2 - C/2, v + 1/2 + C/2)`. -/
theorem dilate_timeInt (C : ℝ) (t : ℤ × ℤ × ℤ) :
    dilate C (timeInt t) = Set.Ico ((2 : ℝ) ^ t.1 * ((t.2.1 : ℝ) + 1 / 2 - C / 2))
      ((2 : ℝ) ^ t.1 * ((t.2.1 : ℝ) + 1 / 2 + C / 2)) := by
  unfold timeInt
  rw [dilate_Ico (timeInt_lt t)]
  congr 1 <;> ring

theorem timeInt_subset_dilate {C : ℝ} (hC : 1 ≤ C) (t : ℤ × ℤ × ℤ) :
    timeInt t ⊆ dilate C (timeInt t) :=
  Ico_subset_dilate (timeInt_lt t) hC

theorem intervalCentre_dyadicInt (s v : ℤ) :
    intervalCentre (dyadicInt s v) = (2 : ℝ) ^ s * ((v : ℝ) + 1 / 2) :=
  intervalCentre_timeInt_eq (s, v, 0)

/-- `C J` with explicit endpoints, for a dyadic interval `J = 2^s[v, v+1)`: `3J` has
centre `2^s(v + 1/2)` and length `3 · 2^s`. -/
theorem dilate_dyadicInt (C : ℝ) (s v : ℤ) :
    dilate C (dyadicInt s v) = Set.Ico ((2 : ℝ) ^ s * ((v : ℝ) + 1 / 2 - C / 2))
      ((2 : ℝ) ^ s * ((v : ℝ) + 1 / 2 + C / 2)) :=
  dilate_timeInt C (s, v, 0)

theorem dyadicInt_subset_dilate {C : ℝ} (hC : 1 ≤ C) (s v : ℤ) :
    dyadicInt s v ⊆ dilate C (dyadicInt s v) :=
  timeInt_subset_dilate hC (s, v, 0)

/-- Every dyadic interval is contained in a dyadic interval of each larger scale. -/
theorem exists_dyadicInt_superset (s v : ℤ) {s' : ℤ} (h : s ≤ s') :
    ∃ v' : ℤ, dyadicInt s v ⊆ dyadicInt s' v' := by
  have hx : (2 : ℝ) ^ s * v ∈ dyadicInt s v :=
    ⟨le_rfl, by have := timeInt_lt (s, v, 0); simpa using this⟩
  refine ⟨⌊(2 : ℝ) ^ s * v / (2 : ℝ) ^ s'⌋, ?_⟩
  have hx' := mem_dyadicInt_floor s' ((2 : ℝ) ^ s * v)
  rcases dyadicInt_nested_or_disjoint s v s' ⌊(2 : ℝ) ^ s * v / (2 : ℝ) ^ s'⌋ with h1 | h1 | h1
  · exact h1
  · have hs : s = s' := le_antisymm h (scale_le_of_dyadicInt_subset h1)
    have hv := index_eq_of_dyadicInt_subset hs.symm h1
    subst hs
    rw [hv]
  · exact absurd hx' (Set.disjoint_left.1 h1 hx)

/-! ### Frequency cells -/

/-- The frequency cell `2^{-s} [n/3, n/3 + 1)` of scale `s` and numerator `n`. -/
def freqCell (s n : ℤ) : Set ℝ :=
  Set.Ico ((2 : ℝ) ^ (-s) * ((n : ℝ) / 3)) ((2 : ℝ) ^ (-s) * ((n : ℝ) / 3 + 1))

/-- The frequency interval `ω_{t,k}` is the cell of scale `s(t)` and numerator `freqNum a b t k`. -/
theorem freqInt_eq_freqCell (a b : ℤ) (k : Fin 3) (t : ℤ × ℤ × ℤ) :
    freqInt a b k t = freqCell t.1 (freqNum a b t k) := rfl

@[simp] theorem freqNum_zero (a b : ℤ) (t : ℤ × ℤ × ℤ) : freqNum a b t 0 = t.2.2 := rfl

@[simp] theorem freqNum_one (a b : ℤ) (t : ℤ × ℤ × ℤ) : freqNum a b t 1 = t.2.2 - a := rfl

@[simp] theorem freqNum_two (a b : ℤ) (t : ℤ × ℤ × ℤ) :
    freqNum a b t 2 = 2 * t.2.2 - a - b := rfl

theorem freqCell_lt (s n : ℤ) :
    (2 : ℝ) ^ (-s) * ((n : ℝ) / 3) < (2 : ℝ) ^ (-s) * ((n : ℝ) / 3 + 1) := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (-s) := zpow_pos (by norm_num) _
  nlinarith

theorem volume_freqCell (s n : ℤ) : volume (freqCell s n) = ENNReal.ofReal ((2 : ℝ) ^ (-s)) := by
  unfold freqCell
  rw [Real.volume_Ico]
  congr 1
  ring

theorem toReal_volume_freqCell (s n : ℤ) : (volume (freqCell s n)).toReal = (2 : ℝ) ^ (-s) := by
  rw [volume_freqCell, ENNReal.toReal_ofReal (zpow_nonneg (by norm_num) _)]

theorem toReal_volume_freqInt_eq (a b : ℤ) (k : Fin 3) (t : ℤ × ℤ × ℤ) :
    (volume (freqInt a b k t)).toReal = (2 : ℝ) ^ (-t.1) :=
  toReal_volume_freqCell _ _

theorem intervalCentre_freqCell (s n : ℤ) :
    intervalCentre (freqCell s n) = (2 : ℝ) ^ (-s) * ((n : ℝ) / 3 + 1 / 2) := by
  unfold freqCell
  rw [intervalCentre_Ico (freqCell_lt s n)]
  ring

/-- The centre `c(ω_{t,k}) = 2^{-s}(n_k/3 + 1/2)`. -/
theorem intervalCentre_freqInt (a b : ℤ) (k : Fin 3) (t : ℤ × ℤ × ℤ) :
    intervalCentre (freqInt a b k t) =
      (2 : ℝ) ^ (-t.1) * ((freqNum a b t k : ℝ) / 3 + 1 / 2) :=
  intervalCentre_freqCell _ _

/-- `C ω` with explicit endpoints: `2^{-s}[n/3 + 1/2 - C/2, n/3 + 1/2 + C/2)`. -/
theorem dilate_freqCell (C : ℝ) (s n : ℤ) :
    dilate C (freqCell s n) = Set.Ico ((2 : ℝ) ^ (-s) * ((n : ℝ) / 3 + 1 / 2 - C / 2))
      ((2 : ℝ) ^ (-s) * ((n : ℝ) / 3 + 1 / 2 + C / 2)) := by
  unfold freqCell
  rw [dilate_Ico (freqCell_lt s n)]
  congr 1 <;> ring

theorem dilate_freqInt (C : ℝ) (a b : ℤ) (k : Fin 3) (t : ℤ × ℤ × ℤ) :
    dilate C (freqInt a b k t) =
      Set.Ico ((2 : ℝ) ^ (-t.1) * ((freqNum a b t k : ℝ) / 3 + 1 / 2 - C / 2))
        ((2 : ℝ) ^ (-t.1) * ((freqNum a b t k : ℝ) / 3 + 1 / 2 + C / 2)) :=
  dilate_freqCell _ _ _

theorem freqInt_subset_dilate {C : ℝ} (hC : 1 ≤ C) (a b : ℤ) (k : Fin 3) (t : ℤ × ℤ × ℤ) :
    freqInt a b k t ⊆ dilate C (freqInt a b k t) :=
  Ico_subset_dilate (freqCell_lt _ _) hC

/-! ### The grid property of the frequency cells -/

theorem freqCell_subset_iff {s n s' n' : ℤ} :
    freqCell s' n' ⊆ freqCell s n ↔
      (2 : ℝ) ^ (-s) * ((n : ℝ) / 3) ≤ (2 : ℝ) ^ (-s') * ((n' : ℝ) / 3) ∧
        (2 : ℝ) ^ (-s') * ((n' : ℝ) / 3 + 1) ≤ (2 : ℝ) ^ (-s) * ((n : ℝ) / 3 + 1) :=
  Set.Ico_subset_Ico_iff (freqCell_lt s' n')

/-- Strict containment of cells forces a strictly finer scale: `ω ⊆ ω'` implies `s' ≤ s`. -/
theorem scale_le_of_freqCell_subset {s n s' n' : ℤ} (h : freqCell s n ⊆ freqCell s' n') :
    s' ≤ s := by
  rw [freqCell_subset_iff] at h
  have hlen : (2 : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-s') := by linarith [h.1, h.2]
  have := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 hlen
  omega

/-- Cells of equal scale that are nested have equal numerators. -/
theorem numerator_eq_of_freqCell_subset {s n n' : ℤ} (h : freqCell s n ⊆ freqCell s n') :
    n = n' := by
  rw [freqCell_subset_iff] at h
  have hp : (0 : ℝ) < (2 : ℝ) ^ (-s) := zpow_pos (by norm_num) _
  have h1 := h.1
  have h2 := h.2
  have : (n : ℝ) = n' := by
    have e1 : (n' : ℝ) ≤ n := by
      by_contra hc
      have hc' := lt_of_not_ge hc
      nlinarith
    have e2 : (n : ℝ) ≤ n' := by
      by_contra hc
      have hc' := lt_of_not_ge hc
      nlinarith
    exact le_antisymm e2 e1
  exact_mod_cast this

theorem freqCell_inj {s n s' n' : ℤ} (h : freqCell s n = freqCell s' n') : s = s' ∧ n = n' := by
  have h1 := scale_le_of_freqCell_subset h.subset
  have h2 := scale_le_of_freqCell_subset h.symm.subset
  have hs : s = s' := le_antisymm h2 h1
  subst hs
  exact ⟨rfl, numerator_eq_of_freqCell_subset h.subset⟩

theorem freqInt_inj {a b : ℤ} {k : Fin 3} {t t' : ℤ × ℤ × ℤ}
    (h : freqInt a b k t = freqInt a b k t') : t.1 = t'.1 ∧ freqNum a b t k = freqNum a b t' k :=
  freqCell_inj h

/-- The key arithmetic fact: `4 ^ e ≡ 1 (mod 3)`. -/
theorem four_pow_modEq (e : ℕ) : (4 : ℤ) ^ e ≡ 1 [ZMOD 3] := by
  simpa using (show (4 : ℤ) ≡ 1 [ZMOD 3] by decide).pow e

/-- **Grid property of the frequency cells.** Two cells whose scales differ by an even number and
whose numerators are congruent mod `3` are nested or disjoint (`2^{2e} ≡ 1 (mod 3)` makes
`(2^{2e} - 1) n / 3 ∈ ℤ`, so the endpoints of the coarser cell lie in the lattice of the finer one). -/
theorem freqCell_subset_or_disjoint {s n s' n' : ℤ} (hs : s ≤ s') (hd : (2 : ℤ) ∣ s' - s)
    (hn : n ≡ n' [ZMOD 3]) :
    freqCell s' n' ⊆ freqCell s n ∨ Disjoint (freqCell s' n') (freqCell s n) := by
  obtain ⟨e, he⟩ : ∃ e : ℕ, s' = s + 2 * e := ⟨((s' - s) / 2).toNat, by omega⟩
  have hM1 : (4 : ℤ) ^ e ≡ 1 [ZMOD 3] := four_pow_modEq e
  have hMpos : (1 : ℤ) ≤ 4 ^ e := one_le_pow₀ (by norm_num)
  have hA : (4 : ℤ) ^ e * n ≡ n [ZMOD 3] := by simpa using hM1.mul_right n
  obtain ⟨M, hMdef⟩ : ∃ M : ℤ, M = 4 ^ e := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℤ, A = M * n := ⟨_, rfl⟩
  rw [← hMdef] at hM1 hMpos hA
  rw [← hAdef] at hA
  have hq : ∃ q : ℤ, n' = A + 3 * q := by
    refine ⟨(n' - A) / 3, ?_⟩
    unfold Int.ModEq at hn hA
    omega
  obtain ⟨q, hq⟩ := hq
  have hw : (0 : ℝ) < (2 : ℝ) ^ (-s') := zpow_pos (by norm_num) _
  have hscale : (2 : ℝ) ^ (-s) = (M : ℝ) * (2 : ℝ) ^ (-s') := by
    have h1 : (-s : ℤ) = ((2 * e : ℕ) : ℤ) + -s' := by push_cast; omega
    rw [h1, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, hMdef]
    push_cast
    rw [pow_mul]
    norm_num
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
  have hAr : (A : ℝ) = M * n := by rw [hAdef]; push_cast; ring
  have hnr : (n' : ℝ) = A + 3 * q := by rw [hq]; push_cast; ring
  rw [freqCell, freqCell, hscale]
  rcases lt_or_ge q 0 with hq0 | hq0
  · right
    have hq1 : (q : ℝ) ≤ -1 := by exact_mod_cast (by omega : q ≤ -1)
    rw [Set.disjoint_left]
    rintro x ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    nlinarith
  · rcases lt_or_ge q M with hqM | hqM
    · left
      have hq1 : (0 : ℝ) ≤ q := by exact_mod_cast hq0
      have hq2 : (q : ℝ) + 1 ≤ M := by exact_mod_cast (by omega : q + 1 ≤ M)
      apply Set.Ico_subset_Ico <;> nlinarith
    · right
      have hq1 : (M : ℝ) ≤ q := by exact_mod_cast hqM
      rw [Set.disjoint_left]
      rintro x ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
      nlinarith

/-- The grid property for two cells whose scales differ by an even number and whose numerators are
congruent mod `3`: nested or disjoint. -/
theorem freqCell_nested_or_disjoint {s n s' n' : ℤ} (hd : (2 : ℤ) ∣ s' - s)
    (hn : n ≡ n' [ZMOD 3]) :
    freqCell s n ⊆ freqCell s' n' ∨ freqCell s' n' ⊆ freqCell s n ∨
      Disjoint (freqCell s n) (freqCell s' n') := by
  rcases le_total s s' with h | h
  · rcases freqCell_subset_or_disjoint h hd hn with h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1.symm)
  · rcases freqCell_subset_or_disjoint h (by omega) hn.symm with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)

/-! ### The index set and the dilation symmetry -/

/-- Two tiles of `Idx_ν` have scales differing by a multiple of `10`. -/
theorem ten_dvd_scale_sub {s' α : ℤ} {t t' : ℤ × ℤ × ℤ} (ht : t ∈ triIdx s' α)
    (ht' : t' ∈ triIdx s' α) : (10 : ℤ) ∣ t'.1 - t.1 := by
  have h1 := ht.1
  have h2 := ht'.1
  unfold Int.ModEq at h1 h2
  omega

/-- Two tiles of `Idx_ν` have `ℓ` congruent mod `3`. -/
theorem modEq_three_of_mem_triIdx {s' α : ℤ} {t t' : ℤ × ℤ × ℤ} (ht : t ∈ triIdx s' α)
    (ht' : t' ∈ triIdx s' α) : t.2.2 ≡ t'.2.2 [ZMOD 3] :=
  ht.2.trans ht'.2.symm

/-- The dilation `T_λ`, `λ = 2^k`, acts on tiles by `(s, v, ℓ) ↦ (s - k, v, ℓ)`. -/
def dilTile (k : ℤ) (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (t.1 - k, t.2.1, t.2.2)

@[simp] theorem dilTile_dilTile_neg (k : ℤ) (t : ℤ × ℤ × ℤ) : dilTile k (dilTile (-k) t) = t := by
  simp [dilTile]

@[simp] theorem dilTile_neg_dilTile (k : ℤ) (t : ℤ × ℤ × ℤ) : dilTile (-k) (dilTile k t) = t := by
  simp [dilTile]

theorem dilTile_injective (k : ℤ) : Function.Injective (dilTile k) := by
  intro t t' h
  simpa using congrArg (dilTile (-k)) h

/-- `dilTile k` maps `Idx_{s', α}` into `Idx_{(s'-k) mod 10, α}` (and back). -/
theorem dilTile_mem_triIdx_iff (k s' α : ℤ) (t : ℤ × ℤ × ℤ) :
    dilTile k t ∈ triIdx ((s' - k) % 10) α ↔ t ∈ triIdx s' α := by
  unfold triIdx dilTile Int.ModEq
  simp only [Set.mem_ofPred_eq]
  omega

/-- `dilTile k` maps `Idx_{s', α}` **onto** `Idx_{(s'-k) mod 10, α}`. -/
theorem image_dilTile_triIdx (k s' α : ℤ) :
    dilTile k '' triIdx s' α = triIdx ((s' - k) % 10) α := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact (dilTile_mem_triIdx_iff k s' α t).2 ht
  · intro hu
    refine ⟨dilTile (-k) u, ?_, dilTile_dilTile_neg k u⟩
    rw [← dilTile_mem_triIdx_iff k s' α, dilTile_dilTile_neg]
    exact hu

/-- The new class `(s' - k) mod 10` is again a valid parameter. -/
theorem triValid_dilTile {a b s' α : ℤ} (k : ℤ) (h : TriValid a b s' α) :
    TriValid a b ((s' - k) % 10) α := by
  obtain ⟨h1, h2, _, h4⟩ := h
  exact ⟨h1, h2, ⟨Int.emod_nonneg _ (by norm_num), by omega⟩, h4⟩

theorem freqNum_dilTile (a b k : ℤ) (t : ℤ × ℤ × ℤ) : freqNum a b (dilTile k t) = freqNum a b t :=
  rfl

private theorem two_zpow_sub (s k : ℤ) : (2 : ℝ) ^ (s - k) = (2 : ℝ) ^ (-k) * (2 : ℝ) ^ s := by
  rw [sub_eq_add_neg, zpow_add₀ (by norm_num), mul_comm]

private theorem two_zpow_neg_sub (s k : ℤ) :
    (2 : ℝ) ^ (-(s - k)) = (2 : ℝ) ^ k * (2 : ℝ) ^ (-s) := by
  rw [show -(s - k) = k + -s by ring, zpow_add₀ (by norm_num)]

/-- `I_{t'} = λ^{-1} I_t` for `t' = dilTile k t`, `λ = 2^k`. -/
theorem timeInt_dilTile (k : ℤ) (t : ℤ × ℤ × ℤ) :
    timeInt (dilTile k t) = (fun x : ℝ => (2 : ℝ) ^ (-k) * x) '' timeInt t := by
  unfold timeInt
  rw [Set.image_mul_left_Ico (zpow_pos (by norm_num) _)]
  simp only [dilTile, two_zpow_sub]
  congr 1 <;> ring

/-- `ω_{t',i} = λ ω_{t,i}` for `t' = dilTile k t`, `λ = 2^k`. -/
theorem freqInt_dilTile (a b k : ℤ) (i : Fin 3) (t : ℤ × ℤ × ℤ) :
    freqInt a b i (dilTile k t) = (fun x : ℝ => (2 : ℝ) ^ k * x) '' freqInt a b i t := by
  unfold freqInt
  rw [Set.image_mul_left_Ico (zpow_pos (by norm_num) _)]
  simp only [freqNum_dilTile]
  simp only [dilTile, two_zpow_neg_sub]
  congr 1 <;> ring

/-- `|I_{t'}| = λ^{-1} |I_t|`. -/
theorem toReal_volume_timeInt_dilTile (k : ℤ) (t : ℤ × ℤ × ℤ) :
    (volume (timeInt (dilTile k t))).toReal = (2 : ℝ) ^ (-k) * (volume (timeInt t)).toReal := by
  rw [toReal_volume_timeInt, toReal_volume_timeInt, dilTile, two_zpow_sub]

end PrimeBHT.TimeFrequency.Tile
