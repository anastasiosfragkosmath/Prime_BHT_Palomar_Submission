module

public import PrimeBHT.TimeFrequency.Tile.Bessel.Defs
public import PrimeBHT.TimeFrequency.Tile.Lacunary
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# The contributing tiles (blueprint C4, step 5 (i)-(iii), unshifted)

Let `𝒯` be a finite family of `i`-trees in `P ⊆ Idx_ν`, pairwise `k`-strongly disjoint, `i ≠ k`.
For `t ∈ T ∈ 𝒯` call `t'` (a tile of a tree `T' ∈ 𝒯`) *contributing* if `s(t') < s(t)` and
`ω_{t,k} ∩ ω_{t',k} ≠ ∅`. Then:

* `ssubset_of_contrib`: `ω_{t,k} ⊊ ω_{t',k}`;
* `disjoint_timeInt_topInt_of_contrib` (steps (i), (ii)): `I_{t'} ∩ I_T = ∅`;
* `disjoint_timeInt_of_contrib` (step (iii)): two contributing tiles `t' ≠ t''` have disjoint time
  intervals.
-/

public section

open MeasureTheory
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Tile

section Contrib

variable {a b s' α : ℤ} {k : Fin 3}

theorem freqNum_inj_ell {t t' : ℤ × ℤ × ℤ} (h : freqNum a b t k = freqNum a b t' k) :
    t.2.2 = t'.2.2 := by
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, freqNum_zero, freqNum_one,
    freqNum_two] at h <;> omega

theorem left_mem_freqInt (a b : ℤ) (k : Fin 3) (t : ℤ × ℤ × ℤ) :
    (2 : ℝ) ^ (-t.1) * ((freqNum a b t k : ℝ) / 3) ∈ freqInt a b k t :=
  ⟨le_rfl, freqCell_lt t.1 (freqNum a b t k)⟩

/-- A tile `t'` of strictly smaller scale whose frequency cell meets that of `t` has
`ω_{t,k} ⊊ ω_{t',k}` (grid + lengths). -/
theorem ssubset_of_contrib {t t' : ℤ × ℤ × ℤ} (ht : t ∈ triIdx s' α) (ht' : t' ∈ triIdx s' α)
    (hs : t'.1 < t.1) (hnd : ¬ Disjoint (freqInt a b k t) (freqInt a b k t')) :
    freqInt a b k t ⊂ freqInt a b k t' := by
  rcases freqInt_nested_or_disjoint (a := a) (b := b) ht ht' k with h | h | h
  · refine Set.ssubset_iff_subset_ne.2 ⟨h, fun heq => ?_⟩
    have := (freqInt_inj heq).1
    omega
  · exfalso
    have := scale_le_of_freqCell_subset h
    omega
  · exact absurd h hnd

/-- Distinct trees of a strongly disjoint family cannot contain tiles `t, t'` with
`ω_{t,k} ⊊ ω_{t',k}` in one tree (lacunarity). -/
theorem eq_of_ssubset_of_mem {i : Fin 3} (hν : TriValid a b s' α) (hik : i ≠ k)
    {P : Finset (ℤ × ℤ × ℤ)} (hP : (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α) {T : TreeData}
    (hT : IsTree a b i P T) {t t' : ℤ × ℤ × ℤ} (ht : t ∈ T.tiles) (ht' : t' ∈ T.tiles) :
    ¬ freqInt a b k t ⊂ freqInt a b k t' := by
  have htI : t ∈ triIdx s' α := hP (hT.subset ht)
  have ht'I : t' ∈ triIdx s' α := hP (hT.subset ht')
  obtain ⟨h50, -⟩ := hT.lacunary hν hik ht
  obtain ⟨-, h2'⟩ := hT.lacunary hν hik ht'
  exact not_ssubset_of_lacunary htI ht'I h50 h2'

variable {i : Fin 3} {P : Finset (ℤ × ℤ × ℤ)} {𝒯 : Finset TreeData}

/-- Steps (i) and (ii) of the claim: a contributing tile has its time interval disjoint from `I_T`. -/
theorem disjoint_timeInt_topInt_of_contrib (hν : TriValid a b s' α) (hik : i ≠ k)
    (hP : (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α) (h𝒯 : ∀ T ∈ 𝒯, IsTree a b i P T)
    (hSD : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → StronglyDisjoint a b k T T')
    {T T' : TreeData} (hT : T ∈ 𝒯) (hT' : T' ∈ 𝒯) {t t' : ℤ × ℤ × ℤ} (ht : t ∈ T.tiles)
    (ht' : t' ∈ T'.tiles) (hs : t'.1 < t.1)
    (hnd : ¬ Disjoint (freqInt a b k t) (freqInt a b k t')) :
    Disjoint (timeInt t') T.topInt := by
  have htI : t ∈ triIdx s' α := hP ((h𝒯 T hT).subset ht)
  have ht'I : t' ∈ triIdx s' α := hP ((h𝒯 T' hT').subset ht')
  have hss := ssubset_of_contrib htI ht'I hs hnd
  have hne : T ≠ T' := by
    rintro rfl
    exact eq_of_ssubset_of_mem hν hik hP (h𝒯 T hT) ht ht' hss
  have hSD' := hSD T hT T' hT' hne t ht t' ht' hss
  have hsub := scale_le_of_dyadicInt_subset ((h𝒯 T hT).timeInt_subset ht)
  rcases dyadicInt_nested_or_disjoint t'.1 t'.2.1 T.top.1 T.top.2 with h1 | h1 | h1
  · exact absurd h1 hSD'
  · have := scale_le_of_dyadicInt_subset h1
    omega
  · exact h1

/-- The ordered form of step (iii): `ω_{t',k} ⊊ ω_{t'',k}` with `t'`, `t''` in trees of `𝒯` gives
disjoint time intervals. -/
theorem disjoint_timeInt_of_ssubset (hν : TriValid a b s' α) (hik : i ≠ k)
    (hP : (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α) (h𝒯 : ∀ T ∈ 𝒯, IsTree a b i P T)
    (hSD : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → StronglyDisjoint a b k T T')
    {T' T'' : TreeData} (hT' : T' ∈ 𝒯) (hT'' : T'' ∈ 𝒯) {t' t'' : ℤ × ℤ × ℤ}
    (ht' : t' ∈ T'.tiles) (ht'' : t'' ∈ T''.tiles)
    (hss : freqInt a b k t' ⊂ freqInt a b k t'') : Disjoint (timeInt t') (timeInt t'') := by
  have ht'I : t' ∈ triIdx s' α := hP ((h𝒯 T' hT').subset ht')
  have ht''I : t'' ∈ triIdx s' α := hP ((h𝒯 T'' hT'').subset ht'')
  have hne : T' ≠ T'' := by
    rintro rfl
    exact eq_of_ssubset_of_mem hν hik hP (h𝒯 T' hT') ht' ht'' hss
  have hSD' := hSD T' hT' T'' hT'' hne t' ht' t'' ht'' hss
  have hsc := scale_add_ten_le_of_ssubset ht'I ht''I hss
  rcases timeInt_nested_or_disjoint t' t'' with h1 | h1 | h1
  · exfalso
    have := scale_le_of_dyadicInt_subset h1
    omega
  · exact absurd (h1.trans ((h𝒯 T' hT').timeInt_subset ht')) hSD'
  · exact h1

/-- Step (iii) of the claim: two distinct tiles, both contributing for `t`, have disjoint time
intervals. -/
theorem disjoint_timeInt_of_contrib (hν : TriValid a b s' α) (hik : i ≠ k)
    (hP : (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α) (h𝒯 : ∀ T ∈ 𝒯, IsTree a b i P T)
    (hSD : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → StronglyDisjoint a b k T T')
    {T' T'' : TreeData} (hT' : T' ∈ 𝒯) (hT'' : T'' ∈ 𝒯) {t t' t'' : ℤ × ℤ × ℤ}
    (ht' : t' ∈ T'.tiles) (ht'' : t'' ∈ T''.tiles)
    (hss' : freqInt a b k t ⊂ freqInt a b k t') (hss'' : freqInt a b k t ⊂ freqInt a b k t'')
    (hne : t' ≠ t'') : Disjoint (timeInt t') (timeInt t'') := by
  have ht'I : t' ∈ triIdx s' α := hP ((h𝒯 T' hT').subset ht')
  have ht''I : t'' ∈ triIdx s' α := hP ((h𝒯 T'' hT'').subset ht'')
  rcases freqInt_nested_or_disjoint (a := a) (b := b) ht'I ht''I k with h | h | h
  · by_cases heq : freqInt a b k t' = freqInt a b k t''
    · obtain ⟨hs, hn⟩ := freqInt_inj heq
      have hl : t'.2.2 = t''.2.2 := freqNum_inj_ell hn
      refine disjoint_timeInt_of_scale_eq hs fun hv => hne ?_
      exact Prod.ext hs (Prod.ext hv hl)
    · exact disjoint_timeInt_of_ssubset hν hik hP h𝒯 hSD hT' hT'' ht' ht''
        (Set.ssubset_iff_subset_ne.2 ⟨h, heq⟩)
  · by_cases heq : freqInt a b k t'' = freqInt a b k t'
    · obtain ⟨hs, hn⟩ := freqInt_inj heq
      have hl : t''.2.2 = t'.2.2 := freqNum_inj_ell hn
      refine disjoint_timeInt_of_scale_eq hs.symm fun hv => hne ?_
      exact Prod.ext hs.symm (Prod.ext hv hl.symm)
    · exact (disjoint_timeInt_of_ssubset hν hik hP h𝒯 hSD hT'' hT' ht'' ht'
        (Set.ssubset_iff_subset_ne.2 ⟨h, heq⟩)).symm
  · exact absurd h (Set.not_disjoint_iff.2
      ⟨_, hss'.subset (left_mem_freqInt a b k t), hss''.subset (left_mem_freqInt a b k t)⟩)

end Contrib

end PrimeBHT.TimeFrequency.Tile
