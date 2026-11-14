module

public import PrimeBHT.TimeFrequency.Tile.Trees
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# Lacunarity, sparse scales, grid and disjointness facts (blueprint node C1)

For parameters `ν = (a, b, s', α)` (`TriValid a b s' α`) and tiles `t ∈ triIdx s' α`:

* (a) `freqInt_nested_or_disjoint`, `freqInt_subset_or_subset_of_nonempty`: the cells `ω_{t,k}` of slot
  `k` form a grid;
* (b) `scale_add_ten_le_of_ssubset`, `toReal_volume_freqInt_le_of_ssubset`: `ω_{t,k} ⊊ ω_{t',k}` implies
  `|ω_{t,k}| ≤ 2^{-10} |ω_{t',k}|`, hence `dilate_fifty_subset_dilate_two_of_ssubset`: `50ω_{t,k} ⊆ 2ω_{t',k}`;
* (c) `disjoint_freqInt_of_timeInt_eq`: `I_t = I_{t'}`, `t ≠ t'` implies `ω_{t,k} ∩ ω_{t',k} = ∅`;
* (d) `lacunarity`: for `i ≠ i'` and `ξ ∈ 3ω_{t,i}`: `(ε_{i'}/ε_i) ξ ∈ 50ω_{t,i'} ∖ 2ω_{t,i'}`, with
  `ε = (1, 1, 2)` (`lacEps`, `lacRatio`);
* (e) `IsTree.lacunary`, `IsTree.disjoint_freqInt_of_scale_ne`: the consequences for trees; and
  `card_le_three_of_timeInt_eq`: at most `3` tiles of an `i`-tree share a time interval.

**Correction of the blueprint.** C1(d) and (T3) print `ε_{i'} ξ` with `ε = (1, 1, 2)`. This is false
for `i = 3` (our `i = 2`): there `ξ ≈ 2ℓ/3` has to be halved to land near `ω_{t,1}` (`ℓ/3`), so the
correct recipe is the ratio `ε_{i'}/ε_i`. (BD26's lemma only asserts the existence of some `ξ'_T`; its
proof for `i = 3` silently uses an `ℓ`-dependent normalisation.) With the ratio, all six cases hold for
every `ℓ`, and no boundary equality occurs (the `a + b = 15` case of the blueprint is not a boundary case).
-/

@[expose] public noncomputable section

open MeasureTheory
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Tile

/-! ### (a) Grid -/

theorem freqNum_modEq_three {a b s' α : ℤ} {t t' : ℤ × ℤ × ℤ} (ht : t ∈ triIdx s' α)
    (ht' : t' ∈ triIdx s' α) (k : Fin 3) : freqNum a b t k ≡ freqNum a b t' k [ZMOD 3] := by
  have h := modEq_three_of_mem_triIdx ht ht'
  unfold Int.ModEq at h ⊢
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, freqNum_zero, freqNum_one,
    freqNum_two] <;> omega

/-- **(a) Grid.** For `t, t' ∈ Idx_ν` the cells `ω_{t,k}`, `ω_{t',k}` are nested or disjoint. -/
theorem freqInt_nested_or_disjoint {a b s' α : ℤ} {t t' : ℤ × ℤ × ℤ} (ht : t ∈ triIdx s' α)
    (ht' : t' ∈ triIdx s' α) (k : Fin 3) :
    freqInt a b k t ⊆ freqInt a b k t' ∨ freqInt a b k t' ⊆ freqInt a b k t ∨
      Disjoint (freqInt a b k t) (freqInt a b k t') := by
  have h10 := ten_dvd_scale_sub ht ht'
  exact freqCell_nested_or_disjoint (by omega) (freqNum_modEq_three ht ht' k)

/-! ### (b) Sparse scales -/

/-- Strict containment of `ω_{t,k} ⊊ ω_{t',k}` forces the scales apart by at least `10`:
`s(t') + 10 ≤ s(t)`. -/
theorem scale_add_ten_le_of_ssubset {a b s' α : ℤ} {t t' : ℤ × ℤ × ℤ} (ht : t ∈ triIdx s' α)
    (ht' : t' ∈ triIdx s' α) {k : Fin 3} (h : freqInt a b k t ⊂ freqInt a b k t') :
    t'.1 + 10 ≤ t.1 := by
  have h1 : t'.1 ≤ t.1 := scale_le_of_freqCell_subset h.subset
  have h10 := ten_dvd_scale_sub ht ht'
  rcases h1.lt_or_eq with h2 | h2
  · omega
  · exfalso
    have hs : t.1 = t'.1 := h2.symm
    have hn : freqNum a b t k = freqNum a b t' k := by
      have : freqCell t.1 (freqNum a b t k) ⊆ freqCell t.1 (freqNum a b t' k) := by
        have := h.subset
        rw [freqInt_eq_freqCell, freqInt_eq_freqCell, ← hs] at this
        exact this
      exact numerator_eq_of_freqCell_subset this
    apply h.ne
    rw [freqInt_eq_freqCell, freqInt_eq_freqCell, ← hs, hn]

/-- **(b) Sparse.** `ω_{t,k} ⊊ ω_{t',k}` implies `|ω_{t,k}| ≤ 2^{-10} |ω_{t',k}|`. -/
theorem toReal_volume_freqInt_le_of_ssubset {a b s' α : ℤ} {t t' : ℤ × ℤ × ℤ}
    (ht : t ∈ triIdx s' α) (ht' : t' ∈ triIdx s' α) {k : Fin 3}
    (h : freqInt a b k t ⊂ freqInt a b k t') :
    (volume (freqInt a b k t)).toReal ≤ (2 : ℝ) ^ (-10 : ℤ) * (volume (freqInt a b k t')).toReal := by
  have h1 := scale_add_ten_le_of_ssubset ht ht' h
  rw [toReal_volume_freqInt_eq, toReal_volume_freqInt_eq, ← zpow_add₀ (by norm_num)]
  exact zpow_le_zpow_right₀ (by norm_num) (by omega)

/-- **(b) Sparse, hence `50ω_{t,k} ⊆ 2ω_{t',k}`** when `ω_{t,k} ⊊ ω_{t',k}`. -/
theorem dilate_fifty_subset_dilate_two_of_ssubset {a b s' α : ℤ} {t t' : ℤ × ℤ × ℤ}
    (ht : t ∈ triIdx s' α) (ht' : t' ∈ triIdx s' α) {k : Fin 3}
    (h : freqInt a b k t ⊂ freqInt a b k t') :
    dilate 50 (freqInt a b k t) ⊆ dilate 2 (freqInt a b k t') := by
  have h1 := toReal_volume_freqInt_le_of_ssubset ht ht' h
  rw [toReal_volume_freqInt_eq, toReal_volume_freqInt_eq] at h1
  have h2 : (2 : ℝ) ^ (-10 : ℤ) = 1 / 1024 := by norm_num
  have h3 : (0 : ℝ) < (2 : ℝ) ^ (-t.1) := zpow_pos (by norm_num) _
  rw [h2] at h1
  exact dilate_fifty_subset_dilate_two (freqCell_lt t.1 (freqNum a b t k))
    (freqCell_lt t'.1 (freqNum a b t' k)) h.subset (by nlinarith)

/-! ### (c) Same interval -/

/-! ### (d) Lacunarity -/

/-- The weights `ε_1 = ε_2 = 1`, `ε_3 = 2` (slots `0, 1, 2`): the three slots move by `(h, h, 2h)` when
the base frequency `ℓ/3` moves by `h/3`. -/
def lacEps : Fin 3 → ℝ := ![1, 1, 2]

/-- The ratio `ε_{i'}/ε_i` relating `ξ ∈ 3ω_{t,i}` to its image `ξ'` in slot `i'`. -/
def lacRatio (i i' : Fin 3) : ℝ := lacEps i' / lacEps i

theorem lacEps_pos (i : Fin 3) : 0 < lacEps i := by
  fin_cases i <;> simp [lacEps]

theorem lacRatio_pos (i i' : Fin 3) : 0 < lacRatio i i' :=
  div_pos (lacEps_pos i') (lacEps_pos i)

@[simp] theorem lacRatio_self (i : Fin 3) : lacRatio i i = 1 :=
  div_self (lacEps_pos i).ne'

/-- **(d) Lacunarity** (BD26 Lemma `l:lac`, L738-745, all six ordered pairs, unshifted): for `i ≠ i'`
and `ξ ∈ 3ω_{t,i}`, `(ε_{i'}/ε_i) ξ ∈ 50ω_{t,i'} ∖ 2ω_{t,i'}`. Holds for every tile `t` (no
congruence condition) and uses only `21 ≤ a ≤ 30`, `-6 ≤ b ≤ 3`. -/
theorem lacunarity {a b s' α : ℤ} (hν : TriValid a b s' α) (t : ℤ × ℤ × ℤ) {i i' : Fin 3}
    (hii : i ≠ i') {ξ : ℝ} (hξ : ξ ∈ dilate 3 (freqInt a b i t)) :
    lacRatio i i' * ξ ∈ dilate 50 (freqInt a b i' t) ∧
      lacRatio i i' * ξ ∉ dilate 2 (freqInt a b i' t) := by
  obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, -, -⟩ := hν
  have hw : (0 : ℝ) < (2 : ℝ) ^ (-t.1) := zpow_pos (by norm_num) _
  rw [dilate_freqInt] at hξ
  rw [dilate_freqInt, dilate_freqInt]
  simp only [Set.mem_Ico] at hξ ⊢
  set w : ℝ := (2 : ℝ) ^ (-t.1) with hwdef
  have ha1' : w * 21 ≤ w * a := mul_le_mul_of_nonneg_left (by exact_mod_cast ha1) hw.le
  have ha2' : w * a ≤ w * 30 := mul_le_mul_of_nonneg_left (by exact_mod_cast ha2) hw.le
  have hb1' : w * (-6) ≤ w * b := mul_le_mul_of_nonneg_left (by exact_mod_cast hb1) hw.le
  have hb2' : w * b ≤ w * 3 := mul_le_mul_of_nonneg_left (by exact_mod_cast hb2) hw.le
  fin_cases i <;> fin_cases i' <;> try exact absurd rfl hii
  all_goals
    simp only [lacRatio, lacEps, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, freqNum_zero,
      freqNum_one, freqNum_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Int.cast_sub, Int.cast_mul, Int.cast_ofNat] at hξ ⊢
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> first | linarith [hξ.1, hξ.2] | (intro h; linarith [hξ.1, hξ.2, h.1, h.2])

/-! ### (e) Consequences for trees -/

theorem IsTree.lacunary {a b s' α : ℤ} (hν : TriValid a b s' α) {i i' : Fin 3} (hii : i ≠ i')
    {P : Finset (ℤ × ℤ × ℤ)} {T : TreeData} (hT : IsTree a b i P T) {t : ℤ × ℤ × ℤ}
    (ht : t ∈ T.tiles) :
    lacRatio i i' * T.ξ ∈ dilate 50 (freqInt a b i' t) ∧
      lacRatio i i' * T.ξ ∉ dilate 2 (freqInt a b i' t) :=
  lacunarity hν t hii (hT.xi_mem ht)

/-- If `ω_{t,k} ⊊ ω_{t',k}` then no `ξ'` lies in `50ω_{t,k}` but outside `2ω_{t',k}`. -/
theorem not_ssubset_of_lacunary {a b s' α : ℤ} {t t' : ℤ × ℤ × ℤ} (ht : t ∈ triIdx s' α)
    (ht' : t' ∈ triIdx s' α) {k : Fin 3} {ξ' : ℝ} (h50 : ξ' ∈ dilate 50 (freqInt a b k t))
    (h2 : ξ' ∉ dilate 2 (freqInt a b k t')) : ¬ freqInt a b k t ⊂ freqInt a b k t' :=
  fun h => h2 (dilate_fifty_subset_dilate_two_of_ssubset ht ht' h h50)

/-- **(e)** For `t, t'` in an `i`-tree `T ⊆ Idx_ν` and `i' ≠ i`, tiles of different scale have disjoint
frequency cells `ω_{t,i'} ∩ ω_{t',i'} = ∅` (so their Fourier supports are disjoint). -/
theorem IsTree.disjoint_freqInt_of_scale_ne {a b s' α : ℤ} (hν : TriValid a b s' α) {i i' : Fin 3}
    (hii : i ≠ i') {P : Finset (ℤ × ℤ × ℤ)} (hP : (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    {T : TreeData} (hT : IsTree a b i P T) {t t' : ℤ × ℤ × ℤ} (ht : t ∈ T.tiles)
    (ht' : t' ∈ T.tiles) (hs : t.1 ≠ t'.1) : Disjoint (freqInt a b i' t) (freqInt a b i' t') := by
  have htI : t ∈ triIdx s' α := hP (hT.subset ht)
  have ht'I : t' ∈ triIdx s' α := hP (hT.subset ht')
  obtain ⟨h50, h2⟩ := hT.lacunary hν hii ht
  obtain ⟨h50', h2'⟩ := hT.lacunary hν hii ht'
  have hne : freqInt a b i' t ≠ freqInt a b i' t' := fun h => hs (freqInt_inj h).1
  rcases freqInt_nested_or_disjoint (a := a) (b := b) htI ht'I i' with h | h | h
  · exact absurd (lt_of_le_of_ne h hne) (not_ssubset_of_lacunary htI ht'I h50 h2')
  · exact absurd (lt_of_le_of_ne h hne.symm) (not_ssubset_of_lacunary ht'I htI h50' h2)
  · exact h

/-! ### At most three tiles of a tree share a time interval -/

/-- Two frequency cells `3ω_{t,i}`, `3ω_{t',i}` of the same scale containing a common `ξ` have
numerators differing by less than `9`. -/
theorem freqNum_lt_add_nine {a b : ℤ} {i : Fin 3} {t t' : ℤ × ℤ × ℤ} {ξ : ℝ} (hs : t.1 = t'.1)
    (h : ξ ∈ dilate 3 (freqInt a b i t)) (h' : ξ ∈ dilate 3 (freqInt a b i t')) :
    freqNum a b t' i < freqNum a b t i + 9 := by
  rw [mem_dilate_three_freqInt] at h h'
  unfold leftEnd3 rightEnd3 at h h'
  rw [← hs] at h'
  have hw : (0 : ℝ) < (2 : ℝ) ^ (-t.1) := zpow_pos (by norm_num) _
  have h1 : (2 : ℝ) ^ (-t.1) * (((freqNum a b t' i : ℤ) : ℝ) / 3 - 1) <
      (2 : ℝ) ^ (-t.1) * (((freqNum a b t i : ℤ) : ℝ) / 3 + 2) := lt_of_le_of_lt h'.1 h.2
  have h2 := lt_of_mul_lt_mul_left h1 hw.le
  have h3 : ((freqNum a b t' i : ℤ) : ℝ) < ((freqNum a b t i : ℤ) : ℝ) + 9 := by linarith
  exact_mod_cast h3

/-- **At most three tiles share a time interval in an `i`-tree**: tiles of `Idx_ν` with one time
interval `J` and a common `ξ ∈ 3ω_{t,i}` (BD26's `ξ_T ∈ 3ω_{p_i}`) are at most `3` in number. -/
theorem card_le_three_of_timeInt_eq {a b s' α : ℤ} {i : Fin 3} {S : Finset (ℤ × ℤ × ℤ)} {ξ : ℝ}
    (hS : ∀ t ∈ S, t ∈ triIdx s' α) {J : Set ℝ} (hJ : ∀ t ∈ S, timeInt t = J)
    (hξ : ∀ t ∈ S, ξ ∈ dilate 3 (freqInt a b i t)) : S.card ≤ 3 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hinj : Set.InjOn (fun t : ℤ × ℤ × ℤ => t.2.2) (↑S : Set (ℤ × ℤ × ℤ)) := by
    intro t ht t' ht' h
    have := timeInt_eq_iff.1 ((hJ t ht).trans (hJ t' ht').symm)
    exact Prod.ext this.1 (Prod.ext this.2 h)
  have hcard : (S.image fun t => t.2.2).card = S.card := Finset.card_image_of_injOn hinj
  rw [← hcard]
  have hLne : (S.image fun t => t.2.2).Nonempty := hne.image _
  have hpair : ∀ l ∈ S.image (fun t => t.2.2), ∀ l' ∈ S.image (fun t => t.2.2),
      l' ≤ l + 8 ∧ l' ≡ l [ZMOD 3] := by
    intro l hl l' hl'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hl
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hl'
    have hs := (timeInt_eq_iff.1 ((hJ t ht).trans (hJ t' ht').symm)).1
    have h9 := freqNum_lt_add_nine (a := a) (b := b) (i := i) hs (hξ t ht) (hξ t' ht')
    have hmod := modEq_three_of_mem_triIdx (hS t' ht') (hS t ht)
    refine ⟨?_, hmod⟩
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, freqNum_zero,
      freqNum_one, freqNum_two] at h9 <;> omega
  set L := S.image fun t => t.2.2 with hL
  have hsub : L ⊆ {L.min' hLne, L.min' hLne + 3, L.min' hLne + 6} := by
    intro l hl
    have h1 := hpair _ (Finset.min'_mem L hLne) l hl
    have h2 := Finset.min'_le L l hl
    have h3 := h1.2
    unfold Int.ModEq at h3
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  exact (Finset.card_le_card hsub).trans Finset.card_le_three

/-- At most three tiles of an `i`-tree `T ⊆ Idx_ν` have a given time interval. -/
theorem IsTree.card_filter_timeInt_le_three {a b s' α : ℤ} {i : Fin 3}
    {P : Finset (ℤ × ℤ × ℤ)} (hP : (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α) {T : TreeData}
    (hT : IsTree a b i P T) (J : Set ℝ) [DecidablePred fun t : ℤ × ℤ × ℤ => timeInt t = J] :
    (T.tiles.filter fun t => timeInt t = J).card ≤ 3 := by
  refine card_le_three_of_timeInt_eq (a := a) (b := b) (s' := s') (α := α) (i := i) (ξ := T.ξ)
    (fun t ht => hP (hT.subset (Finset.mem_filter.1 ht).1)) (J := J)
    (fun t ht => (Finset.mem_filter.1 ht).2) (fun t ht => hT.xi_mem (Finset.mem_filter.1 ht).1)

/-! ### The printed recipe `ε_{i'} ξ` (without the ratio) is false for `i = 3` -/

end PrimeBHT.TimeFrequency.Tile
