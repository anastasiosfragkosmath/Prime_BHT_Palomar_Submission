module

public import PrimeBHT.TimeFrequency.X2.EnergyLemma.Defs
public import PrimeBHT.TimeFrequency.X2.EnergyLemma.Geom
public import PrimeBHT.TimeFrequency.X2.Ortho.Families
public import PrimeBHT.TimeFrequency.X2.Ortho.Geometry

/-!
# X2, node V10: the nested form of strong disjointness (`IsStronglyDisjointN`) and the shell obstruction

`IsStronglyDisjointN` (`EnergyLemma/Defs.lean`) is the form produced by the V12 selection: tile sets pairwise
disjoint, and `ω_R ⊆ ω_{R'}` (distinct boxes) gives `I_{R'} ∩ I_{T(R)} = ∅`.

The TT* argument of V10 (`Ortho/TileBasicA.lean`, nested block `S₂`) needs, for `R'` of a different tree with
`R'.scale ≤ R.scale`, distinct box and `3`-close to `R`, that `I_{R'}` is disjoint from the top of the tree of `R`.
For `IsStronglyDisjointN` this is available exactly when `ω_R ⊆ ω_{R'}`.  A **shell pair** is a pair of distinct
boxes with `10`-dilated slot-`k` intervals meeting and neither interval inside the other (the finer box sits in the
`3`-dilated neighbourhood of the coarser one, outside it).  Shell pairs are NOT excluded by the fields (a)-(h) of
`IsRankOne` nor by the V05 classes: chains of shell pairs give counterexamples to `pint` for `IsStronglyDisjointN`
(report of this node).  What the proof of `pint` needs is the distinct-box `10`-close form:

* `IsStronglyDisjointO k 𝒯`: DPLMV's strong disjointness (`10`-close, both orientations) for pairs of tiles with
  DISTINCT boxes, tile sets pairwise disjoint; `IsStronglyDisjointO.{pairwise_disjoint, restrictFamily, disjoint_top}`,
  `no_three_close_O` (multiplicity `≤ 2`);
* `removal_disjoint_close`: the clause `O2` (wide tile in the LATER tree) follows from the removal of the maximal
  tree for ALL `10`-close pairs; the clause `O1` (wide tile in the EARLIER tree) is what the ordering of the selection
  must provide, and fails for shell chains;
* `NoShell k 𝒯`: family-level absence of shell pairs between different trees; `IsStronglyDisjointN` + `NoShell`
  give `IsStronglyDisjointO` (`IsStronglyDisjointO.of_nested_noShell`); `noShell_of_scale_eq`: a family of tiles of ONE
  box scale has no shell pairs (field (e));
* the nested API `IsStronglyDisjointN.{pairwise_disjoint, restrictFamily, disjoint_top}`, `NoShell.restrictFamily`,
  `no_three_close_N`.
-/

@[expose] public noncomputable section

open MeasureTheory
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- **No shell pairs** between different trees of the family: tiles of different trees with distinct boxes whose
`10`-dilated slot-`k` frequency intervals meet have NESTED frequency intervals. -/
def NoShell (k : Fin 3) (𝒯 : List (Finset TriTile × Top)) : Prop :=
  ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → ∀ R ∈ T.1, ∀ R' ∈ T'.1, R.box ≠ R'.box →
    (dilate 10 (R.box.ω k) ∩ dilate 10 (R'.box.ω k)).Nonempty →
      R.box.ω k ⊆ R'.box.ω k ∨ R'.box.ω k ⊆ R.box.ω k

/-- The tile sets of a nested strongly disjoint family are pairwise disjoint (a field of the predicate). -/
theorem IsStronglyDisjointN.pairwise_disjoint {k : Fin 3} {𝒯 : List (Finset TriTile × Top)}
    (h : IsStronglyDisjointN k 𝒯) : 𝒯.Pairwise (fun T T' => Disjoint T.1 T'.1) :=
  h.2.imp fun hh => hh.1

/-- Nested strong disjointness is inherited by sub-families `T ∩ 𝒬` (same tops). -/
theorem IsStronglyDisjointN.restrictFamily {k : Fin 3} {𝒯 : List (Finset TriTile × Top)}
    (h : IsStronglyDisjointN k 𝒯) (𝒬 : Finset TriTile) :
    IsStronglyDisjointN k (restrictFamily 𝒬 𝒯) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro T hT
    obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.1 hT
    obtain ⟨ht, hl⟩ := h1 T₀ hT₀
    refine ⟨fun R hR => ht R (Finset.mem_inter.1 hR).1, fun R hR R' hR' hne => ?_⟩
    exact hl R (Finset.mem_inter.1 hR).1 R' (Finset.mem_inter.1 hR').1 hne
  · refine List.Pairwise.map _ (fun T T' hTT' => ?_) h2
    refine ⟨?_, fun R hR R' hR' => hTT'.2.1 R (Finset.mem_inter.1 hR).1 R' (Finset.mem_inter.1 hR').1,
      fun R hR R' hR' => hTT'.2.2 R (Finset.mem_inter.1 hR).1 R' (Finset.mem_inter.1 hR').1⟩
    exact Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left hTT'.1)

theorem NoShell.restrictFamily {k : Fin 3} {𝒯 : List (Finset TriTile × Top)} (h : NoShell k 𝒯)
    (𝒬 : Finset TriTile) : NoShell k (restrictFamily 𝒬 𝒯) := by
  intro T hT T' hT' hne R hR R' hR' hb h10
  obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.1 hT
  obtain ⟨T₀', hT₀', rfl⟩ := List.mem_map.1 hT'
  have hne₀ : T₀ ≠ T₀' := fun hh => hne (by rw [hh])
  exact h T₀ hT₀ T₀' hT₀' hne₀ R (Finset.mem_inter.1 hR).1 R' (Finset.mem_inter.1 hR').1 hb h10

/-- Nested strong disjointness, both orientations of a pair of different trees. -/
theorem IsStronglyDisjointN.disjoint_top {k : Fin 3} {𝒯 : List (Finset TriTile × Top)}
    (h : IsStronglyDisjointN k 𝒯) {T T' : Finset TriTile × Top} (hT : T ∈ 𝒯) (hT' : T' ∈ 𝒯)
    (hne : T ≠ T') {R R' : TriTile} (hR : R ∈ T.1) (hR' : R' ∈ T'.1) (hb : R.box ≠ R'.box)
    (hω : R.box.ω k ⊆ R'.box.ω k) : Disjoint R'.I (dyadicInt T.2.1.1 T.2.1.2) := by
  let rel : Finset TriTile × Top → Finset TriTile × Top → Prop := fun T T' =>
    (∀ R ∈ T.1, ∀ R' ∈ T'.1, R.box ≠ R'.box → R'.box.ω k ⊆ R.box.ω k →
          Disjoint R.I (dyadicInt T'.2.1.1 T'.2.1.2)) ∧
      (∀ R ∈ T.1, ∀ R' ∈ T'.1, R.box ≠ R'.box → R.box.ω k ⊆ R'.box.ω k →
          Disjoint R'.I (dyadicInt T.2.1.1 T.2.1.2))
  have : Std.Symm rel :=
    ⟨fun a b hab => ⟨fun R hR R' hR' hb hω => hab.2 R' hR' R hR hb.symm hω,
      fun R hR R' hR' hb hω => hab.1 R' hR' R hR hb.symm hω⟩⟩
  have hrel : rel T T' := (h.2.imp fun hh => hh.2).forall hT hT' hne
  exact hrel.2 R hR R' hR' hb hω

/-- If `x ∈ dilate C ω_k(B)` and `C ≤ hullDil` then `x / freqDir k ∈ hull B`. -/
theorem div_mem_hull_of (B : Box) (k : Fin 3) {C x : ℝ} (hC : C ≤ hullDil)
    (h1 : B.centre k - C * (2 : ℝ) ^ (-B.scale) / 2 ≤ x) (h2 : x ≤ B.centre k + C * (2 : ℝ) ^ (-B.scale) / 2) :
    x / freqDir k ∈ B.hull := by
  have hd := freqDir_pos k
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
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

theorem div_mem_hull_ten (B : Box) (k : Fin 3) {x : ℝ} (hx : x ∈ dilate 10 (B.ω k)) :
    x / freqDir k ∈ B.hull := by
  rw [mem_dilate_omega] at hx
  exact div_mem_hull_of B k (by unfold hullDil; norm_num) hx.1 hx.2.le

/-! ## The distinct-box form `IsStronglyDisjointO` (DPLMV's `10`-close form without the same-box pairs) -/

/-- **`k`-strong disjointness, distinct-box `10`-close form** (DPLMV L1129-1136, restricted to pairs of tiles with
DISTINCT boxes, with tile-set disjointness as a separate conjunct).  Compared with the built `IsStronglyDisjoint`
the same-box pairs are dropped (two trees may share a box with nested tops: no selection can avoid that); compared
with `IsStronglyDisjointN` the nested hypothesis `ω_R ⊆ ω_{R'}` is replaced by `10`-closeness (SHELL pairs are
included).  `IsStronglyDisjointN` + `NoShell` imply it (`IsStronglyDisjointO.of_nested_noShell`). -/
def IsStronglyDisjointO (k : Fin 3) (𝒯 : List (Finset TriTile × Top)) : Prop :=
  (∀ T ∈ 𝒯, IsTree T.1 T.2 ∧ IsLacunary k T.1) ∧
    𝒯.Pairwise (fun T T' =>
      Disjoint T.1 T'.1 ∧
      (∀ R ∈ T.1, ∀ R' ∈ T'.1, R.box ≠ R'.box → R.box.scale ≤ R'.box.scale →
          (dilate 10 (R'.box.ω k) ∩ dilate 10 (R.box.ω k)).Nonempty →
          Disjoint R.I (dyadicInt T'.2.1.1 T'.2.1.2)) ∧
      (∀ R ∈ T.1, ∀ R' ∈ T'.1, R.box ≠ R'.box → R'.box.scale ≤ R.box.scale →
          (dilate 10 (R'.box.ω k) ∩ dilate 10 (R.box.ω k)).Nonempty →
          Disjoint R'.I (dyadicInt T.2.1.1 T.2.1.2)))

theorem IsStronglyDisjointO.pairwise_disjoint {k : Fin 3} {𝒯 : List (Finset TriTile × Top)}
    (h : IsStronglyDisjointO k 𝒯) : 𝒯.Pairwise (fun T T' => Disjoint T.1 T'.1) :=
  h.2.imp fun hh => hh.1

theorem IsStronglyDisjointO.restrictFamily {k : Fin 3} {𝒯 : List (Finset TriTile × Top)}
    (h : IsStronglyDisjointO k 𝒯) (𝒬 : Finset TriTile) :
    IsStronglyDisjointO k (restrictFamily 𝒬 𝒯) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro T hT
    obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.1 hT
    obtain ⟨ht, hl⟩ := h1 T₀ hT₀
    refine ⟨fun R hR => ht R (Finset.mem_inter.1 hR).1, fun R hR R' hR' hne => ?_⟩
    exact hl R (Finset.mem_inter.1 hR).1 R' (Finset.mem_inter.1 hR').1 hne
  · refine List.Pairwise.map _ (fun T T' hTT' => ?_) h2
    refine ⟨?_, fun R hR R' hR' => hTT'.2.1 R (Finset.mem_inter.1 hR).1 R' (Finset.mem_inter.1 hR').1,
      fun R hR R' hR' => hTT'.2.2 R (Finset.mem_inter.1 hR).1 R' (Finset.mem_inter.1 hR').1⟩
    exact Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left hTT'.1)

/-- Both orientations of a pair of different trees. -/
theorem IsStronglyDisjointO.disjoint_top {k : Fin 3} {𝒯 : List (Finset TriTile × Top)}
    (h : IsStronglyDisjointO k 𝒯) {T T' : Finset TriTile × Top} (hT : T ∈ 𝒯) (hT' : T' ∈ 𝒯)
    (hne : T ≠ T') {R R' : TriTile} (hR : R ∈ T.1) (hR' : R' ∈ T'.1) (hb : R'.box ≠ R.box)
    (hs : R'.box.scale ≤ R.box.scale)
    (hc : (dilate 10 (R'.box.ω k) ∩ dilate 10 (R.box.ω k)).Nonempty) :
    Disjoint R'.I (dyadicInt T.2.1.1 T.2.1.2) := by
  let rel : Finset TriTile × Top → Finset TriTile × Top → Prop := fun T T' =>
    (∀ R ∈ T.1, ∀ R' ∈ T'.1, R.box ≠ R'.box → R.box.scale ≤ R'.box.scale →
          (dilate 10 (R'.box.ω k) ∩ dilate 10 (R.box.ω k)).Nonempty →
          Disjoint R.I (dyadicInt T'.2.1.1 T'.2.1.2)) ∧
      (∀ R ∈ T.1, ∀ R' ∈ T'.1, R.box ≠ R'.box → R'.box.scale ≤ R.box.scale →
          (dilate 10 (R'.box.ω k) ∩ dilate 10 (R.box.ω k)).Nonempty →
          Disjoint R'.I (dyadicInt T.2.1.1 T.2.1.2))
  have : Std.Symm rel :=
    ⟨fun a b hab => ⟨fun R hR R' hR' hb hs hc => hab.2 R' hR' R hR hb.symm hs (by rwa [Set.inter_comm]),
      fun R hR R' hR' hb hs hc => hab.1 R' hR' R hR hb.symm hs (by rwa [Set.inter_comm])⟩⟩
  have hrel : rel T T' := (h.2.imp fun hh => hh.2).forall hT hT' hne
  exact hrel.2 R hR R' hR' hb.symm hs hc

/-- **(b) multiplicity `≤ 2`, distinct-box `10`-close form.** -/
theorem no_three_close_O {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {k : Fin 3}
    {𝒯 : List (Finset TriTile × Top)} (hSD : IsStronglyDisjointO k 𝒯)
    (hbox : ∀ T ∈ 𝒯, ∀ R ∈ T.1, R.box ∈ Qs) {R₀ R₁ R₂ R₃ : TriTile}
    (h₁ : R₁ ∈ tilesOf 𝒯) (h₂ : R₂ ∈ tilesOf 𝒯) (h₃ : R₃ ∈ tilesOf 𝒯)
    (s₁ : R₁.box.scale ≤ R₀.box.scale) (s₂ : R₂.box.scale ≤ R₀.box.scale) (s₃ : R₃.box.scale ≤ R₀.box.scale)
    (c₁ : FreqClose k R₁ R₀) (c₂ : FreqClose k R₂ R₀) (c₃ : FreqClose k R₃ R₀)
    (n₁₂ : R₁ ≠ R₂) (n₁₃ : R₁ ≠ R₃) (n₂₃ : R₂ ≠ R₃) {x : ℝ} (x₁ : x ∈ R₁.I) (x₂ : x ∈ R₂.I)
    (x₃ : x ∈ R₃.I) : False := by
  obtain ⟨T₁, hT₁, hR₁⟩ := mem_tilesOf.1 h₁
  obtain ⟨T₂, hT₂, hR₂⟩ := mem_tilesOf.1 h₂
  obtain ⟨T₃, hT₃, hR₃⟩ := mem_tilesOf.1 h₃
  have hdisj := hSD.pairwise_disjoint
  have cross : ∀ {T T' : Finset TriTile × Top} {R R' : TriTile}, T ∈ 𝒯 → T' ∈ 𝒯 → T ≠ T' → R ∈ T.1 →
      R' ∈ T'.1 → R.box.scale ≤ R₀.box.scale → R'.box.scale ≤ R₀.box.scale → FreqClose k R R₀ →
      FreqClose k R' R₀ → ∀ y, y ∈ R.I → y ∈ R'.I → False := by
    intro T T' R R' hT hT' hne hR hR' hs hs' hc hc' y hy hy'
    by_cases hb : R.box = R'.box
    · have hRR' : R = R' :=
        eq_of_omega_eq_of_I_inter (k := k) hQ (hbox T hT R hR) (hbox T' hT' R' hR') (by rw [hb]) hy hy'
      subst hRR'
      have hsymm : Std.Symm (fun T T' : Finset TriTile × Top => Disjoint T.1 T'.1) :=
        ⟨fun a b hab => hab.symm⟩
      exact Finset.disjoint_left.1 (hdisj.forall hT hT' hne) hR hR'
    · have h10 := FreqClose.dilate_ten_of_both hc hc' hs hs'
      rcases le_total R.box.scale R'.box.scale with hle | hle
      · have hd := hSD.disjoint_top hT' hT hne.symm hR' hR hb hle h10
        exact Set.disjoint_left.1 hd hy (((hSD.1 T' hT').1 R' hR').1 hy')
      · have hd := hSD.disjoint_top hT hT' hne hR hR' (Ne.symm hb) hle (by rwa [Set.inter_comm])
        exact Set.disjoint_left.1 hd hy' (((hSD.1 T hT).1 R hR).1 hy)
  have same : ∀ {T T' : Finset TriTile × Top} {R R' : TriTile}, T ∈ 𝒯 → T' ∈ 𝒯 → R ∈ T.1 → R' ∈ T'.1 →
      R.box.scale ≤ R₀.box.scale → R'.box.scale ≤ R₀.box.scale → FreqClose k R R₀ →
      FreqClose k R' R₀ → x ∈ R.I → x ∈ R'.I → T = T' := by
    intro T T' R R' hT hT' hR hR' hs hs' hc hc' hx hx'
    by_contra hne
    exact cross hT hT' hne hR hR' hs hs' hc hc' x hx hx'
  have e₁₂ := same hT₁ hT₂ hR₁ hR₂ s₁ s₂ c₁ c₂ x₁ x₂
  have e₁₃ := same hT₁ hT₃ hR₁ hR₃ s₁ s₃ c₁ c₃ x₁ x₃
  subst e₁₂ e₁₃
  have hlac := (hSD.1 T₁ hT₁).2
  refine IsLacunary.not_three_close hlac hR₁ hR₂ hR₃ s₁ s₂ s₃ c₁ c₂ c₃ ?_ ?_ ?_
  · intro h
    exact n₁₂ (eq_of_omega_eq_of_I_inter hQ (hbox _ hT₁ _ hR₁) (hbox _ hT₁ _ hR₂) h x₁ x₂)
  · intro h
    exact n₁₃ (eq_of_omega_eq_of_I_inter hQ (hbox _ hT₁ _ hR₁) (hbox _ hT₁ _ hR₃) h x₁ x₃)
  · intro h
    exact n₂₃ (eq_of_omega_eq_of_I_inter hQ (hbox _ hT₁ _ hR₂) (hbox _ hT₁ _ hR₃) h x₂ x₃)

/-! ## The removal clause of the selection holds for ALL `10`-close pairs (not only nested ones) -/

/-- **Removal of the maximal tree, `10`-close form** (MTT2 Lemma 7.7, "remove the maximal tree"; generalizes
`removal_disjoint` from nested `ω_R ⊆ ω_{R'}` to `10`-close distinct boxes with `R'.scale ≤ R.scale`, shell pairs
included): a tile `R'` of the residual, `10`-close to a tile `R` of the removed tree and of larger-or-equal frequency
interval, has `I_{R'}` disjoint from the top.  (This is the clause `O2` of `IsStronglyDisjointO` for a pair
`T` (earlier), `T'` (later) of a greedy selection; the clause `O1` -- the wide tile in the EARLIER tree -- is the one
the ordering of the selection has to provide, and it fails for shell pairs.) -/
theorem removal_disjoint_close {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {S : Finset TriTile}
    (hS : ∀ R ∈ S, R.box ∈ Qs) {k : Fin 3} {T : Finset TriTile × Top} (hT : IsTree T.1 T.2)
    {T' : Finset TriTile} (hT' : T' ⊆ S \ maxTree S T.2.1 T.2.2) {R R' : TriTile} (hR : R ∈ T.1)
    (hRS : R ∈ S) (hR' : R' ∈ T') (hne : R'.box ≠ R.box) (hs : R'.box.scale ≤ R.box.scale)
    (hc : (dilate 10 (R'.box.ω k) ∩ dilate 10 (R.box.ω k)).Nonempty) :
    Disjoint R'.I (dyadicInt T.2.1.1 T.2.1.2) := by
  have hR'S := Finset.mem_sdiff.1 (hT' hR')
  obtain ⟨x₀, hx1, hx2⟩ := hc
  have hlt : R'.box.scale < R.box.scale := by
    rcases lt_or_eq_of_le hs with h | h
    · exact h
    · exfalso
      have he := hQ.2.2.2.2.2.1 R'.box (hS R' hR'S.1) R.box (hS R hRS) hne h
      exact Set.disjoint_left.1 he (div_mem_hull_ten R'.box k hx1) (div_mem_hull_ten R.box k hx2)
  have hhull : R.box.hull ⊆ R'.box.hull := by
    obtain ⟨-, -, -, -, -, -, hf, -, -⟩ := hQ
    exact hf R.box (hS R hRS) R'.box (hS R' hR'S.1) hlt
      ⟨x₀ / freqDir k, div_mem_hull_ten R.box k hx2, div_mem_hull_ten R'.box k hx1⟩
  rw [Set.disjoint_iff]
  intro x ⟨hx1, hx2⟩
  have hRI : R.I ⊆ dyadicInt T.2.1.1 T.2.1.2 := (hT R hR).1
  have hsc : R.box.scale ≤ T.2.1.1 := scale_le_of_dyadicInt_subset hRI
  have hsub : R'.I ⊆ dyadicInt T.2.1.1 T.2.1.2 :=
    dyadicInt_subset_of_meet (by omega) hx1 hx2
  exact hR'S.2 (mem_maxTree.2 ⟨hR'S.1, hsub, hhull (hT R hR).2⟩)

end PrimeBHT.TimeFrequency.X2
