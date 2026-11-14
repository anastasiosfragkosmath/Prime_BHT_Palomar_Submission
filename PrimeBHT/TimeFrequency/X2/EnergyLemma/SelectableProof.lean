module

public import PrimeBHT.TimeFrequency.X2.EnergyLemma.SelectO
public import PrimeBHT.TimeFrequency.X2.EnergyLemma.Absorb
public import PrimeBHT.TimeFrequency.X2.Ortho.Nested

/-!
# X2, node V12: `OSelectable` reduced to a relational statement on finite families (partial results)

`OSelectable` (`SelectO.lean`) is reduced, at the level of TILES (no abstract model), to the winnability of the abstract
game of `Absorb.lean` for the tile-level relations

* `DT S Z X`: the tree of `X` meets the maximal tree `maxTree S (top Z)` (choosing `Z` destroys `X`);
* `VT k X Z`: the clause `O1` FAILS for the pair (`X` earlier than `Z`);

on finite families `C` of candidates with MINIMAL tops (`MinTop`: the maximal tree of the top is `⊆`-minimal among the
tops of the same tree).  Proved here:

* `oSelectable_of_rel`: `OSelectableRel → OSelectable` (the translation `Legal` ↔ `SelSeq ∧ OClause1`, completeness ↔
  no candidate left in the residual);
* `VT_imp_DT` (the hypothesis `V X Z → D Z X` of the abstract lemmas, from the geometry of `removal_disjoint_close`) and
  `DT_self`;
* hence `oSelectable_of_sources` / `oSelectable_of_kernel`: `OSelectable` follows from the existence, in every
  nonempty subfamily of MinTop candidates, of a source of the strict relation (resp. from a kernel of `DT`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile
open PrimeBHT.TimeFrequency.X2.Absorb

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-- Choosing `Z` destroys `X`: the tree of `X` meets the maximal tree of the top of `Z`. -/
def DT (S : Finset TriTile) (Z X : Finset TriTile × Top) : Prop := (X.1 ∩ maxTree S Z.2.1 Z.2.2).Nonempty

/-- Choosing `X` before `Z` violates the clause `O1` of `IsStronglyDisjointO`. -/
def VT (k : Fin 3) (X Z : Finset TriTile × Top) : Prop :=
  ¬ (∀ R ∈ X.1, ∀ R' ∈ Z.1, R.box ≠ R'.box → R.box.scale ≤ R'.box.scale →
      (dilate 10 (R'.box.ω k) ∩ dilate 10 (R.box.ω k)).Nonempty → Disjoint R.I (dyadicInt Z.2.1.1 Z.2.1.2))

/-- A candidate of the family `V` inside `S` whose top has a `⊆`-minimal maximal tree among the tops of the same tree. -/
def MinTop (S : Finset TriTile) (V : Finset TriTile → Top → Prop) (T : Finset TriTile × Top) : Prop :=
  V T.1 T.2 ∧ T.1 ⊆ S ∧ ∀ t' : Top, V T.1 t' → maxTree S t'.1 t'.2 ⊆ maxTree S T.2.1 T.2.2 →
    maxTree S T.2.1 T.2.2 ⊆ maxTree S t'.1 t'.2

/-- At most one top per tree in the family. -/
def OneTop (C : Finset (Finset TriTile × Top)) : Prop := ∀ T ∈ C, ∀ T' ∈ C, T.1 = T'.1 → T = T'

/-- **The relational form of the selection lemma (OPEN).**  For every finite family `C` of minimal-top candidates inside
`S` with at most one top per tree, the abstract game `Selectable (DT S) (VT k) C` is winnable. -/
def OSelectableRel : Prop :=
  ∀ (J : ℕ) (Qs : Set Box), IsRankOne J Qs → 16 ≤ J → ∀ (k : Fin 3) (S : Finset TriTile),
    (∀ R ∈ S, R.box ∈ Qs) → ∀ V : Finset TriTile → Top → Prop,
      (∀ Tr t, V Tr t → Tr.Nonempty ∧ IsTree Tr t ∧ IsLacunary k Tr) → SelClosed V →
        ∀ C : Finset (Finset TriTile × Top), (∀ T ∈ C, MinTop S V T) → OneTop C → Selectable (DT S) (VT k) C

/-! ## Translation of a legal selection into `SelSeq`, `OClause1` and completeness -/

theorem not_mem_maxTree_of_mem_removeTrees :
    ∀ (ts : List Top) (S : Finset TriTile) {R : TriTile} {t : Top}, R ∈ removeTrees S ts → t ∈ ts →
      R ∉ maxTree S t.1 t.2
  | [], _, _, _, _, ht => absurd ht List.not_mem_nil
  | t₀ :: ts, S, R, t, hR, ht => by
    have hR' : R ∈ S \ maxTree S t₀.1 t₀.2 := removeTrees_subset _ _ hR
    rcases List.mem_cons.1 ht with rfl | ht
    · exact (Finset.mem_sdiff.1 hR').2
    · intro hm
      exact not_mem_maxTree_of_mem_removeTrees ts (S \ maxTree S t₀.1 t₀.2) hR ht
        (mem_maxTree.2 ⟨hR', (mem_maxTree.1 hm).2⟩)

theorem selSeq_of_legal {V : Finset TriTile → Top → Prop} {S₀ : Finset TriTile} :
    ∀ (𝒵 : List (Finset TriTile × Top)) (R : Finset TriTile), (∀ Z ∈ 𝒵, V Z.1 Z.2 ∧ Z.1 ⊆ S₀ ∧ Z.1 ⊆ R) →
      𝒵.Pairwise (fun Z Z' => ¬ DT S₀ Z Z') → SelSeq V R 𝒵
  | [], _, _, _ => trivial
  | Z :: 𝒵, R, hZ, hp => by
    obtain ⟨h1, -, h3⟩ := hZ Z List.mem_cons_self
    obtain ⟨hp1, hp2⟩ := List.pairwise_cons.1 hp
    refine ⟨h1, h3, selSeq_of_legal 𝒵 _ (fun Z' hZ' => ?_) hp2⟩
    obtain ⟨g1, g2, g3⟩ := hZ Z' (List.mem_cons_of_mem _ hZ')
    refine ⟨g1, g2, fun x hx => Finset.mem_sdiff.2 ⟨g3 hx, fun hm => ?_⟩⟩
    exact hp1 Z' hZ' ⟨x, Finset.mem_inter.2 ⟨hx, mem_maxTree.2 ⟨g2 hx, (mem_maxTree.1 hm).2⟩⟩⟩

theorem oClause1_of_legal {k : Fin 3} {S : Finset TriTile} {𝒵 : List (Finset TriTile × Top)}
    (h : Legal (DT S) (VT k) 𝒵) : OClause1 k 𝒵 :=
  List.Pairwise.imp (fun hh => not_not.1 hh.2) h

/-- **`OSelectable` from the relational form.** -/
theorem oSelectable_of_rel (h : OSelectableRel) : OSelectable := by
  intro J Qs hQ hJ k S hS V hV hcl
  have hrep : ∀ Tr : Finset TriTile, (∃ t, V Tr t) → ∃ t, V Tr t ∧ ∀ t' : Top, V Tr t' →
      maxTree S t'.1 t'.2 ⊆ maxTree S t.1 t.2 → maxTree S t.1 t.2 ⊆ maxTree S t'.1 t'.2 := by
    rintro Tr ⟨t₀, ht₀⟩
    obtain ⟨m, ⟨t, ht, rfl⟩, hmin⟩ := (wellFounded_lt (α := Finset TriTile)).has_min
      {m | ∃ t, V Tr t ∧ m = maxTree S t.1 t.2} ⟨_, t₀, ht₀, rfl⟩
    refine ⟨t, ht, fun t' ht' hsub => ?_⟩
    by_contra hn
    exact hmin _ ⟨t', ht', rfl⟩ (hsub.ssubset_of_not_subset hn)
  choose! rep hrep1 hrep2 using hrep
  set C : Finset (Finset TriTile × Top) :=
    (S.powerset.filter fun Tr => ∃ t, V Tr t).image fun Tr => (Tr, rep Tr) with hC
  have hCmem : ∀ T ∈ C, MinTop S V T := by
    intro T hT
    obtain ⟨Tr, hTr, rfl⟩ := Finset.mem_image.1 hT
    obtain ⟨hTr1, hTr2⟩ := Finset.mem_filter.1 hTr
    exact ⟨hrep1 Tr hTr2, Finset.mem_powerset.1 hTr1, hrep2 Tr hTr2⟩
  have hone : OneTop C := by
    intro T hT T' hT' he
    obtain ⟨Tr, -, rfl⟩ := Finset.mem_image.1 hT
    obtain ⟨Tr', -, rfl⟩ := Finset.mem_image.1 hT'
    have : Tr = Tr' := he
    rw [this]
  obtain ⟨𝒵, hmem, hleg, hcov⟩ := h J Qs hQ hJ k S hS V hV hcl C hCmem hone
  refine ⟨𝒵, selSeq_of_legal 𝒵 S (fun Z hZ => ⟨(hCmem Z (hmem Z hZ)).1, (hCmem Z (hmem Z hZ)).2.1,
      (hCmem Z (hmem Z hZ)).2.1⟩) (hleg.imp fun hh => hh.1), oClause1_of_legal hleg, ?_⟩
  intro Tr hTr t ht
  have hTrS : Tr ⊆ S := hTr.trans (removeTrees_subset _ _)
  have hmemC : (Tr, rep Tr) ∈ C :=
    Finset.mem_image.2 ⟨Tr, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hTrS, ⟨t, ht⟩⟩, rfl⟩
  obtain ⟨Z, hZ, x, hx⟩ := hcov _ hmemC
  obtain ⟨hx1, hx2⟩ := Finset.mem_inter.1 hx
  exact not_mem_maxTree_of_mem_removeTrees _ S (hTr hx1) (List.mem_map_of_mem hZ) hx2

/-! ## The hypotheses of the abstract lemmas, at the level of tiles -/

theorem DT_self {S : Finset TriTile} {Z : Finset TriTile × Top} (hne : Z.1.Nonempty) (hZS : Z.1 ⊆ S)
    (hZ : IsTree Z.1 Z.2) : DT S Z Z := by
  obtain ⟨R, hR⟩ := hne
  exact ⟨R, Finset.mem_inter.2 ⟨hR, mem_maxTree.2 ⟨hZS hR, hZ R hR⟩⟩⟩

/-- A tile `R` of the earlier tree which is wide (`R.scale ≤ R'.scale`), `10`-close to a tile `R'` of the tree of `Z` with
a different box, and whose time interval meets the top of `Z`, lies in the maximal tree of `Z`. -/
theorem mem_maxTree_of_close {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {S : Finset TriTile}
    (hS : ∀ R ∈ S, R.box ∈ Qs) {k : Fin 3} {Z : Finset TriTile × Top} (hZ : IsTree Z.1 Z.2) (hZS : Z.1 ⊆ S)
    {R R' : TriTile} (hRS : R ∈ S) (hR' : R' ∈ Z.1) (hne : R.box ≠ R'.box) (hs : R.box.scale ≤ R'.box.scale)
    (hc : (dilate 10 (R'.box.ω k) ∩ dilate 10 (R.box.ω k)).Nonempty)
    (hnd : ¬ Disjoint R.I (dyadicInt Z.2.1.1 Z.2.1.2)) : R ∈ maxTree S Z.2.1 Z.2.2 := by
  obtain ⟨x₀, hx1, hx2⟩ := hc
  have hlt : R.box.scale < R'.box.scale := by
    rcases lt_or_eq_of_le hs with h | h
    · exact h
    · exfalso
      have he := hQ.2.2.2.2.2.1 R.box (hS R hRS) R'.box (hS R' (hZS hR')) hne h
      exact Set.disjoint_left.1 he (div_mem_hull_ten R.box k hx2) (div_mem_hull_ten R'.box k hx1)
  have hhull : R'.box.hull ⊆ R.box.hull := by
    obtain ⟨-, -, -, -, -, -, hf, -, -⟩ := hQ
    exact hf R'.box (hS R' (hZS hR')) R.box (hS R hRS) hlt
      ⟨x₀ / freqDir k, div_mem_hull_ten R'.box k hx1, div_mem_hull_ten R.box k hx2⟩
  obtain ⟨x, hx1, hx2⟩ := Set.not_disjoint_iff.1 hnd
  have hR'I : R'.I ⊆ dyadicInt Z.2.1.1 Z.2.1.2 := (hZ R' hR').1
  have hsc : R'.box.scale ≤ Z.2.1.1 := scale_le_of_dyadicInt_subset hR'I
  have hsub : R.I ⊆ dyadicInt Z.2.1.1 Z.2.1.2 := dyadicInt_subset_of_meet (by omega) hx1 hx2
  exact mem_maxTree.2 ⟨hRS, hsub, hhull (hZ R' hR').2⟩

/-- `V X Z → D Z X` at the level of tiles: a violation of `O1` means that choosing `Z` destroys `X`. -/
theorem VT_imp_DT {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {S : Finset TriTile}
    (hS : ∀ R ∈ S, R.box ∈ Qs) {k : Fin 3} {X Z : Finset TriTile × Top} (hXS : X.1 ⊆ S) (hZS : Z.1 ⊆ S)
    (hZ : IsTree Z.1 Z.2) (h : VT k X Z) : DT S Z X := by
  unfold VT at h
  push Not at h
  obtain ⟨R, hR, R', hR', hne, hs, hc, hnd⟩ := h
  exact ⟨R, Finset.mem_inter.2 ⟨hR, mem_maxTree_of_close hQ hS hZ hZS (hXS hR) hR' hne hs hc hnd⟩⟩

/-- The hypotheses of the abstract lemmas hold at the level of tiles for every family of candidates. -/
theorem tile_game_hyps {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {k : Fin 3} {S : Finset TriTile}
    (hS : ∀ R ∈ S, R.box ∈ Qs) {V : Finset TriTile → Top → Prop}
    (hV : ∀ Tr t, V Tr t → Tr.Nonempty ∧ IsTree Tr t ∧ IsLacunary k Tr) {C : Finset (Finset TriTile × Top)}
    (hC : ∀ T ∈ C, MinTop S V T) :
    (∀ X ∈ C, DT S X X) ∧ ∀ X ∈ C, ∀ Z ∈ C, VT k X Z → DT S Z X := by
  refine ⟨fun X hX => ?_, fun X hX Z hZ hv => ?_⟩
  · obtain ⟨h1, h2, -⟩ := hC X hX
    obtain ⟨hne, htree, -⟩ := hV _ _ h1
    exact DT_self hne h2 htree
  · obtain ⟨h1, h2, -⟩ := hC X hX
    obtain ⟨g1, g2, -⟩ := hC Z hZ
    exact VT_imp_DT hQ hS h2 g2 (hV _ _ g1).2.1 hv

/-- `OSelectable` from a KERNEL of `DT` (an independent set of candidates destroying all the others) in every finite
family of minimal-top candidates. -/
theorem oSelectable_of_kernel
    (h : ∀ (J : ℕ) (Qs : Set Box), IsRankOne J Qs → 16 ≤ J → ∀ (k : Fin 3) (S : Finset TriTile),
      (∀ R ∈ S, R.box ∈ Qs) → ∀ V : Finset TriTile → Top → Prop,
        (∀ Tr t, V Tr t → Tr.Nonempty ∧ IsTree Tr t ∧ IsLacunary k Tr) → SelClosed V →
          ∀ C : Finset (Finset TriTile × Top), (∀ T ∈ C, MinTop S V T) → OneTop C →
            ∃ K ⊆ C, (∀ Z ∈ K, ∀ Z' ∈ K, Z ≠ Z' → ¬ DT S Z Z') ∧ ∀ X ∈ C, ∃ Z ∈ K, DT S Z X) : OSelectable := by
  refine oSelectable_of_rel fun J Qs hQ hJ k S hS V hV hcl C hC hone => ?_
  obtain ⟨-, hVD⟩ := tile_game_hyps hQ hS hV hC
  obtain ⟨K, hKC, hind, habs⟩ := h J Qs hQ hJ k S hS V hV hcl C hC hone
  exact selectable_of_kernel hVD hKC hind habs

end PrimeBHT.TimeFrequency.X2
