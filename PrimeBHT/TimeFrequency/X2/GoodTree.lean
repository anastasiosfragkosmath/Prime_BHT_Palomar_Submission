module

public import PrimeBHT.TimeFrequency.X2.Collections

/-!
# `goodTree_maxTree` (V06, B4 (c), MTT2 Lemma 4.7)

A maximal tree of a RESIDUAL of a translation-closed base collection of boxes of a rank-1 set is a good tree
(tree conditions b. and c.). The proof needs exactly the fields (e) (one box per scale) and (f) (hull nesting)
of `IsRankOne`. Finding X2-I6 of `docs/audits/X2-V06-V05-check.md`: with fields (a)-(e) only the statement is
FALSE (explicit counterexample, exact arithmetic), so (f) was added to `IsRankOne`; the route check's step B4(c)
was mislabelled CHECKED. The proof was found by the Opus audit worker and checked here.
-/

@[expose] public section

namespace PrimeBHT.TimeFrequency.X2

open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

noncomputable section

open Classical

theorem removeTrees_subset (Cs : Finset TriTile) (ts : List Top) : removeTrees Cs ts ⊆ Cs := by
  induction ts generalizing Cs with
  | nil => exact subset_rfl
  | cons t ts ih => exact (ih _).trans Finset.sdiff_subset

/-- Removal history: a tile of the base that is no longer in the residual was removed by a maximal tree
of an intermediate collection which contains the residual and is disjoint from it. -/
theorem exists_removed (Cs : Finset TriTile) (ts : List Top) {R : TriTile} (hR : R ∈ Cs)
    (hR' : R ∉ removeTrees Cs ts) :
    ∃ (C : Finset TriTile) (t : Top), removeTrees Cs ts ⊆ C ∧ R ∈ maxTree C t.1 t.2 ∧
      Disjoint (removeTrees Cs ts) (maxTree C t.1 t.2) := by
  induction ts generalizing Cs with
  | nil => exact absurd hR hR'
  | cons t ts ih =>
    rw [removeTrees] at hR' ⊢
    by_cases hm : R ∈ maxTree Cs t.1 t.2
    · refine ⟨Cs, t, (removeTrees_subset _ _).trans Finset.sdiff_subset, hm, ?_⟩
      exact Finset.disjoint_of_subset_left (removeTrees_subset _ _) Finset.sdiff_disjoint
    · exact ih (Cs \ maxTree Cs t.1 t.2) (Finset.mem_sdiff.2 ⟨hR, hm⟩) hR'

/-- A dyadic interval meeting `W` at a scale `≤ W`'s scale lies in `W`. -/
theorem dyadicInt_subset_of_meet {s v : ℤ} {W : ℤ × ℤ} {x : ℝ} (hs : s ≤ W.1)
    (hx : x ∈ dyadicInt s v) (hxW : x ∈ dyadicInt W.1 W.2) : dyadicInt s v ⊆ dyadicInt W.1 W.2 := by
  rcases dyadicInt_nested_or_disjoint s v W.1 W.2 with h | h | h
  · exact h
  · have h1 := scale_le_of_dyadicInt_subset h
    have hseq : W.1 = s := le_antisymm h1 hs
    have hv := index_eq_of_dyadicInt_subset hseq h
    rw [← hseq, ← hv]
  · exact absurd (Set.disjoint_left.1 h hx) (not_not.2 hxW)

/-- **`goodTree_maxTree`** with field (f): a maximal tree of a residual of a TC base of boxes of a
rank-1 set is good. -/
theorem goodTree_maxTree {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs)
    {Cs₀ Cs : Finset TriTile} (hbox : ∀ R ∈ Cs₀, R.box ∈ Qs) (hTC : HasTC Cs₀)
    (hres : IsResidual Cs₀ Cs) (t : Top) : IsGoodTree (maxTree Cs t.1 t.2) t := by
  obtain ⟨-, -, -, -, -, he, hf, -, -⟩ := hQ
  obtain ⟨ts, rfl⟩ := hres
  set T := maxTree (removeTrees Cs₀ ts) t.1 t.2 with hT
  have hsub : removeTrees Cs₀ ts ⊆ Cs₀ := removeTrees_subset _ _
  -- tree condition b. from field (e)
  have hb : ∀ R ∈ T, ∀ R' ∈ T, R.box.scale = R'.box.scale → R.box = R'.box := by
    intro R hR R' hR' hs
    rw [hT, mem_maxTree] at hR hR'
    by_contra hne
    exact Set.disjoint_left.1 (he _ (hbox _ (hsub hR.1)) _ (hbox _ (hsub hR'.1)) hne hs) hR.2.2 hR'.2.2
  -- the translate argument (MTT2 Lemma 4.7) with field (f)
  have key : ∀ R ∈ T, ∀ R' ∈ T, R'.box.scale ≤ R.box.scale →
      ∃ R'' ∈ T, R''.box = R.box ∧ R'.I ⊆ R''.I := by
    intro R hR R' hR' hsc
    rcases hsc.lt_or_eq with hlt | heq
    · obtain ⟨v, hv⟩ := exists_dyadicInt_superset R'.box.scale R'.pos hlt.le
      set R'' : TriTile := ⟨R.box, v⟩ with hR''
      have hR'I : R'.I ⊆ R''.I := hv
      have hRm := (mem_maxTree.1 (hT ▸ hR))
      have hR'm := (mem_maxTree.1 (hT ▸ hR'))
      have h0 : R'' ∈ Cs₀ := hTC R (hsub hRm.1) R' (hsub hR'm.1) R'' rfl hsc hR'I
      have hscW : R.box.scale ≤ t.1.1 := scale_le_of_dyadicInt_subset hRm.2.1
      obtain ⟨x, hx⟩ := dyadicInt_nonempty R'.box.scale R'.pos
      have hR''W : R''.I ⊆ dyadicInt t.1.1 t.1.2 :=
        dyadicInt_subset_of_meet hscW (hR'I hx) (hR'm.2.1 hx)
      by_cases hin : R'' ∈ removeTrees Cs₀ ts
      · exact ⟨R'', mem_maxTree.2 ⟨hin, hR''W, hRm.2.2⟩, rfl, hR'I⟩
      · exfalso
        obtain ⟨C, t', hC, hmem, hdisj⟩ := exists_removed Cs₀ ts h0 hin
        have hm := mem_maxTree.1 hmem
        have hnest : R.box.hull ⊆ R'.box.hull :=
          hf _ (hbox _ (hsub hRm.1)) _ (hbox _ (hsub hR'm.1)) hlt ⟨t.2, hRm.2.2, hR'm.2.2⟩
        have hR'C : R' ∈ maxTree C t'.1 t'.2 :=
          mem_maxTree.2 ⟨hC hR'm.1, hR'I.trans hm.2.1, hnest hm.2.2⟩
        exact Finset.disjoint_left.1 hdisj hR'm.1 hR'C
    · exact ⟨R', hR', (hb R hR R' hR' heq.symm).symm, subset_rfl⟩
  refine ⟨fun R hR => (mem_maxTree.1 hR).2, hb, ?_⟩
  intro R hR R' hR' hsc x hx
  simp only [Set.mem_iUnion, Finset.mem_filter] at hx ⊢
  obtain ⟨R₁, ⟨hR₁, hR₁b⟩, hx⟩ := hx
  obtain ⟨R₂, hR₂, hR₂b, hsub₂⟩ := key R hR R₁ hR₁ (by rw [hR₁b]; exact hsc)
  exact ⟨R₂, ⟨hR₂, hR₂b⟩, hsub₂ hx⟩

end

end PrimeBHT.TimeFrequency.X2
