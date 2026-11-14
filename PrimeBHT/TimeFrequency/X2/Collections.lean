module

public import PrimeBHT.TimeFrequency.X2.Classes
public import PrimeBHT.TimeFrequency.Tile.Inside

/-!
# X2, node V06: rank-1 box sets, window-full collections, translation closure, maximal trees, residuals,
trees, lacunarity, strong disjointness, single-scale layers

Definitions of `drafts/x2-interface/02-V06-Collections.lean.txt` and the `insidePart` of `06-V16-Defs`
(design doc `docs/x2-interface-design.md` §3, V06), with the easy lemmas proved:

* `IsWindowFull.hasTC` (B4 (a)), `HasTC.outsidePart` (B4 (b)), `IsWindowFull.layer`;
* `isResidual_refl`, `IsResidual.removeTrees`;
* `IsTree.box_eq_of_scale_eq` (B4 (d), MTT2 Lemma 4.4, from field (e) of `IsRankOne`);
* `mem_layer_iff_of_subset` (B3: each tile inside `Ω` lies in exactly one layer of a maximal dyadic interval of `Ω`).

`goodTree_maxTree` (B4 (c)) is deliberately NOT stated here: it is under audit (X2-I6).

The X2-F12 repair: V05 delivers WINDOW-FULL collections of a rank-1 box set with STANDARD-DYADIC time
intervals (`TriTile.I = dyadicInt scale pos`); every intermediate collection is a RESIDUAL (translation-closed
base minus successively removed MAXIMAL trees), never an arbitrary subset; layers are window-full again.

## Deviations from the draft

* module header and imports (`Tile.Inside` for `maxDyadicKeys`);
* in `IsWindowFull.layer` the collection is written `X2.layer` (the name `layer` would otherwise be ambiguous
  inside the namespace `IsWindowFull`).
-/

@[expose] public noncomputable section

open MeasureTheory
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-- The slot-`k` frequency interval in NORMALIZED coordinates (`ω_k / freqDir k`). -/
def Box.ωn (B : Box) (k : Fin 3) : Set ℝ :=
  Set.Ico ((B.centre k - (2 : ℝ) ^ (-B.scale) / 2) / freqDir k)
    ((B.centre k + (2 : ℝ) ^ (-B.scale) / 2) / freqDir k)

/-- The bound `256` on the hull length of a box (in units of `2^{-scale}`), field (h) of `IsRankOne` (REV3: the hull is the
convex hull of `hullDil = 128` times the slot intervals; V05's hull length is `(|d_b| + 128) ≤ 193`). -/
def hullConst : ℝ := 256

/-- **Rank-1 box set** (DPLMV L496-505, a-d; MTT2 §2 sparse collections).  This is a CONTRACT between
V05 (producer) and V06/V10-V13 (consumers): the V05 worker proves these fields; consumers may ask to
ADD fields (only V05 has to prove them), never to remove them.  The numerology of (c), (d) is DPLMV's
and must be checked against MTT2 L394-507 by the V05/V06 worker (UNVERIFIED as numerology). -/
def IsRankOne (J : ℕ) (Qs : Set Box) : Prop :=
  -- (a) J-dyadic scales (time intervals of length 2^{J j}); scale separation is then automatic
  (∀ B ∈ Qs, ∀ B' ∈ Qs, (J : ℤ) ∣ B.scale - B'.scale) ∧
  -- (a) each family {ω_k} is a grid: nested or disjoint
  (∀ B ∈ Qs, ∀ B' ∈ Qs, ∀ k, B.ω k ⊆ B'.ω k ∨ B'.ω k ⊆ B.ω k ∨ Disjoint (B.ω k) (B'.ω k)) ∧
  -- (b) distinct boxes of the same scale have disjoint frequency intervals in every slot
  (∀ B ∈ Qs, ∀ B' ∈ Qs, B ≠ B' → B.scale = B'.scale → ∀ k, Disjoint (B.ω k) (B'.ω k)) ∧
  -- (c) ω_{P_k} ⊆ ω_{P'_k} for some k ⇒ 2^{J/2} ω_P ⊆ 2^{J/2} ω_{P'}
  (∀ B ∈ Qs, ∀ B' ∈ Qs, ∀ k, B.ω k ⊆ B'.ω k →
      dilate ((2 : ℝ) ^ ((J : ℝ) / 2)) B.hull ⊆ dilate ((2 : ℝ) ^ ((J : ℝ) / 2)) B'.hull) ∧
  -- (d) ω_{P_j} ⊆ ω_{P'_j} (distinct boxes) ⇒ 3ω_{P_k} ∩ 3ω_{P'_k} = ∅ for k ≠ j
  (∀ B ∈ Qs, ∀ B' ∈ Qs, B ≠ B' → ∀ j, B.ω j ⊆ B'.ω j → ∀ k, k ≠ j →
      Disjoint (dilate 3 (B.ω k)) (dilate 3 (B'.ω k))) ∧
  -- (e) ADDED (MTT2 L403-408 sparse single scale; needed for tree condition b., MTT2 Lemma 4.4):
  -- distinct boxes of the same scale have disjoint hulls
  (∀ B ∈ Qs, ∀ B' ∈ Qs, B ≠ B' → B.scale = B'.scale → Disjoint B.hull B'.hull) ∧
  -- (f) ADDED (finding X2-I6 of `docs/audits/X2-V06-V05-check.md`; X2 form of MTT2 Lemma 2.1): hull nesting,
  -- a finer box whose hull meets the hull of a coarser box lies inside it
  (∀ B ∈ Qs, ∀ B' ∈ Qs, B'.scale < B.scale → (B.hull ∩ B'.hull).Nonempty → B.hull ⊆ B'.hull) ∧
  -- (g) ADDED (finding X2-I9 of `docs/audits/X2-V13-route-check.md`; MTT2's single-box Whitney condition): the normalized
  -- 4-dilates of the three slot intervals of a box are pairwise disjoint (needed for the lacunary split of a tree)
  (∀ B ∈ Qs, ∀ k k' : Fin 3, k ≠ k' → Disjoint (dilate 4 (B.ωn k)) (dilate 4 (B.ωn k'))) ∧
  -- (h) ADDED (same finding): the hull has length at most `hullConst * 2^{-scale}`
  (∀ B ∈ Qs, ∀ x ∈ B.hull, ∀ y ∈ B.hull, |x - y| ≤ hullConst * (2 : ℝ) ^ (-B.scale))

/-- **Window-full** collection (X2-F12 repair): all tiles whose box lies in a finite `Q ⊆ Qs` and whose
time interval lies in the standard dyadic window `W`. -/
def IsWindowFull (Qs : Set Box) (Ps : Finset TriTile) : Prop :=
  ∃ (Q : Finset Box) (W : ℤ × ℤ), (↑Q : Set Box) ⊆ Qs ∧
    ∀ R : TriTile, R ∈ Ps ↔ R.box ∈ Q ∧ R.I ⊆ dyadicInt W.1 W.2

/-- **Translation closure (TC)** (MTT2 Lemma 4.7, L817-844, exactly what its proof uses). -/
def HasTC (Cs : Finset TriTile) : Prop :=
  ∀ R ∈ Cs, ∀ R' ∈ Cs, ∀ R'' : TriTile, R''.box = R.box → R'.box.scale ≤ R.box.scale →
    R'.I ⊆ R''.I → R'' ∈ Cs

/-- The maximal tree of `Cs` with top `(I_W, ξ)`: all tiles with `I ⊆ I_W` and `ξ ∈ ω_P` (hull),
DPLMV tree condition a. read literally.  The frequency condition is the one place where V06 may have
to switch to MTT2's tile order with enlarged intervals (Def 4.1-4.3, L683-750) to make
`goodTree_maxTree` provable; such a change touches only this BODY, no statement downstream. -/
def maxTree (Cs : Finset TriTile) (W : ℤ × ℤ) (ξ : ℝ) : Finset TriTile :=
  Cs.filter (fun R => R.I ⊆ dyadicInt W.1 W.2 ∧ ξ ∈ R.box.hull)

/-- Top data `(W, ξ)` of a tree. -/
abbrev Top : Type := (ℤ × ℤ) × ℝ

/-- Remove the maximal trees with the given tops, successively. -/
def removeTrees (Cs : Finset TriTile) : List Top → Finset TriTile
  | [] => Cs
  | t :: ts => removeTrees (Cs \ maxTree Cs t.1 t.2) ts

/-- The removed trees, in order (each is a maximal tree of the collection current at its time). -/
def removedTrees (Cs : Finset TriTile) : List Top → List (Finset TriTile × Top)
  | [] => []
  | t :: ts => (maxTree Cs t.1 t.2, t) :: removedTrees (Cs \ maxTree Cs t.1 t.2) ts

/-- **Residual** of a base `Cs₀`: the base minus successively removed maximal trees (MTT2 Def 9.1
"convex = full tile set minus greedy trees", L2458-2464). -/
def IsResidual (Cs₀ Cs : Finset TriTile) : Prop :=
  ∃ ts : List Top, Cs = removeTrees Cs₀ ts

/-- A tree with top `(W, ξ)` (DPLMV tree condition a.): `I_P ⊆ I_W`, `ξ ∈ ω_P`. -/
def IsTree (Tr : Finset TriTile) (t : Top) : Prop :=
  ∀ R ∈ Tr, R.I ⊆ dyadicInt t.1.1 t.1.2 ∧ t.2 ∈ R.box.hull

/-- DPLMV tree conditions b. (one box per scale) and c. (nested spatial sets `E_{Q,T}`). -/
def IsGoodTree (Tr : Finset TriTile) (t : Top) : Prop :=
  IsTree Tr t ∧
    (∀ R ∈ Tr, ∀ R' ∈ Tr, R.box.scale = R'.box.scale → R.box = R'.box) ∧
    -- c.: the coarse box's spatial set contains the fine box's (R coarse in time, R' fine)
    ∀ R ∈ Tr, ∀ R' ∈ Tr, R'.box.scale ≤ R.box.scale →
      (⋃ R'' ∈ Tr.filter (fun R'' => R''.box = R'.box), R''.I) ⊆
        ⋃ R'' ∈ Tr.filter (fun R'' => R''.box = R.box), R''.I

/-- `k`-lacunary: distinct intervals `3 ω_{P_k}` are disjoint. -/
def IsLacunary (k : Fin 3) (Tr : Finset TriTile) : Prop :=
  ∀ R ∈ Tr, ∀ R' ∈ Tr, R.box.ω k ≠ R'.box.ω k → Disjoint (dilate 3 (R.box.ω k)) (dilate 3 (R'.box.ω k))

/-- `k`-strongly disjoint family of `k`-lacunary trees (DPLMV L1129-1136; internal contract of the
V10-V12 cluster: the V12 worker produces it, V10/V11 consume it; they may adjust it jointly). -/
def IsStronglyDisjoint (k : Fin 3) (𝒯 : List (Finset TriTile × Top)) : Prop :=
  (∀ T ∈ 𝒯, IsTree T.1 T.2 ∧ IsLacunary k T.1) ∧
    𝒯.Pairwise (fun T T' =>
      (∀ R ∈ T.1, ∀ R' ∈ T'.1, R.box.scale ≤ R'.box.scale →
          (dilate 10 (R'.box.ω k) ∩ dilate 10 (R.box.ω k)).Nonempty →
          Disjoint R.I (dyadicInt T'.2.1.1 T'.2.1.2)) ∧
      (∀ R ∈ T.1, ∀ R' ∈ T'.1, R'.box.scale ≤ R.box.scale →
          (dilate 10 (R'.box.ω k) ∩ dilate 10 (R.box.ω k)).Nonempty →
          Disjoint R'.I (dyadicInt T.2.1.1 T.2.1.2)))

/-- The single-scale layer `L_{W,n} = {P ∈ Ps : I_P ⊆ W, |I_P| = 2^{-n}|W|}` (route check B3). -/
def layer (Ps : Finset TriTile) (W : ℤ × ℤ) (n : ℕ) : Finset TriTile :=
  Ps.filter (fun R => R.I ⊆ dyadicInt W.1 W.2 ∧ R.box.scale = W.1 - n)

/-- The outside part `{P ∈ Ps : I_P ⊄ Ω}`. -/
def outsidePart (Ps : Finset TriTile) (Ω : Set ℝ) : Finset TriTile :=
  Ps.filter (fun R => ¬ R.I ⊆ Ω)

/-- The inside part `{P ∈ Ps : I_P ⊆ Ω}`. -/
def insidePart (Ps : Finset TriTile) (Ω : Set ℝ) : Finset TriTile :=
  Ps.filter (fun R => R.I ⊆ Ω)

/-! ## Basic membership lemmas -/

theorem mem_maxTree {Cs : Finset TriTile} {W : ℤ × ℤ} {ξ : ℝ} {R : TriTile} :
    R ∈ maxTree Cs W ξ ↔ R ∈ Cs ∧ R.I ⊆ dyadicInt W.1 W.2 ∧ ξ ∈ R.box.hull := by
  simp [maxTree]

theorem mem_layer {Ps : Finset TriTile} {W : ℤ × ℤ} {n : ℕ} {R : TriTile} :
    R ∈ layer Ps W n ↔ R ∈ Ps ∧ R.I ⊆ dyadicInt W.1 W.2 ∧ R.box.scale = W.1 - n := by
  simp [layer]

theorem mem_outsidePart {Ps : Finset TriTile} {Ω : Set ℝ} {R : TriTile} :
    R ∈ outsidePart Ps Ω ↔ R ∈ Ps ∧ ¬ R.I ⊆ Ω := by
  simp [outsidePart]

theorem mem_insidePart {Ps : Finset TriTile} {Ω : Set ℝ} {R : TriTile} :
    R ∈ insidePart Ps Ω ↔ R ∈ Ps ∧ R.I ⊆ Ω := by
  simp [insidePart]

theorem TriTile.I_nonempty (R : TriTile) : R.I.Nonempty :=
  dyadicInt_nonempty _ _

/-! ## V06 lemmas -/

/-- B4(a): window-full ⇒ TC. -/
theorem IsWindowFull.hasTC {Qs : Set Box} {Ps : Finset TriTile} (h : IsWindowFull Qs Ps) :
    HasTC Ps := by
  obtain ⟨Q, W, -, hP⟩ := h
  intro R hR R' hR' R'' hbox _ hsub
  obtain ⟨hRQ, hRW⟩ := (hP R).1 hR
  obtain ⟨-, hR'W⟩ := (hP R').1 hR'
  refine (hP R'').2 ⟨hbox ▸ hRQ, ?_⟩
  rcases dyadicInt_nested_or_disjoint R''.box.scale R''.pos W.1 W.2 with h1 | h1 | h1
  · exact h1
  · -- `W ⊆ I_{R''}`: the scales force equality
    have hs1 := scale_le_of_dyadicInt_subset h1
    have hs2 : R.box.scale ≤ W.1 := scale_le_of_dyadicInt_subset hRW
    have hs : W.1 = R''.box.scale := by
      have : R''.box.scale = R.box.scale := by rw [hbox]
      omega
    have hv := index_eq_of_dyadicInt_subset hs h1
    have : dyadicInt W.1 W.2 = dyadicInt R''.box.scale R''.pos := by
      rw [hs, hv]
    exact this.ge
  · exfalso
    obtain ⟨x, hx⟩ := TriTile.I_nonempty R'
    exact Set.disjoint_left.1 h1 (hsub hx) (hR'W hx)

/-- B4(b): TC passes to the outside part. -/
theorem HasTC.outsidePart {Cs : Finset TriTile} (h : HasTC Cs) (Ω : Set ℝ) :
    HasTC (X2.outsidePart Cs Ω) := by
  intro R hR R' hR' R'' hbox hle hsub
  rw [mem_outsidePart] at hR hR' ⊢
  refine ⟨h R hR.1 R' hR'.1 R'' hbox hle hsub, fun hsubΩ => hR'.2 (hsub.trans hsubΩ)⟩

/-- Layers of a window-full collection are window-full (so they are TC bases for V12 and V15). -/
theorem IsWindowFull.layer {Qs : Set Box} {Ps : Finset TriTile} (h : IsWindowFull Qs Ps)
    (W : ℤ × ℤ) (n : ℕ) : IsWindowFull Qs (X2.layer Ps W n) := by
  obtain ⟨Q₀, W₀, hQ₀, hP⟩ := h
  have hQ : (↑(Q₀.filter (fun B => B.scale = W.1 - n)) : Set Box) ⊆ Qs := by
    intro B hB
    exact hQ₀ (Finset.mem_filter.1 (Finset.mem_coe.1 hB)).1
  rcases dyadicInt_nested_or_disjoint W.1 W.2 W₀.1 W₀.2 with h1 | h1 | h1
  · -- `W ⊆ W₀`: window `W`
    refine ⟨Q₀.filter (fun B => B.scale = W.1 - n), W, hQ, fun R => ?_⟩
    rw [mem_layer, hP R, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hRQ, -⟩, hRW, hs⟩
      exact ⟨⟨hRQ, hs⟩, hRW⟩
    · rintro ⟨⟨hRQ, hs⟩, hRW⟩
      exact ⟨⟨hRQ, hRW.trans h1⟩, hRW, hs⟩
  · -- `W₀ ⊆ W`: window `W₀`
    refine ⟨Q₀.filter (fun B => B.scale = W.1 - n), W₀, hQ, fun R => ?_⟩
    rw [mem_layer, hP R, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hRQ, hRW₀⟩, -, hs⟩
      exact ⟨⟨hRQ, hs⟩, hRW₀⟩
    · rintro ⟨⟨hRQ, hs⟩, hRW₀⟩
      exact ⟨⟨hRQ, hRW₀⟩, hRW₀.trans h1, hs⟩
  · -- disjoint: the layer is empty
    refine ⟨∅, W₀, by simp, fun R => ?_⟩
    rw [mem_layer, hP R]
    simp only [Finset.notMem_empty, false_and, iff_false]
    rintro ⟨⟨-, hRW₀⟩, hRW, -⟩
    obtain ⟨x, hx⟩ := TriTile.I_nonempty R
    exact Set.disjoint_left.1 h1 (hRW hx) (hRW₀ hx)

theorem isResidual_refl (Cs : Finset TriTile) : IsResidual Cs Cs := ⟨[], rfl⟩

theorem removeTrees_removeTrees (Cs : Finset TriTile) (ts₀ ts : List Top) :
    X2.removeTrees (X2.removeTrees Cs ts₀) ts = X2.removeTrees Cs (ts₀ ++ ts) := by
  induction ts₀ generalizing Cs with
  | nil => rfl
  | cons t ts₀ ih => exact ih _

theorem IsResidual.removeTrees {Cs₀ Cs : Finset TriTile} (h : IsResidual Cs₀ Cs) (ts : List Top) :
    IsResidual Cs₀ (X2.removeTrees Cs ts) := by
  obtain ⟨ts₀, rfl⟩ := h
  exact ⟨ts₀ ++ ts, removeTrees_removeTrees _ _ _⟩

/-- B4(d) (MTT2 Lemma 4.4): a tree inside a single scale has one box. -/
theorem IsTree.box_eq_of_scale_eq {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {Tr : Finset TriTile}
    {t : Top} (hT : IsTree Tr t) (hbox : ∀ R ∈ Tr, R.box ∈ Qs) :
    ∀ R ∈ Tr, ∀ R' ∈ Tr, R.box.scale = R'.box.scale → R.box = R'.box := by
  intro R hR R' hR' hs
  by_contra hne
  exact Set.disjoint_left.1 (hQ.2.2.2.2.2.1 R.box (hbox R hR) R'.box (hbox R' hR') hne hs)
    (hT R hR).2 (hT R' hR').2

/-- B3 (decomposition): the tiles inside `Ω` split into the layers of the maximal dyadic intervals of
`Ω` (finite volume), each tile in exactly one `(W, n)`. -/
theorem mem_layer_iff_of_subset {Ω : Set ℝ} (hΩ : volume Ω ≠ ⊤) {Ps : Finset TriTile} {R : TriTile}
    (hR : R ∈ Ps) (hRΩ : R.I ⊆ Ω) :
    ∃! Wn : (ℤ × ℤ) × ℕ, Wn.1 ∈ maxDyadicKeys Ω ∧ R ∈ X2.layer Ps Wn.1 Wn.2 := by
  obtain ⟨n, hn⟩ := exists_dyadicAnc_mem_maxDyadicKeys hΩ (q := (R.box.scale, R.pos)) hRΩ
  refine ⟨(dyadicAnc (R.box.scale, R.pos) n, n), ⟨hn, ?_⟩, ?_⟩
  · rw [mem_layer]
    refine ⟨hR, dyadicInt_subset_dyadicAnc (R.box.scale, R.pos) n, ?_⟩
    rw [dyadicAnc_fst]
    ring
  · rintro ⟨W', n'⟩ ⟨hW', hRW'⟩
    rw [mem_layer] at hRW'
    simp only at hW' hRW'
    obtain ⟨-, hsub, hs⟩ := hRW'
    have hne : ¬ Disjoint (dyadicInt (dyadicAnc (R.box.scale, R.pos) n).1
        (dyadicAnc (R.box.scale, R.pos) n).2) (dyadicInt W'.1 W'.2) := by
      obtain ⟨x, hx⟩ := TriTile.I_nonempty R
      exact Set.not_disjoint_iff.2
        ⟨x, dyadicInt_subset_dyadicAnc (R.box.scale, R.pos) n hx, hsub hx⟩
    have hWW := eq_of_mem_maxDyadicKeys_of_not_disjoint hn hW' hne
    have h1 := dyadicAnc_fst (R.box.scale, R.pos) n
    rw [hWW] at h1
    have hnn : n' = n := by omega
    rw [hnn, ← hWW]

end PrimeBHT.TimeFrequency.X2
