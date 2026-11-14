module

public import PrimeBHT.TimeFrequency.X2.EnergyLemma.Semikernel

/-!
# X2, node V12: the kernel theorem by LEAF PEELING (Sonnet B)

The destruction relation of the tile game has a kernel on every finite family (this closes `QuadrantKernel`).  The proof is
a structural induction on the (finite) set of boxes: remove the finest box `ℓ`.

Abstract data (`PeelData`): candidates `j : ι` with a top window `a j`, a top point `pt j`, a finite set of tiles `T j`
(each tile has a window `win s` and a box `box s`); `Bel y ξ` says that the box `y` lies below the point `ξ`.  For a finite
set of boxes `Bs`,
`D Bs i j :⟺ ∃ s ∈ T j, box s ∈ Bs ∧ win s ≤ a i ∧ Bel (box s) (pt i)`.
Structural hypotheses (`Valid`): tiles lie below their tops; windows are laminar; every nonempty `Bs' ⊆ Bs₀` has a LEAF
`ℓ` (the chain of boxes of `Bs'` through every point of `ℓ` is the same).

* `PeelData.exists_isKernel`: if every candidate has a tile with box in `Bs₀`, `D Bs₀` has a kernel on `C₀`.
  Induction on `|Bs|`: `Bs' = Bs ∖ {ℓ}`; `D` and `D'` differ only on the candidates through `ℓ` (`L`), whose out-arcs are
  window-monotone; a kernel `K^d` of `D'` gives the kernel `(K^d ∩ N) ∪ (maximal-window representatives of the
  candidates of `L` not in conflict with `K^d ∩ N`)` of `D`.
* `quadrantKernel`: `QuadrantKernel W B` for every pair of forests (Semikernel.lean).
-/

@[expose] public noncomputable section

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2.Absorb

section Abstract

variable {ι : Type*}

/-- A weak kernel: independent, and every candidate outside `K` is destroyed by a member of `K` (candidates of `K` need not
destroy themselves). -/
def IsKernel0 (D : ι → ι → Prop) (C K : Finset ι) : Prop :=
  K ⊆ C ∧ (∀ Z ∈ K, ∀ Z' ∈ K, Z ≠ Z' → ¬ D Z Z') ∧ ∀ X ∈ C, X ∉ K → ∃ Z ∈ K, D Z X

/-- Removal of the bare candidates (those that nobody destroys): the weak kernels exist on all subfamilies of `C₀` as soon
as kernels exist on the subfamilies without bare candidates. -/
theorem exists_isKernel0_of_nonbare {D : ι → ι → Prop} {bare : ι → Prop} (C₀ : Finset ι)
    (hbare : ∀ j, bare j → ∀ i, ¬ D i j)
    (h : ∀ C ⊆ C₀, (∀ j ∈ C, ¬ bare j) → ∃ K, IsKernel D C K) :
    ∀ C ⊆ C₀, ∃ K, IsKernel0 D C K := by
  intro C hC
  set Z0 : Finset ι := C.filter bare with hZ0
  set C1 : Finset ι := C.filter (fun j => ¬ bare j ∧ ∀ z ∈ Z0, ¬ D z j) with hC1
  obtain ⟨K1, hK1C, hK1ind, hK1abs⟩ :=
    h C1 ((Finset.filter_subset _ _).trans hC) (fun j hj => (Finset.mem_filter.1 hj).2.1)
  have hK1mem : ∀ k ∈ K1, k ∈ C ∧ ¬ bare k ∧ ∀ z ∈ Z0, ¬ D z k := fun k hk => by
    have := Finset.mem_filter.1 (hK1C hk)
    exact ⟨this.1, this.2.1, this.2.2⟩
  have hZ0mem : ∀ z ∈ Z0, z ∈ C ∧ bare z := fun z hz => Finset.mem_filter.1 hz
  refine ⟨Z0 ∪ K1, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact (hZ0mem x h).1
    · exact (hK1mem x h).1
  · intro Z hZ Z' hZ' hne
    rcases Finset.mem_union.1 hZ with hz | hz <;> rcases Finset.mem_union.1 hZ' with hz' | hz'
    · exact hbare Z' (hZ0mem Z' hz').2 Z
    · exact (hK1mem Z' hz').2.2 Z hz
    · exact hbare Z' (hZ0mem Z' hz').2 Z
    · exact hK1ind Z hz Z' hz' hne
  · intro X hX hXK
    have hXb : ¬ bare X := fun hb => hXK (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hX, hb⟩))
    by_cases hd : ∃ z ∈ Z0, D z X
    · obtain ⟨z, hz, hzX⟩ := hd
      exact ⟨z, Finset.mem_union_left _ hz, hzX⟩
    · push Not at hd
      have hX1 : X ∈ C1 := Finset.mem_filter.2 ⟨hX, hXb, hd⟩
      obtain ⟨Z, hZ, hZX⟩ := hK1abs X hX1
      exact ⟨Z, Finset.mem_union_right _ hZ, hZX⟩

variable {W : Type*} [Preorder W]

/-- Representatives of the maximal values of a function into a preorder: a subfamily whose values are pairwise
incomparable (as soon as the members are distinct) and which dominates every member. -/
theorem exists_window_reps (a : ι → W) (J : Finset ι) :
    ∃ R ⊆ J, (∀ j ∈ R, ∀ j' ∈ R, j ≠ j' → ¬ a j ≤ a j') ∧ ∀ j ∈ J, ∃ k ∈ R, a j ≤ a k := by
  induction J using Finset.strongInduction with
  | H J ih =>
    rcases J.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
    obtain ⟨j0, hj0, hmax⟩ := Finset.exists_maximalFor a J hne
    set J' : Finset ι := J.filter (fun j => ¬ a j ≤ a j0) with hJ'
    have hlt : J' ⊂ J :=
      Finset.filter_ssubset.2 ⟨j0, hj0, fun h => h le_rfl⟩
    obtain ⟨R', hR'J', hR'ind, hR'abs⟩ := ih J' hlt
    have hR'mem : ∀ j ∈ R', j ∈ J ∧ ¬ a j ≤ a j0 := fun j hj => Finset.mem_filter.1 (hR'J' hj)
    refine ⟨insert j0 R', ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hj0
      · exact (hR'mem x hx).1
    · intro j hj j' hj' hne
      rcases Finset.mem_insert.1 hj with rfl | hj1 <;> rcases Finset.mem_insert.1 hj' with rfl | hj1'
      · exact absurd rfl hne
      · intro hle
        exact (hR'mem j' hj1').2 (hmax (hR'mem j' hj1').1 hle)
      · intro hle
        exact (hR'mem j hj1).2 hle
      · exact hR'ind j hj1 j' hj1' hne
    · intro j hj
      by_cases hle : a j ≤ a j0
      · exact ⟨j0, Finset.mem_insert_self _ _, hle⟩
      · obtain ⟨k, hk, hjk⟩ := hR'abs j (Finset.mem_filter.2 ⟨hj, hle⟩)
        exact ⟨k, Finset.mem_insert_of_mem hk, hjk⟩

end Abstract

section Peel

/-- The data of the leaf-peeling model: candidates `ι`, tiles `Ω` with a window (in the preorder `W`) and a box (in `Bx`),
tops given by a window `a j` and a point `pt j`; `Bel y ξ`: the box `y` lies below the point `ξ`. -/
structure PeelData (ι Ω W Bx Pt : Type*) [Preorder W] where
  T : ι → Finset Ω
  win : Ω → W
  box : Ω → Bx
  a : ι → W
  pt : ι → Pt
  Bel : Bx → Pt → Prop

namespace PeelData

variable {ι Ω W Bx Pt : Type*} [Preorder W] (P : PeelData ι Ω W Bx Pt)

/-- `D Bs i j`: choosing `i` destroys `j`, only the tiles with a box in `Bs` being visible. -/
def D (Bs : Finset Bx) (i j : ι) : Prop :=
  ∃ s ∈ P.T j, P.box s ∈ Bs ∧ P.win s ≤ P.a i ∧ P.Bel (P.box s) (P.pt i)

/-- The structural hypotheses on a family `C₀` and a box set `Bs₀`: tiles lie below their tops, windows are laminar, and
every nonempty sub-box-set has a LEAF. -/
structure Valid (C₀ : Finset ι) (Bs₀ : Finset Bx) : Prop where
  tile : ∀ j ∈ C₀, ∀ s ∈ P.T j, P.win s ≤ P.a j ∧ P.Bel (P.box s) (P.pt j)
  lam : ∀ i ∈ C₀, ∀ j ∈ C₀, ∀ s ∈ P.T j, P.win s ≤ P.a i → P.win s ≤ P.a j →
    P.a i ≤ P.a j ∨ P.a j ≤ P.a i
  leaf : ∀ Bs' ⊆ Bs₀, Bs'.Nonempty → ∃ ℓ ∈ Bs', ∀ i ∈ C₀, ∀ i' ∈ C₀, P.Bel ℓ (P.pt i) →
    P.Bel ℓ (P.pt i') → ∀ y ∈ Bs', P.Bel y (P.pt i) → P.Bel y (P.pt i')

variable {P}

/-- A candidate with a visible tile destroys itself. -/
theorem D_self {C₀ : Finset ι} {Bs₀ : Finset Bx} (hV : P.Valid C₀ Bs₀) {Bs : Finset Bx} {j : ι} (hj : j ∈ C₀)
    (hnb : ∃ s ∈ P.T j, P.box s ∈ Bs) : P.D Bs j j := by
  obtain ⟨s, hs, hb⟩ := hnb
  exact ⟨s, hs, hb, (hV.tile j hj s hs).1, (hV.tile j hj s hs).2⟩

/-- **The lifting step.**  Let `ℓ` be a leaf of `Bs` and `K^d` a weak kernel of `D (Bs ∖ {ℓ})`: then the `N`-part of `K^d`
together with representatives of the maximal windows of the candidates through `ℓ` not in conflict with it is a kernel of
`D Bs`. -/
theorem step {C₀ : Finset ι} {Bs₀ : Finset Bx} (hV : P.Valid C₀ Bs₀) {Bs : Finset Bx} {ℓ : Bx}
    (hleaf : ∀ i ∈ C₀, ∀ i' ∈ C₀, P.Bel ℓ (P.pt i) → P.Bel ℓ (P.pt i') → ∀ y ∈ Bs, P.Bel y (P.pt i) →
      P.Bel y (P.pt i'))
    {C : Finset ι} (hC : C ⊆ C₀) (hnb : ∀ j ∈ C, ∃ s ∈ P.T j, P.box s ∈ Bs)
    (IH : ∃ K, IsKernel0 (P.D (Bs.erase ℓ)) C K) : ∃ K, IsKernel (P.D Bs) C K := by
  obtain ⟨Kd, hKdC, hKdind, hKdabs⟩ := IH
  -- (F1) `D' ⊆ D`
  have F1 : ∀ i j, P.D (Bs.erase ℓ) i j → P.D Bs i j := by
    rintro i j ⟨s, hs, hb, h1, h2⟩
    exact ⟨s, hs, Finset.mem_of_mem_erase hb, h1, h2⟩
  -- (F2) for `i` not through `ℓ`
  have F2 : ∀ i, ¬ P.Bel ℓ (P.pt i) → ∀ j, P.D Bs i j → P.D (Bs.erase ℓ) i j := by
    rintro i hi j ⟨s, hs, hb, h1, h2⟩
    refine ⟨s, hs, Finset.mem_erase.2 ⟨?_, hb⟩, h1, h2⟩
    intro he
    rw [he] at h2
    exact hi h2
  -- (F3) for `j` not through `ℓ`
  have F3 : ∀ j ∈ C, ¬ P.Bel ℓ (P.pt j) → ∀ i, P.D Bs i j → P.D (Bs.erase ℓ) i j := by
    rintro j hj hjl i ⟨s, hs, hb, h1, h2⟩
    refine ⟨s, hs, Finset.mem_erase.2 ⟨?_, hb⟩, h1, h2⟩
    intro he
    have := (hV.tile j (hC hj) s hs).2
    rw [he] at this
    exact hjl this
  -- (F4) the out-arcs of the candidates through `ℓ` are window-monotone
  have F4 : ∀ i ∈ C, ∀ i' ∈ C, P.Bel ℓ (P.pt i) → P.Bel ℓ (P.pt i') → P.a i ≤ P.a i' →
      ∀ j, P.D Bs i j → P.D Bs i' j := by
    rintro i hi i' hi' hli hli' hle j ⟨s, hs, hb, h1, h2⟩
    exact ⟨s, hs, hb, h1.trans hle, hleaf i (hC hi) i' (hC hi') hli hli' _ hb h2⟩
  -- (F5) incomparable windows do not destroy
  have F5 : ∀ i ∈ C, ∀ j ∈ C, ¬ P.a i ≤ P.a j → ¬ P.a j ≤ P.a i → ¬ P.D Bs i j := by
    rintro i hi j hj h1 h2 ⟨s, hs, -, hw, -⟩
    rcases hV.lam i (hC hi) j (hC hj) s hs hw (hV.tile j (hC hj) s hs).1 with h | h
    · exact h1 h
    · exact h2 h
  set NK : Finset ι := Kd.filter (fun j => ¬ P.Bel ℓ (P.pt j)) with hNK
  set L : Finset ι := C.filter (fun j => P.Bel ℓ (P.pt j)) with hL
  set Lok : Finset ι := L.filter (fun j => ∀ k ∈ NK, ¬ P.D Bs k j ∧ ¬ P.D Bs j k) with hLok
  have hNKmem : ∀ k ∈ NK, k ∈ Kd ∧ ¬ P.Bel ℓ (P.pt k) := fun k hk => Finset.mem_filter.1 hk
  have hLokmem : ∀ j ∈ Lok, j ∈ C ∧ P.Bel ℓ (P.pt j) ∧ ∀ k ∈ NK, ¬ P.D Bs k j ∧ ¬ P.D Bs j k := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
    obtain ⟨hj3, hj4⟩ := Finset.mem_filter.1 hj1
    exact ⟨hj3, hj4, hj2⟩
  -- the through-`ℓ` part of `K^d` is conflict free with `NK`
  have hclaim : ∀ u ∈ Kd, P.Bel ℓ (P.pt u) → u ∈ Lok := by
    intro u hu hul
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hKdC hu, hul⟩, fun k hk => ?_⟩
    obtain ⟨hkK, hkl⟩ := hNKmem k hk
    have hne : k ≠ u := fun he => hkl (he ▸ hul)
    refine ⟨fun h => hKdind k hkK u hu hne (F2 k hkl u h), fun h => hKdind u hu k hkK hne.symm ?_⟩
    exact F3 k (hKdC hkK) hkl u h
  obtain ⟨R, hRL, hRind, hRabs⟩ := exists_window_reps P.a Lok
  refine ⟨NK ∪ R, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact hKdC (hNKmem x h).1
    · exact (hLokmem x (hRL h)).1
  · intro Z hZ Z' hZ' hne
    rcases Finset.mem_union.1 hZ with hz | hz <;> rcases Finset.mem_union.1 hZ' with hz' | hz'
    · obtain ⟨hzK, hzl⟩ := hNKmem Z hz
      intro h
      exact hKdind Z hzK Z' (hNKmem Z' hz').1 hne (F2 Z hzl Z' h)
    · exact ((hLokmem Z' (hRL hz')).2.2 Z hz).1
    · exact ((hLokmem Z (hRL hz)).2.2 Z' hz').2
    · exact F5 Z (hLokmem Z (hRL hz)).1 Z' (hLokmem Z' (hRL hz')).1 (hRind Z hz Z' hz' hne)
        (hRind Z' hz' Z hz hne.symm)
  · intro X hX
    -- some member of `K^d` destroys `X`
    have hu : ∃ u ∈ Kd, P.D Bs u X := by
      by_cases hXK : X ∈ Kd
      · exact ⟨X, hXK, D_self hV (hC hX) (hnb X hX)⟩
      · obtain ⟨u, hu, h⟩ := hKdabs X hX hXK
        exact ⟨u, hu, F1 u X h⟩
    obtain ⟨u, huK, hux⟩ := hu
    by_cases hul : P.Bel ℓ (P.pt u)
    · have huLok := hclaim u huK hul
      obtain ⟨k, hkR, hk⟩ := hRabs u huLok
      exact ⟨k, Finset.mem_union_right _ hkR,
        F4 u (hLokmem u huLok).1 k (hLokmem k (hRL hkR)).1 hul (hLokmem k (hRL hkR)).2.1 hk X hux⟩
    · exact ⟨u, Finset.mem_union_left _ (Finset.mem_filter.2 ⟨huK, hul⟩), hux⟩

/-- **The kernel theorem (leaf peeling).**  On a valid family, if every candidate has a tile with box in `Bs₀`, then `D Bs₀`
has a kernel. -/
theorem exists_isKernel_aux {C₀ : Finset ι} {Bs₀ : Finset Bx} (hV : P.Valid C₀ Bs₀) :
    ∀ Bs ⊆ Bs₀, ∀ C ⊆ C₀, (∀ j ∈ C, ∃ s ∈ P.T j, P.box s ∈ Bs) → ∃ K, IsKernel (P.D Bs) C K := by
  intro Bs
  induction Bs using Finset.strongInduction with
  | H Bs ih =>
    intro hBs C hC hnb
    rcases Bs.eq_empty_or_nonempty with rfl | hne
    · have hCe : C = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro j hj
        obtain ⟨s, -, hs⟩ := hnb j hj
        simp at hs
      subst hCe
      exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
    · obtain ⟨ℓ, hℓ, hleaf⟩ := hV.leaf Bs hBs hne
      have hlt : Bs.erase ℓ ⊂ Bs := Finset.erase_ssubset hℓ
      have IH : ∀ C ⊆ C₀, ∃ K, IsKernel0 (P.D (Bs.erase ℓ)) C K := by
        refine exists_isKernel0_of_nonbare C₀ (bare := fun j => ∀ s ∈ P.T j, P.box s ∉ Bs.erase ℓ) ?_ ?_
        · rintro j hj i ⟨s, hs, hb, -⟩
          exact hj s hs hb
        · intro C' hC' hnb'
          refine ih _ hlt (hlt.subset.trans hBs) C' hC' fun j hj => ?_
          have := hnb' j hj
          push Not at this
          exact this
      exact step hV (hleaf) hC hnb (IH C hC)

/-- The kernel theorem for the whole box set. -/
theorem exists_isKernel {C₀ : Finset ι} {Bs₀ : Finset Bx} (hV : P.Valid C₀ Bs₀)
    (hnb : ∀ j ∈ C₀, ∃ s ∈ P.T j, P.box s ∈ Bs₀) : ∃ K, IsKernel (P.D Bs₀) C₀ K :=
  exists_isKernel_aux hV Bs₀ (Finset.Subset.refl _) C₀ (Finset.Subset.refl _) hnb

end PeelData

end Peel

/-! ## The quadrant game: `QuadrantKernel` for every pair of forests -/

section Quadrant

variable (W B : Type*) [PartialOrder W] [PartialOrder B] [IsForest W] [IsForest B]

/-- **The quadrant kernel theorem**: every finite family of quadrant candidates (a tree of windows, a forest of boxes) has a
kernel. -/
theorem quadrantKernel : QuadrantKernel W B := by
  intro C
  let P : PeelData (QCand W B) (W × B) W B B :=
    ⟨fun X => X.T, Prod.fst, Prod.snd, fun X => X.top.1, fun X => X.top.2, fun y b => b ≤ y⟩
  set Bs₀ : Finset B := C.biUnion (fun X => X.T.image Prod.snd) with hBs₀
  have hmem : ∀ X ∈ C, ∀ p ∈ X.T, p.2 ∈ Bs₀ := fun X hX p hp =>
    Finset.mem_biUnion.2 ⟨X, hX, Finset.mem_image_of_mem _ hp⟩
  have hV : P.Valid C Bs₀ := by
    refine ⟨fun j hj s hs => j.upper s hs, fun i _ j _ s _ h1 h2 => IsForest.chain s.1 _ _ h1 h2, ?_⟩
    intro Bs' _ hne
    obtain ⟨ℓ, hℓ, hmin⟩ := Finset.exists_minimal hne
    refine ⟨ℓ, hℓ, fun i _ i' _ hi hi' y hy hiy => ?_⟩
    have hi : i.top.2 ≤ ℓ := hi
    have hi' : i'.top.2 ≤ ℓ := hi'
    have hiy : i.top.2 ≤ y := hiy
    show i'.top.2 ≤ y
    rcases IsForest.chain i.top.2 y ℓ hiy hi with h | h
    · exact hi'.trans (hmin hy h)
    · exact hi'.trans h
  obtain ⟨K, hKC, hKind, hKabs⟩ := P.exists_isKernel hV (fun j hj => by
    obtain ⟨p, hp⟩ := j.nonempty
    exact ⟨p, hp, hmem j hj p hp⟩)
  have hDq : ∀ Z, ∀ X ∈ C, P.D Bs₀ Z X ↔ Dq Z X := by
    intro Z X hX
    constructor
    · rintro ⟨s, hs, -, h1, h2⟩
      exact ⟨s, hs, h1, h2⟩
    · rintro ⟨s, hs, h1, h2⟩
      exact ⟨s, hs, hmem X hX s hs, h1, h2⟩
  refine ⟨K, hKC, fun Z hZ Z' hZ' hne h => hKind Z hZ Z' hZ' hne ?_, fun X hX => ?_⟩
  · exact (hDq Z Z' (hKC hZ')).2 h
  · obtain ⟨Z, hZ, h⟩ := hKabs X hX
    exact ⟨Z, hZ, (hDq Z X hX).1 h⟩

end Quadrant

end PrimeBHT.TimeFrequency.X2.Absorb
