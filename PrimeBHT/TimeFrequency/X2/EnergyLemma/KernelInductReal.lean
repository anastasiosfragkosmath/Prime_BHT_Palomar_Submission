module

public import PrimeBHT.TimeFrequency.X2.EnergyLemma.KernelInduct

/-!
# X2, node V12: `OSelectable` from the leaf-peeling kernel theorem (Sonnet B)

`KernelInduct.lean` proves that the destruction relation of the abstract tile game has a kernel on every finite family
(`PeelData.exists_isKernel`).  Here the real tile game is an instance:

* candidates `X = (Tr, (W, ξ))`, tiles `R` with window `R.I` and box `R.box`, the top window `dyadicInt W`, the point `ξ`,
  `Bel y ξ :⟺ ξ ∈ y.hull`; `DT S Z X ↔ D (boxes of S) Z X` for `X ⊆ S`;
* tiles of a tree lie below its top (`IsTree`);
* windows are laminar (`dyadicInt_nested_or_disjoint`);
* LEAF PROPERTY: the box of maximal scale `ℓ` of a nonempty set of boxes of a rank-one set `Qs` satisfies: a box of the set
  whose hull contains a point of `ℓ.hull` contains all of `ℓ.hull` (fields (e), (f) of `IsRankOne`).

Consequently `kernel_DT`: every finite family of candidates (tops arbitrary, trees nonempty, inside `S`) has a kernel of `DT S`,
and **`oSelectable_proved : OSelectable`** (no `MinTop`, no `OneTop`, no coupling of window and box is used).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile
open PrimeBHT.TimeFrequency.X2.Absorb

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-- The leaf property of the hull forest: for the box `ℓ` of maximal scale of a set `Bs` of boxes of a rank-one collection,
a box of `Bs` whose hull contains a point of `ℓ.hull` contains all of `ℓ.hull`. -/
theorem hull_leaf {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {Bs : Finset Box} (hBs : ∀ y ∈ Bs, y ∈ Qs)
    (hne : Bs.Nonempty) :
    ∃ ℓ ∈ Bs, ∀ ξ ξ' : ℝ, ξ ∈ ℓ.hull → ξ' ∈ ℓ.hull → ∀ y ∈ Bs, ξ ∈ y.hull → ξ' ∈ y.hull := by
  obtain ⟨ℓ, hℓ, hmax⟩ := Finset.exists_max_image Bs Box.scale hne
  refine ⟨ℓ, hℓ, fun ξ ξ' hξ hξ' y hy hξy => ?_⟩
  have hle : y.scale ≤ ℓ.scale := hmax y hy
  rcases lt_or_eq_of_le hle with hlt | heq
  · obtain ⟨-, -, -, -, -, -, hf, -, -⟩ := hQ
    exact hf ℓ (hBs ℓ hℓ) y (hBs y hy) hlt ⟨ξ, hξ, hξy⟩ hξ'
  · by_cases hyl : y = ℓ
    · rw [hyl]; exact hξ'
    · exfalso
      have he := hQ.2.2.2.2.2.1 y (hBs y hy) ℓ (hBs ℓ hℓ) hyl heq
      exact Set.disjoint_left.1 he hξy hξ

/-- The `PeelData` of the real tile game over a collection `S`. -/
def tilePeel : PeelData (Finset TriTile × Top) TriTile (Set ℝ) Box ℝ :=
  ⟨fun X => X.1, TriTile.I, TriTile.box, fun X => dyadicInt X.2.1.1 X.2.1.2, fun X => X.2.2,
    fun y ξ => ξ ∈ y.hull⟩

theorem DT_iff_D {S : Finset TriTile} {Z X : Finset TriTile × Top} (hXS : X.1 ⊆ S) :
    DT S Z X ↔ tilePeel.D (S.image TriTile.box) Z X := by
  constructor
  · rintro ⟨R, hR⟩
    obtain ⟨hR1, hR2⟩ := Finset.mem_inter.1 hR
    obtain ⟨hRS, h1, h2⟩ := mem_maxTree.1 hR2
    exact ⟨R, hR1, Finset.mem_image_of_mem _ hRS, h1, h2⟩
  · rintro ⟨R, hR, -, h1, h2⟩
    exact ⟨R, Finset.mem_inter.2 ⟨hR, mem_maxTree.2 ⟨hXS hR, h1, h2⟩⟩⟩

/-- **The kernel theorem for the real tile game.**  Every finite family of candidates `(Tr, (W, ξ))` of nonempty trees inside
`S` (`IsTree`) has a kernel of `DT S`; `S` may be any finite collection of tiles whose boxes lie in a rank-one set. -/
theorem kernel_DT {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {S : Finset TriTile} (hS : ∀ R ∈ S, R.box ∈ Qs)
    (C : Finset (Finset TriTile × Top)) (hne : ∀ X ∈ C, X.1.Nonempty) (hsub : ∀ X ∈ C, X.1 ⊆ S)
    (htree : ∀ X ∈ C, IsTree X.1 X.2) : ∃ K, IsKernel (DT S) C K := by
  set Bs₀ : Finset Box := S.image TriTile.box with hBs₀
  have hV : tilePeel.Valid C Bs₀ := by
    refine ⟨fun j hj s hs => htree j hj s hs, ?_, ?_⟩
    · intro i _ j _ s _ h1 h2
      rcases dyadicInt_nested_or_disjoint i.2.1.1 i.2.1.2 j.2.1.1 j.2.1.2 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        obtain ⟨x, hx⟩ := s.I_nonempty
        exact Set.disjoint_left.1 h (h1 hx) (h2 hx)
    · intro Bs' hBs' hne'
      obtain ⟨ℓ, hℓ, hleaf⟩ := hull_leaf hQ (Bs := Bs') (fun y hy => by
        obtain ⟨R, hR, rfl⟩ := Finset.mem_image.1 (hBs' hy)
        exact hS R hR) hne'
      exact ⟨ℓ, hℓ, fun i _ i' _ hi hi' y hy hiy => hleaf _ _ hi hi' y hy hiy⟩
  obtain ⟨K, hK⟩ := tilePeel.exists_isKernel hV (fun j hj => by
    obtain ⟨R, hR⟩ := hne j hj
    exact ⟨R, hR, Finset.mem_image_of_mem _ (hsub j hj hR)⟩)
  obtain ⟨hKC, hKind, hKabs⟩ := hK
  refine ⟨K, hKC, fun Z hZ Z' hZ' hne' h => hKind Z hZ Z' hZ' hne' ?_, fun X hX => ?_⟩
  · exact (DT_iff_D (hsub Z' (hKC hZ'))).1 h
  · obtain ⟨Z, hZ, h⟩ := hKabs X hX
    exact ⟨Z, hZ, (DT_iff_D (hsub X hX)).2 h⟩

/-- **`OSelectable` is TRUE.**  The selection lemma follows from `kernel_DT` via `oSelectable_of_kernel`. -/
theorem oSelectable_proved : OSelectable := by
  refine oSelectable_of_kernel fun J Qs hQ hJ k S hS V hV hcl C hC hone => ?_
  have hne : ∀ X ∈ C, X.1.Nonempty := fun X hX => (hV _ _ (hC X hX).1).1
  have hsub : ∀ X ∈ C, X.1 ⊆ S := fun X hX => (hC X hX).2.1
  have htree : ∀ X ∈ C, IsTree X.1 X.2 := fun X hX => (hV _ _ (hC X hX).1).2.1
  obtain ⟨K, hKC, hKind, hKabs⟩ := kernel_DT hQ hS C hne hsub htree
  exact ⟨K, hKC, hKind, hKabs⟩

end PrimeBHT.TimeFrequency.X2
