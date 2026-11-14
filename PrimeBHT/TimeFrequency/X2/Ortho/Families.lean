module

public import PrimeBHT.TimeFrequency.X2.Energy

/-!
# X2, node V10: bookkeeping for strongly disjoint families

* `tilesOf 𝒯`: the union of the tile sets of a family of trees;
* `tileSum 𝒯 = ∑_T ∑_{R ∈ T} |I_R|`;
* sub-families `𝒯.restrict 𝒬 = [(T ∩ 𝒬, t)]`: strong disjointness is inherited, tops (hence `topSum`) are
  unchanged;
* the tile sets of a strongly disjoint family are pairwise disjoint, so `∑_T ∑_{R∈T} f R = ∑_{R ∈ tilesOf 𝒯} f R`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- The union of the tile sets of a family of trees. -/
def tilesOf : List (Finset TriTile × Top) → Finset TriTile
  | [] => ∅
  | T :: 𝒯 => T.1 ∪ tilesOf 𝒯

@[simp] theorem tilesOf_nil : tilesOf [] = ∅ := rfl

@[simp] theorem tilesOf_cons (T : Finset TriTile × Top) (𝒯 : List (Finset TriTile × Top)) :
    tilesOf (T :: 𝒯) = T.1 ∪ tilesOf 𝒯 := rfl

theorem mem_tilesOf {𝒯 : List (Finset TriTile × Top)} {R : TriTile} :
    R ∈ tilesOf 𝒯 ↔ ∃ T ∈ 𝒯, R ∈ T.1 := by
  induction 𝒯 with
  | nil => simp
  | cons T 𝒯 ih => simp [ih]

/-- `∑_T ∑_{R ∈ T} |I_R|`, the sum of the tile lengths of a family. -/
def tileSum (𝒯 : List (Finset TriTile × Top)) : ℝ≥0∞ :=
  (𝒯.map (fun T => ∑ R ∈ T.1, ENNReal.ofReal ((2 : ℝ) ^ R.box.scale))).sum

/-- The sub-family obtained by intersecting every tree with the tile set `𝒬` (same tops). -/
def restrictFamily (𝒬 : Finset TriTile) (𝒯 : List (Finset TriTile × Top)) :
    List (Finset TriTile × Top) :=
  𝒯.map (fun T => (T.1 ∩ 𝒬, T.2))

@[simp] theorem restrictFamily_nil (𝒬 : Finset TriTile) : restrictFamily 𝒬 [] = [] := rfl

@[simp] theorem restrictFamily_cons (𝒬 : Finset TriTile) (T : Finset TriTile × Top)
    (𝒯 : List (Finset TriTile × Top)) :
    restrictFamily 𝒬 (T :: 𝒯) = (T.1 ∩ 𝒬, T.2) :: restrictFamily 𝒬 𝒯 := rfl

theorem topSum_restrictFamily (𝒬 : Finset TriTile) (𝒯 : List (Finset TriTile × Top)) :
    topSum (restrictFamily 𝒬 𝒯) = topSum 𝒯 := by
  induction 𝒯 with
  | nil => rfl
  | cons T 𝒯 ih => simp [ih]

theorem tilesOf_restrictFamily (𝒬 : Finset TriTile) (𝒯 : List (Finset TriTile × Top)) :
    tilesOf (restrictFamily 𝒬 𝒯) = tilesOf 𝒯 ∩ 𝒬 := by
  induction 𝒯 with
  | nil => simp
  | cons T 𝒯 ih => simp [ih, Finset.union_inter_distrib_right]

/-- Strong disjointness is inherited by sub-families. -/
theorem IsStronglyDisjoint.restrictFamily {k : Fin 3} {𝒯 : List (Finset TriTile × Top)}
    (h : IsStronglyDisjoint k 𝒯) (𝒬 : Finset TriTile) :
    IsStronglyDisjoint k (restrictFamily 𝒬 𝒯) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro T hT
    obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.1 hT
    obtain ⟨ht, hl⟩ := h1 T₀ hT₀
    refine ⟨fun R hR => ht R (Finset.mem_inter.1 hR).1, fun R hR R' hR' hne => ?_⟩
    exact hl R (Finset.mem_inter.1 hR).1 R' (Finset.mem_inter.1 hR').1 hne
  · refine List.Pairwise.map _ (fun T T' hTT' => ?_) h2
    refine ⟨fun R hR R' hR' => hTT'.1 R (Finset.mem_inter.1 hR).1 R' (Finset.mem_inter.1 hR').1,
      fun R hR R' hR' => hTT'.2 R (Finset.mem_inter.1 hR).1 R' (Finset.mem_inter.1 hR').1⟩

theorem omega_nonempty (B : Box) (k : Fin 3) : (B.ω k).Nonempty := by
  unfold Box.ω
  apply Set.nonempty_Ico.2
  have : (0 : ℝ) < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
  linarith

/-- In a strongly disjoint family of nonempty trees, the tile sets are pairwise disjoint. -/
theorem IsStronglyDisjoint.pairwise_disjoint {k : Fin 3} {𝒯 : List (Finset TriTile × Top)}
    (h : IsStronglyDisjoint k 𝒯) : 𝒯.Pairwise (fun T T' => Disjoint T.1 T'.1) := by
  obtain ⟨h1, h2⟩ := h
  refine List.Pairwise.imp_of_mem (fun {T T'} hT hT' hTT' => ?_) h2
  rw [Finset.disjoint_left]
  intro R hR hR'
  have hI : R.I ⊆ dyadicInt T'.2.1.1 T'.2.1.2 := ((h1 T' hT').1 R hR').1
  obtain ⟨x, hx⟩ := omega_nonempty R.box k
  have hx' : x ∈ dilate 10 (R.box.ω k) := by
    have hlt : R.box.centre k - (2 : ℝ) ^ (-R.box.scale) / 2 <
        R.box.centre k + (2 : ℝ) ^ (-R.box.scale) / 2 := by
      have : (0 : ℝ) < (2 : ℝ) ^ (-R.box.scale) := zpow_pos (by norm_num) _
      linarith
    exact Ico_subset_dilate hlt (by norm_num) hx
  have := hTT'.1 R hR R hR' le_rfl ⟨x, hx', hx'⟩
  obtain ⟨y, hy⟩ := TriTile.I_nonempty R
  exact Set.disjoint_left.1 this hy (hI hy)

/-- Sums over a strongly disjoint family are sums over its tiles. -/
theorem sum_family_eq {M : Type*} [AddCommMonoid M] {𝒯 : List (Finset TriTile × Top)}
    (hdisj : 𝒯.Pairwise (fun T T' => Disjoint T.1 T'.1)) (f : TriTile → M) :
    (𝒯.map (fun T => ∑ R ∈ T.1, f R)).sum = ∑ R ∈ tilesOf 𝒯, f R := by
  induction 𝒯 with
  | nil => simp
  | cons T 𝒯 ih =>
    rw [List.pairwise_cons] at hdisj
    rw [List.map_cons, List.sum_cons, tilesOf_cons, ih hdisj.2, Finset.sum_union]
    rw [Finset.disjoint_left]
    intro R hR hR'
    obtain ⟨T', hT', hRT'⟩ := mem_tilesOf.1 hR'
    exact Finset.disjoint_left.1 (hdisj.1 T' hT') hR hRT'

theorem tileSum_eq {𝒯 : List (Finset TriTile × Top)}
    (hdisj : 𝒯.Pairwise (fun T T' => Disjoint T.1 T'.1)) :
    tileSum 𝒯 = ∑ R ∈ tilesOf 𝒯, ENNReal.ofReal ((2 : ℝ) ^ R.box.scale) :=
  sum_family_eq hdisj _

end PrimeBHT.TimeFrequency.X2
