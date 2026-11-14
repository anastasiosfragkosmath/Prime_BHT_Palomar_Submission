module

public import PrimeBHT.TimeFrequency.Tile.Trees
public import PrimeBHT.Frozen.IsAdapted
public import PrimeBHT.Frozen.TriIdx

/-!
# The weak Bessel inequality: definitions (blueprint node C4, `TT.bessel`)

* `StronglyDisjoint a b k T T'` (BD26 `k`-strong disjointness of two `i`-trees, unshifted): for `t ∈ T`,
  `t' ∈ T'` with `ω_{t,k} ⊊ ω_{t',k}` we have `I_{t'} ⊄ I_T`.
* `WeakBesselBound a b s' α N φ i k C`: the statement of the weak Bessel inequality (BD26 Lemma
  `l:bessel`, `m = 0`) with constant `C`, as a `Prop`; it is **proved** in `Bessel.lean` as
  `weakBessel`, with an explicit constant `weakBesselConst N` depending on `N` only.

**Correction of the blueprint (C4 statement).** BD26 (and the blueprint) say only "pairwise
`k`-strongly disjoint". Since a tree is *data* `(P_T, I_T, ξ_T)` here, one can take many copies of a
single tree with different `ξ_T ∈ 3ω_{t,i}`; they are `k`-strongly disjoint (the hypothesis is vacuous
for tiles of one tree, by lacunarity), satisfy the two energy hypotheses, and `∑_T |I_T|` is
unbounded. Steps 2 and 4 of the proof use `∑_T ∑_{t ∈ T} = ∑_{t ∈ ∪𝒯}`, i.e. that the tile sets
`P_T` of distinct trees of `𝒯` are **pairwise disjoint**; this is added as a hypothesis (the selection
lemma of C5 supplies it: selected trees are removed from the pool).
-/

@[expose] public section

open MeasureTheory
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Tile

/-- **`k`-strong disjointness** (BD26, unshifted): `t ∈ T`, `t' ∈ T'`, `ω_{t,k} ⊊ ω_{t',k}` imply
`I_{t'} ⊄ I_T`. Not symmetric in `(T, T')`; a family is *pairwise* strongly disjoint if it holds for
all ordered pairs of distinct members. -/
def StronglyDisjoint (a b : ℤ) (k : Fin 3) (T T' : TreeData) : Prop :=
  ∀ t ∈ T.tiles, ∀ t' ∈ T'.tiles, freqInt a b k t ⊂ freqInt a b k t' → ¬ timeInt t' ⊆ T.topInt

/-- **The weak Bessel inequality with constant `C`** (BD26 Lemma `l:bessel`, unshifted; blueprint C4):
for `i ≠ k`, every finite family `𝒯` of `i`-trees in `P ⊆ Idx_ν` (packets `φ t k'` adapted with
exponent `N`) with pairwise disjoint tile sets, pairwise `k`-strongly disjoint, and `f ∈ L²`, `λ > 0` with
the tile bound `|⟨f, φ_{t,k}⟩|² ≤ 4 λ² |I_t|` and the tree bound
`|I_T| λ²/2 ≤ ∑_{t ∈ T} |⟨f, φ_{t,k}⟩|²`, one has `∑_{T ∈ 𝒯} |I_T| ≤ C ‖f‖₂² / λ²`. -/
def WeakBesselBound (a b s' α : ℤ) (N : ℕ) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (i k : Fin 3)
    (C : ℝ) : Prop :=
  i ≠ k → ∀ (P : Finset (ℤ × ℤ × ℤ)), (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α →
    (∀ t ∈ P, ∀ k', IsAdapted N (timeInt t) (freqInt a b k' t) (φ t k')) →
    ∀ (𝒯 : Finset TreeData), (∀ T ∈ 𝒯, IsTree a b i P T) →
      (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → Disjoint T.tiles T'.tiles) →
      (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → StronglyDisjoint a b k T T') →
      ∀ (f : ℝ → ℂ) (lam : ℝ), 0 < lam → MemLp f 2 volume →
        (∀ T ∈ 𝒯, ∀ t ∈ T.tiles, ‖pairing f (φ t k)‖ ^ 2 ≤ 4 * lam ^ 2 * (volume (timeInt t)).toReal) →
        (∀ T ∈ 𝒯, lam ^ 2 / 2 * (volume T.topInt).toReal ≤
          ∑ t ∈ T.tiles, ‖pairing f (φ t k)‖ ^ 2) →
        ∑ T ∈ 𝒯, (volume T.topInt).toReal ≤ C * (∫ x, ‖f x‖ ^ 2) / lam ^ 2

end PrimeBHT.TimeFrequency.Tile
