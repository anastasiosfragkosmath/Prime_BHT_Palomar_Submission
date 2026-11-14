module

public import PrimeBHT.TimeFrequency.Tile.Lacunary
public import PrimeBHT.Frozen.IsAdapted
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The tree selection lemma (blueprint node C5, `TT.select`)

## Main result (read this first)

For a slot `k`, a finite `P' ⊆ Idx_ν`, `f ∈ L²` and `lam > 0` with `size_{i,k}(f, P') ≤ 2 lam` for
`i = 0, 1, 2`, there are finite families of trees `trees i` (`i = 0, 1, 2`, each member an `i`-tree
contained in `P'`) such that, with `rest := P' ∖ ⋃_i ⋃_{T ∈ trees i} P_T`:

* (a) `size_{i,k}(f, rest) ≤ lam` for `i = 0, 1, 2`;
* (b) `∑_i ∑_{T ∈ trees i} |I_T| ≤ 8 C ‖f‖₂² / lam²`,

where `C` is the constant of the weak Bessel inequality (C4). In Lean:

```
theorem exists_selection_of_hC4 {a b s' α : ℤ} (hν : TriValid a b s' α) {N : ℕ} {C : ℝ}
    (hC4 : WeakBesselHyp a b s' α N C) {P' : Finset (ℤ × ℤ × ℤ)}
    (hP' : (↑P' : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α) {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hφ : ∀ t ∈ P', ∀ j, IsAdapted N (timeInt t) (freqInt a b j t) (φ t j)) (k : Fin 3)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) {lam : ℝ} (hlam : 0 < lam)
    (hsize : ∀ i, size a b φ i k f P' ≤ ENNReal.ofReal (2 * lam)) :
    ∃ out : SelectionOutput,
      IsSelection a b φ k f lam (8 * C * (∫ x, ‖f x‖ ^ 2) / lam ^ 2) P' out
```

`WeakBesselHyp a b s' α N C` is the local copy of the weak Bessel inequality C4 (hypothesis `hC4`; it is
the statement of `WeakBesselBound` of `Bessel/Defs.lean` for all `φ, i, k`, with `TriValid` assumed
first). `SelectionOutput` has the fields `trees : Fin 3 → Finset TreeData` and `rest : Finset (ℤ × ℤ × ℤ)`;
`IsSelection` records: every `T ∈ trees i` is an `i`-tree in `P'`; the tile sets of the trees of each
collection are pairwise disjoint (indeed all selected tile sets are disjoint from each other);
`rest = P' ∖ ⋃ tiles`; (a); (b).

## Method

1. `exists_greedy_selection`: an abstract selection lemma over an arbitrary tree system with a real
   order key `κ` (strong induction on the finite set of available tiles). It selects, round after round, a
   large candidate with minimal key, removes its tiles together with the auxiliary tiles `S`
   (`cond T t`), and stops when no large candidate is left.
2. The instantiation: tiles `ℤ × ℤ × ℤ`, trees `TreeData`, candidates = canonical `i'`-trees all of whose
   tiles lie on the side `σ` (`>` or `<`) of `ω_{t,k}` (`tileSide`), key `κ = ± ξ'_T`,
   `ξ'_T = lacRatio i' k · ξ_T`, `cond T t := ξ'_T ∈ 3ω_{t,k} ∧ I_t ⊆ I_T` (this defines the `k`-tree `S`).
   Four stages `(i', σ)`, `i' ≠ k`, `σ ∈ {>, <}`.

## Corrections to the blueprint (checked by hand)

* `ξ'_T := ε_k ξ_T` must be `lacRatio i' k · ξ_T` (see `Lacunary.lean`).
* The side of a tile (`ξ'_T > c(ω_{t,k})` or `<`) does not depend on which `ξ ∈ 3ω_{t,i'}` is used
  (`side_of_mem`, `le_ratio_mul_of_tileSide_true`, `ratio_mul_lt_of_tileSide_false`): the set `r · 3ω_{t,i'}` is an interval inside
  `50ω ∖ 2ω`, which has two components. Hence `T = T_> ∪ T_<` is a partition by tiles, and the
  `>`-trees are exactly the `i'`-trees inside the set of `>`-tiles.
* Step 4 (strong disjointness) is correct in both directions (`>`: `ξ'_{T'} ≥ c' + |ω'| > ξ'_T`;
  `<`: `ξ'_{T'} < c' - |ω'| ≤ ξ'_T`; with the key `± ξ'` the selected tree is the one with the smaller
  key; `T'` is selected after `T`).
* C4 needs the tile sets of the trees of `𝒯` to be pairwise disjoint (a hypothesis of `WeakBesselHyp`);
  the selection supplies it (`exists_stage_selection`, `IsSelection`: all selected tile sets, including the
  `k`-trees `S`, are pairwise disjoint).
* "Maximal for inclusion" is not needed anywhere (selection by the key alone suffices): the removal
  of the tiles `S` handles disjointness, `C4` needs only the criterion, and the stopping criterion is
  about the remainder. The top `I_T` of a selected tree is any admissible top (we pick one).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Tile

/-! ### Part 1: the abstract selection lemma -/

section Abstract

variable {α β : Type*} [DecidableEq α]

/-- **Abstract greedy selection.** Let `tiles : β → Finset α`, `IsT Q T` ("`T` is a tree in `Q`"),
`Large T`, a real key `κ` and a predicate `cond T t` (the tile `t` is swallowed by `T`) be such that
`IsT` is monotone in `Q`, trees live in their ambient set, large trees are nonempty, and the keys of the
large trees of any `Q` form a finite set. Then for every finite `Q` there are a finite family `𝒯` of
large trees in `Q`, sets `S T` of swallowed tiles, and a remainder `R = Q ∖ ⋃_{T ∈ 𝒯} (tiles T ∪ S T)`,
such that no large tree is left in `R`; the sets `tiles T ∪ S T` (`T ∈ 𝒯`) are pairwise disjoint and
`tiles T` is disjoint from `S T`; and for `T, T' ∈ 𝒯` with `κ T < κ T'` no tile of `T'` is a tile of `T`
or swallowed by `T`. -/
theorem exists_greedy_selection
    (tiles : β → Finset α) (IsT : Finset α → β → Prop) (Large : β → Prop) (κ : β → ℝ)
    (cond : β → α → Prop)
    (hmono : ∀ {Q Q' : Finset α} {T : β}, IsT Q T → Q ⊆ Q' → IsT Q' T)
    (hsub : ∀ {Q : Finset α} {T : β}, IsT Q T → tiles T ⊆ Q)
    (hne : ∀ {T : β}, Large T → (tiles T).Nonempty)
    (hfin : ∀ Q : Finset α, (κ '' {T | IsT Q T ∧ Large T}).Finite) (Q : Finset α) :
    ∃ (𝒯 : Finset β) (S : β → Finset α) (R : Finset α),
      (∀ T ∈ 𝒯, IsT Q T ∧ Large T) ∧
      (∀ T, IsT R T → ¬ Large T) ∧
      R ⊆ Q ∧
      R = Q \ 𝒯.biUnion (fun T => tiles T ∪ S T) ∧
      (∀ T ∈ 𝒯, S T ⊆ Q ∧ ∀ t ∈ S T, cond T t) ∧
      (∀ T ∈ 𝒯, Disjoint (tiles T) (S T)) ∧
      (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → Disjoint (tiles T ∪ S T) (tiles T' ∪ S T')) ∧
      (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, κ T < κ T' → ∀ t' ∈ tiles T', t' ∉ tiles T ∧ ¬ cond T t') := by
  classical
  induction Q using Finset.strongInduction with
  | H Q ih =>
    by_cases hex : ∃ T, IsT Q T ∧ Large T
    · obtain ⟨T₀, hT₀⟩ := hex
      have hfinQ := hfin Q
      obtain ⟨y, ⟨T, hT, rfl⟩, hy⟩ := Set.exists_min_image (κ '' {T | IsT Q T ∧ Large T}) id hfinQ
        ⟨κ T₀, ⟨T₀, hT₀, rfl⟩⟩
      have hmin : ∀ T', IsT Q T' → Large T' → κ T ≤ κ T' := fun T' h1 h2 =>
        hy (κ T') ⟨T', ⟨h1, h2⟩, rfl⟩
      obtain ⟨hTQ, hTL⟩ := hT
      set S : Finset α := Q.filter (fun t => t ∉ tiles T ∧ cond T t) with hS
      set Q₁ : Finset α := Q \ (tiles T ∪ S) with hQ₁
      have hTne := hne hTL
      have hQ₁lt : Q₁ ⊂ Q := by
        apply Finset.sdiff_ssubset
        · exact Finset.union_subset (hsub hTQ) (Finset.filter_subset _ _)
        · exact hTne.mono Finset.subset_union_left
      obtain ⟨𝒯₁, S₁, R, h1, h2, h3, h4, h5, h6a, h6, h7⟩ := ih Q₁ hQ₁lt
      have hQ₁sub : Q₁ ⊆ Q := hQ₁lt.subset
      have hTnot : T ∉ 𝒯₁ := by
        intro hmem
        obtain ⟨t, ht⟩ := hTne
        have := hsub (h1 T hmem).1 ht
        rw [hQ₁, Finset.mem_sdiff] at this
        exact this.2 (Finset.mem_union_left _ ht)
      -- the swallowed sets
      set Sf : β → Finset α := fun T'' => if T'' = T then S else S₁ T'' with hSf
      have hSfT : Sf T = S := by simp only [hSf, ↓reduceIte]
      have hSf1 : ∀ T'' ∈ 𝒯₁, Sf T'' = S₁ T'' := by
        intro T'' hT''
        have hne' : ¬ T'' = T := fun h => hTnot (h ▸ hT'')
        simp only [hSf, hne', ↓reduceIte]
      -- tiles of later trees lie in `Q₁`
      have hQ₁mem : ∀ T'' ∈ 𝒯₁, ∀ t ∈ tiles T'' ∪ S₁ T'', t ∈ Q₁ := by
        intro T'' hT'' t ht
        rcases Finset.mem_union.1 ht with ht | ht
        · exact hsub (h1 T'' hT'').1 ht
        · exact (h5 T'' hT'').1 ht
      have hQ₁disj : ∀ t ∈ Q₁, t ∉ tiles T ∪ S := fun t ht => (Finset.mem_sdiff.1 ht).2
      refine ⟨insert T 𝒯₁, Sf, R, ?_, h2, h3.trans hQ₁sub, ?_, ?_, ?_, ?_, ?_⟩
      · intro T'' hT''
        rcases Finset.mem_insert.1 hT'' with h | h
        · subst h
          exact ⟨hTQ, hTL⟩
        · exact ⟨hmono (h1 T'' h).1 hQ₁sub, (h1 T'' h).2⟩
      · have hbi : (insert T 𝒯₁).biUnion (fun T'' => tiles T'' ∪ Sf T'') =
            (tiles T ∪ S) ∪ 𝒯₁.biUnion (fun T'' => tiles T'' ∪ S₁ T'') := by
          rw [Finset.biUnion_insert, hSfT]
          congr 1
          apply Finset.biUnion_congr rfl
          intro T'' hT''
          rw [hSf1 T'' hT'']
        rw [hbi, h4, hQ₁, sdiff_sdiff_left]
        rfl
      · intro T'' hT''
        rcases Finset.mem_insert.1 hT'' with h | h
        · subst h
          rw [hSfT]
          exact ⟨Finset.filter_subset _ _, fun t ht => (Finset.mem_filter.1 ht).2.2⟩
        · rw [hSf1 T'' h]
          exact ⟨(h5 T'' h).1.trans hQ₁sub, (h5 T'' h).2⟩
      · intro T'' hT''
        rcases Finset.mem_insert.1 hT'' with h | h
        · subst h
          rw [hSfT]
          exact Finset.disjoint_left.2 fun t ht ht' => (Finset.mem_filter.1 ht').2.1 ht
        · rw [hSf1 T'' h]
          exact h6a T'' h
      · intro T₁ hT₁ T₂ hT₂ hne12
        rcases Finset.mem_insert.1 hT₁ with e₁ | m₁ <;> rcases Finset.mem_insert.1 hT₂ with e₂ | m₂
        · exact absurd (e₁.trans e₂.symm) hne12
        · rw [e₁, hSfT, hSf1 T₂ m₂]
          exact Finset.disjoint_left.2 fun t ht ht' => hQ₁disj t (hQ₁mem T₂ m₂ t ht') ht
        · rw [e₂, hSfT, hSf1 T₁ m₁]
          exact Finset.disjoint_left.2 fun t ht ht' => hQ₁disj t (hQ₁mem T₁ m₁ t ht) ht'
        · rw [hSf1 T₁ m₁, hSf1 T₂ m₂]
          exact h6 T₁ m₁ T₂ m₂ hne12
      · intro T₁ hT₁ T₂ hT₂ hlt t' ht'
        rcases Finset.mem_insert.1 hT₁ with e₁ | m₁ <;> rcases Finset.mem_insert.1 hT₂ with e₂ | m₂
        · exact absurd (e₁.trans e₂.symm ▸ hlt) (lt_irrefl _)
        · have h8 := hsub (h1 T₂ m₂).1 ht'
          rw [hQ₁, Finset.mem_sdiff] at h8
          rw [e₁]
          refine ⟨fun h => h8.2 (Finset.mem_union_left _ h), fun hc => h8.2 ?_⟩
          refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨h8.1, ?_, hc⟩)
          exact fun h => h8.2 (Finset.mem_union_left _ h)
        · rw [e₂] at hlt
          exact absurd hlt (not_lt.2 (hmin T₁ (hmono (h1 T₁ m₁).1 hQ₁sub) (h1 T₁ m₁).2))
        · exact h7 T₁ m₁ T₂ m₂ hlt t' ht'
    · refine ⟨∅, fun _ => ∅, Q, by simp, fun T hT hL => hex ⟨T, hT, hL⟩, subset_rfl, by simp,
        by simp, by simp, by simp, by simp⟩

end Abstract

/-! ### Part 2: the side of a tile and the geometry of `ξ'` -/

/-- `2ω_{t,k} = [c - |ω|, c + |ω|)` with `c = c(ω_{t,k})` and `|ω| = 2^{-s(t)}`. -/
theorem mem_dilate_two_freqInt {a b : ℤ} {k : Fin 3} {t : ℤ × ℤ × ℤ} {x : ℝ} :
    x ∈ dilate 2 (freqInt a b k t) ↔
      intervalCentre (freqInt a b k t) - (2 : ℝ) ^ (-t.1) ≤ x ∧
        x < intervalCentre (freqInt a b k t) + (2 : ℝ) ^ (-t.1) := by
  rw [dilate_freqInt, intervalCentre_freqInt]
  have e1 : (2 : ℝ) ^ (-t.1) * ((freqNum a b t k : ℝ) / 3 + 1 / 2 - 2 / 2) =
      (2 : ℝ) ^ (-t.1) * ((freqNum a b t k : ℝ) / 3 + 1 / 2) - (2 : ℝ) ^ (-t.1) := by ring
  have e2 : (2 : ℝ) ^ (-t.1) * ((freqNum a b t k : ℝ) / 3 + 1 / 2 + 2 / 2) =
      (2 : ℝ) ^ (-t.1) * ((freqNum a b t k : ℝ) / 3 + 1 / 2) + (2 : ℝ) ^ (-t.1) := by ring
  rw [e1, e2]
  rfl

theorem dilate_two_freqInt_subset_three (a b : ℤ) (k : Fin 3) (t : ℤ × ℤ × ℤ) :
    dilate 2 (freqInt a b k t) ⊆ dilate 3 (freqInt a b k t) :=
  dilate_Ico_mono (freqCell_lt t.1 (freqNum a b t k)) (by norm_num)

open Classical in
/-- The side of the tile `t` for the pair of slots `(i, k)`: `true` iff `ξ' = lacRatio i k · ξ` lies
to the right of `c(ω_{t,k})` (tested at the left endpoint of `3ω_{t,i}`; see `side_of_mem`). -/
def tileSide (a b : ℤ) (i k : Fin 3) (t : ℤ × ℤ × ℤ) : Bool :=
  decide (intervalCentre (freqInt a b k t) < lacRatio i k * leftEnd3 a b i t)

/-- **The side of a tile does not depend on `ξ ∈ 3ω_{t,i}`.** For `ξ ∈ 3ω_{t,i}`, `i ≠ k`:
either `tileSide = true` and `ξ' ≥ c + |ω|`, or `tileSide = false` and `ξ' < c - |ω|`
(`ξ' = lacRatio i k · ξ`, `c = c(ω_{t,k})`, `|ω| = |ω_{t,k}|`). -/
theorem side_of_mem {a b s' α : ℤ} (hν : TriValid a b s' α) {i k : Fin 3} (hik : i ≠ k)
    (t : ℤ × ℤ × ℤ) {ξ : ℝ} (hξ : ξ ∈ dilate 3 (freqInt a b i t)) :
    (tileSide a b i k t = true ∧
        intervalCentre (freqInt a b k t) + (2 : ℝ) ^ (-t.1) ≤ lacRatio i k * ξ) ∨
      (tileSide a b i k t = false ∧
        lacRatio i k * ξ < intervalCentre (freqInt a b k t) - (2 : ℝ) ^ (-t.1)) := by
  have hw : (0 : ℝ) < (2 : ℝ) ^ (-t.1) := zpow_pos (by norm_num) _
  have hr : 0 < lacRatio i k := lacRatio_pos i k
  set c := intervalCentre (freqInt a b k t) with hc
  set w : ℝ := (2 : ℝ) ^ (-t.1) with hwdef
  set r := lacRatio i k with hrdef
  set L := leftEnd3 a b i t with hLdef
  have hξ' := mem_dilate_three_freqInt.1 hξ
  have hLξ : L ≤ ξ := hξ'.1
  have hL : L ∈ dilate 3 (freqInt a b i t) :=
    mem_dilate_three_freqInt.2 ⟨le_rfl, lt_of_le_of_lt hξ'.1 hξ'.2⟩
  have hnot : ∀ {η : ℝ}, η ∈ dilate 3 (freqInt a b i t) → r * η < c - w ∨ c + w ≤ r * η := by
    intro η hη
    have h := (lacunarity hν t hik hη).2
    rw [mem_dilate_two_freqInt] at h
    by_contra hcon
    simp only [not_or, not_lt, not_le] at hcon
    exact h hcon
  have hrL : r * L ≤ r * ξ := mul_le_mul_of_nonneg_left hLξ hr.le
  rcases hnot hL with h | h
  · right
    refine ⟨?_, ?_⟩
    · simp only [tileSide, decide_eq_false_iff_not, not_lt]
      linarith
    · rcases hnot hξ with h' | h'
      · exact h'
      · exfalso
        have hη1 : L < c / r := by rw [lt_div_iff₀ hr]; linarith
        have hη2 : c / r < ξ := by rw [div_lt_iff₀ hr]; linarith
        have hηmem : c / r ∈ dilate 3 (freqInt a b i t) :=
          mem_dilate_three_freqInt.2 ⟨le_trans (le_refl _) (le_trans le_rfl hη1.le), by
            exact lt_trans hη2 hξ'.2⟩
        have hrη : r * (c / r) = c := by field_simp
        rcases hnot hηmem with h'' | h'' <;> rw [hrη] at h'' <;> linarith
  · left
    refine ⟨?_, ?_⟩
    · simp only [tileSide, decide_eq_true_eq]
      linarith
    · rcases hnot hξ with h' | h'
      · exfalso; linarith
      · exact h'

/-- The side of the tiles of a tree: for `ξ ∈ 3ω_{t,i}` and `tileSide = true`, `ξ' ≥ c + |ω|`. -/
theorem le_ratio_mul_of_tileSide_true {a b s' α : ℤ} (hν : TriValid a b s' α) {i k : Fin 3}
    (hik : i ≠ k) (t : ℤ × ℤ × ℤ) {ξ : ℝ} (hξ : ξ ∈ dilate 3 (freqInt a b i t))
    (h : tileSide a b i k t = true) :
    intervalCentre (freqInt a b k t) + (2 : ℝ) ^ (-t.1) ≤ lacRatio i k * ξ := by
  rcases side_of_mem hν hik t hξ with h1 | h1
  · exact h1.2
  · rw [h] at h1; exact absurd h1.1 (by simp)

theorem ratio_mul_lt_of_tileSide_false {a b s' α : ℤ} (hν : TriValid a b s' α) {i k : Fin 3}
    (hik : i ≠ k) (t : ℤ × ℤ × ℤ) {ξ : ℝ} (hξ : ξ ∈ dilate 3 (freqInt a b i t))
    (h : tileSide a b i k t = false) :
    lacRatio i k * ξ < intervalCentre (freqInt a b k t) - (2 : ℝ) ^ (-t.1) := by
  rcases side_of_mem hν hik t hξ with h1 | h1
  · rw [h] at h1; exact absurd h1.1 (by simp)
  · exact h1.2

/-! ### Part 3: one stage `(i', σ)` of the algorithm -/

/-- The candidate trees of the stage `(i, σ)` (`i ≠ k`): canonical `i`-trees in `Q` all of whose tiles lie on
the side `σ` of `ω_{t,k}` (`σ = true`: `ξ' > c(ω_{t,k})`, a `>`-tree; `σ = false`: a `<`-tree). -/
def IsStageTree (a b : ℤ) (i k : Fin 3) (σ : Bool) (Q : Finset (ℤ × ℤ × ℤ)) (T : TreeData) : Prop :=
  IsTree a b i Q T ∧ T.ξ = canonXi a b i T.tiles ∧ ∀ t ∈ T.tiles, tileSide a b i k t = σ

/-- The selection criterion `Σ_{t ∈ T} |⟨f, φ_{t,k}⟩|² > (lam²/2) |I_T|`. -/
def IsLargeTree (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (k : Fin 3) (f : ℝ → ℂ) (lam : ℝ)
    (T : TreeData) : Prop :=
  lam ^ 2 / 2 * (volume T.topInt).toReal < ∑ t ∈ T.tiles, ‖pairing f (φ t k)‖ ^ 2

/-- The order key of the stage: `ξ'` for `>`-trees (smallest first), `-ξ'` for `<`-trees. -/
def stageKey (σ : Bool) (x : ℝ) : ℝ := if σ then x else -x

/-- **One stage of the algorithm, geometric part** (no Bessel inequality yet). For `i ≠ k`, a side `σ`,
`Q ⊆ P' ⊆ Idx_ν` there are a finite family `𝒯` of large `i`-trees in `P'`, the `k`-trees `⟨S T, I_T, ξ'_T⟩`
(`S T` the tiles of `Q` swallowed by `T`) and `R = Q ∖ ⋃_{T ∈ 𝒯} (P_T ∪ S T)` such that: no `σ`-sided
`i`-tree of `R` is large (`≤ lam²/2 · |I_T|`); the tile sets of `𝒯` are pairwise disjoint; and the trees of `𝒯` are
pairwise `k`-strongly disjoint. -/
theorem exists_stage_selection {a b s' α : ℤ} (hν : TriValid a b s' α) {i k : Fin 3} (hik : i ≠ k)
    (σ : Bool) {P' : Finset (ℤ × ℤ × ℤ)} (hP' : (↑P' : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {f : ℝ → ℂ} {lam : ℝ} (hlam : 0 < lam)
    {Q : Finset (ℤ × ℤ × ℤ)} (hQ : Q ⊆ P') :
    ∃ (𝒯 : Finset TreeData) (S : TreeData → Finset (ℤ × ℤ × ℤ)) (R : Finset (ℤ × ℤ × ℤ)),
      (∀ T ∈ 𝒯, IsTree a b i Q T ∧ IsLargeTree φ k f lam T) ∧
      (∀ T, IsTree a b i R T → (∀ t ∈ T.tiles, tileSide a b i k t = σ) →
        ∑ t ∈ T.tiles, ‖pairing f (φ t k)‖ ^ 2 ≤ lam ^ 2 / 2 * (volume T.topInt).toReal) ∧
      R ⊆ Q ∧
      R = Q \ 𝒯.biUnion (fun T => T.tiles ∪ S T) ∧
      (∀ T ∈ 𝒯, IsTree a b k Q ⟨S T, T.top, lacRatio i k * T.ξ⟩) ∧
      (∀ T ∈ 𝒯, Disjoint T.tiles (S T)) ∧
      (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → Disjoint (T.tiles ∪ S T) (T'.tiles ∪ S T')) ∧
      (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → ∀ t ∈ T.tiles, ∀ t' ∈ T'.tiles,
        freqInt a b k t ⊂ freqInt a b k t' → ¬ timeInt t' ⊆ T.topInt) := by
  classical
  have hmono : ∀ {Q Q' : Finset (ℤ × ℤ × ℤ)} {T : TreeData},
      IsStageTree a b i k σ Q T → Q ⊆ Q' → IsStageTree a b i k σ Q' T :=
    fun h hQQ => ⟨h.1.mono hQQ, h.2⟩
  have hsub : ∀ {Q : Finset (ℤ × ℤ × ℤ)} {T : TreeData}, IsStageTree a b i k σ Q T →
      T.tiles ⊆ Q := fun h => h.1.subset
  have hne : ∀ {T : TreeData}, IsLargeTree φ k f lam T → T.tiles.Nonempty := by
    intro T hT
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    have hv := T.toReal_volume_topInt_pos
    have hpos : 0 < lam ^ 2 / 2 * (volume T.topInt).toReal := by positivity
    unfold IsLargeTree at hT
    rw [hcon, Finset.sum_empty] at hT
    linarith
  have hfin : ∀ Q' : Finset (ℤ × ℤ × ℤ),
      ((fun T : TreeData => stageKey σ (lacRatio i k * T.ξ)) ''
        {T | IsStageTree a b i k σ Q' T ∧ IsLargeTree φ k f lam T}).Finite := by
    intro Q'
    refine ((Finset.finite_toSet Q'.powerset).image
      (fun S : Finset (ℤ × ℤ × ℤ) => stageKey σ (lacRatio i k * canonXi a b i S))).subset ?_
    rintro _ ⟨T, ⟨hT, -⟩, rfl⟩
    refine ⟨T.tiles, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_powerset]; exact hsub hT
    · simp only [hT.2.1]
  obtain ⟨𝒯, S, R, h1, h2, h3, h4, h5, h6a, h6b, h7⟩ := exists_greedy_selection
    (tiles := TreeData.tiles) (IsT := IsStageTree a b i k σ) (Large := IsLargeTree φ k f lam)
    (κ := fun T => stageKey σ (lacRatio i k * T.ξ))
    (cond := fun T t => lacRatio i k * T.ξ ∈ dilate 3 (freqInt a b k t) ∧ timeInt t ⊆ T.topInt)
    hmono hsub hne hfin Q
  refine ⟨𝒯, S, R, fun T hT => ⟨(h1 T hT).1.1, (h1 T hT).2⟩, ?_, h3, h4, ?_, h6a, h6b, ?_⟩
  · intro T hT hσ
    have hs : IsStageTree a b i k σ R { T with ξ := canonXi a b i T.tiles } :=
      ⟨hT.canonical, rfl, hσ⟩
    have hnl := h2 { T with ξ := canonXi a b i T.tiles } hs
    unfold IsLargeTree at hnl
    exact not_lt.1 hnl
  · intro T hT
    exact ⟨(h5 T hT).1, fun t ht => (h5 T hT).2 t ht⟩
  · intro T hT T' hT' _ t ht t' ht' hsubset hI
    obtain ⟨hTs, -⟩ := h1 T hT
    obtain ⟨hTs', -⟩ := h1 T' hT'
    have ht_idx : t ∈ triIdx s' α := hP' (hQ (hTs.1.subset ht))
    have ht'_idx : t' ∈ triIdx s' α := hP' (hQ (hTs'.1.subset ht'))
    have hξ := hTs.1.xi_mem ht
    obtain ⟨h50, -⟩ := lacunarity hν t hik hξ
    have h2' : lacRatio i k * T.ξ ∈ dilate 2 (freqInt a b k t') :=
      dilate_fifty_subset_dilate_two_of_ssubset ht_idx ht'_idx hsubset h50
    have h2'' := mem_dilate_two_freqInt.1 h2'
    have hξ' := hTs'.1.xi_mem ht'
    have hside := hTs'.2.2 t' ht'
    have hκ : stageKey σ (lacRatio i k * T.ξ) < stageKey σ (lacRatio i k * T'.ξ) := by
      cases σ
      · have := ratio_mul_lt_of_tileSide_false hν hik t' hξ' hside
        simp only [stageKey, Bool.false_eq_true, ↓reduceIte]
        linarith [h2''.1]
      · have := le_ratio_mul_of_tileSide_true hν hik t' hξ' hside
        simp only [stageKey, ↓reduceIte]
        linarith [h2''.2]
    exact (h7 T hT T' hT' hκ t' ht').2
      ⟨dilate_two_freqInt_subset_three a b k t' h2', hI⟩

/-! ### Part 4: the weak Bessel hypothesis and the four stages -/

/-- **The weak Bessel inequality C4, as a hypothesis** (the proof is another worker's node; exactly the shape
`PrimeBHT/TimeFrequency/Tile/Bessel.lean` is to deliver). For `i ≠ k`, finite `P ⊆ Idx_ν` with packets adapted
(exponent `N`), every finite family `𝒯` of `i`-trees in `P` whose tile sets are pairwise disjoint and which is
pairwise `k`-strongly disjoint, every `f ∈ L²` and `lam > 0` with `|⟨f, φ_{t,k}⟩|² ≤ 4 lam² |I_t|` on all tiles of
all trees and `(lam²/2) |I_T| ≤ Σ_{t ∈ T} |⟨f, φ_{t,k}⟩|²` for all `T ∈ 𝒯`:
`Σ_{T ∈ 𝒯} |I_T| ≤ C ‖f‖₂² / lam²`. -/
def WeakBesselHyp (a b s' α : ℤ) (N : ℕ) (C : ℝ) : Prop :=
  TriValid a b s' α → ∀ (i k : Fin 3), i ≠ k → ∀ (P : Finset (ℤ × ℤ × ℤ)),
    (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α →
    ∀ (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ),
      (∀ t ∈ P, ∀ j, IsAdapted N (timeInt t) (freqInt a b j t) (φ t j)) →
      ∀ 𝒯 : Finset TreeData, (∀ T ∈ 𝒯, IsTree a b i P T) →
        (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → Disjoint T.tiles T'.tiles) →
        (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → ∀ t ∈ T.tiles, ∀ t' ∈ T'.tiles,
          freqInt a b k t ⊂ freqInt a b k t' → ¬ timeInt t' ⊆ T.topInt) →
        ∀ (f : ℝ → ℂ) (lam : ℝ), 0 < lam → MemLp f 2 volume →
          (∀ T ∈ 𝒯, ∀ t ∈ T.tiles,
            ‖pairing f (φ t k)‖ ^ 2 ≤ 4 * lam ^ 2 * (volume (timeInt t)).toReal) →
          (∀ T ∈ 𝒯, lam ^ 2 / 2 * (volume T.topInt).toReal ≤
            ∑ t ∈ T.tiles, ‖pairing f (φ t k)‖ ^ 2) →
          ∑ T ∈ 𝒯, (volume T.topInt).toReal ≤ C * (∫ x, ‖f x‖ ^ 2) / lam ^ 2

theorem sum_union_le_of_nonneg {ι : Type*} [DecidableEq ι] {s t : Finset ι} {g : ι → ℝ}
    (hg : ∀ x, 0 ≤ g x) : ∑ x ∈ s ∪ t, g x ≤ ∑ x ∈ s, g x + ∑ x ∈ t, g x := by
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := g)
  have h0 : 0 ≤ ∑ x ∈ s ∩ t, g x := Finset.sum_nonneg fun x _ => hg x
  linarith

/-- **One stage with the Bessel inequality** (conditional on `hC4`). The output is a finite family
`F` of *typed* trees `(i, T)` (`T` an `i`-tree in `P'`; the `i`-trees of the stage together with the
`k`-trees `S`), and a remainder `R = Q ∖ ⋃_{x ∈ F} P_x` with: no `σ`-sided `i`-tree in `R` is large, the tile
sets of distinct members of `F` are disjoint, and `Σ_{x ∈ F} |I_x| ≤ 2 C ‖f‖₂² / lam²`. -/
theorem exists_stage_output_of_hC4 {a b s' α : ℤ} (hν : TriValid a b s' α) {N : ℕ} {C : ℝ}
    (hC4 : WeakBesselHyp a b s' α N C) {i k : Fin 3} (hik : i ≠ k) (σ : Bool)
    {P' : Finset (ℤ × ℤ × ℤ)} (hP' : (↑P' : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hφ : ∀ t ∈ P', ∀ j, IsAdapted N (timeInt t) (freqInt a b j t) (φ t j))
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) {lam : ℝ} (hlam : 0 < lam)
    (htile : ∀ t ∈ P', ‖pairing f (φ t k)‖ ^ 2 ≤ 4 * lam ^ 2 * (volume (timeInt t)).toReal)
    {Q : Finset (ℤ × ℤ × ℤ)} (hQ : Q ⊆ P') :
    ∃ (F : Finset (Fin 3 × TreeData)) (R : Finset (ℤ × ℤ × ℤ)),
      R ⊆ Q ∧ (∀ x ∈ F, IsTree a b x.1 Q x.2) ∧
      R = Q \ F.biUnion (fun x => x.2.tiles) ∧
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → Disjoint x.2.tiles y.2.tiles) ∧
      (∀ T, IsTree a b i R T → (∀ t ∈ T.tiles, tileSide a b i k t = σ) →
        ∑ t ∈ T.tiles, ‖pairing f (φ t k)‖ ^ 2 ≤ lam ^ 2 / 2 * (volume T.topInt).toReal) ∧
      ∑ x ∈ F, (volume x.2.topInt).toReal ≤ 2 * (C * (∫ x, ‖f x‖ ^ 2) / lam ^ 2) := by
  classical
  obtain ⟨𝒯, S, R, h1, h2, h3, h4, h5, h6a, h6b, h7⟩ :=
    exists_stage_selection (φ := φ) (f := f) hν hik σ hP' hlam hQ
  have hdisjT : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → Disjoint T.tiles T'.tiles :=
    fun T hT T' hT' hne => (h6b T hT T' hT' hne).mono Finset.subset_union_left
      Finset.subset_union_left
  have hbound : ∑ T ∈ 𝒯, (volume T.topInt).toReal ≤ C * (∫ x, ‖f x‖ ^ 2) / lam ^ 2 := by
    refine hC4 hν i k hik P' hP' φ hφ 𝒯 (fun T hT => (h1 T hT).1.mono hQ) hdisjT h7 f lam hlam hf
      ?_ ?_
    · intro T hT t ht
      exact htile t (hQ ((h1 T hT).1.subset ht))
    · intro T hT
      exact (h1 T hT).2.le
  set g : TreeData → TreeData := fun T => ⟨S T, T.top, lacRatio i k * T.ξ⟩ with hg
  have hAB : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, Disjoint T.tiles (S T') := by
    intro T hT T' hT'
    by_cases h : T = T'
    · subst h; exact h6a T hT
    · exact (h6b T hT T' hT' h).mono Finset.subset_union_left Finset.subset_union_right
  refine ⟨𝒯.image (fun T => (i, T)) ∪ 𝒯.image (fun T => (k, g T)), R, h3, ?_, ?_, ?_, h2, ?_⟩
  · intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hx
      exact (h1 T hT).1
    · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hx
      exact h5 T hT
  · rw [h4]
    congr 1
    ext t
    simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨T, hT, ht | ht⟩
      · exact ⟨(i, T), Or.inl ⟨T, hT, rfl⟩, ht⟩
      · exact ⟨(k, g T), Or.inr ⟨T, hT, rfl⟩, ht⟩
    · rintro ⟨x, (⟨T, hT, rfl⟩ | ⟨T, hT, rfl⟩), ht⟩
      · exact ⟨T, hT, Or.inl ht⟩
      · exact ⟨T, hT, Or.inr ht⟩
  · intro x hx y hy hxy
    rcases Finset.mem_union.1 hx with hx | hx <;> rcases Finset.mem_union.1 hy with hy | hy
    · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨T', hT', rfl⟩ := Finset.mem_image.1 hy
      exact hdisjT T hT T' hT' (fun h => hxy (by rw [h]))
    · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨T', hT', rfl⟩ := Finset.mem_image.1 hy
      exact hAB T hT T' hT'
    · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨T', hT', rfl⟩ := Finset.mem_image.1 hy
      exact (hAB T' hT' T hT).symm
    · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨T', hT', rfl⟩ := Finset.mem_image.1 hy
      have hne : T ≠ T' := fun h => hxy (by rw [h])
      exact (h6b T hT T' hT' hne).mono Finset.subset_union_right Finset.subset_union_right
  · have hnn : ∀ x : Fin 3 × TreeData, 0 ≤ (volume x.2.topInt).toReal := fun _ =>
      ENNReal.toReal_nonneg
    have hA : ∑ x ∈ 𝒯.image (fun T => (i, T)), (volume x.2.topInt).toReal =
        ∑ T ∈ 𝒯, (volume T.topInt).toReal := by
      rw [Finset.sum_image (fun _ _ _ _ h => (Prod.mk.inj h).2)]
    have hB : ∑ x ∈ 𝒯.image (fun T => (k, g T)), (volume x.2.topInt).toReal ≤
        ∑ T ∈ 𝒯, (volume T.topInt).toReal :=
      Finset.sum_image_le_of_nonneg (g := fun T => (k, g T))
        (f := fun x : Fin 3 × TreeData => (volume x.2.topInt).toReal) (fun x _ => hnn x)
    calc ∑ x ∈ 𝒯.image (fun T => (i, T)) ∪ 𝒯.image (fun T => (k, g T)),
          (volume x.2.topInt).toReal
        ≤ ∑ x ∈ 𝒯.image (fun T => (i, T)), (volume x.2.topInt).toReal +
          ∑ x ∈ 𝒯.image (fun T => (k, g T)), (volume x.2.topInt).toReal :=
          sum_union_le_of_nonneg hnn
      _ ≤ ∑ T ∈ 𝒯, (volume T.topInt).toReal + ∑ T ∈ 𝒯, (volume T.topInt).toReal := by
          rw [hA]; exact add_le_add le_rfl hB
      _ ≤ 2 * (C * (∫ x, ‖f x‖ ^ 2) / lam ^ 2) := by linarith

/-- **Several stages in sequence** (conditional on `hC4`), by induction on the finite set of stages
`(i, σ)` (all with `i ≠ k`): each stage works on the remainder of the previous ones. -/
theorem exists_multiStage_of_hC4 {a b s' α : ℤ} (hν : TriValid a b s' α) {N : ℕ} {C : ℝ}
    (hC4 : WeakBesselHyp a b s' α N C) {k : Fin 3}
    {P' : Finset (ℤ × ℤ × ℤ)} (hP' : (↑P' : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hφ : ∀ t ∈ P', ∀ j, IsAdapted N (timeInt t) (freqInt a b j t) (φ t j))
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) {lam : ℝ} (hlam : 0 < lam)
    (htile : ∀ t ∈ P', ‖pairing f (φ t k)‖ ^ 2 ≤ 4 * lam ^ 2 * (volume (timeInt t)).toReal) :
    ∀ stg : Finset (Fin 3 × Bool), (∀ st ∈ stg, st.1 ≠ k) → ∀ Q : Finset (ℤ × ℤ × ℤ), Q ⊆ P' →
      ∃ (F : Finset (Fin 3 × TreeData)) (R : Finset (ℤ × ℤ × ℤ)),
        R ⊆ Q ∧ (∀ x ∈ F, IsTree a b x.1 Q x.2) ∧
        R = Q \ F.biUnion (fun x => x.2.tiles) ∧
        (∀ x ∈ F, ∀ y ∈ F, x ≠ y → Disjoint x.2.tiles y.2.tiles) ∧
        (∀ st ∈ stg, ∀ T, IsTree a b st.1 R T → (∀ t ∈ T.tiles, tileSide a b st.1 k t = st.2) →
          ∑ t ∈ T.tiles, ‖pairing f (φ t k)‖ ^ 2 ≤ lam ^ 2 / 2 * (volume T.topInt).toReal) ∧
        ∑ x ∈ F, (volume x.2.topInt).toReal ≤
          2 * (stg.card : ℝ) * (C * (∫ x, ‖f x‖ ^ 2) / lam ^ 2) := by
  classical
  intro stg
  induction stg using Finset.induction_on with
  | empty =>
    intro _ Q _
    exact ⟨∅, Q, subset_rfl, by simp, by simp, by simp, by simp, by simp⟩
  | insert st stg hst ih =>
    intro hstg Q hQ
    have hik : st.1 ≠ k := hstg st (Finset.mem_insert_self _ _)
    obtain ⟨F₁, R₁, hR₁Q, hF₁, hR₁, hd₁, hn₁, hs₁⟩ :=
      exists_stage_output_of_hC4 hν hC4 hik st.2 hP' hφ hf hlam htile hQ
    obtain ⟨F₂, R, hRR₁, hF₂, hR, hd₂, hn₂, hs₂⟩ :=
      ih (fun x hx => hstg x (Finset.mem_insert_of_mem hx)) R₁ (hR₁Q.trans hQ)
    have hF₂sub : ∀ x ∈ F₂, x.2.tiles ⊆ R₁ := fun x hx => (hF₂ x hx).subset
    have hnn : ∀ x : Fin 3 × TreeData, 0 ≤ (volume x.2.topInt).toReal := fun _ =>
      ENNReal.toReal_nonneg
    have hcross : ∀ x ∈ F₁, ∀ y ∈ F₂, Disjoint x.2.tiles y.2.tiles := by
      intro x hx y hy
      refine Finset.disjoint_left.2 fun t ht ht' => ?_
      have h1 := hF₂sub y hy ht'
      rw [hR₁, Finset.mem_sdiff] at h1
      exact h1.2 (Finset.mem_biUnion.2 ⟨x, hx, ht⟩)
    refine ⟨F₁ ∪ F₂, R, hRR₁.trans hR₁Q, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact hF₁ x hx
      · exact (hF₂ x hx).mono hR₁Q
    · rw [Finset.union_biUnion, hR, hR₁, sdiff_sdiff_left]
      rfl
    · intro x hx y hy hxy
      rcases Finset.mem_union.1 hx with hx | hx <;> rcases Finset.mem_union.1 hy with hy | hy
      · exact hd₁ x hx y hy hxy
      · exact hcross x hx y hy
      · exact (hcross y hy x hx).symm
      · exact hd₂ x hx y hy hxy
    · intro st' hst'
      rcases Finset.mem_insert.1 hst' with h | h
      · rw [h]
        exact fun T hT hσ => hn₁ T (hT.mono hRR₁) hσ
      · exact hn₂ st' h
    · have hc : ((insert st stg).card : ℝ) = stg.card + 1 := by
        rw [Finset.card_insert_of_notMem hst]; push_cast; ring
      calc ∑ x ∈ F₁ ∪ F₂, (volume x.2.topInt).toReal
          ≤ ∑ x ∈ F₁, (volume x.2.topInt).toReal + ∑ x ∈ F₂, (volume x.2.topInt).toReal :=
            sum_union_le_of_nonneg hnn
        _ ≤ 2 * (C * (∫ x, ‖f x‖ ^ 2) / lam ^ 2) +
            2 * (stg.card : ℝ) * (C * (∫ x, ‖f x‖ ^ 2) / lam ^ 2) := add_le_add hs₁ hs₂
        _ = 2 * ((insert st stg).card : ℝ) * (C * (∫ x, ‖f x‖ ^ 2) / lam ^ 2) := by
            rw [hc]; ring

/-! ### Part 5: the selection lemma -/

/-- The output of the selection lemma: the selected trees `trees i` of each type `i` and the remainder `rest`. -/
structure SelectionOutput where
  /-- The selected `i`-trees, `i = 0, 1, 2`. -/
  trees : Fin 3 → Finset TreeData
  /-- The remaining tiles `P''`. -/
  rest : Finset (ℤ × ℤ × ℤ)

/-- The properties of a selection (BD26 `l:tree`, unshifted): the selected `i`-trees lie in `P'`; the tile sets
of distinct selected trees (of any types) are disjoint; `rest = P' ∖ ⋃ (selected tiles)`; (a) the sizes of
`rest` are `≤ lam` (`i = 0, 1, 2`); (b) `Σ_i Σ_{T ∈ trees i} |I_T| ≤ B`. -/
def IsSelection (a b : ℤ) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (k : Fin 3) (f : ℝ → ℂ) (lam B : ℝ)
    (P' : Finset (ℤ × ℤ × ℤ)) (out : SelectionOutput) : Prop :=
  (∀ i, ∀ T ∈ out.trees i, IsTree a b i P' T) ∧
  (∀ i, ∀ T ∈ out.trees i, ∀ j, ∀ T' ∈ out.trees j, (i ≠ j ∨ T ≠ T') →
    Disjoint T.tiles T'.tiles) ∧
  out.rest = P' \ Finset.univ.biUnion (fun i => (out.trees i).biUnion TreeData.tiles) ∧
  (∀ i, size a b φ i k f out.rest ≤ ENNReal.ofReal lam) ∧
  ∑ i, ∑ T ∈ out.trees i, (volume T.topInt).toReal ≤ B

/-- The tile bound `|⟨f, φ_{t,k}⟩|² ≤ 4 lam² |I_t|` from `size_{k,k}(f, P') ≤ 2 lam`. -/
theorem norm_sq_pairing_le_of_size {a b : ℤ} {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {k : Fin 3}
    {f : ℝ → ℂ} {P' : Finset (ℤ × ℤ × ℤ)} {lam : ℝ} (hlam : 0 < lam)
    (h : size a b φ k k f P' ≤ ENNReal.ofReal (2 * lam)) :
    ∀ t ∈ P', ‖pairing f (φ t k)‖ ^ 2 ≤ 4 * lam ^ 2 * (volume (timeInt t)).toReal := by
  intro t ht
  rw [size_self] at h
  have h1 := norm_pairing_le_of_sizeDiag_le (by positivity : (0 : ℝ) ≤ 2 * lam) h ht
  have hv := toReal_volume_timeInt_pos t
  have h2 : ((volume (timeInt t)).toReal ^ ((1 : ℝ) / 2)) ^ 2 = (volume (timeInt t)).toReal := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv.le]; norm_num
  calc ‖pairing f (φ t k)‖ ^ 2
      ≤ (2 * lam * (volume (timeInt t)).toReal ^ ((1 : ℝ) / 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = 4 * lam ^ 2 * (volume (timeInt t)).toReal := by rw [mul_pow, mul_pow, h2]; ring

/-- **The tree selection lemma (C5; BD26 `l:tree`, unshifted), conditional on the weak Bessel inequality
`hC4` (C4).** Let `k` be a slot, `P' ⊆ Idx_ν` finite with adapted packets, `f ∈ L²`, `lam > 0` and
`size_{i,k}(f, P') ≤ 2 lam` for `i = 0, 1, 2`. Then there are finite families `trees i` of `i`-trees in `P'`
(including the `k`-trees `S` of the algorithm) with pairwise disjoint tile sets such that, with
`rest = P' ∖ ⋃ tiles`, (a) `size_{i,k}(f, rest) ≤ lam` for all `i`, and
(b) `Σ_i Σ_{T ∈ trees i} |I_T| ≤ 8 C ‖f‖₂² / lam²`. -/
theorem exists_selection_of_hC4 {a b s' α : ℤ} (hν : TriValid a b s' α) {N : ℕ} {C : ℝ}
    (hC4 : WeakBesselHyp a b s' α N C) {P' : Finset (ℤ × ℤ × ℤ)}
    (hP' : (↑P' : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α) {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hφ : ∀ t ∈ P', ∀ j, IsAdapted N (timeInt t) (freqInt a b j t) (φ t j)) (k : Fin 3)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) {lam : ℝ} (hlam : 0 < lam)
    (hsize : ∀ i, size a b φ i k f P' ≤ ENNReal.ofReal (2 * lam)) :
    ∃ out : SelectionOutput,
      IsSelection a b φ k f lam (8 * C * (∫ x, ‖f x‖ ^ 2) / lam ^ 2) P' out := by
  classical
  have htile := norm_sq_pairing_le_of_size hlam (hsize k)
  set stg : Finset (Fin 3 × Bool) :=
    ((Finset.univ : Finset (Fin 3)).erase k) ×ˢ (Finset.univ : Finset Bool) with hstg
  have hstgk : ∀ st ∈ stg, st.1 ≠ k := by
    intro st hst
    rw [hstg, Finset.mem_product, Finset.mem_erase] at hst
    exact hst.1.1
  have hcard : stg.card = 4 := by
    rw [hstg, Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ k)]
    simp
  obtain ⟨F, R, -, hF, hR, hd, hn, hs⟩ :=
    exists_multiStage_of_hC4 hν hC4 hP' hφ hf hlam htile stg hstgk P' subset_rfl
  have hmem : ∀ (i : Fin 3) (T : TreeData),
      T ∈ (F.filter (fun x => x.1 = i)).image Prod.snd ↔ (i, T) ∈ F := by
    intro i T
    simp only [Finset.mem_image, Finset.mem_filter, Prod.exists]
    constructor
    · rintro ⟨a, b, ⟨hab, rfl⟩, rfl⟩
      exact hab
    · intro h
      exact ⟨i, T, ⟨h, rfl⟩, rfl⟩
  have hU : (Finset.univ : Finset (Fin 3)).biUnion
      (fun i => ((F.filter (fun x => x.1 = i)).image Prod.snd).biUnion TreeData.tiles) =
      F.biUnion (fun x => x.2.tiles) := by
    ext t
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, T, hT, ht⟩
      exact ⟨(i, T), (hmem i T).1 hT, ht⟩
    · rintro ⟨x, hx, ht⟩
      exact ⟨x.1, x.2, (hmem x.1 x.2).2 hx, ht⟩
  -- sizes of the remainder, `i ≠ k`
  have hsz : ∀ i, i ≠ k → size a b φ i k f R ≤ ENNReal.ofReal lam := by
    intro i hik
    rw [size_of_ne hik, sizeOff_le_ofReal_iff hlam.le]
    intro T hT
    have hAmem : (i, true) ∈ stg := by
      rw [hstg, Finset.mem_product, Finset.mem_erase]; simp [hik]
    have hBmem : (i, false) ∈ stg := by
      rw [hstg, Finset.mem_product, Finset.mem_erase]; simp [hik]
    have hA := hn (i, true) hAmem
      { T with tiles := T.tiles.filter (fun t => tileSide a b i k t = true) }
      (hT.restrict (Finset.filter_subset _ _)) (fun t ht => (Finset.mem_filter.1 ht).2)
    have hB := hn (i, false) hBmem
      { T with tiles := T.tiles.filter (fun t => ¬ tileSide a b i k t = true) }
      (hT.restrict (Finset.filter_subset _ _))
      (fun t ht => by simpa using (Finset.mem_filter.1 ht).2)
    have hsplit := Finset.sum_filter_add_sum_filter_not T.tiles
      (fun t => tileSide a b i k t = true) (fun t => ‖pairing f (φ t k)‖ ^ 2)
    have hA' : ∑ t ∈ T.tiles.filter (fun t => tileSide a b i k t = true),
        ‖pairing f (φ t k)‖ ^ 2 ≤ lam ^ 2 / 2 * (volume T.topInt).toReal := hA
    have hB' : ∑ t ∈ T.tiles.filter (fun t => ¬ tileSide a b i k t = true),
        ‖pairing f (φ t k)‖ ^ 2 ≤ lam ^ 2 / 2 * (volume T.topInt).toReal := hB
    rw [← hsplit]
    linarith
  obtain ⟨i', hi'⟩ : ∃ i' : Fin 3, i' ≠ k := exists_ne k
  have hsz' : ∀ i, size a b φ i k f R ≤ ENNReal.ofReal lam := by
    intro i
    by_cases hik : i = k
    · subst hik
      rw [size_self]
      calc sizeDiag φ i f R ≤ sizeOff a b φ i' i f R := sizeDiag_le_sizeOff
        _ = size a b φ i' i f R := (size_of_ne hi' f R).symm
        _ ≤ ENNReal.ofReal lam := hsz i' hi'
    · exact hsz i hik
  refine ⟨⟨fun i => (F.filter (fun x => x.1 = i)).image Prod.snd, R⟩, ?_, ?_, ?_, hsz', ?_⟩
  · intro i T hT
    exact hF (i, T) ((hmem i T).1 hT)
  · intro i T hT j T' hT' hij
    refine hd (i, T) ((hmem i T).1 hT) (j, T') ((hmem j T').1 hT') ?_
    intro h
    rcases hij with h' | h'
    · exact h' (Prod.mk.inj h).1
    · exact h' (Prod.mk.inj h).2
  · show R = P' \ _
    rw [hU]
    exact hR
  · have hnn : ∀ x : Fin 3 × TreeData, 0 ≤ (volume x.2.topInt).toReal := fun _ =>
      ENNReal.toReal_nonneg
    calc ∑ i, ∑ T ∈ (F.filter (fun x => x.1 = i)).image Prod.snd, (volume T.topInt).toReal
        ≤ ∑ i, ∑ x ∈ F.filter (fun x => x.1 = i), (volume x.2.topInt).toReal :=
          Finset.sum_le_sum fun i _ => Finset.sum_image_le_of_nonneg (g := Prod.snd)
            (f := fun T : TreeData => (volume T.topInt).toReal) (fun _ _ => ENNReal.toReal_nonneg)
      _ = ∑ x ∈ F, (volume x.2.topInt).toReal :=
          Finset.sum_fiberwise F (fun x => x.1) (fun x => (volume x.2.topInt).toReal)
      _ ≤ 2 * (stg.card : ℝ) * (C * (∫ x, ‖f x‖ ^ 2) / lam ^ 2) := hs
      _ = 8 * C * (∫ x, ‖f x‖ ^ 2) / lam ^ 2 := by
          rw [hcard]; push_cast; ring

end PrimeBHT.TimeFrequency.Tile
