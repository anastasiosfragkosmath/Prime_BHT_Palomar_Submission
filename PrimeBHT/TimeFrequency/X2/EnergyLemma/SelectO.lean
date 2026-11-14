module

public import PrimeBHT.TimeFrequency.X2.EnergyLemma.Select
public import PrimeBHT.TimeFrequency.X2.Ortho.PintNested

/-!
# X2, node V12 (redesign): selections whose output is `IsStronglyDisjointO`

The three-phase selection of `Select.lean` produces `IsStronglyDisjointN` families, which is NOT enough: `pint` is FALSE for
`IsStronglyDisjointN` (shell chains, `Ortho/Nested.lean`).  The true statement is `pint` for `IsStronglyDisjointO`
(`pint_two_O_statement`), whose clause `O2` (wide tile in the LATER tree) holds for every greedy selection
(`removal_disjoint_close`) and whose clause `O1` (wide tile in the EARLIER tree) is a property of the ORDER of the selection.

* `SelSeq V S 𝒯`: a greedy selection of candidates `V` from the collection `S` (each round removes the maximal tree
  `maxTree S t` of the chosen tree `(Tr, t)`; NO optimality condition on the order);
* `OSelectable`: **the selection lemma, stated as a hypothesis** (the combinatorial game of the report): for a candidate
  predicate `V` of lacunary trees with tops, closed under SHRINKING THE TOP WINDOW (which is what `θ < topNorm` is),
  there is a greedy selection that runs until no candidate is left and whose list is `IsStronglyDisjointO`;
* `selectionO`: from `OSelectable` the halving `eng(residual) ≤ θ` and the family with `θ < topNorm`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-- A greedy selection sequence of candidates `V` (no condition on the order of the choices). -/
def SelSeq (V : Finset TriTile → Top → Prop) : Finset TriTile → List (Finset TriTile × Top) → Prop
  | _, [] => True
  | S, T :: 𝒯 => V T.1 T.2 ∧ T.1 ⊆ S ∧ SelSeq V (S \ maxTree S T.2.1 T.2.2) 𝒯

theorem SelSeq.subset : ∀ {V : Finset TriTile → Top → Prop} {S : Finset TriTile}
    {𝒯 : List (Finset TriTile × Top)}, SelSeq V S 𝒯 → ∀ T ∈ 𝒯, T.1 ⊆ S
  | _, _, [], _, T, hT => absurd hT (List.not_mem_nil)
  | V, S, T₀ :: 𝒯, h, T, hT => by
    obtain ⟨-, h2, h4⟩ := h
    rcases List.mem_cons.1 hT with rfl | hT
    · exact h2
    · exact (SelSeq.subset h4 T hT).trans Finset.sdiff_subset

theorem SelSeq.valid : ∀ {V : Finset TriTile → Top → Prop} {S : Finset TriTile}
    {𝒯 : List (Finset TriTile × Top)}, SelSeq V S 𝒯 → ∀ T ∈ 𝒯, V T.1 T.2
  | _, _, [], _, T, hT => absurd hT (List.not_mem_nil)
  | V, S, T₀ :: 𝒯, h, T, hT => by
    obtain ⟨h1, -, h4⟩ := h
    rcases List.mem_cons.1 hT with rfl | hT
    · exact h1
    · exact SelSeq.valid h4 T hT

/-- Candidate predicates of the energy lemma are closed under shrinking the window of the top (the factor
`|I_t|^{-1/q}` of `topNorm` increases). -/
def SelClosed (V : Finset TriTile → Top → Prop) : Prop :=
  ∀ Tr t t', V Tr t → IsTree Tr t' → t'.1.1 ≤ t.1.1 → V Tr t'

/-- The clause `O1` of `IsStronglyDisjointO` for the pairs `T` before `T'` of a list: a tile `R` of the EARLIER tree whose
frequency interval is larger-or-equal to the one of a `10`-close tile `R'` (distinct box) of the later tree is disjoint
from the top of `T'`. -/
def OClause1 (k : Fin 3) (𝒯 : List (Finset TriTile × Top)) : Prop :=
  𝒯.Pairwise (fun T T' =>
    ∀ R ∈ T.1, ∀ R' ∈ T'.1, R.box ≠ R'.box → R.box.scale ≤ R'.box.scale →
      (dilate 10 (R'.box.ω k) ∩ dilate 10 (R.box.ω k)).Nonempty →
      Disjoint R.I (dyadicInt T'.2.1.1 T'.2.1.2))

/-- Tile-disjointness and the clause `O2` (wide tile in the LATER tree) hold for EVERY greedy selection
(`removal_disjoint_close`). -/
theorem SelSeq.pairwise_O2 {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {k : Fin 3}
    {V : Finset TriTile → Top → Prop} (hV : ∀ Tr t, V Tr t → IsTree Tr t) :
    ∀ {S : Finset TriTile} {𝒯 : List (Finset TriTile × Top)}, (∀ R ∈ S, R.box ∈ Qs) → SelSeq V S 𝒯 →
      𝒯.Pairwise (fun T T' => Disjoint T.1 T'.1 ∧
        ∀ R ∈ T.1, ∀ R' ∈ T'.1, R.box ≠ R'.box → R'.box.scale ≤ R.box.scale →
          (dilate 10 (R'.box.ω k) ∩ dilate 10 (R.box.ω k)).Nonempty →
          Disjoint R'.I (dyadicInt T.2.1.1 T.2.1.2))
  | _, [], _, _ => List.Pairwise.nil
  | S, T :: 𝒯, hS, h => by
    obtain ⟨h1, h2, h4⟩ := h
    refine List.Pairwise.cons (fun T' hT' => ?_)
      (SelSeq.pairwise_O2 hQ hV (fun R hR => hS R (Finset.mem_sdiff.1 hR).1) h4)
    have hsub : T'.1 ⊆ S \ maxTree S T.2.1 T.2.2 := SelSeq.subset h4 T' hT'
    have hT := hV _ _ h1
    refine ⟨?_, fun R hR R' hR' hne hs hc => ?_⟩
    · rw [Finset.disjoint_left]
      intro R hR hR'
      have hM : R ∈ maxTree S T.2.1 T.2.2 := mem_maxTree.2 ⟨h2 hR, (hT R hR).1, (hT R hR).2⟩
      exact (Finset.mem_sdiff.1 (hsub hR')).2 hM
    · exact removal_disjoint_close hQ hS hT hsub hR (h2 hR) hR' hne.symm hs hc

/-- **The selection lemma (OPEN; hypothesis).**  For every finite collection `S` of tiles of a rank-1 box set and every
closed predicate `V` of nonempty `k`-lacunary trees with tops, there is a greedy selection from `V` that runs until no
candidate is left and satisfies the clause `O1`.  (The clause `O2` and tile-disjointness are automatic,
`SelSeq.pairwise_O2`.)  An exact solver of the underlying game on an abstract model of the hull forest finds no unwinnable
instance, and the greedy rule "fewest intact strict absorbers, then smallest window" wins in all tested instances; no
proof is known (see the report). -/
def OSelectable : Prop :=
  ∀ (J : ℕ) (Qs : Set Box), IsRankOne J Qs → 16 ≤ J → ∀ (k : Fin 3) (S : Finset TriTile),
    (∀ R ∈ S, R.box ∈ Qs) → ∀ V : Finset TriTile → Top → Prop,
      (∀ Tr t, V Tr t → Tr.Nonempty ∧ IsTree Tr t ∧ IsLacunary k Tr) → SelClosed V →
        ∃ 𝒯 : List (Finset TriTile × Top), SelSeq V S 𝒯 ∧ OClause1 k 𝒯 ∧
          ∀ Tr ⊆ removeTrees S (𝒯.map Prod.snd), ∀ t, ¬ V Tr t

theorem isStronglyDisjointO_of_selSeq {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {k : Fin 3}
    {V : Finset TriTile → Top → Prop} (hV : ∀ Tr t, V Tr t → Tr.Nonempty ∧ IsTree Tr t ∧ IsLacunary k Tr)
    {S : Finset TriTile} (hS : ∀ R ∈ S, R.box ∈ Qs) {𝒯 : List (Finset TriTile × Top)} (h : SelSeq V S 𝒯)
    (h1 : OClause1 k 𝒯) : IsStronglyDisjointO k 𝒯 := by
  refine ⟨fun T hT => ⟨(hV _ _ (h.valid T hT)).2.1, (hV _ _ (h.valid T hT)).2.2⟩, ?_⟩
  have h2 := SelSeq.pairwise_O2 (k := k) hQ (fun Tr t ht => (hV Tr t ht).2.1) hS h
  have := h2.and h1
  refine this.imp fun {T T'} hh => ⟨hh.1.1, hh.2, hh.1.2⟩

/-! ## `topNorm` and the window of the top -/

theorem topNorm_mono_top {P : ℕ} [NeZero P] (𝔭 : Params) (s : ℝ) (k : Fin 3) (F : ℝ → ZMod P → ℂ)
    (Tr : Finset TriTile) {t t' : Top} (h : t'.1.1 ≤ t.1.1) {q : ℝ} (hq : 0 < q) :
    topNorm 𝔭 s k F Tr t q ≤ topNorm 𝔭 s k F Tr t' q := by
  refine topNorm_le_of_forall fun ψ m hdata => ?_
  refine le_trans ?_ (le_topNorm hdata (t := t'))
  unfold treeOpNorm
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  have h2 : (2 : ℝ) ^ t'.1.1 ≤ (2 : ℝ) ^ t.1.1 := zpow_le_zpow_right₀ (by norm_num) h
  have hz : (-1 / q) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hq.le
  exact Real.rpow_le_rpow_of_nonpos (zpow_pos (by norm_num) _) h2 hz

theorem eng_le_of_no_candidates_O {P : ℕ} [NeZero P] (𝔭 : Params) {s qX : ℝ} (hs : 1 ≤ s) (k : Fin 3)
    (F : ℝ → ZMod P → ℂ) (θ : ℝ≥0∞) {S : Finset TriTile}
    (hno : ∀ Tr ⊆ S, ∀ t, ¬ (Tr.Nonempty ∧ IsTree Tr t ∧ IsLacunary k Tr ∧ θ < topNorm 𝔭 s k F Tr t qX)) :
    eng 𝔭 s k F S qX ≤ θ := by
  have hs0 : 0 < s := by linarith
  refine eng_le_of_forall fun Tr hTrS t htree hlac => ?_
  by_contra hcon
  push Not at hcon
  have hne : Tr.Nonempty := by
    rcases Tr.eq_empty_or_nonempty with h | h
    · rw [h, topNorm_empty 𝔭 hs0] at hcon
      exact absurd hcon (not_lt.2 zero_le)
    · exact h
  exact hno Tr hTrS t ⟨hne, htree, hlac, hcon⟩

/-- **The selection of the energy lemma from `OSelectable`**: a `k`-strongly disjoint (`IsStronglyDisjointO`) family of
lacunary trees, each with `θ < topNorm`, inside `S₀`, whose maximal trees leave a residual of energy `≤ θ`. -/
theorem selectionO (hsel : OSelectable) {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) (hJ : 16 ≤ J)
    {S₀ : Finset TriTile} (hS₀ : ∀ R ∈ S₀, R.box ∈ Qs) (𝔭 : Params) {s qX : ℝ} (hs : 1 ≤ s) (hq : 0 < qX)
    (k : Fin 3) {P : ℕ} [NeZero P] (F : ℝ → ZMod P → ℂ) (θ : ℝ≥0∞) :
    ∃ 𝒯 : List (Finset TriTile × Top), IsStronglyDisjointO k 𝒯 ∧
      (∀ T ∈ 𝒯, T.1 ⊆ S₀ ∧ θ < topNorm 𝔭 s k F T.1 T.2 qX) ∧
      eng 𝔭 s k F (removeTrees S₀ (𝒯.map Prod.snd)) qX ≤ θ := by
  set V : Finset TriTile → Top → Prop := fun Tr t =>
    Tr.Nonempty ∧ IsTree Tr t ∧ IsLacunary k Tr ∧ θ < topNorm 𝔭 s k F Tr t qX with hV
  have hV1 : ∀ Tr t, V Tr t → Tr.Nonempty ∧ IsTree Tr t ∧ IsLacunary k Tr :=
    fun Tr t h => ⟨h.1, h.2.1, h.2.2.1⟩
  have hV2 : SelClosed V := by
    intro Tr t t' h ht' hle
    exact ⟨h.1, ht', h.2.2.1, lt_of_lt_of_le h.2.2.2 (topNorm_mono_top 𝔭 s k F Tr hle hq)⟩
  obtain ⟨𝒯, hseq, hO1, hend⟩ := hsel J Qs hQ hJ k S₀ hS₀ V hV1 hV2
  refine ⟨𝒯, isStronglyDisjointO_of_selSeq hQ hV1 hS₀ hseq hO1, fun T hT => ⟨hseq.subset T hT, (hseq.valid T hT).2.2.2⟩, ?_⟩
  exact eng_le_of_no_candidates_O 𝔭 hs k F θ fun Tr hTr t ht => hend Tr hTr t ht

end PrimeBHT.TimeFrequency.X2
