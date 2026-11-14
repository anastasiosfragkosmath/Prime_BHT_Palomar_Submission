module

public import PrimeBHT.TimeFrequency.X2.TreeS.Tile
public import PrimeBHT.TimeFrequency.X2.V16.Hyps

/-!
# X2, node V15s: the single-scale tree lemma

`treeLemmaSingleScale : TreeLemmaSingleScaleStatement` (`X2/V16/Hyps.lean`): for a good tree of one scale (a single box, so
`R ↦ R.pos` is injective and the tile intervals `I_R ⊆ I_t` are pairwise disjoint)
`‖Λ_Tr‖ ≤ ∑_R ‖∫ χ_R Π(T_{m₀}F₀, T_{m₁}F₁, T_{m₂}F₂)‖ ≤ C CT ∑_R |I_R| ∏_k eng ≤ C CT |I_t| ∏_k eng`
(`tile_form_le` for each tile).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- The tile intervals of a single-scale good tree are pairwise disjoint. -/
theorem tileI_disjoint_of_goodTree {Tr : Finset TriTile} {t : Top} (htree : IsGoodTree Tr t) (hss : SingleScale Tr)
    {Q Q' : TriTile} (hQ : Q ∈ Tr) (hQ' : Q' ∈ Tr) (hne : Q ≠ Q') : Disjoint Q.I Q'.I := by
  obtain ⟨s₀, hs₀⟩ := hss
  have hsc : Q.box.scale = Q'.box.scale := by rw [hs₀ Q hQ, hs₀ Q' hQ']
  have hbox : Q.box = Q'.box := htree.2.1 Q hQ Q' hQ' hsc
  have hpos : Q.pos ≠ Q'.pos := by
    intro h
    apply hne
    cases Q; cases Q'
    simp only at hbox h
    simp [hbox, h]
  unfold TriTile.I
  rcases dyadicInt_nested_or_disjoint Q.box.scale Q.pos Q'.box.scale Q'.pos with h | h | h
  · exact absurd (index_eq_of_dyadicInt_subset hsc h) hpos
  · exact absurd (index_eq_of_dyadicInt_subset hsc.symm h).symm hpos
  · exact h

/-- `∑_{R ∈ Tr} |I_R| ≤ |I_t|`. -/
theorem sum_len_le_top {Tr : Finset TriTile} {t : Top} (htree : IsGoodTree Tr t) (hss : SingleScale Tr) :
    ∑ R ∈ Tr, ENNReal.ofReal ((2 : ℝ) ^ R.box.scale) ≤ ENNReal.ofReal ((2 : ℝ) ^ t.1.1) := by
  have hpd : (Tr : Set TriTile).PairwiseDisjoint (fun R => R.I) :=
    fun Q hQ Q' hQ' hne => tileI_disjoint_of_goodTree htree hss hQ hQ' hne
  calc ∑ R ∈ Tr, ENNReal.ofReal ((2 : ℝ) ^ R.box.scale) = ∑ R ∈ Tr, volume R.I := by
        refine Finset.sum_congr rfl fun R _ => ?_
        unfold TriTile.I; rw [volume_dyadicInt]
    _ = volume (⋃ R ∈ Tr, R.I) := (measure_biUnion_finset hpd fun R _ => measurableSet_dyadicInt _ _).symm
    _ ≤ volume (dyadicInt t.1.1 t.1.2) := measure_mono (iUnion₂_subset fun R hR => (htree.1 R hR).1)
    _ = _ := volume_dyadicInt _ _

theorem treeLemmaSingleScale : TreeLemmaSingleScaleStatement := by
  intro 𝔭 h𝔭 _ u R hu hR
  obtain ⟨C₁, hC₁, hC⟩ := tile_form_le h𝔭 hu hR
  refine ⟨C₁, hC₁, ?_⟩
  intro P _ T CT hT Qs hQ Tr t htree hss hbox χ m hdata F hFm hFb
  obtain ⟨hcls, hcons, η, hη, hχ⟩ := hdata
  set Pr : ℝ≥0∞ := ∏ k, eng 𝔭.tree (slotExp u k) k (F k) Tr (qv R k) with hPr
  have hterm : ∀ Q ∈ Tr, ‖∫ x, (χ Q x : ℂ) * T (tmult (m Q 0) (F 0) x) (tmult (m Q 1) (F 1) x)
      (tmult (m Q 2) (F 2) x)‖ₑ ≤ ENNReal.ofReal (C₁ * CT) * ENNReal.ofReal ((2 : ℝ) ^ Q.box.scale) * Pr := by
    intro Q hQ'
    have := hC P T CT hT Tr Q hQ' η hη (m Q) (fun k => (hcls Q hQ').2 k) F hFm hFb
    rw [hχ Q hQ']
    exact this
  unfold modelForm
  calc ‖∑ Q ∈ Tr, ∫ x, (χ Q x : ℂ) * T (tmult (m Q 0) (F 0) x) (tmult (m Q 1) (F 1) x) (tmult (m Q 2) (F 2) x)‖ₑ
      ≤ ∑ Q ∈ Tr, ‖∫ x, (χ Q x : ℂ) * T (tmult (m Q 0) (F 0) x) (tmult (m Q 1) (F 1) x)
          (tmult (m Q 2) (F 2) x)‖ₑ := enorm_sum_le _ _
    _ ≤ ∑ Q ∈ Tr, ENNReal.ofReal (C₁ * CT) * ENNReal.ofReal ((2 : ℝ) ^ Q.box.scale) * Pr :=
        Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (C₁ * CT) * (∑ Q ∈ Tr, ENNReal.ofReal ((2 : ℝ) ^ Q.box.scale)) * Pr := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ ENNReal.ofReal (C₁ * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) * Pr :=
        mul_le_mul' (mul_le_mul' le_rfl (sum_len_le_top htree hss)) le_rfl

end PrimeBHT.TimeFrequency.X2
