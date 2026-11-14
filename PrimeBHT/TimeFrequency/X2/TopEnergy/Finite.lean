module

public import PrimeBHT.TimeFrequency.X2.TopEnergy.Select

/-!
# X2, node V12-top (TB-0): finiteness of the admissible top data below a scale

For a finite collection `C` and tree hulls `H` that are bounded on the boxes of `C`, the set of grid top data
`(W, ξ)` with `IsTopDatumH H ρ J C W ξ` and `|W| = 2^{W.1} ≤ L₀` is finite (`finite_topData`): `W.1` lies between the scale
of a witness tile and `log₂ L₀`, the index of `W` is determined by the witness tile and `W.1`, and the grid frequency
`ξ ∈ (2^{-W.1}/8) ℤ` lies in the bounded hull.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

theorem exists_zpow_ge (L₀ : ℝ) : ∃ w : ℤ, L₀ ≤ (2 : ℝ) ^ w := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt L₀ (by norm_num : (1 : ℝ) < 2)
  exact ⟨(n : ℤ), by rw [zpow_natCast]; exact hn.le⟩

theorem finite_topData {H : Box → Set ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) (J : ℕ) (C : Finset TriTile) {M : ℝ}
    (hM : 0 ≤ M) (hH : ∀ R ∈ C, ∀ x ∈ H R.box, |x| ≤ M) (L₀ : ℝ) :
    {p : (ℤ × ℤ) × ℝ | IsTopDatumH H ρ J C p.1 p.2 ∧ (2 : ℝ) ^ p.1.1 ≤ L₀}.Finite := by
  obtain ⟨w₀, hw₀⟩ := exists_zpow_ge L₀
  set N : ℕ := ⌈8 * M * (2 : ℝ) ^ w₀⌉₊ with hN
  have hcover : {p : (ℤ × ℤ) × ℝ | IsTopDatumH H ρ J C p.1 p.2 ∧ (2 : ℝ) ^ p.1.1 ≤ L₀} ⊆
      ⋃ R ∈ (C : Set TriTile), ⋃ w ∈ Icc R.box.scale w₀, ⋃ z ∈ Icc (-(N : ℤ)) (N : ℤ),
        {((w, ⌊(2 : ℝ) ^ R.box.scale * R.pos / (2 : ℝ) ^ w⌋), (z : ℝ) * (gridMesh * (2 : ℝ) ^ (-w)))} := by
    intro p hp
    obtain ⟨hd, hL⟩ := hp
    obtain ⟨W, ξ'⟩ := p
    obtain ⟨⟨z, hz⟩, R, hR, h1, h2, h3⟩ := hd
    simp only at hz h1 h2 h3 hL
    have ha : (0 : ℝ) < (2 : ℝ) ^ (-W.1) := zpow_pos (by norm_num) _
    have hlow : R.box.scale ≤ W.1 := scale_le_of_dyadicInt_subset h1
    have hup : W.1 ≤ w₀ := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 (hL.trans hw₀)
    -- the index of `W`
    have hx₀ : (2 : ℝ) ^ R.box.scale * R.pos ∈ dyadicInt W.1 W.2 := by
      refine h1 ?_
      show (2 : ℝ) ^ R.box.scale * R.pos ∈ dyadicInt R.box.scale R.pos
      exact ⟨le_rfl, by have := zpow_pos (by norm_num : (0 : ℝ) < 2) R.box.scale; nlinarith⟩
    have hW2 : W.2 = ⌊(2 : ℝ) ^ R.box.scale * R.pos / (2 : ℝ) ^ W.1⌋ := by
      have hp : (0 : ℝ) < (2 : ℝ) ^ W.1 := zpow_pos (by norm_num) _
      obtain ⟨hx1, hx2⟩ := hx₀
      symm
      rw [Int.floor_eq_iff]
      constructor
      · rw [le_div_iff₀ hp]; linarith
      · rw [div_lt_iff₀ hp]; linarith
    -- the bound on `z`
    have hξ : |ξ'| ≤ M := by
      have : ξ' ∈ Icc (ξ' - ρ * (2 : ℝ) ^ (-W.1)) (ξ' + ρ * (2 : ℝ) ^ (-W.1)) :=
        ⟨by nlinarith, by nlinarith⟩
      exact hH R hR ξ' (h3 this)
    have hzN : |(z : ℝ)| ≤ N := by
      have hg : (0 : ℝ) < gridMesh * (2 : ℝ) ^ (-W.1) := by unfold gridMesh; positivity
      have e1 : |ξ'| = |(z : ℝ)| * (gridMesh * (2 : ℝ) ^ (-W.1)) := by
        rw [hz, abs_mul, abs_of_pos hg]
      have e2 : (2 : ℝ) ^ (-W.1) = ((2 : ℝ) ^ W.1)⁻¹ := zpow_neg _ _
      have hpos : (0 : ℝ) < (2 : ℝ) ^ W.1 := zpow_pos (by norm_num) _
      have hmono : (2 : ℝ) ^ W.1 ≤ (2 : ℝ) ^ w₀ := zpow_le_zpow_right₀ (by norm_num) hup
      have h4 : |(z : ℝ)| = |ξ'| * (8 * (2 : ℝ) ^ W.1) := by
        rw [e1, e2]; unfold gridMesh; field_simp
      rw [h4]
      calc |ξ'| * (8 * (2 : ℝ) ^ W.1) ≤ M * (8 * (2 : ℝ) ^ w₀) :=
            mul_le_mul hξ (by nlinarith) (by positivity) hM
        _ = 8 * M * (2 : ℝ) ^ w₀ := by ring
        _ ≤ N := Nat.le_ceil _
    have hzN' : -(N : ℤ) ≤ z ∧ z ≤ N := by
      have := abs_le.1 hzN
      constructor
      · have : (-(N : ℝ)) ≤ (z : ℝ) := this.1
        exact_mod_cast this
      · exact_mod_cast this.2
    simp only [Set.mem_iUnion, Finset.mem_coe, Set.mem_singleton_iff]
    refine ⟨R, hR, W.1, ⟨hlow, hup⟩, z, hzN', ?_⟩
    rw [Prod.ext_iff]
    refine ⟨Prod.ext rfl hW2, hz⟩
  refine Set.Finite.subset ?_ hcover
  exact (C.finite_toSet).biUnion fun R _ => (Set.finite_Icc _ _).biUnion fun w _ =>
    (Set.finite_Icc _ _).biUnion fun z _ => Set.finite_singleton _

end PrimeBHT.TimeFrequency.X2
