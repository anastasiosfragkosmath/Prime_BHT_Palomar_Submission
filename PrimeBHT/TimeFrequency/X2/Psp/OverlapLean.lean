module

public import PrimeBHT.TimeFrequency.X2.Psp.OverlapCoef
public import PrimeBHT.TimeFrequency.X2.Psp.OverlapStmt

/-!
# X2, V13/V15 interface: `OverlapPspLean` and the concrete O2 target

This file is the interface between the V15 glue (`Psp/TreeHardFinal.lean`: `treeLemmaRev2_of_overlapPspLean`) and the overlapping projection:

**Margin `hND : 𝔭.N / 8 + 3 ≤ 𝔭.D`** (part of `ProfileOK`): both statements are conditional on it (`hND → ∃ C, …`): the kernel decay of the
multipliers (`D` derivatives) must beat the polynomial growth `N/8` of the low-pass operators off `Ẽ_σ` (`docs/audits/X2-O2-coordination.md` (C3)).
The constant `C` may be taken `≥ 1` (for `E = ⊤` the sup conjunct needs `C a > 0`).

* `OverlapPspLean 𝔭`: what the hard parts of the tree lemma consume (O1 with boundedness, O2; no O3), for a HILBERT slot `k ≠ 2` at
  `(s, q) = (2, 2)`, `K₀ = 2`;
* `OverlapO2Ovg 𝔭`: (O2) for the CONCRETE function `ovG` of `Psp/OverlapCoef.lean` (the construction `G = Π̃F - Σ c φ`), the statement to be proved
  (MTT2 §8, `error-1`, decomposition (d1)-(d6));
* `bdryEnds_window`: the boundary sets `∂Ẽ_σ` of a part live in the window of lattice scales `[-max|scale| - 1, top scale]` (this is the
  finite set `S` of `μ_σ`).
O1 for `ovG` is `ovG_O1`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform Real ContDiff
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-- **The overlapping projection, lean form (NOT PROVED; the exact remaining input of V15).**  For a part `TA` of a good tree whose Hilbert
slot `k ≠ 2` is overlapping and `F` bounded measurable, there is a measurable bounded `G` with `E = engTop 𝔭.tree 2 k F Tr 2`:
* (O1) `‖G(x)‖_{L²(Y)} ≤ C E` and `G = 0` off `3 I_t`;
* (O2) for every scale `σ` of the lattice, `R₀` of scale `σ`, `I₀ = dyadicInt σ v`, and every finite set `S` of lattice scales containing all `σ'`
  with `∂Ẽ_{σ'} ≠ ∅`: `χ̃_σ T_{m_σ k}(F - G)` obeys `OvBound 2 2` with `a = |I₀|^{-1} ∫ w_{I₀} μ_σ` (`K₀ = 2`). -/
def OverlapPspLean (𝔭 : Params) : Prop :=
  𝔭.N / 8 + 3 ≤ 𝔭.D → ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (Qs : Set Box) (Tr TA : Finset TriTile) (t : Top) (k : Fin 3) (η : ℝ → ℝ)
    (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ),
    k ≠ 2 → 𝔭.Admissible → 𝔭.tree.Admissible → IsEtaCut 𝔭 η → (∃ η' : ℝ → ℝ, IsEtaCut 𝔭.tree η') → IsRankOne 𝔭.J Qs →
    TA ⊆ Tr → (∀ R ∈ Tr, R.box ∈ Qs) → IsGoodTree TA t → (∀ R ∈ TA, IsOvSlot t k R.box) → LacData 𝔭 TA k η χ m →
    ∀ F : ℝ → ZMod P → ℂ, Measurable F → (∃ B, ∀ x, yNorm 2 (F x) ≤ B) →
      ∃ G : ℝ → ZMod P → ℂ, Measurable G ∧ (∃ B, ∀ x, yNorm 2 (G x) ≤ B) ∧
        ((∀ x, ENNReal.ofReal (yNorm 2 (G x)) ≤ ENNReal.ofReal C * engTop 𝔭.tree 2 k F Tr 2) ∧
          ∀ x, x ∉ dilate 3 (dyadicInt t.1.1 t.1.2) → G x = 0) ∧
        (∀ (σ : ℤ) (R₀ : TriTile), R₀ ∈ layer' TA σ → ∀ (v : ℤ) (S : Finset ℤ),
          (∀ σ' ∈ S, (𝔭.J : ℤ) ∣ σ' - σ) →
          (∀ σ' : ℤ, (𝔭.J : ℤ) ∣ σ' - σ → (bdryEnds TA t.1 σ').Nonempty → σ' ∈ S) →
          OvBound 2 2 C (((2 : ℝ) ^ σ)⁻¹ * ∫ y, ovWeight 2 σ v y * muW 𝔭.J S (bdryEnds TA t.1) σ y)
            (engTop 𝔭.tree 2 k F Tr 2) σ v (fun x => (layerCut η TA σ x : ℂ) • tmult (m R₀ k) (F - G) x))

/-- The boundary sets `∂Ẽ_{σ'}` of a part are empty outside the window `[-max |scale| - 1, top scale]`. -/
theorem bdryEnds_window {TA : Finset TriTile} {t : Top} {σ' : ℤ} (h : (bdryEnds TA t.1 σ').Nonempty) :
    -((TA.sup (fun R => R.box.scale.natAbs) : ℕ) : ℤ) - 1 ≤ σ' ∧ σ' ≤ t.1.1 := by
  obtain ⟨z, hz⟩ := h
  have hk : (eTilKeys TA t.1 σ').Nonempty := by
    rcases Finset.mem_union.1 hz with h1 | h1
    · obtain ⟨v, hv, -⟩ := mem_leftEndsOf.1 h1
      exact ⟨v, mem_eTilKeysF.1 hv⟩
    · obtain ⟨v, hv, -⟩ := mem_rightEndsOf.1 h1
      exact ⟨v, mem_eTilKeysF.1 hv⟩
  obtain ⟨v, hv⟩ := hk
  obtain ⟨h1, R, hR, h2⟩ := mem_eTilKeys.1 hv
  have h3 := scale_le_of_dyadicInt_subset h1
  have h4 : R.box.scale ≤ σ' + 1 := scale_le_of_subset_dilate_three (by unfold TriTile.I at h2; exact h2)
  have h5 : (R.box.scale.natAbs : ℕ) ≤ TA.sup (fun R => R.box.scale.natAbs) := Finset.le_sup (f := fun R : TriTile => R.box.scale.natAbs) hR
  refine ⟨?_, h3⟩
  have : -R.box.scale ≤ ((TA.sup (fun R => R.box.scale.natAbs) : ℕ) : ℤ) := by
    have h6 : -R.box.scale ≤ (R.box.scale.natAbs : ℤ) := by omega
    exact h6.trans (by exact_mod_cast h5)
  omega


/-- **(O2) for the concrete `G = ovG`** (NOT PROVED; the statement for the V13 O2 task).  For every lattice scale `σ` (`≡ s₀ mod J`), tile `R₀`
of scale `σ`, `σ`-interval `I₀ = dyadicInt σ v` and finite set `S` of lattice scales containing all `σ'` with `∂Ẽ_{σ'} ≠ ∅`:
`χ̃_σ T_{m_σ k}(F - ovG F)` obeys `OvBound 2 2` with `a = |I₀|^{-1} ∫ w_{I₀} μ_σ`, `w_{I₀}(y) = ⟨(y - c_{I₀})/|I₀|⟩^{-2}`,
`μ_σ = muW` (MTT2 (51)), `E = engTop 𝔭.tree 2 k F Tr 2`. -/
def OverlapO2Ovg (𝔭 : Params) : Prop :=
  𝔭.N / 8 + 3 ≤ 𝔭.D → ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (Qs : Set Box) (Tr TA : Finset TriTile) (t : Top) (k : Fin 3) (η : ℝ → ℝ)
    (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ) (s₀ : ℤ),
    k ≠ 2 → 𝔭.Admissible → 𝔭.tree.Admissible → IsEtaCut 𝔭 η → (∃ η' : ℝ → ℝ, IsEtaCut 𝔭.tree η') → IsRankOne 𝔭.J Qs →
    TA ⊆ Tr → (∀ R ∈ Tr, R.box ∈ Qs) → IsGoodTree TA t → (∀ R ∈ TA, IsOvSlot t k R.box) → LacData 𝔭 TA k η χ m →
    (∀ R ∈ TA, (𝔭.J : ℤ) ∣ R.box.scale - s₀) →
    ∀ F : ℝ → ZMod P → ℂ, Measurable F → (∃ B, ∀ x, yNorm 2 (F x) ≤ B) →
      ∀ (σ : ℤ) (R₀ : TriTile), R₀ ∈ layer' TA σ → ∀ (v : ℤ) (S : Finset ℤ),
        (∀ σ' ∈ S, (𝔭.J : ℤ) ∣ σ' - σ) →
        (∀ σ' : ℤ, (𝔭.J : ℤ) ∣ σ' - σ → (bdryEnds TA t.1 σ').Nonempty → σ' ∈ S) →
        OvBound 2 2 C (((2 : ℝ) ^ σ)⁻¹ * ∫ y, ovWeight 2 σ v y * muW 𝔭.J S (bdryEnds TA t.1) σ y)
          (engTop 𝔭.tree 2 k F Tr 2) σ v
          (fun x => (layerCut η TA σ x : ℂ) • tmult (m R₀ k) (F - ovG 𝔭.J TA t k s₀ F) x)

end PrimeBHT.TimeFrequency.X2
