module

public import PrimeBHT.TimeFrequency.X2.Psp.OverlapBdd
public import PrimeBHT.TimeFrequency.X2.Psp.TreeHardFinal

/-!
# X2, V15 (final assembly): `OverlapPspLean` from the concrete O2, and `treeLemmaRev2_of_O2`

* `OvBound.mono_C`: `OvBound` is monotone in the constant (for a nonnegative factor `a`);
* `overlapPspLean_of_O2`: `OverlapO2Ovg 𝔭 → OverlapPspLean 𝔭` (for `𝔭`, `𝔭.tree` admissible): the function `G = ovG 𝔭.J TA t k s₀ F`
  with `s₀` the scale of a tile of `TA` (rank-one gives `J ∣ scale - s₀`); (O1) is `ovG_O1` at the class `𝔭.tree` (`q = 2`, `s = 2`),
  boundedness is `ovG_bdd`, and (O2) is the hypothesis (constant `max (C₂, C₁)`);
* `treeLemmaRev2_of_O2`: `TreeLemmaStatementRev2` from `OverlapO2Ovg` for all admissible `𝔭` (the tree profile is `ProfileOK 𝔭`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

theorem OvBound.mono_C {P : ℕ} [NeZero P] {s q C C' a : ℝ} {E : ℝ≥0∞} {σ v : ℤ} {U : ℝ → ZMod P → ℂ} (ha : 0 ≤ a)
    (hC : C ≤ C') (h : OvBound s q C a E σ v U) : OvBound s q C' a E σ v U := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x hx => (h1 x hx).trans
    (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC ha)) le_rfl),
    h2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC ha)
    (Real.rpow_nonneg (zpow_two_pos σ).le _)

/-- **`OverlapPspLean` from the concrete O2** (the only open input of the overlapping projection). -/
theorem overlapPspLean_of_O2 {𝔭 : Params} (h𝔭 : 𝔭.Admissible) (h𝔭t : 𝔭.tree.Admissible) (hO2 : OverlapO2Ovg 𝔭) :
    OverlapPspLean 𝔭 := by
  intro hND
  obtain ⟨C₂, hC₂, hO2⟩ := hO2 hND
  set C₁ : ℝ := max (oaConst 𝔭.tree 2) 0 + 16 * (coefConst 𝔭.tree 2 + 1) + 1 with hC₁
  refine ⟨max C₂ (max C₁ 0), le_max_of_le_left hC₂, ?_⟩
  intro P _ Qs Tr TA t k η χ m hk _ _ hη hη' hrank hsub hbox hgood hov hlac F hF hFb
  obtain ⟨η', hη'⟩ := hη'
  have hs₀ : ∃ s₀ : ℤ, ∀ R ∈ TA, (𝔭.J : ℤ) ∣ R.box.scale - s₀ := by
    rcases TA.eq_empty_or_nonempty with rfl | ⟨R₀, hR₀⟩
    · exact ⟨0, by simp⟩
    · exact ⟨R₀.box.scale, fun R hR =>
        hrank.1 R.box (hbox R (hsub hR)) R₀.box (hbox R₀ (hsub hR₀))⟩
  obtain ⟨s₀, hs₀⟩ := hs₀
  have hJ2 : 2 ≤ 𝔭.tree.J := le_trans (by norm_num [jFloor]) h𝔭t.1
  have hs₀' : ∀ R ∈ TA, (𝔭.tree.J : ℤ) ∣ R.box.scale - s₀ := by
    simpa using hs₀
  obtain ⟨hmeas, hbound, hsupp⟩ := ovG_O1 h𝔭t hJ2 hη' (s := 2) (q := 2) (by norm_num) (by norm_num) hF hFb hsub hov hs₀'
  have hGeq : ovG 𝔭.tree.J TA t k s₀ F = ovG 𝔭.J TA t k s₀ F := by simp
  rw [hGeq] at hmeas hbound hsupp
  refine ⟨ovG 𝔭.J TA t k s₀ F, hmeas, ovG_bdd _ _ _ _ _ hFb, ⟨fun x => ?_, hsupp⟩, ?_⟩
  · exact (hbound x).trans (mul_le_mul'
      (ENNReal.ofReal_le_ofReal ((le_max_left C₁ 0).trans (le_max_right _ _))) le_rfl)
  · intro σ R₀ hR₀ v S hS1 hS2
    exact OvBound.mono_C (ovFactor_nonneg 𝔭.J S (bdryEnds TA t.1) σ v) (le_max_left _ _)
      (hO2 P Qs Tr TA t k η χ m s₀ hk h𝔭 h𝔭t hη ⟨η', hη'⟩ hrank hsub hbox hgood hov hlac hs₀ F hF hFb σ R₀ hR₀ v S hS1 hS2)

/-- **V15 from the concrete O2**: `TreeLemmaStatementRev2` from `OverlapO2Ovg` (for every admissible class).  The second profile `η'`
of the class `𝔭.tree` is `ProfileOK 𝔭`, carried by the parameters. -/
theorem treeLemmaRev2_of_O2
    (hO2 : ∀ 𝔭 : Params, 𝔭.Admissible → 𝔭.tree.Admissible → OverlapO2Ovg 𝔭) : TreeLemmaStatementRev2 :=
  treeLemmaRev2_of_overlapPspLean fun 𝔭 h h' => overlapPspLean_of_O2 h h' (hO2 𝔭 h h')

end PrimeBHT.TimeFrequency.X2
