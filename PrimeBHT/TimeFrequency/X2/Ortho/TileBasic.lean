module

public import PrimeBHT.TimeFrequency.X2.Ortho.TileBasicA
public import PrimeBHT.TimeFrequency.X2.Ortho.TileEng
public import PrimeBHT.TimeFrequency.X2.Ortho.Families

/-!
# X2, node V10: `OrthoTileBasic` from the dual vectors (ENNReal glue)

`TileDuals 𝔭`: for every finite set of tiles and bounded measurable `F` there are `a_R ≥ 0` and dual vectors `z_R`
satisfying (Z1)-(Z3) (`TileDualData`) with `ĉ_R = ℓ_R^{-1/2} a_R` a factor-`2` near-optimizer of the single-tile
energy: `tileEng R ≤ 2 ofReal ĉ_R`, `ofReal ĉ_R ≤ tileEng R`.
`tile_basic_of_duals`: `TileDuals 𝔭` gives the statement of `OrthoTileBasic 𝔭`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-- The existence of the dual vectors (Layer B: Fourier analysis of the tile operators). -/
def TileDuals (𝔭 : Params) : Prop :=
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (P : ℕ) [NeZero P] (Qs : Set Box), IsRankOne 𝔭.J Qs → ∀ (k : Fin 3)
    (𝒮 : Finset TriTile), (∀ R ∈ 𝒮, R.box ∈ Qs) → ∀ (F : ℝ → ZMod P → ℂ) (B : ℝ), Measurable F →
      (∀ x, yNorm 2 (F x) ≤ B) →
        ∃ (a : TriTile → ℝ) (z : TriTile → ℝ → ZMod P → ℂ), TileDualData k F 𝒮 C₀ a z ∧
          ∀ R ∈ 𝒮, tileEng 𝔭 k F R ≤ 2 * ENNReal.ofReal (chat a R) ∧
            ENNReal.ofReal (chat a R) ≤ tileEng 𝔭 k F R

theorem list_sum_ne_top {ι : Type*} (l : List ι) (f : ι → ℝ≥0∞) (hf : ∀ x ∈ l, f x ≠ ⊤) :
    (l.map f).sum ≠ ⊤ := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons]
    exact ENNReal.add_ne_top.2 ⟨hf x (by simp), ih (fun y hy => hf y (by simp [hy]))⟩

theorem toReal_list_sum {ι : Type*} (l : List ι) (f : ι → ℝ≥0∞) (hf : ∀ x ∈ l, f x ≠ ⊤) :
    (l.map f).sum.toReal = (l.map fun x => (f x).toReal).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
      ENNReal.toReal_add (hf x (by simp)) (list_sum_ne_top l f (fun y hy => hf y (by simp [hy]))),
      ih (fun y hy => hf y (by simp [hy]))]

theorem integrable_of_mixedPow_ne_top {P : ℕ} [NeZero P] {F : ℝ → ZMod P → ℂ} (hF : Measurable F)
    (h : mixedPow 2 2 F ≠ ⊤) : Integrable (fun x => yNorm 2 (F x) ^ 2) := by
  have hm : Measurable fun x => yNorm 2 (F x) ^ 2 := ((measurable_yNorm_fun 2).comp hF).pow_const 2
  unfold mixedPow at h
  simp_rw [Real.rpow_two] at h
  exact (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Eventually.of_forall fun x => by positivity)).1 h

theorem mixedPow_eq_ofReal {P : ℕ} [NeZero P] {F : ℝ → ZMod P → ℂ}
    (h : Integrable (fun x => yNorm 2 (F x) ^ 2)) :
    mixedPow 2 2 F = ENNReal.ofReal (∫ x, yNorm 2 (F x) ^ 2) := by
  unfold mixedPow
  simp_rw [Real.rpow_two]
  rw [ofReal_integral_eq_lintegral_ofReal h (Eventually.of_forall fun x => by positivity)]

end PrimeBHT.TimeFrequency.X2
