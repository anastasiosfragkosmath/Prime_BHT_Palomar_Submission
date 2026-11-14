module

public import PrimeBHT.TimeFrequency.X2.V16.Inside
public import PrimeBHT.TimeFrequency.X2.V16.Concrete

/-!
# X2, node V16: B12 (the assembly `V16Statement`)

`v16_of_energy`: `V16Statement` from the abstract B5 / V12 / V15 (outside, `EnergyTree`) and B5 / V12 / V15s (inside,
`EnergyTreeSS`) hypotheses on TWO energy families (REV3); the concrete theorem from the named node statements is
`v16_of_hyps_rev3` in `X2/V16/Final.lean`.

Proof (route check B12): B1 (`exceptionalMajor_facts`) gives the major subset `Ẽ = exceptionalMajor 48 E τ`, a function of
`(E, τ)` only, with `|E_τ| ≤ 2 |Ẽ|`; the finite collection splits `Ps = outsidePart ⊔ insidePart` (for
`Ω = exceptionalOmega 48 E τ`); B10 (`outside_le_of_energy`) and B11 (`inside_le_of_energy`) bound the two parts.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile
open Classical

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.V16

/-- `Ps = outsidePart ⊔ insidePart` at the level of the model form. -/
theorem modelForm_split {P : ℕ} [NeZero P] (T : Form P) (Ps : Finset TriTile) (Ω : Set ℝ)
    (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ) (F₁ F₂ F₃ : ℝ → ZMod P → ℂ) :
    modelForm T Ps χ m F₁ F₂ F₃ =
      modelForm T (outsidePart Ps Ω) χ m F₁ F₂ F₃ + modelForm T (insidePart Ps Ω) χ m F₁ F₂ F₃ := by
  unfold modelForm outsidePart insidePart
  rw [add_comm]
  exact (Finset.sum_filter_add_sum_filter_not Ps (fun R => R.I ⊆ Ω) _).symm

/-- **B12 (V16)**, generic in TWO energy families and interval families (REV3): `V16Statement` from the abstract B5, V12,
V15 for the OUTSIDE families `eO u 𝔭` (`IntsContain`; B10: tile and fat top energies; `EnergyStepG`: the localized count is
false for the top energy and not used by B10) and the abstract B5, V12, V15s for
the INSIDE families `eI u 𝔭` (`IntsScale`; B11: tile energies, single-scale layers), for `u > 1`, `V16Params u 𝔭`, with tail
orders `Mf u > 32 Rof(u) + 1`. -/
theorem v16_of_energy (eO eI : ℝ → Params → EnergyFamily) (intsO intsI : ℝ → Params → IntFamily)
    (Mf : ℝ → ℝ) (hMf : ∀ u, 1 < u → 32 * Rof u + 1 < Mf u)
    (hypO : ∀ u, 1 < u → ∀ 𝔭 : Params, V16Params u 𝔭 →
      IntsContain (intsO u 𝔭) ∧ EnergyMono (eO u 𝔭) ∧ EnergyTailBound (eO u 𝔭) (intsO u 𝔭) u 𝔭 (Mf u) ∧
        EnergyStepG (eO u 𝔭) u 𝔭 ∧ EnergyTree (eO u 𝔭) u 𝔭)
    (hypI : ∀ u, 1 < u → ∀ 𝔭 : Params, V16Params u 𝔭 →
      IntsScale (intsI u 𝔭) ∧ EnergyMono (eI u 𝔭) ∧ EnergyTailBound (eI u 𝔭) (intsI u 𝔭) u 𝔭 (Mf u) ∧
        EnergyStep (eI u 𝔭) u 𝔭 ∧ EnergyTreeSS (eI u 𝔭) u 𝔭) :
    V16Statement := by
  intro u hu 𝔭 h𝔭
  obtain ⟨hcont, hmonoO, htailO, hstepO, htreeO⟩ := hypO u hu 𝔭 h𝔭
  obtain ⟨hscale, hmonoI, htailI, hstepI, htreeI⟩ := hypI u hu 𝔭 h𝔭
  have hR4 : 4 ≤ Rof u := four_le_Rof hu
  have hM := hMf u hu
  obtain ⟨Co, hCo0, hCo⟩ := outside_le_of_energy hu 𝔭 (e := eO u 𝔭) (ints := intsO u 𝔭) (M := Mf u)
    (by linarith) hcont hmonoO htailO hstepO htreeO
  obtain ⟨Ci, hCi0, hCi⟩ := inside_le_of_energy hu 𝔭 (e := eI u 𝔭) (ints := intsI u 𝔭) (M := Mf u) hM
    hscale hmonoI htailI hstepI htreeI
  refine ⟨Co + Ci, by linarith, ?_⟩
  intro P _ T CT hT Qs hQ Ps hPs χ m hmd β hβ E hEm hEpos hEfin τ hEmax
  have hfacts := exceptionalMajor_facts hEm (fun i => (hEpos i).ne') (fun i => (hEfin i).ne)
    (le_refl (48 : ℝ)) τ
  obtain ⟨-, -, -, -, hmeas, hsub, hvol⟩ := hfacts
  refine ⟨exceptionalMajor 48 E τ, hmeas, hsub, hvol, ?_⟩
  intro h hhm hdom hdomτ
  have hH : IsHullData u E τ h := ⟨hEm, hEpos, hEfin, hEmax, hhm, hdom, hdomτ⟩
  have hCT : 0 ≤ CT := not_lt.1 fun hneg => not_bound_of_neg T (by linarith) hneg hT
  show ‖modelForm T Ps χ m (h 0) (h 1) (h 2)‖ ≤ (Co + Ci) * CT * ∏ i, (volume (E i)).toReal ^ β i
  rw [modelForm_split T Ps (exceptionalOmega 48 E τ)]
  refine (norm_add_le _ _).trans ?_
  have h1 := hCo P T CT hT Qs hQ Ps hPs χ m hmd β hβ E τ h hH
  have h2 := hCi P T CT hT Qs hQ Ps hPs χ m hmd β hβ E τ h hH
  calc _ ≤ Co * CT * ∏ i, (volume (E i)).toReal ^ β i + Ci * CT * ∏ i, (volume (E i)).toReal ^ β i :=
        add_le_add h1 h2
    _ = _ := by ring

end PrimeBHT.TimeFrequency.X2.V16
