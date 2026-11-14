module

public import PrimeBHT.TimeFrequency.X2.Psp.OverlapLean
public import PrimeBHT.TimeFrequency.X2.ModelOpTools

/-!
# X2, V13/V15: boundedness of the concrete overlapping projection `ovG`

`OverlapPspLean` asks for a G that is bounded in `L^∞(L²(Y))` (a qualitative bound, independent of `engTop`, which may be `∞` for a
bounded `F` that is not in `L^q`).  For the concrete `ovG = Π̃F - Σ cφ`:

* `goodKernel_lowSym`: `GoodKernel (lowSym θ σ)` (integrable, continuous, bounded kernel);
* `overlapPi_bdd`: `Π̃F` is bounded (finite sum over the lattice scales of `T_σ F`, `‖T_σ F‖_∞ ≤ ‖𝓕⁻ lowSym‖₁ ‖F‖_∞`);
* `overlapBumps_bdd`: the bump part is bounded for ANY coefficients (finite index set, at most one bump nonzero at a point:
  `yNorm_leftBumps_le`; `yNorm` is a finite real number);
* `ovG_bdd`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

theorem goodKernel_lowSym (θ : ℝ) (σ : ℤ) : GoodKernel (lowSym θ σ) := by
  refine ⟨integrable_fourierInv_of_smooth (contDiff_lowSym θ σ) (c := θ) (r := 17 / 4 * (2 : ℝ) ^ (-σ))
    (fun ξ hξ => lowSym_eq_zero hξ.le), continuous_fourierInv_lowSym θ σ, ∫ ξ, ‖lowSym θ σ ξ‖, fun w => ?_⟩
  rw [Real.fourierInv_eq_fourier_neg]
  exact Real.norm_fourier_le_integral_norm _ _

section Bdd

variable {P : ℕ} [NeZero P]

/-- `T_σ F` is bounded in `yNorm 2` for a bounded `F` (`GoodKernel`, `norm_tmult_le`). -/
theorem yNorm_two_tmult_lowSym_bdd (θ : ℝ) (σ : ℤ) {F : ℝ → ZMod P → ℂ} {B : ℝ} (hB : ∀ x, yNorm 2 (F x) ≤ B) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x, yNorm 2 (tmult (lowSym θ σ) F x) ≤ A := by
  have hB0 : 0 ≤ B := (yNorm_nonneg' 2 (F 0)).trans (hB 0)
  set M : ℝ := (P : ℝ) ^ (2 : ℝ)⁻¹ * B with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hcoord : ∀ z y, ‖F z y‖ ≤ M := fun z y =>
    (norm_apply_le_rpow_mul_yNorm (by norm_num) (F z) y).trans
      (mul_le_mul_of_nonneg_left (hB z) (by positivity))
  have hK := goodKernel_lowSym θ σ
  refine ⟨kerNorm (lowSym θ σ) * M, mul_nonneg (kerNorm_nonneg _) hM0, fun x => ?_⟩
  exact yNorm_le_of_forall_le (by norm_num) (mul_nonneg (kerNorm_nonneg _) hM0)
    (fun y => norm_tmult_le hK hcoord x y)

/-- `Π̃F` is bounded. -/
theorem overlapPi_bdd (TA : Finset TriTile) (W : ℤ × ℤ) (L : Finset ℤ) (θ : ℝ) {F : ℝ → ZMod P → ℂ}
    (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) : ∃ B : ℝ, ∀ y, yNorm 2 (overlapPi TA W L θ F y) ≤ B := by
  obtain ⟨B, hB⟩ := hFb
  have hex : ∀ σ : ℤ, ∃ A : ℝ, 0 ≤ A ∧ ∀ x, yNorm 2 (tmult (lowSym θ σ) F x) ≤ A :=
    fun σ => yNorm_two_tmult_lowSym_bdd θ σ hB
  choose A hA0 hA using hex
  refine ⟨∑ σ ∈ L, A σ, fun y => ?_⟩
  unfold overlapPi
  refine (CZ.yNorm_sum_le (by norm_num) L _).trans (Finset.sum_le_sum fun σ _ => ?_)
  by_cases hy : y ∈ overlapA TA W L σ
  · rw [Set.indicator_of_mem hy]
    exact hA σ y
  · rw [Set.indicator_of_notMem hy, yNorm_zero_ov (by norm_num)]
    exact hA0 σ

theorem le_sum_sigma_leftEnds (TA : Finset TriTile) (W : ℤ × ℤ) (L : Finset ℤ) (cL : ℤ → ℝ → ZMod P → ℂ) :
    ∀ σ ∈ L, ∀ x ∈ leftEnds TA W σ,
      yNorm 2 (cL σ x) ≤ ∑ p ∈ L.sigma (fun σ => leftEnds TA W σ), yNorm 2 (cL p.1 p.2) := by
  intro σ hσ x hx
  have hmem : (⟨σ, x⟩ : Σ _ : ℤ, ℝ) ∈ L.sigma (fun σ => leftEnds TA W σ) := Finset.mem_sigma.2 ⟨hσ, hx⟩
  set g : (Σ _ : ℤ, ℝ) → ℝ := fun p => yNorm 2 (cL p.1 p.2) with hg
  have h0 : ∀ p ∈ L.sigma (fun σ => leftEnds TA W σ), 0 ≤ g p := fun p _ => yNorm_nonneg' 2 _
  have h1 : g ⟨σ, x⟩ ≤ ∑ p ∈ L.sigma (fun σ => leftEnds TA W σ), g p := Finset.single_le_sum h0 hmem
  exact h1

theorem le_sum_sigma_rightEnds (TA : Finset TriTile) (W : ℤ × ℤ) (L : Finset ℤ) (cR : ℤ → ℝ → ZMod P → ℂ) :
    ∀ σ ∈ L, ∀ x ∈ rightEnds TA W σ,
      yNorm 2 (cR σ x) ≤ ∑ p ∈ L.sigma (fun σ => rightEnds TA W σ), yNorm 2 (cR p.1 p.2) := by
  intro σ hσ x hx
  have hmem : (⟨σ, x⟩ : Σ _ : ℤ, ℝ) ∈ L.sigma (fun σ => rightEnds TA W σ) := Finset.mem_sigma.2 ⟨hσ, hx⟩
  set g : (Σ _ : ℤ, ℝ) → ℝ := fun p => yNorm 2 (cR p.1 p.2) with hg
  have h0 : ∀ p ∈ L.sigma (fun σ => rightEnds TA W σ), 0 ≤ g p := fun p _ => yNorm_nonneg' 2 _
  have h1 : g ⟨σ, x⟩ ≤ ∑ p ∈ L.sigma (fun σ => rightEnds TA W σ), g p := Finset.single_le_sum h0 hmem
  exact h1

/-- The bump part is bounded for ANY coefficient families. -/
theorem overlapBumps_bdd (TA : Finset TriTile) (W : ℤ × ℤ) (L : Finset ℤ) (θ : ℝ) (cL cR : ℤ → ℝ → ZMod P → ℂ) :
    ∃ B : ℝ, ∀ y, yNorm 2 (overlapBumps TA W L θ cL cR y) ≤ B := by
  have hBL0 : 0 ≤ ∑ p ∈ L.sigma (fun σ => leftEnds TA W σ), yNorm 2 (cL p.1 p.2) :=
    Finset.sum_nonneg fun p _ => yNorm_nonneg' 2 _
  have hBR0 : 0 ≤ ∑ p ∈ L.sigma (fun σ => rightEnds TA W σ), yNorm 2 (cR p.1 p.2) :=
    Finset.sum_nonneg fun p _ => yNorm_nonneg' 2 _
  refine ⟨8 * (∑ p ∈ L.sigma (fun σ => leftEnds TA W σ), yNorm 2 (cL p.1 p.2)) +
    8 * (∑ p ∈ L.sigma (fun σ => rightEnds TA W σ), yNorm 2 (cR p.1 p.2)), fun y => ?_⟩
  have h1 := yNorm_leftBumps_le (TA := TA) (W := W) (L := L) (cL := cL) (s := 2) (by norm_num) hBL0
    (le_sum_sigma_leftEnds TA W L cL) θ y
  have h2 := yNorm_rightBumps_le (TA := TA) (W := W) (L := L) (cR := cR) (s := 2) (by norm_num) hBR0
    (le_sum_sigma_rightEnds TA W L cR) θ y
  have h3 := CZ.yNorm_add_le (P := P) (s := 2) (by norm_num)
    (∑ p ∈ L.sigma (fun σ => leftEnds TA W σ), (ovPhase θ y * ((leftPhi p.1 p.2 y : ℝ) : ℂ)) • cL p.1 p.2)
    (∑ p ∈ L.sigma (fun σ => rightEnds TA W σ), (ovPhase θ y * ((rightPhi p.1 p.2 y : ℝ) : ℂ)) • cR p.1 p.2)
  exact h3.trans (add_le_add h1 h2)

/-- `G = Π̃F - Σ cφ` is bounded, for ANY coefficients. -/
theorem overlapG_bdd (TA : Finset TriTile) (W : ℤ × ℤ) (L : Finset ℤ) (θ : ℝ) {F : ℝ → ZMod P → ℂ}
    (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) (cL cR : ℤ → ℝ → ZMod P → ℂ) :
    ∃ B : ℝ, ∀ y, yNorm 2 (overlapG TA W L θ F cL cR y) ≤ B := by
  obtain ⟨B₁, h₁⟩ := overlapPi_bdd TA W L θ hFb
  obtain ⟨B₂, h₂⟩ := overlapBumps_bdd TA W L θ cL cR
  refine ⟨B₁ + B₂, fun y => ?_⟩
  unfold overlapG
  exact (yNorm_sub_ov (by norm_num) _ _).trans (add_le_add (h₁ y) (h₂ y))

/-- **`ovG` is bounded**. -/
theorem ovG_bdd (J : ℕ) (TA : Finset TriTile) (t : Top) (k : Fin 3) (s₀ : ℤ) {F : ℝ → ZMod P → ℂ}
    (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) : ∃ B : ℝ, ∀ y, yNorm 2 (ovG J TA t k s₀ F y) ≤ B :=
  overlapG_bdd _ _ _ _ hFb _ _

end Bdd

end PrimeBHT.TimeFrequency.X2
