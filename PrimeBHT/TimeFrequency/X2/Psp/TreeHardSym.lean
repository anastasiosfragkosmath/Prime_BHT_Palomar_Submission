module

public import PrimeBHT.TimeFrequency.X2.Psp.TreeHardMod

/-!
# X2, V15 (assembly), step 10: the V14 symbol classes

With the anchor `A = 2^{-s₀}/8` and `σ_j = s₀ - J j` (the scale of the index `j`), `A 2^{J j} = 2^{-σ_j}/8`:

* `isLPSymbol_lac`: `Λ⁻¹ lacSym 0 σ_j` is an `IsLPSymbol` (support `[2^{-σ}/8, 2^{-σ} 2^{2J}/8] ⊇ supp lacProfile`), `J ≥ 16`;
* `isLowSymbol_mult`: `𝔭.C⁻¹ m(· + θ)` is an `IsLowSymbol` for `m ∈ M_ω(𝔭)` at scale `σ_j` with `|c - θ| ≤ (13/8) 2^{-σ}` (support
  `|ξ| ≤ 3 · 2^{-σ} ≤ 2^{-σ} 2^{J/2}/8`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform Real ContDiff
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

theorem hasCompactSupport_lacProfileC : HasCompactSupport (fun u : ℝ => ((lacProfile u : ℝ) : ℂ)) :=
  hasCompactSupport_of_far (c := 0) (r := lacHi0) (fun u hu => by
    rw [sub_zero] at hu
    rw [lacProfile_eq_zero_of_ge hu.le, Complex.ofReal_zero])

theorem exists_lacProfile_deriv_bound (D : ℕ) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∀ a ≤ D, ∀ u : ℝ, ‖iteratedDeriv a (fun u : ℝ => ((lacProfile u : ℝ) : ℂ)) u‖ ≤ Λ := by
  have hs : ContDiff ℝ ∞ (fun u : ℝ => ((lacProfile u : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_lacProfile
  obtain ⟨C, hC0, hC⟩ := hasCompactSupport_lacProfileC.exists_bound_iteratedFDeriv hs D
  refine ⟨max 1 C, le_max_left _ _, fun a ha u => ?_⟩
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact (hC a ha u).trans (le_max_right _ _)

theorem norm_iteratedDeriv_lacSym0_le {D : ℕ} {Λ : ℝ}
    (hΛ : ∀ a ≤ D, ∀ u : ℝ, ‖iteratedDeriv a (fun u : ℝ => ((lacProfile u : ℝ) : ℂ)) u‖ ≤ Λ)
    (σ : ℤ) {a : ℕ} (ha : a ≤ D) (ξ : ℝ) :
    ‖iteratedDeriv a (lacSym 0 σ) ξ‖ ≤ ((2 : ℝ) ^ σ) ^ a * Λ := by
  have hf : ContDiff ℝ a (fun u : ℝ => ((lacProfile u : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp contDiff_lacProfile).of_le (by exact_mod_cast le_top)
  have e : lacSym 0 σ = fun ξ => (fun u : ℝ => ((lacProfile u : ℝ) : ℂ)) ((2 : ℝ) ^ σ * ξ) := by
    funext ξ; unfold lacSym; rw [sub_zero, mul_comm]
  have h2 := congrFun (iteratedDeriv_comp_const_smul (n := a) (f := fun u : ℝ => ((lacProfile u : ℝ) : ℂ)) hf
    ((2 : ℝ) ^ σ : ℝ)) ξ
  rw [e]
  rw [h2]
  simp only [norm_smul, norm_pow, Real.norm_of_nonneg (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) σ)]
  exact mul_le_mul_of_nonneg_left (hΛ a ha _) (by positivity)

theorem two_pow_half_ge {J : ℕ} (hJ : 16 ≤ J) : (256 : ℝ) ≤ (2 : ℝ) ^ ((J : ℝ) / 2) := by
  have : (256 : ℝ) = (2 : ℝ) ^ (8 : ℝ) := by norm_num
  rw [this]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
    have : (16 : ℝ) ≤ J := by exact_mod_cast hJ
    linarith)

/-- `A 2^{J j} = 2^{-σ_j}/8` for `A = 2^{-s₀}/8`, `σ_j = s₀ - J j`. -/
theorem anchor_scale (J : ℕ) {s₀ j σ : ℤ} (hσ : σ = s₀ - (J : ℤ) * j) :
    (2 : ℝ) ^ (-s₀) / 8 * (2 : ℝ) ^ ((J : ℝ) * j) = (2 : ℝ) ^ (-σ) / 8 := by
  have : (2 : ℝ) ^ ((J : ℝ) * j) = (2 : ℝ) ^ ((J : ℤ) * j) := by
    have := pw_eq_zpow J j
    unfold pw at this
    exact this
  rw [this, div_mul_eq_mul_div, ← zpow_add₀ (by norm_num), hσ]
  congr 2; ring

theorem anchor_scale_half (J : ℕ) {s₀ j σ : ℤ} (hσ : σ = s₀ - (J : ℤ) * j) :
    (2 : ℝ) ^ (-s₀) / 8 * (2 : ℝ) ^ ((J : ℝ) * (j + 1 / 2)) = (2 : ℝ) ^ (-σ) / 8 * (2 : ℝ) ^ ((J : ℝ) / 2) := by
  rw [show (J : ℝ) * (j + 1 / 2) = (J : ℝ) * j + (J : ℝ) / 2 by ring, Real.rpow_add (by norm_num), ← mul_assoc,
    anchor_scale J hσ]

theorem anchor_scale_two (J : ℕ) {s₀ j σ : ℤ} (hσ : σ = s₀ - (J : ℤ) * j) :
    (2 : ℝ) ^ (-s₀) / 8 * (2 : ℝ) ^ ((J : ℝ) * (j + 2)) = (2 : ℝ) ^ (-σ) / 8 * (2 : ℝ) ^ (2 * J) := by
  rw [show (J : ℝ) * (j + 2) = (J : ℝ) * j + (2 * J : ℕ) by push_cast; ring, Real.rpow_add (by norm_num), ← mul_assoc,
    anchor_scale J hσ, Real.rpow_natCast]

/-- The constant of the lacunary symbols. -/
def lacLam : ℝ := Classical.choose (exists_lacProfile_deriv_bound 3)

theorem lacLam_spec : 1 ≤ lacLam ∧ ∀ a ≤ 3, ∀ u : ℝ, ‖iteratedDeriv a (fun u : ℝ => ((lacProfile u : ℝ) : ℂ)) u‖ ≤ lacLam :=
  Classical.choose_spec (exists_lacProfile_deriv_bound 3)

/-- **`Λ⁻¹ lacSym 0 σ_j` is an `IsLPSymbol`** (anchor `A = 2^{-s₀}/8`). -/
theorem isLPSymbol_lac {J : ℕ} (hJ : 16 ≤ J) {s₀ j σ : ℤ} (hσ : σ = s₀ - (J : ℤ) * j) :
    IsLPSymbol ((2 : ℝ) ^ (-s₀) / 8) J 3 j (fun ξ => ((lacLam⁻¹ : ℝ) : ℂ) * lacSym 0 σ ξ) := by
  have hp := zpow_two_pos (-σ)
  have hpσ := zpow_two_pos σ
  obtain ⟨hL1, hL⟩ := lacLam_spec
  refine ⟨contDiff_const.mul (contDiff_lacSym 0 σ), ?_, ?_⟩
  · intro ξ hξ
    beta_reduce
    rw [anchor_scale J hσ, anchor_scale_two J hσ] at hξ
    rcases hξ with h | h
    · rw [lacSym_eq_zero_of_le (θ := 0) (ξ := ξ) (σ := σ) (by rw [sub_zero]; nlinarith), mul_zero]
    · have h2 : (2 : ℝ) ^ (2 * J) ≥ 8 * 517 := by
        have : (2 : ℝ) ^ (2 * J) ≥ (2 : ℝ) ^ 32 := pow_le_pow_right₀ (by norm_num) (by omega)
        nlinarith
      rw [lacSym_eq_zero_of_ge (θ := 0) (ξ := ξ) (σ := σ) (by rw [sub_zero, lacHi0_eq]; nlinarith), mul_zero]
  · intro a ha ξ
    rw [anchor_scale J hσ]
    have h1 : iteratedDeriv a (fun ξ => ((lacLam⁻¹ : ℝ) : ℂ) * lacSym 0 σ ξ) ξ =
        ((lacLam⁻¹ : ℝ) : ℂ) * iteratedDeriv a (lacSym 0 σ) ξ := iteratedDeriv_const_mul_field _ _
    rw [h1, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (by linarith))]
    have h2 := norm_iteratedDeriv_lacSym0_le hL σ ha ξ
    have h3 : ((2 : ℝ) ^ (-σ) / 8) ^ a * ((2 : ℝ) ^ σ) ^ a = (1 / 8) ^ a := by
      rw [← mul_pow, div_mul_eq_mul_div, ← zpow_add₀ (by norm_num)]; simp
    have hL0 : 0 < lacLam := by linarith
    calc ((2 : ℝ) ^ (-σ) / 8) ^ a * (lacLam⁻¹ * ‖iteratedDeriv a (lacSym 0 σ) ξ‖)
        ≤ ((2 : ℝ) ^ (-σ) / 8) ^ a * (lacLam⁻¹ * (((2 : ℝ) ^ σ) ^ a * lacLam)) := by gcongr
      _ = (((2 : ℝ) ^ (-σ) / 8) ^ a * ((2 : ℝ) ^ σ) ^ a) * (lacLam⁻¹ * lacLam) := by ring
      _ = (1 / 8) ^ a := by rw [h3, inv_mul_cancel₀ hL0.ne', mul_one]
      _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

/-- **`𝔭.C⁻¹ m(· + θ)` is an `IsLowSymbol`** (`m ∈ M_ω(𝔭)` at the scale `σ_j`, `|c - θ| ≤ (13/8) 2^{-σ}`). -/
theorem isLowSymbol_mult {𝔭 : Params} (h𝔭 : 𝔭.Admissible) {J : ℕ} (hJ : 16 ≤ J) {s₀ j σ : ℤ}
    (hσ : σ = s₀ - (J : ℤ) * j) {c θ : ℝ} {m' : ℝ → ℂ} (hm : InMult 𝔭 σ c m')
    (hθ : |c - θ| ≤ 13 / 8 * (2 : ℝ) ^ (-σ)) :
    IsLowSymbol ((2 : ℝ) ^ (-s₀) / 8) J 3 j (fun ξ => ((𝔭.C⁻¹ : ℝ) : ℂ) * m' (ξ + θ)) := by
  have hp := zpow_two_pos (-σ)
  obtain ⟨hN, hD, hβ, hC⟩ := h𝔭.bounds
  have hβ2 := h𝔭.beta_le
  have hC0 : 0 < 𝔭.C := by linarith
  refine ⟨contDiff_const.mul (hm.1.comp (contDiff_id.add contDiff_const)), ?_, ?_⟩
  · intro ξ hξ
    beta_reduce
    rw [anchor_scale_half J hσ] at hξ
    have h256 := two_pow_half_ge hJ
    have hmz : m' (ξ + θ) = 0 := by
      refine hm.2.1 (ξ + θ) ?_
      have h1 : 3 * (2 : ℝ) ^ (-σ) < |ξ| := by nlinarith
      have h2 : |ξ| ≤ |ξ + θ - c| + |c - θ| := by
        calc |ξ| = |(ξ + θ - c) + (c - θ)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      nlinarith
    rw [hmz, mul_zero]
  · intro a ha ξ
    rw [anchor_scale J hσ]
    have h1 : iteratedDeriv a (fun ξ => ((𝔭.C⁻¹ : ℝ) : ℂ) * m' (ξ + θ)) ξ =
        ((𝔭.C⁻¹ : ℝ) : ℂ) * iteratedDeriv a m' (ξ + θ) := by
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_add_const]
    rw [h1, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hC0.le)]
    have h2 := hm.2.2 a (by omega) (ξ + θ)
    calc ((2 : ℝ) ^ (-σ) / 8) ^ a * (𝔭.C⁻¹ * ‖iteratedDeriv a m' (ξ + θ)‖)
        = (1 / 8) ^ a * (𝔭.C⁻¹ * (((2 : ℝ) ^ (-σ)) ^ a * ‖iteratedDeriv a m' (ξ + θ)‖)) := by
          simp only [div_pow, one_div, inv_pow]; ring
      _ ≤ (1 / 8) ^ a * (𝔭.C⁻¹ * 𝔭.C) := by gcongr
      _ ≤ 1 := by rw [inv_mul_cancel₀ hC0.ne', mul_one]; exact pow_le_one₀ (by norm_num) (by norm_num)

theorem isLowSymbol_zero (A : ℝ) (J a₀ : ℕ) (j : ℤ) : IsLowSymbol A J a₀ j (fun _ => (0 : ℂ)) := by
  refine ⟨contDiff_const, fun ξ _ => rfl, fun a _ ξ => ?_⟩
  have : iteratedDeriv a (fun _ : ℝ => (0 : ℂ)) ξ = 0 := by
    have : (fun _ : ℝ => (0 : ℂ)) = (0 : ℝ → ℂ) := rfl
    rw [this]; simp
  rw [this]; simp

end PrimeBHT.TimeFrequency.X2
