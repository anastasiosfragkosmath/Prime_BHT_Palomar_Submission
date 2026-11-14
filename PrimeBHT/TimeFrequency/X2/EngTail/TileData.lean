module

public import PrimeBHT.TimeFrequency.X2.EngTail.Bernstein
public import PrimeBHT.TimeFrequency.X2.EngTail.KernelDeriv
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# X2, node B5: class data give `TileBound`s (demodulated kernels)

For a tile of the class (`ψ ∈ Ψ_I(𝔭)`, `m ∈ M_ω(𝔭)`, `I = dyadicInt s v`) and a demodulation frequency `θ` with
`|c_ω - θ| ≤ C₀ 2^{-s}`, put `κ = 𝓕⁻(m(· + θ))`, so that `𝓕⁻ m(w) = e^{2πiθw} κ(w)`.  Then
`TileBound (𝔭.N) M C_φ C_κ s v ψ κ` for every real `M ≤ D - 1` with explicit constants.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

theorem InMult.shift {𝔭 : Params} {s : ℤ} {c : ℝ} {m : ℝ → ℂ} (hm : InMult 𝔭 s c m) (θ : ℝ) :
    InMult 𝔭 s (c - θ) (fun η => m (η + θ)) := by
  obtain ⟨hsm, hsupp, hder⟩ := hm
  refine ⟨hsm.comp (contDiff_id.add contDiff_const), fun ξ hξ => hsupp _ ?_, fun a ha ξ => ?_⟩
  · rw [show ξ + θ - c = ξ - (c - θ) by ring]; exact hξ
  · rw [iteratedDeriv_comp_add_const]; exact hder a ha (ξ + θ)

/-- The demodulated kernel `κ = 𝓕⁻(m(· + θ))`. -/
def kernelDemod (θ : ℝ) (m : ℝ → ℂ) : ℝ → ℂ := 𝓕⁻ (fun η => m (η + θ))

theorem fourierInv_eq_exp_mul_kernelDemod {m : ℝ → ℂ} (θ : ℝ) (w : ℝ) :
    𝓕⁻ m w = Complex.exp (2 * π * Complex.I * θ * w) * kernelDemod θ m w := by
  unfold kernelDemod
  rw [Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  have h1 : ∫ η : ℝ, Complex.exp (↑(-2 * Real.pi * η * -w) * Complex.I) • m η =
      ∫ η : ℝ, Complex.exp (↑(-2 * Real.pi * (η + θ) * -w) * Complex.I) • m (η + θ) :=
    (integral_add_right_eq_self (fun η : ℝ => Complex.exp (↑(-2 * Real.pi * η * -w) * Complex.I) • m η) θ).symm
  rw [h1, ← integral_const_mul]
  congr 1
  funext η
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem inv_pow_le_rpow_neg {t M : ℝ} {M' : ℕ} (ht : 0 ≤ t) (hMM : M ≤ M') :
    ((1 + t)⁻¹) ^ M' ≤ (1 + t) ^ (-M) := by
  have hb : (1 : ℝ) ≤ 1 + t := by linarith
  have e1 : ((1 + t)⁻¹) ^ M' = (1 + t) ^ (-(M' : ℝ)) := by
    rw [Real.rpow_neg (by linarith), Real.rpow_natCast, inv_pow]
  rw [e1]
  exact Real.rpow_le_rpow_of_exponent_le hb (by linarith)

section Tile

variable {𝔭 : Params}

/-- The constant `C_κ` of the demodulated kernels (order `M' = ⌈M⌉`). -/
def kappaConst (𝔭 : Params) (M' : ℕ) (C₀ : ℝ) : ℝ :=
  2 ^ (M' + 1) * 𝔭.β * (2 * π) * 𝔭.C * (C₀ + 𝔭.β / 2 + M')

theorem kappaConst_nonneg (h𝔭 : 0 ≤ 𝔭.β) (hC : 0 ≤ 𝔭.C) (M' : ℕ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    0 ≤ kappaConst 𝔭 M' C₀ := by
  unfold kappaConst; positivity

/-- **Kernel bounds of a class multiplier after demodulation.** -/
theorem kernelDemod_bounds {M : ℝ} (hM1 : 1 ≤ M) (hM : M + 1 ≤ 𝔭.D) (hβ : 1 ≤ 𝔭.β) (hC : 1 ≤ 𝔭.C)
    {s : ℤ} {c θ C₀ : ℝ} {m : ℝ → ℂ} (hm : InMult 𝔭 s c m) (hC₀ : 0 ≤ C₀)
    (hθ : |c - θ| ≤ C₀ * (2 : ℝ) ^ (-s)) :
    (∀ w, ‖kernelDemod θ m w‖ ≤ kappaConst 𝔭 ⌈M⌉₊ C₀ *
        (((2 : ℝ) ^ s)⁻¹ * (1 + |w| / (2 : ℝ) ^ s) ^ (-M))) ∧
      Differentiable ℝ (kernelDemod θ m) ∧
      ∀ w, ‖deriv (kernelDemod θ m) w‖ ≤ kappaConst 𝔭 ⌈M⌉₊ C₀ *
        ((((2 : ℝ) ^ s)⁻¹) ^ 2 * (1 + |w| / (2 : ℝ) ^ s) ^ (-M)) := by
  have hM0 : 0 ≤ M := by linarith
  have hMc : ⌈M⌉₊ ≤ 𝔭.D := by
    have : M ≤ 𝔭.D := by linarith
    exact Nat.ceil_le.2 this
  have hM1c : 1 ≤ ⌈M⌉₊ := Nat.one_le_ceil_iff.2 (by linarith)
  have hL : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) s
  have hl : (2 : ℝ) ^ (-s) = ((2 : ℝ) ^ s)⁻¹ := zpow_neg _ _
  have hn := hm.shift θ
  set n : ℝ → ℂ := fun η => m (η + θ) with hn_def
  have hcont : Continuous n := hn.1.continuous
  have hrel : ∀ w, (1 + (2 : ℝ) ^ (-s) * |w|) = 1 + |w| / (2 : ℝ) ^ s := by
    intro w; rw [hl]; field_simp
  have hw0 : ∀ w : ℝ, 0 ≤ |w| / (2 : ℝ) ^ s := fun w => by positivity
  have hCp : 0 ≤ 𝔭.C := by linarith
  have hβp : 0 ≤ 𝔭.β := by linarith
  have hconst : 1 ≤ 2 * π * (C₀ + 𝔭.β / 2 + (⌈M⌉₊ : ℝ)) := by
    have : (1 : ℝ) ≤ ⌈M⌉₊ := by exact_mod_cast hM1c
    have h3 := Real.pi_gt_three
    nlinarith
  refine ⟨fun w => ?_, ?_, fun w => ?_⟩
  · have h1 := norm_fourierInv_inMult_le_pow hMc hβp hn w
    unfold kernelDemod
    refine h1.trans ?_
    rw [hrel, hl]
    have h2 := inv_pow_le_rpow_neg (hw0 w) (show M ≤ ((⌈M⌉₊ : ℕ) : ℝ) from Nat.le_ceil M)
    have hk0 : 0 ≤ kappaConst 𝔭 ⌈M⌉₊ C₀ := kappaConst_nonneg hβp hCp _ hC₀
    unfold kappaConst at hk0 ⊢
    have hfac : 2 ^ (⌈M⌉₊ + 1) * 𝔭.β * 𝔭.C ≤ 2 ^ (⌈M⌉₊ + 1) * 𝔭.β * (2 * π) * 𝔭.C * (C₀ + 𝔭.β / 2 + ⌈M⌉₊) := by
      have : 0 ≤ 2 ^ (⌈M⌉₊ + 1) * 𝔭.β * 𝔭.C := by positivity
      nlinarith [mul_nonneg this (sub_nonneg.2 hconst)]
    have h3 : 0 ≤ ((2 : ℝ) ^ s)⁻¹ := by positivity
    have h4 : 0 ≤ ((2 : ℝ) ^ s)⁻¹ * ((1 + |w| / (2 : ℝ) ^ s)⁻¹) ^ ⌈M⌉₊ := by
      have : 0 < 1 + |w| / (2 : ℝ) ^ s := by have := hw0 w; linarith
      positivity
    exact mul_le_mul hfac (mul_le_mul_of_nonneg_left h2 h3) h4 (by positivity)
  · have hder : ∀ w, HasDerivAt (kernelDemod θ m) (𝓕⁻ (fun η : ℝ => (2 * π * Complex.I * η) * n η) w) w :=
      fun w => hasDerivAt_fourierInv_cs hcont hn.2.1 w
    exact fun w => (hder w).differentiableAt
  · have hder : HasDerivAt (kernelDemod θ m) (𝓕⁻ (fun η : ℝ => (2 * π * Complex.I * η) * n η) w) w :=
      hasDerivAt_fourierInv_cs hcont hn.2.1 w
    rw [hder.deriv]
    have hc' : |c - θ| ≤ C₀ * (2 : ℝ) ^ (-s) := hθ
    have h1 := norm_fourierInv_deriv_inMult_le hM1c hMc hβp hn hC₀ hc' w
    refine h1.trans ?_
    rw [hrel, hl]
    have h2 := inv_pow_le_rpow_neg (hw0 w) (show M ≤ ((⌈M⌉₊ : ℕ) : ℝ) from Nat.le_ceil M)
    unfold kappaConst
    have e : 2 ^ (⌈M⌉₊ + 1) * (2 * (𝔭.β * ((2 : ℝ) ^ s)⁻¹ / 2)) *
        (2 * π * 𝔭.C * ((2 : ℝ) ^ s)⁻¹ * (C₀ + 𝔭.β / 2 + ⌈M⌉₊)) * ((1 + |w| / (2 : ℝ) ^ s)⁻¹) ^ ⌈M⌉₊ =
        (2 ^ (⌈M⌉₊ + 1) * 𝔭.β * (2 * π) * 𝔭.C * (C₀ + 𝔭.β / 2 + ⌈M⌉₊)) *
          ((((2 : ℝ) ^ s)⁻¹) ^ 2 * ((1 + |w| / (2 : ℝ) ^ s)⁻¹) ^ ⌈M⌉₊) := by ring
    rw [e]
    have : 0 ≤ (2 ^ (⌈M⌉₊ + 1) * 𝔭.β * (2 * π) * 𝔭.C * (C₀ + 𝔭.β / 2 + ⌈M⌉₊)) := by positivity
    have h3 : 0 ≤ (((2 : ℝ) ^ s)⁻¹) ^ 2 := by positivity
    gcongr

end Tile


section Tile2

variable {𝔭 : Params}

/-- **The tile bounds of the class**, uniformly in the tile: constants depending on `(𝔭, M, C₀)` only. -/
theorem exists_tileBound (h𝔭 : 𝔭.Admissible) {M : ℝ} (hM1 : 1 ≤ M) (hM : M + 1 ≤ 𝔭.D) {C₀ : ℝ}
    (hC₀ : 0 ≤ C₀) :
    ∃ Cφ Cκ : ℝ, 0 ≤ Cφ ∧ 0 ≤ Cκ ∧ ∀ (s v : ℤ) (c θ : ℝ) (ψ m : ℝ → ℂ), InPsi 𝔭 s v ψ → InMult 𝔭 s c m →
      |c - θ| ≤ C₀ * (2 : ℝ) ^ (-s) → TileBound (𝔭.N : ℝ) M Cφ Cκ s v ψ (kernelDemod θ m) := by
  have hδ := Params.Admissible.delta_le_half h𝔭
  obtain ⟨-, hN, hD, -, -, hβ, -, hC⟩ := h𝔭
  have hN2 : 2 ≤ 𝔭.N := le_trans (by unfold classFloor; norm_num) hN
  obtain ⟨CB, hCB0, hCB⟩ := inPsi_deriv_bound 𝔭 hN2 hδ (by linarith)
  refine ⟨max 𝔭.C CB, kappaConst 𝔭 ⌈M⌉₊ C₀, le_trans (by linarith) (le_max_left _ _),
    kappaConst_nonneg (by linarith) (by linarith) _ hC₀, ?_⟩
  intro s v c θ ψ m hψ hm hθ
  obtain ⟨h1, h2, h3⟩ := kernelDemod_bounds hM1 hM hβ hC hm hC₀ hθ
  obtain ⟨hdiff, hder⟩ := hCB s v ψ hψ
  have hL : (0 : ℝ) < ((2 : ℝ) ^ s)⁻¹ := inv_pos.2 (zpow_pos (by norm_num) s)
  refine ⟨fun x => ?_, hdiff, fun x => ?_, h1, h2, h3⟩
  · exact (hψ.le_tw x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (tw_nonneg _ _ _ _))
  · refine (hder x).trans ?_
    have := tw_nonneg (𝔭.N : ℝ) s v x
    gcongr
    exact le_max_right _ _

end Tile2

end PrimeBHT.TimeFrequency.X2
