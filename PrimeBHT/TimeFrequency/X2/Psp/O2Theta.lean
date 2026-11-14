module

public import PrimeBHT.TimeFrequency.X2.Psp.O2Endpoint

/-!
# X2, V13 O2 (f): the frames: `ovS`, `ovCoef`, the layer kernel in the frame centred at `θ`

Modulation covariance (`fourierInv_shift`): with `F̂ = e(-θ ·) F`,
`T_{s(· - θ)} F = e(θ ·) T_s F̂`, `S_τ F = e(θ ·) T_{lpSym} F̂` (`ovS_eq`), `c_τ(x) = 2^{-τ} ∫ tilPhi(x - a) (T_{lpSym} F̂)(a) da` (`ovCoef_eq`),
and the single-endpoint estimate in the ORIGINAL frame: `err_endpoint_theta`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform ContDiff Real Convolution
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

theorem ovPhase_add (θ a b : ℝ) : ovPhase θ (a + b) = ovPhase θ a * ovPhase θ b := by
  unfold ovPhase
  rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem ovPhase_neg_mul (θ a : ℝ) : ovPhase (-θ) a * ovPhase θ a = 1 := by
  unfold ovPhase
  rw [← Complex.exp_add]
  have : (((2 * π * -θ * a : ℝ) : ℂ) * Complex.I + ((2 * π * θ * a : ℝ) : ℂ) * Complex.I) = 0 := by
    push_cast; ring
  rw [this, Complex.exp_zero]

theorem ovPhase_sub_mul (θ a b : ℝ) : ovPhase θ (a - b) * ovPhase θ b = ovPhase θ a := by
  rw [← ovPhase_add]; congr 1; ring

section Frames

variable {P : ℕ} [NeZero P]

/-- the demodulated function `F̂ = e(-θ ·) F` -/
def demod (θ : ℝ) (F : ℝ → ZMod P → ℂ) : ℝ → ZMod P → ℂ := fun z y => ovPhase (-θ) z * F z y

omit [NeZero P] in
theorem measurable_demod (θ : ℝ) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) : Measurable (demod θ F) := by
  refine measurable_pi_iff.2 fun y => ?_
  have h1 : Measurable (ovPhase (-θ)) := (continuous_ovPhase (-θ)).measurable
  exact h1.mul (measurable_pi_iff.1 hF y)

omit [NeZero P] in
theorem norm_demod_le (θ : ℝ) {F : ℝ → ZMod P → ℂ} {B : ℝ} (hB : ∀ z y, ‖F z y‖ ≤ B) (z : ℝ) (y : ZMod P) :
    ‖demod θ F z y‖ ≤ B := by
  unfold demod
  rw [norm_mul, norm_ovPhase, one_mul]; exact hB z y

omit [NeZero P] in
/-- `T_{s(· - θ)} F = e(θ ·) T_s F̂` -/
theorem tmult_shift (s : ℝ → ℂ) (θ : ℝ) (F : ℝ → ZMod P → ℂ) (x : ℝ) (y : ZMod P) :
    tmult (fun ξ => s (ξ - θ)) F x y = ovPhase θ x * tmult s (demod θ F) x y := by
  unfold tmult demod
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  beta_reduce
  rw [fourierInv_shift s θ (x - z)]
  have h2 : Complex.exp (↑(2 * π * θ * (x - z)) * Complex.I) = ovPhase θ x * ovPhase (-θ) z := by
    unfold ovPhase; rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [h2]
  ring

theorem lowSym_eq_shift (θ : ℝ) (τ : ℤ) : lowSym θ τ = fun ξ => lowSym 0 τ (ξ - θ) := by
  funext ξ; unfold lowSym; simp

theorem tmult_lowSym (θ : ℝ) (τ : ℤ) (F : ℝ → ZMod P → ℂ) (x : ℝ) (y : ZMod P) :
    tmult (lowSym θ τ) F x y = ovPhase θ x * tmult (lowSym 0 τ) (demod θ F) x y := by
  rw [lowSym_eq_shift]; exact tmult_shift (lowSym 0 τ) θ F x y

omit [NeZero P] in
theorem tmult_lpSym {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {B : ℝ} (hB : ∀ z y, ‖F z y‖ ≤ B) (J : ℕ) (τ : ℤ)
    (x : ℝ) (y : ZMod P) :
    tmult (lpSym J τ) F x y = tmult (lowSym 0 τ) F x y - tmult (lowSym 0 (τ + (J : ℤ))) F x y := by
  have hc1 := contDiff_lowSym 0 τ
  have hc2 := contDiff_lowSym 0 (τ + (J : ℤ))
  have hs1 : HasCompactSupport (lowSym 0 τ) :=
    hasCompactSupport_of_far (c := 0) (r := 17 / 4 * (2 : ℝ) ^ (-τ)) fun ξ hξ =>
      lowSym_eq_zero (by simpa using hξ.le)
  have hs2 : HasCompactSupport (lowSym 0 (τ + (J : ℤ))) :=
    hasCompactSupport_of_far (c := 0) (r := 17 / 4 * (2 : ℝ) ^ (-(τ + (J : ℤ)))) fun ξ hξ =>
      lowSym_eq_zero (by simpa using hξ.le)
  obtain ⟨hk1c, hk1i⟩ := kernel_facts hc1 hs1
  obtain ⟨hk2c, hk2i⟩ := kernel_facts hc2 hs2
  have hFy := measurable_pi_iff.1 hF y
  have hk : ∀ u, 𝓕⁻ (lpSym J τ) u = 𝓕⁻ (lowSym 0 τ) u - 𝓕⁻ (lowSym 0 (τ + (J : ℤ))) u := by
    intro u
    rw [fourierInv_eq_integral_exp, fourierInv_eq_integral_exp, fourierInv_eq_integral_exp]
    have i1 : Integrable (fun v : ℝ => Complex.exp (↑(2 * π * v * u) * Complex.I) * lowSym 0 τ v) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ hs1.mul_left
      have := hc1.continuous; fun_prop
    have i2 : Integrable (fun v : ℝ => Complex.exp (↑(2 * π * v * u) * Complex.I) * lowSym 0 (τ + (J : ℤ)) v) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ hs2.mul_left
      have := hc2.continuous; fun_prop
    rw [← integral_sub i1 i2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    unfold lpSym; ring
  unfold tmult
  have i1 := integrable_kmul hk1i hFy (fun z => hB z y) x hk1c
  have i2 := integrable_kmul hk2i hFy (fun z => hB z y) x hk2c
  rw [← integral_sub i1 i2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  beta_reduce
  rw [hk]; ring

/-- `S_τ F = e(θ ·) T_{lpSym} F̂` -/
theorem ovS_eq (J : ℕ) (θ : ℝ) (τ : ℤ) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {B : ℝ} (hB : ∀ z y, ‖F z y‖ ≤ B)
    (x : ℝ) (y : ZMod P) : ovS J θ τ F x y = ovPhase θ x * tmult (lpSym J τ) (demod θ F) x y := by
  unfold ovS
  rw [tmult_lpSym (measurable_demod θ hF) (norm_demod_le θ hB) J τ x y, Pi.sub_apply, tmult_lowSym θ τ F x y,
    tmult_lowSym θ (τ + (J : ℤ)) F x y]
  ring

theorem ovCoef_eq (J : ℕ) (θ : ℝ) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {B : ℝ} (hB : ∀ z y, ‖F z y‖ ≤ B) (τ : ℤ)
    (x : ℝ) (y : ZMod P) :
    ovCoef J θ F τ x y = ((((2 : ℝ) ^ τ)⁻¹ : ℝ) : ℂ) * ∫ a, tilPhi J τ (x - a) * tmult (lpSym J τ) (demod θ F) a y := by
  unfold ovCoef
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  beta_reduce
  rw [ovS_eq J θ τ hF hB a y]
  have := ovPhase_neg_mul θ a
  calc tilPhi J τ (x - a) * ovPhase (-θ) a * (ovPhase θ a * tmult (lpSym J τ) (demod θ F) a y)
      = tilPhi J τ (x - a) * (ovPhase (-θ) a * ovPhase θ a) * tmult (lpSym J τ) (demod θ F) a y := by ring
    _ = _ := by rw [this]; ring

/-- **The single-endpoint estimate in the original frame** (terms (d5), (d6) of MTT2 for one endpoint `x` of `Ẽ_τ`). -/
theorem err_endpoint_theta {J : ℕ} {τ σ : ℤ} (hστ : τ + (J : ℤ) ≤ σ) {M : ℕ} {C₀ : ℝ} {m : ℝ → ℂ} {θ : ℝ}
    (hm : Sym0 σ M C₀ (fun ξ => m (ξ + θ))) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {BF : ℝ}
    (hBF : ∀ z y, ‖F z y‖ ≤ BF) {x Ag N A₁ : ℝ} (hAg : 0 ≤ Ag) (hN : 0 ≤ N) (hA₁ : 0 ≤ A₁) {q : ℕ}
    (hq : N + 2 * ((M : ℝ) + 3) ≤ q) (hgrow : ∀ b, yNorm 2 (ovS J θ τ F b) ≤ Ag * jb ((b - x) / (2 : ℝ) ^ τ) ^ N)
    (hcn : yNorm 2 (ovCoef J θ F τ x) ≤ A₁) {β : ℝ → ℝ} (hβ : BumpData ((2 : ℝ) ^ τ) x β) (x₀ : ℝ) :
    yNorm 2 (fun y => ∫ z, 𝓕⁻ m (x₀ - z) *
        (((heav (z - x) : ℝ) : ℂ) * ovS J θ τ F z y - ovPhase θ z * ((β z : ℝ) : ℂ) * ovCoef J θ F τ x y)) ≤
      (endC3 M C₀ * 2 ^ M * (2 * endQ J M q N * ((2 : ℝ) ^ ((J : ℤ) + 1)) ^ 2 + 1)) * (Ag + A₁) *
        ((2 : ℝ) ^ (τ - σ)) ^ 2 * jb ((x₀ - x) / (2 : ℝ) ^ σ) ^ (-(M : ℝ)) := by
  have hFh := measurable_demod θ hF
  have hBFh := norm_demod_le θ hBF
  have hgrow' : ∀ b, yNorm 2 (tmult (lpSym J τ) (demod θ F) b) ≤ Ag * jb ((b - x) / (2 : ℝ) ^ τ) ^ N := fun b => by
    have e : ovS J θ τ F b = fun y => ovPhase θ b * tmult (lpSym J τ) (demod θ F) b y :=
      funext fun y => ovS_eq J θ τ hF hBF b y
    have := hgrow b
    rw [e, yNorm_fun_const_mul (by norm_num), norm_ovPhase, one_mul] at this
    exact this
  have hmain := endpoint_bound hστ hm hFh hBFh hAg hN hA₁ hq hgrow' (c := ovCoef J θ F τ x)
    (fun y => ovCoef_eq J θ hF hBF τ x y) hcn hβ x₀
  have hrw : (fun y => ∫ z, 𝓕⁻ m (x₀ - z) *
        (((heav (z - x) : ℝ) : ℂ) * ovS J θ τ F z y - ovPhase θ z * ((β z : ℝ) : ℂ) * ovCoef J θ F τ x y)) =
      fun y => ovPhase θ x₀ * ∫ z, 𝓕⁻ (fun ξ => m (ξ + θ)) (x₀ - z) *
        (((heav (z - x) : ℝ) : ℂ) * tmult (lpSym J τ) (demod θ F) z y - ((β z : ℝ) : ℂ) * ovCoef J θ F τ x y) := by
    funext y
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    have hk : 𝓕⁻ m (x₀ - z) = ovPhase θ (x₀ - z) * 𝓕⁻ (fun ξ => m (ξ + θ)) (x₀ - z) := by
      have := fourierInv_shift (fun ξ => m (ξ + θ)) θ (x₀ - z)
      have e : (fun ξ => (fun ξ => m (ξ + θ)) (ξ - θ)) = m := funext fun ξ => by simp
      rw [e] at this
      exact this
    rw [hk, ovS_eq J θ τ hF hBF z y]
    have hp : ovPhase θ x₀ = ovPhase θ (x₀ - z) * ovPhase θ z := (ovPhase_sub_mul θ x₀ z).symm
    rw [hp]
    ring
  rw [hrw, yNorm_fun_const_mul (by norm_num), norm_ovPhase, one_mul]
  exact hmain

end Frames

end PrimeBHT.TimeFrequency.X2
