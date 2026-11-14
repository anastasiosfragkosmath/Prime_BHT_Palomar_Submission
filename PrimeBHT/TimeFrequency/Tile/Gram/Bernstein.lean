module

public import PrimeBHT.TimeFrequency.Tile.Gram.Pair
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Bernstein's inequality for adapted packets: (G0) of blueprint node C2 (`TT.gram`)

For `φ` adapted (exponent `N`) to `(I, ω)` with `ω = [β, β + 1/|I|)` (general interval `I`, `|I| > 0`) and
`φ̃ = demod ω φ = e^{-2πi c(ω) ·} φ`:

* `fourier_demod_eq_zero`: `𝓕 φ̃` vanishes off `[-1/(2|I|), 1/(2|I|)]`;
* `contDiff_demod`: `φ̃` is `C^m` for every `m`;
* `iteratedDeriv_demod_eq`: `D^n φ̃(x) = ∫ φ̃(y) |I|^{-1-n} K_n((x - y)/|I|) dy` with the fixed Schwartz kernels
  `K_n = kernelG0 n = 𝓕[(-2πiη)^n χ(η)]` (`χ = bumpG0`, `= 1` on `[-1/2, 1/2]`); for `n = 0`:
  `φ̃ = φ̃ * K_{|I|}`, `K_{|I|} = |I|^{-1}K_0(·/|I|)`, `𝓕⁻ K_0 = χ` (`fourierInv_kernelG0_zero`);
* `exists_norm_iteratedDeriv_demod_le`: for all `n`, `N` there is `C_{n,N}` with
  `|D^n φ̃(x)| ≤ C_{n,N} |I|^{-n-1/2} (1 + |x - c(I)|/|I|)^{-N}`.

(G0) is not used by (G1)-(G5) here (see `Gram/Bessel.lean` for the Bernstein-free proof of (G4)).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform

namespace PrimeBHT.TimeFrequency.Tile

open PrimeBHT.Statements

/-! ### (G0) Bernstein: the reproducing formula and bounds for all derivatives -/

/-- The demodulated packet `φ̃(y) = e^{-2πi c(ω) y} φ(y)` (exactly the function of `IsAdapted`). -/
noncomputable def demod (ω : Set ℝ) (φ : ℝ → ℂ) : ℝ → ℂ := fun y =>
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (intervalCentre ω : ℂ) * (y : ℂ))) * φ y

/-- The fixed bump: smooth, `= 1` on `[-1/2, 1/2]`, supported in `[-1, 1]`. -/
noncomputable def bumpG0 : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- `κ_n(η) = (-2πiη)^n χ(η)` with `χ = bumpG0`. -/
noncomputable def kappaG0 (n : ℕ) (η : ℝ) : ℂ :=
  (-2 * (Real.pi : ℂ) * Complex.I * η) ^ n * ((bumpG0 η : ℝ) : ℂ)

/-- The kernels `K_n = 𝓕 κ_n` (Schwartz). `K_0 = 𝓕 χ`, and `𝓕 K_0 = χ(-·) = 1` on `[-1/2, 1/2]`. -/
noncomputable def kernelG0 (n : ℕ) : ℝ → ℂ := 𝓕 (kappaG0 n)

theorem bumpG0_eq_one {η : ℝ} (h : |η| ≤ 1 / 2) : bumpG0 η = 1 :=
  bumpG0.one_of_mem_closedBall (by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact h)

theorem contDiff_kappaG0 (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (kappaG0 n) := by
  have hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun η : ℝ => ((bumpG0 η : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp bumpG0.contDiff
  have hp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun η : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * η) ^ n) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).pow n
  exact hp.mul hb

theorem hasCompactSupport_kappaG0 (n : ℕ) : HasCompactSupport (kappaG0 n) := by
  have hb : HasCompactSupport (fun η : ℝ => ((bumpG0 η : ℝ) : ℂ)) :=
    bumpG0.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  exact hb.mul_left

/-- Decay of the kernels: `|K_n(u)| ≤ C (1 + |u|)^{-k}`. -/
theorem exists_norm_kernelG0_le (n k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, ‖kernelG0 n u‖ ≤ C * (1 + |u|) ^ (-(k : ℝ)) := by
  set S : SchwartzMap ℝ ℂ := (hasCompactSupport_kappaG0 n).toSchwartzMap (contDiff_kappaG0 n)
  set C := 2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (𝓕 S)
  have hC : ∀ u : ℝ, (1 + ‖u‖) ^ k * ‖(𝓕 S) u‖ ≤ C := by
    intro u
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl (𝓕 S) u
    rwa [norm_iteratedFDeriv_zero] at h
  refine ⟨C, le_trans (by positivity) (hC 0), fun u => ?_⟩
  have hu : 0 < 1 + |u| := by positivity
  have h1 : kernelG0 n u = (𝓕 S) u := rfl
  rw [h1, Real.rpow_neg hu.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity),
    mul_comm]
  have := hC u
  rwa [Real.norm_eq_abs] at this

/-- Fubini: `∫ e(-ξx) ρ(ξ) 𝓕u(-ξ) dξ = ∫ u(y) 𝓕ρ(x - y) dy` for integrable `ρ`, `u`. -/
theorem integral_fourier_mul_fourier_neg {ρ u : ℝ → ℂ} (hρ : Integrable ρ) (hu : Integrable u)
    (x : ℝ) :
    ∫ ξ, Complex.exp (↑(-2 * Real.pi * ξ * x) * Complex.I) * (ρ ξ * 𝓕 u (-ξ)) =
      ∫ y, u y * 𝓕 ρ (x - y) := by
  have hF : Integrable (fun p : ℝ × ℝ => Complex.exp (↑(-2 * Real.pi * p.1 * x) * Complex.I) *
      (ρ p.1 * (Complex.exp (↑(-2 * Real.pi * p.2 * -p.1) * Complex.I) * u p.2)))
      (volume.prod volume) := by
    refine (hρ.norm.mul_prod hu.norm).mono' ?_ (ae_of_all _ fun p => ?_)
    · refine (Continuous.aestronglyMeasurable (by fun_prop)).mul
        ((hρ.aestronglyMeasurable.comp_fst).mul
          ((Continuous.aestronglyMeasurable (by fun_prop)).mul hu.aestronglyMeasurable.comp_snd))
    · simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      rfl
  calc ∫ ξ, Complex.exp (↑(-2 * Real.pi * ξ * x) * Complex.I) * (ρ ξ * 𝓕 u (-ξ))
      = ∫ ξ, ∫ y, Complex.exp (↑(-2 * Real.pi * ξ * x) * Complex.I) *
          (ρ ξ * (Complex.exp (↑(-2 * Real.pi * y * -ξ) * Complex.I) * u y)) := by
        congr 1
        funext ξ
        rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul, ← integral_const_mul]
        rfl
    _ = ∫ y, ∫ ξ, Complex.exp (↑(-2 * Real.pi * ξ * x) * Complex.I) *
          (ρ ξ * (Complex.exp (↑(-2 * Real.pi * y * -ξ) * Complex.I) * u y)) :=
        integral_integral_swap hF
    _ = ∫ y, u y * 𝓕 ρ (x - y) := by
        congr 1
        funext y
        rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
        congr 1
        funext ξ
        simp only [smul_eq_mul]
        have : Complex.exp (↑(-2 * Real.pi * ξ * x) * Complex.I) *
            Complex.exp (↑(-2 * Real.pi * y * -ξ) * Complex.I) =
            Complex.exp (↑(-2 * Real.pi * ξ * (x - y)) * Complex.I) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        rw [← this]
        ring

/-- Scaling: the Fourier transform of `ξ ↦ (-2πiξ)^n χ(Lξ)` is `L^{-1-n} K_n(·/L)`. -/
theorem fourier_scaled_kappa (n : ℕ) {L : ℝ} (hL : 0 < L) (z : ℝ) :
    𝓕 (fun ξ : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * ξ) ^ n * ((bumpG0 (L * ξ) : ℝ) : ℂ)) z =
      ((L ^ (-(1 : ℝ) - n) : ℝ) : ℂ) * kernelG0 n (z / L) := by
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have h1 : (fun ξ : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * ξ) ^ n * ((bumpG0 (L * ξ) : ℝ) : ℂ)) =
      fun ξ => ((L : ℂ)⁻¹) ^ n * kappaG0 n (L * ξ) := by
    funext ξ
    simp only [kappaG0]
    push_cast
    rw [← mul_assoc, ← mul_pow]
    congr 2
    field_simp
  rw [h1, Real.fourier_real_eq_integral_exp_smul, kernelG0, Real.fourier_real_eq_integral_exp_smul]
  have h2 : (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * z) * Complex.I) •
      (((L : ℂ)⁻¹) ^ n * kappaG0 n (L * v))) = fun v => ((L : ℂ)⁻¹) ^ n *
        (fun η : ℝ => Complex.exp (↑(-2 * Real.pi * η * (z / L)) * Complex.I) * kappaG0 n η)
          (L * v) := by
    funext v
    simp only [smul_eq_mul]
    have : -2 * Real.pi * (L * v) * (z / L) = -2 * Real.pi * v * z := by field_simp
    rw [this]
    ring
  rw [h2, integral_const_mul, Measure.integral_comp_mul_left
    (fun η : ℝ => Complex.exp (↑(-2 * Real.pi * η * (z / L)) * Complex.I) * kappaG0 n η) L,
    abs_of_pos (inv_pos.2 hL), Complex.real_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc]
  congr 1
  have : (-(1 : ℝ) - n) = -((n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [this, Real.rpow_neg hL.le, Real.rpow_natCast]
  push_cast
  rw [pow_succ, mul_inv, inv_pow]

end PrimeBHT.TimeFrequency.Tile
