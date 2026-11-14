module

public import PrimeBHT.TimeFrequency.X1.RealLine.Dilation
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Dilated averages with complex-valued profiles (blueprint nodes R1, R3)

`dilAvgC φ t f g x = ∫ f(x-y) g(x+y) t⁻¹ φ(y/t) dy` for a complex profile `φ : ℝ → ℂ`. For a real profile
it agrees with `dilAvg` (`dilAvg_eq_dilAvgC`); the existing real version is kept unchanged.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PrimeBHT.TimeFrequency.RealLine

/-- `B_t(φ, f, g)(x) = ∫ f(x - y) g(x + y) t⁻¹ φ(y / t) dy` for a complex-valued profile `φ`. -/
def dilAvgC (φ : ℝ → ℂ) (t : ℝ) (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, f (x - y) * g (x + y) * (((t⁻¹ : ℝ) : ℂ) * φ (y / t))

/-- For a real profile `dilAvgC` is the existing `dilAvg`. -/
theorem dilAvg_eq_dilAvgC (φ : ℝ → ℝ) (t : ℝ) (f g : ℝ → ℂ) (x : ℝ) :
    dilAvg φ t f g x = dilAvgC (fun y => (φ y : ℂ)) t f g x := by
  unfold dilAvg dilAvgC
  simp only [Complex.ofReal_mul]

/-- **R1 (a) for complex profiles.** `B_t(φ, D_s f, D_s g)(x) = B_{t s}(φ, f, g)(s x)`, `s > 0`. -/
theorem dilAvgC_dilate (φ : ℝ → ℂ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (f g : ℝ → ℂ) (x : ℝ) :
    dilAvgC φ t (fun u => f (s * u)) (fun u => g (s * u)) x = dilAvgC φ (t * s) f g (s * x) := by
  have hs0 : s ≠ 0 := hs.ne'
  have ht0 : t ≠ 0 := ht.ne'
  unfold dilAvgC
  rw [integral_dilate hs f g (fun y => ((t⁻¹ : ℝ) : ℂ) * φ (y / t)) x]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have e : ((s⁻¹ : ℝ) : ℂ) * (((t⁻¹ : ℝ) : ℂ) * φ (u / s / t)) =
      (((t * s)⁻¹ : ℝ) : ℂ) * φ (u / (t * s)) := by
    rw [div_div, mul_comm s t, mul_inv, Complex.ofReal_mul]
    ring
  simp only [e]

/-- Rescaling of the profile: `B_t(λ g(λ ·), f, h) = B_{t/λ}(g, f, h)` for `λ ≠ 0`. -/
theorem dilAvgC_scale_profile (g : ℝ → ℂ) {l t : ℝ} (hl : l ≠ 0) (ht : t ≠ 0) (f h : ℝ → ℂ) (x : ℝ) :
    dilAvgC (fun y => (l : ℂ) * g (l * y)) t f h x = dilAvgC g (t / l) f h x := by
  unfold dilAvgC
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have e : ((t⁻¹ : ℝ) : ℂ) * ((l : ℂ) * g (l * (y / t))) = (((t / l)⁻¹ : ℝ) : ℂ) * g (y / (t / l)) := by
    have e1 : l * (y / t) = y / (t / l) := by field_simp
    have e2 : (((t / l)⁻¹ : ℝ) : ℂ) = (l : ℂ) * ((t⁻¹ : ℝ) : ℂ) := by
      rw [inv_div, div_eq_mul_inv, Complex.ofReal_mul]
    rw [e1, e2]; ring
  simp only [e]

/-- Scalars factor out of the profile. -/
theorem dilAvgC_const_mul (a : ℂ) (φ : ℝ → ℂ) (t : ℝ) (f g : ℝ → ℂ) (x : ℝ) :
    dilAvgC (fun y => a * φ y) t f g x = a * dilAvgC φ t f g x := by
  unfold dilAvgC
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  ring

/-- Complex conjugation: `B_t(\bar φ, f, g) = \overline{B_t(φ, \bar f, \bar g)}`. -/
theorem dilAvgC_conj (φ : ℝ → ℂ) (t : ℝ) (f g : ℝ → ℂ) (x : ℝ) :
    dilAvgC (fun y => (starRingEnd ℂ) (φ y)) t f g x =
      (starRingEnd ℂ) (dilAvgC φ t (fun u => (starRingEnd ℂ) (f u)) (fun u => (starRingEnd ℂ) (g u)) x) := by
  unfold dilAvgC
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [map_mul, Complex.conj_ofReal, starRingEnd_self_apply]

/-- Integrability of the integrand of `dilAvgC` for bounded continuous `f, g` and integrable `φ`. -/
theorem integrable_dilAvgC_integrand {φ : ℝ → ℂ} (hφ : Integrable φ) {t : ℝ} (ht : t ≠ 0)
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) {Bf Bg : ℝ} (hBf : ∀ x, ‖f x‖ ≤ Bf)
    (hBg : ∀ x, ‖g x‖ ≤ Bg) (x : ℝ) :
    Integrable (fun y => f (x - y) * g (x + y) * (((t⁻¹ : ℝ) : ℂ) * φ (y / t))) := by
  have h1 : Integrable (fun y => ((t⁻¹ : ℝ) : ℂ) * φ (y / t)) :=
    (hφ.comp_div ht).const_mul _
  refine Integrable.bdd_mul (c := Bf * Bg) h1 ?_ (Eventually.of_forall fun y => ?_)
  · exact ((hf.comp (continuous_const.sub continuous_id)).mul
      (hg.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  · rw [norm_mul]
    exact mul_le_mul (hBf _) (hBg _) (norm_nonneg _) ((norm_nonneg _).trans (hBf 0))

/-- `x ↦ dilAvgC φ t f g x` is strongly measurable for continuous `φ, f, g`. -/
theorem aestronglyMeasurable_dilAvgC {φ : ℝ → ℂ} (hφ : Continuous φ) {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (t : ℝ) :
    AEStronglyMeasurable (dilAvgC φ t f g) volume := by
  have hc : Continuous (fun p : ℝ × ℝ =>
      f (p.1 - p.2) * g (p.1 + p.2) * (((t⁻¹ : ℝ) : ℂ) * φ (p.2 / t))) := by fun_prop
  exact (hc.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable

/-- `∫ ‖integrand‖ ≤ Bf Bg ∫ ‖φ‖`. -/
theorem integral_norm_integrand_le {φ : ℝ → ℂ} (hφ : Integrable φ) {t : ℝ} (ht : 0 < t)
    {f g : ℝ → ℂ} {Bf Bg : ℝ} (hBf : ∀ x, ‖f x‖ ≤ Bf) (hBg : ∀ x, ‖g x‖ ≤ Bg) (x : ℝ) :
    ∫ y, ‖f (x - y) * g (x + y) * (((t⁻¹ : ℝ) : ℂ) * φ (y / t))‖ ≤ Bf * Bg * ∫ y, ‖φ y‖ := by
  have hBf0 : 0 ≤ Bf := (norm_nonneg _).trans (hBf 0)
  have hBg0 : 0 ≤ Bg := (norm_nonneg _).trans (hBg 0)
  have h1 : Integrable (fun y => ‖φ (y / t)‖) := (hφ.norm.comp_div ht.ne')
  have h2 : (∫ y, ‖φ (y / t)‖) = t * ∫ y, ‖φ y‖ := by
    rw [Measure.integral_comp_div (fun y => ‖φ y‖) t, abs_of_pos ht, smul_eq_mul]
  calc ∫ y, ‖f (x - y) * g (x + y) * (((t⁻¹ : ℝ) : ℂ) * φ (y / t))‖
      ≤ ∫ y, Bf * Bg * (t⁻¹ * ‖φ (y / t)‖) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
          ((h1.const_mul t⁻¹).const_mul (Bf * Bg)) (Eventually.of_forall fun y => ?_)
        dsimp only
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht)]
        exact mul_le_mul (mul_le_mul (hBf _) (hBg _) (norm_nonneg _) hBf0) le_rfl (by positivity)
          (by positivity)
    _ = Bf * Bg * ∫ y, ‖φ y‖ := by
        rw [integral_const_mul, integral_const_mul, h2]
        field_simp

end PrimeBHT.TimeFrequency.RealLine

end
