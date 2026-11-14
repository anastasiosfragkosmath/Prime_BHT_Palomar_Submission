module

public import PrimeBHT.TimeFrequency.X2.Paraproduct.Tensor
public import PrimeBHT.TimeFrequency.X2.FourierSupport

/-!
# X2, node V05-2 (R2): the trilinear Parseval identity for `tmult`

`parseval3`: for Schwartz `g₁ g₂ g₃`: `∫ g₁ (g₂ conj g₃) = ∫∫ ĝ₁(ξ₁) ĝ₂(ξ₂) conj ĝ₃(ξ₁+ξ₂)`.
`integral_form_tmult`: for smooth compactly supported `m₁ m₂ m₃` and tensor Schwartz data,
`∫ Π(T_{m₁}F₁, T_{m₂}F₂, T_{m₃}F₃)(x) dx = ∫∫ m₁(ξ₁) m₂(ξ₂) conj m₃(ξ₁+ξ₂) Π(F̂₁(ξ₁), F̂₂(ξ₂), F̂₃(ξ₁+ξ₂))`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate Real ContDiff ENNReal
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Disc

theorem integrable_parseval_kernel (g₁ g₂ g₃ : 𝓢(ℝ, ℂ)) :
    Integrable (fun ξ : ℝ × ℝ => 𝓕 (⇑g₁) ξ.1 * 𝓕 (⇑g₂) ξ.2 * (starRingEnd ℂ) (𝓕 (⇑g₃) (ξ.1 + ξ.2)))
      (volume.prod volume) := by
  have h12 : Integrable (fun ξ : ℝ × ℝ => 𝓕 (⇑g₁) ξ.1 * 𝓕 (⇑g₂) ξ.2) (volume.prod volume) :=
    Integrable.mul_prod (integrable_fourier_schwartz g₁) (integrable_fourier_schwartz g₂)
  obtain ⟨C, hC⟩ := schwartz_bdd (𝓕 g₃)
  have hc : Continuous fun ξ : ℝ × ℝ => (starRingEnd ℂ) (𝓕 (⇑g₃) (ξ.1 + ξ.2)) := by
    have : Continuous (𝓕 (⇑g₃)) := by
      have := (𝓕 g₃ : 𝓢(ℝ, ℂ)).continuous
      rwa [SchwartzMap.fourier_coe] at this
    exact Complex.continuous_conj.comp (this.comp (continuous_fst.add continuous_snd))
  refine h12.mul_bdd (c := C) hc.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Complex.norm_conj]
  have := hC (ξ.1 + ξ.2)
  rwa [SchwartzMap.fourier_coe] at this

theorem parseval3 (g₁ g₂ g₃ : 𝓢(ℝ, ℂ)) :
    ∫ x, g₁ x * (g₂ x * (starRingEnd ℂ) (g₃ x)) =
      ∫ ξ : ℝ × ℝ, 𝓕 (⇑g₁) ξ.1 * 𝓕 (⇑g₂) ξ.2 * (starRingEnd ℂ) (𝓕 (⇑g₃) (ξ.1 + ξ.2)) := by
  set H₁ : 𝓢(ℝ, ℂ) := 𝓕⁻ g₁ with hH₁
  have hw := integrable_mul_conj g₂ g₃
  have hh1 : (⇑g₁ : ℝ → ℂ) = 𝓕 (⇑H₁) := by
    have : 𝓕 H₁ = g₁ := FourierTransform.fourier_fourierInv_eq g₁
    rw [← SchwartzMap.fourier_coe, this]
  have key : ∫ ξ, 𝓕 (⇑H₁) ξ * (g₂ ξ * (starRingEnd ℂ) (g₃ ξ)) =
      ∫ x, H₁ x * 𝓕 (fun x => g₂ x * (starRingEnd ℂ) (g₃ x)) x := by
    simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner H₁.integrable hw
  have e1 : ∫ x, g₁ x * (g₂ x * (starRingEnd ℂ) (g₃ x)) = ∫ ξ, 𝓕 (⇑H₁) ξ * (g₂ ξ * (starRingEnd ℂ) (g₃ ξ)) := by
    rw [hh1]
  have hH : ∀ x, H₁ x = 𝓕 (⇑g₁) (-x) := by
    intro x
    have := congrFun (SchwartzMap.fourierInv_coe g₁) x
    rw [hH₁, this, Real.fourierInv_eq_fourier_neg]
  rw [e1, key]
  simp_rw [fourier_mul_conj_apply, hH]
  -- substitute x ↦ -x
  have e2 : ∫ x : ℝ, 𝓕 (⇑g₁) (-x) * ∫ ζ, 𝓕 (⇑g₂) ζ * (starRingEnd ℂ) (𝓕 (⇑g₃) (ζ - x)) =
      ∫ y : ℝ, 𝓕 (⇑g₁) y * ∫ ζ, 𝓕 (⇑g₂) ζ * (starRingEnd ℂ) (𝓕 (⇑g₃) (ζ + y)) := by
    rw [← integral_neg_eq_self (fun y : ℝ => 𝓕 (⇑g₁) y * ∫ ζ, 𝓕 (⇑g₂) ζ * (starRingEnd ℂ) (𝓕 (⇑g₃) (ζ + y)))]
    simp only [← sub_eq_add_neg]
  rw [e2, Measure.volume_eq_prod, integral_prod _ (integrable_parseval_kernel g₁ g₂ g₃)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
  simp only [add_comm ζ y]
  ring

section Vector

variable {P : ℕ} [NeZero P]

theorem tensorFourier_eq_sum (f : TS P) (ξ : ℝ) :
    tensorFourier f ξ = ∑ A, 𝓕 (⇑(f A)) ξ • yChar A := by
  ext y
  simp [tensorFourier, yChar, Finset.sum_apply]

theorem tmult_tensorFun_eq {σ : ℝ → ℂ} (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ) (f : TS P) (x : ℝ) :
    tmult σ (tensorFun f) x = tensorFun (tmS σ f) x := by
  have hT : σ.HasTemperateGrowth := hc.hasTemperateGrowth hσ
  rw [tmult_tensorFun hσ hc, tensorMult_eq_tensorFun hT]

/-- **R2.**  The trilinear Parseval identity for `tmult` on tensor Schwartz data. -/
theorem integral_form_tmult (T : Form P) {m₁ m₂ m₃ : ℝ → ℂ}
    (h₁ : ContDiff ℝ ∞ m₁) (c₁ : HasCompactSupport m₁) (h₂ : ContDiff ℝ ∞ m₂) (c₂ : HasCompactSupport m₂)
    (h₃ : ContDiff ℝ ∞ m₃) (c₃ : HasCompactSupport m₃) (f₁ f₂ f₃ : TS P) :
    ∫ x, T (tmult m₁ (tensorFun f₁) x) (tmult m₂ (tensorFun f₂) x) (tmult m₃ (tensorFun f₃) x) =
      ∫ ξ : ℝ × ℝ, m₁ ξ.1 * m₂ ξ.2 * (starRingEnd ℂ) (m₃ (ξ.1 + ξ.2)) *
        T (tensorFourier f₁ ξ.1) (tensorFourier f₂ ξ.2) (tensorFourier f₃ (ξ.1 + ξ.2)) := by
  have hLHS : (fun x => T (tmult m₁ (tensorFun f₁) x) (tmult m₂ (tensorFun f₂) x) (tmult m₃ (tensorFun f₃) x)) =
      Tfun T (tmS m₁ f₁) (tmS m₂ f₂) (tmS m₃ f₃) := by
    funext x
    unfold Tfun
    rw [tmult_tensorFun_eq h₁ c₁, tmult_tensorFun_eq h₂ c₂, tmult_tensorFun_eq h₃ c₃]
  rw [hLHS, integral_Tfun]
  have hpt : ∀ ξ : ℝ × ℝ, m₁ ξ.1 * m₂ ξ.2 * (starRingEnd ℂ) (m₃ (ξ.1 + ξ.2)) *
        T (tensorFourier f₁ ξ.1) (tensorFourier f₂ ξ.2) (tensorFourier f₃ (ξ.1 + ξ.2)) =
      ∑ c, ∑ b, ∑ a, T (yChar a) (yChar b) (yChar c) *
        (𝓕 (⇑(tmS m₁ f₁ a)) ξ.1 * 𝓕 (⇑(tmS m₂ f₂ b)) ξ.2 *
          (starRingEnd ℂ) (𝓕 (⇑(tmS m₃ f₃ c)) (ξ.1 + ξ.2))) := by
    intro ξ
    rw [tensorFourier_eq_sum, tensorFourier_eq_sum, tensorFourier_eq_sum, T_expand, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hm₁ : m₁.HasTemperateGrowth := c₁.hasTemperateGrowth h₁
    have hm₂ : m₂.HasTemperateGrowth := c₂.hasTemperateGrowth h₂
    have hm₃ : m₃.HasTemperateGrowth := c₃.hasTemperateGrowth h₃
    simp only [tmS, fourier_multSch hm₁, fourier_multSch hm₂, fourier_multSch hm₃, map_mul]
    ring
  simp_rw [hpt]
  have hint : ∀ (a b c : ZMod P), Integrable (fun ξ : ℝ × ℝ => T (yChar a) (yChar b) (yChar c) *
        (𝓕 (⇑(tmS m₁ f₁ a)) ξ.1 * 𝓕 (⇑(tmS m₂ f₂ b)) ξ.2 *
          (starRingEnd ℂ) (𝓕 (⇑(tmS m₃ f₃ c)) (ξ.1 + ξ.2)))) volume := by
    intro a b c
    have := integrable_parseval_kernel (tmS m₁ f₁ a) (tmS m₂ f₂ b) (tmS m₃ f₃ c)
    rw [← Measure.volume_eq_prod] at this
    exact this.const_mul _
  rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun b _ => integrable_finsetSum _ fun a _ => hint a b c]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_finsetSum _ fun b _ => integrable_finsetSum _ fun a _ => hint a b c]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_finsetSum _ fun a _ => hint a b c]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_const_mul, Measure.volume_eq_prod]
  congr 1
  exact parseval3 (tmS m₁ f₁ a) (tmS m₂ f₂ b) (tmS m₃ f₃ c)

/-- Integrability of the model integrand on tensor Schwartz data. -/
theorem integrable_T_tmult (T : Form P) {m₁ m₂ m₃ : ℝ → ℂ}
    (h₁ : ContDiff ℝ ∞ m₁) (c₁ : HasCompactSupport m₁) (h₂ : ContDiff ℝ ∞ m₂) (c₂ : HasCompactSupport m₂)
    (h₃ : ContDiff ℝ ∞ m₃) (c₃ : HasCompactSupport m₃) (f₁ f₂ f₃ : TS P) :
    Integrable (fun x => T (tmult m₁ (tensorFun f₁) x) (tmult m₂ (tensorFun f₂) x) (tmult m₃ (tensorFun f₃) x)) := by
  have hLHS : (fun x => T (tmult m₁ (tensorFun f₁) x) (tmult m₂ (tensorFun f₂) x) (tmult m₃ (tensorFun f₃) x)) =
      Tfun T (tmS m₁ f₁) (tmS m₂ f₂) (tmS m₃ f₃) := by
    funext x
    unfold Tfun
    rw [tmult_tensorFun_eq h₁ c₁, tmult_tensorFun_eq h₂ c₂, tmult_tensorFun_eq h₃ c₃]
  rw [hLHS]
  exact integrable_Tfun T _ _ _

end Vector

end PrimeBHT.TimeFrequency.X2.Disc
