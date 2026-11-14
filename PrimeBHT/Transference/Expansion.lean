module

public import PrimeCarleson.Proof.Common.FourierR

/-!
# N42 (42b): the `T`-expansion

For Schwartz `φ₁, φ₂, φ₃` with compactly supported Fourier transforms, a Schwartz kernel `K`, a
bounded weight `w : ℤ → ℂ` and a real shift `s`,
`∑_{x ∈ ℤ} ∑_{n ∈ ℤ} K(n) w(n) φ₁(x-n) φ₂(x+n) conj(φ₃(x)) e(xs)
  = ∑_{k ∈ ℤ} ∫∫ φ̂₁(α) φ̂₂(β) conj(φ̂₃(α+β+s-k)) M(α-β) dα dβ`,
`M(θ) = ∑_n K(n) w(n) e(-nθ)` (blueprint N42 step 2, `e:chart-expanded`).

In the application `φ₁ = f_a`, `φ₂ = g_b`, `φ₃ = h_c`, `s = (a+b-c)/N` and
`w(n) = Λ_B(n) e(n(b-a)/N)`, so that `M(θ) = M_B(θ + (a-b)/N)` and the argument of `M_B` is
`(a-b)/N + α - β`, as in FINDINGS `e:chart-expanded`.

Proof order: (1) for real `x`, `∑_n K(n) w(n) φ₁(x-n) φ₂(x+n) = ∫ φ̂₁(α) φ̂₂(β) e(x(α+β)) M(α-β)`
(Fourier inversion, `∑_n`/`∫` swap); (2) Poisson summation in `x` for
`h(x) = (∑_n …)(x) conj(φ₃(x))`; (3) `ĥ(η) = ∫ φ̂₁ φ̂₂ M(α-β) conj(φ̂₃(α+β-η))` (Fubini), which is
compactly supported.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Asymptotics
open scoped FourierTransform Real SchwartzMap ComplexConjugate

namespace PrimeBHT.Transference

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-- The multiplier `M(θ) = ∑_n K(n) w(n) e(-nθ)`. -/
def multiplier (K : 𝓢(ℝ, ℂ)) (w : ℤ → ℂ) (θ : ℝ) : ℂ :=
  ∑' n : ℤ, K n * w n * e (-((n : ℝ) * θ))

theorem summable_norm_schwartz_int (K : 𝓢(ℝ, ℂ)) : Summable fun n : ℤ => ‖K n‖ := by
  have h := ((K.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite).norm_left
  refine summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two) ?_
  simpa [Function.comp_def] using h

section

variable {w : ℤ → ℂ} {C : ℝ} (hw : ∀ n, ‖w n‖ ≤ C) (K : 𝓢(ℝ, ℂ))
include hw

theorem norm_multiplier_term_le (n : ℤ) (θ : ℝ) :
    ‖K n * w n * e (-((n : ℝ) * θ))‖ ≤ ‖K n‖ * C := by
  rw [norm_mul, norm_mul, norm_e, mul_one]
  exact mul_le_mul_of_nonneg_left (hw n) (norm_nonneg _)

theorem continuous_multiplier : Continuous (multiplier K w) :=
  continuous_tsum (fun n => continuous_const.mul (continuous_e.comp (by fun_prop)))
    ((summable_norm_schwartz_int K).mul_right C) (norm_multiplier_term_le hw K)

theorem norm_multiplier_le (θ : ℝ) :
    ‖multiplier K w θ‖ ≤ ∑' n : ℤ, ‖K n‖ * C :=
  tsum_of_norm_bounded ((summable_norm_schwartz_int K).mul_right C).hasSum
    (norm_multiplier_term_le hw K · θ)

end

theorem integrable_mul_e {F : ℝ → ℂ} (hFc : Continuous F) (hF : Integrable F) {g : ℝ → ℝ}
    (hg : Continuous g) : Integrable fun α : ℝ => F α * e (g α) := by
  refine hF.norm.mono' ?_ (Eventually.of_forall fun α => ?_)
  · exact (hFc.mul (continuous_e.comp hg)).aestronglyMeasurable
  · rw [norm_mul, norm_e, mul_one]

section Expansion

variable {w : ℤ → ℂ} {C : ℝ} (hw : ∀ n, ‖w n‖ ≤ C) (K φ₁ φ₂ φ₃ : 𝓢(ℝ, ℂ))

/-- The amplitude `H(α, β) = φ̂₁(α) φ̂₂(β) M(α - β)`. -/
def amplitude (w : ℤ → ℂ) (p : ℝ × ℝ) : ℂ :=
  𝓕 (φ₁ : ℝ → ℂ) p.1 * 𝓕 (φ₂ : ℝ → ℂ) p.2 * multiplier K w (p.1 - p.2)

include hw

theorem continuous_amplitude : Continuous (amplitude K φ₁ φ₂ w) := by
  unfold amplitude
  have h1 : Continuous (𝓕 (φ₁ : ℝ → ℂ)) := (𝓕 φ₁).continuous
  have h2 : Continuous (𝓕 (φ₂ : ℝ → ℂ)) := (𝓕 φ₂).continuous
  exact ((h1.comp continuous_fst).mul (h2.comp continuous_snd)).mul
    ((continuous_multiplier hw K).comp (continuous_fst.sub continuous_snd))

theorem integrable_amplitude_mul {g : ℝ × ℝ → ℂ} (hg : Continuous g) {B : ℝ}
    (hB : ∀ p, ‖g p‖ ≤ B) :
    Integrable (fun p => amplitude K φ₁ φ₂ w p * g p) (volume.prod volume) := by
  set BM := ∑' n : ℤ, ‖K n‖ * C
  have hi : Integrable (fun p : ℝ × ℝ => ‖𝓕 (φ₁ : ℝ → ℂ) p.1‖ * ‖𝓕 (φ₂ : ℝ → ℂ) p.2‖)
      (volume.prod volume) :=
    ((𝓕 φ₁).integrable (μ := volume)).norm.mul_prod ((𝓕 φ₂).integrable (μ := volume)).norm
  refine (hi.const_mul (BM * B)).mono' ((continuous_amplitude hw K φ₁ φ₂).mul
    hg).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  unfold amplitude
  rw [norm_mul, norm_mul, norm_mul]
  have hM := norm_multiplier_le hw K (p.1 - p.2)
  have hgp := hB p
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB p)
  have hBM0 : 0 ≤ BM := (norm_nonneg _).trans hM
  have ha := norm_nonneg (𝓕 (φ₁ : ℝ → ℂ) p.1)
  have hb := norm_nonneg (𝓕 (φ₂ : ℝ → ℂ) p.2)
  calc ‖𝓕 (φ₁ : ℝ → ℂ) p.1‖ * ‖𝓕 (φ₂ : ℝ → ℂ) p.2‖ * ‖multiplier K w (p.1 - p.2)‖ * ‖g p‖
      ≤ ‖𝓕 (φ₁ : ℝ → ℂ) p.1‖ * ‖𝓕 (φ₂ : ℝ → ℂ) p.2‖ * BM * B := by gcongr
    _ = BM * B * (‖𝓕 (φ₁ : ℝ → ℂ) p.1‖ * ‖𝓕 (φ₂ : ℝ → ℂ) p.2‖) := by ring

/-- Step (1): for real `x`,
`∑_n K(n) w(n) φ₁(x-n) φ₂(x+n) = ∫ φ̂₁(α) φ̂₂(β) M(α-β) e(x(α+β)) d(α,β)`. -/
theorem tsum_kernel_mul_eq_integral (x : ℝ) :
    ∑' n : ℤ, K n * w n * (φ₁ (x - n) * φ₂ (x + n)) =
      ∫ p : ℝ × ℝ, amplitude K φ₁ φ₂ w p * e (x * (p.1 + p.2)) := by
  set F₁ := 𝓕 (φ₁ : ℝ → ℂ)
  set F₂ := 𝓕 (φ₂ : ℝ → ℂ)
  -- the `n`-th term as an integral over `ℝ²`
  set G : ℤ → ℝ × ℝ → ℂ := fun n p =>
    K n * w n * ((F₁ p.1 * e (p.1 * x + -(p.1 * n))) * (F₂ p.2 * e (p.2 * x + p.2 * n)))
  have hterm : ∀ n : ℤ, K n * w n * (φ₁ (x - n) * φ₂ (x + n)) =
      ∫ p, G n p ∂(volume.prod volume) := fun n => by
    simp only [G]
    rw [integral_const_mul, integral_prod_mul (μ := volume) (ν := volume)
      (fun α => F₁ α * e (α * x + -(α * n))) (fun β => F₂ β * e (β * x + β * n)),
      fourier_inversion_schwartz φ₁ (x - n), fourier_inversion_schwartz φ₂ (x + n)]
    congr 2
    · refine integral_congr_ae (Eventually.of_forall fun α => ?_)
      simp only [F₁]; congr 2; ring
    · refine integral_congr_ae (Eventually.of_forall fun β => ?_)
      simp only [F₂]; congr 2; ring
  have hint1 : ∀ n : ℤ, Integrable (fun α : ℝ => F₁ α * e (α * x + -(α * n))) := fun n => by
    exact integrable_mul_e (𝓕 φ₁).continuous (𝓕 φ₁).integrable (by fun_prop)
  have hint2 : ∀ n : ℤ, Integrable (fun β : ℝ => F₂ β * e (β * x + β * n)) := fun n => by
    exact integrable_mul_e (𝓕 φ₂).continuous (𝓕 φ₂).integrable (by fun_prop)
  have hGint : ∀ n, Integrable (G n) (volume.prod volume) := fun n =>
    ((hint1 n).mul_prod (hint2 n)).const_mul _
  have hGnorm : ∀ n, ∫ p, ‖G n p‖ ∂(volume.prod volume) =
      ‖K n‖ * ‖w n‖ * ((∫ α, ‖F₁ α‖) * ∫ β, ‖F₂ β‖) := fun n => by
    simp only [G, norm_mul, norm_e, mul_one]
    rw [integral_const_mul, integral_prod_mul (μ := volume) (ν := volume)
      (fun α => ‖F₁ α‖) (fun β => ‖F₂ β‖)]
  have hsum : Summable fun n => ∫ p, ‖G n p‖ ∂(volume.prod volume) := by
    simp_rw [hGnorm]
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (((summable_norm_schwartz_int K).mul_right C).mul_right
        ((∫ α, ‖F₁ α‖) * ∫ β, ‖F₂ β‖))
    have hA : 0 ≤ (∫ α, ‖F₁ α‖) * ∫ β, ‖F₂ β‖ :=
      mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
    gcongr
    exact hw n
  simp_rw [hterm]
  rw [integral_tsum_of_summable_integral_norm hGint hsum, Measure.volume_eq_prod]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [G, amplitude, multiplier]
  rw [mul_assoc, ← tsum_mul_right, ← tsum_mul_left]
  congr 1
  ext n
  have : e (-((n : ℝ) * (p.1 - p.2))) * e (x * (p.1 + p.2)) =
      e (p.1 * x + -(p.1 * n)) * e (p.2 * x + p.2 * n) := by
    rw [← e_add, ← e_add]; congr 1; ring
  calc K n * w n * (F₁ p.1 * e (p.1 * x + -(p.1 * n)) * (F₂ p.2 * e (p.2 * x + p.2 * n)))
      = F₁ p.1 * F₂ p.2 * (K n * w n) *
          (e (p.1 * x + -(p.1 * n)) * e (p.2 * x + p.2 * n)) := by ring
    _ = F₁ p.1 * F₂ p.2 * (K n * w n * e (-((n : ℝ) * (p.1 - p.2))) * e (x * (p.1 + p.2))) := by
        rw [← this]; ring


/-- The bilinear part `G(x) = ∑_n K(n) w(n) φ₁(x-n) φ₂(x+n)`, `x ∈ ℝ`. -/
def bilinearPart (w : ℤ → ℂ) (x : ℝ) : ℂ := ∑' n : ℤ, K n * w n * (φ₁ (x - n) * φ₂ (x + n))

theorem norm_bilinearPart_term_le (n : ℤ) (x : ℝ) :
    ‖K n * w n * (φ₁ (x - n) * φ₂ (x + n))‖ ≤
      ‖K n‖ * C * (SchwartzMap.seminorm ℝ 0 0 φ₁ * SchwartzMap.seminorm ℝ 0 0 φ₂) := by
  rw [norm_mul, norm_mul, norm_mul]
  have h1 := SchwartzMap.norm_le_seminorm ℝ φ₁ (x - n)
  have h2 := SchwartzMap.norm_le_seminorm ℝ φ₂ (x + n)
  have := hw n
  gcongr
  exact mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans this)

theorem continuous_bilinearPart : Continuous (bilinearPart K φ₁ φ₂ w) :=
  continuous_tsum (fun n => continuous_const.mul
      ((φ₁.continuous.comp (by fun_prop)).mul (φ₂.continuous.comp (by fun_prop))))
    (((summable_norm_schwartz_int K).mul_right C).mul_right _)
    (norm_bilinearPart_term_le hw K φ₁ φ₂)

theorem norm_bilinearPart_le (x : ℝ) :
    ‖bilinearPart K φ₁ φ₂ w x‖ ≤ ∑' n : ℤ,
      ‖K n‖ * C * (SchwartzMap.seminorm ℝ 0 0 φ₁ * SchwartzMap.seminorm ℝ 0 0 φ₂) :=
  tsum_of_norm_bounded (((summable_norm_schwartz_int K).mul_right C).mul_right _).hasSum
    (norm_bilinearPart_term_le hw K φ₁ φ₂ · x)

theorem isBigO_bilinearPart_mul_conj :
    (fun x : ℝ => bilinearPart K φ₁ φ₂ w x * conj (φ₃ x)) =O[cocompact ℝ]
      fun x : ℝ => |x| ^ (-(2 : ℝ)) := by
  refine IsBigO.trans ?_ (φ₃.isBigO_cocompact_rpow (-2))
  refine IsBigO.of_bound (∑' n : ℤ,
      ‖K n‖ * C * (SchwartzMap.seminorm ℝ 0 0 φ₁ * SchwartzMap.seminorm ℝ 0 0 φ₂))
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_right (norm_bilinearPart_le hw K φ₁ φ₂ x) (norm_nonneg _)

theorem integrable_amplitude : Integrable (amplitude K φ₁ φ₂ w) := by
  have := integrable_amplitude_mul hw K φ₁ φ₂ (g := fun _ => (1 : ℂ)) continuous_const
    (B := 1) (fun _ => by simp)
  simpa [Measure.volume_eq_prod] using this

/-- Step (3): `ĥ(η) = ∫ φ̂₁(α) φ̂₂(β) M(α-β) conj(φ̂₃(α+β-η))` for
`h(x) = G(x) conj(φ₃(x))`. -/
theorem fourier_bilinearPart_mul_conj (η : ℝ) :
    𝓕 (fun x : ℝ => bilinearPart K φ₁ φ₂ w x * conj (φ₃ x)) η =
      ∫ p : ℝ × ℝ, amplitude K φ₁ φ₂ w p * conj (𝓕 (φ₃ : ℝ → ℂ) (p.1 + p.2 - η)) := by
  rw [fourier_eq_integral_e]
  set f : ℝ → ℝ × ℝ → ℂ := fun x p =>
    e (-(x * η)) * conj (φ₃ x) * (amplitude K φ₁ φ₂ w p * e (x * (p.1 + p.2)))
  have h1 : ∀ x : ℝ, e (-(x * η)) * (bilinearPart K φ₁ φ₂ w x * conj (φ₃ x)) =
      ∫ p : ℝ × ℝ, f x p := fun x => by
    simp only [f, bilinearPart]
    rw [tsum_kernel_mul_eq_integral hw K φ₁ φ₂ x, integral_const_mul]
    ring
  have hfi : Integrable (Function.uncurry f) (volume.prod volume) := by
    have hb : Integrable (fun z : ℝ × (ℝ × ℝ) => ‖φ₃ z.1‖ * ‖amplitude K φ₁ φ₂ w z.2‖)
        (volume.prod volume) :=
      (φ₃.integrable (μ := volume)).norm.mul_prod (integrable_amplitude hw K φ₁ φ₂).norm
    refine hb.mono' ?_ (Eventually.of_forall fun z => ?_)
    · have hc : Continuous (Function.uncurry f) := by
        simp only [f, Function.uncurry_def]
        have ha := continuous_amplitude hw K φ₁ φ₂
        exact ((continuous_e.comp (by fun_prop)).mul
          (Complex.continuous_conj.comp (φ₃.continuous.comp continuous_fst))).mul
          ((ha.comp continuous_snd).mul (continuous_e.comp (by fun_prop)))
      exact hc.aestronglyMeasurable
    · simp only [f, Function.uncurry_def, norm_mul, norm_e, Complex.norm_conj, one_mul, mul_one]
      exact le_rfl
  simp_rw [h1]
  rw [integral_integral_swap hfi]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [f]
  rw [fourier_eq_integral_e, ← integral_conj, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hconj : ∀ t : ℝ, conj (e t) = e (-t) := fun t => by rw [e_neg]
  simp only [map_mul, hconj, neg_neg]
  have : e (x * (p.1 + p.2 - η)) = e (-(x * η)) * e (x * (p.1 + p.2)) := by
    rw [← e_add]; congr 1; ring
  rw [this]
  ring

/-- `ĥ` is compactly supported when `φ̂₁, φ̂₂, φ̂₃` are. -/
theorem hasCompactSupport_fourier_bilinearPart_mul_conj
    (h₁ : HasCompactSupport (𝓕 (φ₁ : ℝ → ℂ))) (h₂ : HasCompactSupport (𝓕 (φ₂ : ℝ → ℂ)))
    (h₃ : HasCompactSupport (𝓕 (φ₃ : ℝ → ℂ))) :
    HasCompactSupport (𝓕 (fun x : ℝ => bilinearPart K φ₁ φ₂ w x * conj (φ₃ x))) := by
  obtain ⟨R₁, -, hR₁⟩ := h₁.exists_pos_le_norm
  obtain ⟨R₂, -, hR₂⟩ := h₂.exists_pos_le_norm
  obtain ⟨R₃, -, hR₃⟩ := h₃.exists_pos_le_norm
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (R₁ + R₂ + R₃)) fun η hη => ?_
  rw [fourier_bilinearPart_mul_conj hw K φ₁ φ₂ φ₃ η]
  refine (integral_congr_ae (Eventually.of_forall fun p => ?_)).trans (integral_zero _ _)
  simp only [Metric.mem_closedBall, dist_zero_right, not_le, Real.norm_eq_abs] at hη
  simp only [amplitude]
  by_cases hp1 : R₁ ≤ |p.1|
  · rw [hR₁ p.1 hp1]; simp
  by_cases hp2 : R₂ ≤ |p.2|
  · rw [hR₂ p.2 hp2]; simp
  have : R₃ ≤ ‖p.1 + p.2 - η‖ := by
    rw [Real.norm_eq_abs]
    have h1 := abs_sub_abs_le_abs_sub η (p.1 + p.2)
    have h2 := abs_add_le p.1 p.2
    rw [abs_sub_comm] at h1
    linarith
  rw [hR₃ _ this]; simp

/-- **`T`-expansion** (N42 (42b), `e:chart-expanded` in abstract form): for Schwartz
`φ₁, φ₂, φ₃` with compactly supported Fourier transforms, a Schwartz kernel `K`, a bounded weight
`w` (`‖w n‖ ≤ C`) and `s ∈ ℝ`,
`∑_x ∑_n K(n) w(n) φ₁(x-n) φ₂(x+n) conj(φ₃(x)) e(xs)
  = ∑_k ∫∫ φ̂₁(α) φ̂₂(β) conj(φ̂₃(α+β+s-k)) M(α-β) dα dβ`. -/
theorem tsum_tsum_eq_tsum_integral_integral
    (h₁ : HasCompactSupport (𝓕 (φ₁ : ℝ → ℂ))) (h₂ : HasCompactSupport (𝓕 (φ₂ : ℝ → ℂ)))
    (h₃ : HasCompactSupport (𝓕 (φ₃ : ℝ → ℂ))) (s : ℝ) :
    ∑' x : ℤ, ∑' n : ℤ, K n * w n * φ₁ (x - n) * φ₂ (x + n) * conj (φ₃ x) * e (x * s) =
      ∑' k : ℤ, ∫ α : ℝ, ∫ β : ℝ, 𝓕 (φ₁ : ℝ → ℂ) α * 𝓕 (φ₂ : ℝ → ℂ) β *
        conj (𝓕 (φ₃ : ℝ → ℂ) (α + β + s - k)) * multiplier K w (α - β) := by
  set h : ℝ → ℂ := fun x => bilinearPart K φ₁ φ₂ w x * conj (φ₃ x)
  have hL : ∀ x : ℤ, ∑' n : ℤ, K n * w n * φ₁ (x - n) * φ₂ (x + n) * conj (φ₃ x) * e (x * s) =
      h x * e (-((x : ℝ) * -s)) := fun x => by
    simp only [h, bilinearPart]
    rw [mul_assoc, ← tsum_mul_right, show -((x : ℝ) * -s) = x * s by ring]
    congr 1; ext n; ring
  simp_rw [hL]
  have hc : Continuous h := (continuous_bilinearPart hw K φ₁ φ₂).mul
    (Complex.continuous_conj.comp φ₃.continuous)
  rw [tsum_mul_e_eq_tsum_fourier_add hc one_lt_two (isBigO_bilinearPart_mul_conj hw K φ₁ φ₂ φ₃)
    (isBigO_cocompact_of_hasCompactSupport
      (hasCompactSupport_fourier_bilinearPart_mul_conj hw K φ₁ φ₂ φ₃ h₁ h₂ h₃) _) (-s)]
  congr 1
  ext k
  simp only [h]
  rw [fourier_bilinearPart_mul_conj hw K φ₁ φ₂ φ₃, Measure.volume_eq_prod, integral_prod]
  · refine integral_congr_ae (Eventually.of_forall fun α => ?_)
    refine integral_congr_ae (Eventually.of_forall fun β => ?_)
    simp only [amplitude]
    have : α + β - (-s + k) = α + β + s - k := by ring
    rw [this]; ring
  · refine integrable_amplitude_mul hw K φ₁ φ₂ (B := SchwartzMap.seminorm ℝ 0 0 (𝓕 φ₃)) ?_
      fun p => ?_
    · exact Complex.continuous_conj.comp ((𝓕 φ₃).continuous.comp (by fun_prop))
    · rw [Complex.norm_conj]
      exact SchwartzMap.norm_le_seminorm ℝ (𝓕 φ₃) _

end Expansion

/-- An `N`-periodic weight is bounded. -/
theorem norm_le_sum_of_periodic {N : ℕ} [NeZero N] {w : ℤ → ℂ}
    (hw : Function.Periodic w (N : ℤ)) (n : ℤ) :
    ‖w n‖ ≤ ∑ r : ZMod N, ‖w (r.val : ℤ)‖ := by
  have hval : w ((n : ZMod N).val : ℤ) = w n := by
    rw [ZMod.val_intCast, Int.emod_def, mul_comm]
    have h := hw.int_mul (n / N) (n - n / N * N)
    simp only [Int.cast_id, sub_add_cancel] at h
    exact h.symm
  rw [← hval]
  exact Finset.single_le_sum (f := fun r : ZMod N => ‖w (r.val : ℤ)‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ _)

/-- **`T`-expansion** (N42 (42b)) for an `N`-periodic weight. -/
theorem tsum_tsum_eq_tsum_integral_integral_periodic {N : ℕ} [NeZero N] {w : ℤ → ℂ}
    (hw : Function.Periodic w (N : ℤ)) (K φ₁ φ₂ φ₃ : 𝓢(ℝ, ℂ))
    (h₁ : HasCompactSupport (𝓕 (φ₁ : ℝ → ℂ))) (h₂ : HasCompactSupport (𝓕 (φ₂ : ℝ → ℂ)))
    (h₃ : HasCompactSupport (𝓕 (φ₃ : ℝ → ℂ))) (s : ℝ) :
    ∑' x : ℤ, ∑' n : ℤ, K n * w n * φ₁ (x - n) * φ₂ (x + n) * conj (φ₃ x) * e (x * s) =
      ∑' k : ℤ, ∫ α : ℝ, ∫ β : ℝ, 𝓕 (φ₁ : ℝ → ℂ) α * 𝓕 (φ₂ : ℝ → ℂ) β *
        conj (𝓕 (φ₃ : ℝ → ℂ) (α + β + s - k)) * multiplier K w (α - β) :=
  tsum_tsum_eq_tsum_integral_integral (norm_le_sum_of_periodic hw) K φ₁ φ₂ φ₃ h₁ h₂ h₃ s

end PrimeBHT.Transference
