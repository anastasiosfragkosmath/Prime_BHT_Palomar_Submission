module

public import PrimeBHT.Kernel
public import Mathlib.Analysis.Fourier.Convolution

/-!
# Fourier-side facts about the long kernel `K_{Q;τ}` (blueprint node N25 (b), (c))

* `IsSmoother c φ`: `φ` real even Schwartz, `∫ φ = 1`, `supp φ̂ ⊆ [-c, c]`.
* `exists_isSmoother`: such a `φ` exists for every `c > 0`.
* `fourier_smooth_kernelI`: `K̂(ξ) = φ̂(Nξ) ∑_{k=a}^{b} ψ̂(2^k ξ)` for `K = smooth φ N (kernelI χ a b)`.
* `fourier_smooth_kernelI_eq_zero`: `K̂(ξ) = 0` for `|ξ| > c / N`.
* `exists_schwartz_smooth_kernelI`: `K` is a Schwartz function.

The uniform symbol bounds (N25 (b), `e:kernel-BV`) are in `PrimeBHT/KernelFourier/Uniform.lean`
(with `Dyadic.lean`, `Symbol.lean` as helpers).
-/

@[expose] public section

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

namespace PrimeBHT.KernelFourier

/-- The smoothing function `φ` of N25: a real even Schwartz function with `∫ φ = 1` (`φ̂(0) = 1`)
whose Fourier transform is supported in `[-c, c]`. -/
structure IsSmoother (c : ℝ) (φ : 𝓢(ℝ, ℝ)) : Prop where
  even : ∀ x, φ (-x) = φ x
  integral_eq_one : ∫ x, φ x = 1
  fourier_eq_zero : ∀ ξ, c < |ξ| → 𝓕 (fun x => ((φ x : ℝ) : ℂ)) ξ = 0

theorem exists_isSmoother {c : ℝ} (hc : 0 < c) : ∃ φ : 𝓢(ℝ, ℝ), IsSmoother c φ := by
  let b : ContDiffBump (0 : ℝ) := ⟨c / 2, c, by positivity, by linarith⟩
  have hbc : ContDiff ℝ ∞ (fun x : ℝ => ((b x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hbs : HasCompactSupport (fun x : ℝ => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) (by simp)
  let g : 𝓢(ℝ, ℂ) := hbs.toSchwartzMap hbc
  have hg : ∀ x, g x = ((b x : ℝ) : ℂ) := fun x => rfl
  have hgneg : ∀ x, g (-x) = g x := fun x => by rw [hg, hg, b.neg]
  let φc : 𝓢(ℝ, ℂ) := 𝓕⁻ g
  have hFφc : 𝓕 (φc : ℝ → ℂ) = g :=
    congrArg (fun h : 𝓢(ℝ, ℂ) => (h : ℝ → ℂ))
      (FourierInvPair.fourier_fourierInv_eq (F := 𝓢(ℝ, ℂ)) g)
  have hFg_even : ∀ w, 𝓕 (g : ℝ → ℂ) (-w) = 𝓕 (g : ℝ → ℂ) w := by
    intro w
    have h1 := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ)) (g : ℝ → ℂ) w
    have h2 : ((g : ℝ → ℂ) ∘ (LinearIsometryEquiv.neg ℝ (E := ℝ))) = (g : ℝ → ℂ) := by
      funext x; exact hgneg x
    rw [h2] at h1
    rw [h1]; rfl
  have hφc_eq : ∀ x, φc x = 𝓕 (g : ℝ → ℂ) (-x) := fun x => by
    have h1 : φc x = 𝓕⁻ (g : ℝ → ℂ) x := congrFun (SchwartzMap.fourierInv_coe g) x
    rw [h1]; exact Real.fourierInv_eq_fourier_neg _ x
  have hconj : ∀ x, (starRingEnd ℂ) (φc x) = φc x := by
    intro x
    have key : (starRingEnd ℂ) (𝓕 (g : ℝ → ℂ) (-x)) = 𝓕 (g : ℝ → ℂ) x := by
      rw [Real.fourier_real_eq, Real.fourier_real_eq, ← integral_conj]
      refine integral_congr_ae (ae_of_all _ fun v => ?_)
      simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, map_mul,
        Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I, hg]
      congr 2
      push_cast; ring
    rw [hφc_eq, key, hFg_even]
  let φ : 𝓢(ℝ, ℝ) := SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM φc
  have hφ : ∀ x, φ x = (φc x).re := fun x => rfl
  have hreal : ∀ x, ((φ x : ℝ) : ℂ) = φc x := fun x => by
    rw [hφ]; exact Complex.conj_eq_iff_re.1 (hconj x)
  have hfun : (fun x => ((φ x : ℝ) : ℂ)) = (φc : ℝ → ℂ) := funext hreal
  refine ⟨φ, ⟨?_, ?_, ?_⟩⟩
  · intro x
    rw [hφ, hφ, hφc_eq, hφc_eq, neg_neg, hFg_even]
  · have h0 : 𝓕 (φc : ℝ → ℂ) 0 = ∫ v, φc v := by
      rw [Real.fourier_real_eq]; simp
    rw [hFφc] at h0
    have h1 : ∫ x, ((φ x : ℝ) : ℂ) = 1 := by
      simp only [hreal]
      rw [← h0, hg, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]; simp
    rw [integral_complex_ofReal] at h1
    exact_mod_cast h1
  · intro ξ hξ
    rw [hfun, hFφc, hg]
    have : (b ξ) = 0 := b.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hξ.le)
    rw [this]; simp

section Kernel

open PrimeBHT.Kernel
open scoped Convolution

variable {χ : ℝ → ℝ}

theorem _root_.PrimeBHT.Kernel.IsCutoff.contDiff_psiK (hχ : IsCutoff χ) (k : ℕ) :
    ContDiff ℝ ∞ (psiK χ k) := by
  unfold psiK
  exact (hχ.contDiff_psi.comp (contDiff_id.div_const _)).div_const _

theorem _root_.PrimeBHT.Kernel.IsCutoff.hasCompactSupport_psiK (hχ : IsCutoff χ) (k : ℕ) :
    HasCompactSupport (psiK χ k) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(2 : ℝ) ^ k) (b := (2 : ℝ) ^ k))
  intro t ht
  apply hχ.psiK_eq_zero_of_le_abs k
  by_contra h
  rw [not_le, abs_lt] at h
  exact ht ⟨h.1.le, h.2.le⟩

theorem _root_.PrimeBHT.Kernel.IsCutoff.contDiff_kernelI (hχ : IsCutoff χ) (a b : ℕ) :
    ContDiff ℝ ∞ (kernelI χ a b) := by
  unfold kernelI
  exact ContDiff.sum fun k _ => hχ.contDiff_psiK k

theorem _root_.PrimeBHT.Kernel.IsCutoff.hasCompactSupport_kernelI (hχ : IsCutoff χ) (a b : ℕ) :
    HasCompactSupport (kernelI χ a b) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(2 : ℝ) ^ b) (b := (2 : ℝ) ^ b))
  intro t ht
  unfold kernelI
  refine Finset.sum_eq_zero fun k hk => ?_
  apply hχ.psiK_eq_zero_of_le_abs k
  have hkb : k ≤ b := (Finset.mem_Icc.1 hk).2
  have h2 : (2 : ℝ) ^ k ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) hkb
  by_contra h
  rw [not_le, abs_lt] at h
  exact ht ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Real function viewed as a complex one. -/
theorem fourier_dilate (f : ℝ → ℝ) {N : ℝ} (hN : 0 < N) (ξ : ℝ) :
    𝓕 (fun y => ((dilate f N y : ℝ) : ℂ)) ξ = 𝓕 (fun y => ((f y : ℝ) : ℂ)) (N * ξ) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  have h : (fun y : ℝ => Real.fourierChar (-(y * ξ)) • ((dilate f N y : ℝ) : ℂ)) =
      fun y => (fun u : ℝ => (N⁻¹ : ℝ) • (Real.fourierChar (-(u * (N * ξ))) • ((f u : ℝ) : ℂ)))
        (y / N) := by
    funext y
    have : y / N * (N * ξ) = y * ξ := by field_simp
    simp only [this, dilate]
    simp only [Circle.smul_def, smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  rw [h, Measure.integral_comp_div (fun u : ℝ => (N⁻¹ : ℝ) • (Real.fourierChar (-(u * (N * ξ))) •
    ((f u : ℝ) : ℂ))) N, integral_smul, smul_smul, abs_of_pos hN,
    mul_inv_cancel₀ hN.ne', one_smul]

/-- The Fourier transform of `ψ` (complexified). -/
noncomputable def psiHat (χ : ℝ → ℝ) (ξ : ℝ) : ℂ := 𝓕 (fun t => ((psi χ t : ℝ) : ℂ)) ξ

theorem psiK_eq_dilate (χ : ℝ → ℝ) (k : ℕ) : psiK χ k = dilate (psi χ) ((2 : ℝ) ^ k) := by
  funext t
  simp only [psiK, dilate, div_eq_inv_mul]

/-- `(ψ_k)^(ξ) = ψ^(2^k ξ)`. -/
theorem fourier_psiK (χ : ℝ → ℝ) (k : ℕ) (ξ : ℝ) :
    𝓕 (fun t => ((psiK χ k t : ℝ) : ℂ)) ξ = psiHat χ (2 ^ k * ξ) := by
  rw [psiK_eq_dilate]
  exact fourier_dilate (psi χ) (by positivity) ξ

theorem integrable_psiK (hχ : IsCutoff χ) (k : ℕ) :
    MeasureTheory.Integrable (fun t => ((psiK χ k t : ℝ) : ℂ)) := by
  have := (Complex.ofRealCLM.contDiff.comp (hχ.contDiff_psiK k)).continuous.integrable_of_hasCompactSupport
    (μ := MeasureTheory.volume)
    ((hχ.hasCompactSupport_psiK k).comp_left (g := ((↑) : ℝ → ℂ)) (by simp))
  exact this

theorem integrable_fourierChar_smul {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    Integrable fun x : ℝ => Real.fourierChar (-(x * ξ)) • f x := by
  have h : Integrable fun x : ℝ => ((Real.fourierChar (-(x * ξ)) : Circle) : ℂ) * f x := by
    refine Integrable.bdd_mul hf ?_ (c := 1) (Filter.Eventually.of_forall fun x => ?_)
    · exact (by fun_prop : Continuous fun x : ℝ => ((Real.fourierChar (-(x * ξ)) : Circle) : ℂ)).aestronglyMeasurable
    · simp
  simpa [Circle.smul_def] using h

theorem integrable_kernelI (hχ : IsCutoff χ) (a b : ℕ) :
    MeasureTheory.Integrable (fun t => ((kernelI χ a b t : ℝ) : ℂ)) := by
  have := (Complex.ofRealCLM.contDiff.comp (hχ.contDiff_kernelI a b)).continuous.integrable_of_hasCompactSupport
    (μ := MeasureTheory.volume)
    ((hχ.hasCompactSupport_kernelI a b).comp_left (g := ((↑) : ℝ → ℂ)) (by simp))
  exact this

/-- `(∑_{k=a}^b ψ_k)^(ξ) = ∑_{k=a}^b ψ^(2^k ξ)`. -/
theorem fourier_kernelI (hχ : IsCutoff χ) (a b : ℕ) (ξ : ℝ) :
    𝓕 (fun t => ((kernelI χ a b t : ℝ) : ℂ)) ξ = ∑ k ∈ Finset.Icc a b, psiHat χ (2 ^ k * ξ) := by
  have h1 : (fun t => ((kernelI χ a b t : ℝ) : ℂ)) =
      fun t => ∑ k ∈ Finset.Icc a b, ((psiK χ k t : ℝ) : ℂ) := by
    funext t; simp [kernelI]
  rw [h1, Real.fourier_real_eq]
  simp_rw [Finset.smul_sum]
  rw [integral_finsetSum _ (fun k _ => integrable_fourierChar_smul (integrable_psiK hχ k) ξ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← fourier_psiK, Real.fourier_real_eq]

theorem ofReal_smooth (φ : ℝ → ℝ) (N : ℝ) (K : ℝ → ℝ) (x : ℝ) :
    ((smooth φ N K x : ℝ) : ℂ) =
      ((fun y => ((dilate φ N y : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun y => ((K y : ℝ) : ℂ))) x := by
  rw [convolution_def]
  simp only [smooth, ContinuousLinearMap.mul_apply']
  rw [← integral_complex_ofReal]
  simp

theorem fourier_smooth_kernelI (hχ : IsCutoff χ) (φ : 𝓢(ℝ, ℝ)) {N : ℝ} (hN : 0 < N) (a b : ℕ)
    (ξ : ℝ) :
    𝓕 (fun x => ((smooth φ N (kernelI χ a b) x : ℝ) : ℂ)) ξ =
      𝓕 (fun x => ((φ x : ℝ) : ℂ)) (N * ξ) * ∑ k ∈ Finset.Icc a b, psiHat χ (2 ^ k * ξ) := by
  have h : (fun x => ((smooth φ N (kernelI χ a b) x : ℝ) : ℂ)) =
      (fun y => ((dilate φ N y : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun y => ((kernelI χ a b y : ℝ) : ℂ)) := funext (ofReal_smooth _ _ _)
  rw [h]
  refine (Real.fourier_mul_convolution_eq (integrable_dilate φ hN).ofReal
    (integrable_kernelI hχ a b) ξ).trans ?_
  refine congrArg₂ (· * ·) ?_ ?_
  · exact fourier_dilate _ hN ξ
  · exact fourier_kernelI hχ a b ξ

/-- N25 (c): `K = φ_N * ∑_{k=a}^b ψ_k` is a Schwartz function. -/
theorem exists_schwartz_smooth_kernelI (hχ : IsCutoff χ) (φ : 𝓢(ℝ, ℝ)) {N : ℝ} (hN : 0 < N)
    (a b : ℕ) : ∃ S : 𝓢(ℝ, ℝ), (S : ℝ → ℝ) = smooth φ N (kernelI χ a b) := by
  let e : ℝ ≃L[ℝ] ℝ :=
    (LinearEquiv.smulOfNeZero ℝ ℝ N⁻¹ (inv_ne_zero hN.ne')).toContinuousLinearEquiv
  let D : 𝓢(ℝ, ℝ) := N⁻¹ • SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e φ
  have hD : ∀ y, D y = dilate φ N y := fun y => by
    simp [D, e, dilate, div_eq_inv_mul]
  let Dc : 𝓢(ℝ, ℂ) := SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM D
  have hDc : (Dc : ℝ → ℂ) = fun y => ((dilate φ N y : ℝ) : ℂ) := funext fun y => by
    simp [Dc, hD]
  have hbc : ContDiff ℝ ∞ (fun x : ℝ => ((kernelI χ a b x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hχ.contDiff_kernelI a b)
  have hbs : HasCompactSupport (fun x : ℝ => ((kernelI χ a b x : ℝ) : ℂ)) :=
    (hχ.hasCompactSupport_kernelI a b).comp_left (g := ((↑) : ℝ → ℂ)) (by simp)
  let Pc : 𝓢(ℝ, ℂ) := hbs.toSchwartzMap hbc
  have hPc : (Pc : ℝ → ℂ) = fun y => ((kernelI χ a b y : ℝ) : ℂ) := rfl
  let C : 𝓢(ℝ, ℂ) := SchwartzMap.convolution (𝕜 := ℂ) (ContinuousLinearMap.mul ℂ ℂ) Dc Pc
  refine ⟨SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM C, funext fun x => ?_⟩
  have hC : C x = ((smooth φ N (kernelI χ a b) x : ℝ) : ℂ) := by
    show SchwartzMap.convolution (𝕜 := ℂ) (ContinuousLinearMap.mul ℂ ℂ) Dc Pc x = _
    rw [SchwartzMap.convolution_apply, hDc, hPc, ofReal_smooth]
  show (C x).re = _
  rw [hC]; simp

end Kernel

end PrimeBHT.KernelFourier
