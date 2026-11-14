module

public import PrimeBHT.TimeFrequency.X2.Paraproduct.Estimates

/-!
# V14 (paraproduct) for tensor Schwartz data: the proof of the route check §1.3

`paraproduct_schwartz` is the inequality (PI) for tensor Schwartz data `tensorFun (f k)`, with the symbols
anchored at `A > 0` (constant uniform in `A`, `P`, `T`, `js`, `ε`).  Proof:

1. `σ₁ = lowRem + σ₁(0) ϑ_j` (`Symbols.lean`), `ϑ_j = 1` on `{|ξ| ≤ 2^{2J+1} A 2^{Jj}}`;
2. the **pull-out** (Parseval, `triL_tmS_eq_zero`): `∫ T(T_{ϑ_j} f₀, S_j f₁, S_j f₂) = ∫ T(f₀, S_j f₁, S_j f₂)`
   since the Fourier support of `S_j f₁ · conj S_j f₂` lies in `{|ξ| ≤ 2^{2J+1} A 2^{Jj}}` and `ϑ_j - 1` vanishes there;
3. the remainders `lowRem_j` form a Mikhlin family with constants independent of `js`: Cauchy-Schwarz in `j`
   (`enorm_sum_triL_le`);
4. the main term `Σ_j ε_j σ₁j(0) ∫ T(f₀, S_j f₁, S_j f₂)` is bounded by random-sign decoupling
   (`enorm_sum_triL_pull_le`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate Real ContDiff
open PrimeBHT.Statements PrimeBHT.TimeFrequency.X2.CZ

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

section Algebra

variable {P : ℕ}

theorem tmS_add_smul {ρ ϑ : ℝ → ℂ} (hρ : ρ.HasTemperateGrowth) (hϑ : ϑ.HasTemperateGrowth) (μ : ℂ)
    (f : TS P) : tmS (fun ξ => ρ ξ + μ * ϑ ξ) f = tmS ρ f + μ • tmS ϑ f := by
  have := tmS_sum (Finset.univ : Finset (Fin 2)) ![1, μ] ![ρ, ϑ]
    (fun i _ => by fin_cases i <;> simpa) f
  simpa [Fin.sum_univ_two] using this

theorem tmS_sub_one {ϑ : ℝ → ℂ} (hϑ : ϑ.HasTemperateGrowth) (f : TS P) :
    tmS (fun ξ => ϑ ξ - 1) f = tmS ϑ f - f := by
  have := tmS_sum (Finset.univ : Finset (Fin 2)) ![1, -1] ![ϑ, fun _ => 1]
    (fun i _ => by
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; exact hϑ
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one]
        exact Function.HasTemperateGrowth.const (1 : ℂ)) f
  simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_mul, neg_mul, tmS_one, one_smul, neg_smul] at this
  simpa [sub_eq_add_neg] using this

end Algebra

/-! ## Temperate growth of the symbols -/

theorem hasCompactSupport_lowCut {A : ℝ} (hA : 0 < A) (J : ℕ) (j : ℤ) : HasCompactSupport (lowCut A J j) :=
  hasCompactSupport_of_far (c := 0) (r := (2 : ℝ) ^ (2 * J + 2) * fscale A J j)
    (fun ξ hξ => lowCut_eq_zero hA (by simpa using hξ.le))

theorem hasTemperateGrowth_lowCut {A : ℝ} (hA : 0 < A) (J : ℕ) (j : ℤ) :
    (lowCut A J j).HasTemperateGrowth :=
  (hasCompactSupport_lowCut hA J j).hasTemperateGrowth (contDiff_lowCut A J j)

theorem IsLowSymbol.hasTemperateGrowth {A : ℝ} (hA : 0 < A) {J a₀ : ℕ} (ha₀ : 2 ≤ a₀) {j : ℤ} {σ : ℝ → ℂ}
    (h : IsLowSymbol A J a₀ j σ) : σ.HasTemperateGrowth :=
  (h.adapted hA ha₀).hasCompactSupport.hasTemperateGrowth h.1

theorem IsLPSymbol.hasTemperateGrowth {A : ℝ} {J a₀ : ℕ} (ha₀ : 2 ≤ a₀) {j : ℤ} {σ : ℝ → ℂ}
    (h : IsLPSymbol A J a₀ j σ) : σ.HasTemperateGrowth :=
  (h.adapted ha₀).hasCompactSupport.hasTemperateGrowth h.1

theorem hasCompactSupport_lowRem {A : ℝ} (hA : 0 < A) {J a₀ : ℕ} {j : ℤ} {σ : ℝ → ℂ}
    (h : IsLowSymbol A J a₀ j σ) : HasCompactSupport (lowRem A J j σ) :=
  hasCompactSupport_of_far (c := 0) (r := (2 : ℝ) ^ (2 * J + 2) * fscale A J j)
    (fun ξ hξ => lowRem_eq_zero_of_far hA h (by simpa using hξ))

theorem hasTemperateGrowth_lowRem {A : ℝ} (hA : 0 < A) {J a₀ : ℕ} {j : ℤ} {σ : ℝ → ℂ}
    (h : IsLowSymbol A J a₀ j σ) : (lowRem A J j σ).HasTemperateGrowth :=
  (hasCompactSupport_lowRem hA h).hasTemperateGrowth (contDiff_lowRem h.1)

/-! ## The decomposition and the pull-out for one scale -/

section PullOut

variable {P : ℕ} [NeZero P]

/-- **V14 Steps 1 and 3 for one scale**: `∫ T(T_{σ₁} f₀, S f₁, S' f₂) = ∫ T(T_{lowRem σ₁} f₀, S f₁, S' f₂) +
σ₁(0) ∫ T(f₀, S f₁, S' f₂)`. -/
theorem triL_low_decomp {A : ℝ} (hA : 0 < A) {J a₀ : ℕ} (ha₀ : 2 ≤ a₀) (T : Form P) {j : ℤ}
    {σ₁ σ₂ σ₃ : ℝ → ℂ} (h1 : IsLowSymbol A J a₀ j σ₁) (h2 : IsLPSymbol A J a₀ j σ₂)
    (h3 : IsLPSymbol A J a₀ j σ₃) (f₀ f₁ f₂ : TS P) :
    triL T (tmS σ₁ f₀) (tmS σ₂ f₁) (tmS σ₃ f₂) =
      triL T (tmS (lowRem A J j σ₁) f₀) (tmS σ₂ f₁) (tmS σ₃ f₂) +
        σ₁ 0 * triL T f₀ (tmS σ₂ f₁) (tmS σ₃ f₂) := by
  have hρ := hasTemperateGrowth_lowRem hA h1
  have hϑ := hasTemperateGrowth_lowCut hA J j
  have hσ₂t := h2.hasTemperateGrowth ha₀
  have hσ₃t := h3.hasTemperateGrowth ha₀
  have hsplit : σ₁ = fun ξ => lowRem A J j σ₁ ξ + σ₁ 0 * lowCut A J j ξ := by
    ext ξ; simp [lowRem]
  -- the Parseval step
  have hϑ1 : (fun ξ => lowCut A J j ξ - 1).HasTemperateGrowth :=
    hϑ.sub (Function.HasTemperateGrowth.const 1)
  have hpar : triL T (tmS (fun ξ => lowCut A J j ξ - 1) f₀) (tmS σ₂ f₁) (tmS σ₃ f₂) = 0 := by
    refine triL_tmS_eq_zero T hϑ1 hσ₂t hσ₃t (R := (2 : ℝ) ^ (2 * J) * fscale A J j) ?_ ?_ ?_ f₀ f₁ f₂
    · intro ξ hξ
      simp only [lowCut_eq_one hA (by rw [pow_succ]; linarith), sub_self]
    · intro ξ hξ
      exact h2.2.1 ξ (Or.inr (by rw [rpow_J_add_two]; exact hξ))
    · intro ξ hξ
      exact h3.2.1 ξ (Or.inr (by rw [rpow_J_add_two]; exact hξ))
  rw [tmS_sub_one hϑ] at hpar
  have e := congrArg (fun s => tmS s f₀) hsplit
  rw [e, tmS_add_smul hρ hϑ, map_add, map_smul]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  congr 1
  have hs : triL T (tmS (lowCut A J j) f₀) (tmS σ₂ f₁) (tmS σ₃ f₂) = triL T f₀ (tmS σ₂ f₁) (tmS σ₃ f₂) := by
    rw [map_sub, LinearMap.sub_apply, LinearMap.sub_apply, sub_eq_zero] at hpar
    exact hpar
  rw [hs]

end PullOut

/-! ## Monotonicity of the V08 constants -/

theorem CZ.VectorMikhlinSquare.mono {a₀ : ℕ} {q s C C' : ℝ} (h : VectorMikhlinSquare a₀ q s C) (hC : C ≤ C') :
    VectorMikhlinSquare a₀ q s C' := by
  intro P _ N n B hη f
  have hB : 0 ≤ B := (hη (fun _ => 1) (fun _ => by simp)).nonneg
  refine (h P N n B hη f).trans ?_
  gcongr

theorem CZ.VectorMikhlinStrong.mono {a₀ : ℕ} {q s C C' : ℝ} (h : VectorMikhlinStrong a₀ q s C) (hC : C ≤ C') :
    VectorMikhlinStrong a₀ q s C' := by
  intro P _ B σ hσ f
  have hB : 0 ≤ B := hσ.nonneg
  refine (h P B σ hσ f).trans ?_
  gcongr

/-! ## The theorem for tensor Schwartz data -/

/-- **V14 (PI) for tensor Schwartz data** (route check §1.3; symbols anchored at `A > 0`; constant uniform in
`A`, `P`, `T`, `js`, `ε`).  The three slots carry `tmult (σ_k j) (tensorFun (f k))`; the right side is the product
of the mixed norms `‖F_k‖_{L^{p_k}(ℝ; L^{s_k}(Y_P))}`, `s = (2, 2, u)`. -/
theorem paraproduct_schwartz (J a₀ : ℕ) (hJ : 1 ≤ J) (ha₀ : 3 ≤ a₀) {u : ℝ} (hu : 1 < u) {p : Fin 3 → ℝ}
    (hp : ∀ k, 1 < p k) (hpsum : ∑ k, 1 / p k = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 < A → ∀ (P : ℕ) [NeZero P] (T : Form P) (CT : ℝ), FormBound u T CT →
      ∀ (js : Finset ℤ) (ε : ℤ → ℂ), (∀ j, ‖ε j‖ ≤ 1) →
      ∀ (σ₁ σ₂ σ₃ : ℤ → ℝ → ℂ), (∀ j, IsLowSymbol A J a₀ j (σ₁ j)) → (∀ j, IsLPSymbol A J a₀ j (σ₂ j)) →
        (∀ j, IsLPSymbol A J a₀ j (σ₃ j)) → ∀ f : Fin 3 → ZMod P → 𝓢(ℝ, ℂ),
          ‖∑ j ∈ js, ε j * ∫ x, T (tmult (σ₁ j) (tensorFun (f 0)) x) (tmult (σ₂ j) (tensorFun (f 1)) x)
              (tmult (σ₃ j) (tensorFun (f 2)) x)‖ₑ ≤
            ENNReal.ofReal (C * CT) * (mixedENorm (p 0) 2 (tensorFun (f 0)) *
              mixedENorm (p 1) 2 (tensorFun (f 1)) * mixedENorm (p 2) u (tensorFun (f 2))) := by
  have hsum : 1 / p 0 + 1 / p 1 + 1 / p 2 = 1 := by simpa [Fin.sum_univ_three] using hpsum
  obtain ⟨Cs₀, hS₀⟩ := vectorMikhlinSquareStatement_three (p 0) 2 (hp 0) one_lt_two
  obtain ⟨Cs₁, hS₁⟩ := vectorMikhlinSquareStatement_three (p 1) 2 (hp 1) one_lt_two
  obtain ⟨Ct₁, hC₁⟩ := vectorMikhlinStrongStatement_three (p 1) 2 (hp 1) one_lt_two
  obtain ⟨Ct₂, hC₂⟩ := vectorMikhlinStrongStatement_three (p 2) u (hp 2) hu
  obtain ⟨K, hK0, hK⟩ := exists_isMikhlin_sum_lowRem
  set Cm : ℝ := ((PrimeCarleson.Proof.Common.maximalHLRConst (ENNReal.ofReal (p 2)) : NNReal) : ℝ) with hCm
  have hCm0 : 0 ≤ Cm := NNReal.coe_nonneg _
  set B₁ : ℝ := K * 2 ^ (6 * J + 7) with hB₁
  set B₂ : ℝ := 3 * 2 ^ (6 * J) with hB₂
  have hB₁0 : 0 ≤ B₁ := by positivity
  have hB₂0 : 0 ≤ B₂ := by positivity
  set Cs₀' := max Cs₀ 0
  set Cs₁' := max Cs₁ 0
  set Ct₁' := max Ct₁ 0
  set Ct₂' := max Ct₂ 0
  set Kx : ℝ := 60 * (2 : ℝ) ^ (2 * J) with hKx
  set C₁ : ℝ := Cs₀' * B₁ * (Cs₁' * B₂) * Kx * Cm with hC₁def
  set C₂ : ℝ := Ct₁' * B₂ * (Ct₂' * B₂) with hC₂def
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  intro A hA P _ T CT hT js ε hε σ₁ σ₂ σ₃ h1 h2 h3 f
  have hCT : 0 ≤ CT := nonneg_of_formBound (by linarith) hT
  have ha₀2 : 2 ≤ a₀ := by omega
  -- conversion of the left side
  have hLHS : ∀ j, ∫ x, T (tmult (σ₁ j) (tensorFun (f 0)) x) (tmult (σ₂ j) (tensorFun (f 1)) x)
      (tmult (σ₃ j) (tensorFun (f 2)) x) =
      triL T (tmS (σ₁ j) (f 0)) (tmS (σ₂ j) (f 1)) (tmS (σ₃ j) (f 2)) := by
    intro j
    have a1 := (h1 j).adapted hA ha₀2
    have a2 := (h2 j).adapted ha₀2
    have a3 := (h3 j).adapted ha₀2
    rw [triL_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Tfun]
    rw [tmult_tensorFun a1.1 a1.hasCompactSupport, tmult_tensorFun a2.1 a2.hasCompactSupport,
      tmult_tensorFun a3.1 a3.hasCompactSupport,
      tensorMult_eq_tensorFun ((h1 j).hasTemperateGrowth hA ha₀2),
      tensorMult_eq_tensorFun ((h2 j).hasTemperateGrowth ha₀2),
      tensorMult_eq_tensorFun ((h3 j).hasTemperateGrowth ha₀2)]
  simp_rw [hLHS]
  have hdec : ∀ j, triL T (tmS (σ₁ j) (f 0)) (tmS (σ₂ j) (f 1)) (tmS (σ₃ j) (f 2)) =
      triL T (tmS (lowRem A J j (σ₁ j)) (f 0)) (tmS (σ₂ j) (f 1)) (tmS (σ₃ j) (f 2)) +
        σ₁ j 0 * triL T (f 0) (tmS (σ₂ j) (f 1)) (tmS (σ₃ j) (f 2)) :=
    fun j => triL_low_decomp hA ha₀2 T (h1 j) (h2 j) (h3 j) (f 0) (f 1) (f 2)
  have hsplit : ∑ j ∈ js, ε j * triL T (tmS (σ₁ j) (f 0)) (tmS (σ₂ j) (f 1)) (tmS (σ₃ j) (f 2)) =
      ∑ j ∈ js, ε j * triL T (tmS (lowRem A J j (σ₁ j)) (f 0)) (tmS (σ₂ j) (f 1)) (tmS (σ₃ j) (f 2)) +
        ∑ j ∈ js, (ε j * σ₁ j 0) * triL T (f 0) (tmS (σ₂ j) (f 1)) (tmS (σ₃ j) (f 2)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hdec j]; ring
  rw [hsplit]
  refine (enorm_add_le _ _).trans ?_
  -- the symbol families
  have hB₁' : ∀ η : ℤ → ℂ, (∀ j, ‖η j‖ ≤ 1) →
      IsMikhlin 3 B₁ (fun ξ => ∑ j ∈ js, η j * lowRem A J j (σ₁ j) ξ) :=
    fun η hη => hK A hA J hJ a₀ ha₀ js η hη σ₁ h1
  have hB₂' : ∀ η : ℤ → ℂ, (∀ j, ‖η j‖ ≤ 1) → IsMikhlin 3 B₂ (fun ξ => ∑ j ∈ js, η j * σ₂ j ξ) :=
    fun η hη => isMikhlin_sum_lp hA hJ ha₀ js η hη σ₂ h2
  have hB₃' : ∀ η : ℤ → ℂ, (∀ j, ‖η j‖ ≤ 1) → IsMikhlin 3 B₂ (fun ξ => ∑ j ∈ js, η j * σ₃ j ξ) :=
    fun η hη => isMikhlin_sum_lp hA hJ ha₀ js η hη σ₃ h3
  have hc : ∀ j, ‖ε j * σ₁ j 0‖ ≤ 1 := by
    intro j
    rw [norm_mul]
    have h0 : ‖σ₁ j 0‖ ≤ 1 := by simpa using (h1 j).2.2 0 (Nat.zero_le _) 0
    calc ‖ε j‖ * ‖σ₁ j 0‖ ≤ 1 * 1 := mul_le_mul (hε j) h0 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have E₁ := enorm_sum_triL_le hA hu hT (hp 0) (hp 1) (hp 2) hsum (hS₀.mono (le_max_left Cs₀ 0))
    (hS₁.mono (le_max_left Cs₁ 0)) js ε hε (fun j => lowRem A J j (σ₁ j)) σ₂ σ₃
    (fun j => hasTemperateGrowth_lowRem hA (h1 j)) (fun j => (h2 j).hasTemperateGrowth ha₀2)
    (fun j => (h3 j).adapted ha₀2) hB₁' hB₂' (f 0) (f 1) (f 2)
  have E₂ := enorm_sum_triL_pull_le (by linarith) hT (by linarith [hp 0]) (hp 1) (hp 2) hsum
    (hC₁.mono (le_max_left Ct₁ 0)) (hC₂.mono (le_max_left Ct₂ 0)) js (fun j => ε j * σ₁ j 0) hc σ₂ σ₃
    (fun j => (h2 j).hasTemperateGrowth ha₀2) (fun j => (h3 j).hasTemperateGrowth ha₀2) hB₂' hB₃'
    (f 0) (f 1) (f 2)
  have hCm' : ((PrimeCarleson.Proof.Common.maximalHLRConst (ENNReal.ofReal (p 2)) : NNReal) : ℝ≥0∞) =
      ENNReal.ofReal Cm := (ENNReal.ofReal_coe_nnreal).symm
  rw [hCm'] at E₁
  have hKx0 : 0 ≤ Kx := by positivity
  have hCs₀ : 0 ≤ Cs₀' := le_max_right _ _
  have hCs₁ : 0 ≤ Cs₁' := le_max_right _ _
  have hCt₁ : 0 ≤ Ct₁' := le_max_right _ _
  have hCt₂ : 0 ≤ Ct₂' := le_max_right _ _
  have e1 : ENNReal.ofReal (C₁ * CT) = ENNReal.ofReal CT * ENNReal.ofReal (Cs₀' * B₁) *
      ENNReal.ofReal (Cs₁' * B₂) * ENNReal.ofReal Kx * ENNReal.ofReal Cm := by
    rw [← ENNReal.ofReal_mul hCT, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [hC₁def]
    ring
  have e2 : ENNReal.ofReal (C₂ * CT) = ENNReal.ofReal CT * (ENNReal.ofReal (Ct₁' * B₂) *
      ENNReal.ofReal (Ct₂' * B₂)) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hCT]
    congr 1
    simp only [hC₂def]
    ring
  have hC₁nn : 0 ≤ C₁ := by positivity
  have hC₂nn : 0 ≤ C₂ := by positivity
  calc _ ≤ _ := add_le_add E₁ E₂
    _ = (ENNReal.ofReal (C₁ * CT) + ENNReal.ofReal (C₂ * CT)) *
        (mixedENorm (p 0) 2 (tensorFun (f 0)) * mixedENorm (p 1) 2 (tensorFun (f 1)) *
          mixedENorm (p 2) u (tensorFun (f 2))) := by
        rw [e1, e2]; ring
    _ = ENNReal.ofReal ((C₁ + C₂) * CT) * (mixedENorm (p 0) 2 (tensorFun (f 0)) *
        mixedENorm (p 1) 2 (tensorFun (f 1)) * mixedENorm (p 2) u (tensorFun (f 2))) := by
        rw [← ENNReal.ofReal_add (mul_nonneg hC₁nn hCT) (mul_nonneg hC₂nn hCT)]
        congr 2
        ring

/-! ## The symmetric case (overlapping slot 2) -/

/-- Swapping the two Hilbert slots of a frozen form. -/
def Form.swap12 {P : ℕ} (T : Form P) : Form P := LinearMap.flip T

theorem Form.swap12_apply {P : ℕ} (T : Form P) (F G H : ZMod P → ℂ) : T.swap12 F G H = T G F H := rfl

theorem FormBound.swap12 {P : ℕ} [NeZero P] {u CT : ℝ} {T : Form P} (h : FormBound u T CT) :
    FormBound u T.swap12 CT := by
  intro F G H
  rw [Form.swap12_apply]
  have := h G F H
  calc ‖T G F H‖ ≤ CT * yNorm 2 G * yNorm 2 F * yNorm u H := this
    _ = CT * yNorm 2 F * yNorm 2 G * yNorm u H := by ring

end PrimeBHT.TimeFrequency.X2
