module

public import PrimeBHT.KernelFourier
public import PrimeBHT.KernelFourier.Symbol

/-!
# Uniform symbol bounds for `K̂_{Q;τ}` (blueprint N25 (b), `e:kernel-BV`)

For `K = φ_N * ∑_{k=a}^{b} ψ_k`: for every `j` there is `A_j(φ, χ, j)` (independent of `N, a, b`) with
`|t|^j ‖∂^j K̂(t)‖ ≤ A_j` for all `t ≠ 0`.
-/

@[expose] public section

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

namespace PrimeBHT.KernelFourier

open PrimeBHT.Kernel

variable {χ : ℝ → ℝ}

/-- `ψ` (complexified) as a Schwartz function. -/
noncomputable def psiS (hχ : IsCutoff χ) : 𝓢(ℝ, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun t => ((psi χ t : ℝ) : ℂ))
    (hχ.hasCompactSupport_psi.comp_left (g := ((↑) : ℝ → ℂ)) (by simp))
    (Complex.ofRealCLM.contDiff.comp hχ.contDiff_psi)

theorem coe_fourier_psiS (hχ : IsCutoff χ) :
    ((𝓕 (psiS hχ) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = psiHat χ := rfl

theorem psiHat_zero (hχ : IsCutoff χ) : psiHat χ 0 = 0 := by
  unfold psiHat
  rw [Real.fourier_real_eq]
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul]
  rw [integral_complex_ofReal]
  have : ∫ t, psi χ t = 0 := by
    have h := integral_neg_eq_self (psi χ) volume
    simp only [hχ.psi_neg, integral_neg] at h
    linarith
  rw [this]; simp

/-- The constants for `ψ̂`: `S_{i+1,i} + S_{0,i} + S_{0,1}` (Schwartz seminorms of `ψ̂`). -/
noncomputable def psiConst (hχ : IsCutoff χ) (i : ℕ) : ℝ :=
  SchwartzMap.seminorm ℝ (i + 1) i (𝓕 (psiS hχ) : 𝓢(ℝ, ℂ)) +
    SchwartzMap.seminorm ℝ 0 i (𝓕 (psiS hχ) : 𝓢(ℝ, ℂ)) +
    SchwartzMap.seminorm ℝ 0 1 (𝓕 (psiS hχ) : 𝓢(ℝ, ℂ))

theorem psiConst_nonneg (hχ : IsCutoff χ) (i : ℕ) : 0 ≤ psiConst hχ i := by
  unfold psiConst
  exact add_nonneg (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) (apply_nonneg _ _)

/-- `‖ψ̂(u)‖ ≤ S_{0,1} |u|` (mean value theorem, `ψ̂(0) = 0`). -/
theorem norm_psiHat_le (hχ : IsCutoff χ) (u : ℝ) :
    ‖psiHat χ u‖ ≤ SchwartzMap.seminorm ℝ 0 1 (𝓕 (psiS hχ) : 𝓢(ℝ, ℂ)) * |u| := by
  set Ψ : 𝓢(ℝ, ℂ) := 𝓕 (psiS hχ) with hΨ
  have hd : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ (Ψ : ℝ → ℂ) x := fun x _ =>
    (Ψ.differentiableAt)
  have hb : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv (Ψ : ℝ → ℂ) x‖ ≤
      SchwartzMap.seminorm ℝ 0 1 Ψ := fun x _ => by
    have := SchwartzMap.le_seminorm' ℝ 0 1 Ψ x
    simpa [iteratedDeriv_one] using this
  have := Convex.norm_image_sub_le_of_norm_deriv_le hd hb convex_univ (Set.mem_univ 0)
    (Set.mem_univ u)
  have h0 : (Ψ : ℝ → ℂ) 0 = 0 := psiHat_zero hχ
  rw [h0, sub_zero, sub_zero, Real.norm_eq_abs] at this
  exact this

theorem psiHat_dyadic_bound (hχ : IsCutoff χ) (i : ℕ) (u : ℝ) (hu : u ≠ 0) :
    |u| ^ i * ‖iteratedDeriv i (psiHat χ) u‖ ≤ psiConst hχ i * min |u| |u|⁻¹ := by
  set Ψ : 𝓢(ℝ, ℂ) := 𝓕 (psiS hχ) with hΨ
  have hcoe : (psiHat χ) = (Ψ : ℝ → ℂ) := (coe_fourier_psiS hχ).symm
  rw [hcoe]
  have hu0 : 0 < |u| := abs_pos.2 hu
  have hS1 := SchwartzMap.le_seminorm' ℝ (i + 1) i Ψ u
  have hS2 := SchwartzMap.le_seminorm' ℝ 0 i Ψ u
  have hS3 : ‖(Ψ : ℝ → ℂ) u‖ ≤ SchwartzMap.seminorm ℝ 0 1 Ψ * |u| := by
    have := norm_psiHat_le hχ u
    rw [hcoe] at this
    exact this
  have hn : 0 ≤ ‖iteratedDeriv i (Ψ : ℝ → ℂ) u‖ := norm_nonneg _
  have hc1 : 0 ≤ SchwartzMap.seminorm ℝ (i + 1) i Ψ := apply_nonneg _ _
  have hc2 : 0 ≤ SchwartzMap.seminorm ℝ 0 i Ψ := apply_nonneg _ _
  have hc3 : 0 ≤ SchwartzMap.seminorm ℝ 0 1 Ψ := apply_nonneg _ _
  rcases le_or_gt 1 |u| with h | h
  · have hmin : min |u| |u|⁻¹ = |u|⁻¹ :=
      min_eq_right ((inv_le_one_of_one_le₀ h).trans h)
    rw [hmin]
    have e : |u| ^ i * ‖iteratedDeriv i (Ψ : ℝ → ℂ) u‖ =
        (|u| ^ (i + 1) * ‖iteratedDeriv i (Ψ : ℝ → ℂ) u‖) * |u|⁻¹ := by
      field_simp
      ring
    rw [e]
    have : 0 ≤ |u|⁻¹ := by positivity
    unfold psiConst
    calc (|u| ^ (i + 1) * ‖iteratedDeriv i (Ψ : ℝ → ℂ) u‖) * |u|⁻¹
        ≤ SchwartzMap.seminorm ℝ (i + 1) i Ψ * |u|⁻¹ := by gcongr
      _ ≤ _ := by nlinarith
  · have hmin : min |u| |u|⁻¹ = |u| :=
      min_eq_left (h.le.trans (one_le_inv₀ hu0 |>.2 h.le))
    rw [hmin]
    unfold psiConst
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [pow_zero, one_mul]
      simp only [iteratedDeriv_zero]
      nlinarith
    · have hp : |u| ^ i ≤ |u| := pow_le_of_le_one hu0.le h.le hi.ne'
      simp only [pow_zero, one_mul] at hS2
      calc |u| ^ i * ‖iteratedDeriv i (Ψ : ℝ → ℂ) u‖
          ≤ |u| * SchwartzMap.seminorm ℝ 0 i Ψ := by gcongr
        _ ≤ _ := by nlinarith

/-- `φ̂` (complexified) as a Schwartz function. -/
noncomputable def phiHatS (φ : 𝓢(ℝ, ℝ)) : 𝓢(ℝ, ℂ) :=
  𝓕 (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φ : 𝓢(ℝ, ℂ))

/-- The constant `A_j` of the uniform symbol bound; it depends on `χ`, `φ`, `j` only. -/
noncomputable def symbolConst (hχ : IsCutoff χ) (φ : 𝓢(ℝ, ℝ)) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
    SchwartzMap.seminorm ℝ i i (phiHatS φ) * (6 * psiConst hχ (j - i))

/-- **N25 (b), `e:kernel-BV`**: for every `j`, `|t|^j ‖∂^j K̂(t)‖ ≤ A_j(χ, φ, j)` for all `t ≠ 0`,
uniformly in `N > 0` and in the scales `a, b`, where `K = φ_N * ∑_{k=a}^b ψ_k`. -/
theorem symbol_bound (hχ : IsCutoff χ) (φ : 𝓢(ℝ, ℝ)) (j : ℕ) {N : ℝ} (hN : 0 < N) (a b : ℕ)
    {t : ℝ} (ht : t ≠ 0) :
    |t| ^ j * ‖iteratedDeriv j
      (fun s => 𝓕 (fun x => ((smooth φ N (kernelI χ a b) x : ℝ) : ℂ)) s) t‖ ≤
      symbolConst hχ φ j := by
  have hfun : (fun s => 𝓕 (fun x => ((smooth φ N (kernelI χ a b) x : ℝ) : ℂ)) s) =
      fun s => (phiHatS φ) (N * s) * ∑ k ∈ Finset.Icc a b, psiHat χ (2 ^ k * s) :=
    funext fun s => fourier_smooth_kernelI hχ φ hN a b s
  rw [hfun]
  have hΨ : ContDiff ℝ ∞ (psiHat χ) := by
    rw [← coe_fourier_psiS hχ]; exact (𝓕 (psiS hχ) : 𝓢(ℝ, ℂ)).smooth'
  exact symbol_core (phiHatS φ).smooth' hΨ (fun i => SchwartzMap.seminorm ℝ i i (phiHatS φ))
    (psiConst hχ) (fun i u => SchwartzMap.le_seminorm' ℝ i i (phiHatS φ) u)
    (psiConst_nonneg hχ) (fun i u hu => psiHat_dyadic_bound hχ i u hu) N a b j ht

/-- The shape needed by `drafts/X2Statement.lean.txt`: `m(t) = K̂(-t)`. -/
theorem symbol_bound_neg (hχ : IsCutoff χ) (φ : 𝓢(ℝ, ℝ)) (j : ℕ) {N : ℝ} (hN : 0 < N) (a b : ℕ)
    {t : ℝ} (ht : t ≠ 0) :
    |t| ^ j * ‖iteratedDeriv j
      (fun s => 𝓕 (fun x => ((smooth φ N (kernelI χ a b) x : ℝ) : ℂ)) (-s)) t‖ ≤
      symbolConst hχ φ j := by
  have h := iteratedDeriv_comp_neg j
    (fun s => 𝓕 (fun x => ((smooth φ N (kernelI χ a b) x : ℝ) : ℂ)) s) t
  rw [h]
  simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have := symbol_bound hχ φ j hN a b (neg_ne_zero.2 ht)
  rwa [abs_neg] at this

/-- `K̂` is smooth (`K` is Schwartz). -/
theorem contDiff_fourier_smooth_kernelI (hχ : IsCutoff χ) (φ : 𝓢(ℝ, ℝ)) {N : ℝ} (hN : 0 < N)
    (a b : ℕ) :
    ContDiff ℝ ∞ (fun s => 𝓕 (fun x => ((smooth φ N (kernelI χ a b) x : ℝ) : ℂ)) s) := by
  obtain ⟨S, hS⟩ := exists_schwartz_smooth_kernelI hχ φ hN a b
  have h : (fun x => ((smooth φ N (kernelI χ a b) x : ℝ) : ℂ)) =
      ((SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM S : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    funext x
    rw [← hS]; rfl
  rw [h]
  exact (𝓕 (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM S : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)).smooth'

/-- `m(t) = K̂(-t)` is smooth. -/
theorem contDiff_fourier_smooth_kernelI_neg (hχ : IsCutoff χ) (φ : 𝓢(ℝ, ℝ)) {N : ℝ} (hN : 0 < N)
    (a b : ℕ) :
    ContDiff ℝ ∞ (fun s => 𝓕 (fun x => ((smooth φ N (kernelI χ a b) x : ℝ) : ℂ)) (-s)) :=
  (contDiff_fourier_smooth_kernelI hχ φ hN a b).comp contDiff_neg

end PrimeBHT.KernelFourier
