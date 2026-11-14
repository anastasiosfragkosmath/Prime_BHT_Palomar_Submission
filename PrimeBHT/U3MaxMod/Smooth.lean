module

public import PrimeBHT.U3MaxMod.Modulation
public import PrimeBHT.U3MaxMod.Minkowski
public import PrimeCarleson.Proof.Common.FourierR

/-!
# `l:U3maxmod`, part 7: the smooth-weight variant (Fourier inversion + modulation + Minkowski)

For `φ ∈ C²(ℝ)` with `supp φ ⊆ [0,1]`, `‖φ‖_∞, ‖φ''‖_∞ ≤ M`, `φ_N(n) = N⁻¹ φ(n/N)`:
`‖∑_n φ_N(n) W(n) f(x-n) g(x+n)‖_{ℓ²_x} ≤ 8 M ‖W‖_{U³([N])} ‖f‖_4 ‖g‖_4`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform ComplexConjugate ENNReal

set_option autoImplicit false

namespace PrimeBHT.U3MaxMod

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

lemma continuous_e : Continuous e := by
  unfold e
  fun_prop

lemma integrable_fourier_mul_e {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (n : ℤ) (N : ℝ) : Integrable (fun ξ : ℝ => 𝓕 φ ξ * e (ξ * n / N)) :=
  (integrable_fourier_of_contDiff_two hφ hc).mul_bdd (c := 1)
    (by exact (continuous_e.comp (by fun_prop)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ξ => (norm_e _).le)

/-- Pointwise decomposition of the modulated sum into characters `ξ ↦ e(ξ n / N)`. -/
lemma fourier_mul_modulated (N : ℕ+) (W f g : ℤ → ℂ) (φ : ℝ → ℂ) (x : ℤ) (ξ : ℝ) :
    𝓕 φ ξ * (((N : ℕ) : ℂ)⁻¹ * ∑ n ∈ Finset.Icc (1 : ℤ) N,
        (e ((ξ / (N : ℕ)) * (n : ℝ)) * W n) * f (x - n) * g (x + n)) =
      ∑ n ∈ Finset.Icc (1 : ℤ) N, (((N : ℕ) : ℂ)⁻¹ * W n * f (x - n) * g (x + n)) *
        (𝓕 φ ξ * e (ξ * n / (N : ℕ))) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have : (ξ / ((N : ℕ) : ℝ)) * (n : ℝ) = ξ * n / ((N : ℕ) : ℝ) := by ring
  rw [this]
  ring

theorem smooth_eq_integral (N : ℕ+) (W f g : ℤ → ℂ) {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (x : ℤ) :
    ∫ ξ : ℝ, 𝓕 φ ξ * (((N : ℕ) : ℂ)⁻¹ * ∑ n ∈ Finset.Icc (1 : ℤ) N,
        (e ((ξ / (N : ℕ)) * (n : ℝ)) * W n) * f (x - n) * g (x + n)) =
      ∑ n ∈ Finset.Icc (1 : ℤ) N, (((N : ℕ) : ℂ)⁻¹ * φ ((n : ℝ) / (N : ℕ))) * W n *
        f (x - n) * g (x + n) := by
  simp_rw [fourier_mul_modulated]
  rw [integral_finsetSum _ (fun n _ => (integrable_fourier_mul_e hφ hc n _).const_mul _)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, ← fourier_inversion_div hφ hc (n : ℝ) ((N : ℕ) : ℝ)]
  ring


/-- **`l:U3maxmod` (b), real-sum form.** -/
theorem l2_smooth_le (N : ℕ+) (W f g : ℤ → ℂ) (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) {φ : ℝ → ℂ} {M : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : Function.support φ ⊆ Set.Icc 0 1) (h0 : ∀ t, ‖φ t‖ ≤ M)
    (h2 : ∀ t, ‖deriv (deriv φ) t‖ ≤ M) :
    Real.sqrt (∑' x, ‖∑ n ∈ Finset.Icc (1 : ℤ) N,
        (((N : ℕ) : ℂ)⁻¹ * φ ((n : ℝ) / (N : ℕ))) * W n * f (x - n) * g (x + n)‖ ^ 2) ≤
      8 * M * gowersNormInterval 3 N W * (∑' x, ‖f x‖ ^ 4) ^ (1 / 4 : ℝ) *
        (∑' x, ‖g x‖ ^ 4) ^ (1 / 4 : ℝ) := by
  set I : Finset ℤ := Finset.Icc (1 : ℤ) N with hI
  have hc : HasCompactSupport φ :=
    HasCompactSupport.intro isCompact_Icc fun x hx => by
      by_contra h
      exact hx (hsupp h)
  have hM : 0 ≤ M := (norm_nonneg _).trans (h0 0)
  set Wn : ℝ := gowersNormInterval 3 N W with hWn
  have hWn0 : 0 ≤ Wn := div_nonneg (PrimeCarleson.Proof.Paper.gowersNorm_nonneg _ _)
    (PrimeCarleson.Proof.Paper.gowersNorm_nonneg _ _)
  set Ff : ℝ := (∑' x, ‖f x‖ ^ 4) ^ (1 / 4 : ℝ) with hFf
  set Fg : ℝ := (∑' x, ‖g x‖ ^ 4) ^ (1 / 4 : ℝ) with hFg
  have hFf0 : 0 ≤ Ff := Real.rpow_nonneg (tsum_nonneg fun x => by positivity) _
  have hFg0 : 0 ≤ Fg := Real.rpow_nonneg (tsum_nonneg fun x => by positivity) _
  set K : ℝ := 2 * Wn * Ff * Fg with hKdef
  have hK0 : 0 ≤ K := by positivity
  -- a finite set outside which everything vanishes
  have hXs : (⋃ n ∈ I, Function.support (fun x => f (x + -n))).Finite :=
    Set.Finite.biUnion I.finite_toSet fun n _ => fin_supp_of_imp (-n) hf fun x hx => hx
  set X : Finset ℤ := hXs.toFinset with hXdef
  have hvan : ∀ (c : ℤ → ℂ) (x : ℤ), x ∉ X →
      ∑ n ∈ I, c n * f (x - n) * g (x + n) = 0 := by
    intro c x hx
    refine Finset.sum_eq_zero fun n hn => ?_
    have : f (x - n) = 0 := by
      by_contra hne
      apply hx
      rw [hXdef, Set.Finite.mem_toFinset]
      simp only [Set.mem_iUnion, Function.mem_support, ne_eq]
      exact ⟨n, hn, by simpa [sub_eq_add_neg] using hne⟩
    rw [this]; simp
  -- the ℓ² bound for each modulated average
  have hK : ∀ ξ : ℝ, ∑ x ∈ X, ‖((N : ℕ) : ℂ)⁻¹ * ∑ n ∈ I,
      (e ((ξ / (N : ℕ)) * (n : ℝ)) * W n) * f (x - n) * g (x + n)‖ ^ 2 ≤ K ^ 2 := by
    intro ξ
    have h1 := l2_bilinAvg_le N (fun n : ℤ => e ((ξ / (N : ℕ)) * (n : ℝ)) * W n) f g hf hg
    rw [gowersNormInterval_mod] at h1
    have h2 := (Real.sqrt_le_iff.1 h1).2
    have hT0 : ∀ x : ℤ, x ∉ X → ‖((N : ℕ) : ℂ)⁻¹ * ∑ n ∈ I,
        (e ((ξ / (N : ℕ)) * (n : ℝ)) * W n) * f (x - n) * g (x + n)‖ ^ 2 = 0 := by
      intro x hx
      rw [hvan (fun n => e ((ξ / (N : ℕ)) * (n : ℝ)) * W n) x hx]
      simp
    rw [tsum_eq_sum (s := X) hT0] at h2
    simpa [hKdef, hWn, hFf, hFg] using h2
  have hint : ∀ n : ℤ, Integrable (fun ξ : ℝ => 𝓕 φ ξ * e (ξ * n / ((N : ℕ) : ℝ))) :=
    fun n => integrable_fourier_mul_e hφ hc n _
  have hH : ∀ x ∈ X, Integrable (fun ξ : ℝ => 𝓕 φ ξ * (((N : ℕ) : ℂ)⁻¹ * ∑ n ∈ I,
      (e ((ξ / (N : ℕ)) * (n : ℝ)) * W n) * f (x - n) * g (x + n))) := by
    intro x _
    simp_rw [hI, fourier_mul_modulated]
    exact integrable_finsetSum _ fun n _ => (hint n).const_mul _
  have hmk := l2_integral_le (X := X) (𝓕 φ) (fun ξ x => ((N : ℕ) : ℂ)⁻¹ * ∑ n ∈ I,
      (e ((ξ / (N : ℕ)) * (n : ℝ)) * W n) * f (x - n) * g (x + n)) K
    (integrable_fourier_of_contDiff_two hφ hc) hH hK hK0
  simp_rw [hI, smooth_eq_integral N W f g hφ hc] at hmk
  have h4 := integral_norm_fourier_le_four_mul hφ hsupp h0 h2
  have hS0 : ∀ x : ℤ, x ∉ X → ‖∑ n ∈ I,
      (((N : ℕ) : ℂ)⁻¹ * φ ((n : ℝ) / (N : ℕ))) * W n * f (x - n) * g (x + n)‖ ^ 2 = 0 := by
    intro x hx
    rw [hvan (fun n => ((N : ℕ) : ℂ)⁻¹ * φ ((n : ℝ) / (N : ℕ)) * W n) x hx]
    simp
  rw [tsum_eq_sum (s := X) hS0]
  calc _ ≤ K * ∫ ξ, ‖𝓕 φ ξ‖ := hmk
    _ ≤ K * (4 * M) := mul_le_mul_of_nonneg_left h4 hK0
    _ = 8 * M * Wn * Ff * Fg := by rw [hKdef]; ring


/-- **`l:U3maxmod` (b), `eLpNorm` form**, with `‖φ‖_∞, ‖φ''‖_∞ ≤ M`: the constant is `8 M`
(`4 M` from `‖φ̂‖_{L¹} ≤ 4 M`, times `2` from the plain-average bound). -/
theorem eLpNorm_smooth_le (N : ℕ+) (W : ℤ → ℂ) (f g : ℤ →₀ ℂ) {φ : ℝ → ℂ} {M : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : Function.support φ ⊆ Set.Icc 0 1) (h0 : ∀ t, ‖φ t‖ ≤ M)
    (h2 : ∀ t, ‖deriv (deriv φ) t‖ ≤ M) :
    eLpNorm (fun x : ℤ => ∑ n ∈ Finset.Icc (1 : ℤ) N,
        (((N : ℕ) : ℂ)⁻¹ * φ ((n : ℝ) / (N : ℕ))) * W n * f (x - n) * g (x + n)) 2
        Measure.count ≤
      ENNReal.ofReal (8 * M * gowersNormInterval 3 N W) * eLpNorm (⇑f) 4 Measure.count *
        eLpNorm (⇑g) 4 Measure.count := by
  have hf := PrimeCarleson.Proof.Common.GowersCS.finsupp_support_finite f
  have hg := PrimeCarleson.Proof.Common.GowersCS.finsupp_support_finite g
  have hM : 0 ≤ M := (norm_nonneg _).trans (h0 0)
  have hW : 0 ≤ gowersNormInterval 3 N W :=
    div_nonneg (PrimeCarleson.Proof.Paper.gowersNorm_nonneg _ _)
      (PrimeCarleson.Proof.Paper.gowersNorm_nonneg _ _)
  have hfs := fs_bilin (Finset.Icc (1 : ℤ) N)
    (fun n : ℤ => ((N : ℕ) : ℂ)⁻¹ * φ ((n : ℝ) / (N : ℕ)) * W n) f g hf
  rw [eLpNorm_count_two _ hfs, eLpNorm_count_four _ hf, eLpNorm_count_four _ hg,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (l2_smooth_le N W f g hf hg hφ hsupp h0 h2)

end PrimeBHT.U3MaxMod
