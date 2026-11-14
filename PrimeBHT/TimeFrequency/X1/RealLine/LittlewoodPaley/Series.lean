module

public import PrimeBHT.TimeFrequency.X1.RealLine.LittlewoodPaley.Recon
public import PrimeBHT.TimeFrequency.X1.RealLine.LittlewoodPaley.DilAvgC
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Filter.AtTopBot.Finset

/-!
# The series `ψ^{[c]} = ∑_k (ψ_k^+ + ψ_k^-)` inside dilated averages (blueprint node R3, step 6)

For bounded continuous `f, g` and `t > 0`, `x ∈ ℝ`:
`∑_{|k| ≤ K} (B_t(ψ_k^+, f, g)(x) + B_t(ψ_k^-, f, g)(x)) → B_t(ψ^{[c]}, f, g)(x)` as `K → ∞`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped FourierTransform ContDiff ENNReal Real
open PrimeBHT.Statements

namespace PrimeBHT.TimeFrequency.RealLine

theorem tendsto_sum_Icc_of_hasSum {f : ℤ → ℂ} {a : ℂ} (h : HasSum f a) :
    Tendsto (fun K : ℕ => ∑ k ∈ Finset.Icc (-(K : ℤ)) K, f k) atTop (𝓝 a) := by
  have hm : Monotone (fun K : ℕ => Finset.Icc (-(K : ℤ)) K) := fun K K' hK =>
    Finset.Icc_subset_Icc (by omega) (by omega)
  have ht : Tendsto (fun K : ℕ => Finset.Icc (-(K : ℤ)) K) atTop atTop :=
    tendsto_atTop_finset_of_monotone hm (fun k => ⟨k.natAbs, by simp only [Finset.mem_Icc]; omega⟩)
  exact h.comp ht

/-! ## `L^1` and sup bounds for the pieces -/

theorem exists_integral_norm_gPiece_le {χ : ℝ → ℝ} (hχ : IsCutoff χ) :
    ∃ C : ℝ, ∀ c ∈ Set.Icc (1 : ℝ) 2, ∀ k : ℤ, ∫ x, ‖gPiece χ c k x‖ ≤ C * lpW (lpLam k) := by
  obtain ⟨C, hC0, hC⟩ := exists_decay_gPiece hχ 2
  have hI : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(2 : ℝ))) :=
    integrable_one_add_norm (μ := volume) (by simp)
  refine ⟨C * ∫ x : ℝ, (1 + ‖x‖) ^ (-(2 : ℝ)), fun c hc k => ?_⟩
  have hint := integrable_gPiece hχ hc k
  have hW := lpW_nonneg (lpLam_pos k)
  calc ∫ x, ‖gPiece χ c k x‖ ≤ ∫ x : ℝ, C * lpW (lpLam k) * (1 + ‖x‖) ^ (-(2 : ℝ)) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
          (hI.const_mul _) (Eventually.of_forall fun x => ?_)
        have h := hC c hc k x
        have hpos : 0 < (1 + |x|) ^ 2 := by positivity
        have e : (1 + ‖x‖) ^ (-(2 : ℝ)) = ((1 + |x|) ^ 2)⁻¹ := by
          rw [Real.rpow_neg (by positivity), Real.norm_eq_abs]
          norm_cast
        dsimp only
        rw [e, ← div_eq_mul_inv, le_div_iff₀ hpos]
        linarith
    _ = C * (∫ x : ℝ, (1 + ‖x‖) ^ (-(2 : ℝ))) * lpW (lpLam k) := by
        rw [integral_const_mul]; ring

theorem integrable_psiPlus {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2) (k : ℤ) :
    Integrable (psiPlus χ c k) :=
  ((integrable_gPiece hχ hc k).comp_mul_left' (lpLam_ne_zero k)).const_mul _

theorem continuous_psiPlus {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2) (k : ℤ) :
    Continuous (psiPlus χ c k) := by
  unfold psiPlus
  have := continuous_gPiece hχ hc k
  fun_prop

theorem integral_norm_psiPlus {χ : ℝ → ℝ} (k : ℤ) (c : ℝ) :
    ∫ y, ‖psiPlus χ c k y‖ = ∫ x, ‖gPiece χ c k x‖ := by
  have hl := lpLam_pos k
  have h1 : ∀ y, ‖psiPlus χ c k y‖ = lpLam k * ‖gPiece χ c k (lpLam k * y)‖ := fun y => by
    unfold psiPlus
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl]
  simp_rw [h1]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun x => ‖gPiece χ c k x‖) (lpLam k),
    abs_of_pos (inv_pos.2 hl), smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hl.ne', one_mul]

theorem exists_norm_psiPlus_le {χ : ℝ → ℝ} (hχ : IsCutoff χ) :
    ∃ C : ℝ, ∀ c ∈ Set.Icc (1 : ℝ) 2, ∀ k : ℤ, ∀ y : ℝ,
      ‖psiPlus χ c k y‖ ≤ C * (lpLam k * lpW (lpLam k)) := by
  obtain ⟨C, hC0, hC⟩ := exists_decay_gPiece hχ 0
  refine ⟨C, fun c hc k y => ?_⟩
  have h := hC c hc k (lpLam k * y)
  simp only [pow_zero, one_mul] at h
  have hl := lpLam_pos k
  unfold psiPlus
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl]
  calc lpLam k * ‖gPiece χ c k (lpLam k * y)‖ ≤ lpLam k * (C * lpW (lpLam k)) :=
        mul_le_mul_of_nonneg_left h hl.le
    _ = C * (lpLam k * lpW (lpLam k)) := by ring

/-- The pointwise `ℤ`-sum of the pieces. -/
theorem hasSum_psiPlus_add_conj {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (z : ℝ) :
    HasSum (fun k : ℤ => psiPlus χ c k z + (starRingEnd ℂ) (psiPlus χ c k z)) (psiCC χ c z) := by
  obtain ⟨C, hC⟩ := exists_norm_psiPlus_le hχ
  have hs : Summable (fun k : ℤ => psiPlus χ c k z + (starRingEnd ℂ) (psiPlus χ c k z)) := by
    refine Summable.of_norm_bounded ((summable_lpLam_mul_lpW.mul_left (2 * C))) fun k => ?_
    calc ‖psiPlus χ c k z + (starRingEnd ℂ) (psiPlus χ c k z)‖
        ≤ ‖psiPlus χ c k z‖ + ‖(starRingEnd ℂ) (psiPlus χ c k z)‖ := norm_add_le _ _
      _ = 2 * ‖psiPlus χ c k z‖ := by rw [RCLike.norm_conj]; ring
      _ ≤ 2 * (C * (lpLam k * lpW (lpLam k))) :=
          mul_le_mul_of_nonneg_left (hC c hc k z) (by norm_num)
      _ = 2 * C * (lpLam k * lpW (lpLam k)) := by ring
  have h1 := tendsto_sum_Icc_of_hasSum hs.hasSum
  have h2 := tendsto_sum_psiPlus_add_conj hχ hc z
  have := tendsto_nhds_unique h1 h2
  rw [← this]
  exact hs.hasSum

theorem integrable_conj_psiPlus {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2)
    (k : ℤ) : Integrable (fun y => (starRingEnd ℂ) (psiPlus χ c k y)) := by
  refine Integrable.mono' (integrable_psiPlus hχ hc k).norm ?_ (Eventually.of_forall fun y => ?_)
  · exact ((continuous_star (R := ℂ)).comp (continuous_psiPlus hχ hc k)).aestronglyMeasurable
  · simp

theorem summable_lpW_one : Summable fun k : ℤ => lpW (lpLam k) := by
  simpa using summable_lpW_rpow (ρ := 1) one_pos

/-- **Convergence of the series inside a dilated average.** -/
theorem tendsto_sum_dilAvgC {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2)
    {t : ℝ} (ht : 0 < t) {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) {Bf Bg : ℝ}
    (hBf : ∀ x, ‖f x‖ ≤ Bf) (hBg : ∀ x, ‖g x‖ ≤ Bg) (x : ℝ) :
    Tendsto (fun K : ℕ => ∑ k ∈ Finset.Icc (-(K : ℤ)) K,
      (dilAvgC (psiPlus χ c k) t f g x +
        dilAvgC (fun y => (starRingEnd ℂ) (psiPlus χ c k y)) t f g x))
      atTop (𝓝 (dilAvgC (psiCC χ c) t f g x)) := by
  obtain ⟨C, hC⟩ := exists_integral_norm_gPiece_le hχ
  set P : ℤ → ℝ → ℂ := fun k y => psiPlus χ c k y + (starRingEnd ℂ) (psiPlus χ c k y) with hP
  set F : ℤ → ℝ → ℂ := fun k y => f (x - y) * g (x + y) * (((t⁻¹ : ℝ) : ℂ) * P k (y / t)) with hFdef
  have hPint : ∀ k, Integrable (P k) := fun k =>
    (integrable_psiPlus hχ hc k).add (integrable_conj_psiPlus hχ hc k)
  have hF_int : ∀ k, Integrable (F k) := fun k =>
    integrable_dilAvgC_integrand (hPint k) ht.ne' hf hg hBf hBg x
  have hBf0 : 0 ≤ Bf := (norm_nonneg _).trans (hBf 0)
  have hBg0 : 0 ≤ Bg := (norm_nonneg _).trans (hBg 0)
  have hnormP : ∀ k, ∫ y, ‖P k y‖ ≤ 2 * (C * lpW (lpLam k)) := by
    intro k
    have h1 : ∫ y, ‖P k y‖ ≤ ∫ y, (‖psiPlus χ c k y‖ + ‖psiPlus χ c k y‖) := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
        ((integrable_psiPlus hχ hc k).norm.add (integrable_psiPlus hχ hc k).norm)
        (Eventually.of_forall fun y => ?_)
      simp only [hP]
      refine (norm_add_le _ _).trans ?_
      rw [RCLike.norm_conj]
    rw [integral_add (integrable_psiPlus hχ hc k).norm (integrable_psiPlus hχ hc k).norm,
      integral_norm_psiPlus k c] at h1
    have := hC c hc k
    linarith
  have hsum : Summable fun k => ∫ y, ‖F k y‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun y => norm_nonneg _) (fun k => ?_)
      (summable_lpW_one.mul_left (Bf * Bg * (2 * C)))
    refine (integral_norm_integrand_le (hPint k) ht hBf hBg x).trans ?_
    calc Bf * Bg * ∫ y, ‖P k y‖ ≤ Bf * Bg * (2 * (C * lpW (lpLam k))) :=
          mul_le_mul_of_nonneg_left (hnormP k) (mul_nonneg hBf0 hBg0)
      _ = Bf * Bg * (2 * C) * lpW (lpLam k) := by ring
  have hHas := hasSum_integral_of_summable_integral_norm hF_int hsum
  have hlim : (∫ y, ∑' k, F k y) = dilAvgC (psiCC χ c) t f g x := by
    unfold dilAvgC
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have e1 : ∀ k, F k y = (f (x - y) * g (x + y) * ((t⁻¹ : ℝ) : ℂ)) * P k (y / t) := fun k => by
      simp only [hFdef]; ring
    simp_rw [e1]
    rw [tsum_mul_left, (hasSum_psiPlus_add_conj hχ hc (y / t)).tsum_eq]
    ring
  rw [hlim] at hHas
  have hT := tendsto_sum_Icc_of_hasSum hHas
  refine hT.congr fun K => Finset.sum_congr rfl fun k _ => ?_
  have hi1 := integrable_dilAvgC_integrand (integrable_psiPlus hχ hc k) ht.ne' hf hg hBf hBg x
  have hi2 := integrable_dilAvgC_integrand (integrable_conj_psiPlus hχ hc k) ht.ne' hf hg hBf hBg x
  unfold dilAvgC
  rw [← integral_add hi1 hi2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [hFdef, hP]
  ring

end PrimeBHT.TimeFrequency.RealLine

end
