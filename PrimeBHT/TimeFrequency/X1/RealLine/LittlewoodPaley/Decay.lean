module

public import PrimeBHT.TimeFrequency.X1.RealLine.LittlewoodPaley.PsiHat
public import PrimeBHT.TimeFrequency.X1.RealLine.LittlewoodPaley.Bump
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# The rescaled pieces `g_k` and their decay with geometric coefficients (blueprint node R3, steps 3-4)

For `c ∈ [1, 2]` and `k ∈ ℤ` put `λ_k = μ^k / 8` and
`h_{c,k}(η) = ψ̂^{[c]}(λ_k η) b(η)` (`hFun`), `g_{c,k} = 𝓕⁻ h_{c,k}` (`gPiece`). Then:

* `𝓕 g_{c,k} = h_{c,k}` is supported in `[8, 9]`;
* `(1 + |x|)^M ‖g_{c,k}(x)‖ ≤ C · lpW(λ_k)` with `lpW λ = min λ λ⁻³` and `C` independent of `c, k`
  (`exists_decay_gPiece`), obtained from the Schwartz bounds of `ψ̂^{[c]}` (uniform in `c`) and the
  vanishing `ψ̂(0) = 0`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped FourierTransform ContDiff ENNReal Real
open PrimeBHT.Statements

namespace PrimeBHT.TimeFrequency.RealLine

/-- The Fourier multiplier `η ↦ ψ̂^{[c]}(λ_k η) b(η)` of the rescaled piece `g_{c,k}`. -/
def hFun (χ : ℝ → ℝ) (c : ℝ) (k : ℤ) : ℝ → ℂ :=
  fun η => 𝓕 (psiCC χ c) (lpLam k * η) * (lpBump η : ℂ)

/-- The rescaled piece `g_{c,k} = 𝓕⁻ h_{c,k}`. -/
def gPiece (χ : ℝ → ℝ) (c : ℝ) (k : ℤ) : ℝ → ℂ := 𝓕⁻ (hFun χ c k)

/-- The decay weight `lpW λ = min λ λ⁻³`. -/
def lpW (l : ℝ) : ℝ := min l (l⁻¹ ^ 3)

theorem lpW_nonneg {l : ℝ} (hl : 0 < l) : 0 ≤ lpW l :=
  le_min hl.le (by positivity)

theorem lpW_of_le_one {l : ℝ} (hl : 0 < l) (h : l ≤ 1) : lpW l = l := by
  refine min_eq_left ?_
  have h1 : 1 ≤ l⁻¹ := (one_le_inv₀ hl).2 h
  have : 1 ≤ l⁻¹ ^ 3 := one_le_pow₀ h1
  linarith

theorem lpW_of_one_le {l : ℝ} (h : 1 ≤ l) : lpW l = l⁻¹ ^ 3 := by
  refine min_eq_right ?_
  have hl : 0 < l := by linarith
  have h1 : l⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h
  have : l⁻¹ ^ 3 ≤ 1 := pow_le_one₀ (by positivity) h1
  linarith

/-! ## Smoothness and support of `h_{c,k}` -/

theorem contDiff_fourier_psiCC {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2) :
    ContDiff ℝ ∞ (𝓕 (psiCC χ c)) := by
  let Ψ : SchwartzMap ℝ ℂ := (hasCompactSupport_psiCC hχ hc.1).toSchwartzMap (contDiff_psiCC hχ hc)
  have h : (𝓕 (psiCC χ c) : ℝ → ℂ) = ⇑(SchwartzMap.fourierTransformCLM ℂ Ψ) := rfl
  rw [h]
  exact (SchwartzMap.fourierTransformCLM ℂ Ψ).smooth ⊤

theorem contDiff_lpBumpC : ContDiff ℝ ∞ (fun η : ℝ => (lpBump η : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp contDiff_lpBump

theorem contDiff_hFun {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : c ∈ Set.Icc (1 : ℝ) 2) (k : ℤ) :
    ContDiff ℝ ∞ (hFun χ c k) :=
  ((contDiff_fourier_psiCC hχ hc).comp (contDiff_const.mul contDiff_id)).mul contDiff_lpBumpC

theorem hFun_eq_zero_of_notMem {χ : ℝ → ℝ} {c : ℝ} (k : ℤ) {η : ℝ} (h : η ∉ Set.Icc (8 : ℝ) 9) :
    hFun χ c k η = 0 := by
  simp [hFun, lpBump_eq_zero_of_notMem h]

theorem hasCompactSupport_hFun {χ : ℝ → ℝ} {c : ℝ} (k : ℤ) : HasCompactSupport (hFun χ c k) :=
  HasCompactSupport.intro (isCompact_Icc (a := (8 : ℝ)) (b := 9)) fun _ hη =>
    hFun_eq_zero_of_notMem k hη

theorem iteratedFDeriv_hFun_eq_zero {χ : ℝ → ℝ} {c : ℝ} (k : ℤ) (n : ℕ) {η : ℝ}
    (h : η ∉ Set.Icc (8 : ℝ) 9) : iteratedFDeriv ℝ n (hFun χ c k) η = 0 := by
  have hev : hFun χ c k =ᶠ[𝓝 η] fun _ => (0 : ℂ) := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds h] with z hz
    exact hFun_eq_zero_of_notMem k hz
  rw [(hev.iteratedFDeriv ℝ n).self_of_nhds]
  exact congrFun iteratedFDeriv_fun_zero η

/-! ## Bounds of the derivatives of the scaled `ψ̂` -/

/-- Uniform bound `λ^i ‖D^i ψ̂^{[c]}(λ v)‖ ≤ A · lpW λ` for `v ∈ [8, 9]`, `λ > 0`, `c ∈ [1, 2]`. -/
theorem exists_scaled_bound {χ : ℝ → ℝ} (hχ : IsCutoff χ) (i : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ c ∈ Set.Icc (1 : ℝ) 2, ∀ l : ℝ, 0 < l → ∀ v ∈ Set.Icc (8 : ℝ) 9,
      l ^ i * ‖iteratedFDeriv ℝ i (𝓕 (psiCC χ c)) (l * v)‖ ≤ A * lpW l := by
  obtain ⟨A3, hA3⟩ := exists_norm_fourier_psiCC_le hχ
  obtain ⟨A1, hA1⟩ := exists_bound_iteratedFDeriv_fourier_psiCC hχ i 0
  obtain ⟨A2, hA2⟩ := exists_bound_iteratedFDeriv_fourier_psiCC hχ i (i + 3)
  refine ⟨9 * |A3| + |A1| + |A2|, by positivity, fun c hc l hl v hv => ?_⟩
  have hv0 : 0 < v := by linarith [hv.1]
  have hW := lpW_nonneg hl
  by_cases hl1 : l ≤ 1
  · rw [lpW_of_le_one hl hl1]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have h := hA3 c hc (l * v)
      simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero]
      refine h.trans ?_
      rw [abs_of_pos (mul_pos hl hv0)]
      have : A3 * (l * v) ≤ |A3| * (l * 9) := by
        have h1 : A3 ≤ |A3| := le_abs_self A3
        have h2 : l * v ≤ l * 9 := mul_le_mul_of_nonneg_left hv.2 hl.le
        have h3 : 0 ≤ l * v := (mul_pos hl hv0).le
        calc A3 * (l * v) ≤ |A3| * (l * v) := mul_le_mul_of_nonneg_right h1 h3
          _ ≤ |A3| * (l * 9) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      have : |A3| * (l * 9) ≤ (9 * |A3| + |A1| + |A2|) * l := by
        have := abs_nonneg A1; have := abs_nonneg A2; have := abs_nonneg A3; nlinarith
      linarith
    · have h := hA1 c hc (l * v)
      simp only [pow_zero, one_mul] at h
      have hli : l ^ i ≤ l := pow_le_of_le_one hl.le hl1 hi.ne'
      calc l ^ i * ‖iteratedFDeriv ℝ i (𝓕 (psiCC χ c)) (l * v)‖
          ≤ l * |A1| := by
            refine mul_le_mul hli (h.trans (le_abs_self _)) (norm_nonneg _) hl.le
        _ ≤ (9 * |A3| + |A1| + |A2|) * l := by
            have := abs_nonneg A1; have := abs_nonneg A2; have := abs_nonneg A3; nlinarith
  · rw [not_le] at hl1
    rw [lpW_of_one_le hl1.le]
    have h := hA2 c hc (l * v)
    have hlv : l ≤ ‖l * v‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (mul_pos hl hv0)]
      nlinarith [hv.1]
    have hpow : l ^ (i + 3) ≤ ‖l * v‖ ^ (i + 3) := pow_le_pow_left₀ hl.le hlv _
    have hne : 0 < l ^ (i + 3) := by positivity
    have hT := norm_nonneg (iteratedFDeriv ℝ i (𝓕 (psiCC χ c)) (l * v))
    have h4 : l ^ (i + 3) * ‖iteratedFDeriv ℝ i (𝓕 (psiCC χ c)) (l * v)‖ ≤ |A2| :=
      (mul_le_mul_of_nonneg_right hpow hT).trans (h.trans (le_abs_self _))
    have h5 : l ^ i * ‖iteratedFDeriv ℝ i (𝓕 (psiCC χ c)) (l * v)‖ ≤ |A2| * l⁻¹ ^ 3 := by
      have : l ^ i * ‖iteratedFDeriv ℝ i (𝓕 (psiCC χ c)) (l * v)‖ =
          (l ^ (i + 3) * ‖iteratedFDeriv ℝ i (𝓕 (psiCC χ c)) (l * v)‖) * l⁻¹ ^ 3 := by
        rw [pow_add]; field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right h4 (by positivity)
    refine h5.trans ?_
    have := abs_nonneg A1; have := abs_nonneg A2; have := abs_nonneg A3
    have : 0 ≤ l⁻¹ ^ 3 := by positivity
    nlinarith

/-! ## Derivatives of `h_{c,k}` -/

theorem exists_bound_iteratedFDeriv_lpBumpC (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v, ‖iteratedFDeriv ℝ m (fun η : ℝ => (lpBump η : ℂ)) v‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := (hasCompactSupport_lpBump.comp_left (g := fun r : ℝ => (r : ℂ))
    Complex.ofReal_zero).exists_bound_iteratedFDeriv contDiff_lpBumpC m
  exact ⟨B, hB0, fun v => hB m le_rfl v⟩

/-- `‖D^j h_{c,k}‖ ≤ E_j lpW(λ_k)` on `[8, 9]`, uniformly in `c ∈ [1, 2]` and `k`. -/
theorem exists_bound_iteratedFDeriv_hFun {χ : ℝ → ℝ} (hχ : IsCutoff χ) (j : ℕ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ c ∈ Set.Icc (1 : ℝ) 2, ∀ k : ℤ, ∀ v ∈ Set.Icc (8 : ℝ) 9,
      ‖iteratedFDeriv ℝ j (hFun χ c k) v‖ ≤ E * lpW (lpLam k) := by
  choose A hA0 hA using exists_scaled_bound hχ
  choose B hB0 hB using exists_bound_iteratedFDeriv_lpBumpC
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A i * B (j - i), ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => by have := hA0 i; have := hB0 (j - i); positivity
  intro c hc k v hv
  have hl := lpLam_pos k
  have hW := lpW_nonneg hl
  have hFc := contDiff_fourier_psiCC hχ hc
  have hu : ContDiff ℝ ∞ (fun η : ℝ => 𝓕 (psiCC χ c) (lpLam k * η)) :=
    hFc.comp (contDiff_const.mul contDiff_id)
  have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := fun η : ℝ => 𝓕 (psiCC χ c) (lpLam k * η))
    (g := fun η : ℝ => (lpBump η : ℂ)) (N := ∞) hu contDiff_lpBumpC v (n := j)
    (by exact_mod_cast le_top)
  have h0 : hFun χ c k = fun η : ℝ => 𝓕 (psiCC χ c) (lpLam k * η) * (lpBump η : ℂ) := rfl
  rw [h0]
  refine hmul.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hsc : iteratedFDeriv ℝ i (fun η : ℝ => 𝓕 (psiCC χ c) (lpLam k * η)) v =
      lpLam k ^ i • iteratedFDeriv ℝ i (𝓕 (psiCC χ c)) (lpLam k • v) :=
    congrFun (iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (lpLam k) (hFc.of_le (by exact_mod_cast le_top))) v
  have hn : ‖iteratedFDeriv ℝ i (fun η : ℝ => 𝓕 (psiCC χ c) (lpLam k * η)) v‖ =
      lpLam k ^ i * ‖iteratedFDeriv ℝ i (𝓕 (psiCC χ c)) (lpLam k * v)‖ := by
    rw [hsc, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hl i), smul_eq_mul]
  have h1 := hA i c hc (lpLam k) hl v hv
  have h2 := hB (j - i) v
  rw [hn]
  have hc0 : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
  calc (j.choose i : ℝ) * (lpLam k ^ i * ‖iteratedFDeriv ℝ i (𝓕 (psiCC χ c)) (lpLam k * v)‖) *
        ‖iteratedFDeriv ℝ (j - i) (fun η : ℝ => (lpBump η : ℂ)) v‖
      ≤ (j.choose i : ℝ) * (A i * lpW (lpLam k)) * B (j - i) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left h1 hc0) h2 (norm_nonneg _) (by
          have := hA0 i; positivity)
    _ = (j.choose i : ℝ) * A i * B (j - i) * lpW (lpLam k) := by ring

/-- `‖x‖^M ‖g_{c,k}(x)‖ ≤ 2^M ∑_{j ≤ M} ∫ ‖D^j h_{c,k}‖`. -/
theorem norm_pow_mul_gPiece_le {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ}
    (hc : c ∈ Set.Icc (1 : ℝ) 2) (k : ℤ) (M : ℕ) (x : ℝ) :
    ‖x‖ ^ M * ‖gPiece χ c k x‖ ≤
      2 ^ M * ∑ j ∈ Finset.range (M + 1), ∫ v, ‖iteratedFDeriv ℝ j (hFun χ c k) v‖ := by
  have hh := contDiff_hFun hχ hc k
  have hint : ∀ (k' n : ℕ), (k' : ℕ∞) ≤ (⊤ : ℕ∞) → (n : ℕ∞) ≤ (⊤ : ℕ∞) →
      Integrable (fun v : ℝ => ‖v‖ ^ k' * ‖iteratedFDeriv ℝ n (hFun χ c k) v‖) := by
    intro k' n _ _
    have hc1 : Continuous (fun v : ℝ => ‖v‖ ^ k' * ‖iteratedFDeriv ℝ n (hFun χ c k) v‖) := by
      apply Continuous.mul (by fun_prop)
      exact (hh.of_le (mod_cast le_top)).continuous_iteratedFDeriv'.norm
    refine hc1.integrable_of_hasCompactSupport ?_
    exact ((hasCompactSupport_hFun k).iteratedFDeriv _).norm.mul_left
  have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := ⊤) (N := ⊤) (f := hFun χ c k) hh hint
    (k := 0) (n := M) le_top le_top (-x)
  rw [Finset.sum_product, Finset.sum_range_one] at h
  simp only [norm_neg, norm_iteratedFDeriv_zero, pow_zero, one_mul] at h
  have e : gPiece χ c k x = 𝓕 (hFun χ c k) (-x) := Real.fourierInv_eq_fourier_neg _ _
  rw [e]
  refine h.trans (le_of_eq ?_)
  norm_num

theorem exists_integral_norm_iteratedFDeriv_hFun_le {χ : ℝ → ℝ} (hχ : IsCutoff χ) (j : ℕ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ c ∈ Set.Icc (1 : ℝ) 2, ∀ k : ℤ,
      ∫ v, ‖iteratedFDeriv ℝ j (hFun χ c k) v‖ ≤ E * lpW (lpLam k) := by
  obtain ⟨E, hE0, hE⟩ := exists_bound_iteratedFDeriv_hFun hχ j
  refine ⟨E, hE0, fun c hc k => ?_⟩
  have h := norm_integral_le_of_forall_Icc (fun v : ℝ => ‖iteratedFDeriv ℝ j (hFun χ c k) v‖)
    (a := 8) (b := 9) (B := E * lpW (lpLam k)) (by norm_num)
    (fun v hv => by simp [iteratedFDeriv_hFun_eq_zero k j hv])
    (fun v hv => by rw [norm_norm]; exact hE c hc k v hv)
  have h' : (∫ v, ‖iteratedFDeriv ℝ j (hFun χ c k) v‖) ≤
      ‖∫ v, ‖iteratedFDeriv ℝ j (hFun χ c k) v‖‖ := Real.le_norm_self _
  have h2 : E * lpW (lpLam k) * (9 - 8) = E * lpW (lpLam k) := by ring
  linarith

theorem one_add_abs_pow_le (M : ℕ) (t : ℝ) (ht : 0 ≤ t) : (1 + t) ^ M ≤ 2 ^ M * (1 + t ^ M) := by
  rcases le_total t 1 with h | h
  · calc (1 + t) ^ M ≤ 2 ^ M := pow_le_pow_left₀ (by linarith) (by linarith) M
      _ = 2 ^ M * 1 := (mul_one _).symm
      _ ≤ 2 ^ M * (1 + t ^ M) := by
        have : 0 ≤ t ^ M := pow_nonneg ht M
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · calc (1 + t) ^ M ≤ (2 * t) ^ M := pow_le_pow_left₀ (by linarith) (by linarith) M
      _ = 2 ^ M * t ^ M := mul_pow _ _ _
      _ ≤ 2 ^ M * (1 + t ^ M) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- **Decay of the rescaled pieces.** For every `M` there is `C > 0` such that for all `c ∈ [1, 2]`,
`k ∈ ℤ`, `x`: `(1 + |x|)^M ‖g_{c,k}(x)‖ ≤ C · lpW(λ_k)`. -/
theorem exists_decay_gPiece {χ : ℝ → ℝ} (hχ : IsCutoff χ) (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c ∈ Set.Icc (1 : ℝ) 2, ∀ k : ℤ, ∀ x : ℝ,
      (1 + |x|) ^ M * ‖gPiece χ c k x‖ ≤ C * lpW (lpLam k) := by
  choose E hE0 hE using exists_integral_norm_iteratedFDeriv_hFun_le hχ
  set S := ∑ j ∈ Finset.range (M + 1), E j with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => hE0 j
  refine ⟨2 ^ M * (E 0 + 2 ^ M * S) + 1, by have := hE0 0; positivity, fun c hc k x => ?_⟩
  have hW := lpW_nonneg (lpLam_pos k)
  have h0 := norm_pow_mul_gPiece_le hχ hc k 0 x
  simp only [pow_zero, one_mul, zero_add, Finset.sum_range_one] at h0
  have h0' : ‖gPiece χ c k x‖ ≤ E 0 * lpW (lpLam k) := h0.trans (hE 0 c hc k)
  have h1 := norm_pow_mul_gPiece_le hχ hc k M x
  have h1' : |x| ^ M * ‖gPiece χ c k x‖ ≤ 2 ^ M * S * lpW (lpLam k) := by
    refine h1.trans ?_
    rw [Real.norm_eq_abs] at *
    have : ∑ j ∈ Finset.range (M + 1), ∫ v, ‖iteratedFDeriv ℝ j (hFun χ c k) v‖ ≤
        S * lpW (lpLam k) := by
      rw [hS, Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ => hE j c hc k
    calc 2 ^ M * ∑ j ∈ Finset.range (M + 1), ∫ v, ‖iteratedFDeriv ℝ j (hFun χ c k) v‖
        ≤ 2 ^ M * (S * lpW (lpLam k)) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 ^ M * S * lpW (lpLam k) := by ring
  have hg0 : 0 ≤ ‖gPiece χ c k x‖ := norm_nonneg _
  calc (1 + |x|) ^ M * ‖gPiece χ c k x‖
      ≤ 2 ^ M * (1 + |x| ^ M) * ‖gPiece χ c k x‖ :=
        mul_le_mul_of_nonneg_right (one_add_abs_pow_le M |x| (abs_nonneg x)) hg0
    _ = 2 ^ M * (‖gPiece χ c k x‖ + |x| ^ M * ‖gPiece χ c k x‖) := by ring
    _ ≤ 2 ^ M * (E 0 * lpW (lpLam k) + 2 ^ M * S * lpW (lpLam k)) := by
        gcongr
    _ = 2 ^ M * (E 0 + 2 ^ M * S) * lpW (lpLam k) := by ring
    _ ≤ (2 ^ M * (E 0 + 2 ^ M * S) + 1) * lpW (lpLam k) := by
        have := hE0 0; nlinarith

/-! ## Summability of the geometric weights -/

theorem lpLam_natCast (n : ℕ) : lpLam (n : ℤ) = lpMu ^ n / 8 := by
  simp [lpLam]

theorem lpLam_neg_natCast (n : ℕ) : lpLam (-(n : ℤ)) = (lpMu ^ n)⁻¹ / 8 := by
  simp [lpLam, zpow_neg]

theorem lpW_lpLam_le (k : ℤ) :
    lpW (lpLam k) ≤ 512 * lpMu⁻¹ ^ k.natAbs ∧
      lpLam k * lpW (lpLam k) ≤ 512 * lpMu⁻¹ ^ k.natAbs := by
  have hm := lpMu_pos
  have hm1 := one_lt_lpMu
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · have ht : lpMu⁻¹ ^ n = (lpMu ^ n)⁻¹ := inv_pow _ _
    simp only [Int.natAbs_natCast]
    rw [ht]
    set t := (lpMu ^ n)⁻¹ with htdef
    have hmn : 1 ≤ lpMu ^ n := one_le_pow₀ hm1.le
    have ht0 : 0 < t := inv_pos.2 (by positivity)
    have ht1 : t ≤ 1 := inv_le_one_of_one_le₀ hmn
    have hl : lpLam (n : ℤ) = 1 / (8 * t) := by
      rw [lpLam_natCast, htdef]; field_simp
    have hli : (lpLam (n : ℤ))⁻¹ = 8 * t := by rw [hl]; field_simp
    have hlp := lpLam_pos (n : ℤ)
    have hw : lpW (lpLam n) ≤ (lpLam n)⁻¹ ^ 3 := min_le_right _ _
    rw [hli] at hw
    have h3 : (8 * t) ^ 3 ≤ 512 * t := by
      have : t ^ 3 ≤ t := pow_le_of_le_one ht0.le ht1 (by norm_num)
      nlinarith
    refine ⟨hw.trans h3, ?_⟩
    have h4 : lpLam n * lpW (lpLam n) ≤ lpLam n * (8 * t) ^ 3 :=
      mul_le_mul_of_nonneg_left hw hlp.le
    have h5 : lpLam n * (8 * t) ^ 3 = 64 * t ^ 2 := by rw [hl]; field_simp; ring
    have h6 : t ^ 2 ≤ t := pow_le_of_le_one ht0.le ht1 (by norm_num)
    linarith
  · have ht : lpMu⁻¹ ^ n = (lpMu ^ n)⁻¹ := inv_pow _ _
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    rw [ht]
    set t := (lpMu ^ n)⁻¹ with htdef
    have hmn : 1 ≤ lpMu ^ n := one_le_pow₀ hm1.le
    have ht0 : 0 < t := inv_pos.2 (by positivity)
    have ht1 : t ≤ 1 := inv_le_one_of_one_le₀ hmn
    have hl : lpLam (-(n : ℤ)) = t / 8 := by rw [lpLam_neg_natCast]
    have hlp := lpLam_pos (-(n : ℤ))
    have hw : lpW (lpLam (-(n : ℤ))) ≤ lpLam (-(n : ℤ)) := min_le_left _ _
    rw [hl] at hw ⊢
    refine ⟨by linarith, ?_⟩
    have h4 : t / 8 * lpW (t / 8) ≤ t / 8 * (t / 8) := mul_le_mul_of_nonneg_left hw (by positivity)
    nlinarith

theorem summable_geom_natAbs {ν : ℝ} (h0 : 0 ≤ ν) (h1 : ν < 1) :
    Summable fun k : ℤ => ν ^ k.natAbs := by
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨?_, ?_⟩
  · simpa using summable_geometric_of_lt_one h0 h1
  · simpa using summable_geometric_of_lt_one h0 h1

theorem lpMu_inv_lt_one : lpMu⁻¹ < 1 := inv_lt_one_of_one_lt₀ one_lt_lpMu

/-- `∑_k lpW(λ_k)^ρ < ∞` for every `ρ > 0`. -/
theorem summable_lpW_rpow {ρ : ℝ} (hρ : 0 < ρ) :
    Summable fun k : ℤ => lpW (lpLam k) ^ ρ := by
  have hν0 : 0 ≤ lpMu⁻¹ := (inv_pos.2 lpMu_pos).le
  have hνρ : lpMu⁻¹ ^ ρ < 1 := Real.rpow_lt_one hν0 lpMu_inv_lt_one hρ
  have hs : Summable fun k : ℤ => 512 ^ ρ * (lpMu⁻¹ ^ ρ) ^ k.natAbs :=
    (summable_geom_natAbs (Real.rpow_nonneg hν0 ρ) hνρ).mul_left _
  refine Summable.of_nonneg_of_le (fun k => Real.rpow_nonneg (lpW_nonneg (lpLam_pos k)) ρ)
    (fun k => ?_) hs
  calc lpW (lpLam k) ^ ρ ≤ (512 * lpMu⁻¹ ^ k.natAbs) ^ ρ :=
        Real.rpow_le_rpow (lpW_nonneg (lpLam_pos k)) (lpW_lpLam_le k).1 hρ.le
    _ = 512 ^ ρ * (lpMu⁻¹ ^ ρ) ^ k.natAbs := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_pow_comm hν0]

theorem summable_lpLam_mul_lpW : Summable fun k : ℤ => lpLam k * lpW (lpLam k) := by
  have hν0 : 0 ≤ lpMu⁻¹ := (inv_pos.2 lpMu_pos).le
  have hs : Summable fun k : ℤ => 512 * lpMu⁻¹ ^ k.natAbs :=
    (summable_geom_natAbs hν0 lpMu_inv_lt_one).mul_left _
  exact Summable.of_nonneg_of_le (fun k => mul_nonneg (lpLam_pos k).le (lpW_nonneg (lpLam_pos k)))
    (fun k => (lpW_lpLam_le k).2) hs

end PrimeBHT.TimeFrequency.RealLine

end
