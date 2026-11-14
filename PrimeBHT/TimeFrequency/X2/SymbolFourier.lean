module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.PSeries

/-!
# X2, node V04 (auxiliary): Fourier series of smooth functions supported in `[-2, 2]`, on `[-4, 4)`

For `h : ℝ → ℂ` of class `C^∞` with `h x = 0` for `|x| > 2`, the Fourier coefficients on `[-4, 4)`
(period `8`), `fcoef h n = (1/8) ∫_{-4}^{4} h(x) e^{-iπ n x/4} dx` (Mathlib's `fourierCoeffOn`), satisfy:

* `norm_fcoef_mul_le`: `(1 + |n|)^N ‖fcoef h n‖ ≤ max M₀ ((8/π)^N M_N)` when `‖h‖ ≤ M₀` and
  `‖h^{(N)}‖ ≤ M_N` (`N` integrations by parts, Mathlib's `fourierCoeffOn_of_hasDerivAt`);
* `summable_fcoef`, and `hasSum_fcoef`: `h(s) = ∑_n fcoef h n e^{iπ n s/4}` for `-4 ≤ s < 4`
  (Mathlib's `has_pointwise_sum_fourier_series_of_summable`).

Also `summable_inv_one_add_abs_pow : 2 ≤ N → Summable (n ↦ ((1 + |n|)^N)⁻¹)` over `ℤ`.
-/

@[expose] public section

open MeasureTheory Complex
open scoped Real ComplexConjugate ContDiff

namespace PrimeBHT.TimeFrequency.X2

theorem norm_fourierCoeffOn_le {a b : ℝ} (hab : a < b) {h : ℝ → ℂ} {M : ℝ} (hM : ∀ x, ‖h x‖ ≤ M)
    (n : ℤ) : ‖fourierCoeffOn hab h n‖ ≤ M := by
  have hpos : 0 < b - a := sub_pos.2 hab
  rw [fourierCoeffOn_eq_integral, norm_smul]
  have h1 : ‖∫ x in a..b, fourier (-n) (x : AddCircle (b - a)) • h x‖ ≤ M * |b - a| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => ?_
    rw [norm_smul]
    have hn1 : ‖fourier (-n) (x : AddCircle (b - a))‖ = 1 := by
      rw [fourier_apply]; exact Circle.norm_coe _
    rw [hn1, one_mul]
    exact hM x
  rw [abs_of_pos hpos] at h1
  calc ‖(1 / (b - a) : ℝ)‖ * ‖∫ x in a..b, fourier (-n) (x : AddCircle (b - a)) • h x‖
      ≤ ‖(1 / (b - a) : ℝ)‖ * (M * (b - a)) := by gcongr
    _ = M := by
      rw [Real.norm_of_nonneg (by positivity)]
      field_simp

theorem norm_fourierCoeffOn_deriv {a b : ℝ} (hab : a < b) {h h' : ℝ → ℂ}
    (hd : ∀ x, HasDerivAt h (h' x) x) (hc' : Continuous h') (hper : h a = h b) {n : ℤ}
    (hn : n ≠ 0) :
    ‖fourierCoeffOn hab h n‖ = (b - a) / (2 * π * |(n : ℝ)|) * ‖fourierCoeffOn hab h' n‖ := by
  have := fourierCoeffOn_of_hasDerivAt hab hn (fun x _ => hd x) (hc'.intervalIntegrable a b)
  rw [this, ← hper, sub_self, mul_zero, zero_sub, norm_mul, norm_neg, norm_mul]
  have hpos : 0 < b - a := sub_pos.2 hab
  have hn' : (0 : ℝ) < |(n : ℝ)| := by positivity
  simp only [one_div, norm_inv, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, 
    Complex.norm_I, Complex.norm_intCast, norm_ofNat]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg hpos.le, abs_of_pos Real.pi_pos]
  field_simp

theorem norm_fourierCoeffOn_le_pow {a b : ℝ} (hab : a < b) (N : ℕ) :
    ∀ {h : ℝ → ℂ}, ContDiff ℝ ∞ h → (∀ k : ℕ, iteratedDeriv k h a = iteratedDeriv k h b) →
    ∀ {M : ℝ}, (∀ x, ‖iteratedDeriv N h x‖ ≤ M) → ∀ {n : ℤ}, n ≠ 0 →
    ‖fourierCoeffOn hab h n‖ ≤ ((b - a) / (2 * π * |(n : ℝ)|)) ^ N * M := by
  induction N with
  | zero =>
    intro h hh hper M hM n hn
    simpa using norm_fourierCoeffOn_le hab (by simpa using hM) n
  | succ N ih =>
    intro h hh hper M hM n hn
    have hdiff : Differentiable ℝ h := (contDiff_infty_iff_deriv.1 hh).1
    have hh' : ContDiff ℝ ∞ (deriv h) := (contDiff_infty_iff_deriv.1 hh).2
    have hd : ∀ x, HasDerivAt h (deriv h x) x := fun x => (hdiff x).hasDerivAt
    have hstep := norm_fourierCoeffOn_deriv hab hd hh'.continuous (by simpa using hper 0) hn
    have hrec := ih hh' (fun k => by simpa [iteratedDeriv_succ'] using hper (k + 1))
      (M := M) (fun x => by simpa [iteratedDeriv_succ'] using hM x) hn
    have hpos : 0 ≤ (b - a) / (2 * π * |(n : ℝ)|) := by
      have : 0 < b - a := sub_pos.2 hab
      positivity
    rw [hstep]
    calc (b - a) / (2 * π * |(n : ℝ)|) * ‖fourierCoeffOn hab (deriv h) n‖
        ≤ (b - a) / (2 * π * |(n : ℝ)|) * (((b - a) / (2 * π * |(n : ℝ)|)) ^ N * M) :=
          mul_le_mul_of_nonneg_left hrec hpos
      _ = ((b - a) / (2 * π * |(n : ℝ)|)) ^ (N + 1) * M := by ring

theorem hasSum_fourierCoeffOn {a T : ℝ} (hT : 0 < T) {h : ℝ → ℂ} (hc : Continuous h)
    (hper : h a = h (a + T))
    (hsum : Summable (fun n : ℤ => fourierCoeffOn (lt_add_of_pos_right a hT) h n)) {s : ℝ}
    (hs : s ∈ Set.Ico a (a + T)) :
    HasSum (fun n : ℤ => fourierCoeffOn (lt_add_of_pos_right a hT) h n *
      Complex.exp (2 * π * I * n * s / T)) (h s) := by
  have : Fact (0 < T) := ⟨hT⟩
  have hcont : Continuous (AddCircle.liftIco T a h) :=
    AddCircle.liftIco_continuous hper hc.continuousOn
  let f : C(AddCircle T, ℂ) := ⟨_, hcont⟩
  have hco : fourierCoeff f = fun n : ℤ => fourierCoeffOn (lt_add_of_pos_right a hT) h n :=
    funext fun n => fourierCoeff_liftIco_eq h n
  have hsum' : Summable (fourierCoeff f) := by rw [hco]; exact hsum
  have := has_pointwise_sum_fourier_series_of_summable hsum' (s : AddCircle T)
  have hfs : f (s : AddCircle T) = h s := AddCircle.liftIco_coe_apply hs
  rw [hfs] at this
  convert this using 2 with n
  rw [hco, smul_eq_mul, fourier_coe_apply]

/-! ### Specialization to `[-4, 4)` -/

/-- The Fourier coefficients on `[-4, 4)` (period `8`) of `h : ℝ → ℂ`. -/
noncomputable def fcoef (h : ℝ → ℂ) (n : ℤ) : ℂ :=
  fourierCoeffOn (lt_add_of_pos_right (-4 : ℝ) (by norm_num : (0 : ℝ) < 8)) h n

theorem iteratedDeriv_eq_zero_of_vanish {h : ℝ → ℂ} (hvan : ∀ x, 2 < |x| → h x = 0) (k : ℕ) {x : ℝ}
    (hx : 2 < |x|) : iteratedDeriv k h x = 0 := by
  have hev : h =ᶠ[nhds x] fun _ => (0 : ℂ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hx] with y hy using hvan y hy
  rw [hev.iteratedDeriv_eq k]
  simp

theorem hasCompactSupport_of_vanish {h : ℝ → ℂ} (hvan : ∀ x, 2 < |x| → h x = 0) :
    HasCompactSupport h := by
  refine HasCompactSupport.intro (K := Set.Icc (-2 : ℝ) 2) isCompact_Icc fun x hx => hvan x ?_
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hx | hx
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem exists_bound_iteratedDeriv {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) (hvan : ∀ x, 2 < |x| → h x = 0)
    (N : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖iteratedDeriv N h x‖ ≤ M := by
  obtain ⟨C, hC0, hC⟩ := (hasCompactSupport_of_vanish hvan).exists_bound_iteratedFDeriv hh N
  exact ⟨C, hC0, fun x => by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact hC N le_rfl x⟩

theorem norm_fcoef_mul_le {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) (hvan : ∀ x, 2 < |x| → h x = 0) (N : ℕ)
    {M₀ M : ℝ} (hM₀ : ∀ x, ‖h x‖ ≤ M₀) (hM : ∀ x, ‖iteratedDeriv N h x‖ ≤ M) (n : ℤ) :
    (1 + |(n : ℝ)|) ^ N * ‖fcoef h n‖ ≤ max M₀ ((8 / π) ^ N * M) := by
  have hper : ∀ k : ℕ, iteratedDeriv k h (-4) = iteratedDeriv k h (-4 + 8) := fun k => by
    rw [iteratedDeriv_eq_zero_of_vanish hvan k (by norm_num [abs_of_neg]),
      iteratedDeriv_eq_zero_of_vanish hvan k (by norm_num [abs_of_pos])]
  by_cases hn : n = 0
  · subst hn
    simp only [Int.cast_zero, abs_zero, add_zero, one_pow, one_mul]
    exact (norm_fourierCoeffOn_le _ hM₀ 0).trans (le_max_left _ _)
  · have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
      exact_mod_cast this
    have hb := norm_fourierCoeffOn_le_pow (lt_add_of_pos_right (-4 : ℝ) (by norm_num : (0 : ℝ) < 8))
      N hh hper hM hn
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have e8 : ((-4 + 8 : ℝ) - (-4)) = 8 := by norm_num
    rw [e8] at hb
    have hnpos : 0 < |(n : ℝ)| := by linarith
    calc (1 + |(n : ℝ)|) ^ N * ‖fcoef h n‖
        ≤ (2 * |(n : ℝ)|) ^ N * ((8 / (2 * π * |(n : ℝ)|)) ^ N * M) := by
          gcongr
          · linarith
          · exact hb
      _ = (8 / π) ^ N * M := by
          rw [← mul_assoc, ← mul_pow]
          congr 2
          field_simp
      _ ≤ max M₀ ((8 / π) ^ N * M) := le_max_right _ _

theorem summable_inv_one_add_abs_pow {N : ℕ} (hN : 2 ≤ N) :
    Summable (fun n : ℤ => ((1 + |(n : ℝ)|) ^ N)⁻¹) := by
  have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ N)⁻¹) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 (by omega : 1 < N))
    simpa using this
  refine summable_int_iff_summable_nat_and_neg.2 ⟨?_, ?_⟩
  · refine h1.congr fun n => ?_
    simp [add_comm]
  · refine h1.congr fun n => ?_
    simp [add_comm]

theorem summable_fcoef {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) (hvan : ∀ x, 2 < |x| → h x = 0) :
    Summable (fcoef h) := by
  obtain ⟨M₀, -, hM₀⟩ := exists_bound_iteratedDeriv hh hvan 0
  obtain ⟨M₂, -, hM₂⟩ := exists_bound_iteratedDeriv hh hvan 2
  refine Summable.of_norm_bounded ((summable_inv_one_add_abs_pow (le_refl 2)).mul_left
    (max M₀ ((8 / π) ^ 2 * M₂))) fun n => ?_
  have := norm_fcoef_mul_le hh hvan 2 (M₀ := M₀) (M := M₂) (by simpa using hM₀) hM₂ n
  have hpos : 0 < (1 + |(n : ℝ)|) ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
  exact this

theorem hasSum_fcoef {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) (hvan : ∀ x, 2 < |x| → h x = 0) {s : ℝ}
    (hs : -4 ≤ s ∧ s < 4) :
    HasSum (fun n : ℤ => fcoef h n * Complex.exp (π * I * n * s / 4)) (h s) := by
  have := hasSum_fourierCoeffOn (a := -4) (T := 8) (by norm_num) hh.continuous
    (by rw [hvan (-4) (by norm_num [abs_of_neg]), hvan (-4 + 8) (by norm_num [abs_of_pos])])
    (summable_fcoef hh hvan) (s := s) ⟨hs.1, by linarith [hs.2]⟩
  convert this using 3 with n
  · rfl
  · congr 1
    push_cast
    ring

end PrimeBHT.TimeFrequency.X2
