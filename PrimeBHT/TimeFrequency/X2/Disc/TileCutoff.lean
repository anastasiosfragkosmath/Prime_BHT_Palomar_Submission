module

public import PrimeBHT.TimeFrequency.X2.Disc.Eta
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Algebra.Order.ToIntervalMod

/-!
# X2, node V05-5a: the tile cutoffs `χ_P = 1_{I_P} * η_s` lie in `X_I(𝔭)`; partition of unity

For `η` with `IsEtaCut` of constant `C'`, the tile cutoff `tileCutoff η s v` is in `InX 𝔭 s v` as soon as
`C' (3/2)^N ≤ 𝔭.C` (`disc_inX_tileCutoff`); `Σ_v tileCutoff η s v = 1` (`hasSum_tileCutoff`).
Together with `exists_etaCut`: if `N (3N/δ)^N (3/2)^N ≤ 𝔭.C` (N even) there is `η` with `IsEtaCut 𝔭 η` and
`InX 𝔭 s v (tileCutoff η s v)` for all `s, v` (`exists_eta_inX`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform Convolution ContDiff Real
open PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

theorem tileCutoff_eq {η : ℝ → ℝ} (_hη : Continuous η) (s v : ℤ) (x : ℝ) :
    tileCutoff η s v x = ∫ u in (x / 2 ^ s - v - 1)..(x / 2 ^ s - v), η u := by
  have hL : (2 : ℝ) ^ s ≠ 0 := zpow_ne_zero _ (by norm_num)
  unfold tileCutoff dyadicInt
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by
    have : (0 : ℝ) < 2 ^ s := zpow_pos (by norm_num) _
    nlinarith)]
  have h1 : ∀ y : ℝ, (2 : ℝ) ^ (-s) * η ((x - y) / 2 ^ s) = (2 : ℝ) ^ (-s) * η (x / 2 ^ s - y / 2 ^ s) := by
    intro y; rw [sub_div]
  simp_rw [h1]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_div (fun w => η w) hL]
  rw [smul_eq_mul, ← mul_assoc]
  have : (2 : ℝ) ^ (-s) * 2 ^ s = 1 := by rw [← zpow_add₀ (by norm_num)]; simp
  rw [this, one_mul]
  congr 1 <;> field_simp <;> ring

theorem tileCutoff_eq_centre {η : ℝ → ℝ} (hη : Continuous η) (s v : ℤ) (x : ℝ) :
    tileCutoff η s v x =
      ∫ w in ((x - dyCentre s v) / 2 ^ s - 1 / 2)..((x - dyCentre s v) / 2 ^ s + 1 / 2), η w := by
  rw [tileCutoff_eq hη]
  have hL : (2 : ℝ) ^ s ≠ 0 := zpow_ne_zero _ (by norm_num)
  unfold dyCentre
  congr 1 <;> field_simp <;> ring

theorem disc_continuous_tileCutoff {η : ℝ → ℝ} (hη : Continuous η) (s v : ℤ) : Continuous (tileCutoff η s v) := by
  have : tileCutoff η s v = fun x => (∫ u in (0 : ℝ)..(x / 2 ^ s - v), η u) -
      ∫ u in (0 : ℝ)..(x / 2 ^ s - v - 1), η u := by
    funext x
    rw [tileCutoff_eq hη, intervalIntegral.integral_interval_sub_left]
    · exact hη.intervalIntegrable _ _
    · exact hη.intervalIntegrable _ _
  rw [this]
  have hc := intervalIntegral.continuous_primitive (μ := volume) (fun a b => hη.intervalIntegrable a b) 0
  exact (hc.comp (by fun_prop)).sub (hc.comp (by fun_prop))

theorem jb_le_mul {u w : ℝ} (h : |w - u| ≤ 1 / 2) : jb u ≤ 3 / 2 * jb w := by
  unfold jb
  have := abs_sub_abs_le_abs_sub u w
  rw [abs_sub_comm] at this
  nlinarith [abs_nonneg w, abs_nonneg u]

theorem disc_tileCutoff_le {η : ℝ → ℝ} (hη : Continuous η) {C' : ℝ} {N : ℕ}
    (hb : ∀ x, η x ≤ C' * ((1 + |x|) ^ N)⁻¹) (hC' : 0 ≤ C') (s v : ℤ) (x : ℝ) :
    tileCutoff η s v x ≤ C' * (3 / 2) ^ N * ((1 + |(x - dyCentre s v) / 2 ^ s|) ^ N)⁻¹ := by
  set u := (x - dyCentre s v) / 2 ^ s with hu
  rw [tileCutoff_eq_centre hη]
  rw [← hu]
  have hpt : ∀ w ∈ Set.uIcc (u - 1 / 2) (u + 1 / 2),
      η w ≤ C' * (3 / 2) ^ N * ((1 + |u|) ^ N)⁻¹ := by
    intro w hw
    rw [Set.uIcc_of_le (by linarith)] at hw
    have hwu : |w - u| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hw.1, hw.2]
    have h1 := jb_le_mul hwu
    unfold jb at h1
    have hw0 : 0 < 1 + |w| := by positivity
    have hu0 : 0 < 1 + |u| := by positivity
    calc η w ≤ C' * ((1 + |w|) ^ N)⁻¹ := hb w
      _ ≤ C' * (3 / 2) ^ N * ((1 + |u|) ^ N)⁻¹ := by
        have : ((1 + |w|) ^ N)⁻¹ ≤ (3 / 2) ^ N * ((1 + |u|) ^ N)⁻¹ := by
          have h2 : (1 + |w|)⁻¹ ≤ 3 / 2 * (1 + |u|)⁻¹ := by
            rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hw0 hu0]
            linarith
          calc ((1 + |w|) ^ N)⁻¹ = ((1 + |w|)⁻¹) ^ N := (inv_pow _ _).symm
            _ ≤ (3 / 2 * (1 + |u|)⁻¹) ^ N := pow_le_pow_left₀ (by positivity) h2 N
            _ = (3 / 2) ^ N * ((1 + |u|)⁻¹) ^ N := mul_pow _ _ _
            _ = (3 / 2) ^ N * ((1 + |u|) ^ N)⁻¹ := by rw [inv_pow]
        calc C' * ((1 + |w|) ^ N)⁻¹ ≤ C' * ((3 / 2) ^ N * ((1 + |u|) ^ N)⁻¹) :=
              mul_le_mul_of_nonneg_left this hC'
          _ = C' * (3 / 2) ^ N * ((1 + |u|) ^ N)⁻¹ := by ring
  calc ∫ w in (u - 1 / 2)..(u + 1 / 2), η w
      ≤ ∫ w in (u - 1 / 2)..(u + 1 / 2), C' * (3 / 2) ^ N * ((1 + |u|) ^ N)⁻¹ :=
        intervalIntegral.integral_mono_on (by linarith) (hη.intervalIntegrable _ _)
          intervalIntegrable_const (fun w hw => hpt w (by rw [Set.uIcc_of_le (by linarith)]; exact hw))
    _ = C' * (3 / 2) ^ N * ((1 + |u|) ^ N)⁻¹ := by
        rw [intervalIntegral.integral_const]; simp; ring

theorem disc_le_tileCutoff {η : ℝ → ℝ} (hη : Continuous η) {C' : ℝ} {N : ℕ}
    (hb : ∀ x, C'⁻¹ * ((1 + |x|) ^ N)⁻¹ ≤ η x) (hC' : 0 < C') (s v : ℤ) (x : ℝ) :
    C'⁻¹ * (2 / 3) ^ N * ((1 + |(x - dyCentre s v) / 2 ^ s|) ^ N)⁻¹ ≤ tileCutoff η s v x := by
  set u := (x - dyCentre s v) / 2 ^ s with hu
  rw [tileCutoff_eq_centre hη]
  rw [← hu]
  have hpt : ∀ w ∈ Set.uIcc (u - 1 / 2) (u + 1 / 2),
      C'⁻¹ * (2 / 3) ^ N * ((1 + |u|) ^ N)⁻¹ ≤ η w := by
    intro w hw
    rw [Set.uIcc_of_le (by linarith)] at hw
    have hwu : |u - w| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hw.1, hw.2]
    have h1 := jb_le_mul hwu
    unfold jb at h1
    have hw0 : 0 < 1 + |w| := by positivity
    have hu0 : 0 < 1 + |u| := by positivity
    refine le_trans ?_ (hb w)
    have h2 : (2 / 3) * (1 + |u|)⁻¹ ≤ (1 + |w|)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hu0 hw0]
      linarith
    have : (2 / 3) ^ N * ((1 + |u|) ^ N)⁻¹ ≤ ((1 + |w|) ^ N)⁻¹ := by
      calc (2 / 3) ^ N * ((1 + |u|) ^ N)⁻¹ = (2 / 3 * (1 + |u|)⁻¹) ^ N := by rw [mul_pow, inv_pow]
        _ ≤ ((1 + |w|)⁻¹) ^ N := pow_le_pow_left₀ (by positivity) h2 N
        _ = ((1 + |w|) ^ N)⁻¹ := inv_pow _ _
    calc C'⁻¹ * (2 / 3) ^ N * ((1 + |u|) ^ N)⁻¹ = C'⁻¹ * ((2 / 3) ^ N * ((1 + |u|) ^ N)⁻¹) := by ring
      _ ≤ C'⁻¹ * ((1 + |w|) ^ N)⁻¹ := mul_le_mul_of_nonneg_left this (by positivity)
  calc C'⁻¹ * (2 / 3) ^ N * ((1 + |u|) ^ N)⁻¹
      = ∫ w in (u - 1 / 2)..(u + 1 / 2), C'⁻¹ * (2 / 3) ^ N * ((1 + |u|) ^ N)⁻¹ := by
        rw [intervalIntegral.integral_const]; simp; ring
    _ ≤ ∫ w in (u - 1 / 2)..(u + 1 / 2), η w :=
        intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
          (hη.intervalIntegrable _ _) (fun w hw => hpt w (by rw [Set.uIcc_of_le (by linarith)]; exact hw))

/-! ### Partition of unity -/

theorem hasSum_tileCutoff {η : ℝ → ℝ} (hη : Continuous η) (hint : Integrable η) (h1 : ∫ x, η x = 1)
    (s : ℤ) (x : ℝ) : HasSum (fun v : ℤ => tileCutoff η s v x) 1 := by
  set a : ℝ := x / 2 ^ s - 1 with ha
  have hS : ∀ n : ℤ, ∫ w in Ico (a + n) (a + n + 1), η w =
      tileCutoff η s (-n) x := by
    intro n
    rw [tileCutoff_eq hη, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    congr 1 <;> push_cast <;> ring
  have hsum : HasSum (fun n : ℤ => ∫ w in Ico (a + n) (a + n + 1), η w) 1 := by
    have h := hasSum_integral_iUnion (μ := volume) (f := η) (s := fun n : ℤ => Ico (a + n) (a + n + 1))
      (fun n => measurableSet_Ico) (pairwise_disjoint_Ico_add_intCast a) hint.integrableOn
    rw [iUnion_Ico_add_intCast, setIntegral_univ, h1] at h
    exact h
  have h2 : (fun v : ℤ => tileCutoff η s v x) = (fun n : ℤ => ∫ w in Ico (a + n) (a + n + 1), η w) ∘ (Equiv.neg ℤ) := by
    funext v
    simp only [Function.comp, Equiv.neg_apply]
    rw [hS, neg_neg]
  rw [h2]
  exact (Equiv.hasSum_iff (Equiv.neg ℤ)).2 hsum

/-! ### Fourier support -/

theorem fourier_etaScale (η : ℝ → ℝ) (s : ℤ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (((2 : ℝ) ^ (-s) * η (x / 2 ^ s) : ℝ) : ℂ)) ξ =
      𝓕 (fun x : ℝ => (η x : ℂ)) ((2 : ℝ) ^ s * ξ) := by
  have hL : (2 : ℝ) ^ s ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hL' : (2 : ℝ) ^ (-s) = ((2 : ℝ) ^ s)⁻¹ := zpow_neg _ _
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  set L : ℝ := (2 : ℝ) ^ s with hLdef
  have h := MeasureTheory.Measure.integral_comp_mul_left
    (fun x : ℝ => Complex.exp (↑(-2 * π * x * ξ) * Complex.I) • (((L⁻¹ * η (x / L) : ℝ)) : ℂ)) L
  rw [hL']
  have hL0 : 0 < L := zpow_pos (by norm_num) _
  have e1 : ∀ x : ℝ, Complex.exp (↑(-2 * π * (L * x) * ξ) * Complex.I) • (((L⁻¹ * η (L * x / L) : ℝ)) : ℂ) =
      (L⁻¹ : ℝ) • (Complex.exp (↑(-2 * π * x * (L * ξ)) * Complex.I) • ((η x : ℝ) : ℂ)) := by
    intro x
    rw [mul_div_cancel_left₀ _ hL]
    have : -2 * π * (L * x) * ξ = -2 * π * x * (L * ξ) := by ring
    rw [this]
    simp only [Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  simp_rw [e1] at h
  rw [integral_smul, abs_of_pos (inv_pos.2 hL0)] at h
  calc ∫ v : ℝ, Complex.exp (↑(-2 * π * v * ξ) * Complex.I) • (((L⁻¹ * η (v / L) : ℝ)) : ℂ)
      = L • (L⁻¹ • ∫ v : ℝ, Complex.exp (↑(-2 * π * v * (L * ξ)) * Complex.I) • ((η v : ℝ) : ℂ)) := by
        rw [h, smul_smul, mul_inv_cancel₀ hL, one_smul]
    _ = ∫ v : ℝ, Complex.exp (↑(-2 * π * v * (L * ξ)) * Complex.I) • ((η v : ℝ) : ℂ) := by
        rw [smul_smul, mul_inv_cancel₀ hL, one_smul]

theorem fourier_tileCutoff_eq_zero {η : ℝ → ℝ} (hint : Integrable η) {δ : ℝ}
    (hsupp : ∀ ξ, δ < |ξ| → 𝓕 (fun x : ℝ => (η x : ℂ)) ξ = 0) (s v : ℤ) {ξ : ℝ}
    (hξ : δ * (2 : ℝ) ^ (-s) < |ξ|) :
    𝓕 (fun x : ℝ => ((tileCutoff η s v x : ℝ) : ℂ)) ξ = 0 := by
  have hL : (0 : ℝ) < 2 ^ s := zpow_pos (by norm_num) _
  set f₁ : ℝ → ℂ := Set.indicator (dyadicInt s v) (fun _ => (1 : ℂ)) with hf₁def
  set f₂ : ℝ → ℂ := fun x => (((2 : ℝ) ^ (-s) * η (x / 2 ^ s) : ℝ) : ℂ) with hf₂def
  have hf₁ : Integrable f₁ := by
    refine (integrableOn_const (μ := volume) (s := dyadicInt s v) (C := (1 : ℂ)) ?_ ?_).integrable_indicator
      measurableSet_Ico
    · unfold dyadicInt; simp
    · simp
  have hf₂ : Integrable f₂ := by
    have h1 : Integrable (fun x : ℝ => η (x / 2 ^ s)) := by
      simpa [div_eq_inv_mul] using hint.comp_mul_left' (R := ((2 : ℝ) ^ s)⁻¹) (inv_ne_zero hL.ne')
    exact (h1.const_mul ((2 : ℝ) ^ (-s))).ofReal
  have hconv : (fun x : ℝ => ((tileCutoff η s v x : ℝ) : ℂ)) = f₁ ⋆[ContinuousLinearMap.mul ℂ ℂ] f₂ := by
    funext x
    rw [MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
    have : (fun t : ℝ => f₁ t * f₂ (x - t)) = Set.indicator (dyadicInt s v) (fun t => f₂ (x - t)) := by
      funext t
      by_cases ht : t ∈ dyadicInt s v <;> simp [hf₁def, ht]
    have hm : MeasurableSet (dyadicInt s v) := measurableSet_Ico
    rw [this, integral_indicator hm]
    unfold tileCutoff
    rw [← integral_complex_ofReal]
  rw [hconv, Real.fourier_mul_convolution_eq hf₁ hf₂, fourier_etaScale]
  have : δ < |(2 : ℝ) ^ s * ξ| := by
    rw [abs_mul, abs_of_pos hL]
    have h2 : (2 : ℝ) ^ s * (2 : ℝ) ^ (-s) = 1 := by rw [← zpow_add₀ (by norm_num)]; simp
    calc δ = 2 ^ s * (δ * 2 ^ (-s)) := by linear_combination (-δ) * h2
      _ < 2 ^ s * |ξ| := mul_lt_mul_of_pos_left hξ hL
  rw [hsupp _ this, mul_zero]

/-! ### `tileCutoff ∈ X_I(𝔭)` -/

/-- **V05-5a.**  If `η` satisfies `IsEtaCut` with the amplitude constant `C'` and `C' (3/2)^N ≤ 𝔭.C`, every tile cutoff
`1_{I} * η_s` is in `X_I(𝔭)`. -/
theorem disc_inX_tileCutoff {𝔭 : Params} {η : ℝ → ℝ} {C' : ℝ} (hη : IsEtaCut { 𝔭 with C := C' } η)
    (hC' : 0 < C') (hC : C' * (3 / 2) ^ 𝔭.N ≤ 𝔭.C) (s v : ℤ) : InX 𝔭 s v (tileCutoff η s v) := by
  obtain ⟨hcont, hnn, hint1, hup, hlow, hsupp⟩ := hη
  have hint : Integrable η := by
    by_contra h
    rw [integral_undef h] at hint1
    exact zero_ne_one hint1
  have hup' : ∀ x, η x ≤ C' * ((1 + |x|) ^ 𝔭.N)⁻¹ := by
    intro x
    have := hup x
    rwa [jb_rpow_neg_natCast] at this
  have hlow' : ∀ x, C'⁻¹ * ((1 + |x|) ^ 𝔭.N)⁻¹ ≤ η x := by
    intro x
    have := hlow x
    rwa [jb_rpow_neg_natCast] at this
  have hC0 : 0 < 𝔭.C := lt_of_lt_of_le (by positivity) hC
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact Complex.continuous_ofReal.comp (disc_continuous_tileCutoff hcont s v)
  · intro x
    rw [jb_rpow_neg_natCast, Complex.norm_real, Real.norm_eq_abs]
    have h0 : 0 ≤ tileCutoff η s v x := by
      have := disc_le_tileCutoff hcont hlow' hC' s v x
      exact le_trans (by positivity) this
    rw [abs_of_nonneg h0]
    refine (disc_tileCutoff_le hcont hup' hC'.le s v x).trans ?_
    exact mul_le_mul_of_nonneg_right hC (by positivity)
  · intro ξ hξ
    exact fourier_tileCutoff_eq_zero hint hsupp s v hξ
  · intro x
    rw [jb_rpow_neg_natCast]
    refine le_trans ?_ (disc_le_tileCutoff hcont hlow' hC' s v x)
    have h1 : 𝔭.C⁻¹ ≤ C'⁻¹ * (2 / 3) ^ 𝔭.N := by
      have h2 : C' * (3 / 2) ^ 𝔭.N ≤ 𝔭.C := hC
      have h3 : (0 : ℝ) < (3 / 2) ^ 𝔭.N := by positivity
      have : C'⁻¹ * (2 / 3) ^ 𝔭.N = (C' * (3 / 2) ^ 𝔭.N)⁻¹ := by
        rw [mul_inv, ← inv_pow]; norm_num
      rw [this]
      exact inv_anti₀ (by positivity) h2
    exact mul_le_mul_of_nonneg_right h1 (by positivity)

/-- **V05-1 + V05-5a combined.**  For `N` even `≥ 2`, `0 < δ ≤ 1/4` and `N (3N/δ)^N (3/2)^N ≤ 𝔭.C` there is a profile
`η` with `IsEtaCut 𝔭 η` whose tile cutoffs are all in `X_I(𝔭)` (the two conditions required by `IsModelData`).
(Condition on the amplitude: `N (9N/(2δ))^N ≤ 𝔭.C`.) -/
theorem exists_eta_inX (𝔭 : Params) (hN : Even 𝔭.N) (hN2 : 2 ≤ 𝔭.N) (hδ : 0 < 𝔭.δ) (hδ1 : 𝔭.δ ≤ 1 / 4)
    (hC : (𝔭.N : ℝ) * (3 * 𝔭.N / 𝔭.δ) ^ 𝔭.N * (3 / 2) ^ 𝔭.N ≤ 𝔭.C) :
    ∃ η : ℝ → ℝ, IsEtaCut 𝔭 η ∧ ∀ s v : ℤ, InX 𝔭 s v (tileCutoff η s v) := by
  set C' : ℝ := (𝔭.N : ℝ) * (3 * 𝔭.N / 𝔭.δ) ^ 𝔭.N with hC'
  have hN0 : (0 : ℝ) < 𝔭.N := by exact_mod_cast (by omega : 0 < 𝔭.N)
  have hC'0 : 0 < C' := by rw [hC']; positivity
  obtain ⟨η, hη⟩ := exists_etaCut { 𝔭 with C := C' } hN hN2 hδ hδ1 le_rfl
  refine ⟨η, ?_, fun s v => disc_inX_tileCutoff hη hC'0 hC s v⟩
  obtain ⟨hcont, hnn, hint1, hup, hlow, hsupp⟩ := hη
  have h1 : C' ≤ 𝔭.C := le_trans (le_mul_of_one_le_right hC'0.le (one_le_pow₀ (by norm_num))) hC
  refine ⟨hcont, hnn, hint1, fun x => ?_, fun x => ?_, hsupp⟩
  · exact (hup x).trans (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (jb_pos x).le _))
  · exact le_trans (mul_le_mul_of_nonneg_right (inv_anti₀ hC'0 h1) (Real.rpow_nonneg (jb_pos x).le _)) (hlow x)

end PrimeBHT.TimeFrequency.X2
