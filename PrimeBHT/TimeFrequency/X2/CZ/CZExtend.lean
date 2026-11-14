module

public import PrimeBHT.TimeFrequency.X2.CZ.CZStrong
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# V08 addendum: from the class `𝒞` to bounded measurable functions of finite `L^q(L^s)` norm

For a bounded measurable kernel `Φ` with the size bound `|Φ(x, u)| ≤ 1/|x - u|`, the function
`u ↦ Φ(x, u)` lies in `L^r(ℝ)` for every `r > 1` (`lintegral_kernel_rpow_lt_top`); hence `Φ(x, ·) F(·, y)` is
integrable for `F(·, y) ∈ L^q`, and (dominated convergence) the truncations `F 1_{|u| ≤ R}` converge:
`kop Φ (F 1_{|·| ≤ R}) x → kop Φ F x`.  Fatou then extends a strong `(q, s)` bound valid on `𝒞` to all bounded
measurable `F` (`kStrong_extend`).  No Bochner "junk zero" can enter.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology Real ComplexConjugate

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

open PrimeBHT.Statements

section Kernel

variable {Φ : ℝ → ℝ → ℂ}

theorem norm_kernel_le_japanese {M : ℝ} (hM : ∀ x u, ‖Φ x u‖ ≤ M)
    (hsz : ∀ x u, x ≠ u → ‖Φ x u‖ ≤ 1 / |x - u|) (x u : ℝ) :
    ‖Φ x u‖ ≤ (2 * max M 1) * (1 + |x - u|) ^ (-1 : ℝ) := by
  have hd := abs_nonneg (x - u)
  have hmax : 1 ≤ max M 1 := le_max_right _ _
  have hMm : M ≤ max M 1 := le_max_left _ _
  rw [Real.rpow_neg_one]
  have h1 : 0 < 1 + |x - u| := by linarith
  rw [← div_eq_mul_inv, le_div_iff₀ h1]
  by_cases hx : |x - u| ≤ 1
  · calc ‖Φ x u‖ * (1 + |x - u|) ≤ M * 2 := by
          have : 0 ≤ ‖Φ x u‖ := norm_nonneg _
          nlinarith [hM x u]
      _ ≤ 2 * max M 1 := by linarith
  · push Not at hx
    have hne : x ≠ u := by
      intro h; rw [h, sub_self, abs_zero] at hx; linarith
    have hpos : 0 < |x - u| := by linarith
    have := hsz x u hne
    calc ‖Φ x u‖ * (1 + |x - u|) ≤ 1 / |x - u| * (1 + |x - u|) :=
          mul_le_mul_of_nonneg_right this h1.le
      _ ≤ 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hpos]; linarith
      _ ≤ 2 * max M 1 := by linarith

/-- `Φ(x, ·) ∈ L^r(ℝ)` for `r > 1`: the `r`-th power has finite integral. -/
theorem lintegral_kernel_rpow_lt_top (_hΦm : Measurable (Function.uncurry Φ)) {M : ℝ}
    (hM : ∀ x u, ‖Φ x u‖ ≤ M) (hsz : ∀ x u, x ≠ u → ‖Φ x u‖ ≤ 1 / |x - u|) {r : ℝ} (hr : 1 < r) (x : ℝ) :
    ∫⁻ u, ‖Φ x u‖ₑ ^ r < ⊤ := by
  have hr0 : 0 < r := by linarith
  have hint : Integrable (fun u : ℝ => (1 + ‖x - u‖) ^ (-r)) volume := by
    have h0 : Integrable (fun v : ℝ => (1 + ‖v‖) ^ (-r)) volume :=
      integrable_one_add_norm (by simpa using hr)
    exact h0.comp_sub_left x
  have hint' : Integrable (fun u : ℝ => (2 * max M 1) ^ r * (1 + ‖x - u‖) ^ (-r)) volume :=
    hint.const_mul _
  refine lt_of_le_of_lt (lintegral_mono fun u => ?_) hint'.lintegral_lt_top
  have h1 := norm_kernel_le_japanese hM hsz x u
  have hd : 0 < 1 + |x - u| := by have := abs_nonneg (x - u); linarith
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖Φ x u‖ ^ r ≤ ((2 * max M 1) * (1 + |x - u|) ^ (-1 : ℝ)) ^ r :=
        Real.rpow_le_rpow (norm_nonneg _) h1 hr0.le
    _ = (2 * max M 1) ^ r * (1 + ‖x - u‖) ^ (-r) := by
        rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hd.le _), ← Real.rpow_mul hd.le,
          Real.norm_eq_abs]
        congr 2; ring

/-- A product of `L^{q'}` and `L^q` functions is integrable (Hölder). -/
theorem integrable_mul_of_lintegral {f g : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) {q q' : ℝ} (hq : q'.HolderConjugate q)
    (hfi : ∫⁻ u, ‖f u‖ₑ ^ q' < ⊤) (hgi : ∫⁻ u, ‖g u‖ₑ ^ q < ⊤) :
    Integrable (fun u => f u * g u) volume := by
  refine ⟨hf.mul hg, ?_⟩
  unfold HasFiniteIntegral
  have hfm : AEMeasurable (fun u => ‖f u‖ₑ) volume := hf.enorm
  have hgm : AEMeasurable (fun u => ‖g u‖ₑ) volume := hg.enorm
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hq hfm hgm
  simp only [Pi.mul_apply] at h
  simp_rw [enorm_mul]
  refine lt_of_le_of_lt h (ENNReal.mul_lt_top ?_ ?_)
  · exact ENNReal.rpow_lt_top_of_nonneg (by have := hq.pos; positivity) hfi.ne
  · exact ENNReal.rpow_lt_top_of_nonneg (by have := hq.symm.pos; positivity) hgi.ne

end Kernel

section Extend

variable {P : ℕ} [NeZero P]

/-- The truncation `F 1_{|u| ≤ R}`. -/
def cutoff (R : ℕ) (F : ℝ → ZMod P → ℂ) : ℝ → ZMod P → ℂ := fun u y => if |u| ≤ R then F u y else 0

theorem yNorm_cutoff_le {s : ℝ} (hs : 0 < s) (R : ℕ) (F : ℝ → ZMod P → ℂ) (u : ℝ) :
    yNorm s (cutoff R F u) ≤ yNorm s (F u) := by
  unfold cutoff
  by_cases h : |u| ≤ R
  · simp [h]
  · have : (fun y => if |u| ≤ R then F u y else 0) = 0 := by ext y; simp [h]
    rw [this, yNorm_zero' hs]; exact yNorm_nonneg s _

theorem isTestFun_cutoff {s : ℝ} (hs : 0 < s) (R : ℕ) {F : ℝ → ZMod P → ℂ}
    (hFm : ∀ y, Measurable fun u => F u y) {B : ℝ} (hB : ∀ u, yNorm s (F u) ≤ B) :
    IsTestFun (cutoff R F) := by
  have hP : (0 : ℝ) ≤ (P : ℝ) ^ s⁻¹ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨fun y => ?_, ⟨(P : ℝ) ^ s⁻¹ * B, fun u y => ?_⟩, ⟨R, fun u hu y => ?_⟩⟩
  · exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const) (hFm y)
      measurable_const
  · unfold cutoff
    by_cases h : |u| ≤ R
    · simp only [h, ite_true]
      exact (norm_le_rpow_mul_yNorm hs (F u) y).trans (mul_le_mul_of_nonneg_left (hB u) hP)
    · simp only [h, ite_false, norm_zero]
      exact mul_nonneg hP ((yNorm_nonneg s _).trans (hB 0))
  · unfold cutoff
    have : ¬ |u| ≤ R := not_le.2 hu
    simp [this]

theorem lintegral_norm_fibre_lt_top {s q : ℝ} (hs : 0 < s) (hq : 0 < q) {F : ℝ → ZMod P → ℂ}
    (hFq : ∫⁻ u, ENNReal.ofReal (yNorm s (F u)) ^ q < ⊤) (y : ZMod P) :
    ∫⁻ u, ‖F u y‖ₑ ^ q < ⊤ := by
  have hc : (ENNReal.ofReal ((P : ℝ) ^ s⁻¹)) ^ q < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg hq.le ENNReal.ofReal_ne_top
  calc ∫⁻ u, ‖F u y‖ₑ ^ q ≤ ∫⁻ u, (ENNReal.ofReal ((P : ℝ) ^ s⁻¹)) ^ q *
          ENNReal.ofReal (yNorm s (F u)) ^ q := by
        refine lintegral_mono fun u => ?_
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.ofReal_mul (Real.rpow_nonneg
          (Nat.cast_nonneg _) _), ← ofReal_norm]
        exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (norm_le_rpow_mul_yNorm hs (F u) y)) hq.le
    _ = (ENNReal.ofReal ((P : ℝ) ^ s⁻¹)) ^ q * ∫⁻ u, ENNReal.ofReal (yNorm s (F u)) ^ q :=
        lintegral_const_mul' _ _ hc.ne
    _ < ⊤ := ENNReal.mul_lt_top hc hFq

/-- **Extension of a strong `(q, s)` bound from `𝒞` to bounded measurable `F` of finite `L^q(L^s)` norm**
(Fatou along the truncations; dominated convergence by Hölder, using the size bound of the kernel). -/
theorem kStrong_extend {Φ : ℝ → ℝ → ℂ} {M : ℝ} (hΦm : Measurable (Function.uncurry Φ))
    (hM : ∀ x u, ‖Φ x u‖ ≤ M) (hsz : ∀ x u, x ≠ u → ‖Φ x u‖ ≤ 1 / |x - u|) {q s A : ℝ} (hq : 1 < q)
    (hs : 1 < s) (hK : KStrong P Φ q s A) {F : ℝ → ZMod P → ℂ}
    (hFm : ∀ y, Measurable fun u => F u y) {B : ℝ} (hB : ∀ u, yNorm s (F u) ≤ B)
    (hFq : ∫⁻ u, ENNReal.ofReal (yNorm s (F u)) ^ q < ⊤) :
    ∫⁻ x, ENNReal.ofReal (yNorm s (fun y => kop Φ (fun u => F u y) x)) ^ q ≤
      ENNReal.ofReal A ^ q * ∫⁻ u, ENNReal.ofReal (yNorm s (F u)) ^ q := by
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < s := by linarith
  have hq' := Real.HolderConjugate.conjExponent hq
  have hbound : ∀ R : ℕ, ∫⁻ x, ENNReal.ofReal (yNorm s (fun y => kop Φ (fun u => cutoff R F u y) x)) ^ q ≤
      ENNReal.ofReal A ^ q * ∫⁻ u, ENNReal.ofReal (yNorm s (F u)) ^ q := by
    intro R
    refine (hK (cutoff R F) (isClassC_of_testFun (isTestFun_cutoff hs0 R hFm hB))).trans ?_
    refine mul_le_mul' le_rfl (lintegral_mono fun u => ?_)
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (yNorm_cutoff_le hs0 R F u)) hq0.le
  have hmeas : ∀ R : ℕ, Measurable fun x => ENNReal.ofReal (yNorm s (fun y => kop Φ
      (fun u => cutoff R F u y) x)) ^ q := fun R =>
    ((measurable_yNorm s (fun y => measurable_kop hΦm ((isTestFun_cutoff hs0 R hFm hB).1 y))).ennreal_ofReal).pow_const q
  -- pointwise convergence
  have hlim_y : ∀ x y, Tendsto (fun R : ℕ => kop Φ (fun u => cutoff R F u y) x) atTop
      (nhds (kop Φ (fun u => F u y) x)) := by
    intro x y
    have hΦx : Measurable fun u => Φ x u := hΦm.comp (measurable_const.prodMk measurable_id)
    have hint : Integrable (fun u => Φ x u * F u y) volume :=
      integrable_mul_of_lintegral hΦx.aestronglyMeasurable (hFm y).aestronglyMeasurable hq'.symm
        (lintegral_kernel_rpow_lt_top hΦm hM hsz (one_lt_conjExponent' hq) x)
        (lintegral_norm_fibre_lt_top hs0 hq0 hFq y)
    unfold kop
    refine tendsto_integral_of_dominated_convergence (fun u => ‖Φ x u * F u y‖) (fun R => ?_) hint.norm
      (fun R => ae_of_all _ fun u => ?_) (ae_of_all _ fun u => ?_)
    · exact (hΦx.mul ((isTestFun_cutoff hs0 R hFm hB).1 y)).aestronglyMeasurable
    · unfold cutoff
      by_cases h : |u| ≤ R
      · simp only [h, ite_true, le_refl]
      · simp only [h, ite_false, mul_zero, norm_zero]; exact norm_nonneg _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈|u|⌉₊] with R hR
      have : |u| ≤ R := (Nat.le_ceil _).trans (by exact_mod_cast hR)
      unfold cutoff
      simp [this]
  have hlim : ∀ x, Tendsto (fun R : ℕ => ENNReal.ofReal (yNorm s (fun y => kop Φ
      (fun u => cutoff R F u y) x)) ^ q) atTop
      (nhds (ENNReal.ofReal (yNorm s (fun y => kop Φ (fun u => F u y) x)) ^ q)) := by
    intro x
    have h1 : Tendsto (fun R : ℕ => yNorm s (fun y => kop Φ (fun u => cutoff R F u y) x)) atTop
        (nhds (yNorm s (fun y => kop Φ (fun u => F u y) x))) :=
      ((continuous_yNorm hs0).tendsto _).comp (tendsto_pi_nhds.2 fun y => hlim_y x y)
    exact ((ENNReal.continuous_rpow_const (y := q)).tendsto _).comp
      ((ENNReal.continuous_ofReal.tendsto _).comp h1)
  exact lintegral_le_of_tendsto_of_le hmeas hlim hbound

end Extend

end PrimeBHT.TimeFrequency.X2.CZ
