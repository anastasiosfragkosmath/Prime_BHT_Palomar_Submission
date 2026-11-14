module

public import PrimeBHT.TimeFrequency.X2.Ortho.Gram
public import PrimeBHT.TimeFrequency.X2.Ortho.Closing

/-!
# X2, node V12-top (TB-5, Layer A): the abstract Bessel inequality for separated dual families

The TT* argument of MTT2 (L2860-2950) in the form of V10's dual vectors, for an arbitrary finite index family:

`DualFam F 𝒮 C₀ ℓ c a z Ov`: for each index `i` a length `ℓ_i`, a centre `c_i`, an amplitude `a_i ≥ 0` and a vector
function `z_i` with (Z1) `⟨z_i, F⟩ = a_i²`, (Z2) `‖z_i(x)‖_{L²(Y)} ≤ C₀ ℓ_i^{-1/2} a_i wt₆(c_i, ℓ_i)(x)`,
(Z3) `⟨z_i, z_j⟩ = 0` unless the indices overlap (`Ov i j`).

`bessel_of_sep`: if the overlapping smaller-or-equal indices of each `i` have pairwise disjoint time intervals
`[c_j - ℓ_j/2, c_j + ℓ_j/2)` (the top separation lemma, `TopSelect.lean`) and the normalized amplitudes
`ĉ_i = ℓ_i^{-1/2} a_i` lie in `[μ/4, Kμ]`, then `Σ a_i² ≤ 64 C₀² K ‖F‖²`.
`single_bound`: for one index, `a ≤ C ‖F‖₂` and `ĉ ≤ C B` if `‖F‖_∞ ≤ B`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open PrimeBHT.Statements

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

section Bessel

variable {P : ℕ} [NeZero P] {ι : Type*}

/-- The dual data (Z1)-(Z3) of a family of indices. -/
structure DualFam (F : ℝ → ZMod P → ℂ) (𝒮 : Finset ι) (C₀ : ℝ) (ℓ c a : ι → ℝ)
    (z : ι → ℝ → ZMod P → ℂ) (Ov : ι → ι → Prop) : Prop where
  pos : ∀ i ∈ 𝒮, 0 < ℓ i
  nonneg : ∀ i ∈ 𝒮, 0 ≤ a i
  meas : ∀ i ∈ 𝒮, Measurable (z i)
  inner_F : ∀ i ∈ 𝒮, ∫ x, yInner (z i x) (F x) = ((a i ^ 2 : ℝ) : ℂ)
  bound : ∀ i ∈ 𝒮, ∀ x, yNorm 2 (z i x) ≤ C₀ * ℓ i ^ (-(1 : ℝ) / 2) * a i * wt 6 (c i) (ℓ i) x
  orth : ∀ i ∈ 𝒮, ∀ j ∈ 𝒮, ¬ Ov i j → ∫ x, yInner (z i x) (z j x) = 0

/-- `ĉ_i = ℓ_i^{-1/2} a_i`. -/
def chatF (ℓ a : ι → ℝ) (i : ι) : ℝ := ℓ i ^ (-(1 : ℝ) / 2) * a i

theorem ell_mul_chatF_sq {ℓ : ι → ℝ} {i : ι} (h : 0 < ℓ i) (a : ι → ℝ) :
    ℓ i * chatF ℓ a i ^ 2 = a i ^ 2 := by
  unfold chatF
  rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul h.le]
  have : ℓ i * ℓ i ^ ((-(1 : ℝ) / 2) * ((2 : ℕ) : ℝ)) = 1 := by
    rw [show ((-(1 : ℝ) / 2) * ((2 : ℕ) : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
    field_simp
  calc ℓ i * (ℓ i ^ ((-(1 : ℝ) / 2) * ((2 : ℕ) : ℝ)) * a i ^ 2) =
      (ℓ i * ℓ i ^ ((-(1 : ℝ) / 2) * ((2 : ℕ) : ℝ))) * a i ^ 2 := by ring
    _ = a i ^ 2 := by rw [this, one_mul]

variable {F : ℝ → ZMod P → ℂ} {𝒮 : Finset ι} {C₀ : ℝ} {ℓ c a : ι → ℝ} {z : ι → ℝ → ZMod P → ℂ}
  {Ov : ι → ι → Prop}

theorem chatF_nonneg (h : DualFam F 𝒮 C₀ ℓ c a z Ov) {i : ι} (hi : i ∈ 𝒮) : 0 ≤ chatF ℓ a i :=
  mul_nonneg (Real.rpow_nonneg (h.pos i hi).le _) (h.nonneg i hi)

/-- `J(i, j) = ∫ wt₆(c_i, ℓ_i) wt₆(c_j, ℓ_j)`. -/
def Jw (ℓ c : ι → ℝ) (i j : ι) : ℝ := ∫ x, wt 6 (c i) (ℓ i) x * wt 6 (c j) (ℓ j) x

theorem integrable_wt_mul' {c₁ ℓ₁ c₂ ℓ₂ : ℝ} (h₁ : 0 < ℓ₁) (h₂ : 0 < ℓ₂) :
    Integrable (fun x => wt 6 c₁ ℓ₁ x * wt 6 c₂ ℓ₂ x) := by
  refine Integrable.mono' (integrable_wt (q := 6) (by norm_num) c₁ h₁)
    ((continuous_wt 6 _ _ h₁).mul (continuous_wt 6 _ _ h₂)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (wt_pos _ _ _ _ h₁).le (wt_pos _ _ _ _ h₂).le)]
  calc _ ≤ wt 6 c₁ ℓ₁ x * 1 :=
        mul_le_mul_of_nonneg_left (wt_le_one (by norm_num) _ _ _ h₂) (wt_pos _ _ _ _ h₁).le
    _ = _ := mul_one _

theorem Jw_comm (ℓ c : ι → ℝ) (i j : ι) : Jw ℓ c i j = Jw ℓ c j i := by
  unfold Jw
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

theorem Jw_nonneg (h : DualFam F 𝒮 C₀ ℓ c a z Ov) {i j : ι} (hi : i ∈ 𝒮) (hj : j ∈ 𝒮) :
    0 ≤ Jw ℓ c i j :=
  integral_nonneg fun _x => mul_nonneg (wt_pos _ _ _ _ (h.pos i hi)).le (wt_pos _ _ _ _ (h.pos j hj)).le

/-- The pointwise product bound. -/
theorem yy_le' (h : DualFam F 𝒮 C₀ ℓ c a z Ov) (hC₀ : 0 ≤ C₀) {i j : ι} (hi : i ∈ 𝒮) (hj : j ∈ 𝒮) (x : ℝ) :
    yNorm 2 (z i x) * yNorm 2 (z j x) ≤
      C₀ ^ 2 * (chatF ℓ a i * chatF ℓ a j) * (wt 6 (c i) (ℓ i) x * wt 6 (c j) (ℓ j) x) := by
  have h1 := h.bound i hi x
  have h2 := h.bound j hj x
  have hn : ∀ t : ι, 0 ≤ yNorm 2 (z t x) := fun t => by unfold yNorm; positivity
  calc yNorm 2 (z i x) * yNorm 2 (z j x) ≤ (C₀ * ℓ i ^ (-(1 : ℝ) / 2) * a i * wt 6 (c i) (ℓ i) x) *
        (C₀ * ℓ j ^ (-(1 : ℝ) / 2) * a j * wt 6 (c j) (ℓ j) x) :=
      mul_le_mul h1 h2 (hn j) (mul_nonneg (mul_nonneg (mul_nonneg hC₀
        (Real.rpow_nonneg (h.pos i hi).le _)) (h.nonneg i hi)) (wt_pos _ _ _ _ (h.pos i hi)).le)
    _ = _ := by unfold chatF; ring

theorem integrable_yy' (h : DualFam F 𝒮 C₀ ℓ c a z Ov) (hC₀ : 0 ≤ C₀) {i j : ι} (hi : i ∈ 𝒮) (hj : j ∈ 𝒮) :
    Integrable (fun x => yNorm 2 (z i x) * yNorm 2 (z j x)) := by
  have hm : ∀ t ∈ 𝒮, Measurable fun x => yNorm 2 (z t x) := fun t ht =>
    (measurable_yNorm_fun 2).comp (h.meas t ht)
  refine ((integrable_wt_mul' (c₁ := c i) (c₂ := c j) (h.pos i hi) (h.pos j hj)).const_mul
    (C₀ ^ 2 * (chatF ℓ a i * chatF ℓ a j))).mono'
    ((hm i hi).mul (hm j hj)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hn : 0 ≤ yNorm 2 (z i x) * yNorm 2 (z j x) := by unfold yNorm; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact yy_le' h hC₀ hi hj x

theorem integral_yy_le' (h : DualFam F 𝒮 C₀ ℓ c a z Ov) (hC₀ : 0 ≤ C₀) {i j : ι} (hi : i ∈ 𝒮) (hj : j ∈ 𝒮) :
    ∫ x, yNorm 2 (z i x) * yNorm 2 (z j x) ≤ C₀ ^ 2 * (chatF ℓ a i * chatF ℓ a j) * Jw ℓ c i j := by
  unfold Jw
  rw [← integral_const_mul]
  exact integral_mono (integrable_yy' h hC₀ hi hj)
    ((integrable_wt_mul' (c₁ := c i) (c₂ := c j) (h.pos i hi) (h.pos j hj)).const_mul _) fun x => yy_le' h hC₀ hi hj x

theorem norm_inner_le' (h : DualFam F 𝒮 C₀ ℓ c a z Ov) (hC₀ : 0 ≤ C₀) {i j : ι} (hi : i ∈ 𝒮)
    (hj : j ∈ 𝒮) : ‖∫ x, yInner (z i x) (z j x)‖ ≤ ∫ x, yNorm 2 (z i x) * yNorm 2 (z j x) := by
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) (integrable_yy' h hC₀ hi hj)
    (Eventually.of_forall fun x => norm_yInner_le _ _)

theorem integrable_yInner' (h : DualFam F 𝒮 C₀ ℓ c a z Ov) (hC₀ : 0 ≤ C₀) {i j : ι} (hi : i ∈ 𝒮)
    (hj : j ∈ 𝒮) : Integrable (fun x => yInner (z i x) (z j x)) := by
  have h1 : ∀ y : ZMod P, Measurable fun x => z i x y := fun y => (measurable_pi_apply y).comp (h.meas i hi)
  have h2 : ∀ y : ZMod P, Measurable fun x => z j x y := fun y => (measurable_pi_apply y).comp (h.meas j hj)
  have hm : Measurable fun x => yInner (z i x) (z j x) := by
    unfold yInner
    exact Measurable.const_mul (Finset.measurable_sum _ fun y _ =>
      (h1 y).mul (Complex.continuous_conj.measurable.comp (h2 y))) _
  exact (integrable_yy' h hC₀ hi hj).mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun x => norm_yInner_le _ _)

theorem integral_sq_sum_le' (h : DualFam F 𝒮 C₀ ℓ c a z Ov) (hC₀ : 0 ≤ C₀) :
    ∫ x, yNorm 2 (∑ i ∈ 𝒮, z i x) ^ 2 ≤ ∑ i ∈ 𝒮, ∑ j ∈ 𝒮,
      (if Ov i j then ∫ x, yNorm 2 (z i x) * yNorm 2 (z j x) else 0) := by
  have hint2 : Integrable (fun x => ∑ i ∈ 𝒮, ∑ j ∈ 𝒮, yInner (z i x) (z j x)) :=
    integrable_finsetSum _ fun i hi => integrable_finsetSum _ fun j hj => integrable_yInner' h hC₀ hi hj
  have key : ∀ x, yNorm 2 (∑ i ∈ 𝒮, z i x) ^ 2 = (∑ i ∈ 𝒮, ∑ j ∈ 𝒮, yInner (z i x) (z j x)).re := by
    intro x
    have h1 := yInner_self (∑ i ∈ 𝒮, z i x)
    rw [yInner_sum_left] at h1
    simp_rw [yInner_sum_right] at h1
    rw [h1, Complex.ofReal_re]
  have hre : ∫ x, (∑ i ∈ 𝒮, ∑ j ∈ 𝒮, yInner (z i x) (z j x)).re =
      (∫ x, ∑ i ∈ 𝒮, ∑ j ∈ 𝒮, yInner (z i x) (z j x)).re := by
    simpa using (Complex.reCLM.integral_comp_comm hint2)
  simp_rw [key]
  rw [hre, integral_finsetSum _ (fun i hi => integrable_finsetSum _ fun j hj => integrable_yInner' h hC₀ hi hj)]
  have e : ∀ i ∈ 𝒮, ∫ x, ∑ j ∈ 𝒮, yInner (z i x) (z j x) = ∑ j ∈ 𝒮, ∫ x, yInner (z i x) (z j x) :=
    fun i hi => integral_finsetSum _ fun j hj => integrable_yInner' h hC₀ hi hj
  rw [Finset.sum_congr rfl e]
  refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_))
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  by_cases hc : Ov i j
  · rw [ite_eq_left hc]; exact norm_inner_le' h hC₀ hi hj
  · rw [ite_eq_right hc, h.orth i hi j hj hc]; simp

theorem integrable_sq_sum' (h : DualFam F 𝒮 C₀ ℓ c a z Ov) (hC₀ : 0 ≤ C₀) :
    Integrable (fun x => yNorm 2 (∑ i ∈ 𝒮, z i x) ^ 2) := by
  have hint2 : Integrable (fun x => ∑ i ∈ 𝒮, ∑ j ∈ 𝒮, yInner (z i x) (z j x)) :=
    integrable_finsetSum _ fun i hi => integrable_finsetSum _ fun j hj => integrable_yInner' h hC₀ hi hj
  refine hint2.re.congr (Eventually.of_forall fun x => ?_)
  have h1 := yInner_self (∑ i ∈ 𝒮, z i x)
  rw [yInner_sum_left] at h1
  simp_rw [yInner_sum_right] at h1
  simp only [RCLike.re_to_complex]
  rw [h1, Complex.ofReal_re]

/-- **TT\***: `S² ≤ ‖∑ z_i‖² ‖F‖²`. -/
theorem tt_star' (h : DualFam F 𝒮 C₀ ℓ c a z Ov) (hC₀ : 0 ≤ C₀) (hF : Measurable F) {B : ℝ}
    (hFb : ∀ x, yNorm 2 (F x) ≤ B) (hFint : Integrable (fun x => yNorm 2 (F x) ^ 2)) :
    (∑ i ∈ 𝒮, a i ^ 2) ^ 2 ≤ (∫ x, yNorm 2 (∑ i ∈ 𝒮, z i x) ^ 2) * ∫ x, yNorm 2 (F x) ^ 2 := by
  have hS0 : 0 ≤ ∑ i ∈ 𝒮, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hFm : Measurable fun x => yNorm 2 (F x) := (measurable_yNorm_fun 2).comp hF
  have hZint := integrable_sq_sum' h hC₀
  have hZm : Measurable fun x => yNorm 2 (∑ i ∈ 𝒮, z i x) :=
    (measurable_yNorm_fun 2).comp (Finset.measurable_sum _ fun i hi => h.meas i hi)
  have hint : ∀ i ∈ 𝒮, Integrable (fun x => yInner (z i x) (F x)) := by
    intro i hi
    have h1 : ∀ y : ZMod P, Measurable fun x => z i x y := fun y => (measurable_pi_apply y).comp (h.meas i hi)
    have h2 : ∀ y : ZMod P, Measurable fun x => F x y := fun y => (measurable_pi_apply y).comp hF
    have hm : Measurable fun x => yInner (z i x) (F x) := by
      unfold yInner
      exact Measurable.const_mul (Finset.measurable_sum _ fun y _ =>
        (h1 y).mul (Complex.continuous_conj.measurable.comp (h2 y))) _
    have hb : Integrable (fun x => (C₀ * ℓ i ^ (-(1 : ℝ) / 2) * a i * B) * wt 6 (c i) (ℓ i) x) :=
      (integrable_wt (q := 6) (by norm_num) (c i) (h.pos i hi)).const_mul _
    refine hb.mono' hm.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    refine (norm_yInner_le _ _).trans ?_
    have := h.bound i hi x
    have hn : 0 ≤ yNorm 2 (F x) := by unfold yNorm; positivity
    calc yNorm 2 (z i x) * yNorm 2 (F x) ≤ (C₀ * ℓ i ^ (-(1 : ℝ) / 2) * a i * wt 6 (c i) (ℓ i) x) * B :=
          mul_le_mul this (hFb x) hn (mul_nonneg (mul_nonneg (mul_nonneg hC₀
            (Real.rpow_nonneg (h.pos i hi).le _)) (h.nonneg i hi)) (wt_pos _ _ _ _ (h.pos i hi)).le)
      _ = _ := by ring
  have hSc : (((∑ i ∈ 𝒮, a i ^ 2 : ℝ)) : ℂ) = ∫ x, yInner (∑ i ∈ 𝒮, z i x) (F x) := by
    rw [Complex.ofReal_sum]
    rw [Finset.sum_congr rfl (fun i hi => (h.inner_F i hi).symm)]
    rw [← integral_finsetSum _ hint]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [yInner_sum_left]
  have hint' : Integrable (fun x => yInner (∑ i ∈ 𝒮, z i x) (F x)) := by
    have := integrable_finsetSum 𝒮 hint
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [yInner_sum_left]
  have hfg : Integrable (fun x => yNorm 2 (∑ i ∈ 𝒮, z i x) * yNorm 2 (F x)) := by
    refine ((hZint.add hFint).const_mul 1).mono' (hZm.mul hFm).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have h0 : 0 ≤ yNorm 2 (∑ i ∈ 𝒮, z i x) * yNorm 2 (F x) := by unfold yNorm; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    simp only [Pi.add_apply, one_mul]
    nlinarith [sq_nonneg (yNorm 2 (∑ i ∈ 𝒮, z i x) - yNorm 2 (F x))]
  have hSle : ∑ i ∈ 𝒮, a i ^ 2 ≤ ∫ x, yNorm 2 (∑ i ∈ 𝒮, z i x) * yNorm 2 (F x) := by
    have h1 : ∑ i ∈ 𝒮, a i ^ 2 = ‖(((∑ i ∈ 𝒮, a i ^ 2 : ℝ)) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0]
    rw [h1, hSc]
    refine (norm_integral_le_integral_norm _).trans ?_
    exact integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) hfg
      (Eventually.of_forall fun x => norm_yInner_le _ _)
  refine sq_le_of_forall hS0 (integral_nonneg fun x => by positivity)
    (integral_nonneg fun x => by positivity) fun l hl => ?_
  have h2 : 2 * l * ∫ x, yNorm 2 (∑ i ∈ 𝒮, z i x) * yNorm 2 (F x) ≤
      ∫ x, (l ^ 2 * yNorm 2 (∑ i ∈ 𝒮, z i x) ^ 2 + yNorm 2 (F x) ^ 2) := by
    rw [← integral_const_mul]
    exact integral_mono (hfg.const_mul _) ((hZint.const_mul _).add hFint) fun x => by
      simp only
      nlinarith [sq_nonneg (l * yNorm 2 (∑ i ∈ 𝒮, z i x) - yNorm 2 (F x))]
  rw [integral_add (hZint.const_mul _) hFint, integral_const_mul] at h2
  have h3 : 2 * l * ∑ i ∈ 𝒮, a i ^ 2 ≤ 2 * l * ∫ x, yNorm 2 (∑ i ∈ 𝒮, z i x) * yNorm 2 (F x) :=
    mul_le_mul_of_nonneg_left hSle (by positivity)
  linarith

/-- The per-index bound: the overlapping smaller-or-equal indices have disjoint time intervals, hence
`∑_{j ∈ N(i)} ĉ_j J(i,j) ≤ 8 K μ ℓ_i`. -/
theorem sum_Jw_le (h : DualFam F 𝒮 C₀ ℓ c a z Ov)
    (hsep : ∀ i ∈ 𝒮, ∀ j ∈ 𝒮, ∀ j' ∈ 𝒮, j ≠ j' → Ov i j → Ov i j' → ℓ j ≤ ℓ i → ℓ j' ≤ ℓ i →
      Disjoint (Ico (c j - ℓ j / 2) (c j + ℓ j / 2)) (Ico (c j' - ℓ j' / 2) (c j' + ℓ j' / 2)))
    {i : ι} (hi : i ∈ 𝒮) :
    ∑ j ∈ 𝒮.filter (fun j => Ov i j ∧ ℓ j ≤ ℓ i), Jw ℓ c i j ≤ 8 * ℓ i := by
  set N := 𝒮.filter (fun j => Ov i j ∧ ℓ j ≤ ℓ i) with hN
  have hℓi := h.pos i hi
  have hmem : ∀ j ∈ N, j ∈ 𝒮 ∧ Ov i j ∧ ℓ j ≤ ℓ i := fun j hj => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hj
    exact ⟨h1, h2⟩
  have h1 : ∀ j ∈ N, Jw ℓ c i j ≤ 8 * ∫ y in Ico (c j - ℓ j / 2) (c j + ℓ j / 2), wt 3 (c i) (ℓ i) y := by
    intro j hj
    obtain ⟨hj𝒮, -, hle⟩ := hmem j hj
    have := J_le_setIntegral (c := c i) (ℓ := ℓ i) (a := c j - ℓ j / 2) (ℓ' := ℓ j) (h.pos j hj𝒮) hle
    have e1 : c j - ℓ j / 2 + ℓ j / 2 = c j := by ring
    have e2 : c j - ℓ j / 2 + ℓ j = c j + ℓ j / 2 := by ring
    rw [e1, e2] at this
    exact this
  have hdisj : Set.Pairwise (↑N : Set ι) (Function.onFun Disjoint fun j => Ico (c j - ℓ j / 2) (c j + ℓ j / 2)) := by
    intro j hj j' hj' hne
    obtain ⟨hj𝒮, hOj, hlej⟩ := hmem j hj
    obtain ⟨hj'𝒮, hOj', hlej'⟩ := hmem j' hj'
    exact hsep i hi j hj𝒮 j' hj'𝒮 hne hOj hOj' hlej hlej'
  have hint : ∀ j ∈ N, IntegrableOn (wt 3 (c i) (ℓ i)) (Ico (c j - ℓ j / 2) (c j + ℓ j / 2)) := fun j _ =>
    (integrable_wt (q := 3) (by norm_num) (c i) hℓi).integrableOn
  have hU := integral_biUnion_finset N (f := wt 3 (c i) (ℓ i)) (μ := volume)
    (s := fun j => Ico (c j - ℓ j / 2) (c j + ℓ j / 2)) (fun j _ => measurableSet_Ico) hdisj hint
  have hle1 : ∫ y in ⋃ j ∈ N, Ico (c j - ℓ j / 2) (c j + ℓ j / 2), wt 3 (c i) (ℓ i) y ≤
      ∫ y, wt 3 (c i) (ℓ i) y :=
    setIntegral_le_integral (integrable_wt (q := 3) (by norm_num) (c i) hℓi)
      (Eventually.of_forall fun y => (wt_pos _ _ _ _ hℓi).le)
  have hI : ∫ y, wt 3 (c i) (ℓ i) y = ℓ i := by
    rw [integral_wt (q := 3) (by norm_num) (c i) hℓi]; ring
  calc ∑ j ∈ N, Jw ℓ c i j ≤ ∑ j ∈ N, 8 * ∫ y in Ico (c j - ℓ j / 2) (c j + ℓ j / 2), wt 3 (c i) (ℓ i) y :=
        Finset.sum_le_sum h1
    _ = 8 * ∑ j ∈ N, ∫ y in Ico (c j - ℓ j / 2) (c j + ℓ j / 2), wt 3 (c i) (ℓ i) y := by
        rw [← Finset.mul_sum]
    _ = 8 * ∫ y in ⋃ j ∈ N, Ico (c j - ℓ j / 2) (c j + ℓ j / 2), wt 3 (c i) (ℓ i) y := by rw [hU]
    _ ≤ 8 * ℓ i := by have := hle1; rw [hI] at this; linarith

/-- **The Bessel inequality for separated dual families** (the TT* argument of MTT2 L2860-2950): `∑ a_i² ≤ 64 C₀² K ‖F‖²`. -/
theorem bessel_of_sep (h : DualFam F 𝒮 C₀ ℓ c a z Ov) (hC₀ : 0 ≤ C₀) (hF : Measurable F) {B : ℝ}
    (hFb : ∀ x, yNorm 2 (F x) ≤ B) (hFint : Integrable (fun x => yNorm 2 (F x) ^ 2))
    (hsym : ∀ i ∈ 𝒮, ∀ j ∈ 𝒮, Ov i j → Ov j i)
    (hsep : ∀ i ∈ 𝒮, ∀ j ∈ 𝒮, ∀ j' ∈ 𝒮, j ≠ j' → Ov i j → Ov i j' → ℓ j ≤ ℓ i → ℓ j' ≤ ℓ i →
      Disjoint (Ico (c j - ℓ j / 2) (c j + ℓ j / 2)) (Ico (c j' - ℓ j' / 2) (c j' + ℓ j' / 2)))
    {μ K : ℝ} (hK : 0 ≤ K) (hμ : ∀ i ∈ 𝒮, chatF ℓ a i ≤ K * μ ∧ μ ≤ 4 * chatF ℓ a i) :
    ∑ i ∈ 𝒮, a i ^ 2 ≤ 64 * C₀ ^ 2 * K * ∫ x, yNorm 2 (F x) ^ 2 := by
  set S := ∑ i ∈ 𝒮, a i ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  set T := ∫ x, yNorm 2 (∑ i ∈ 𝒮, z i x) ^ 2 with hT
  have hF0 : 0 ≤ ∫ x, yNorm 2 (F x) ^ 2 := integral_nonneg fun x => by positivity
  have hTT := tt_star' h hC₀ hF hFb hFint
  set M : ι → ι → ℝ := fun i j => C₀ ^ 2 * (chatF ℓ a i * chatF ℓ a j) * Jw ℓ c i j with hM
  have hMnn : ∀ i ∈ 𝒮, ∀ j ∈ 𝒮, 0 ≤ M i j := fun i hi j hj =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (chatF_nonneg h hi) (chatF_nonneg h hj)))
      (Jw_nonneg h hi hj)
  have hMsymm : ∀ i j, M i j = M j i := fun i j => by
    simp only [hM, Jw_comm ℓ c i j]; ring
  -- Step 1: `T ≤ Σ Σ [Ov] M`
  have hstep1 : T ≤ ∑ i ∈ 𝒮, ∑ j ∈ 𝒮, (if Ov i j then M i j else 0) := by
    refine (integral_sq_sum_le' h hC₀).trans ?_
    refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
    by_cases hc : Ov i j
    · simp only [ite_eq_left hc]; exact integral_yy_le' h hC₀ hi hj
    · simp [hc]
  -- Step 2: symmetrization
  set N : ι → Finset ι := fun i => 𝒮.filter (fun j => Ov i j ∧ ℓ j ≤ ℓ i) with hN
  have hstep2 : ∑ i ∈ 𝒮, ∑ j ∈ 𝒮, (if Ov i j then M i j else 0) ≤
      2 * ∑ i ∈ 𝒮, ∑ j ∈ N i, M i j := by
    set E1 : ι → ι → ℝ := fun i j => if Ov i j ∧ ℓ j ≤ ℓ i then M i j else 0 with hE1
    have hsum1 : ∀ i, ∑ j ∈ N i, M i j = ∑ j ∈ 𝒮, E1 i j := fun i => by
      simp only [hN, hE1, Finset.sum_filter]
    have hE1nn : ∀ i ∈ 𝒮, ∀ j ∈ 𝒮, 0 ≤ E1 i j := by
      intro i hi j hj
      simp only [hE1]
      split_ifs
      · exact hMnn i hi j hj
      · exact le_rfl
    have hle : ∀ i ∈ 𝒮, ∀ j ∈ 𝒮, (if Ov i j then M i j else 0) ≤ E1 i j + E1 j i := by
      intro i hi j hj
      by_cases hc : Ov i j
      · have hc' := hsym i hi j hj hc
        rcases le_total (ℓ j) (ℓ i) with hl | hl
        · have e1 : E1 i j = M i j := by simp only [hE1]; rw [ite_eq_left ⟨hc, hl⟩]
          have := hE1nn j hj i hi
          rw [ite_eq_left hc, e1]
          linarith
        · have e1 : E1 j i = M j i := by simp only [hE1]; rw [ite_eq_left ⟨hc', hl⟩]
          have := hE1nn i hi j hj
          rw [ite_eq_left hc, e1, hMsymm j i]
          linarith
      · rw [ite_eq_right hc]
        have := hE1nn i hi j hj
        have := hE1nn j hj i hi
        linarith
    calc ∑ i ∈ 𝒮, ∑ j ∈ 𝒮, (if Ov i j then M i j else 0) ≤ ∑ i ∈ 𝒮, ∑ j ∈ 𝒮, (E1 i j + E1 j i) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hle i hi j hj
      _ = ∑ i ∈ 𝒮, ∑ j ∈ 𝒮, E1 i j + ∑ i ∈ 𝒮, ∑ j ∈ 𝒮, E1 j i := by
          simp only [Finset.sum_add_distrib]
      _ = 2 * ∑ i ∈ 𝒮, ∑ j ∈ 𝒮, E1 i j := by
          rw [Finset.sum_comm (f := fun i j => E1 j i)]; ring
      _ = 2 * ∑ i ∈ 𝒮, ∑ j ∈ N i, M i j := by
          simp only [hsum1]
  -- Step 3: the per-index bound
  have hstep3 : ∀ i ∈ 𝒮, ∑ j ∈ N i, M i j ≤ C₀ ^ 2 * chatF ℓ a i * (K * μ) * (8 * ℓ i) := by
    intro i hi
    have hsJ := sum_Jw_le h hsep hi
    have hci := chatF_nonneg h hi
    calc ∑ j ∈ N i, M i j = ∑ j ∈ N i, (C₀ ^ 2 * chatF ℓ a i) * (chatF ℓ a j * Jw ℓ c i j) := by
          refine Finset.sum_congr rfl fun j _ => ?_; simp only [hM]; ring
      _ = (C₀ ^ 2 * chatF ℓ a i) * ∑ j ∈ N i, chatF ℓ a j * Jw ℓ c i j := by rw [Finset.mul_sum]
      _ ≤ (C₀ ^ 2 * chatF ℓ a i) * ((K * μ) * ∑ j ∈ N i, Jw ℓ c i j) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (sq_nonneg _) hci)
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun j hj => ?_
          have hj𝒮 := (Finset.mem_filter.1 hj).1
          exact mul_le_mul_of_nonneg_right (hμ j hj𝒮).1 (Jw_nonneg h hi hj𝒮)
      _ ≤ (C₀ ^ 2 * chatF ℓ a i) * ((K * μ) * (8 * ℓ i)) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (sq_nonneg _) hci)
          refine mul_le_mul_of_nonneg_left hsJ ?_
          rcases 𝒮.eq_empty_or_nonempty with he | ⟨i₀, hi₀⟩
          · simp [he] at hi
          exact (chatF_nonneg h hi₀).trans (hμ i₀ hi₀).1
      _ = _ := by ring
  -- Step 4
  have hstep4 : ∀ i ∈ 𝒮, C₀ ^ 2 * chatF ℓ a i * (K * μ) * (8 * ℓ i) ≤ 32 * C₀ ^ 2 * K * a i ^ 2 := by
    intro i hi
    have hci := chatF_nonneg h hi
    have hℓ := h.pos i hi
    have hμi := (hμ i hi).2
    have hsq := ell_mul_chatF_sq hℓ a
    have h1 : μ * (chatF ℓ a i * ℓ i) ≤ 4 * (chatF ℓ a i ^ 2 * ℓ i) := by
      have : 0 ≤ chatF ℓ a i * ℓ i := mul_nonneg hci hℓ.le
      nlinarith
    have hKC : 0 ≤ C₀ ^ 2 * K := mul_nonneg (sq_nonneg _) hK
    calc C₀ ^ 2 * chatF ℓ a i * (K * μ) * (8 * ℓ i) = 8 * (C₀ ^ 2 * K) * (μ * (chatF ℓ a i * ℓ i)) := by ring
      _ ≤ 8 * (C₀ ^ 2 * K) * (4 * (chatF ℓ a i ^ 2 * ℓ i)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 32 * C₀ ^ 2 * K * (ℓ i * chatF ℓ a i ^ 2) := by ring
      _ = 32 * C₀ ^ 2 * K * a i ^ 2 := by rw [hsq]
  have hT_le : T ≤ 64 * C₀ ^ 2 * K * S := by
    calc T ≤ 2 * ∑ i ∈ 𝒮, ∑ j ∈ N i, M i j := hstep1.trans hstep2
      _ ≤ 2 * ∑ i ∈ 𝒮, 32 * C₀ ^ 2 * K * a i ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => (hstep3 i hi).trans (hstep4 i hi))
            (by norm_num)
      _ = 64 * C₀ ^ 2 * K * S := by rw [← Finset.mul_sum, hS]; ring
  -- Step 5
  have hT0 : 0 ≤ T := integral_nonneg fun x => by positivity
  by_cases hS00 : S = 0
  · rw [hS00]; positivity
  · have hSpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hS00)
    have h1 : S ^ 2 ≤ (64 * C₀ ^ 2 * K * S) * ∫ x, yNorm 2 (F x) ^ 2 :=
      hTT.trans (mul_le_mul_of_nonneg_right hT_le hF0)
    have h2 : S * S ≤ S * (64 * C₀ ^ 2 * K * ∫ x, yNorm 2 (F x) ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left h2 hSpos

/-- A single index satisfies the `L²` bound `a² ≤ 64 C₀² ‖F‖₂²`. -/
theorem single_L2 (h : DualFam F 𝒮 C₀ ℓ c a z Ov) (hC₀ : 0 ≤ C₀) (hF : Measurable F) {B : ℝ}
    (hFb : ∀ x, yNorm 2 (F x) ≤ B) (hFint : Integrable (fun x => yNorm 2 (F x) ^ 2)) {i : ι} (hi : i ∈ 𝒮) :
    a i ^ 2 ≤ 64 * C₀ ^ 2 * ∫ x, yNorm 2 (F x) ^ 2 := by
  have h1 : DualFam F {i} C₀ ℓ c a z Ov :=
    ⟨fun j hj => h.pos j (by rw [Finset.mem_singleton.1 hj]; exact hi),
      fun j hj => h.nonneg j (by rw [Finset.mem_singleton.1 hj]; exact hi),
      fun j hj => h.meas j (by rw [Finset.mem_singleton.1 hj]; exact hi),
      fun j hj => h.inner_F j (by rw [Finset.mem_singleton.1 hj]; exact hi),
      fun j hj => h.bound j (by rw [Finset.mem_singleton.1 hj]; exact hi),
      fun j hj k hk hn => h.orth j (by rw [Finset.mem_singleton.1 hj]; exact hi) k
        (by rw [Finset.mem_singleton.1 hk]; exact hi) hn⟩
  have := bessel_of_sep h1 hC₀ hF hFb hFint
    (fun x hx y hy hxy => by
      rw [Finset.mem_singleton.1 hx] at hxy
      rw [Finset.mem_singleton.1 hy] at hxy ⊢
      rw [Finset.mem_singleton.1 hx]
      exact hxy)
    (fun _ _ j hj j' hj' hne => absurd ((Finset.mem_singleton.1 hj).trans (Finset.mem_singleton.1 hj').symm) hne)
    (μ := chatF ℓ a i) (K := 1) zero_le_one
    (fun j hj => by
      rw [Finset.mem_singleton.1 hj]
      have := chatF_nonneg h hi
      constructor <;> linarith)
  simpa using this

/-- The `L^∞`-type bound for a single index: `ĉ ≤ (2/5) C₀ B`. -/
theorem chat_le_of_bdd (h : DualFam F 𝒮 C₀ ℓ c a z Ov) (hC₀ : 0 ≤ C₀) (hF : Measurable F) {B : ℝ}
    (hFb : ∀ x, yNorm 2 (F x) ≤ B) {i : ι} (hi : i ∈ 𝒮) : chatF ℓ a i ≤ 2 / 5 * C₀ * B := by
  have hℓ := h.pos i hi
  have hci := chatF_nonneg h hi
  have hB0 : 0 ≤ B := (by unfold yNorm; positivity : 0 ≤ yNorm 2 (F 0)).trans (hFb 0)
  have hm : Measurable fun x => yInner (z i x) (F x) := by
    have h1 : ∀ y : ZMod P, Measurable fun x => z i x y := fun y => (measurable_pi_apply y).comp (h.meas i hi)
    have h2 : ∀ y : ZMod P, Measurable fun x => F x y := fun y => (measurable_pi_apply y).comp hF
    unfold yInner
    exact Measurable.const_mul (Finset.measurable_sum _ fun y _ =>
      (h1 y).mul (Complex.continuous_conj.measurable.comp (h2 y))) _
  have hb : Integrable (fun x => (C₀ * chatF ℓ a i * B) * wt 6 (c i) (ℓ i) x) :=
    (integrable_wt (q := 6) (by norm_num) (c i) hℓ).const_mul _
  have hpt : ∀ x, ‖yInner (z i x) (F x)‖ ≤ (C₀ * chatF ℓ a i * B) * wt 6 (c i) (ℓ i) x := by
    intro x
    refine (norm_yInner_le _ _).trans ?_
    have := h.bound i hi x
    have hn : 0 ≤ yNorm 2 (F x) := by unfold yNorm; positivity
    calc yNorm 2 (z i x) * yNorm 2 (F x) ≤ (C₀ * ℓ i ^ (-(1 : ℝ) / 2) * a i * wt 6 (c i) (ℓ i) x) * B :=
          mul_le_mul this (hFb x) hn (mul_nonneg (mul_nonneg (mul_nonneg hC₀
            (Real.rpow_nonneg hℓ.le _)) (h.nonneg i hi)) (wt_pos _ _ _ _ hℓ).le)
      _ = _ := by unfold chatF; ring
  have hint : Integrable (fun x => yInner (z i x) (F x)) := hb.mono' hm.aestronglyMeasurable
    (Eventually.of_forall hpt)
  have h1 : a i ^ 2 ≤ (C₀ * chatF ℓ a i * B) * (2 * ℓ i / 5) := by
    have hnorm : ‖(((a i ^ 2 : ℝ)) : ℂ)‖ = a i ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [← hnorm, ← h.inner_F i hi]
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ x, ‖yInner (z i x) (F x)‖ ≤ ∫ x, (C₀ * chatF ℓ a i * B) * wt 6 (c i) (ℓ i) x :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) hb (Eventually.of_forall hpt)
      _ = (C₀ * chatF ℓ a i * B) * (2 * ℓ i / 5) := by
          rw [integral_const_mul, integral_wt (q := 6) (by norm_num) (c i) hℓ]; norm_num
  have h2 := ell_mul_chatF_sq hℓ a (i := i)
  rcases hci.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have h3 : ℓ i * chatF ℓ a i ^ 2 ≤ (C₀ * B * (2 * ℓ i / 5)) * chatF ℓ a i := by nlinarith
    have h4 : ℓ i * chatF ℓ a i * chatF ℓ a i ≤ (C₀ * B * (2 / 5) * ℓ i) * chatF ℓ a i := by nlinarith
    have h5 : ℓ i * chatF ℓ a i ≤ C₀ * B * (2 / 5) * ℓ i :=
      le_of_mul_le_mul_right h4 hpos
    have h6 : chatF ℓ a i * ℓ i ≤ (2 / 5 * C₀ * B) * ℓ i := by nlinarith
    exact le_of_mul_le_mul_right h6 hℓ

end Bessel

end PrimeBHT.TimeFrequency.X2
