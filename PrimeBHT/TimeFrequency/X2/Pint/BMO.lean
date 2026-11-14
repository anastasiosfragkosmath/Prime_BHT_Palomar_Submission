module

public import PrimeBHT.TimeFrequency.X2.Pint.TheoremIIAux
public import PrimeBHT.TimeFrequency.X2.CZ.Addendum
public import PrimeBHT.TimeFrequency.X2.CZ.CZHormander

/-!
# X2, V11-a: the `L^∞ → BMO` endpoint of a Calderón-Zygmund kernel operator (vector valued)

`bmo_of_cz`: for a CZ kernel `K` (`CZ.IsCZKernel A K`, jointly strongly measurable, with a qualitative row bound) whose
operator is bounded on `L^p(L^p(Y))` with constant `Cs`, every measurable `G` with `‖G(w)‖_{L^p(Y)} ≤ 1` satisfies
`∫_{[a,b)} ‖K G - avg_{[a,b)} K G‖_{L^p(Y)} ≤ 2 (2 Cs + A) (b - a)`.

Proof: split `G = G 1_{|w - c| ≤ ℓ} + G 1_{|w - c| > ℓ}` (`c` the centre, `ℓ = b - a`); local part by Hölder and the
strong type, far part pointwise by the Hörmander smoothness in the first variable against `K G_far (c)`; then Jensen for
the average.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Pint

variable {P : ℕ} [NeZero P]

theorem integrable_mul_bdd {k : ℝ → ℂ} (hk : Integrable k) {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {C : ℝ}
    (hgb : ∀ w, ‖g w‖ ≤ C) : Integrable fun w => k w * g w :=
  Integrable.mono' (hk.norm.mul_const C) (hk.aestronglyMeasurable.mul hg) (ae_of_all _ fun w => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hgb w) (norm_nonneg _))

/-- Minkowski for a kernel operator: `‖∫ k(w) G(w) dw‖_p ≤ ∫ |k| ‖G‖_p`. -/
theorem ofReal_yNorm_integral_le {p : ℝ} (hp : 1 < p) {k : ℝ → ℂ} (hk : Integrable k) {G : ℝ → ZMod P → ℂ}
    (hG : Measurable G) {Bg : ℝ} (hGb : ∀ w, yNorm p (G w) ≤ Bg) :
    ENNReal.ofReal (yNorm p (fun y => ∫ w, k w * G w y)) ≤ ∫⁻ w, ‖k w‖ₑ * ENNReal.ofReal (yNorm p (G w)) := by
  have hp0 : 0 < p := by linarith
  have hBg : 0 ≤ Bg := (yNorm_nonneg _ _).trans (hGb 0)
  have hGi : ∀ y, Integrable fun w => k w * G w y := fun y =>
    integrable_mul_bdd hk ((measurable_pi_apply y).comp hG).aestronglyMeasurable (C := (P : ℝ) ^ p⁻¹ * Bg)
      fun w => (norm_apply_le_yNorm hp0 _ y).trans (mul_le_mul_of_nonneg_left (hGb w) (by positivity))
  have hn : ∀ w, yNorm p (fun y => k w * G w y) = ‖k w‖ * yNorm p (G w) := fun w => yNorm_fun_const_mul hp0 _ _
  have hni : Integrable fun w => ‖k w‖ * yNorm p (G w) :=
    Integrable.mono' (hk.norm.mul_const Bg)
      (hk.norm.aestronglyMeasurable.mul ((measurable_yNorm_fun p).comp hG).aestronglyMeasurable)
      (ae_of_all _ fun w => by
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (yNorm_nonneg _ _))]
        exact mul_le_mul_of_nonneg_left (hGb w) (norm_nonneg _))
  have h := CZ.yNorm_integral_le hp (fun w y => k w * G w y) hGi (by simp_rw [hn]; exact hni)
  simp_rw [hn] at h
  refine (ENNReal.ofReal_le_ofReal h).trans (le_of_eq ?_)
  rw [ofReal_integral_eq_lintegral_ofReal hni (ae_of_all _ fun w => mul_nonneg (norm_nonneg _) (yNorm_nonneg _ _))]
  refine lintegral_congr fun w => ?_
  rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]

/-- **BMO endpoint of a CZ kernel operator.** -/
theorem bmo_of_cz {p : ℝ} (hp : 1 < p) {A Cs Cloc : ℝ} {K : ℝ → ℝ → ℂ} (hCZ : CZ.IsCZKernel A K)
    (hKm : StronglyMeasurable (Function.uncurry K)) (hKr : ∀ x, ∫⁻ w, ‖K x w‖ₑ ≤ ENNReal.ofReal Cloc)
    (hCs : 0 ≤ Cs)
    (hstr : ∀ G : ℝ → ZMod P → ℂ, Measurable G → (∃ B, ∀ x, yNorm p (G x) ≤ B) →
      eLpNorm (fun x => yNorm p (kernelOp K G x)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal Cs * eLpNorm (fun x => yNorm p (G x)) (ENNReal.ofReal p) volume)
    {G : ℝ → ZMod P → ℂ} (hG : Measurable G) (hG1 : ∀ w, yNorm p (G w) ≤ 1) {a b : ℝ} (hab : a < b) :
    ∫⁻ x in Ico a b, ENNReal.ofReal (yNorm p (kernelOp K G x - avgOn a b (kernelOp K G))) ≤
      ENNReal.ofReal (2 * (2 * Cs + A) * (b - a)) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := hp.le
  have hA : 0 ≤ A := hCZ.nonneg
  set ℓ := b - a with hℓ
  have hℓ0 : 0 < ℓ := sub_pos.2 hab
  set c := (a + b) / 2 with hc
  set J : Set ℝ := {w | ℓ < |w - c|} with hJ
  have hJm : MeasurableSet J := measurableSet_lt measurable_const (continuous_abs.measurable.comp (measurable_id.sub_const _))
  set G1 : ℝ → ZMod P → ℂ := Jᶜ.indicator G with hG1def
  set G2 : ℝ → ZMod P → ℂ := J.indicator G with hG2def
  have hG1m : Measurable G1 := hG.indicator hJm.compl
  have hG2m : Measurable G2 := hG.indicator hJm
  have hyG1 : ∀ w, yNorm p (G1 w) ≤ 1 := fun w => by
    by_cases hw : w ∈ Jᶜ
    · rw [hG1def, indicator_of_mem hw]; exact hG1 w
    · rw [hG1def, indicator_of_notMem hw, yNorm_zero_of_pos hp0]; norm_num
  have hyG2 : ∀ w, yNorm p (G2 w) ≤ 1 := fun w => by
    by_cases hw : w ∈ J
    · rw [hG2def, indicator_of_mem hw]; exact hG1 w
    · rw [hG2def, indicator_of_notMem hw, yNorm_zero_of_pos hp0]; norm_num
  have hKx : ∀ x, Integrable (K x) := fun x => integrable_kernel_row hKm hKr x
  have hbd : ∀ (H : ℝ → ZMod P → ℂ), Measurable H → (∀ w, yNorm p (H w) ≤ 1) → ∀ x y,
      Integrable fun w => K x w * H w y := fun H hH hH1 x y =>
    integrable_mul_bdd (hKx x) ((measurable_pi_apply y).comp hH).aestronglyMeasurable (C := (P : ℝ) ^ p⁻¹)
      fun w => (norm_apply_le_yNorm hp0 _ y).trans
        (mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hH1 w))
  have hlin : ∀ x, kernelOp K G x = kernelOp K G1 x + kernelOp K G2 x := by
    intro x; funext y
    simp only [kernelOp, Pi.add_apply]
    rw [← integral_add (hbd G1 hG1m hyG1 x y) (hbd G2 hG2m hyG2 x y)]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only [hG1def, hG2def]
    by_cases hw : w ∈ J
    · simp [hw]
    · simp [hw]
  set c' := kernelOp K G2 c with hc'
  -- the far part
  have hfar : ∀ x ∈ Ico a b, yNorm p (kernelOp K G2 x - c') ≤ A := by
    intro x hx
    have hxc : |x - c| ≤ ℓ / 2 := by
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    have e : kernelOp K G2 x - c' = fun y => ∫ w, (K x w - K c w) * G2 w y := by
      funext y
      simp only [hc', kernelOp, Pi.sub_apply]
      rw [← integral_sub (hbd G2 hG2m hyG2 x y) (hbd G2 hG2m hyG2 c y)]
      exact integral_congr_ae (ae_of_all _ fun w => by ring)
    have h1 := ofReal_yNorm_integral_le hp (k := fun w => K x w - K c w) ((hKx x).sub (hKx c)) hG2m hyG2
    rw [← e] at h1
    have h2 : ∫⁻ w, ‖K x w - K c w‖ₑ * ENNReal.ofReal (yNorm p (G2 w)) ≤
        ∫⁻ w in J, ENNReal.ofReal (A * (ℓ / 2)) * ENNReal.ofReal (1 / (w - c) ^ 2) := by
      rw [← lintegral_indicator hJm]
      refine lintegral_mono fun w => ?_
      by_cases hw : w ∈ J
      · rw [indicator_of_mem hw, hG2def, indicator_of_mem hw]
        have hwc : ℓ < |w - c| := hw
        have hsm := (hCZ.2 c x w (by rw [abs_sub_comm c x, abs_sub_comm c w]; linarith)).trans' (le_add_of_nonneg_right
          (norm_nonneg (K w c - K w x)))
        have hk : ‖K x w - K c w‖ ≤ A * (ℓ / 2) * (1 / (w - c) ^ 2) := by
          rw [norm_sub_rev] at hsm
          refine hsm.trans ?_
          rw [abs_sub_comm c x, abs_sub_comm c w, sq_abs, mul_one_div]
          have hpos : 0 < (w - c) ^ 2 := by
            have : 0 < |w - c| := by linarith
            have : w - c ≠ 0 := fun h => by rw [h, abs_zero] at this; exact lt_irrefl 0 this
            positivity
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxc hA) hpos.le
        calc ‖K x w - K c w‖ₑ * ENNReal.ofReal (yNorm p (G w)) ≤ ‖K x w - K c w‖ₑ * 1 := by
              gcongr; exact ENNReal.ofReal_le_one.2 (hG1 w)
          _ ≤ _ := by
              rw [mul_one, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
              exact ENNReal.ofReal_le_ofReal hk
      · rw [indicator_of_notMem hw, hG2def, indicator_of_notMem hw, yNorm_zero_of_pos hp0,
          ENNReal.ofReal_zero, mul_zero]
    rw [lintegral_const_mul _ (by fun_prop), CZ.lintegral_tail_inv_sq_shift hℓ0 c,
      ← ENNReal.ofReal_mul (by positivity)] at h2
    have h3 := h1.trans h2
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
    calc yNorm p (kernelOp K G2 x - c') ≤ A * (ℓ / 2) * (2 / ℓ) := h3
      _ = A := by field_simp
  -- the local part
  have hloc : ∫⁻ x in Ico a b, ENNReal.ofReal (yNorm p (kernelOp K G1 x)) ≤ ENNReal.ofReal (2 * Cs * ℓ) := by
    have hq := Real.HolderConjugate.conjExponent hp
    set q := Real.conjExponent p
    have hTm : Measurable fun x => ENNReal.ofReal (yNorm p (kernelOp K G1 x)) :=
      ((measurable_yNorm_fun p).comp (measurable_kernelOp hKm hG1m)).ennreal_ofReal
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ico a b)) hq hTm.aemeasurable
      (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, Real.volume_Ico, one_mul] at hH
    have hst := hstr G1 hG1m ⟨1, hyG1⟩
    have hpe : ENNReal.ofReal p ≠ 0 := by simpa using hp0
    have hm1 : AEStronglyMeasurable (fun x => yNorm p (kernelOp K G1 x)) volume :=
      ((measurable_yNorm_fun p).comp (measurable_kernelOp hKm hG1m)).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (fun x => yNorm p (G1 x)) volume :=
      ((measurable_yNorm_fun p).comp hG1m).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpe ENNReal.ofReal_ne_top hm1,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hpe ENNReal.ofReal_ne_top hm2, ENNReal.toReal_ofReal hp0.le] at hst
    simp only [Real.enorm_eq_ofReal (yNorm_nonneg _ _)] at hst
    have hG1v : ∫⁻ x, ENNReal.ofReal (yNorm p (G1 x)) ^ p ≤ ENNReal.ofReal (2 * ℓ) := by
      calc ∫⁻ x, ENNReal.ofReal (yNorm p (G1 x)) ^ p ≤ ∫⁻ x, Jᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x := by
            refine lintegral_mono fun x => ?_
            by_cases hx : x ∈ Jᶜ
            · rw [indicator_of_mem hx]
              exact ENNReal.rpow_le_one (ENNReal.ofReal_le_one.2 (hyG1 x)) hp0.le
            · rw [indicator_of_notMem hx, hG1def, indicator_of_notMem hx, yNorm_zero_of_pos hp0,
                ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hp0]
        _ = volume Jᶜ := lintegral_indicator_one hJm.compl
        _ ≤ volume (Icc (c - ℓ) (c + ℓ)) := measure_mono fun x hx => by
            have : |x - c| ≤ ℓ := not_lt.1 hx
            rw [abs_le] at this; exact ⟨by linarith, by linarith⟩
        _ = ENNReal.ofReal (2 * ℓ) := by rw [Real.volume_Icc]; congr 1; ring
    have hI : (∫⁻ x in Ico a b, ENNReal.ofReal (yNorm p (kernelOp K G1 x)) ^ p) ^ (1 / p) ≤
        ENNReal.ofReal Cs * ENNReal.ofReal (2 * ℓ) ^ (1 / p) :=
      (ENNReal.rpow_le_rpow (setLIntegral_le_lintegral _ _) (by positivity)).trans
        (hst.trans (mul_le_mul_right (ENNReal.rpow_le_rpow hG1v (by positivity)) _))
    refine hH.trans ?_
    calc (∫⁻ x in Ico a b, ENNReal.ofReal (yNorm p (kernelOp K G1 x)) ^ p) ^ (1 / p) *
          ENNReal.ofReal (b - a) ^ (1 / q)
        ≤ ENNReal.ofReal Cs * ENNReal.ofReal (2 * ℓ) ^ (1 / p) * ENNReal.ofReal ℓ ^ (1 / q) := by gcongr
      _ = ENNReal.ofReal (Cs * (2 * ℓ) ^ (1 / p) * ℓ ^ (1 / q)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
            ENNReal.ofReal_rpow_of_nonneg hℓ0.le (by have := hq.symm.pos; positivity),
            ← ENNReal.ofReal_mul hCs, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (2 * Cs * ℓ) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hpq : 1 / p + 1 / q = 1 := by rw [one_div, one_div]; exact hq.inv_add_inv_eq_one
          rw [Real.mul_rpow (by norm_num) hℓ0.le, mul_assoc, mul_assoc, ← Real.rpow_add hℓ0, hpq,
            Real.rpow_one]
          have h2 : (2 : ℝ) ^ (1 / p) ≤ 2 := by
            calc (2 : ℝ) ^ (1 / p) ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [div_le_one hp0]; exact hp1)
              _ = 2 := Real.rpow_one 2
          have := mul_le_mul_of_nonneg_left h2 hCs
          nlinarith
  -- assembly
  have hTy : ∀ x, yNorm p (kernelOp K G x) ≤ max Cloc 0 := by
    intro x
    have h1 := ofReal_yNorm_integral_le hp (hKx x) hG hG1
    have h2 : ∫⁻ w, ‖K x w‖ₑ * ENNReal.ofReal (yNorm p (G w)) ≤ ENNReal.ofReal (max Cloc 0) :=
      (lintegral_mono fun w => mul_le_of_le_one_right zero_le (ENNReal.ofReal_le_one.2 (hG1 w))).trans
        ((hKr x).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    exact (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).1 (h1.trans h2)
  set D : ℝ → ZMod P → ℂ := fun x => kernelOp K G x - c' with hD
  have hDm : Measurable D := (measurable_kernelOp hKm hG).sub_const _
  have hDy : ∀ x, yNorm p (D x) ≤ max Cloc 0 + yNorm p c' := fun x =>
    (yNorm_sub_le hp1 _ _).trans (by linarith [hTy x])
  have hDi : ∀ y, IntegrableOn (fun x => D x y) (Ico a b) := fun y =>
    integrableOn_Ico_of_bound ((measurable_pi_apply y).comp hDm).aestronglyMeasurable
      (C := (P : ℝ) ^ p⁻¹ * (max Cloc 0 + yNorm p c')) fun x =>
        (norm_apply_le_yNorm hp0 _ y).trans (mul_le_mul_of_nonneg_left (hDy x) (by positivity))
  have hDn : IntegrableOn (fun x => yNorm p (D x)) (Ico a b) :=
    integrableOn_Ico_of_bound ((measurable_yNorm_fun p).comp hDm).aestronglyMeasurable
      (C := max Cloc 0 + yNorm p c') fun x => by
        simp only [Function.comp_apply]; rw [Real.norm_of_nonneg (yNorm_nonneg _ _)]; exact hDy x
  have havg : avgOn a b (kernelOp K G) - c' = avgOn a b D := by
    funext y
    have hTi : IntegrableOn (fun x => kernelOp K G x y) (Ico a b) := by
      have := (hDi y).add (integrableOn_const (C := c' y) (by simp [Real.volume_Ico]))
      exact this.congr_fun (fun x _ => by simp [hD]) measurableSet_Ico
    simp only [avgOn, Pi.sub_apply, hD]
    rw [integral_sub hTi (integrableOn_const (C := c' y) (by simp [Real.volume_Ico])), setIntegral_const,
      Real.volume_real_Ico_of_le hab.le, mul_sub]
    congr 1
    rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hℓ0.ne', Complex.ofReal_one, one_mul]
  have hpt : ∀ x, yNorm p (kernelOp K G x - avgOn a b (kernelOp K G)) ≤
      yNorm p (D x) + (b - a)⁻¹ * ∫ x in Ico a b, yNorm p (D x) := by
    intro x
    have e : kernelOp K G x - avgOn a b (kernelOp K G) = D x - (avgOn a b (kernelOp K G) - c') := by
      simp only [hD]; abel
    rw [e, havg]
    exact (yNorm_sub_le hp1 _ _).trans (add_le_add le_rfl (yNorm_avgOn_le hp hab hDi hDn))
  have hDl : ∫⁻ x in Ico a b, ENNReal.ofReal (yNorm p (D x)) ≤ ENNReal.ofReal (2 * Cs * ℓ) + ENNReal.ofReal (A * ℓ) := by
    calc ∫⁻ x in Ico a b, ENNReal.ofReal (yNorm p (D x))
        ≤ ∫⁻ x in Ico a b, (ENNReal.ofReal (yNorm p (kernelOp K G1 x)) + ENNReal.ofReal A) := by
          refine setLIntegral_mono' measurableSet_Ico fun x hx => ?_
          rw [← ENNReal.ofReal_add (yNorm_nonneg _ _) hA]
          refine ENNReal.ofReal_le_ofReal ?_
          have e : D x = kernelOp K G1 x + (kernelOp K G2 x - c') := by
            simp only [hD, hlin x]; abel
          rw [e]
          exact (CZ.yNorm_add_le hp1 _ _).trans (add_le_add le_rfl (hfar x hx))
      _ = (∫⁻ x in Ico a b, ENNReal.ofReal (yNorm p (kernelOp K G1 x))) + ENNReal.ofReal (A * ℓ) := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const, Real.volume_Ico,
            ← ENNReal.ofReal_mul hA]
      _ ≤ _ := add_le_add hloc le_rfl
  have hDe : ENNReal.ofReal (∫ x in Ico a b, yNorm p (D x)) = ∫⁻ x in Ico a b, ENNReal.ofReal (yNorm p (D x)) :=
    ofReal_integral_eq_lintegral_ofReal hDn (ae_of_all _ fun x => yNorm_nonneg _ _)
  calc ∫⁻ x in Ico a b, ENNReal.ofReal (yNorm p (kernelOp K G x - avgOn a b (kernelOp K G)))
      ≤ ∫⁻ x in Ico a b, (ENNReal.ofReal (yNorm p (D x)) +
          ENNReal.ofReal ((b - a)⁻¹ * ∫ x in Ico a b, yNorm p (D x))) :=
        lintegral_mono fun x => by
          rw [← ENNReal.ofReal_add (yNorm_nonneg _ _) (mul_nonneg (by positivity)
            (integral_nonneg fun x => yNorm_nonneg _ _))]
          exact ENNReal.ofReal_le_ofReal (hpt x)
    _ = 2 * ∫⁻ x in Ico a b, ENNReal.ofReal (yNorm p (D x)) := by
        have e2 : ((b - a)⁻¹ * ∫ x in Ico a b, yNorm p (D x)) * (b - a) = ∫ x in Ico a b, yNorm p (D x) := by
          field_simp
        rw [lintegral_add_right _ measurable_const, setLIntegral_const, Real.volume_Ico,
          ← ENNReal.ofReal_mul (mul_nonneg (by positivity) (integral_nonneg fun x => yNorm_nonneg _ _)), e2, hDe,
          two_mul]
    _ ≤ 2 * (ENNReal.ofReal (2 * Cs * ℓ) + ENNReal.ofReal (A * ℓ)) := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring

end PrimeBHT.TimeFrequency.X2.Pint
