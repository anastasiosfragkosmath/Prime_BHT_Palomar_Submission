module

public import PrimeBHT.TimeFrequency.X2.Pint.TheoremIIAux

/-!
# X2, V11: Theorem II (interpolation with a BMO endpoint), step functions

`theoremII_step`: for finitely many kernels `K i` (jointly strongly measurable, with qualitative row and column `L¹`
bounds `Cloc`), satisfying
* (BMO) the mean oscillation bound `⨍_{[a,b)} ‖K_i G - avg_{[a,b)} K_i G‖_{s₀} ≤ Cb` for step functions `G` with
  `‖G‖_{L^∞(L^{s₀})} ≤ 1` (`s₀ = s / rF s qX`), and
* (H) the HLC intersection-form Hilbert endpoint for step functions,
every step function `F` with `yNorm s F ≤ B` satisfies
`∑_i ‖K_i F‖_{L^{qX}(L^s)}^{qX} ≤ iiConst qX Cb · (A B^{qX/2} + B₂ ‖F‖_{L^{qX}(L^s)}^{qX/2})²`.

Proof: `osc_interp` on every interval with the oscillation `d_k = coefK - avg coefK`, the reduction of the `Re z = 1`
side to `2 ⨍ ‖K_i F_{1+it}‖_2`, Minkowski (`minkowski_sq`) and the maximal function give the sharp-function majorant
`h_i = K0 · (M W_i)^{2/qX}` with `W_i = (∫ ‖K_i F_{1+it}‖_2² dν)^{1/2}`; then `fefferman_stein`, the maximal theorem in
`L²`, Tonelli and (H) for `F_{1+it}`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Complex
open scoped ENNReal
open PrimeBHT.Statements PrimeCarleson.Proof.Common

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Pint

variable {P : ℕ} [NeZero P]

/-- `‖K F_{1+it}(x)‖_2`. -/
def fT (K : ℝ → ℝ → ℂ) {κ : Type*} [Fintype κ] (E : κ → Set ℝ) (s qX : ℝ) (v : κ → ZMod P → ℂ) (t x : ℝ) : ℝ :=
  yNorm 2 (kernelOp K (stepFun E fun k => famF s qX (v k) (1 + t * I)) x)

/-- `W(x) = (∫ ‖K F_{1+it}(x)‖_2² dν(t))^{1/2}`. -/
def fW (ν : Measure ℝ) (K : ℝ → ℝ → ℂ) {κ : Type*} [Fintype κ] (E : κ → Set ℝ) (s qX : ℝ) (v : κ → ZMod P → ℂ)
    (x : ℝ) : ℝ≥0∞ :=
  (∫⁻ t, ENNReal.ofReal (fT K E s qX v t x) ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ)

/-- The constant of the sharp-function majorant. -/
def iiK0 (qX Cb : ℝ) : ℝ := (2 ^ qX * Cb ^ (qX - 2) * 4) ^ (1 / qX)

/-- The constant of Theorem II. -/
def iiConst (qX Cb : ℝ) : ℝ :=
  fsConst qX * (2 ^ qX * Cb ^ (qX - 2) * 4) * (maximalHLRConst (ENNReal.ofReal 2) : ℝ) ^ 2

section Single

variable {s qX : ℝ} (hE : 1 < s ∧ s < qX ∧ s / (s - 1) < qX) {K : ℝ → ℝ → ℂ}
  (hKm : StronglyMeasurable (Function.uncurry K)) {Cloc : ℝ} (hCloc : 0 ≤ Cloc)
  (hKr : ∀ x, ∫⁻ w, ‖K x w‖ₑ ≤ ENNReal.ofReal Cloc) {κ : Type*} [Fintype κ] {E : κ → Set ℝ}
  (hEd : IsStepData E)

include hE hKm hKr hEd

theorem measurable_fT (v : κ → ZMod P → ℂ) :
    Measurable (Function.uncurry fun x t => ENNReal.ofReal (fT K E s qX v t x)) := by
  have h1 : (Function.uncurry fun x t => ENNReal.ofReal (fT K E s qX v t x)) =
      fun p : ℝ × ℝ => ENNReal.ofReal (yNorm 2 (∑ k, coefK K E p.1 k • famF s qX (v k) (1 + p.2 * I))) := by
    funext p; simp only [Function.uncurry, fT, kernelOp_stepFun' hKm hKr hEd]
  rw [h1]
  refine ENNReal.measurable_ofReal.comp ((measurable_yNorm_fun 2).comp ?_)
  refine measurable_pi_iff.2 fun y => ?_
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ fun k _ => ((measurable_coefK hKm hEd k).comp measurable_fst).mul ?_
  have hcont : Continuous fun t : ℝ => famF s qX (v k) (1 + t * I) y :=
    (differentiable_famVec _ _ _ _ _ _ y).continuous.comp (by fun_prop)
  exact hcont.measurable.comp measurable_snd

include hCloc in
theorem fT_le (v : κ → ZMod P → ℂ) (t x : ℝ) :
    fT K E s qX v t x ≤ ∑ k, Cloc * yNorm s (v k) ^ (qX / 2) := by
  rw [fT, kernelOp_stepFun' hKm hKr hEd]
  refine (yNorm_sum_le (by norm_num) _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [yNorm_smul' two_pos, yNorm_famF_one hE]
  exact mul_le_mul_of_nonneg_right (norm_coefK_le hKr hEd hCloc x k) (Real.rpow_nonneg (yNorm_nonneg _ _) _)

include hCloc in
theorem integrableOn_coefK (a b : ℝ) (k : κ) : IntegrableOn (fun y => coefK K E y k) (Ico a b) :=
  integrableOn_Ico_of_bound (measurable_coefK hKm hEd k).aestronglyMeasurable
    fun y => norm_coefK_le hKr hEd hCloc y k

include hCloc in
/-- The vector average of a kernel operator on a step function. -/
theorem avgOn_kernelOp {a b : ℝ} (w : κ → ZMod P → ℂ) :
    avgOn a b (kernelOp K (stepFun E w)) =
      ∑ k, ((((b - a)⁻¹ : ℝ) : ℂ) * ∫ y in Ico a b, coefK K E y k) • w k := by
  funext y'
  simp only [avgOn, kernelOp_stepFun' hKm hKr hEd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_finset_sum _ fun k _ => (integrableOn_coefK hE hKm hCloc hKr hEd a b k).mul_const _,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_mul_const]; ring

variable {Cb : ℝ} (hCb : 0 ≤ Cb)
  (hBMO : ∀ (v' : κ → ZMod P → ℂ), (∀ w, yNorm (s / rF s qX) (stepFun E v' w) ≤ 1) → ∀ a b : ℝ, a < b →
    ∫⁻ x in Ico a b, ENNReal.ofReal (yNorm (s / rF s qX)
      (kernelOp K (stepFun E v') x - avgOn a b (kernelOp K (stepFun E v')))) ≤ ENNReal.ofReal (Cb * (b - a)))
  {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : PJProp (2 / qX) ν)

include hCloc hCb hBMO hν in
/-- **The sharp-function majorant** on one interval. -/
theorem osc_bound (v : κ → ZMod P → ℂ) {a b x : ℝ} (hab : a < b) (hx : x ∈ Ico a b) :
    ∃ c : ℝ, ∫⁻ y in Ico a b, ENNReal.ofReal |yNorm s (kernelOp K (stepFun E v) y) - c| ≤
      ENNReal.ofReal (b - a) * (ENNReal.ofReal (iiK0 qX Cb) * maximalHLR (fW ν K E s qX v) x ^ (2 / qX)) := by
  classical
  have hq2 := two_lt_qX hE
  have hq0 : 0 < qX := by linarith
  have hs1 : 1 ≤ s := hE.1.le
  have hba : 0 < b - a := sub_pos.2 hab
  set ak : κ → ℂ := fun k => (((b - a)⁻¹ : ℝ) : ℂ) * ∫ y in Ico a b, coefK K E y k with hak
  set d : κ → ℝ → ℂ := fun k y => coefK K E y k - ak k with hd
  have hdm : ∀ k, Measurable (d k) := fun k => (measurable_coefK hKm hEd k).sub_const _
  have hak : ∀ k, ‖ak k‖ ≤ Cloc := by
    intro k
    rw [hak, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have h1 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ico a b) measure_Ico_lt_top
      (fun y _ => norm_coefK_le hKr hEd hCloc y k)
    rw [Real.volume_real_Ico_of_le hab.le] at h1
    calc (b - a)⁻¹ * ‖∫ y in Ico a b, coefK K E y k‖ ≤ (b - a)⁻¹ * (Cloc * (b - a)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Cloc := by field_simp
  have hdb : ∀ k y, ‖d k y‖ ≤ 2 * Cloc := fun k y =>
    (norm_sub_le _ _).trans (by linarith [norm_coefK_le hKr hEd hCloc y k, hak k])
  have hid : ∀ (w : κ → ZMod P → ℂ) y, ∑ k, d k y • w k =
      kernelOp K (stepFun E w) y - avgOn a b (kernelOp K (stepFun E w)) := by
    intro w y
    rw [avgOn_kernelOp hE hKm hCloc hKr hEd w, kernelOp_stepFun' hKm hKr hEd, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => sub_smul _ _ _
  -- the `Re z = 0` hypothesis
  have h0 : ∀ t : ℝ, ∫⁻ y in Ico a b, ENNReal.ofReal (yNorm (s / rF s qX) (oscU s qX d v (t * I) y)) ≤
      ENNReal.ofReal (Cb * (b - a)) := by
    intro t
    simp only [oscU, hid]
    refine hBMO _ (fun w => ?_) a b hab
    by_cases hw : ∃ k, w ∈ E k
    · obtain ⟨k, hk⟩ := hw
      rw [stepFun_eq_of_mem hEd.2.2 _ hk]
      exact yNorm_famF_zero hE (v k) t
    · push Not at hw
      rw [stepFun_eq_zero _ hw, yNorm_zero_of_pos (div_pos (by linarith [hE.1]) (rF_pos hE))]
      norm_num
  have hOI := osc_interp hE hν d hdm hdb v hab hCb h0
  -- the `θ` side
  set c0 : ZMod P → ℂ := avgOn a b (kernelOp K (stepFun E v)) with hc0
  have hθid : ∀ y, oscU s qX d v ((2 / qX : ℝ) : ℂ) y = kernelOp K (stepFun E v) y - c0 := by
    intro y
    simp only [oscU, famF_theta hE]
    exact hid v y
  set Aθ := (b - a)⁻¹ * ∫ y in Ico a b, yNorm s (oscU s qX d v ((2 / qX : ℝ) : ℂ) y) with hAθ
  have hAθ0 : 0 ≤ Aθ := mul_nonneg (by positivity) (integral_nonneg fun y => yNorm_nonneg _ _)
  -- the `Re z = 1` side
  have hfT0 : ∀ t y, 0 ≤ fT K E s qX v t y := fun t y => yNorm_nonneg _ _
  have hfTint : ∀ t, IntegrableOn (fun y => fT K E s qX v t y) (Ico a b) := by
    intro t
    refine integrableOn_Ico_of_bound ?_ (C := ∑ k, Cloc * yNorm s (v k) ^ (qX / 2)) fun y => ?_
    · have := (measurable_fT hE hKm hKr hEd v).comp (measurable_prodMk_right (y := t))
      exact (ENNReal.measurable_toReal.comp this).aestronglyMeasurable.congr
        (ae_of_all _ fun y => by simp [ENNReal.toReal_ofReal (yNorm_nonneg _ _), fT])
    · rw [Real.norm_of_nonneg (hfT0 t y)]
      exact fT_le hE hKm hCloc hKr hEd v t y
  have h1side : ∀ t : ℝ, (b - a)⁻¹ * ∫ y in Ico a b, yNorm 2 (oscU s qX d v (1 + t * I) y) ≤
      2 * (b - a)⁻¹ * ∫ y in Ico a b, fT K E s qX v t y := by
    intro t
    set Gt : ℝ → ZMod P → ℂ := kernelOp K (stepFun E fun k => famF s qX (v k) (1 + t * I)) with hGt
    have hGi : ∀ y', IntegrableOn (fun x => Gt x y') (Ico a b) := by
      intro y'
      have e : (fun x => Gt x y') = fun x => ∑ k, coefK K E x k * famF s qX (v k) (1 + t * I) y' := by
        funext x; simp only [hGt, kernelOp_stepFun' hKm hKr hEd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [e]
      exact integrable_finset_sum _ fun k _ => (integrableOn_coefK hE hKm hCloc hKr hEd a b k).mul_const _
    have hav := yNorm_avgOn_le (p := 2) (by norm_num) hab hGi (hfTint t)
    have hpt : ∀ y, yNorm 2 (oscU s qX d v (1 + t * I) y) ≤ fT K E s qX v t y + yNorm 2 (avgOn a b Gt) := by
      intro y
      simp only [oscU]
      rw [hid]
      exact yNorm_sub_le (by norm_num) _ _
    have hI1 : ∫ y in Ico a b, yNorm 2 (oscU s qX d v (1 + t * I) y) ≤
        ∫ y in Ico a b, (fT K E s qX v t y + yNorm 2 (avgOn a b Gt)) :=
      integral_mono (integrableOn_yNorm_oscU hE hdm hdb v _ (by norm_num) a b)
        ((hfTint t).add (integrableOn_Ico_of_bound aestronglyMeasurable_const (C := yNorm 2 (avgOn a b Gt))
          fun _ => le_of_eq (Real.norm_of_nonneg (yNorm_nonneg _ _)))) hpt
    rw [integral_add (hfTint t) (integrableOn_Ico_of_bound aestronglyMeasurable_const
      (C := yNorm 2 (avgOn a b Gt)) fun _ => le_of_eq (Real.norm_of_nonneg (yNorm_nonneg _ _))),
      setIntegral_const, Real.volume_real_Ico_of_le hab.le, smul_eq_mul] at hI1
    have : (b - a) * yNorm 2 (avgOn a b Gt) ≤ ∫ y in Ico a b, fT K E s qX v t y := by
      have := mul_le_mul_of_nonneg_left hav hba.le
      rwa [← mul_assoc, mul_inv_cancel₀ hba.ne', one_mul] at this
    calc (b - a)⁻¹ * ∫ y in Ico a b, yNorm 2 (oscU s qX d v (1 + t * I) y)
        ≤ (b - a)⁻¹ * (2 * ∫ y in Ico a b, fT K E s qX v t y) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  -- Minkowski and the maximal function
  set Cv : ℝ := ∑ k, Cloc * yNorm s (v k) ^ (qX / 2) with hCv
  have hCv0 : 0 ≤ Cv := Finset.sum_nonneg fun k _ => mul_nonneg hCloc (Real.rpow_nonneg (yNorm_nonneg _ _) _)
  have hGt : ∀ t, ∫⁻ y in Ico a b, ENNReal.ofReal (fT K E s qX v t y) ≤ ENNReal.ofReal (Cv * (b - a)) := by
    intro t
    calc ∫⁻ y in Ico a b, ENNReal.ofReal (fT K E s qX v t y) ≤ ∫⁻ _y in Ico a b, ENNReal.ofReal Cv :=
          lintegral_mono fun y => ENNReal.ofReal_le_ofReal (fT_le hE hKm hCloc hKr hEd v t y)
      _ = _ := by rw [setLIntegral_const, Real.volume_Ico, ← ENNReal.ofReal_mul hCv0]
  have hmink := minkowski_sq (μ := volume.restrict (Ico a b)) (ν := ν) (measurable_fT hE hKm hKr hEd v)
    ENNReal.ofReal_ne_top hGt
  have hWI : ∫⁻ y in Ico a b, fW ν K E s qX v y ≤ ENNReal.ofReal (b - a) * maximalHLR (fW ν K E s qX v) x := by
    have h1 := PrimeBHT.TimeFrequency.Tile.lintegral_Icc_le_mul_maximalHLR (fW ν K E s qX v) hab
      (Ico_subset_Icc_self hx)
    simp only [enorm_eq_self] at h1
    exact (lintegral_mono_set Ico_subset_Icc_self).trans h1
  set Mx := maximalHLR (fW ν K E s qX v) x with hMx
  have hchain : ENNReal.ofReal (Aθ ^ qX) ≤ ENNReal.ofReal (2 ^ qX * Cb ^ (qX - 2) * 4) * Mx ^ (2 : ℝ) := by
    refine hOI.trans ?_
    calc ENNReal.ofReal (2 ^ qX * Cb ^ (qX - 2)) * ∫⁻ t, ENNReal.ofReal (((b - a)⁻¹ *
          ∫ y in Ico a b, yNorm 2 (oscU s qX d v (1 + t * I) y)) ^ 2) ∂ν
        ≤ ENNReal.ofReal (2 ^ qX * Cb ^ (qX - 2)) * ∫⁻ t, ENNReal.ofReal ((2 * (b - a)⁻¹) ^ 2) *
          (∫⁻ y in Ico a b, ENNReal.ofReal (fT K E s qX v t y)) ^ (2 : ℝ) ∂ν := by
          gcongr with t
          have hY0 : 0 ≤ ∫ y in Ico a b, fT K E s qX v t y := integral_nonneg fun y => hfT0 t y
          have e : (∫⁻ y in Ico a b, ENNReal.ofReal (fT K E s qX v t y)) =
              ENNReal.ofReal (∫ y in Ico a b, fT K E s qX v t y) :=
            (ofReal_integral_eq_lintegral_ofReal (hfTint t) (ae_of_all _ fun y => hfT0 t y)).symm
          rw [e, ENNReal.ofReal_rpow_of_nonneg hY0 (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hX0 : 0 ≤ (b - a)⁻¹ * ∫ y in Ico a b, yNorm 2 (oscU s qX d v (1 + t * I) y) :=
            mul_nonneg (by positivity) (integral_nonneg fun y => yNorm_nonneg _ _)
          calc ((b - a)⁻¹ * ∫ y in Ico a b, yNorm 2 (oscU s qX d v (1 + t * I) y)) ^ 2
              ≤ (2 * (b - a)⁻¹ * ∫ y in Ico a b, fT K E s qX v t y) ^ 2 :=
                pow_le_pow_left₀ hX0 (h1side t) 2
            _ = _ := by rw [Real.rpow_two]; ring
      _ = ENNReal.ofReal (2 ^ qX * Cb ^ (qX - 2)) * (ENNReal.ofReal ((2 * (b - a)⁻¹) ^ 2) *
          ∫⁻ t, (∫⁻ y in Ico a b, ENNReal.ofReal (fT K E s qX v t y)) ^ (2 : ℝ) ∂ν) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (2 ^ qX * Cb ^ (qX - 2)) * (ENNReal.ofReal ((2 * (b - a)⁻¹) ^ 2) *
          (ENNReal.ofReal (b - a) * Mx) ^ (2 : ℝ)) := by
          gcongr
          exact hmink.trans (ENNReal.rpow_le_rpow hWI (by norm_num))
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_nonneg hba.le (by norm_num),
            ← mul_assoc (ENNReal.ofReal _), ← ENNReal.ofReal_mul (by positivity), ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          rw [Real.rpow_two]; field_simp; ring
  have hroot : ENNReal.ofReal Aθ ≤ ENNReal.ofReal (iiK0 qX Cb) * Mx ^ (2 / qX) := by
    have hK0 : 0 ≤ 2 ^ qX * Cb ^ (qX - 2) * 4 := by
      have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) qX
      have := Real.rpow_nonneg hCb (qX - 2)
      positivity
    have h1 := ENNReal.rpow_le_rpow hchain (by positivity : (0 : ℝ) ≤ qX⁻¹)
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hAθ0 _) (by positivity),
      Real.rpow_rpow_inv hAθ0 hq0.ne', ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ENNReal.ofReal_rpow_of_nonneg hK0 (by positivity), ← ENNReal.rpow_mul] at h1
    rw [iiK0, one_div, div_eq_mul_inv]
    exact h1
  refine ⟨yNorm s c0, ?_⟩
  calc ∫⁻ y in Ico a b, ENNReal.ofReal |yNorm s (kernelOp K (stepFun E v) y) - yNorm s c0|
      ≤ ∫⁻ y in Ico a b, ENNReal.ofReal (yNorm s (oscU s qX d v ((2 / qX : ℝ) : ℂ) y)) := by
        refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
        rw [hθid]
        exact abs_yNorm_sub_le hs1 _ _
    _ = ENNReal.ofReal (b - a) * ENNReal.ofReal Aθ := by
        rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_yNorm_oscU hE hdm hdb v _ hs1 a b)
          (ae_of_all _ fun y => yNorm_nonneg _ _), ← ENNReal.ofReal_mul hba.le, hAθ, ← mul_assoc,
          mul_inv_cancel₀ hba.ne', one_mul]
    _ ≤ _ := by gcongr

end Single

/-- **Theorem II** (interpolation between the BMO endpoint and the Hilbert endpoint), step functions. -/
theorem theoremII_step {s qX : ℝ} (hE : 1 < s ∧ s < qX ∧ s / (s - 1) < qX) {ι : Type*} [Fintype ι]
    {K : ι → ℝ → ℝ → ℂ} {Cloc Cb A B₂ : ℝ} (hCloc : 0 ≤ Cloc) (hCb : 0 ≤ Cb)
    (hKm : ∀ i, StronglyMeasurable (Function.uncurry (K i)))
    (hKr : ∀ i x, ∫⁻ w, ‖K i x w‖ₑ ≤ ENNReal.ofReal Cloc)
    (hKc : ∀ i w, ∫⁻ x, ‖K i x w‖ₑ ≤ ENNReal.ofReal Cloc)
    {κ : Type*} [Fintype κ] {E : κ → Set ℝ} (hEd : IsStepData E)
    (hBMO : ∀ i (v' : κ → ZMod P → ℂ), (∀ w, yNorm (s / rF s qX) (stepFun E v' w) ≤ 1) → ∀ a b : ℝ, a < b →
      ∫⁻ x in Ico a b, ENNReal.ofReal (yNorm (s / rF s qX)
        (kernelOp (K i) (stepFun E v') x - avgOn a b (kernelOp (K i) (stepFun E v')))) ≤
          ENNReal.ofReal (Cb * (b - a)))
    (hH : ∀ (v' : κ → ZMod P → ℂ) (B₀ : ℝ), (∀ w, yNorm 2 (stepFun E v' w) ≤ B₀) →
      ∑ i, ∫⁻ x, ENNReal.ofReal (yNorm 2 (kernelOp (K i) (stepFun E v') x) ^ 2) ≤
        ENNReal.ofReal ((A * B₀ + B₂ * (∫ x, yNorm 2 (stepFun E v' x) ^ 2) ^ ((1 : ℝ) / 2)) ^ 2))
    (v : κ → ZMod P → ℂ) (B : ℝ) (hB : ∀ w, yNorm s (stepFun E v w) ≤ B) :
    ∑ i, ∫⁻ x, ENNReal.ofReal (yNorm s (kernelOp (K i) (stepFun E v) x) ^ qX) ≤
      ENNReal.ofReal (iiConst qX Cb) *
        ENNReal.ofReal ((A * B ^ (qX / 2) + B₂ * (∫ x, yNorm s (stepFun E v x) ^ qX) ^ ((1 : ℝ) / 2)) ^ 2) := by
  have hq2 := two_lt_qX hE
  have hq0 : 0 < qX := by linarith
  have hs1 : 1 ≤ s := hE.1.le
  obtain ⟨ν, hν1, hν⟩ := exists_pointwisePJ (θ := 2 / qX) ⟨by positivity, by rw [div_lt_one hq0]; linarith⟩
  have := hν1
  set CM : ℝ := (maximalHLRConst (ENNReal.ofReal 2) : ℝ) with hCM
  set X0 : ℝ := 2 ^ qX * Cb ^ (qX - 2) * 4 with hX0
  have hX00 : 0 ≤ X0 := by
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) qX
    have := Real.rpow_nonneg hCb (qX - 2)
    positivity
  set RHS : ℝ := (A * B ^ (qX / 2) + B₂ * (∫ x, yNorm s (stepFun E v x) ^ qX) ^ ((1 : ℝ) / 2)) ^ 2 with hRHS
  set f : ι → ℝ → ℝ → ℝ≥0∞ := fun i x t => ENNReal.ofReal (fT (K i) E s qX v t x) ^ (2 : ℝ) with hf
  have hfm : ∀ i, Measurable (Function.uncurry (f i)) := fun i =>
    (measurable_fT hE (hKm i) (hKr i) hEd v).pow_const _
  -- per kernel
  have hper : ∀ i, ∫⁻ x, ENNReal.ofReal (yNorm s (kernelOp (K i) (stepFun E v) x) ^ qX) ≤
      ENNReal.ofReal (fsConst qX * X0 * CM ^ 2) * ∫⁻ x, ∫⁻ t, f i x t ∂ν := by
    intro i
    set g : ℝ → ℝ := fun x => yNorm s (kernelOp (K i) (stepFun E v) x) with hg
    have hrep : ∀ x, g x = yNorm s (∑ k, coefK (K i) E x k • v k) := fun x => by
      rw [hg]; simp only [kernelOp_stepFun' (hKm i) (hKr i) hEd]
    have hgm : Measurable g := by
      have : g = fun x => yNorm s (∑ k, coefK (K i) E x k • v k) := funext hrep
      rw [this]
      exact (measurable_yNorm_fun s).comp (Finset.measurable_sum _ fun k _ =>
        (measurable_coefK (hKm i) hEd k).smul_const _)
    have hg0 : ∀ x, 0 ≤ g x := fun x => yNorm_nonneg _ _
    have hgle : ∀ x, g x ≤ ∑ k, ‖coefK (K i) E x k‖ * yNorm s (v k) := fun x => by
      rw [hrep]
      refine (yNorm_sum_le hs1 _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [yNorm_smul' (by linarith)]
    have hgi : Integrable g := by
      refine Integrable.mono' (g := fun x => ∑ k, ‖coefK (K i) E x k‖ * yNorm s (v k))
        (integrable_finset_sum Finset.univ fun k _ =>
        ((integrable_coefK (hKm i) hEd (hKc i) k).norm.mul_const (yNorm s (v k)))) hgm.aestronglyMeasurable
        (ae_of_all _ fun x => ?_)
      rw [Real.norm_of_nonneg (hg0 x)]
      exact hgle x
    set Cg : ℝ := ∑ k, Cloc * yNorm s (v k) with hCg
    have hgC : ∀ x, g x ≤ Cg := fun x => (hgle x).trans (Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_right (norm_coefK_le (hKr i) hEd hCloc x k) (yNorm_nonneg _ _))
    have hfin : ∫⁻ x, ENNReal.ofReal (g x ^ qX) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ∫⁻ x, ENNReal.ofReal (Cg ^ (qX - 1)) * ENNReal.ofReal (g x)) ?_
        (lintegral_mono fun x => ?_)
      · rw [lintegral_const_mul _ hgm.ennreal_ofReal]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          ((hasFiniteIntegral_iff_ofReal (ae_of_all _ hg0)).1 hgi.2).ne
      · rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ((hg0 x).trans (hgC x)) _)]
        refine ENNReal.ofReal_le_ofReal ?_
        have e : g x ^ qX = g x ^ (qX - 1) * g x := by
          rw [← Real.rpow_add_one' (hg0 x) (by linarith)]; ring_nf
        rw [e]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (hg0 x) (hgC x) (by linarith)) (hg0 x)
    set M := maximalHLR (fW ν (K i) E s qX v) with hMdef
    have hWm : Measurable (fW ν (K i) E s qX v) :=
      (Measurable.lintegral_prod_right' (hfm i)).pow_const _
    have hFS := fefferman_stein (by linarith : 1 < qX) hgm hg0 hgi hfin
      (measurable_const.mul ((measurable_maximalHLR _).pow_const (2 / qX)))
      (fun a b hab x hx => osc_bound hE (hKm i) hCloc (hKr i) hEd hCb (hBMO i) hν v hab hx)
    have hM2 : ∫⁻ x, M x ^ (2 : ℝ) ≤ ENNReal.ofReal (CM ^ 2) * ∫⁻ x, fW ν (K i) E s qX v x ^ (2 : ℝ) := by
      have h1 := lintegral_maximal_rpow_le (by norm_num : (1 : ℝ) < 2) hWm
      have h2 := ENNReal.rpow_le_rpow h1 (by norm_num : (0 : ℝ) ≤ 2)
      rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
        show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one] at h2
      refine h2.trans_eq ?_
      rw [show ((maximalHLRConst (ENNReal.ofReal 2) : ℝ≥0∞)) = ENNReal.ofReal CM from
        (ENNReal.ofReal_coe_nnreal).symm, ENNReal.ofReal_rpow_of_nonneg (NNReal.coe_nonneg _) (by norm_num),
        Real.rpow_two]
    have hW2 : ∀ x, fW ν (K i) E s qX v x ^ (2 : ℝ) = ∫⁻ t, f i x t ∂ν := fun x => by
      rw [fW, ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
    have hh : ∀ x, (ENNReal.ofReal (iiK0 qX Cb) * M x ^ (2 / qX)) ^ qX = ENNReal.ofReal X0 * M x ^ (2 : ℝ) := by
      intro x
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, div_mul_cancel₀ _ hq0.ne', iiK0,
        ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hX00 _) hq0.le, ← Real.rpow_mul hX00,
        one_div_mul_cancel hq0.ne', Real.rpow_one]
    refine hFS.trans (le_of_eq_of_le (congrArg (ENNReal.ofReal (fsConst qX) * ·) (lintegral_congr hh)) ?_)
    rw [lintegral_const_mul _ ((measurable_maximalHLR _).pow_const _)]
    calc ENNReal.ofReal (fsConst qX) * (ENNReal.ofReal X0 * ∫⁻ x, M x ^ (2 : ℝ))
        ≤ ENNReal.ofReal (fsConst qX) * (ENNReal.ofReal X0 *
          (ENNReal.ofReal (CM ^ 2) * ∫⁻ x, fW ν (K i) E s qX v x ^ (2 : ℝ))) := by gcongr
      _ = _ := by
          simp_rw [hW2]
          rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (fsConst_pos qX).le,
            ← ENNReal.ofReal_mul (mul_nonneg (fsConst_pos qX).le hX00)]
  -- the Hilbert endpoint at `F_{1+it}`
  have hH' : ∀ t, ∑ i, ∫⁻ x, f i x t ≤ ENNReal.ofReal RHS := by
    intro t
    have hpt2 : ∀ w, yNorm 2 (stepFun E (fun k => famF s qX (v k) (1 + t * I)) w) =
        yNorm s (stepFun E v w) ^ (qX / 2) := yNorm_stepFun_famF hE hEd.2.2 v t
    have hInt : ∫ x, yNorm 2 (stepFun E (fun k => famF s qX (v k) (1 + t * I)) x) ^ 2 =
        ∫ x, yNorm s (stepFun E v x) ^ qX := by
      congr 1; funext x
      rw [hpt2, ← Real.rpow_natCast, ← Real.rpow_mul (yNorm_nonneg _ _)]
      congr 1; push_cast; ring
    have h := hH (fun k => famF s qX (v k) (1 + t * I)) (B ^ (qX / 2)) (fun w => by
      rw [hpt2]; exact Real.rpow_le_rpow (yNorm_nonneg _ _) (hB w) (by linarith))
    rw [hInt] at h
    refine le_of_eq_of_le (Finset.sum_congr rfl fun i _ => lintegral_congr fun x => ?_) h
    simp only [hf, fT]
    rw [ENNReal.ofReal_rpow_of_nonneg (yNorm_nonneg _ _) (by norm_num), Real.rpow_two]
  calc ∑ i, ∫⁻ x, ENNReal.ofReal (yNorm s (kernelOp (K i) (stepFun E v) x) ^ qX)
      ≤ ∑ i, ENNReal.ofReal (fsConst qX * X0 * CM ^ 2) * ∫⁻ x, ∫⁻ t, f i x t ∂ν :=
        Finset.sum_le_sum fun i _ => hper i
    _ = ENNReal.ofReal (fsConst qX * X0 * CM ^ 2) * ∫⁻ t, (∑ i, ∫⁻ x, f i x t) ∂ν := by
        rw [← Finset.mul_sum]
        congr 1
        rw [lintegral_finsetSum (μ := ν) Finset.univ (f := fun i t => ∫⁻ x, f i x t)
          fun i _ => (hfm i).lintegral_prod_left']
        exact Finset.sum_congr rfl fun i _ =>
          lintegral_lintegral_swap (μ := volume) (ν := ν) (hfm i).aemeasurable
    _ ≤ ENNReal.ofReal (fsConst qX * X0 * CM ^ 2) * ∫⁻ _, ENNReal.ofReal RHS ∂ν := by
        gcongr with t
        exact hH' t
    _ = _ := by rw [lintegral_const, measure_univ, mul_one, iiConst]

end PrimeBHT.TimeFrequency.X2.Pint
