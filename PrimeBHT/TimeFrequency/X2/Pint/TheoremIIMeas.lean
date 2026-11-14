module

public import PrimeBHT.TimeFrequency.X2.Pint.TheoremII

/-!
# X2, V11: Theorem II for measurable functions (density)

`theoremII_meas`: the conclusion of `theoremII_step` for every measurable `F` with `yNorm s (F w) ≤ B` and
`∫⁻ yNorm s (F w)^{qX} < ⊤`, from the BMO and Hilbert hypotheses for step functions; the proof of `theoremI_meas`
verbatim (simple-function approximation retracted onto the `yNorm s`-ball, Fatou, dominated convergence).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Pint

variable {P : ℕ} [NeZero P]

theorem theoremII_meas {s qX : ℝ} (hE : 1 < s ∧ s < qX ∧ s / (s - 1) < qX) {ι : Type*} [Fintype ι]
    {K : ι → ℝ → ℝ → ℂ} {Cloc Cb A B₂ : ℝ} (hCloc : 0 ≤ Cloc) (hCb : 0 ≤ Cb)
    (hKm : ∀ i, StronglyMeasurable (Function.uncurry (K i)))
    (hKr : ∀ i x, ∫⁻ w, ‖K i x w‖ₑ ≤ ENNReal.ofReal Cloc)
    (hKc : ∀ i w, ∫⁻ x, ‖K i x w‖ₑ ≤ ENNReal.ofReal Cloc)
    (hBMO : ∀ (κ : Type) [Fintype κ] (E : κ → Set ℝ), IsStepData E → ∀ i (v' : κ → ZMod P → ℂ),
      (∀ w, yNorm (s / rF s qX) (stepFun E v' w) ≤ 1) → ∀ a b : ℝ, a < b →
      ∫⁻ x in Ico a b, ENNReal.ofReal (yNorm (s / rF s qX)
        (kernelOp (K i) (stepFun E v') x - avgOn a b (kernelOp (K i) (stepFun E v')))) ≤
          ENNReal.ofReal (Cb * (b - a)))
    (hH : ∀ (κ : Type) [Fintype κ] (E : κ → Set ℝ), IsStepData E → ∀ (v' : κ → ZMod P → ℂ) (B₀ : ℝ),
      (∀ w, yNorm 2 (stepFun E v' w) ≤ B₀) →
      ∑ i, ∫⁻ x, ENNReal.ofReal (yNorm 2 (kernelOp (K i) (stepFun E v') x) ^ 2) ≤
        ENNReal.ofReal ((A * B₀ + B₂ * (∫ x, yNorm 2 (stepFun E v' x) ^ 2) ^ ((1 : ℝ) / 2)) ^ 2))
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {B : ℝ} (hB : ∀ w, yNorm s (F w) ≤ B)
    (hM : ∫⁻ w, ENNReal.ofReal (yNorm s (F w) ^ qX) ≠ ⊤) :
    ∑ i, ∫⁻ x, ENNReal.ofReal (yNorm s (kernelOp (K i) F x) ^ qX) ≤
      ENNReal.ofReal (iiConst qX Cb) *
        ENNReal.ofReal ((A * B ^ (qX / 2) + B₂ * (∫ x, yNorm s (F x) ^ qX) ^ ((1 : ℝ) / 2)) ^ 2) := by
  have hq2 := two_lt_qX hE
  have hs : 0 < s := by linarith [hE.1]
  have hq0 : 0 < qX := by linarith
  have hB0 : 0 ≤ B := (yNorm_nonneg s (F 0)).trans (hB 0)
  have hKx : ∀ i x, Integrable (K i x) := fun i x =>
    ⟨((hKm i).comp_measurable measurable_prodMk_left).aestronglyMeasurable,
      (hKr i x).trans_lt ENNReal.ofReal_lt_top⟩
  have hPs : 0 < (P : ℝ) ^ s⁻¹ :=
    Real.rpow_pos_of_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))) _
  have hsup : ∀ v : ZMod P → ℂ, ‖v‖ ≤ (P : ℝ) ^ s⁻¹ * yNorm s v := fun v =>
    (pi_norm_le_iff_of_nonneg (by have := yNorm_nonneg s v; positivity)).2 fun y => norm_apply_le_yNorm hs v y
  have hcY : Continuous fun v : ZMod P → ℂ => yNorm s v ^ qX :=
    (continuous_yNorm hs).rpow_const fun _ => Or.inr hq0.le
  rcases eq_or_lt_of_le hB0 with hB0' | hBpos
  · have hF0 : ∀ w, F w = 0 := fun w =>
      (yNorm_eq_zero_iff_of_pos hs _).1 (le_antisymm (hB0' ▸ hB w) (yNorm_nonneg _ _))
    have h0 : ∀ i x, kernelOp (K i) F x = 0 := fun i x => by funext y; simp [kernelOp, hF0]
    simp only [h0, yNorm_zero_of_pos hs, Real.zero_rpow hq0.ne', ENNReal.ofReal_zero, lintegral_zero,
      Finset.sum_const_zero]
    exact zero_le
  -- the approximation
  set ap : ℕ → SimpleFunc ℝ (ZMod P → ℂ) := fun n =>
    SimpleFunc.approxOn F hF Set.univ 0 (Set.mem_univ _) n with hap
  set G : ℕ → SimpleFunc ℝ (ZMod P → ℂ) := fun n => (ap n).map (retr s B) with hG
  have hGapp : ∀ n w, G n w = retr s B (ap n w) := fun n w => rfl
  have hGlim : ∀ w, Tendsto (fun n => G n w) atTop (𝓝 (F w)) := by
    intro w
    have h1 := SimpleFunc.tendsto_approxOn hF (Set.mem_univ (0 : ZMod P → ℂ)) (x := w) (by simp)
    have h2 := ((continuous_retr hs hBpos).tendsto (F w)).comp h1
    rwa [retr_of_le hs hBpos (hB w)] at h2
  have hGB : ∀ n w, yNorm s (G n w) ≤ B := fun n w => yNorm_retr_le hs hBpos _
  have hGnorm : ∀ n w, ‖G n w‖ ≤ 2 * ‖F w‖ := by
    intro n w
    refine (norm_retr_le hs hBpos _).trans ?_
    have h := SimpleFunc.edist_approxOn_y0_le hF (Set.mem_univ (0 : ZMod P → ℂ)) w n
    simp only [edist_dist, dist_zero_left] at h
    rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
    linarith
  have hFmeas : Measurable fun w => ENNReal.ofReal (yNorm s (F w) ^ qX) :=
    ENNReal.measurable_ofReal.comp (((measurable_yNorm_fun s).comp hF).pow_const qX)
  have hstep : ∀ n, IsStepData (fun c : ↥((G n).range.filter (· ≠ 0)) => (G n) ⁻¹' {c.1}) := by
    intro n
    refine ⟨fun c => (G n).measurableSet_fiber _, fun c => ?_, fun c c' hcc => ?_⟩
    · have hc0 : c.1 ≠ 0 := (Finset.mem_filter.1 c.2).2
      set δ := ‖c.1‖ / (2 * (P : ℝ) ^ s⁻¹) with hδ
      have hδ0 : 0 < δ := div_pos (norm_pos_iff.2 hc0) (by positivity)
      have hsub : (G n) ⁻¹' {c.1} ⊆
          {w | ENNReal.ofReal (δ ^ qX) ≤ ENNReal.ofReal (yNorm s (F w) ^ qX)} := by
        intro w hw
        have hw' : G n w = c.1 := hw
        have h1 : ‖c.1‖ ≤ 2 * ‖F w‖ := hw' ▸ hGnorm n w
        have h2 := hsup (F w)
        have h3 : δ ≤ yNorm s (F w) := by
          rw [hδ, div_le_iff₀ (by positivity)]; nlinarith
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hδ0.le h3 hq0.le)
      have hne : ENNReal.ofReal (δ ^ qX) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hδ0 _)).ne'
      exact (measure_mono hsub).trans_lt ((meas_ge_le_lintegral_div hFmeas.aemeasurable hne
        ENNReal.ofReal_ne_top).trans_lt (ENNReal.div_lt_top hM hne))
    · refine Set.disjoint_left.2 fun w hw hw' => hcc (Subtype.ext ?_)
      exact (hw : G n w = c.1).symm.trans (hw' : G n w = c'.1)
  have hGI : ∀ n, ∑ i, ∫⁻ x, ENNReal.ofReal (yNorm s (kernelOp (K i) (G n) x) ^ qX) ≤
      ENNReal.ofReal (iiConst qX Cb) * ENNReal.ofReal ((A * B ^ (qX / 2) +
        B₂ * (∫ x, yNorm s (G n x) ^ qX) ^ ((1 : ℝ) / 2)) ^ 2) := by
    intro n
    have hfe : stepFun (fun c : ↥((G n).range.filter (· ≠ 0)) => (G n) ⁻¹' {c.1}) (fun c => c.1) = ⇑(G n) :=
      funext (simpleFunc_eq_stepFun (G n))
    have h := theoremII_step (κ := ↥((G n).range.filter (· ≠ 0))) hE hCloc hCb hKm hKr hKc (hstep n)
      (fun i => hBMO _ _ (hstep n) i) (hH _ _ (hstep n)) (fun c => c.1) B (fun w => by rw [hfe]; exact hGB n w)
    rwa [hfe] at h
  -- convergence of the kernel operators
  have hKlim : ∀ i x, Tendsto (fun n => kernelOp (K i) (G n) x) atTop (𝓝 (kernelOp (K i) F x)) := by
    intro i x
    refine tendsto_pi_nhds.2 fun y => ?_
    show Tendsto (fun n => ∫ w, K i x w * G n w y) atTop (𝓝 (∫ w, K i x w * F w y))
    refine tendsto_integral_of_dominated_convergence (fun w => ‖K i x w‖ * ((P : ℝ) ^ s⁻¹ * B))
      (fun n => ?_) ((hKx i x).norm.mul_const _) (fun n => ae_of_all _ fun w => ?_) (ae_of_all _ fun w => ?_)
    · exact (hKx i x).aestronglyMeasurable.mul
        ((measurable_pi_apply y).comp (G n).measurable).aestronglyMeasurable
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((norm_apply_le_yNorm hs _ y).trans
        (mul_le_mul_of_nonneg_left (hGB n w) hPs.le)) (norm_nonneg _)
    · exact tendsto_const_nhds.mul ((continuous_apply y).continuousAt.tendsto.comp (hGlim w))
  set f : ℕ → ℝ → ℝ≥0∞ := fun n x => ∑ i, ENNReal.ofReal (yNorm s (kernelOp (K i) (G n) x) ^ qX) with hf
  have hfi : ∀ n i, Measurable fun x => ENNReal.ofReal (yNorm s (kernelOp (K i) (G n) x) ^ qX) :=
    fun n i => ENNReal.measurable_ofReal.comp
      (((measurable_yNorm_fun s).comp (measurable_kernelOp (hKm i) (G n).measurable)).pow_const qX)
  have hfm : ∀ n, Measurable (f n) := fun n => Finset.measurable_sum _ fun i _ => hfi n i
  have hflim : ∀ x, Tendsto (fun n => f n x) atTop
      (𝓝 (∑ i, ENNReal.ofReal (yNorm s (kernelOp (K i) F x) ^ qX))) := by
    intro x
    refine tendsto_finset_sum _ fun i _ => ?_
    exact ENNReal.tendsto_ofReal ((hcY.tendsto _).comp (hKlim i x))
  -- convergence of the right side
  have hFint : Integrable (fun x => yNorm s (F x) ^ qX) :=
    ⟨(((measurable_yNorm_fun s).comp hF).pow_const qX).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => Real.rpow_nonneg (yNorm_nonneg _ _) _)).2
        (lt_top_iff_ne_top.2 hM)⟩
  have hInt : Tendsto (fun n => ∫ x, yNorm s (G n x) ^ qX) atTop (𝓝 (∫ x, yNorm s (F x) ^ qX)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => (2 * (P : ℝ) ^ s⁻¹) ^ qX * yNorm s (F x) ^ qX)
      (fun n => ?_) (hFint.const_mul _) (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · exact (((measurable_yNorm_fun s).comp (G n).measurable).pow_const qX).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (Real.rpow_nonneg (yNorm_nonneg _ _) _),
        ← Real.mul_rpow (by positivity) (yNorm_nonneg _ _)]
      refine Real.rpow_le_rpow (yNorm_nonneg _ _) ?_ hq0.le
      calc yNorm s (G n x) ≤ ‖G n x‖ := yNorm_le_norm hs _
        _ ≤ 2 * ‖F x‖ := hGnorm n x
        _ ≤ 2 * ((P : ℝ) ^ s⁻¹ * yNorm s (F x)) := by gcongr; exact hsup (F x)
        _ = 2 * (P : ℝ) ^ s⁻¹ * yNorm s (F x) := by ring
    · exact (hcY.tendsto _).comp (hGlim x)
  have hR : Tendsto (fun n => ENNReal.ofReal (iiConst qX Cb) * ENNReal.ofReal ((A * B ^ (qX / 2) +
      B₂ * (∫ x, yNorm s (G n x) ^ qX) ^ ((1 : ℝ) / 2)) ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (iiConst qX Cb) * ENNReal.ofReal ((A * B ^ (qX / 2) +
        B₂ * (∫ x, yNorm s (F x) ^ qX) ^ ((1 : ℝ) / 2)) ^ 2))) := by
    refine ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal ?_) (Or.inr ENNReal.ofReal_ne_top)
    have hc : Continuous fun I : ℝ => (A * B ^ (qX / 2) + B₂ * I ^ ((1 : ℝ) / 2)) ^ 2 :=
      (continuous_const.add (continuous_const.mul (Real.continuous_rpow_const (by norm_num)))).pow 2
    exact (hc.tendsto _).comp hInt
  calc ∑ i, ∫⁻ x, ENNReal.ofReal (yNorm s (kernelOp (K i) F x) ^ qX)
      = ∫⁻ x, ∑ i, ENNReal.ofReal (yNorm s (kernelOp (K i) F x) ^ qX) :=
        (lintegral_finsetSum _ fun i _ => ENNReal.measurable_ofReal.comp
          (((measurable_yNorm_fun s).comp (measurable_kernelOp (hKm i) hF)).pow_const qX)).symm
    _ = ∫⁻ x, liminf (fun n => f n x) atTop := lintegral_congr fun x => ((hflim x).liminf_eq).symm
    _ ≤ liminf (fun n => ∫⁻ x, f n x) atTop := lintegral_liminf_le hfm
    _ ≤ liminf (fun n => ENNReal.ofReal (iiConst qX Cb) * ENNReal.ofReal ((A * B ^ (qX / 2) +
          B₂ * (∫ x, yNorm s (G n x) ^ qX) ^ ((1 : ℝ) / 2)) ^ 2)) atTop := by
        refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
        rw [hf, lintegral_finsetSum _ fun i _ => hfi n i]
        exact hGI n
    _ = _ := hR.liminf_eq

end PrimeBHT.TimeFrequency.X2.Pint
