module

public import PrimeBHT.TimeFrequency.X2.EnergyTop
public import PrimeBHT.TimeFrequency.X2.V16.Exceptional
public import PrimeBHT.TimeFrequency.X2.Ortho.Kernel
public import PrimeBHT.TimeFrequency.X2.Ortho.Weights
public import PrimeBHT.TimeFrequency.X2.Ortho.TileEng
public import PrimeBHT.TimeFrequency.X2.ClassKernel

/-!
# X2, nodes B5 / B5-top: the single-operator tail bound

`ψ · T_m F` for one cutoff `ψ` (decay `N` around a centre `c` at scale `R`) and one multiplier `m` whose kernel
`𝓕⁻ m` decays like `R⁻¹ (1 + |w|/R)^{-M}` satisfies

  `R^{-1/q} ‖ψ T_m F‖_{L^q(ℝ; L^s(Y))} ≤ K · λ_M(‖F‖; I)`,   `λ_M` the tail mass of `V16/Exceptional.lean`,

for `1 ≤ s`, `1 ≤ q`, `M > 1`, `N ≥ M + 1/q + ε`-type margin (`(N - M) q > 1`), `F` measurable with `‖F‖_{L^s(Y)} ≤ 1`.

Steps (all `ℝ≥0∞`-free once the pointwise bound is established):
* `ofReal_yNorm_tmult_le_kernelMul`: Minkowski's integral inequality with an arbitrary kernel bound;
* `lintegral_kernel_le_tailMass`: Peetre's inequality turns the kernel integral into `(1 + |x - c|/R)^M λ_M`;
* `yNorm_psi_tmult_le`: the pointwise bound `‖ψ(x) T_m F(x)‖ ≤ C (1 + |x-c|/R)^{M-N} λ_M`;
* `eLpNorm_psi_tmult_le`: the `L^q` norm (`∫ (1 + |x - c|/R)^{-(N-M)q} = 2R/((N-M)q - 1)`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform ComplexConjugate ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- `(1 + |t|)^{-M} ≤ ⟨t⟩^{-M} = (1 + t²)^{-M/2}` (the converse of `V16.tailWeight_le_rpow`). -/
theorem rpow_le_tailWeight {M : ℝ} (hM : 0 ≤ M) (t : ℝ) :
    (1 + |t|) ^ (-M) ≤ V16.tailWeight M t := by
  unfold V16.tailWeight
  have h1 : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
  have h0 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have h2 : (1 + t ^ 2) ^ (1 / 2 : ℝ) ≤ 1 + |t| := by
    calc (1 + t ^ 2) ^ (1 / 2 : ℝ) ≤ ((1 + |t|) ^ 2) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow h0.le h1 (by norm_num)
      _ = 1 + |t| := by
          rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_sq (by positivity)
  have h3 : (1 + |t|) ^ (-M) ≤ ((1 + t ^ 2) ^ (1 / 2 : ℝ)) ^ (-M) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
  calc (1 + |t|) ^ (-M) ≤ ((1 + t ^ 2) ^ (1 / 2 : ℝ)) ^ (-M) := h3
    _ = (1 + t ^ 2) ^ (-(M / 2)) := by
        rw [← Real.rpow_mul h0.le]; congr 1; ring

section Kernel

variable {P : ℕ} [NeZero P]

/-- Minkowski's integral inequality for `T_m F` with an arbitrary kernel bound `‖𝓕⁻ m w‖ ≤ c₀ kern w`. -/
theorem ofReal_yNorm_tmult_le_kernelMul {s : ℝ} (hs : 1 ≤ s) {m : ℝ → ℂ} (hcont : Continuous (𝓕⁻ m))
    {c0 : ℝ} (hc0 : 0 < c0) {kern : ℝ → ℝ} (hkern : ∀ w, 0 ≤ kern w)
    (hk : ∀ w, ‖𝓕⁻ m w‖ ≤ c0 * kern w) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) (x : ℝ) :
    ENNReal.ofReal (yNorm s (tmult m F x)) ≤ ENNReal.ofReal c0 *
      ∫⁻ z, ENNReal.ofReal (kern (x - z)) * ENNReal.ofReal (yNorm s (F z)) := by
  have hs0 : 0 < s := by linarith
  set Kf : ℝ → ℂ := 𝓕⁻ m with hKf
  set I : ℝ≥0∞ := ∫⁻ z, ENNReal.ofReal (kern (x - z)) * ENNReal.ofReal (yNorm s (F z)) with hI
  by_cases hItop : I = ⊤
  · rw [hItop, ENNReal.mul_top (by simpa using hc0)]
    exact le_top
  have hg_meas : Measurable fun z => yNorm s (F z) := (measurable_yNorm_fun s).comp hF
  have hKmeas : Continuous fun z => Kf (x - z) := hcont.comp (continuous_const.sub continuous_id)
  have hprod_meas : AEStronglyMeasurable (fun z => ‖Kf (x - z)‖ * yNorm s (F z)) volume :=
    (hKmeas.norm.aestronglyMeasurable).mul hg_meas.aestronglyMeasurable
  have hpt : ∀ z, ENNReal.ofReal (‖Kf (x - z)‖ * yNorm s (F z)) ≤
      ENNReal.ofReal c0 * (ENNReal.ofReal (kern (x - z)) * ENNReal.ofReal (yNorm s (F z))) := by
    intro z
    rw [← ENNReal.ofReal_mul (hkern _), ← ENNReal.ofReal_mul hc0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hk (x - z)
    calc ‖Kf (x - z)‖ * yNorm s (F z) ≤ (c0 * kern (x - z)) * yNorm s (F z) :=
          mul_le_mul_of_nonneg_right this (yNorm_nonneg' s _)
      _ = _ := by ring
  have hlint : ∫⁻ z, ENNReal.ofReal (‖Kf (x - z)‖ * yNorm s (F z)) ≤ ENNReal.ofReal c0 * I := by
    calc _ ≤ ∫⁻ z, ENNReal.ofReal c0 *
          (ENNReal.ofReal (kern (x - z)) * ENNReal.ofReal (yNorm s (F z))) := lintegral_mono hpt
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hlint_fin : ∫⁻ z, ENNReal.ofReal (‖Kf (x - z)‖ * yNorm s (F z)) < ⊤ :=
    lt_of_le_of_lt hlint (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hItop))
  have hint : Integrable (fun z => ‖Kf (x - z)‖ * yNorm s (F z)) volume :=
    ⟨hprod_meas, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun z => mul_nonneg (norm_nonneg _) (yNorm_nonneg' s _))).2 hlint_fin⟩
  have hV : ∀ y, Integrable (fun z => Kf (x - z) * F z y) volume := by
    intro y
    refine (hint.const_mul ((P : ℝ) ^ s⁻¹)).mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact hKmeas.aestronglyMeasurable.mul ((measurable_pi_apply y).comp hF).aestronglyMeasurable
    · rw [norm_mul]
      calc ‖Kf (x - z)‖ * ‖F z y‖ ≤ ‖Kf (x - z)‖ * ((P : ℝ) ^ s⁻¹ * yNorm s (F z)) :=
            mul_le_mul_of_nonneg_left (norm_apply_le_rpow_mul_yNorm hs0 _ _) (norm_nonneg _)
        _ = (P : ℝ) ^ s⁻¹ * (‖Kf (x - z)‖ * yNorm s (F z)) := by ring
  have hMink := yNorm_integral_le_of_one_le hs (fun z y => Kf (x - z) * F z y) hV
  have h1 : yNorm s (tmult m F x) ≤ ∫ z, ‖Kf (x - z)‖ * yNorm s (F z) := by
    refine hMink.trans (le_of_eq (integral_congr_ae (Eventually.of_forall fun z => ?_)))
    exact yNorm_fun_const_mul hs0 _ _
  calc ENNReal.ofReal (yNorm s (tmult m F x))
      ≤ ENNReal.ofReal (∫ z, ‖Kf (x - z)‖ * yNorm s (F z)) := ENNReal.ofReal_le_ofReal h1
    _ = ∫⁻ z, ENNReal.ofReal (‖Kf (x - z)‖ * yNorm s (F z)) :=
        ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun z => mul_nonneg (norm_nonneg _) (yNorm_nonneg' s _))
    _ ≤ _ := hlint

end Kernel

/-- The kernel integral against the polynomial kernel `R⁻¹ (1 + |x - z|/R)^{-M}` is at most
`(1 + |x - c|/R)^M λ_M(G; I)` (Peetre's inequality; `G ≥ 0` measurable, `G ≤ 1`, `I` of length `R`, centre `c`). -/
theorem lintegral_kernel_le_tailMass {M : ℝ} (hM : 1 < M) {G : ℝ → ℝ} (hGm : Measurable G)
    (hG0 : ∀ z, 0 ≤ G z) (hG1 : ∀ z, G z ≤ 1) {I : Set ℝ} (hR : 0 < (volume I).toReal) (x : ℝ) :
    ∫⁻ z, ENNReal.ofReal (((volume I).toReal)⁻¹ * (1 + |x - z| / (volume I).toReal) ^ (-M)) *
        ENNReal.ofReal (G z) ≤
      ENNReal.ofReal ((1 + |x - intervalCentre I| / (volume I).toReal) ^ M * V16.tailMass M G I) := by
  set R := (volume I).toReal with hRdef
  set c := intervalCentre I with hcdef
  set Λ := V16.tailMass M G I with hΛ
  have hM0 : 0 ≤ M := by linarith
  have hint := V16.integrable_tailWeight hM c hR
  have hBint : Integrable (fun z => (1 + |x - c| / R) ^ M * (R⁻¹ * (G z * V16.tailWeight M ((z - c) / R)))) := by
    refine Integrable.const_mul (Integrable.const_mul ?_ _) _
    refine hint.mono' (hGm.mul ((V16.measurable_tailWeight M).comp (by fun_prop))).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hG0 z) (V16.tailWeight_nonneg _ _))]
    exact mul_le_of_le_one_left (V16.tailWeight_nonneg _ _) (hG1 z)
  have hpt : ∀ z, ENNReal.ofReal (R⁻¹ * (1 + |x - z| / R) ^ (-M)) * ENNReal.ofReal (G z) ≤
      ENNReal.ofReal ((1 + |x - c| / R) ^ M * (R⁻¹ * (G z * V16.tailWeight M ((z - c) / R)))) := by
    intro z
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    -- Peetre in the form `(1 + |x - z|/R)^{-M} ≤ (1 + |x - c|/R)^M (1 + |z - c|/R)^{-M}`
    have h1 : (1 + |x - z| / R) ^ (-M) ≤ (1 + |x - c| / R) ^ M * (1 + |z - c| / R) ^ (-M) := by
      have hP2 := wt_peetre hM0 z hR x c
      have e1 : wt M z R x = (1 + |x - z| / R) ^ (-M) := by unfold wt; rw [abs_sub_comm]
      have e2 : wt M z R c = (1 + |z - c| / R) ^ (-M) := by unfold wt; rw [abs_sub_comm]
      rw [e1, e2] at hP2
      exact hP2
    have h2 : (1 + |z - c| / R) ^ (-M) ≤ V16.tailWeight M ((z - c) / R) := by
      have := rpow_le_tailWeight hM0 ((z - c) / R)
      rwa [abs_div, abs_of_pos hR] at this
    have hGz := hG0 z
    have hRi : 0 ≤ R⁻¹ := inv_nonneg.2 hR.le
    calc R⁻¹ * (1 + |x - z| / R) ^ (-M) * G z
        ≤ R⁻¹ * ((1 + |x - c| / R) ^ M * V16.tailWeight M ((z - c) / R)) * G z := by
          gcongr
          exact h1.trans (by gcongr)
      _ = _ := by ring
  calc ∫⁻ z, ENNReal.ofReal (R⁻¹ * (1 + |x - z| / R) ^ (-M)) * ENNReal.ofReal (G z)
      ≤ ∫⁻ z, ENNReal.ofReal ((1 + |x - c| / R) ^ M * (R⁻¹ * (G z * V16.tailWeight M ((z - c) / R)))) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (∫ z, (1 + |x - c| / R) ^ M * (R⁻¹ * (G z * V16.tailWeight M ((z - c) / R)))) :=
        (ofReal_integral_eq_lintegral_ofReal hBint
          (Eventually.of_forall fun z => by
            have := V16.tailWeight_nonneg M ((z - c) / R)
            have := hG0 z
            positivity)).symm
    _ = _ := by
        congr 1
        rw [integral_const_mul, integral_const_mul]
        rw [hΛ]
        unfold V16.tailMass
        have : ∀ z, ‖G z‖ = G z := fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hG0 z)]
        simp only [this, hRdef, hcdef]


/-- `T_m F` is measurable as soon as the kernel `𝓕⁻ m` is continuous (the existing `measurable_tmult` takes
`m ∈ M_ω(𝔭)`). -/
theorem measurable_tmult_of_cont {P : ℕ} {m : ℝ → ℂ} (hK : Continuous (𝓕⁻ m)) {F : ℝ → ZMod P → ℂ}
    (hF : Measurable F) : Measurable (tmult m F) := by
  refine measurable_pi_iff.2 fun y => ?_
  have h1 : StronglyMeasurable (Function.uncurry fun (x z : ℝ) => 𝓕⁻ m (x - z) * F z y) :=
    ((hK.comp (continuous_fst.sub continuous_snd)).stronglyMeasurable).mul
      ((((measurable_pi_apply y).comp hF).comp measurable_snd).stronglyMeasurable)
  exact (h1.integral_prod_right).measurable

section Pointwise

variable {P : ℕ} [NeZero P]

/-- **Pointwise single-operator bound**: `‖ψ(x) T_m F(x)‖ ≤ C (1 + |x - c|/R)^{M-N} λ_M(‖F‖; I)`. -/
theorem yNorm_psi_tmult_le {s M N : ℝ} (hs : 1 ≤ s) (hM : 1 < M) {I : Set ℝ}
    (hR : 0 < (volume I).toReal) {Cψ c0 : ℝ} (hCψ : 0 ≤ Cψ) (hc0 : 0 < c0) {ψ m : ℝ → ℂ}
    (hψ : ∀ x, ‖ψ x‖ ≤ Cψ * (1 + |x - intervalCentre I| / (volume I).toReal) ^ (-N))
    (hcont : Continuous (𝓕⁻ m))
    (hk : ∀ w, ‖𝓕⁻ m w‖ ≤
      c0 * (((volume I).toReal)⁻¹ * (1 + |w| / (volume I).toReal) ^ (-M)))
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) (hFb : ∀ x, yNorm s (F x) ≤ 1) (x : ℝ) :
    yNorm s (ψ x • tmult m F x) ≤ Cψ * c0 *
      (1 + |x - intervalCentre I| / (volume I).toReal) ^ (M - N) *
        V16.tailMass M (fun y => yNorm s (F y)) I := by
  set R := (volume I).toReal with hRdef
  set c := intervalCentre I with hcdef
  set G : ℝ → ℝ := fun y => yNorm s (F y) with hG
  have hs0 : 0 < s := by linarith
  have hGm : Measurable G := (measurable_yNorm_fun s).comp hF
  have hG0 : ∀ z, 0 ≤ G z := fun z => yNorm_nonneg' s _
  have hkern : ∀ w, 0 ≤ R⁻¹ * (1 + |w| / R) ^ (-M) := fun w => by positivity
  have h1 := ofReal_yNorm_tmult_le_kernelMul hs hcont hc0 hkern hk hF x
  have h2 := lintegral_kernel_le_tailMass hM hGm hG0 hFb hR x
  have h3 : ENNReal.ofReal (yNorm s (tmult m F x)) ≤
      ENNReal.ofReal (c0 * ((1 + |x - c| / R) ^ M * V16.tailMass M G I)) := by
    refine h1.trans ?_
    rw [ENNReal.ofReal_mul hc0.le]
    exact mul_le_mul' le_rfl h2
  have hΛ := V16.tailMass_nonneg M G I
  have h4 : yNorm s (tmult m F x) ≤ c0 * ((1 + |x - c| / R) ^ M * V16.tailMass M G I) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
  have hnorm : yNorm s (ψ x • tmult m F x) = ‖ψ x‖ * yNorm s (tmult m F x) :=
    yNorm_fun_const_mul hs0 (ψ x) (tmult m F x)
  have hb : 0 < 1 + |x - c| / R := by positivity
  have e1 : (1 + |x - c| / R) ^ (-N) * (1 + |x - c| / R) ^ M = (1 + |x - c| / R) ^ (M - N) := by
    rw [← Real.rpow_add hb]; congr 1; ring
  calc yNorm s (ψ x • tmult m F x) = ‖ψ x‖ * yNorm s (tmult m F x) := hnorm
    _ ≤ (Cψ * (1 + |x - c| / R) ^ (-N)) * (c0 * ((1 + |x - c| / R) ^ M * V16.tailMass M G I)) :=
        mul_le_mul (hψ x) h4 (yNorm_nonneg' s _) (by positivity)
    _ = Cψ * c0 * ((1 + |x - c| / R) ^ (-N) * (1 + |x - c| / R) ^ M) * V16.tailMass M G I := by ring
    _ = _ := by rw [e1]

end Pointwise

/-- `‖wt a c R‖_{L^q} = (2R/(aq - 1))^{1/q}`. -/
theorem eLpNorm_wt {a q : ℝ} (hq : 1 ≤ q) (haq : 1 < a * q) (c : ℝ) {R : ℝ} (hR : 0 < R) :
    eLpNorm (wt a c R) (ENNReal.ofReal q) volume = ENNReal.ofReal ((2 * R / (a * q - 1)) ^ (1 / q)) := by
  have hq0 : 0 < q := by linarith
  have ha : 0 < a := by
    by_contra h
    push Not at h
    nlinarith
  have hp0 : ENNReal.ofReal q ≠ 0 := by simpa using hq0
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top
    (continuous_wt a c R hR).aestronglyMeasurable, ENNReal.toReal_ofReal hq0.le]
  have e : ∀ x : ℝ, ‖wt a c R x‖ₑ ^ q = ENNReal.ofReal (wt (a * q) c R x) := by
    intro x
    have hw := wt_pos a c R x hR
    rw [Real.enorm_eq_ofReal hw.le, ENNReal.ofReal_rpow_of_nonneg hw.le hq0.le]
    congr 1
    unfold wt
    rw [← Real.rpow_mul (by positivity)]
    congr 1; ring
  simp_rw [e]
  have hint := integrable_wt haq c hR
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun x => (wt_pos _ _ _ _ hR).le), integral_wt haq c hR,
    ENNReal.ofReal_rpow_of_nonneg (by have : 0 < a * q - 1 := by linarith
                                      positivity) (by positivity)]

section Lq

variable {P : ℕ} [NeZero P]

/-- **`L^q` single-operator bound**: `R^{-1/q} ‖ψ T_m F‖_{L^q(ℝ; L^s(Y))} ≤ C λ_M(‖F‖; I)`. -/
theorem eLpNorm_psi_tmult_le {s q M N : ℝ} (hs : 1 ≤ s) (hq : 1 ≤ q) (hM : 1 < M)
    (hNM : 1 < (N - M) * q) {I : Set ℝ} (hR : 0 < (volume I).toReal) {Cψ c0 : ℝ} (hCψ : 0 ≤ Cψ)
    (hc0 : 0 < c0) {ψ m : ℝ → ℂ} (hψc : Continuous ψ)
    (hψ : ∀ x, ‖ψ x‖ ≤ Cψ * (1 + |x - intervalCentre I| / (volume I).toReal) ^ (-N))
    (hcont : Continuous (𝓕⁻ m))
    (hk : ∀ w, ‖𝓕⁻ m w‖ ≤
      c0 * (((volume I).toReal)⁻¹ * (1 + |w| / (volume I).toReal) ^ (-M)))
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) (hFb : ∀ x, yNorm s (F x) ≤ 1) :
    ENNReal.ofReal (((volume I).toReal) ^ (-1 / q)) *
        eLpNorm (fun x => yNorm s (ψ x • tmult m F x)) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (Cψ * c0 * (2 / ((N - M) * q - 1)) ^ (1 / q)) *
        ENNReal.ofReal (V16.tailMass M (fun y => yNorm s (F y)) I) := by
  set R := (volume I).toReal with hRdef
  set c := intervalCentre I with hcdef
  set Λ := V16.tailMass M (fun y => yNorm s (F y)) I with hΛdef
  have hΛ : 0 ≤ Λ := V16.tailMass_nonneg _ _ _
  have hq0 : 0 < q := by linarith
  have hmeasψ : Measurable (fun x => ψ x • tmult m F x) :=
    measurable_pi_iff.2 fun y =>
      hψc.measurable.mul ((measurable_pi_apply y).comp (measurable_tmult_of_cont hcont hF))
  have hmeas : Measurable (fun x => yNorm s (ψ x • tmult m F x)) :=
    (measurable_yNorm_fun s).comp hmeasψ
  have hpt := yNorm_psi_tmult_le hs hM hR hCψ hc0 hψ hcont hk hF hFb
  set A := Cψ * c0 * Λ with hA
  have hA0 : 0 ≤ A := by positivity
  have hmajor : ∀ x, ‖yNorm s (ψ x • tmult m F x)‖ ≤ A * wt (N - M) c R x := by
    intro x
    have hy : 0 ≤ yNorm s (ψ x • tmult m F x) := yNorm_nonneg' s _
    rw [Real.norm_eq_abs, abs_of_nonneg hy]
    refine (hpt x).trans (le_of_eq ?_)
    unfold wt
    have : (1 + |x - c| / R) ^ (M - N) = (1 + |x - c| / R) ^ (-(N - M)) := by congr 1; ring
    rw [this, hA]; ring
  have h1 : eLpNorm (fun x => yNorm s (ψ x • tmult m F x)) (ENNReal.ofReal q) volume ≤
      eLpNorm (fun x => A * wt (N - M) c R x) (ENNReal.ofReal q) volume :=
    eLpNorm_mono_ae_real hmeas.aestronglyMeasurable (Eventually.of_forall hmajor)
  have h2 : eLpNorm (fun x => A * wt (N - M) c R x) (ENNReal.ofReal q) volume =
      ENNReal.ofReal A * eLpNorm (wt (N - M) c R) (ENNReal.ofReal q) volume := by
    have := eLpNorm_const_smul (μ := volume) (p := ENNReal.ofReal q) A (wt (N - M) c R)
    rw [Real.enorm_eq_ofReal hA0] at this
    exact this
  have h3 := eLpNorm_wt (a := N - M) hq hNM c hR
  have hb : 0 < (N - M) * q - 1 := by linarith
  have e : R ^ (-1 / q) * (2 * R / ((N - M) * q - 1)) ^ (1 / q) = (2 / ((N - M) * q - 1)) ^ (1 / q) := by
    have e1 : R ^ (-1 / q) = (R⁻¹) ^ (1 / q) := by
      rw [Real.inv_rpow hR.le, ← Real.rpow_neg hR.le]; congr 1; ring
    rw [e1, ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  calc ENNReal.ofReal (R ^ (-1 / q)) * eLpNorm (fun x => yNorm s (ψ x • tmult m F x)) (ENNReal.ofReal q) volume
      ≤ ENNReal.ofReal (R ^ (-1 / q)) * (ENNReal.ofReal A *
          ENNReal.ofReal ((2 * R / ((N - M) * q - 1)) ^ (1 / q))) := by
        rw [h2, h3] at h1
        exact mul_le_mul' le_rfl h1
    _ = ENNReal.ofReal (Cψ * c0 * (2 / ((N - M) * q - 1)) ^ (1 / q)) * ENNReal.ofReal Λ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hA, ← e]
        ring

end Lq

end PrimeBHT.TimeFrequency.X2
