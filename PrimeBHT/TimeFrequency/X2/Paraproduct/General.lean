module

public import PrimeBHT.TimeFrequency.X2.Paraproduct.Schwartz
public import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# V14 (paraproduct) for the data class of the draft: density from tensor Schwartz data

The draft `paraproduct` is stated for measurable `g_k : ℝ → (ZMod P → ℂ)` with `yNorm 2 (g_k x)` bounded and
integrable.  `Paraproduct/Schwartz.lean` proves the inequality for tensor Schwartz data; here it is extended by
density (`paraproduct`):

* `GoodData`: the draft's hypotheses on `g_k`;
* coordinates `yInner (g x) (yChar a)` are bounded, integrable, hence in every `L^p`, `1 ≤ p < ∞`, and are
  approximated by Schwartz maps in `L^{p}` (`MemLp.exist_eLpNorm_sub_le`);
* `eLpNorm_tmult_le`: for an adapted symbol `σ` the convolution `tmult σ` is bounded on `L^p(ℝ; L^s(Y_P))`
  (single-scale maximal bound + Hardy-Littlewood), so the three-term telescoping of the trilinear integrand and
  Hölder show that the left side is continuous in the `L^{p_k}` norms;
* the inequality passes to the limit.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate Real ContDiff
open PrimeBHT.Statements PrimeBHT.TimeFrequency.X2.CZ

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-! ## `L^p` membership of bounded integrable functions -/

theorem memLp_of_bdd_integrable' {φ : ℝ → ℂ} (hm : Measurable φ) (hi : Integrable φ volume) {B : ℝ}
    (hB : ∀ x, ‖φ x‖ ≤ B) {p : ℝ} (hp : 1 ≤ p) : MemLp φ (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top
    hm.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
  have h1 : ∀ x, ‖φ x‖ₑ ^ p ≤ ENNReal.ofReal B ^ (p - 1) * ‖φ x‖ₑ := by
    intro x
    have hle : ‖φ x‖ₑ ≤ ENNReal.ofReal B := by
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hB x)
    rcases eq_or_ne ‖φ x‖ₑ 0 with h0 | h0
    · rw [h0, ENNReal.zero_rpow_of_pos hp0]; simp
    · calc ‖φ x‖ₑ ^ p = ‖φ x‖ₑ ^ (p - 1) * ‖φ x‖ₑ := by
            conv_lhs => rw [show p = (p - 1) + 1 by ring]
            rw [ENNReal.rpow_add _ _ h0 enorm_ne_top, ENNReal.rpow_one]
        _ ≤ _ := mul_le_mul' (ENNReal.rpow_le_rpow hle (by linarith)) le_rfl
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono h1) ?_)
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)]
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top) hi.2

/-- Schwartz approximation in `L^p`, `1 ≤ p < ∞`. -/
theorem exists_schwartz_approx {p : ℝ} (hp : 1 ≤ p) {φ : ℝ → ℂ} (hφ : MemLp φ (ENNReal.ofReal p) volume)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : 𝓢(ℝ, ℂ), eLpNorm (fun x => φ x - ψ x) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal ε := by
  have hp0 : 0 < p := by linarith
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  obtain ⟨g, hg1, hg2, hg3⟩ := hφ.exist_eLpNorm_sub_le ENNReal.ofReal_ne_top h1 hε
  exact ⟨hg1.toSchwartzMap hg2, hg3⟩

/-! ## The data class of the draft -/

section Good

variable {P : ℕ} [NeZero P]

theorem yNorm_sub_le {s : ℝ} (hs : 1 ≤ s) (F G : ZMod P → ℂ) : yNorm s (F - G) ≤ yNorm s F + yNorm s G := by
  have : Fact (1 ≤ ENNReal.ofReal s) := ⟨by simpa using ENNReal.ofReal_le_ofReal hs⟩
  rw [yNorm_eq_norm_toLp hs, yNorm_eq_norm_toLp hs, yNorm_eq_norm_toLp hs]
  have hc : 0 ≤ (P : ℝ) ^ (-s⁻¹) := by positivity
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ hc
  have : (WithLp.toLp (ENNReal.ofReal s) (F - G) : PiLp (ENNReal.ofReal s) (fun _ : ZMod P => ℂ)) =
      WithLp.toLp (ENNReal.ofReal s) F - WithLp.toLp (ENNReal.ofReal s) G := rfl
  rw [this]
  exact norm_sub_le (WithLp.toLp (ENNReal.ofReal s) F) (WithLp.toLp (ENNReal.ofReal s) G)

/-- The hypotheses of the draft on a slot function `g : ℝ → (ZMod P → ℂ)`. -/
structure GoodData (F : ℝ → ZMod P → ℂ) : Prop where
  meas : Measurable F
  bdd : ∃ B : ℝ, ∀ x, yNorm 2 (F x) ≤ B
  int : Integrable (fun x => yNorm 2 (F x)) volume

theorem GoodData.sub {F G : ℝ → ZMod P → ℂ} (hF : GoodData F) (hG : GoodData G) :
    GoodData (fun x => F x - G x) := by
  refine ⟨hF.meas.sub hG.meas, ?_, ?_⟩
  · obtain ⟨B₁, h₁⟩ := hF.bdd
    obtain ⟨B₂, h₂⟩ := hG.bdd
    exact ⟨B₁ + B₂, fun x => (yNorm_sub_le (by norm_num) _ _).trans (add_le_add (h₁ x) (h₂ x))⟩
  · refine Integrable.mono' (hF.int.add hG.int) ?_ (Eventually.of_forall fun x => ?_)
    · exact ((measurable_yNorm_fun 2).comp (hF.meas.sub hG.meas)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (yNorm_nonneg' _ _)]
      exact yNorm_sub_le (by norm_num) _ _

theorem GoodData.tensorFun (f : TS P) : GoodData (tensorFun f) := by
  refine ⟨measurable_tensorFun f, ?_, ?_⟩
  · have : ∀ A : ZMod P, ∃ C : ℝ, ∀ x, ‖f A x‖ ≤ C := fun A => schwartz_bdd (f A)
    choose C hC using this
    exact ⟨∑ A, C A, fun x => (yNorm_tensorFun_le (by norm_num) f x).trans
      (Finset.sum_le_sum fun A _ => hC A x)⟩
  · refine Integrable.mono' (integrable_finsetSum (Finset.univ : Finset (ZMod P)) fun A _ => (f A).integrable.norm) ?_
      (Eventually.of_forall fun x => ?_)
    · exact (measurable_yNorm_tensorFun 2 f).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (yNorm_nonneg' _ _)]
      exact yNorm_tensorFun_le (by norm_num) f x

/-! ### Coordinates and Schwartz approximation -/

/-- The coordinate `a` of a slot function: `x ↦ ⟨F(x), e_a⟩`. -/
def coordF (F : ℝ → ZMod P → ℂ) (a : ZMod P) (x : ℝ) : ℂ := yInner (F x) (yChar a)

theorem eq_sum_coordF (F : ℝ → ZMod P → ℂ) (x : ℝ) : F x = ∑ a, coordF F a x • yChar a :=
  eq_sum_yInner_smul_yChar (F x)

theorem measurable_coordF {F : ℝ → ZMod P → ℂ} (hF : Measurable F) (a : ZMod P) :
    Measurable (coordF F a) := by
  unfold coordF yInner
  refine measurable_const.mul (Finset.measurable_sum _ fun y _ => ?_)
  exact ((measurable_pi_apply y).comp hF).mul measurable_const

theorem yNorm_two_yChar (a : ZMod P) : yNorm 2 (yChar a) = 1 := by
  have h := yInner_self (yChar a)
  rw [yInner_yChar_yChar] at h
  simp only [↓reduceIte] at h
  have h2 : yNorm 2 (yChar a) ^ 2 = 1 := by exact_mod_cast h.symm
  have h3 := yNorm_nonneg' (P := P) 2 (yChar a)
  nlinarith

theorem norm_coordF_le (F : ℝ → ZMod P → ℂ) (a : ZMod P) (x : ℝ) : ‖coordF F a x‖ ≤ yNorm 2 (F x) := by
  have h := norm_pairingY_le (P := P) (s := 2) (s' := 2) Real.HolderConjugate.two_two (F x) (yChar a)
  rw [yNorm_two_yChar, mul_one] at h
  exact h

theorem GoodData.coord {F : ℝ → ZMod P → ℂ} (hF : GoodData F) (a : ZMod P) :
    Measurable (coordF F a) ∧ Integrable (coordF F a) volume ∧ ∃ B : ℝ, ∀ x, ‖coordF F a x‖ ≤ B := by
  refine ⟨measurable_coordF hF.meas a, ?_, ?_⟩
  · refine Integrable.mono' hF.int (measurable_coordF hF.meas a).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    exact norm_coordF_le F a x
  · obtain ⟨B, hB⟩ := hF.bdd
    exact ⟨B, fun x => (norm_coordF_le F a x).trans (hB x)⟩

theorem exists_tensorFun_approx {F : ℝ → ZMod P → ℂ} (hF : GoodData F) {p s : ℝ} (hp : 1 ≤ p) (hs : 1 ≤ s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : TS P, eLpNorm (fun x => yNorm s (F x - tensorFun f x)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ε := by
  have hPpos : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
  have hδ : 0 < ε / P := by positivity
  have hex : ∀ a : ZMod P, ∃ ψ : 𝓢(ℝ, ℂ), eLpNorm (fun x => coordF F a x - ψ x) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (ε / P) := by
    intro a
    obtain ⟨hm, hi, B, hB⟩ := hF.coord a
    exact exists_schwartz_approx hp (memLp_of_bdd_integrable' hm hi hB hp) hδ
  choose ψ hψ using hex
  refine ⟨ψ, ?_⟩
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hmeas : ∀ a : ZMod P, Measurable fun x => coordF F a x - ψ a x := fun a =>
    (measurable_coordF hF.meas a).sub (ψ a).continuous.measurable
  have hpt : ∀ x, yNorm s (F x - tensorFun ψ x) ≤ ∑ a, ‖coordF F a x - ψ a x‖ := by
    intro x
    have e : F x - tensorFun ψ x = fun y => ∑ a, (coordF F a x - ψ a x) * yChar a y := by
      ext y
      rw [Pi.sub_apply, eq_sum_coordF F x, tensorFun_eq_sum]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
    rw [e]
    exact yNorm_sum_yChar_le (by linarith) _
  calc eLpNorm (fun x => yNorm s (F x - tensorFun ψ x)) (ENNReal.ofReal p) volume
      ≤ eLpNorm (fun x => ∑ a, ‖coordF F a x - ψ a x‖) (ENNReal.ofReal p) volume := by
        refine eLpNorm_mono ((measurable_yNorm_fun s).comp (hF.meas.sub (measurable_tensorFun ψ))).aestronglyMeasurable (fun x => ?_)
        rw [Real.norm_of_nonneg (yNorm_nonneg' _ _), Real.norm_of_nonneg (Finset.sum_nonneg fun a _ => norm_nonneg _)]
        exact hpt x
    _ ≤ ∑ a, eLpNorm (fun x => ‖coordF F a x - ψ a x‖) (ENNReal.ofReal p) volume := by
        have := eLpNorm_sum_le (μ := volume) (p := ENNReal.ofReal p) (s := (Finset.univ : Finset (ZMod P)))
          (f := fun a x => ‖coordF F a x - ψ a x‖) hp1
        convert this using 2
        ext x
        simp [Finset.sum_apply]
    _ = ∑ a, eLpNorm (fun x => coordF F a x - ψ a x) (ENNReal.ofReal p) volume := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact eLpNorm_norm _ (hmeas a).aestronglyMeasurable
    _ ≤ ∑ a : ZMod P, ENNReal.ofReal (ε / P) := Finset.sum_le_sum fun a _ => hψ a
    _ = ENNReal.ofReal ε := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        field_simp

/-! ### The convolution `tmult σ` on good data -/

/-- `𝓕⁻ σ` is bounded and continuous for an integrable symbol. -/
theorem fourierInv_bdd_cont {σ : ℝ → ℂ} (hint : Integrable σ volume) :
    Continuous (𝓕⁻ σ) ∧ ∃ M : ℝ, ∀ w, ‖𝓕⁻ σ w‖ ≤ M :=
  ⟨continuous_fourierInv_of_integrable' hint, ∫ ξ, ‖σ ξ‖, fun w => by
    rw [Real.fourierInv_eq_fourier_neg]; exact Real.norm_fourier_le_integral_norm σ (-w)⟩

theorem GoodData.integrable_coe {F : ℝ → ZMod P → ℂ} (hF : GoodData F) (y : ZMod P) :
    Integrable (fun z => F z y) volume := by
  refine Integrable.mono' (hF.int.const_mul ((P : ℝ) ^ (2 : ℝ)⁻¹)) ?_ (Eventually.of_forall fun z => ?_)
  · exact ((measurable_pi_apply y).comp hF.meas).aestronglyMeasurable
  · exact norm_apply_le_rpow_mul_yNorm (by norm_num) _ _

theorem GoodData.integrable_kernel_mul {σ : ℝ → ℂ} (hint : Integrable σ volume) {F : ℝ → ZMod P → ℂ}
    (hF : GoodData F) (x : ℝ) (y : ZMod P) : Integrable (fun z => 𝓕⁻ σ (x - z) * F z y) volume := by
  obtain ⟨hc, M, hM⟩ := fourierInv_bdd_cont hint
  exact (hF.integrable_coe y).bdd_mul (c := M)
    (hc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable (Eventually.of_forall fun z => hM _)

theorem tmult_sub_apply {σ : ℝ → ℂ} (hint : Integrable σ volume) {F G : ℝ → ZMod P → ℂ}
    (hF : GoodData F) (hG : GoodData G) (x : ℝ) :
    tmult σ (fun z => F z - G z) x = tmult σ F x - tmult σ G x := by
  ext y
  simp only [tmult, Pi.sub_apply, mul_sub]
  exact integral_sub (hF.integrable_kernel_mul hint x y) (hG.integrable_kernel_mul hint x y)

omit [NeZero P] in
theorem measurable_tmult {σ : ℝ → ℂ} (hint : Integrable σ volume) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) :
    Measurable (tmult σ F) := by
  refine measurable_pi_iff.2 fun y => ?_
  have hc := (fourierInv_bdd_cont hint).1
  have : StronglyMeasurable fun p : ℝ × ℝ => 𝓕⁻ σ (p.1 - p.2) * F p.2 y :=
    (((hc.measurable.comp (measurable_fst.sub measurable_snd)).mul
      (((measurable_pi_apply y).comp hF).comp measurable_snd))).stronglyMeasurable
  exact (this.integral_prod_right' (ν := volume)).measurable

theorem eLpNorm_tmult_le {A : ℝ} (hA : 0 < A) {J : ℕ} {j : ℤ} {σ : ℝ → ℂ} (hσ : IsAdaptedSymbol A J j σ)
    {p s : ℝ} (hp : 1 < p) (hs : 1 ≤ s) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) :
    eLpNorm (fun x => yNorm s (tmult σ F x)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (60 * (2 : ℝ) ^ (2 * J)) *
        ((PrimeCarleson.Proof.Common.maximalHLRConst (ENNReal.ofReal p) : NNReal) : ℝ≥0∞) *
          eLpNorm (fun z => yNorm s (F z)) (ENNReal.ofReal p) volume := by
  have hint : Integrable σ volume := hσ.1.continuous.integrable_of_hasCompactSupport hσ.hasCompactSupport
  have hp0 : 0 < p := by linarith
  set K : ℝ≥0∞ := ENNReal.ofReal (60 * (2 : ℝ) ^ (2 * J)) with hK
  set M : ℝ → ℝ≥0∞ := fun x => PrimeCarleson.Proof.Common.maximalHLR
    (fun z => ENNReal.ofReal (yNorm s (F z))) x with hM
  have hM_m : Measurable M := PrimeCarleson.Proof.Common.measurable_maximalHLR _
  have hmeas : Measurable fun x => yNorm s (tmult σ F x) :=
    (measurable_yNorm_fun s).comp (measurable_tmult hint hF)
  have hpt : ∀ x, ENNReal.ofReal (yNorm s (tmult σ F x)) ≤ K * M x :=
    fun x => ofReal_yNorm_tmult_le_adapted hA hσ hs hF x
  rw [← eLpNorm_ofReal_real p hmeas (fun x => yNorm_nonneg' _ _)]
  rw [eLpNorm_ofReal_eq_lintegral hp0 hmeas.ennreal_ofReal]
  calc (∫⁻ x, ENNReal.ofReal (yNorm s (tmult σ F x)) ^ p) ^ (1 / p)
      ≤ (∫⁻ x, (K * M x) ^ p) ^ (1 / p) := by
        gcongr with x
        exact hpt x
    _ = K * (∫⁻ x, M x ^ p) ^ (1 / p) := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
        rw [mul_one_div_cancel hp0.ne', ENNReal.rpow_one]
    _ = K * eLpNorm M (ENNReal.ofReal p) volume := by
        rw [eLpNorm_ofReal_eq_lintegral hp0 hM_m]
    _ ≤ K * (PrimeCarleson.Proof.Common.maximalHLRConst (ENNReal.ofReal p) *
          eLpNorm (fun z => yNorm s (F z)) (ENNReal.ofReal p) volume) :=
        mul_le_mul' le_rfl (eLpNorm_maximal_yNorm_le hp s hF)
    _ = _ := by rw [mul_assoc]

/-! ### The trilinear integrand -/

theorem measurable_T_apply (T : Form P) {A B C : ℝ → ZMod P → ℂ} (hA : Measurable A) (hB : Measurable B)
    (hC : Measurable C) : Measurable fun x => T (A x) (B x) (C x) := by
  have : (fun x => T (A x) (B x) (C x)) = fun x => ∑ c, ∑ b, ∑ a, T (yChar a) (yChar b) (yChar c) *
      (coordF A a x * (coordF B b x * (starRingEnd ℂ) (coordF C c x))) := by
    ext x
    conv_lhs => rw [eq_sum_coordF A x, eq_sum_coordF B x, eq_sum_coordF C x]
    exact T_expand T _ _ _
  rw [this]
  refine Finset.measurable_sum _ fun c _ => Finset.measurable_sum _ fun b _ => Finset.measurable_sum _ fun a _ => ?_
  exact measurable_const.mul ((measurable_coordF hA a).mul ((measurable_coordF hB b).mul
    (Complex.continuous_conj.measurable.comp (measurable_coordF hC c))))

theorem norm_T_sub_le {u CT : ℝ} {T : Form P} (hT : FormBound u T CT) (a₀ a₁ a₂ a₀' a₁' a₂' : ZMod P → ℂ) :
    ‖T a₀ a₁ a₂ - T a₀' a₁' a₂'‖ ≤
      CT * yNorm 2 (a₀ - a₀') * yNorm 2 a₁ * yNorm u a₂ + CT * yNorm 2 a₀' * yNorm 2 (a₁ - a₁') * yNorm u a₂ +
        CT * yNorm 2 a₀' * yNorm 2 a₁' * yNorm u (a₂ - a₂') := by
  have e : T a₀ a₁ a₂ - T a₀' a₁' a₂' = T (a₀ - a₀') a₁ a₂ + T a₀' (a₁ - a₁') a₂ + T a₀' a₁' (a₂ - a₂') := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  rw [e]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  exact add_le_add (add_le_add (hT _ _ _) (hT _ _ _)) (hT _ _ _)

theorem lintegral_ofReal_mul3_le {CT : ℝ} (hCT : 0 ≤ CT) {p₀ p₁ p₂ : ℝ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁)
    (hp₂ : 0 < p₂) (hsum : 1 / p₀ + 1 / p₁ + 1 / p₂ = 1) {f g h : ℝ → ℝ} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x) :
    ∫⁻ x, ENNReal.ofReal (CT * f x * g x * h x) ≤ ENNReal.ofReal CT *
      (eLpNorm f (ENNReal.ofReal p₀) volume * eLpNorm g (ENNReal.ofReal p₁) volume *
        eLpNorm h (ENNReal.ofReal p₂) volume) := by
  have hpt : ∀ x, ENNReal.ofReal (CT * f x * g x * h x) = ENNReal.ofReal CT *
      (ENNReal.ofReal (f x) * ENNReal.ofReal (g x) * ENNReal.ofReal (h x)) := by
    intro x
    rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCT (hf0 x)) (hg0 x)),
      ENNReal.ofReal_mul (mul_nonneg hCT (hf0 x)), ENNReal.ofReal_mul hCT]
    ring
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine mul_le_mul' le_rfl ((lintegral_mul_three_le hp₀ hp₁ hp₂ hsum hf.ennreal_ofReal hg.ennreal_ofReal
    hh.ennreal_ofReal).trans ?_)
  rw [eLpNorm_ofReal_real p₀ hf hf0, eLpNorm_ofReal_real p₁ hg hg0, eLpNorm_ofReal_real p₂ hh hh0]

theorem lintegral_enorm_T_sub_le {u CT : ℝ} (hu : 0 < u) {T : Form P} (hT : FormBound u T CT)
    {p₀ p₁ p₂ : ℝ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hsum : 1 / p₀ + 1 / p₁ + 1 / p₂ = 1)
    {a₀ a₁ a₂ a₀' a₁' a₂' : ℝ → ZMod P → ℂ} (h0 : Measurable a₀) (h1 : Measurable a₁) (h2 : Measurable a₂)
    (h0' : Measurable a₀') (h1' : Measurable a₁') (h2' : Measurable a₂') :
    ∫⁻ x, ‖T (a₀ x) (a₁ x) (a₂ x) - T (a₀' x) (a₁' x) (a₂' x)‖ₑ ≤
      ENNReal.ofReal CT * (
        mixedENorm p₀ 2 (fun x => a₀ x - a₀' x) * mixedENorm p₁ 2 a₁ * mixedENorm p₂ u a₂ +
        mixedENorm p₀ 2 a₀' * mixedENorm p₁ 2 (fun x => a₁ x - a₁' x) * mixedENorm p₂ u a₂ +
        mixedENorm p₀ 2 a₀' * mixedENorm p₁ 2 a₁' * mixedENorm p₂ u (fun x => a₂ x - a₂' x)) := by
  have hCT : 0 ≤ CT := nonneg_of_formBound hu hT
  have mY : ∀ (s : ℝ) {A : ℝ → ZMod P → ℂ}, Measurable A → Measurable fun x => yNorm s (A x) :=
    fun s A hA => (measurable_yNorm_fun s).comp hA
  set d₀ : ℝ → ZMod P → ℂ := fun x => a₀ x - a₀' x with hd₀
  set d₁ : ℝ → ZMod P → ℂ := fun x => a₁ x - a₁' x with hd₁
  set d₂ : ℝ → ZMod P → ℂ := fun x => a₂ x - a₂' x with hd₂
  have md₀ : Measurable d₀ := h0.sub h0'
  have md₁ : Measurable d₁ := h1.sub h1'
  have md₂ : Measurable d₂ := h2.sub h2'
  have hpt : ∀ x, ‖T (a₀ x) (a₁ x) (a₂ x) - T (a₀' x) (a₁' x) (a₂' x)‖ₑ ≤
      ENNReal.ofReal (CT * yNorm 2 (d₀ x) * yNorm 2 (a₁ x) * yNorm u (a₂ x)) +
      ENNReal.ofReal (CT * yNorm 2 (a₀' x) * yNorm 2 (d₁ x) * yNorm u (a₂ x)) +
      ENNReal.ofReal (CT * yNorm 2 (a₀' x) * yNorm 2 (a₁' x) * yNorm u (d₂ x)) := by
    intro x
    have nn3 : ∀ (s₀ s₁ s₂ : ℝ) (F G H : ZMod P → ℂ), 0 ≤ CT * yNorm s₀ F * yNorm s₁ G * yNorm s₂ H :=
      fun s₀ s₁ s₂ F G H => mul_nonneg (mul_nonneg (mul_nonneg hCT (yNorm_nonneg' _ _)) (yNorm_nonneg' _ _))
        (yNorm_nonneg' _ _)
    rw [← ofReal_norm, ← ENNReal.ofReal_add (nn3 _ _ _ _ _ _) (nn3 _ _ _ _ _ _),
      ← ENNReal.ofReal_add (add_nonneg (nn3 _ _ _ _ _ _) (nn3 _ _ _ _ _ _)) (nn3 _ _ _ _ _ _)]
    exact ENNReal.ofReal_le_ofReal (norm_T_sub_le hT _ _ _ _ _ _)
  have hterm : ∀ (F G H : ℝ → ZMod P → ℂ) (s₀ s₁ s₂ : ℝ), Measurable F → Measurable G → Measurable H →
      Measurable fun x => ENNReal.ofReal (CT * yNorm s₀ (F x) * yNorm s₁ (G x) * yNorm s₂ (H x)) :=
    fun F G H s₀ s₁ s₂ hF hG hH => ENNReal.measurable_ofReal.comp
      (((measurable_const.mul (mY s₀ hF)).mul (mY s₁ hG)).mul (mY s₂ hH))
  calc ∫⁻ x, ‖T (a₀ x) (a₁ x) (a₂ x) - T (a₀' x) (a₁' x) (a₂' x)‖ₑ
      ≤ ∫⁻ x, (ENNReal.ofReal (CT * yNorm 2 (d₀ x) * yNorm 2 (a₁ x) * yNorm u (a₂ x)) +
          ENNReal.ofReal (CT * yNorm 2 (a₀' x) * yNorm 2 (d₁ x) * yNorm u (a₂ x)) +
          ENNReal.ofReal (CT * yNorm 2 (a₀' x) * yNorm 2 (a₁' x) * yNorm u (d₂ x))) := lintegral_mono hpt
    _ = (∫⁻ x, ENNReal.ofReal (CT * yNorm 2 (d₀ x) * yNorm 2 (a₁ x) * yNorm u (a₂ x))) +
          (∫⁻ x, ENNReal.ofReal (CT * yNorm 2 (a₀' x) * yNorm 2 (d₁ x) * yNorm u (a₂ x))) +
          (∫⁻ x, ENNReal.ofReal (CT * yNorm 2 (a₀' x) * yNorm 2 (a₁' x) * yNorm u (d₂ x))) := by
        rw [lintegral_add_right _ (hterm _ _ _ _ _ _ h0' h1' md₂),
          lintegral_add_right _ (hterm _ _ _ _ _ _ h0' md₁ h2)]
    _ ≤ ENNReal.ofReal CT * (mixedENorm p₀ 2 d₀ * mixedENorm p₁ 2 a₁ * mixedENorm p₂ u a₂) +
          ENNReal.ofReal CT * (mixedENorm p₀ 2 a₀' * mixedENorm p₁ 2 d₁ * mixedENorm p₂ u a₂) +
          ENNReal.ofReal CT * (mixedENorm p₀ 2 a₀' * mixedENorm p₁ 2 a₁' * mixedENorm p₂ u d₂) := by
        refine add_le_add (add_le_add ?_ ?_) ?_ <;>
        exact lintegral_ofReal_mul3_le hCT hp₀ hp₁ hp₂ hsum (mY _ ‹_›) (mY _ ‹_›) (mY _ ‹_›)
          (fun x => yNorm_nonneg' _ _) (fun x => yNorm_nonneg' _ _) (fun x => yNorm_nonneg' _ _)
    _ = _ := by ring

/-! ### Finiteness of the slot norms and the multiplier constant -/

theorem yNorm_le_sum_coordF {s : ℝ} (hs : 0 < s) (F : ℝ → ZMod P → ℂ) (x : ℝ) :
    yNorm s (F x) ≤ ∑ a, ‖coordF F a x‖ := by
  have e : F x = fun y => ∑ a, coordF F a x * yChar a y := by
    ext y
    conv_lhs => rw [eq_sum_coordF F x]
    simp [Finset.sum_apply]
  rw [e]
  exact yNorm_sum_yChar_le hs _

theorem GoodData.mixedENorm_lt_top {F : ℝ → ZMod P → ℂ} (hF : GoodData F) {p s : ℝ} (hp : 1 ≤ p) (hs : 1 ≤ s) :
    mixedENorm p s F < ⊤ := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hmeas : Measurable fun x => yNorm s (F x) := (measurable_yNorm_fun s).comp hF.meas
  calc mixedENorm p s F ≤ eLpNorm (fun x => ∑ a, ‖coordF F a x‖) (ENNReal.ofReal p) volume := by
        refine eLpNorm_mono hmeas.aestronglyMeasurable (fun x => ?_)
        rw [Real.norm_of_nonneg (yNorm_nonneg' _ _),
          Real.norm_of_nonneg (Finset.sum_nonneg fun a _ => norm_nonneg _)]
        exact yNorm_le_sum_coordF (by linarith) F x
    _ ≤ ∑ a, eLpNorm (fun x => ‖coordF F a x‖) (ENNReal.ofReal p) volume := by
        have := eLpNorm_sum_le (μ := volume) (p := ENNReal.ofReal p) (s := (Finset.univ : Finset (ZMod P)))
          (f := fun a x => ‖coordF F a x‖) hp1
        convert this using 2
        ext x
        simp [Finset.sum_apply]
    _ < ⊤ := by
        refine ENNReal.sum_lt_top.2 fun a _ => ?_
        obtain ⟨hm, hi, B, hB⟩ := hF.coord a
        rw [eLpNorm_norm _ hm.aestronglyMeasurable]
        exact memLp_of_bdd_integrable' hm hi hB hp

/-- The constant of the single-scale bound at exponent `p`. -/
def kappa (J : ℕ) (p : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (60 * (2 : ℝ) ^ (2 * J)) *
    ((PrimeCarleson.Proof.Common.maximalHLRConst (ENNReal.ofReal p) : NNReal) : ℝ≥0∞)

theorem kappa_ne_top (J : ℕ) (p : ℝ) : kappa J p ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top

theorem mixedENorm_tmult_le {A : ℝ} (hA : 0 < A) {J : ℕ} {j : ℤ} {σ : ℝ → ℂ} (hσ : IsAdaptedSymbol A J j σ)
    {p s : ℝ} (hp : 1 < p) (hs : 1 ≤ s) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) :
    mixedENorm p s (tmult σ F) ≤ kappa J p * mixedENorm p s F :=
  eLpNorm_tmult_le hA hσ hp hs hF

/-! ### One scale: integrability and the difference estimate -/

theorem integrable_of_adapted {A : ℝ} (hA : 0 < A) {J : ℕ} {j : ℤ} {u CT : ℝ} (hu : 1 < u) {T : Form P}
    (hT : FormBound u T CT) {p₀ p₁ p₂ : ℝ} (hp₀ : 1 < p₀) (hp₁ : 1 < p₁) (hp₂ : 1 < p₂)
    (hsum : 1 / p₀ + 1 / p₁ + 1 / p₂ = 1) {σ₀ σ₁ σ₂ : ℝ → ℂ} (h₀ : IsAdaptedSymbol A J j σ₀)
    (h₁ : IsAdaptedSymbol A J j σ₁) (h₂ : IsAdaptedSymbol A J j σ₂) {g₀ g₁ g₂ : ℝ → ZMod P → ℂ}
    (hg₀ : GoodData g₀) (hg₁ : GoodData g₁) (hg₂ : GoodData g₂) :
    Integrable (fun x => T (tmult σ₀ g₀ x) (tmult σ₁ g₁ x) (tmult σ₂ g₂ x)) volume := by
  have hCT : 0 ≤ CT := nonneg_of_formBound (by linarith) hT
  have i₀ : Integrable σ₀ volume := h₀.1.continuous.integrable_of_hasCompactSupport h₀.hasCompactSupport
  have i₁ : Integrable σ₁ volume := h₁.1.continuous.integrable_of_hasCompactSupport h₁.hasCompactSupport
  have i₂ : Integrable σ₂ volume := h₂.1.continuous.integrable_of_hasCompactSupport h₂.hasCompactSupport
  have m₀ := measurable_tmult i₀ hg₀.meas
  have m₁ := measurable_tmult i₁ hg₁.meas
  have m₂ := measurable_tmult i₂ hg₂.meas
  refine ⟨(measurable_T_apply T m₀ m₁ m₂).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have mY : ∀ (s : ℝ) {B : ℝ → ZMod P → ℂ}, Measurable B → Measurable fun x => yNorm s (B x) :=
    fun s B hB => (measurable_yNorm_fun s).comp hB
  calc ∫⁻ x, ‖T (tmult σ₀ g₀ x) (tmult σ₁ g₁ x) (tmult σ₂ g₂ x)‖ₑ
      ≤ ∫⁻ x, ENNReal.ofReal (CT * yNorm 2 (tmult σ₀ g₀ x) * yNorm 2 (tmult σ₁ g₁ x) *
          yNorm u (tmult σ₂ g₂ x)) := by
        refine lintegral_mono fun x => ?_
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hT _ _ _)
    _ ≤ ENNReal.ofReal CT * (mixedENorm p₀ 2 (tmult σ₀ g₀) * mixedENorm p₁ 2 (tmult σ₁ g₁) *
          mixedENorm p₂ u (tmult σ₂ g₂)) :=
        lintegral_ofReal_mul3_le hCT (by linarith) (by linarith) (by linarith) hsum (mY 2 m₀) (mY 2 m₁)
          (mY u m₂) (fun x => yNorm_nonneg' _ _) (fun x => yNorm_nonneg' _ _) (fun x => yNorm_nonneg' _ _)
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ ?_) ?_)
        · exact (mixedENorm_tmult_le hA h₀ hp₀ (by norm_num) hg₀.meas).trans_lt
            (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (kappa_ne_top _ _)) (hg₀.mixedENorm_lt_top hp₀.le (by norm_num)))
        · exact (mixedENorm_tmult_le hA h₁ hp₁ (by norm_num) hg₁.meas).trans_lt
            (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (kappa_ne_top _ _)) (hg₁.mixedENorm_lt_top hp₁.le (by norm_num)))
        · exact (mixedENorm_tmult_le hA h₂ hp₂ hu.le hg₂.meas).trans_lt
            (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (kappa_ne_top _ _)) (hg₂.mixedENorm_lt_top hp₂.le hu.le))

theorem enorm_integral_sub_le {A : ℝ} (hA : 0 < A) {J : ℕ} {j : ℤ} {u CT : ℝ} (hu : 1 < u) {T : Form P}
    (hT : FormBound u T CT) {p₀ p₁ p₂ : ℝ} (hp₀ : 1 < p₀) (hp₁ : 1 < p₁) (hp₂ : 1 < p₂)
    (hsum : 1 / p₀ + 1 / p₁ + 1 / p₂ = 1) {σ₀ σ₁ σ₂ : ℝ → ℂ} (h₀ : IsAdaptedSymbol A J j σ₀)
    (h₁ : IsAdaptedSymbol A J j σ₁) (h₂ : IsAdaptedSymbol A J j σ₂) {g₀ g₁ g₂ : ℝ → ZMod P → ℂ}
    (hg₀ : GoodData g₀) (hg₁ : GoodData g₁) (hg₂ : GoodData g₂) (f₀ f₁ f₂ : TS P) :
    ‖(∫ x, T (tmult σ₀ g₀ x) (tmult σ₁ g₁ x) (tmult σ₂ g₂ x)) -
        ∫ x, T (tmult σ₀ (tensorFun f₀) x) (tmult σ₁ (tensorFun f₁) x) (tmult σ₂ (tensorFun f₂) x)‖ₑ ≤
      ENNReal.ofReal CT * (
        kappa J p₀ * mixedENorm p₀ 2 (fun x => g₀ x - tensorFun f₀ x) *
          (kappa J p₁ * mixedENorm p₁ 2 g₁) * (kappa J p₂ * mixedENorm p₂ u g₂) +
        kappa J p₀ * mixedENorm p₀ 2 (tensorFun f₀) *
          (kappa J p₁ * mixedENorm p₁ 2 (fun x => g₁ x - tensorFun f₁ x)) * (kappa J p₂ * mixedENorm p₂ u g₂) +
        kappa J p₀ * mixedENorm p₀ 2 (tensorFun f₀) * (kappa J p₁ * mixedENorm p₁ 2 (tensorFun f₁)) *
          (kappa J p₂ * mixedENorm p₂ u (fun x => g₂ x - tensorFun f₂ x))) := by
  have hCT : 0 ≤ CT := nonneg_of_formBound (by linarith) hT
  have i₀ : Integrable σ₀ volume := h₀.1.continuous.integrable_of_hasCompactSupport h₀.hasCompactSupport
  have i₁ : Integrable σ₁ volume := h₁.1.continuous.integrable_of_hasCompactSupport h₁.hasCompactSupport
  have i₂ : Integrable σ₂ volume := h₂.1.continuous.integrable_of_hasCompactSupport h₂.hasCompactSupport
  have G₀ := GoodData.tensorFun f₀
  have G₁ := GoodData.tensorFun f₁
  have G₂ := GoodData.tensorFun f₂
  have hI := integrable_of_adapted hA hu hT hp₀ hp₁ hp₂ hsum h₀ h₁ h₂ hg₀ hg₁ hg₂
  have hI' := integrable_of_adapted hA hu hT hp₀ hp₁ hp₂ hsum h₀ h₁ h₂ G₀ G₁ G₂
  rw [← integral_sub hI hI']
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have e₀ : (fun x => tmult σ₀ g₀ x - tmult σ₀ (tensorFun f₀) x) =
      tmult σ₀ (fun z => g₀ z - tensorFun f₀ z) := funext fun x => (tmult_sub_apply i₀ hg₀ G₀ x).symm
  have e₁ : (fun x => tmult σ₁ g₁ x - tmult σ₁ (tensorFun f₁) x) =
      tmult σ₁ (fun z => g₁ z - tensorFun f₁ z) := funext fun x => (tmult_sub_apply i₁ hg₁ G₁ x).symm
  have e₂ : (fun x => tmult σ₂ g₂ x - tmult σ₂ (tensorFun f₂) x) =
      tmult σ₂ (fun z => g₂ z - tensorFun f₂ z) := funext fun x => (tmult_sub_apply i₂ hg₂ G₂ x).symm
  have E3 := lintegral_enorm_T_sub_le (by linarith) hT (by linarith : 0 < p₀) (by linarith : 0 < p₁)
    (by linarith : 0 < p₂) hsum (measurable_tmult i₀ hg₀.meas) (measurable_tmult i₁ hg₁.meas)
    (measurable_tmult i₂ hg₂.meas) (measurable_tmult i₀ G₀.meas) (measurable_tmult i₁ G₁.meas)
    (measurable_tmult i₂ G₂.meas)
  rw [e₀, e₁, e₂] at E3
  refine E3.trans ?_
  have d₀ := mixedENorm_tmult_le hA h₀ hp₀ (by norm_num : (1 : ℝ) ≤ 2) (hg₀.sub G₀).meas
  have d₁ := mixedENorm_tmult_le hA h₁ hp₁ (by norm_num : (1 : ℝ) ≤ 2) (hg₁.sub G₁).meas
  have d₂ := mixedENorm_tmult_le hA h₂ hp₂ hu.le (hg₂.sub G₂).meas
  have n₁ := mixedENorm_tmult_le hA h₁ hp₁ (by norm_num : (1 : ℝ) ≤ 2) hg₁.meas
  have n₂ := mixedENorm_tmult_le hA h₂ hp₂ hu.le hg₂.meas
  have n₀' := mixedENorm_tmult_le hA h₀ hp₀ (by norm_num : (1 : ℝ) ≤ 2) G₀.meas
  have n₁' := mixedENorm_tmult_le hA h₁ hp₁ (by norm_num : (1 : ℝ) ≤ 2) G₁.meas
  refine mul_le_mul' le_rfl ?_
  refine add_le_add (add_le_add ?_ ?_) ?_
  · exact mul_le_mul' (mul_le_mul' d₀ n₁) n₂
  · exact mul_le_mul' (mul_le_mul' n₀' d₁) n₂
  · exact mul_le_mul' (mul_le_mul' n₀' n₁') d₂

theorem mixedENorm_le_add {F G : ℝ → ZMod P → ℂ} (hF : Measurable F) (hG : Measurable G) {p s : ℝ}
    (hp : 1 ≤ p) (hs : 1 ≤ s) :
    mixedENorm p s G ≤ mixedENorm p s F + mixedENorm p s (fun x => F x - G x) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have mF : Measurable fun x => yNorm s (F x) := (measurable_yNorm_fun s).comp hF
  have mD : Measurable fun x => yNorm s (F x - G x) := (measurable_yNorm_fun s).comp (hF.sub hG)
  have mG : Measurable fun x => yNorm s (G x) := (measurable_yNorm_fun s).comp hG
  calc mixedENorm p s G ≤ eLpNorm (fun x => yNorm s (F x) + yNorm s (F x - G x)) (ENNReal.ofReal p) volume := by
        refine eLpNorm_mono mG.aestronglyMeasurable (fun x => ?_)
        rw [Real.norm_of_nonneg (yNorm_nonneg' _ _),
          Real.norm_of_nonneg (add_nonneg (yNorm_nonneg' _ _) (yNorm_nonneg' _ _))]
        have := yNorm_sub_le hs (F x) (F x - G x)
        rwa [sub_sub_cancel] at this
    _ ≤ mixedENorm p s F + mixedENorm p s (fun x => F x - G x) :=
        eLpNorm_add_le (f := fun x => yNorm s (F x)) (g := fun x => yNorm s (F x - G x)) hp1

end Good

theorem poly3 (a b c e : ℝ≥0∞) (he : e ≤ 1) :
    (a + e) * (b + e) * (c + e) ≤ a * b * c + e * ((a + 1) * (b + 1) * (c + 1)) := by
  have h2 : e * e ≤ e := by
    calc e * e ≤ 1 * e := mul_le_mul' he le_rfl
      _ = e := one_mul e
  have h3 : e * e * e ≤ e * 1 := by
    calc e * e * e ≤ e * e * 1 := mul_le_mul' le_rfl he
      _ = e * e := mul_one _
      _ ≤ e := h2
      _ = e * 1 := (mul_one e).symm
  have hx : (e * e) * (a + b + c) ≤ e * (a + b + c) := mul_le_mul' h2 le_rfl
  have e1 : (a + e) * (b + e) * (c + e) =
      a * b * c + (e * (a * b + a * c + b * c) + (e * e) * (a + b + c) + e * e * e) := by ring
  have e2 : a * b * c + e * ((a + 1) * (b + 1) * (c + 1)) =
      a * b * c + (e * (a * b * c) + e * (a * b + a * c + b * c) + e * (a + b + c) + e * 1) := by ring
  rw [e1, e2]
  refine add_le_add le_rfl ?_
  have hX : e * (a * b + a * c + b * c) ≤ e * (a * b * c) + e * (a * b + a * c + b * c) := le_add_self
  calc e * (a * b + a * c + b * c) + (e * e) * (a + b + c) + e * e * e
      ≤ (e * (a * b * c) + e * (a * b + a * c + b * c)) + e * (a + b + c) + e * 1 :=
        add_le_add (add_le_add hX hx) h3
    _ = _ := by ring

theorem le_of_seq {X R Λ : ℝ≥0∞} (hΛ : Λ ≠ ⊤) {e : ℕ → ℝ≥0∞} (he : Tendsto e atTop (𝓝 0))
    (h : ∀ n, X ≤ R + e n * Λ) : X ≤ R := by
  have : Tendsto (fun n => R + e n * Λ) atTop (𝓝 (R + 0 * Λ)) :=
    tendsto_const_nhds.add (ENNReal.Tendsto.mul_const he (Or.inr hΛ))
  simp only [zero_mul, add_zero] at this
  exact ge_of_tendsto' this h

theorem bracket_le (c κ₀ κ₁ κ₂ n₀ n₁ n₂ d₀ d₁ d₂ a₀' a₁' e : ℝ≥0∞) (hd₀ : d₀ ≤ e) (hd₁ : d₁ ≤ e)
    (hd₂ : d₂ ≤ e) (ha₀ : a₀' ≤ n₀ + 1) (ha₁ : a₁' ≤ n₁ + 1) :
    c * (κ₀ * d₀ * (κ₁ * n₁) * (κ₂ * n₂) + κ₀ * a₀' * (κ₁ * d₁) * (κ₂ * n₂) +
        κ₀ * a₀' * (κ₁ * a₁') * (κ₂ * d₂)) ≤
      e * (c * κ₀ * κ₁ * κ₂ * (n₁ * n₂ + (n₀ + 1) * n₂ + (n₀ + 1) * (n₁ + 1))) := by
  calc _ ≤ c * (κ₀ * e * (κ₁ * n₁) * (κ₂ * n₂) + κ₀ * (n₀ + 1) * (κ₁ * e) * (κ₂ * n₂) +
        κ₀ * (n₀ + 1) * (κ₁ * (n₁ + 1)) * (κ₂ * e)) := by gcongr
    _ = _ := by ring

/-! ## The theorem for the data class of the draft -/

/-- **V14 (PI) for the data class of the draft** (`drafts/x2-interface/05-V13-V15-Tree.lean.txt`): `g_k`
measurable with `yNorm 2 (g_k x)` bounded and integrable; symbols anchored at `A > 0`, `C` uniform in
`A, P, T, js, ε`.  The right side is the product of the mixed norms `‖g_k‖_{L^{p_k}(ℝ; L^{s_k}(Y_P))}`,
`s = (2, 2, u)` (`= ∏ k, eLpNorm (yNorm (slotExp u k) ∘ g k) (p k)` of the draft). -/
theorem paraproduct (J a₀ : ℕ) (hJ : 1 ≤ J) (ha₀ : 3 ≤ a₀) {u : ℝ} (hu : 1 < u) {p : Fin 3 → ℝ}
    (hp : ∀ k, 1 < p k) (hpsum : ∑ k, 1 / p k = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 < A → ∀ (P : ℕ) [NeZero P] (T : Form P) (CT : ℝ), FormBound u T CT →
      ∀ (js : Finset ℤ) (ε : ℤ → ℂ), (∀ j, ‖ε j‖ ≤ 1) →
      ∀ (σ₁ σ₂ σ₃ : ℤ → ℝ → ℂ), (∀ j, IsLowSymbol A J a₀ j (σ₁ j)) → (∀ j, IsLPSymbol A J a₀ j (σ₂ j)) →
        (∀ j, IsLPSymbol A J a₀ j (σ₃ j)) →
      ∀ g : Fin 3 → ℝ → ZMod P → ℂ, (∀ k, Measurable (g k)) →
        (∀ k, ∃ B, ∀ x, yNorm 2 (g k x) ≤ B) → (∀ k, Integrable (fun x => yNorm 2 (g k x)) volume) →
          ‖∑ j ∈ js, ε j * ∫ x, T (tmult (σ₁ j) (g 0) x) (tmult (σ₂ j) (g 1) x) (tmult (σ₃ j) (g 2) x)‖ₑ ≤
            ENNReal.ofReal (C * CT) * (mixedENorm (p 0) 2 (g 0) * mixedENorm (p 1) 2 (g 1) *
              mixedENorm (p 2) u (g 2)) := by
  obtain ⟨C, hC0, hC⟩ := paraproduct_schwartz J a₀ hJ ha₀ hu hp hpsum
  refine ⟨C, hC0, ?_⟩
  intro A hA P _ T CT hT js ε hε σ₁ σ₂ σ₃ h1 h2 h3 g hm hb hi
  have hsum : 1 / p 0 + 1 / p 1 + 1 / p 2 = 1 := by simpa [Fin.sum_univ_three] using hpsum
  have hg : ∀ k, GoodData (g k) := fun k => ⟨hm k, hb k, hi k⟩
  have hCT : 0 ≤ CT := nonneg_of_formBound (by linarith) hT
  have ha₀2 : 2 ≤ a₀ := by omega
  have a1 : ∀ j, IsAdaptedSymbol A J j (σ₁ j) := fun j => (h1 j).adapted hA ha₀2
  have a2 : ∀ j, IsAdaptedSymbol A J j (σ₂ j) := fun j => (h2 j).adapted ha₀2
  have a3 : ∀ j, IsAdaptedSymbol A J j (σ₃ j) := fun j => (h3 j).adapted ha₀2
  set n0 := mixedENorm (p 0) 2 (g 0) with hn0
  set n1 := mixedENorm (p 1) 2 (g 1) with hn1
  set n2 := mixedENorm (p 2) u (g 2) with hn2
  have n0t : n0 ≠ ⊤ := (hg 0).mixedENorm_lt_top (hp 0).le (by norm_num) |>.ne
  have n1t : n1 ≠ ⊤ := (hg 1).mixedENorm_lt_top (hp 1).le (by norm_num) |>.ne
  have n2t : n2 ≠ ⊤ := (hg 2).mixedENorm_lt_top (hp 2).le hu.le |>.ne
  have hex : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose f0 hf0 using fun n : ℕ =>
    exists_tensorFun_approx (hg 0) (hp 0).le (by norm_num : (1 : ℝ) ≤ 2) (hex n)
  choose f1 hf1 using fun n : ℕ =>
    exists_tensorFun_approx (hg 1) (hp 1).le (by norm_num : (1 : ℝ) ≤ 2) (hex n)
  choose f2 hf2 using fun n : ℕ => exists_tensorFun_approx (hg 2) (hp 2).le hu.le (hex n)
  set e : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / ((n : ℝ) + 1)) with he
  have he1 : ∀ n, e n ≤ 1 := fun n => by
    simp only [he]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have he0 : Tendsto e atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa [he] using this
  set κ₀ := kappa J (p 0)
  set κ₁ := kappa J (p 1)
  set κ₂ := kappa J (p 2)
  set Λ₂ : ℝ≥0∞ := (js.card : ℝ≥0∞) * (ENNReal.ofReal CT * κ₀ * κ₁ * κ₂ *
    (n1 * n2 + (n0 + 1) * n2 + (n0 + 1) * (n1 + 1))) with hΛ₂
  set Λ : ℝ≥0∞ := ENNReal.ofReal (C * CT) * ((n0 + 1) * (n1 + 1) * (n2 + 1)) + Λ₂ with hΛ
  have hΛt : Λ ≠ ⊤ := by
    have k0 := kappa_ne_top J (p 0)
    have k1 := kappa_ne_top J (p 1)
    have k2 := kappa_ne_top J (p 2)
    simp only [hΛ, hΛ₂]
    refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_, ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top _) ?_⟩
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨n0t, ENNReal.one_ne_top⟩)
        (ENNReal.add_ne_top.2 ⟨n1t, ENNReal.one_ne_top⟩)) (ENNReal.add_ne_top.2 ⟨n2t, ENNReal.one_ne_top⟩)
    · refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top k0) k1) k2) ?_
      refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top n1t n2t,
        ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨n0t, ENNReal.one_ne_top⟩) n2t⟩,
        ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨n0t, ENNReal.one_ne_top⟩)
          (ENNReal.add_ne_top.2 ⟨n1t, ENNReal.one_ne_top⟩)⟩
  set LHS : ℂ := ∑ j ∈ js, ε j * ∫ x, T (tmult (σ₁ j) (g 0) x) (tmult (σ₂ j) (g 1) x)
    (tmult (σ₃ j) (g 2) x) with hLHS
  refine le_of_seq (X := ‖LHS‖ₑ) (Λ := Λ) hΛt he0 fun n => ?_
  have G0 := GoodData.tensorFun (f0 n)
  have G1 := GoodData.tensorFun (f1 n)
  have G2 := GoodData.tensorFun (f2 n)
  have d0 : mixedENorm (p 0) 2 (fun x => g 0 x - tensorFun (f0 n) x) ≤ e n := hf0 n
  have d1 : mixedENorm (p 1) 2 (fun x => g 1 x - tensorFun (f1 n) x) ≤ e n := hf1 n
  have d2 : mixedENorm (p 2) u (fun x => g 2 x - tensorFun (f2 n) x) ≤ e n := hf2 n
  have b0 : mixedENorm (p 0) 2 (tensorFun (f0 n)) ≤ n0 + e n :=
    (mixedENorm_le_add (hg 0).meas G0.meas (hp 0).le (by norm_num)).trans (add_le_add le_rfl d0)
  have b1 : mixedENorm (p 1) 2 (tensorFun (f1 n)) ≤ n1 + e n :=
    (mixedENorm_le_add (hg 1).meas G1.meas (hp 1).le (by norm_num)).trans (add_le_add le_rfl d1)
  have b2 : mixedENorm (p 2) u (tensorFun (f2 n)) ≤ n2 + e n :=
    (mixedENorm_le_add (hg 2).meas G2.meas (hp 2).le hu.le).trans (add_le_add le_rfl d2)
  have c0 : mixedENorm (p 0) 2 (tensorFun (f0 n)) ≤ n0 + 1 := b0.trans (add_le_add le_rfl (he1 n))
  have c1 : mixedENorm (p 1) 2 (tensorFun (f1 n)) ≤ n1 + 1 := b1.trans (add_le_add le_rfl (he1 n))
  -- the Schwartz bound
  have hS := hC A hA P T CT hT js ε hε σ₁ σ₂ σ₃ h1 h2 h3 ![f0 n, f1 n, f2 n]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hS
  set LHSn : ℂ := ∑ j ∈ js, ε j * ∫ x, T (tmult (σ₁ j) (tensorFun (f0 n)) x)
    (tmult (σ₂ j) (tensorFun (f1 n)) x) (tmult (σ₃ j) (tensorFun (f2 n)) x) with hLHSn
  -- the difference
  have hdiff : ‖LHS - LHSn‖ₑ ≤ e n * Λ₂ := by
    have e1 : LHS - LHSn = ∑ j ∈ js, ε j * ((∫ x, T (tmult (σ₁ j) (g 0) x) (tmult (σ₂ j) (g 1) x)
        (tmult (σ₃ j) (g 2) x)) - ∫ x, T (tmult (σ₁ j) (tensorFun (f0 n)) x)
        (tmult (σ₂ j) (tensorFun (f1 n)) x) (tmult (σ₃ j) (tensorFun (f2 n)) x)) := by
      rw [hLHS, hLHSn, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => (mul_sub _ _ _).symm
    rw [e1]
    refine (enorm_sum_le _ _).trans ?_
    calc ∑ j ∈ js, ‖ε j * ((∫ x, T (tmult (σ₁ j) (g 0) x) (tmult (σ₂ j) (g 1) x) (tmult (σ₃ j) (g 2) x)) -
          ∫ x, T (tmult (σ₁ j) (tensorFun (f0 n)) x) (tmult (σ₂ j) (tensorFun (f1 n)) x)
            (tmult (σ₃ j) (tensorFun (f2 n)) x))‖ₑ
        ≤ ∑ j ∈ js, e n * (ENNReal.ofReal CT * κ₀ * κ₁ * κ₂ *
            (n1 * n2 + (n0 + 1) * n2 + (n0 + 1) * (n1 + 1))) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [enorm_mul]
          refine le_trans (mul_le_of_le_one_left zero_le
            (by rw [← ofReal_norm]; exact ENNReal.ofReal_le_one.2 (hε j))) ?_
          refine (enorm_integral_sub_le hA hu hT (hp 0) (hp 1) (hp 2) hsum (a1 j) (a2 j) (a3 j)
            (hg 0) (hg 1) (hg 2) (f0 n) (f1 n) (f2 n)).trans ?_
          exact bracket_le _ _ _ _ _ _ _ _ _ _ _ _ _ d0 d1 d2 c0 c1
      _ = e n * Λ₂ := by
          rw [Finset.sum_const, nsmul_eq_mul, hΛ₂]; ring
  -- the combination
  have hmain : ‖LHSn‖ₑ ≤ ENNReal.ofReal (C * CT) * (n0 * n1 * n2) +
      e n * (ENNReal.ofReal (C * CT) * ((n0 + 1) * (n1 + 1) * (n2 + 1))) := by
    refine hS.trans ?_
    calc ENNReal.ofReal (C * CT) * (mixedENorm (p 0) 2 (tensorFun (f0 n)) *
          mixedENorm (p 1) 2 (tensorFun (f1 n)) * mixedENorm (p 2) u (tensorFun (f2 n)))
        ≤ ENNReal.ofReal (C * CT) * ((n0 + e n) * (n1 + e n) * (n2 + e n)) := by gcongr
      _ ≤ ENNReal.ofReal (C * CT) * (n0 * n1 * n2 + e n * ((n0 + 1) * (n1 + 1) * (n2 + 1))) :=
          mul_le_mul' le_rfl (poly3 _ _ _ _ (he1 n))
      _ = _ := by ring
  calc ‖LHS‖ₑ = ‖LHSn + (LHS - LHSn)‖ₑ := by rw [add_sub_cancel]
    _ ≤ ‖LHSn‖ₑ + ‖LHS - LHSn‖ₑ := enorm_add_le _ _
    _ ≤ (ENNReal.ofReal (C * CT) * (n0 * n1 * n2) +
          e n * (ENNReal.ofReal (C * CT) * ((n0 + 1) * (n1 + 1) * (n2 + 1)))) + e n * Λ₂ :=
        add_le_add hmain hdiff
    _ = ENNReal.ofReal (C * CT) * (n0 * n1 * n2) + e n * Λ := by rw [hΛ]; ring

end PrimeBHT.TimeFrequency.X2
