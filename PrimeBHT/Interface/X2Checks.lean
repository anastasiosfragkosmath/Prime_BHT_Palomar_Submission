module

public import PrimeBHT.Frozen.YNorm
public import PrimeBHT.Frozen.TensorFun
public import PrimeBHT.Frozen.TensorFourier
public import PrimeBHT.Frozen.MultiplierForm

/-!
# Sanity checks for the frozen X2 statement (`t_finiteBV` and its four definitions)

Migrated from section 3 of the pre-freeze candidate draft `drafts/X2Statement.lean.txt`, over the
FROZEN definitions `PrimeBHT.Statements.{yNorm, tensorFun, tensorFourier, multiplierForm}` (ruling R11).
Everything here is fully proved. It does NOT mention the frozen theorem `t_finiteBV` (quarantine of the
`DRAFT_SORRY` anchor); the statement as a `Prop` is `PrimeBHT.TransferenceAssembly.X2Statement`, and
`scripts/interface_check.sh` checks it is literally the type of the frozen theorem.

Contents:
* (i) the case `P = 1`: the norms and the form reduce to the scalar ones;
* (ii) the hypotheses of `t_finiteBV` are satisfiable (constant and sign multipliers, scalar form);
* (iii) `Λ_m^Π` is a genuine absolutely convergent integral (the first conjunct of the statement);
* (iv) the three mixed norms of a tensor Schwartz function are finite (the right side is a number);
* (v) the `CT`-hypothesis is exactly "`CT` bounds the operator norm of `Π`", and `CT ≥ 0`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate ContDiff
open PrimeBHT.Statements (yNorm tensorFun tensorFourier multiplierForm)

set_option autoImplicit false

namespace PrimeBHT.Interface.X2

open Complex in
/-- `e(A y / P)` is `ZMod.stdAddChar` of the integer representative: for an integer `a`,
`ZMod.stdAddChar (a : ZMod P) = exp (2π i a / P)`, i.e. `e(a/P)` (line 314: `e(t) = e^{2π i t}`). -/
theorem stdAddChar_intCast {P : ℕ} [NeZero P] (a : ℤ) :
    (ZMod.stdAddChar (a : ZMod P) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * a / P) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_intCast]

/-! ### (i) The case `P = 1`: the norms and the form reduce to the scalar ones -/

/-- For `P = 1` the normalized `L^s(Y_1)` norm is `|F 0|` (`s > 0`). -/
theorem yNorm_one {s : ℝ} (hs : 0 < s) (F : ZMod 1 → ℂ) : yNorm s F = ‖F 0‖ := by
  unfold yNorm
  rw [Fintype.sum_subsingleton _ (0 : ZMod 1)]
  simp [Real.rpow_rpow_inv (norm_nonneg _) hs.ne']

/-- For `P = 1`: `F(x; y) = f_0(x)`. -/
theorem tensorFun_one (f : ZMod 1 → 𝓢(ℝ, ℂ)) (x : ℝ) (y : ZMod 1) :
    tensorFun f x y = f 0 x := by
  unfold tensorFun
  rw [Fintype.sum_subsingleton _ (0 : ZMod 1)]
  simp

/-- For `P = 1`: `F̂(ξ; y) = f̂_0(ξ)`. -/
theorem tensorFourier_one (f : ZMod 1 → 𝓢(ℝ, ℂ)) (ξ : ℝ) (y : ZMod 1) :
    tensorFourier f ξ y = 𝓕 (⇑(f 0)) ξ := by
  unfold tensorFourier
  rw [Fintype.sum_subsingleton _ (0 : ZMod 1)]
  simp

/-- The scalar trilinear form `Π(F, G, H) = F(0) G(0) conj(H(0))` on `(ℤ/1 → ℂ)³`
(complex-linear, complex-linear, conjugate-linear): the case `P = 1`, `Π` = the scalar product. -/
def scalarForm : (ZMod 1 → ℂ) →ₗ[ℂ] (ZMod 1 → ℂ) →ₗ[ℂ] (ZMod 1 → ℂ) →ₗ⋆[ℂ] ℂ where
  toFun F :=
    { toFun := fun G =>
        { toFun := fun H => F 0 * G 0 * conj (H 0)
          map_add' := fun H H' => by simp [mul_add]
          map_smul' := fun c H => by simp [mul_left_comm] }
      map_add' := fun G G' => by ext H; simp [add_mul, mul_add]
      map_smul' := fun c G => by ext H; simp; ring }
  map_add' := fun F F' => by ext G H; simp [add_mul]
  map_smul' := fun c F => by ext G H; simp; ring

theorem scalarForm_apply (F G H : ZMod 1 → ℂ) : scalarForm F G H = F 0 * G 0 * conj (H 0) := rfl

/-- `‖Π‖ = 1` for the scalar form: equality `|Π(F,G,H)| = ‖F‖_{L²} ‖G‖_{L²} ‖H‖_{L^u}`, every `u > 0`. -/
theorem norm_scalarForm {u : ℝ} (hu : 0 < u) (F G H : ZMod 1 → ℂ) :
    ‖scalarForm F G H‖ = 1 * yNorm 2 F * yNorm 2 G * yNorm u H := by
  rw [yNorm_one two_pos, yNorm_one two_pos, yNorm_one hu, scalarForm_apply]
  simp

/-- For `P = 1` the form `Λ_m^Π` with the scalar `Π` is the scalar trilinear Fourier form
`∫∫ m(ξ₂ - ξ₁) f̂₁(ξ₁) f̂₂(ξ₂) conj(f̂₃(ξ₁ + ξ₂)) dξ₁ dξ₂` (the bilinear-Hilbert-transform form
for `m = sign`). -/
theorem multiplierForm_one (m : ℝ → ℂ) (f₁ f₂ f₃ : ZMod 1 → 𝓢(ℝ, ℂ)) :
    multiplierForm m scalarForm f₁ f₂ f₃ =
      ∫ ξ : ℝ × ℝ, m (ξ.2 - ξ.1) *
        (𝓕 (⇑(f₁ 0)) ξ.1 * 𝓕 (⇑(f₂ 0)) ξ.2 * conj (𝓕 (⇑(f₃ 0)) (ξ.1 + ξ.2))) := by
  unfold multiplierForm
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [scalarForm_apply, tensorFourier_one]

/-! ### (ii) The hypotheses of `t_finiteBV` are satisfiable -/

/-- The constant multiplier `m = 1` satisfies the all-multi-index decay with `A_0 = 1`, `A_j = 0`
(`j ≥ 1`). -/
theorem const_multiplier_decay :
    ContDiffOn ℝ ∞ (fun _ : ℝ => (1 : ℂ)) {0}ᶜ ∧
    ∀ j : ℕ, ∀ t : ℝ, t ≠ 0 →
      |t| ^ j * ‖iteratedDeriv j (fun _ : ℝ => (1 : ℂ)) t‖ ≤ (if j = 0 then 1 else 0 : ℝ) := by
  refine ⟨contDiffOn_const, fun j t _ => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · simp [iteratedDeriv_const, hj.ne']

/-- The bilinear-Hilbert-transform symbol `m(t) = sign(t)` (value `-1` at `t = 0`, irrelevant: a null
set) is smooth on `ℝ ∖ {0}` and satisfies the all-multi-index decay with `A_0 = 1`, `A_j = 0`
(`j ≥ 1`) although it is discontinuous at `0`: the hypotheses of `t_finiteBV` are satisfied by
a genuinely singular symbol, and `m` need only be smooth away from `0`. -/
theorem sign_multiplier_decay :
    ContDiffOn ℝ ∞ (fun t : ℝ => if 0 < t then (1 : ℂ) else -1) {0}ᶜ ∧
    ∀ j : ℕ, ∀ t : ℝ, t ≠ 0 →
      |t| ^ j * ‖iteratedDeriv j (fun t : ℝ => if 0 < t then (1 : ℂ) else -1) t‖ ≤
        (if j = 0 then 1 else 0 : ℝ) := by
  set m : ℝ → ℂ := fun t => if 0 < t then 1 else -1 with hm
  have hloc : ∀ t : ℝ, t ≠ 0 → ∃ c : ℂ, ‖c‖ ≤ 1 ∧ m =ᶠ[nhds t] fun _ => c := by
    intro t ht
    rcases lt_or_gt_of_ne ht with h | h
    · exact ⟨-1, by simp, Filter.eventuallyEq_of_mem (Iio_mem_nhds h)
        fun y hy => by simp [hm, not_lt.2 (le_of_lt hy)]⟩
    · exact ⟨1, by simp, Filter.eventuallyEq_of_mem (Ioi_mem_nhds h) fun y hy => by simp [hm, show 0 < y from hy]⟩
  refine ⟨fun t ht => ?_, fun j t ht => ?_⟩
  · obtain ⟨c, -, hc⟩ := hloc t ht
    exact (contDiffAt_const.congr_of_eventuallyEq hc).contDiffWithinAt
  · obtain ⟨c, hc1, hc⟩ := hloc t ht
    rw [hc.iteratedDeriv_eq j]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simpa using hc1
    · simp [iteratedDeriv_const, hj.ne']

/-- All hypotheses of `t_finiteBV` (other than the choice of test functions, which are arbitrary)
hold simultaneously for `P = 1`, `u = 2`, `m = 1`, `Π` = the scalar form, `CT = 1`. -/
theorem hypotheses_satisfiable_P1 :
    ∃ (u : ℝ) (A : ℕ → ℝ) (m : ℝ → ℂ) (CT : ℝ), 1 < u ∧ ContDiffOn ℝ ∞ m {0}ᶜ ∧
      (∀ j : ℕ, ∀ t : ℝ, t ≠ 0 → |t| ^ j * ‖iteratedDeriv j m t‖ ≤ A j) ∧
      (∀ F G H : ZMod 1 → ℂ,
        ‖scalarForm F G H‖ ≤ CT * yNorm 2 F * yNorm 2 G * yNorm u H) := by
  obtain ⟨h1, h2⟩ := const_multiplier_decay
  exact ⟨2, fun j => if j = 0 then 1 else 0, fun _ => 1, 1, by norm_num, h1, h2,
    fun F G H => (norm_scalarForm (by norm_num) F G H).le⟩

/-! ### (iii) `Λ_m^Π` is a genuine (absolutely convergent) Lebesgue integral, not the junk value `0` -/

/-- Schwartz functions are bounded. -/
theorem schwartz_bounded (g : 𝓢(ℝ, ℂ)) : ∃ c : ℝ, ∀ x, ‖g x‖ ≤ c :=
  ⟨‖g.toBoundedContinuousFunction‖, fun x => by
    simpa using g.toBoundedContinuousFunction.norm_coe_le_norm x⟩

/-- The model term `ξ ↦ ĝ(ξ₁) ĥ(ξ₂) conj(k̂(ξ₁ + ξ₂))` is integrable on `ℝ²`, `g, h, k ∈ 𝓢(ℝ)`. -/
theorem integrable_fourier_term (g h k : 𝓢(ℝ, ℂ)) :
    Integrable (fun ξ : ℝ × ℝ =>
      𝓕 (⇑g) ξ.1 * 𝓕 (⇑h) ξ.2 * conj (𝓕 (⇑k) (ξ.1 + ξ.2))) := by
  have hg : Integrable (𝓕 (⇑g)) := SchwartzMap.integrable (𝓕 g)
  have hh : Integrable (𝓕 (⇑h)) := SchwartzMap.integrable (𝓕 h)
  have hprod : Integrable (fun ξ : ℝ × ℝ => 𝓕 (⇑g) ξ.1 * 𝓕 (⇑h) ξ.2) :=
    by simpa [Measure.volume_eq_prod] using hg.mul_prod hh
  have hkc : Continuous (𝓕 (⇑k)) := (𝓕 k).continuous
  obtain ⟨c, hc⟩ := schwartz_bounded (𝓕 k)
  have hmeas : AEStronglyMeasurable (fun ξ : ℝ × ℝ => conj (𝓕 (⇑k) (ξ.1 + ξ.2))) volume :=
    (Complex.continuous_conj.comp (hkc.comp (continuous_fst.add continuous_snd))).aestronglyMeasurable
  have := hprod.bdd_mul (c := c) hmeas (Filter.Eventually.of_forall fun ξ => by
    show ‖conj (𝓕 (⇑k) (ξ.1 + ξ.2))‖ ≤ c
    rw [RCLike.norm_conj]
    exact hc _)
  convert this using 2 with ξ
  ring

/-- `tensorFourier f ξ = ∑_A f̂_A(ξ) • χ_A`, with the characters `χ_A(y) = e(A y / P)`. -/
theorem tensorFourier_eq_sum {P : ℕ} [NeZero P] (f : ZMod P → 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    tensorFourier f ξ =
      ∑ A : ZMod P, 𝓕 (⇑(f A)) ξ • (fun y : ZMod P => (ZMod.stdAddChar (A * y) : ℂ)) := by
  funext y
  simp [tensorFourier, Finset.sum_apply]

/-- Trilinear expansion of a form (linear, linear, conjugate-linear) on finite combinations. -/
theorem form_expand {P : ℕ} [NeZero P]
    (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
    (a b c : ZMod P → ℂ) (χ : ZMod P → ZMod P → ℂ) :
    T (∑ A, a A • χ A) (∑ B, b B • χ B) (∑ C, c C • χ C) =
      ∑ A, ∑ B, ∑ C, T (χ A) (χ B) (χ C) * (a A * b B * conj (c C)) := by
  have h1 : T (∑ A, a A • χ A) = ∑ A, a A • T (χ A) := by
    rw [map_sum]; simp only [map_smul]
  have h2 : ∀ A, T (χ A) (∑ B, b B • χ B) = ∑ B, b B • T (χ A) (χ B) := fun A => by
    rw [map_sum]; simp only [map_smul]
  have h3 : ∀ A B, T (χ A) (χ B) (∑ C, c C • χ C) =
      ∑ C, conj (c C) • T (χ A) (χ B) (χ C) := fun A B => by
    rw [map_sum]; simp only [map_smulₛₗ]
  rw [h1, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [LinearMap.smul_apply, h2, LinearMap.sum_apply, h3, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun B _ => Finset.sum_congr rfl fun C _ => ?_
  ring

/-- **Integrability of the integrand of `Λ_m^Π`.** If `m` is continuous off `0` and bounded,
the integrand `m(ξ₂ - ξ₁) Π(F̂₁(ξ₁;·), F̂₂(ξ₂;·), F̂₃(ξ₁+ξ₂;·))` of `multiplierForm` is Lebesgue
integrable on `ℝ²` for every form `Π` and all tensor Schwartz functions; hence `multiplierForm`
is the true integral (not the junk value `0` of a non-integrable Bochner integral). The hypotheses
of `t_finiteBV` give boundedness (`j = 0`) and continuity off `0` (smoothness). -/
theorem integrable_multiplierForm {P : ℕ} [NeZero P] (m : ℝ → ℂ) (hm : ContinuousOn m {0}ᶜ)
    (c : ℝ) (hc : ∀ t, ‖m t‖ ≤ c)
    (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
    (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) :
    Integrable (fun ξ : ℝ × ℝ => m (ξ.2 - ξ.1) *
      T (tensorFourier f₁ ξ.1) (tensorFourier f₂ ξ.2) (tensorFourier f₃ (ξ.1 + ξ.2))) := by
  set χ : ZMod P → ZMod P → ℂ := fun A y => (ZMod.stdAddChar (A * y) : ℂ) with hχ
  have hS : Integrable (fun ξ : ℝ × ℝ =>
      T (tensorFourier f₁ ξ.1) (tensorFourier f₂ ξ.2) (tensorFourier f₃ (ξ.1 + ξ.2))) := by
    have : (fun ξ : ℝ × ℝ =>
        T (tensorFourier f₁ ξ.1) (tensorFourier f₂ ξ.2) (tensorFourier f₃ (ξ.1 + ξ.2))) =
        fun ξ => ∑ A, ∑ B, ∑ C, T (χ A) (χ B) (χ C) *
          (𝓕 (⇑(f₁ A)) ξ.1 * 𝓕 (⇑(f₂ B)) ξ.2 * conj (𝓕 (⇑(f₃ C)) (ξ.1 + ξ.2))) := by
      funext ξ
      rw [tensorFourier_eq_sum f₁, tensorFourier_eq_sum f₂, tensorFourier_eq_sum f₃,
        form_expand T (fun A => 𝓕 (⇑(f₁ A)) ξ.1) (fun B => 𝓕 (⇑(f₂ B)) ξ.2)
          (fun C => 𝓕 (⇑(f₃ C)) (ξ.1 + ξ.2)) χ]
    rw [this]
    exact integrable_finsetSum _ fun A _ => integrable_finsetSum _ fun B _ =>
      integrable_finsetSum _ fun C _ => (integrable_fourier_term _ _ _).const_mul _
  have hmeas : AEStronglyMeasurable (fun ξ : ℝ × ℝ => m (ξ.2 - ξ.1)) volume :=
    ((measurable_of_continuousOn_compl_singleton 0 hm).comp
      (measurable_snd.sub measurable_fst)).aestronglyMeasurable
  exact hS.bdd_mul (c := c) hmeas (Filter.Eventually.of_forall fun ξ => hc _)

/-- Under the hypotheses of `t_finiteBV` (smooth off `0`, `sup |m| ≤ A_0`) the integrand of `Λ_m^Π`
is integrable: the value `multiplierForm m T f₁ f₂ f₃` is the genuine integral. -/
theorem integrable_multiplierForm_of_decay {P : ℕ} [NeZero P] (m : ℝ → ℂ)
    (hsm : ContDiffOn ℝ ∞ m {0}ᶜ) (A₀ : ℝ)
    (hA : ∀ t : ℝ, t ≠ 0 → |t| ^ 0 * ‖iteratedDeriv 0 m t‖ ≤ A₀)
    (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
    (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) :
    Integrable (fun ξ : ℝ × ℝ => m (ξ.2 - ξ.1) *
      T (tensorFourier f₁ ξ.1) (tensorFourier f₂ ξ.2) (tensorFourier f₃ (ξ.1 + ξ.2))) := by
  refine integrable_multiplierForm m (hsm.continuousOn) (max A₀ ‖m 0‖) (fun t => ?_) T f₁ f₂ f₃
  by_cases ht : t = 0
  · subst ht; exact le_max_right _ _
  · have := hA t ht
    simp only [pow_zero, one_mul, iteratedDeriv_zero] at this
    exact this.trans (le_max_left _ _)

/-! ### (iv) The three mixed norms of a tensor Schwartz function are finite -/

theorem yNorm_nonneg {P : ℕ} [NeZero P] (s : ℝ) (F : ZMod P → ℂ) : 0 ≤ yNorm s F :=
  Real.rpow_nonneg (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg P))
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) s)) _

/-- A pointwise bound `‖G y‖ ≤ M` bounds the normalized `L^s(Y_P)` norm by `M` (`s > 0`). -/
theorem yNorm_le {P : ℕ} [NeZero P] {s : ℝ} (hs : 0 < s) (G : ZMod P → ℂ) {M : ℝ}
    (hM : ∀ y, ‖G y‖ ≤ M) : yNorm s G ≤ M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hP : (P : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne P)
  unfold yNorm
  have hsum : ∑ y, ‖G y‖ ^ s ≤ (P : ℝ) * M ^ s := by
    calc ∑ y, ‖G y‖ ^ s ≤ ∑ _y : ZMod P, M ^ s :=
          Finset.sum_le_sum fun y _ => Real.rpow_le_rpow (norm_nonneg _) (hM y) hs.le
      _ = (P : ℝ) * M ^ s := by simp [ZMod.card]
  calc ((P : ℝ)⁻¹ * ∑ y, ‖G y‖ ^ s) ^ s⁻¹ ≤ ((P : ℝ)⁻¹ * ((P : ℝ) * M ^ s)) ^ s⁻¹ :=
        Real.rpow_le_rpow (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg P))
          (Finset.sum_nonneg fun y _ => Real.rpow_nonneg (norm_nonneg _) s))
          (mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 (Nat.cast_nonneg P)))
          (inv_nonneg.2 hs.le)
    _ = M := by
        rw [← mul_assoc, inv_mul_cancel₀ hP, one_mul, Real.rpow_rpow_inv hM0 hs.ne']

theorem norm_tensorFun_le {P : ℕ} [NeZero P] (f : ZMod P → 𝓢(ℝ, ℂ)) (x : ℝ) (y : ZMod P) :
    ‖tensorFun f x y‖ ≤ ∑ A, ‖f A x‖ := by
  unfold tensorFun
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun A _ => ?_)
  rw [norm_mul]
  have : ‖(ZMod.stdAddChar (A * y) : ℂ)‖ = 1 := by simp [ZMod.stdAddChar_apply]
  rw [this, mul_one]

theorem continuous_yNorm_tensorFun {P : ℕ} [NeZero P] {s : ℝ} (hs : 0 < s)
    (f : ZMod P → 𝓢(ℝ, ℂ)) : Continuous fun x : ℝ => yNorm s (tensorFun f x) := by
  have hc : ∀ y : ZMod P, Continuous fun x : ℝ => tensorFun f x y := fun y => by
    unfold tensorFun
    exact continuous_finsetSum _ fun A _ => (f A).continuous.mul continuous_const
  unfold yNorm
  exact Continuous.rpow_const (continuous_const.mul (continuous_finsetSum _ fun y _ =>
    (continuous_norm.comp (hc y)).rpow_const fun _ => Or.inr hs.le))
    fun _ => Or.inr (inv_nonneg.2 hs.le)

/-- `‖F‖_{L^∞_x L^u_y} < ∞` for a tensor Schwartz function, `u > 0`. -/
theorem eLpNorm_top_tensorFun_lt_top {P : ℕ} [NeZero P] {u : ℝ} (hu : 0 < u)
    (f : ZMod P → 𝓢(ℝ, ℂ)) :
    eLpNorm (fun x : ℝ => yNorm u (tensorFun f x)) ⊤ volume < ⊤ := by
  choose c hc using fun A => schwartz_bounded (f A)
  have hb : ∀ x : ℝ, ‖yNorm u (tensorFun f x)‖ ≤ ∑ A, c A := fun x => by
    rw [Real.norm_of_nonneg (yNorm_nonneg _ _)]
    exact yNorm_le hu _ fun y => (norm_tensorFun_le f x y).trans
      (Finset.sum_le_sum fun A _ => hc A x)
  rw [eLpNorm_exponent_top (continuous_yNorm_tensorFun hu f).aestronglyMeasurable]
  exact lt_of_le_of_lt (eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hb))
    ENNReal.ofReal_lt_top

/-- `‖F‖_{L²_x L²_y} < ∞` for a tensor Schwartz function. -/
theorem eLpNorm_two_tensorFun_lt_top {P : ℕ} [NeZero P] (f : ZMod P → 𝓢(ℝ, ℂ)) :
    eLpNorm (fun x : ℝ => yNorm 2 (tensorFun f x)) 2 volume < ⊤ := by
  have hmem : MemLp (fun x : ℝ => ∑ A, ‖f A x‖) 2 volume :=
    memLp_finsetSum (Finset.univ : Finset (ZMod P)) fun A _ => ((f A).memLp 2 volume).norm
  refine lt_of_le_of_lt (eLpNorm_mono_real
    (continuous_yNorm_tensorFun two_pos f).aestronglyMeasurable fun x => ?_) hmem.eLpNorm_lt_top
  rw [Real.norm_of_nonneg (yNorm_nonneg _ _)]
  exact yNorm_le two_pos _ fun y => norm_tensorFun_le f x y

/-! ### (v) The `CT`-hypothesis is exactly "`CT` is an upper bound of the operator norm `‖Π‖`" -/

/-- `yNorm s F = 0` only for `F = 0` (`s > 0`): `yNorm` is a norm, not a seminorm. -/
theorem eq_zero_of_yNorm_eq_zero {P : ℕ} [NeZero P] {s : ℝ} (hs : 0 < s) {F : ZMod P → ℂ}
    (h : yNorm s F = 0) : F = 0 := by
  have hP : (P : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 (NeZero.ne P))
  unfold yNorm at h
  have hnn : 0 ≤ (P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ s :=
    mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg P))
      (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) s)
  have h1 := (Real.rpow_eq_zero hnn (inv_ne_zero hs.ne')).1 h
  have h2 : ∑ y, ‖F y‖ ^ s = 0 := (mul_eq_zero.1 h1).resolve_left hP
  funext y
  have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) s).1 h2
    y (Finset.mem_univ y)
  have h3 := (Real.rpow_eq_zero (norm_nonneg _) hs.ne').1 this
  simpa using h3

/-- Homogeneity: `yNorm s (r • F) = ‖r‖ * yNorm s F` (`s > 0`). -/
theorem yNorm_smul {P : ℕ} [NeZero P] {s : ℝ} (hs : 0 < s) (r : ℂ) (F : ZMod P → ℂ) :
    yNorm s (r • F) = ‖r‖ * yNorm s F := by
  unfold yNorm
  have hnn : 0 ≤ (P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ s :=
    mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg P))
      (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) s)
  have : (P : ℝ)⁻¹ * ∑ y, ‖(r • F) y‖ ^ s = ‖r‖ ^ s * ((P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ s) := by
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Real.mul_rpow (norm_nonneg r) (norm_nonneg _),
      ← Finset.mul_sum]
    ring
  rw [this, Real.mul_rpow (Real.rpow_nonneg (norm_nonneg r) s) hnn,
    Real.rpow_rpow_inv (norm_nonneg r) hs.ne']

/-- For `CT ≥ 0` and `u > 0`, `|Π(F,G,H)| ≤ CT ‖F‖_{L²} ‖G‖_{L²} ‖H‖_{L^u}` for all `F,G,H` is
equivalent to `|Π(F,G,H)| ≤ CT` on the unit balls, i.e. to `‖Π‖ ≤ CT` with the paper's
`‖Π‖ = sup{|Π(f₁,f₂,f₃)| : ‖f_i‖_{X_i} ≤ 1}` (line 935-937). -/
theorem bound_iff_opNorm_le {P : ℕ} [NeZero P]
    (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
    {u : ℝ} (hu : 0 < u) {CT : ℝ} (hCT : 0 ≤ CT) :
    (∀ F G H : ZMod P → ℂ, ‖T F G H‖ ≤ CT * yNorm 2 F * yNorm 2 G * yNorm u H) ↔
    (∀ F G H : ZMod P → ℂ, yNorm 2 F ≤ 1 → yNorm 2 G ≤ 1 → yNorm u H ≤ 1 → ‖T F G H‖ ≤ CT) := by
  constructor
  · intro h F G H hF hG hH
    have h0 := yNorm_nonneg 2 F
    have h1 := yNorm_nonneg 2 G
    have h2 := yNorm_nonneg u H
    calc ‖T F G H‖ ≤ CT * yNorm 2 F * yNorm 2 G * yNorm u H := h F G H
      _ ≤ CT * 1 * 1 * 1 := by gcongr
      _ = CT := by ring
  · intro h F G H
    by_cases hF0 : yNorm 2 F = 0
    · have hF := eq_zero_of_yNorm_eq_zero two_pos hF0
      have : T F G H = 0 := by rw [hF]; simp
      rw [this, hF0]; simp
    by_cases hG0 : yNorm 2 G = 0
    · have hG := eq_zero_of_yNorm_eq_zero two_pos hG0
      have : T F G H = 0 := by rw [hG]; simp
      rw [this, hG0]; simp
    by_cases hH0 : yNorm u H = 0
    · have hH := eq_zero_of_yNorm_eq_zero hu hH0
      have : T F G H = 0 := by rw [hH]; simp
      rw [this, hH0]; simp
    have ha : 0 < yNorm 2 F := lt_of_le_of_ne (yNorm_nonneg _ _) (Ne.symm hF0)
    have hb : 0 < yNorm 2 G := lt_of_le_of_ne (yNorm_nonneg _ _) (Ne.symm hG0)
    have hc : 0 < yNorm u H := lt_of_le_of_ne (yNorm_nonneg _ _) (Ne.symm hH0)
    have key := h (((yNorm 2 F)⁻¹ : ℝ) • F) (((yNorm 2 G)⁻¹ : ℝ) • G) (((yNorm u H)⁻¹ : ℝ) • H)
      (by rw [show (((yNorm 2 F)⁻¹ : ℝ) • F : ZMod P → ℂ) = (((yNorm 2 F)⁻¹ : ℝ) : ℂ) • F from rfl,
            yNorm_smul two_pos]; simp [abs_of_pos ha, inv_mul_cancel₀ hF0])
      (by rw [show (((yNorm 2 G)⁻¹ : ℝ) • G : ZMod P → ℂ) = (((yNorm 2 G)⁻¹ : ℝ) : ℂ) • G from rfl,
            yNorm_smul two_pos]; simp [abs_of_pos hb, inv_mul_cancel₀ hG0])
      (by rw [show (((yNorm u H)⁻¹ : ℝ) • H : ZMod P → ℂ) = (((yNorm u H)⁻¹ : ℝ) : ℂ) • H from rfl,
            yNorm_smul hu]; simp [abs_of_pos hc, inv_mul_cancel₀ hH0])
    have hexp : T (((yNorm 2 F)⁻¹ : ℝ) • F) (((yNorm 2 G)⁻¹ : ℝ) • G) (((yNorm u H)⁻¹ : ℝ) • H) =
        (((yNorm 2 F)⁻¹ * (yNorm 2 G)⁻¹ * (yNorm u H)⁻¹ : ℝ) : ℂ) • T F G H := by
      have e1 : (((yNorm 2 F)⁻¹ : ℝ) • F : ZMod P → ℂ) = (((yNorm 2 F)⁻¹ : ℝ) : ℂ) • F := rfl
      have e2 : (((yNorm 2 G)⁻¹ : ℝ) • G : ZMod P → ℂ) = (((yNorm 2 G)⁻¹ : ℝ) : ℂ) • G := rfl
      have e3 : (((yNorm u H)⁻¹ : ℝ) • H : ZMod P → ℂ) = (((yNorm u H)⁻¹ : ℝ) : ℂ) • H := rfl
      rw [e1, e2, e3]
      simp only [map_smul, LinearMap.smul_apply, map_smulₛₗ, Complex.conj_ofReal, smul_eq_mul]
      push_cast
      ring
    rw [hexp, norm_smul] at key
    have hpos : 0 < (yNorm 2 F)⁻¹ * (yNorm 2 G)⁻¹ * (yNorm u H)⁻¹ := by positivity
    rw [Complex.norm_real, Real.norm_of_nonneg hpos.le] at key
    have hk : ‖T F G H‖ = (yNorm 2 F * yNorm 2 G * yNorm u H) *
        ((yNorm 2 F)⁻¹ * (yNorm 2 G)⁻¹ * (yNorm u H)⁻¹ * ‖T F G H‖) := by
      field_simp
    rw [hk]
    calc (yNorm 2 F * yNorm 2 G * yNorm u H) *
          ((yNorm 2 F)⁻¹ * (yNorm 2 G)⁻¹ * (yNorm u H)⁻¹ * ‖T F G H‖)
        ≤ (yNorm 2 F * yNorm 2 G * yNorm u H) * CT :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = CT * yNorm 2 F * yNorm 2 G * yNorm u H := by ring

/-- An admissible `CT` is automatically `≥ 0` (test with `F = G = H = 1`, which is nonzero because
`Y_P` is nonempty): so `ENNReal.ofReal (C * CT)` in `t_finiteBV` never truncates a negative number
in a case where the hypotheses can hold. -/
theorem nonneg_of_bound {P : ℕ} [NeZero P]
    (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
    {u : ℝ} (hu : 0 < u) {CT : ℝ}
    (h : ∀ F G H : ZMod P → ℂ, ‖T F G H‖ ≤ CT * yNorm 2 F * yNorm 2 G * yNorm u H) :
    0 ≤ CT := by
  have h1 : (1 : ZMod P → ℂ) ≠ 0 := fun h0 => by simpa using congrFun h0 0
  have ha : 0 < yNorm 2 (1 : ZMod P → ℂ) :=
    lt_of_le_of_ne (yNorm_nonneg _ _) fun h0 => h1 (eq_zero_of_yNorm_eq_zero two_pos h0.symm)
  have hc : 0 < yNorm u (1 : ZMod P → ℂ) :=
    lt_of_le_of_ne (yNorm_nonneg _ _) fun h0 => h1 (eq_zero_of_yNorm_eq_zero hu h0.symm)
  have := (norm_nonneg _).trans (h 1 1 1)
  have hpos : 0 < yNorm 2 (1 : ZMod P → ℂ) * yNorm 2 (1 : ZMod P → ℂ) * yNorm u (1 : ZMod P → ℂ) :=
    by positivity
  nlinarith

/-- The right-hand side of `t_finiteBV` is a finite number (so the inequality is not trivial
through `⊤`, nor through the `else ⊤` branch of `eLpNorm` for non-measurable functions). -/
theorem rhs_lt_top {P : ℕ} [NeZero P] {u : ℝ} (hu : 0 < u) (C CT : ℝ)
    (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) :
    ENNReal.ofReal (C * CT) *
      eLpNorm (fun x : ℝ => yNorm 2 (tensorFun f₁ x)) 2 volume *
      eLpNorm (fun x : ℝ => yNorm 2 (tensorFun f₂ x)) 2 volume *
      eLpNorm (fun x : ℝ => yNorm u (tensorFun f₃ x)) ⊤ volume < ⊤ :=
  ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (eLpNorm_two_tensorFun_lt_top f₁)) (eLpNorm_two_tensorFun_lt_top f₂))
    (eLpNorm_top_tensorFun_lt_top hu f₃)

/-! ### (vi) The integrability conjunct of the frozen statement is a theorem of its hypotheses -/

/-- Under the hypotheses of `t_finiteBV` on `m` (smooth off `0`, all-multi-index decay with the bounds
`A`), the integrand of `Λ_m^Π` is Lebesgue integrable on `ℝ²`, for every form `Π` and all tensor
Schwartz functions: this is the first conjunct of the conclusion of the frozen statement (it needs
only `j = 0` of the decay). -/
theorem integrable_of_hyps {P : ℕ} [NeZero P] (m : ℝ → ℂ) (hsm : ContDiffOn ℝ ∞ m {0}ᶜ)
    (A : ℕ → ℝ) (hA : ∀ j : ℕ, ∀ t : ℝ, t ≠ 0 → |t| ^ j * ‖iteratedDeriv j m t‖ ≤ A j)
    (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
    (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) :
    Integrable (fun ξ : ℝ × ℝ => m (ξ.2 - ξ.1) *
      T (tensorFourier f₁ ξ.1) (tensorFourier f₂ ξ.2) (tensorFourier f₃ (ξ.1 + ξ.2))) volume :=
  integrable_multiplierForm_of_decay m hsm (A 0) (hA 0) T f₁ f₂ f₃

end PrimeBHT.Interface.X2

end
