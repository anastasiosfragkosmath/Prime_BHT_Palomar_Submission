module

public import PrimeBHT.TimeFrequency.X2.CZ.Statements
public import PrimeBHT.Lift
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.MeanInequalities

/-!
# V08: the mixed-norm API on `ℝ → ZMod P → ℂ`

`mixedENorm q s F = ‖x ↦ yNorm s (F x)‖_{L^q(ℝ)} ∈ [0, ∞]` (`Statements.lean`).  This file collects what the
vector-valued Calderón-Zygmund node needs about it; everything is uniform in `P` (the only place where
`P` enters is the normalization `P⁻¹ Σ_y`).

* `yNorm` bridge to `PrimeBHT.Lift.yNorm` (same body) and the elementary facts.
* **Fubini identification** (`mixedENorm_diag_rpow`, `mixedENorm_diag_rpow_fibre`): for `0 < s`,
  `‖F‖_{L^s(ℝ; L^s(Y))}^s = P⁻¹ Σ_y ∫ ‖F(x, y)‖^s dx = P⁻¹ Σ_y ‖F(·, y)‖_{L^s(ℝ)}^s`
  (the identification `L^s(ℝ; L^s(Y)) = L^s(ℝ × Y)`).
* **Hilbert case** `X = H = L²(Y)` (`mixedENorm_two_sq`): `‖F‖_{L²(ℝ; H)}² = P⁻¹ Σ_y ‖F(·, y)‖₂²`.
* **Fibrewise action** (`tensorMult_eq_multOp_fibre`): `(T_σ ⊗ Id)(tensorFun f)(x, y) = T_σ (F(·, y))(x)`.
* **Duality (e)**.  The pairing `⟨F, G⟩ = ∫ P⁻¹ Σ_y F(x,y) conj G(x,y) dx`; Hölder
  `ofReal ‖⟨F, G⟩‖ ≤ ‖F‖_{L^q(L^s)} ‖G‖_{L^{q'}(L^{s'})}` (`ofReal_norm_mixedPairing_le`, the
  *proved* easy half of `L^q(ℝ; L^s(Y))' = L^{q'}(ℝ; L^{s'}(Y))`), and the norming statement
  `MixedNormDuality` (the other half, stated as a `Prop`: `‖F‖ = sup` over bounded compactly supported
  `G` of unit dual norm; to be proved in the duality module of the V08b phase).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate Real

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

open PrimeBHT.Statements

section YNorm

variable {P : ℕ} [NeZero P]

theorem yNorm_nonneg (s : ℝ) (F : ZMod P → ℂ) : 0 ≤ yNorm s F :=
  PrimeBHT.Lift.yNorm_nonneg s F

theorem yNorm_rpow_self {s : ℝ} (hs : s ≠ 0) (F : ZMod P → ℂ) :
    yNorm s F ^ s = (P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ s :=
  PrimeBHT.Lift.yNorm_rpow_self hs F

/-- `(‖F‖_{L^s(Y)})^s = P⁻¹ Σ_y ‖F y‖^s` in `[0, ∞]`. -/
theorem ofReal_yNorm_rpow {s : ℝ} (hs : 0 < s) (F : ZMod P → ℂ) :
    ENNReal.ofReal (yNorm s F) ^ s = (P : ℝ≥0∞)⁻¹ * ∑ y, ‖F y‖ₑ ^ s := by
  rw [ENNReal.ofReal_rpow_of_nonneg (yNorm_nonneg s F) hs.le, yNorm_rpow_self hs.ne',
    ENNReal.ofReal_mul (inv_nonneg.2 (Nat.cast_nonneg P)),
    ENNReal.ofReal_sum_of_nonneg (fun y _ => Real.rpow_nonneg (norm_nonneg _) _)]
  congr 1
  · rw [ENNReal.ofReal_inv_of_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P)))]
    simp
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hs.le, ofReal_norm]

end YNorm

section Fubini

variable {P : ℕ} [NeZero P]

/-- `x ↦ ‖F x‖_{L^s(Y)}` is a.e. measurable as soon as every fibre `x ↦ F x y` is. -/
theorem aemeasurable_yNorm (s : ℝ) {F : ℝ → ZMod P → ℂ}
    (hF : ∀ y, AEStronglyMeasurable (fun x => F x y) volume) :
    AEMeasurable (fun x => yNorm s (F x)) volume := by
  unfold yNorm
  refine AEMeasurable.pow_const (AEMeasurable.const_mul ?_ _) _
  have : (fun x => ∑ y, ‖F x y‖ ^ s) = ∑ y, fun x => ‖F x y‖ ^ s := by
    ext x; simp
  rw [this]
  exact Finset.aemeasurable_sum _ fun y _ => ((hF y).aemeasurable.norm).pow_const s

/-- `‖F‖_{L^q(ℝ; L^s(Y))}^q = ∫ (‖F x‖_{L^s(Y)})^q dx` in `[0, ∞]`. -/
theorem mixedENorm_rpow {q : ℝ} (hq : 0 < q) (s : ℝ) {F : ℝ → ZMod P → ℂ}
    (hF : ∀ y, AEStronglyMeasurable (fun x => F x y) volume) :
    mixedENorm q s F ^ q = ∫⁻ x, ENNReal.ofReal (yNorm s (F x)) ^ q := by
  unfold mixedENorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq).ne' (by simp)
      (aemeasurable_yNorm s hF).aestronglyMeasurable,
    ENNReal.toReal_ofReal hq.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq.ne',
    ENNReal.rpow_one]
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal (yNorm_nonneg s (F x))]

/-- **Fubini identification** `L^s(ℝ; L^s(Y)) = L^s(ℝ × Y)`:
`‖F‖_{L^s(ℝ; L^s(Y))}^s = P⁻¹ Σ_y ∫ ‖F(x, y)‖^s dx` (each fibre measurable). -/
theorem mixedENorm_diag_rpow {s : ℝ} (hs : 0 < s) {F : ℝ → ZMod P → ℂ}
    (hF : ∀ y, AEStronglyMeasurable (fun x => F x y) volume) :
    mixedENorm s s F ^ s = (P : ℝ≥0∞)⁻¹ * ∑ y, ∫⁻ x, ‖F x y‖ₑ ^ s := by
  rw [mixedENorm_rpow hs s hF]
  simp_rw [ofReal_yNorm_rpow hs]
  rw [lintegral_const_mul'' _ ?_, lintegral_finsetSum']
  · exact fun y _ => ((hF y).aemeasurable.enorm).pow_const s
  · have : (fun x => ∑ y, ‖F x y‖ₑ ^ s) = ∑ y, fun x => ‖F x y‖ₑ ^ s := by
      ext x; simp
    rw [this]
    exact Finset.aemeasurable_sum _ fun y _ => ((hF y).aemeasurable.enorm).pow_const s

/-- The same, with the scalar `L^s(ℝ)` norms of the fibres `F(·, y)`:
`‖F‖_{L^s(ℝ; L^s(Y))}^s = P⁻¹ Σ_y ‖F(·, y)‖_{L^s(ℝ)}^s`. -/
theorem mixedENorm_diag_rpow_fibre {s : ℝ} (hs : 0 < s) {F : ℝ → ZMod P → ℂ}
    (hF : ∀ y, AEStronglyMeasurable (fun x => F x y) volume) :
    mixedENorm s s F ^ s =
      (P : ℝ≥0∞)⁻¹ * ∑ y, eLpNorm (fun x => F x y) (ENNReal.ofReal s) volume ^ s := by
  rw [mixedENorm_diag_rpow hs hF]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hs).ne' (by simp) (hF y),
    ENNReal.toReal_ofReal hs.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hs.ne',
    ENNReal.rpow_one]

end Fubini

section Fibre

variable {P : ℕ} [NeZero P]

theorem fourier_coe_apply (g : 𝓢(ℝ, ℂ)) (ξ : ℝ) : (𝓕 g : 𝓢(ℝ, ℂ)) ξ = 𝓕 (⇑g) ξ :=
  congrFun (SchwartzMap.fourier_coe g) ξ

/-- Linearity of the Fourier transform of Schwartz functions, at the level of the underlying functions. -/
theorem fourier_coe_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℂ) (g : ι → 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (⇑(∑ i ∈ s, c i • g i)) ξ = ∑ i ∈ s, c i * 𝓕 (⇑(g i)) ξ := by
  have h3 : (𝓕 (∑ i ∈ s, c i • g i : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) ξ =
      ∑ i ∈ s, c i * (𝓕 (g i) : 𝓢(ℝ, ℂ)) ξ := by simp
  rw [fourier_coe_apply] at h3
  exact h3.trans (Finset.sum_congr rfl fun i _ => by rw [fourier_coe_apply])

theorem integrable_fourierChar_smul {h : ℝ → ℂ} (hh : Integrable h volume) (w : ℝ) :
    Integrable (fun v : ℝ => 𝐞 (-(inner ℝ v w)) • h v) volume :=
  (VectorFourier.fourierIntegral_convergent_iff (e := Real.fourierChar) (μ := volume)
    (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner w).2 hh

/-- The Fourier transform of a finite sum of integrable functions. -/
theorem fourier_finset_sum_fun {ι : Type*} (s : Finset ι) (h : ι → ℝ → ℂ)
    (hi : ∀ i ∈ s, Integrable (h i) volume) (w : ℝ) :
    𝓕 (fun ξ => ∑ i ∈ s, h i ξ) w = ∑ i ∈ s, 𝓕 (h i) w := by
  simp only [Real.fourier_eq]
  rw [← integral_finsetSum _ fun i hi' => integrable_fourierChar_smul (hi i hi') w]
  simp [Finset.smul_sum]

/-- The inverse Fourier transform of a finite sum of integrable functions. -/
theorem fourierInv_finset_sum_fun {ι : Type*} (s : Finset ι) (h : ι → ℝ → ℂ)
    (hi : ∀ i ∈ s, Integrable (h i) volume) (x : ℝ) :
    𝓕⁻ (fun ξ => ∑ i ∈ s, h i ξ) x = ∑ i ∈ s, 𝓕⁻ (h i) x := by
  simp only [Real.fourierInv_eq_fourier_neg]
  exact fourier_finset_sum_fun s h hi (-x)

theorem fourierInv_const_mul (c : ℂ) (h : ℝ → ℂ) (x : ℝ) :
    𝓕⁻ (fun ξ => c * h ξ) x = c * 𝓕⁻ h x := by
  simp only [Real.fourierInv_eq]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [Circle.smul_def, smul_eq_mul]
  ring

/-- A bounded measurable symbol: `σ` is a.e. strongly measurable and `‖σ‖ ≤ B` a.e. -/
structure IsBoundedSymbol (B : ℝ) (σ : ℝ → ℂ) : Prop where
  aestronglyMeasurable : AEStronglyMeasurable σ volume
  ae_norm_le : ∀ᵐ ξ ∂volume, ‖σ ξ‖ ≤ B

/-- For `σ` bounded and measurable and `g` Schwartz, `σ · 𝓕 g` is integrable. -/
theorem IsBoundedSymbol.integrable_mul_fourier {B : ℝ} {σ : ℝ → ℂ} (hσ : IsBoundedSymbol B σ)
    (g : 𝓢(ℝ, ℂ)) : Integrable (fun ξ => σ ξ * 𝓕 (⇑g) ξ) volume := by
  have h : Integrable (⇑(𝓕 g : 𝓢(ℝ, ℂ))) volume := (𝓕 g : 𝓢(ℝ, ℂ)).integrable
  have h' : Integrable (𝓕 (⇑g)) volume := by
    rw [← SchwartzMap.fourier_coe]; exact h
  exact h'.bdd_mul hσ.aestronglyMeasurable hσ.ae_norm_le

/-- Linearity of `T_σ` on finite combinations of Schwartz functions. -/
theorem multOp_coe_sum_smul {B : ℝ} {σ : ℝ → ℂ} (hσ : IsBoundedSymbol B σ)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (g : ι → 𝓢(ℝ, ℂ)) (x : ℝ) :
    multOp σ (⇑(∑ i ∈ s, c i • g i)) x = ∑ i ∈ s, c i * multOp σ (⇑(g i)) x := by
  unfold multOp
  have h1 : (fun ξ => σ ξ * 𝓕 (⇑(∑ i ∈ s, c i • g i)) ξ) =
      fun ξ => ∑ i ∈ s, c i * (σ ξ * 𝓕 (⇑(g i)) ξ) := by
    ext ξ
    rw [fourier_coe_sum_smul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, fourierInv_finset_sum_fun s _ (fun i _ => (hσ.integrable_mul_fourier (g i)).const_mul (c i))]
  exact Finset.sum_congr rfl fun i _ => fourierInv_const_mul (c i) _ x

/-- The fibre `x ↦ tensorFun f x y` is the Schwartz function `Σ_A e(Ay/P) f_A`. -/
theorem tensorFun_fibre_eq_coe (f : ZMod P → 𝓢(ℝ, ℂ)) (y : ZMod P) :
    (fun x => tensorFun f x y) = ⇑(∑ A : ZMod P, (ZMod.stdAddChar (A * y) : ℂ) • f A) := by
  ext x
  simp [tensorFun, mul_comm]

/-- **Fibrewise action**: `(T_σ ⊗ Id)(tensorFun f)(x, y) = T_σ (x' ↦ F(x', y))(x)`. -/
theorem tensorMult_eq_multOp_fibre {B : ℝ} {σ : ℝ → ℂ} (hσ : IsBoundedSymbol B σ)
    (f : ZMod P → 𝓢(ℝ, ℂ)) (x : ℝ) (y : ZMod P) :
    tensorMult σ f x y = multOp σ (fun x' => tensorFun f x' y) x := by
  rw [tensorFun_fibre_eq_coe, multOp_coe_sum_smul hσ]
  unfold tensorMult
  exact Finset.sum_congr rfl fun A _ => mul_comm _ _

end Fibre

/-! ## Duality (e): the pairing and Hölder -/

section Duality

variable {P : ℕ} [NeZero P]

/-- The normalized `L²(Y_P)` pairing `⟨F, G⟩_Y = P⁻¹ Σ_y F(y) conj(G(y))`. -/
def pairingY (F G : ZMod P → ℂ) : ℂ :=
  (P : ℂ)⁻¹ * ∑ y, F y * conj (G y)

/-- The pairing `⟨F, G⟩ = ∫ ⟨F(x), G(x)⟩_Y dx` of `L^q(ℝ; L^s(Y))` with `L^{q'}(ℝ; L^{s'}(Y))`
(a Bochner integral: it is `0` if the integrand is not integrable). -/
def mixedPairing (F G : ℝ → ZMod P → ℂ) : ℂ :=
  ∫ x, pairingY (F x) (G x)

/-- Real Hölder inequality for the normalized counting measure on `Y_P`. -/
theorem avg_mul_le_yNorm_mul {s s' : ℝ} (hs : s.HolderConjugate s') (a b : ZMod P → ℝ)
    (ha : ∀ y, 0 ≤ a y) (hb : ∀ y, 0 ≤ b y) :
    (P : ℝ)⁻¹ * ∑ y, a y * b y ≤
      ((P : ℝ)⁻¹ * ∑ y, a y ^ s) ^ s⁻¹ * ((P : ℝ)⁻¹ * ∑ y, b y ^ s') ^ s'⁻¹ := by
  have hP : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
  set c : ℝ := (P : ℝ) ^ (-(s⁻¹)) with hc
  set d : ℝ := (P : ℝ) ^ (-(s'⁻¹)) with hd
  have hc0 : 0 ≤ c := Real.rpow_nonneg hP.le _
  have hd0 : 0 ≤ d := Real.rpow_nonneg hP.le _
  have hcs : c ^ s = (P : ℝ)⁻¹ := by
    rw [hc, ← Real.rpow_mul hP.le, neg_mul, inv_mul_cancel₀ hs.pos.ne', Real.rpow_neg_one]
  have hds : d ^ s' = (P : ℝ)⁻¹ := by
    rw [hd, ← Real.rpow_mul hP.le, neg_mul, inv_mul_cancel₀ hs.symm.pos.ne', Real.rpow_neg_one]
  have hcd : c * d = (P : ℝ)⁻¹ := by
    rw [hc, hd, ← Real.rpow_add hP, ← neg_add, hs.inv_add_inv_eq_one, Real.rpow_neg_one]
  have key := Real.inner_le_Lp_mul_Lq_of_nonneg (Finset.univ : Finset (ZMod P))
    (f := fun y => c * a y) (g := fun y => d * b y) hs (fun y _ => mul_nonneg hc0 (ha y))
    (fun y _ => mul_nonneg hd0 (hb y))
  have e1 : ∑ y, (c * a y) * (d * b y) = (P : ℝ)⁻¹ * ∑ y, a y * b y := by
    rw [Finset.mul_sum, ← hcd]
    exact Finset.sum_congr rfl fun y _ => by ring
  have e2 : ∑ y, (c * a y) ^ s = (P : ℝ)⁻¹ * ∑ y, a y ^ s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Real.mul_rpow hc0 (ha y), hcs]
  have e3 : ∑ y, (d * b y) ^ s' = (P : ℝ)⁻¹ * ∑ y, b y ^ s' := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Real.mul_rpow hd0 (hb y), hds]
  rw [e1, e2, e3] at key
  simpa only [one_div] using key

/-- Hölder in `y`: `‖⟨F, G⟩_Y‖ ≤ ‖F‖_{L^s(Y)} ‖G‖_{L^{s'}(Y)}`. -/
theorem norm_pairingY_le {s s' : ℝ} (hs : s.HolderConjugate s') (F G : ZMod P → ℂ) :
    ‖pairingY F G‖ ≤ yNorm s F * yNorm s' G := by
  have hP : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
  unfold pairingY
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (P : ℝ)⁻¹ * ‖∑ y, F y * conj (G y)‖
      ≤ (P : ℝ)⁻¹ * ∑ y, ‖F y‖ * ‖G y‖ := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
        rw [norm_mul, Complex.norm_conj]
    _ ≤ yNorm s F * yNorm s' G :=
        avg_mul_le_yNorm_mul hs (fun y => ‖F y‖) (fun y => ‖G y‖) (fun y => norm_nonneg _)
          (fun y => norm_nonneg _)

/-- **Duality (e), the easy half (Hölder)**:
`‖⟨F, G⟩‖ ≤ ‖F‖_{L^q(ℝ; L^s(Y))} ‖G‖_{L^{q'}(ℝ; L^{s'}(Y))}` for conjugate exponents, in `[0, ∞]`,
uniformly in `P`. -/
theorem ofReal_norm_mixedPairing_le {q q' s s' : ℝ} (hq : q.HolderConjugate q')
    (hs : s.HolderConjugate s') {F G : ℝ → ZMod P → ℂ}
    (hF : ∀ y, AEStronglyMeasurable (fun x => F x y) volume)
    (hG : ∀ y, AEStronglyMeasurable (fun x => G x y) volume) :
    ENNReal.ofReal ‖mixedPairing F G‖ ≤ mixedENorm q s F * mixedENorm q' s' G := by
  have hFm := (aemeasurable_yNorm s hF).ennreal_ofReal
  have hGm := (aemeasurable_yNorm s' hG).ennreal_ofReal
  calc ENNReal.ofReal ‖mixedPairing F G‖
      = ‖∫ x, pairingY (F x) (G x)‖ₑ := (ofReal_norm _)
    _ ≤ ∫⁻ x, ‖pairingY (F x) (G x)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, (ENNReal.ofReal (yNorm s (F x)) * ENNReal.ofReal (yNorm s' (G x))) := by
        refine lintegral_mono fun x => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_mul (yNorm_nonneg _ _)]
        exact ENNReal.ofReal_le_ofReal (norm_pairingY_le hs _ _)
    _ ≤ (∫⁻ x, ENNReal.ofReal (yNorm s (F x)) ^ q) ^ (1 / q) *
          (∫⁻ x, ENNReal.ofReal (yNorm s' (G x)) ^ q') ^ (1 / q') :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq volume hq hFm hGm
    _ = mixedENorm q s F * mixedENorm q' s' G := by
        rw [← mixedENorm_rpow hq.pos s hF, ← mixedENorm_rpow hq.symm.pos s' hG, one_div, one_div,
          ENNReal.rpow_rpow_inv hq.pos.ne', ENNReal.rpow_rpow_inv hq.symm.pos.ne']

/-- Test functions for the norming statement: measurable fibres, bounded, vanishing outside a
bounded interval. -/
def IsTestFun {P : ℕ} [NeZero P] (G : ℝ → ZMod P → ℂ) : Prop :=
  (∀ y, Measurable fun x => G x y) ∧ (∃ M : ℝ, ∀ x y, ‖G x y‖ ≤ M) ∧
    ∃ R : ℝ, ∀ x, R < |x| → ∀ y, G x y = 0

end Duality

end PrimeBHT.TimeFrequency.X2.CZ
