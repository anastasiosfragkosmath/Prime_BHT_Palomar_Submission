module

public import PrimeBHT.TimeFrequency.X2.Paraproduct.Symbols
public import PrimeBHT.TimeFrequency.X2.Paraproduct.Tensor
public import PrimeBHT.TimeFrequency.X2.Paraproduct.MaxBound
public import PrimeBHT.TimeFrequency.X2.CZ.MikhlinAll
public import PrimeBHT.TimeFrequency.X2.CZ.Square

/-!
# V14 (paraproduct): the two estimates of the proof

* `lintegral_mul_three_le`: Hölder for three factors with exponents `1/p₀ + 1/p₁ + 1/p₂ = 1`;
* `square_bound`: the Hilbert-slot square function `(Σ_{j ∈ js} ‖T_{n_j} F(x)‖_H²)^{1/2}` is bounded on
  `L^q(ℝ; H)` (V08(d), upper half, reindexed from `Fin N` to a finite set of integers);
* `enorm_sum_triL_le` (**errors, V14 Step 2**): for LP-type families `n_j`, `σ_{2,j}` (Mikhlin sums) and adapted
  `σ_{3,j}`: `‖Σ_j ε_j ∫ T(T_{n_j} f₀, T_{σ₂ⱼ} f₁, T_{σ₃ⱼ} f₂)‖ ≲ CT ∏ ‖f_k‖` (Cauchy-Schwarz in `j` with the two
  Hilbert slots in `ℓ²_j` and the `X_u` slot bounded pointwise by the maximal function);
* `enorm_sum_triL_pull_le` (**the decoupled main term, V14 Step 4**): for `g₀` independent of `j`,
  `‖Σ_j c_j ∫ T(f₀, T_{σ₂ⱼ} f₁, T_{σ₃ⱼ} f₂)‖ ≲ CT ∏ ‖f_k‖` (random-sign decoupling over the `2^{#js}`
  sign patterns, then Hölder and the strong bounds of V08 for each fixed pattern).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate Real ContDiff
open PrimeBHT.Statements PrimeBHT.TimeFrequency.X2.CZ

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-! ## Hölder for three factors -/

theorem eLpNorm_ofReal_eq_lintegral {p : ℝ} (hp : 0 < p) {a : ℝ → ℝ≥0∞} (ha : Measurable a) :
    eLpNorm a (ENNReal.ofReal p) volume = (∫⁻ x, a x ^ p) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top
    ha.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  simp only [enorm_eq_self]

theorem lintegral_mul_three_le {p₀ p₁ p₂ : ℝ} (h₀ : 0 < p₀) (h₁ : 0 < p₁) (h₂ : 0 < p₂)
    (hsum : 1 / p₀ + 1 / p₁ + 1 / p₂ = 1)
    {a b c : ℝ → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    ∫⁻ x, a x * b x * c x ≤ eLpNorm a (ENNReal.ofReal p₀) volume * eLpNorm b (ENNReal.ofReal p₁) volume *
      eLpNorm c (ENNReal.ofReal p₂) volume := by
  rw [eLpNorm_ofReal_eq_lintegral h₀ ha, eLpNorm_ofReal_eq_lintegral h₁ hb,
    eLpNorm_ofReal_eq_lintegral h₂ hc]
  have key := ENNReal.lintegral_prod_norm_pow_le (μ := (volume : Measure ℝ)) (Finset.univ : Finset (Fin 3))
    (f := ![fun x => a x ^ p₀, fun x => b x ^ p₁, fun x => c x ^ p₂])
    (p := ![1 / p₀, 1 / p₁, 1 / p₂]) (by
      intro i _
      fin_cases i
      · exact (ha.pow_const p₀).aemeasurable
      · exact (hb.pow_const p₁).aemeasurable
      · exact (hc.pow_const p₂).aemeasurable)
    (by simpa [Fin.sum_univ_three] using hsum)
    (by intro i _; fin_cases i <;> simp <;> positivity)
  simp only [Fin.prod_univ_three] at key
  simp only [one_div, ENNReal.rpow_rpow_inv h₀.ne', ENNReal.rpow_rpow_inv h₁.ne', ENNReal.rpow_rpow_inv h₂.ne',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at key
  simpa [one_div] using key

/-! ## The Hilbert-slot square function -/

section Square

variable {P : ℕ} [NeZero P]

theorem yNorm_two_sq (F : ZMod P → ℂ) : yNorm 2 F ^ 2 = (P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ 2 := by
  have h := yNorm_rpow_self (P := P) (s := 2) (by norm_num) F
  simpa [Real.rpow_two] using h

theorem yNorm_two_latticeSquare {N : ℕ} (h : Fin N → ZMod P → ℂ) :
    yNorm 2 (fun y => ((latticeSquare h y : ℝ) : ℂ)) = Real.sqrt (∑ i, yNorm 2 (h i) ^ 2) := by
  have hsq : yNorm 2 (fun y => ((latticeSquare h y : ℝ) : ℂ)) ^ 2 = ∑ i, yNorm 2 (h i) ^ 2 := by
    rw [yNorm_two_sq]
    have e : ∀ y, ‖((latticeSquare h y : ℝ) : ℂ)‖ ^ 2 = ∑ i, ‖h i y‖ ^ 2 := by
      intro y
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      unfold latticeSquare
      rw [show ((2 : ℝ)⁻¹) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
        Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
    simp_rw [e]
    simp_rw [yNorm_two_sq, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [← hsq, Real.sqrt_sq (yNorm_nonneg 2 _)]

/-- **Square function bound (V08(d), upper half) for a finite set of integer indices.** -/
theorem square_bound {q C : ℝ} (hC : VectorMikhlinSquare 3 q 2 C) (js : Finset ℤ) (n : ℤ → ℝ → ℂ) {B : ℝ}
    (hB : ∀ η : ℤ → ℂ, (∀ j, ‖η j‖ ≤ 1) → IsMikhlin 3 B (fun ξ => ∑ j ∈ js, η j * n j ξ))
    (f : ZMod P → 𝓢(ℝ, ℂ)) :
    eLpNorm (fun x => Real.sqrt (∑ j ∈ js, yNorm 2 (tensorMult (n j) f x) ^ 2)) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (C * B) * mixedENorm q 2 (tensorFun f) := by
  classical
  set N := js.card with hN
  set e : js ≃ Fin N := js.equivFin with he
  set n' : Fin N → ℝ → ℂ := fun i => n ((e.symm i : js) : ℤ) with hn'
  have hsum_eq : ∀ (g : ℤ → ℝ → ℂ) (ξ : ℝ) (η : Fin N → ℂ),
      ∑ i : Fin N, η i * g ((e.symm i : js) : ℤ) ξ =
        ∑ j ∈ js, (if h : j ∈ js then η (e ⟨j, h⟩) else 0) * g j ξ := by
    intro g ξ η
    rw [← Finset.sum_coe_sort js (fun j => (if h : j ∈ js then η (e ⟨j, h⟩) else 0) * g j ξ)]
    rw [← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [(e.symm j).2]
  have hη : ∀ η : Fin N → ℂ, (∀ j, ‖η j‖ = 1) → IsMikhlin 3 B (fun ξ => ∑ j, η j * n' j ξ) := by
    intro η hη1
    have := hB (fun j => if h : j ∈ js then η (e ⟨j, h⟩) else 0) (fun j => by
      by_cases h : j ∈ js
      · simp [h, hη1]
      · simp [h])
    have e2 : (fun ξ => ∑ j, η j * n' j ξ) =
        fun ξ => ∑ j ∈ js, (if h : j ∈ js then η (e ⟨j, h⟩) else 0) * n j ξ :=
      funext fun ξ => hsum_eq n ξ η
    rw [e2]
    exact this
  have key := hC P N n' B hη f
  have hpt : ∀ x, yNorm 2 (fun y => ((latticeSquare (fun i => tensorMult (n' i) f x) y : ℝ) : ℂ)) =
      Real.sqrt (∑ j ∈ js, yNorm 2 (tensorMult (n j) f x) ^ 2) := by
    intro x
    rw [yNorm_two_latticeSquare]
    congr 1
    rw [← Finset.sum_coe_sort js (fun j => yNorm 2 (tensorMult (n j) f x) ^ 2)]
    rw [← Equiv.sum_comp e.symm]
  simp only [hpt] at key
  exact key

end Square

/-! ## Measurability and elementary inequalities -/

theorem measurable_tensorFun {P : ℕ} [NeZero P] (F : TS P) : Measurable (tensorFun F) := by
  refine measurable_pi_iff.2 fun y => ?_
  have : Continuous fun x => tensorFun F x y := by
    unfold tensorFun
    exact continuous_finsetSum _ fun A _ => (F A).continuous.mul continuous_const
  exact this.measurable

theorem measurable_yNorm_tensorFun {P : ℕ} [NeZero P] (s : ℝ) (F : TS P) :
    Measurable fun x => yNorm s (tensorFun F x) :=
  (measurable_yNorm_fun s).comp (measurable_tensorFun F)

theorem eLpNorm_ofReal_real (q : ℝ) {g : ℝ → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) :
    eLpNorm (fun x => ENNReal.ofReal (g x)) (ENNReal.ofReal q) volume =
      eLpNorm g (ENNReal.ofReal q) volume := by
  refine eLpNorm_congr_enorm_ae hg.ennreal_ofReal.aestronglyMeasurable hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [enorm_eq_self, Real.enorm_eq_ofReal (hg0 z)]

theorem sum_mul_le_sqrt_mul_sqrt' {ι : Type*} (js : Finset ι) (a b : ι → ℝ) :
    ∑ j ∈ js, a j * b j ≤ Real.sqrt (∑ j ∈ js, a j ^ 2) * Real.sqrt (∑ j ∈ js, b j ^ 2) := by
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  apply Real.le_sqrt_of_sq_le
  exact Finset.sum_mul_sq_le_sq_mul_sq js a b

theorem sum_ofReal_le {ι : Type*} (js : Finset ι) (CT K : ℝ) (hCT : 0 ≤ CT) (a b c : ι → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (Mx : ℝ≥0∞)
    (hcM : ∀ j, ENNReal.ofReal (c j) ≤ ENNReal.ofReal K * Mx) :
    ∑ j ∈ js, ENNReal.ofReal (CT * a j * b j * c j) ≤
      ENNReal.ofReal CT * (ENNReal.ofReal (Real.sqrt (∑ j ∈ js, a j ^ 2)) *
        ENNReal.ofReal (Real.sqrt (∑ j ∈ js, b j ^ 2))) * (ENNReal.ofReal K * Mx) := by
  calc ∑ j ∈ js, ENNReal.ofReal (CT * a j * b j * c j)
      = ∑ j ∈ js, ENNReal.ofReal (CT * a j * b j) * ENNReal.ofReal (c j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCT (ha j)) (hb j))]
    _ ≤ ∑ j ∈ js, ENNReal.ofReal (CT * a j * b j) * (ENNReal.ofReal K * Mx) :=
        Finset.sum_le_sum fun j _ => by gcongr; exact hcM j
    _ = ENNReal.ofReal (CT * ∑ j ∈ js, a j * b j) * (ENNReal.ofReal K * Mx) := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg
          (fun j _ => mul_nonneg (mul_nonneg hCT (ha j)) (hb j)), Finset.mul_sum]
        congr 2
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ ENNReal.ofReal (CT * (Real.sqrt (∑ j ∈ js, a j ^ 2) * Real.sqrt (∑ j ∈ js, b j ^ 2))) *
          (ENNReal.ofReal K * Mx) := by
        gcongr
        exact sum_mul_le_sqrt_mul_sqrt' js a b
    _ = _ := by
        rw [ENNReal.ofReal_mul hCT, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

theorem nonneg_of_formBound {P : ℕ} [NeZero P] {u CT : ℝ} (hu : 0 < u) {T : Form P} (hT : FormBound u T CT) :
    0 ≤ CT := by
  by_contra h
  exact not_bound_of_neg T hu (not_le.1 h) hT

/-! ## The error estimate (V14 Step 2) -/

section Error

variable {P : ℕ} [NeZero P]

/-- **Step 2 of the V14 route (all-lacunary comparable terms)**: Cauchy-Schwarz in `j` with the two Hilbert
slots in `ℓ²_j` (square functions `square_bound`) and the `X_u` slot bounded pointwise by the maximal function. -/
theorem enorm_sum_triL_le {A : ℝ} (hA : 0 < A) {J : ℕ} {u CT : ℝ} (hu : 1 < u) {T : Form P}
    (hT : FormBound u T CT) {p₀ p₁ p₂ : ℝ} (hp₀ : 1 < p₀) (hp₁ : 1 < p₁) (hp₂ : 1 < p₂)
    (hsum : 1 / p₀ + 1 / p₁ + 1 / p₂ = 1) {Cs₀ Cs₁ : ℝ} (hS₀ : VectorMikhlinSquare 3 p₀ 2 Cs₀)
    (hS₁ : VectorMikhlinSquare 3 p₁ 2 Cs₁) (js : Finset ℤ) (ε : ℤ → ℂ) (hε : ∀ j, ‖ε j‖ ≤ 1)
    (n σ₂ σ₃ : ℤ → ℝ → ℂ) (hn : ∀ j, (n j).HasTemperateGrowth) (hσ₂ : ∀ j, (σ₂ j).HasTemperateGrowth)
    (hσ₃ : ∀ j, IsAdaptedSymbol A J j (σ₃ j)) {B₁ B₂ : ℝ}
    (hB₁ : ∀ η : ℤ → ℂ, (∀ j, ‖η j‖ ≤ 1) → IsMikhlin 3 B₁ (fun ξ => ∑ j ∈ js, η j * n j ξ))
    (hB₂ : ∀ η : ℤ → ℂ, (∀ j, ‖η j‖ ≤ 1) → IsMikhlin 3 B₂ (fun ξ => ∑ j ∈ js, η j * σ₂ j ξ))
    (f₀ f₁ f₂ : TS P) :
    ‖∑ j ∈ js, ε j * triL T (tmS (n j) f₀) (tmS (σ₂ j) f₁) (tmS (σ₃ j) f₂)‖ₑ ≤
      ENNReal.ofReal CT * ENNReal.ofReal (Cs₀ * B₁) * ENNReal.ofReal (Cs₁ * B₂) *
        ENNReal.ofReal (60 * (2 : ℝ) ^ (2 * J)) *
        (PrimeCarleson.Proof.Common.maximalHLRConst (ENNReal.ofReal p₂) : ℝ≥0∞) *
        mixedENorm p₀ 2 (tensorFun f₀) * mixedENorm p₁ 2 (tensorFun f₁) * mixedENorm p₂ u (tensorFun f₂) := by
  have hCT : 0 ≤ CT := nonneg_of_formBound (by linarith) hT
  have hσ₃t : ∀ j, (σ₃ j).HasTemperateGrowth := fun j =>
    (hσ₃ j).hasCompactSupport.hasTemperateGrowth (hσ₃ j).1
  have hV : ∀ j x, tensorFun (tmS (n j) f₀) x = tensorMult (n j) f₀ x := fun j x => by
    rw [tensorMult_eq_tensorFun (hn j)]
  have hW : ∀ j x, tensorFun (tmS (σ₂ j) f₁) x = tensorMult (σ₂ j) f₁ x := fun j x => by
    rw [tensorMult_eq_tensorFun (hσ₂ j)]
  have hX : ∀ j x, tensorFun (tmS (σ₃ j) f₂) x = tmult (σ₃ j) (tensorFun f₂) x := fun j x => by
    rw [tmult_tensorFun (hσ₃ j).1 (hσ₃ j).hasCompactSupport, tensorMult_eq_tensorFun (hσ₃t j)]
  set K : ℝ := 60 * (2 : ℝ) ^ (2 * J) with hK
  set M : ℝ → ℝ≥0∞ := fun x => PrimeCarleson.Proof.Common.maximalHLR
    (fun z => ENNReal.ofReal (yNorm u (tensorFun f₂ z))) x with hM
  set sa : ℝ → ℝ := fun x => Real.sqrt (∑ j ∈ js, yNorm 2 (tensorMult (n j) f₀ x) ^ 2) with hsa
  set sb : ℝ → ℝ := fun x => Real.sqrt (∑ j ∈ js, yNorm 2 (tensorMult (σ₂ j) f₁ x) ^ 2) with hsb
  have hsa_m : Measurable sa := by
    refine Real.continuous_sqrt.measurable.comp (Finset.measurable_sum _ fun j _ => ?_)
    have := measurable_yNorm_tensorFun (P := P) 2 (tmS (n j) f₀)
    simp only [hV] at this
    exact this.pow_const 2
  have hsb_m : Measurable sb := by
    refine Real.continuous_sqrt.measurable.comp (Finset.measurable_sum _ fun j _ => ?_)
    have := measurable_yNorm_tensorFun (P := P) 2 (tmS (σ₂ j) f₁)
    simp only [hW] at this
    exact this.pow_const 2
  have hM_m : Measurable M := PrimeCarleson.Proof.Common.measurable_maximalHLR _
  -- pointwise bound of the sum
  have hpt : ∀ x, ∑ j ∈ js, ENNReal.ofReal (CT * yNorm 2 (tensorFun (tmS (n j) f₀) x) *
        yNorm 2 (tensorFun (tmS (σ₂ j) f₁) x) * yNorm u (tensorFun (tmS (σ₃ j) f₂) x)) ≤
      ENNReal.ofReal CT * (ENNReal.ofReal (sa x) * ENNReal.ofReal (sb x)) * (ENNReal.ofReal K * M x) := by
    intro x
    simp only [hV, hW, hX]
    refine sum_ofReal_le js CT K hCT _ _ _ (fun j => yNorm_nonneg' _ _) (fun j => yNorm_nonneg' _ _) (M x)
      (fun j => ?_)
    exact ofReal_yNorm_tmult_le_adapted hA (hσ₃ j) hu.le (measurable_tensorFun f₂) x
  have hsa_nn : ∀ x, 0 ≤ sa x := fun x => Real.sqrt_nonneg _
  have hsb_nn : ∀ x, 0 ≤ sb x := fun x => Real.sqrt_nonneg _
  have h1 : eLpNorm (fun x => ENNReal.ofReal (sa x)) (ENNReal.ofReal p₀) volume ≤
      ENNReal.ofReal (Cs₀ * B₁) * mixedENorm p₀ 2 (tensorFun f₀) := by
    rw [eLpNorm_ofReal_real p₀ hsa_m hsa_nn]
    exact square_bound hS₀ js n hB₁ f₀
  have h2 : eLpNorm (fun x => ENNReal.ofReal (sb x)) (ENNReal.ofReal p₁) volume ≤
      ENNReal.ofReal (Cs₁ * B₂) * mixedENorm p₁ 2 (tensorFun f₁) := by
    rw [eLpNorm_ofReal_real p₁ hsb_m hsb_nn]
    exact square_bound hS₁ js σ₂ hB₂ f₁
  have h3 : eLpNorm M (ENNReal.ofReal p₂) volume ≤
      (PrimeCarleson.Proof.Common.maximalHLRConst (ENNReal.ofReal p₂) : ℝ≥0∞) *
        mixedENorm p₂ u (tensorFun f₂) :=
    eLpNorm_maximal_yNorm_le hp₂ u (measurable_tensorFun f₂)
  calc ‖∑ j ∈ js, ε j * triL T (tmS (n j) f₀) (tmS (σ₂ j) f₁) (tmS (σ₃ j) f₂)‖ₑ
      ≤ ∑ j ∈ js, ‖ε j * triL T (tmS (n j) f₀) (tmS (σ₂ j) f₁) (tmS (σ₃ j) f₂)‖ₑ := enorm_sum_le _ _
    _ ≤ ∑ j ∈ js, ‖triL T (tmS (n j) f₀) (tmS (σ₂ j) f₁) (tmS (σ₃ j) f₂)‖ₑ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [enorm_mul]
        exact mul_le_of_le_one_left zero_le (by rw [← ofReal_norm]; exact ENNReal.ofReal_le_one.2 (hε j))
    _ ≤ ∑ j ∈ js, ∫⁻ x, ENNReal.ofReal (CT * yNorm 2 (tensorFun (tmS (n j) f₀) x) *
          yNorm 2 (tensorFun (tmS (σ₂ j) f₁) x) * yNorm u (tensorFun (tmS (σ₃ j) f₂) x)) :=
        Finset.sum_le_sum fun j _ => enorm_triL_le T hT _ _ _
    _ = ∫⁻ x, ∑ j ∈ js, ENNReal.ofReal (CT * yNorm 2 (tensorFun (tmS (n j) f₀) x) *
          yNorm 2 (tensorFun (tmS (σ₂ j) f₁) x) * yNorm u (tensorFun (tmS (σ₃ j) f₂) x)) := by
        rw [lintegral_finsetSum]
        intro j _
        refine ENNReal.measurable_ofReal.comp ?_
        exact (((measurable_const.mul (measurable_yNorm_tensorFun 2 _)).mul
          (measurable_yNorm_tensorFun 2 _)).mul (measurable_yNorm_tensorFun u _))
    _ ≤ ∫⁻ x, ENNReal.ofReal CT * (ENNReal.ofReal (sa x) * ENNReal.ofReal (sb x)) *
          (ENNReal.ofReal K * M x) := lintegral_mono hpt
    _ = (ENNReal.ofReal CT * ENNReal.ofReal K) * ∫⁻ x, ENNReal.ofReal (sa x) * ENNReal.ofReal (sb x) * M x := by
        rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
        refine lintegral_congr fun x => ?_
        ring
    _ ≤ (ENNReal.ofReal CT * ENNReal.ofReal K) *
          (eLpNorm (fun x => ENNReal.ofReal (sa x)) (ENNReal.ofReal p₀) volume *
            eLpNorm (fun x => ENNReal.ofReal (sb x)) (ENNReal.ofReal p₁) volume *
            eLpNorm M (ENNReal.ofReal p₂) volume) := by
        gcongr
        exact lintegral_mul_three_le (by linarith) (by linarith) (by linarith) hsum
          hsa_m.ennreal_ofReal hsb_m.ennreal_ofReal hM_m
    _ ≤ (ENNReal.ofReal CT * ENNReal.ofReal K) *
          ((ENNReal.ofReal (Cs₀ * B₁) * mixedENorm p₀ 2 (tensorFun f₀)) *
            (ENNReal.ofReal (Cs₁ * B₂) * mixedENorm p₁ 2 (tensorFun f₁)) *
            ((PrimeCarleson.Proof.Common.maximalHLRConst (ENNReal.ofReal p₂) : ℝ≥0∞) *
              mixedENorm p₂ u (tensorFun f₂))) := by
        gcongr
    _ = _ := by ring

end Error

/-! ## Sign patterns and the decoupling lemma (V14 Step 4) -/

/-- The sign pattern attached to a subset `U`: `+1` on `U`, `-1` off `U`. -/
def sgnU (U : Finset ℤ) (j : ℤ) : ℝ := if j ∈ U then 1 else -1

theorem sgnU_sq (U : Finset ℤ) (j : ℤ) : sgnU U j * sgnU U j = 1 := by
  unfold sgnU; split_ifs <;> norm_num

/-- Flip the membership of `j` in `U`. -/
def flipU (j : ℤ) (U : Finset ℤ) : Finset ℤ := if j ∈ U then U.erase j else insert j U

theorem flipU_flipU (j : ℤ) (U : Finset ℤ) : flipU j (flipU j U) = U := by
  unfold flipU
  by_cases h : j ∈ U
  · simp [h, Finset.insert_erase h]
  · simp [h]

theorem sgnU_flipU_self (j : ℤ) (U : Finset ℤ) : sgnU (flipU j U) j = - sgnU U j := by
  unfold sgnU flipU
  by_cases h : j ∈ U <;> simp [h]

theorem sgnU_flipU_ne {j k : ℤ} (hjk : k ≠ j) (U : Finset ℤ) : sgnU (flipU j U) k = sgnU U k := by
  unfold sgnU flipU
  by_cases h : j ∈ U <;> simp [h, hjk]

theorem flipU_mem_powerset {js U : Finset ℤ} {j : ℤ} (hj : j ∈ js) (hU : U ∈ js.powerset) :
    flipU j U ∈ js.powerset := by
  rw [Finset.mem_powerset] at hU ⊢
  unfold flipU
  split_ifs
  · exact (Finset.erase_subset _ _).trans hU
  · exact Finset.insert_subset hj hU

theorem sum_sgnU_mul (js : Finset ℤ) {j k : ℤ} (hj : j ∈ js) :
    ∑ U ∈ js.powerset, sgnU U j * sgnU U k = if j = k then (2 : ℝ) ^ js.card else 0 := by
  by_cases hjk : j = k
  · subst hjk
    simp [sgnU_sq, Finset.card_powerset]
  · simp only [hjk, ↓reduceIte]
    refine Finset.sum_involution (fun U _ => flipU j U) ?_ ?_ ?_ ?_
    · intro U hU
      rw [sgnU_flipU_self, sgnU_flipU_ne (Ne.symm hjk)]
      ring
    · intro U hU hne heq
      have := congrArg (fun V => sgnU V j) heq
      simp only [sgnU_flipU_self] at this
      have h1 : sgnU U j = 1 ∨ sgnU U j = -1 := by unfold sgnU; split_ifs <;> simp
      rcases h1 with h1 | h1 <;> rw [h1] at this <;> norm_num at this
    · intro U hU
      exact flipU_mem_powerset hj hU
    · intro U hU
      exact flipU_flipU j U

section Decouple

variable {P : ℕ} [NeZero P]

/-- Hölder bound of the trilinear form: `‖∫ T(F, G, H)‖ ≤ CT ‖F‖_{L^{p₀}(H)} ‖G‖_{L^{p₁}(H)} ‖H‖_{L^{p₂}(X_u)}`. -/
theorem enorm_triL_holder_le {u CT : ℝ} (hu : 0 < u) {T : Form P} (hT : FormBound u T CT)
    {p₀ p₁ p₂ : ℝ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hsum : 1 / p₀ + 1 / p₁ + 1 / p₂ = 1)
    (F G H : TS P) :
    ‖triL T F G H‖ₑ ≤ ENNReal.ofReal CT * (mixedENorm p₀ 2 (tensorFun F) * mixedENorm p₁ 2 (tensorFun G) *
      mixedENorm p₂ u (tensorFun H)) := by
  have hCT : 0 ≤ CT := nonneg_of_formBound hu hT
  refine (enorm_triL_le T hT F G H).trans ?_
  have hpt : ∀ x, ENNReal.ofReal (CT * yNorm 2 (tensorFun F x) * yNorm 2 (tensorFun G x) *
      yNorm u (tensorFun H x)) = ENNReal.ofReal CT * (ENNReal.ofReal (yNorm 2 (tensorFun F x)) *
        ENNReal.ofReal (yNorm 2 (tensorFun G x)) * ENNReal.ofReal (yNorm u (tensorFun H x))) := by
    intro x
    rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCT (yNorm_nonneg' _ _)) (yNorm_nonneg' _ _)),
      ENNReal.ofReal_mul (mul_nonneg hCT (yNorm_nonneg' _ _)), ENNReal.ofReal_mul hCT]
    ring
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  gcongr
  refine (lintegral_mul_three_le hp₀ hp₁ hp₂ hsum
    (measurable_yNorm_tensorFun 2 F).ennreal_ofReal (measurable_yNorm_tensorFun 2 G).ennreal_ofReal
    (measurable_yNorm_tensorFun u H).ennreal_ofReal).trans ?_
  unfold mixedENorm
  rw [eLpNorm_ofReal_real p₀ (measurable_yNorm_tensorFun 2 F) (fun x => yNorm_nonneg' _ _),
    eLpNorm_ofReal_real p₁ (measurable_yNorm_tensorFun 2 G) (fun x => yNorm_nonneg' _ _),
    eLpNorm_ofReal_real p₂ (measurable_yNorm_tensorFun u H) (fun x => yNorm_nonneg' _ _)]

theorem triL_bilinear_sum (T : Form P) (F : TS P) (js : Finset ℤ) (a b : ℤ → ℂ) (X Y : ℤ → TS P) :
    triL T F (∑ j ∈ js, a j • X j) (∑ k ∈ js, b k • Y k) =
      ∑ j ∈ js, ∑ k ∈ js, a j * (starRingEnd ℂ) (b k) * triL T F (X j) (Y k) := by
  simp only [map_sum, LinearMap.sum_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **The random-sign identity** (`E[η_j η_k] = δ_{jk}` for the `2^{#js}` sign patterns): the diagonal sum
`Σ_j c_j T(f₀, S_j f₁, S_j f₂)` equals the average over sign patterns `U` of `T(f₀, Σ_j η_j S_j f₁, Σ_k λ_k S_k f₂)`
with `η_j = sgn_U(j)`, `λ_k = sgn_U(k) conj(c_k)` (slot 3 is conjugate-linear). -/
theorem sum_sign_triL (T : Form P) (f₀ f₁ f₂ : TS P) (js : Finset ℤ) (c : ℤ → ℂ) (σ₂ σ₃ : ℤ → ℝ → ℂ)
    (hσ₂ : ∀ j, (σ₂ j).HasTemperateGrowth) (hσ₃ : ∀ j, (σ₃ j).HasTemperateGrowth) :
    ∑ U ∈ js.powerset, triL T f₀
        (tmS (fun ξ => ∑ j ∈ js, ((sgnU U j : ℝ) : ℂ) * σ₂ j ξ) f₁)
        (tmS (fun ξ => ∑ k ∈ js, (((sgnU U k : ℝ) : ℂ) * (starRingEnd ℂ) (c k)) * σ₃ k ξ) f₂) =
      (((2 : ℝ) ^ js.card : ℝ) : ℂ) * ∑ j ∈ js, c j * triL T f₀ (tmS (σ₂ j) f₁) (tmS (σ₃ j) f₂) := by
  classical
  have hU : ∀ U : Finset ℤ, triL T f₀
        (tmS (fun ξ => ∑ j ∈ js, ((sgnU U j : ℝ) : ℂ) * σ₂ j ξ) f₁)
        (tmS (fun ξ => ∑ k ∈ js, (((sgnU U k : ℝ) : ℂ) * (starRingEnd ℂ) (c k)) * σ₃ k ξ) f₂) =
      ∑ j ∈ js, ∑ k ∈ js, (((sgnU U j * sgnU U k : ℝ) : ℂ)) *
        (c k * triL T f₀ (tmS (σ₂ j) f₁) (tmS (σ₃ k) f₂)) := by
    intro U
    rw [tmS_sum js _ _ (fun j _ => hσ₂ j), tmS_sum js _ _ (fun j _ => hσ₃ j), triL_bilinear_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
    push_cast
    ring
  simp_rw [hU]
  set w : ℤ → ℤ → ℂ := fun j k => c k * triL T f₀ (tmS (σ₂ j) f₁) (tmS (σ₃ k) f₂) with hw
  calc ∑ U ∈ js.powerset, ∑ j ∈ js, ∑ k ∈ js, (((sgnU U j * sgnU U k : ℝ) : ℂ)) * w j k
      = ∑ j ∈ js, ∑ k ∈ js, (∑ U ∈ js.powerset, (((sgnU U j * sgnU U k : ℝ) : ℂ))) * w j k := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ j ∈ js, ∑ k ∈ js, (if j = k then (((2 : ℝ) ^ js.card : ℝ) : ℂ) else 0) * w j k := by
        refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k _ => ?_
        rw [← Complex.ofReal_sum, sum_sgnU_mul js hj]
        split_ifs <;> simp
    _ = (((2 : ℝ) ^ js.card : ℝ) : ℂ) * ∑ j ∈ js, c j * triL T f₀ (tmS (σ₂ j) f₁) (tmS (σ₃ j) f₂) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq, hj, ↓reduceIte, hw]

theorem hasTemperateGrowth_sum_mul {ι : Type*} (js : Finset ι) (a : ι → ℂ) {σ : ι → ℝ → ℂ}
    (hσ : ∀ j, (σ j).HasTemperateGrowth) : (fun ξ => ∑ j ∈ js, a j * σ j ξ).HasTemperateGrowth :=
  Function.HasTemperateGrowth.sum fun j _ => (Function.HasTemperateGrowth.const (a j)).mul (hσ j)

/-- **Step 4 of the V14 route (decoupling the lacunary pair, first slot pulled out)**: for every family of
coefficients `‖c_j‖ ≤ 1`,
`‖Σ_j c_j ∫ T(f₀, T_{σ₂ⱼ} f₁, T_{σ₃ⱼ} f₂)‖ ≤ CT ‖f₀‖_{L^{p₀}(H)} · C B₂ ‖f₁‖_{L^{p₁}(H)} · C B₃ ‖f₂‖_{L^{p₂}(X_u)}`. -/
theorem enorm_sum_triL_pull_le {u CT : ℝ} (hu : 1 < u) {T : Form P} (hT : FormBound u T CT)
    {p₀ p₁ p₂ : ℝ} (hp₀ : 0 < p₀) (hp₁ : 1 < p₁) (hp₂ : 1 < p₂) (hsum : 1 / p₀ + 1 / p₁ + 1 / p₂ = 1)
    {Cs₁ Cs₂ : ℝ} (hC₁ : VectorMikhlinStrong 3 p₁ 2 Cs₁) (hC₂ : VectorMikhlinStrong 3 p₂ u Cs₂)
    (js : Finset ℤ) (c : ℤ → ℂ) (hc : ∀ j, ‖c j‖ ≤ 1) (σ₂ σ₃ : ℤ → ℝ → ℂ)
    (hσ₂ : ∀ j, (σ₂ j).HasTemperateGrowth) (hσ₃ : ∀ j, (σ₃ j).HasTemperateGrowth) {B₂ B₃ : ℝ}
    (hB₂ : ∀ η : ℤ → ℂ, (∀ j, ‖η j‖ ≤ 1) → IsMikhlin 3 B₂ (fun ξ => ∑ j ∈ js, η j * σ₂ j ξ))
    (hB₃ : ∀ η : ℤ → ℂ, (∀ j, ‖η j‖ ≤ 1) → IsMikhlin 3 B₃ (fun ξ => ∑ j ∈ js, η j * σ₃ j ξ))
    (f₀ f₁ f₂ : TS P) :
    ‖∑ j ∈ js, c j * triL T f₀ (tmS (σ₂ j) f₁) (tmS (σ₃ j) f₂)‖ₑ ≤
      ENNReal.ofReal CT * (ENNReal.ofReal (Cs₁ * B₂) * ENNReal.ofReal (Cs₂ * B₃) *
        (mixedENorm p₀ 2 (tensorFun f₀) * mixedENorm p₁ 2 (tensorFun f₁) *
          mixedENorm p₂ u (tensorFun f₂))) := by
  classical
  set M₀ : ℝ≥0∞ := ENNReal.ofReal CT * (ENNReal.ofReal (Cs₁ * B₂) * ENNReal.ofReal (Cs₂ * B₃) *
        (mixedENorm p₀ 2 (tensorFun f₀) * mixedENorm p₁ 2 (tensorFun f₁) *
          mixedENorm p₂ u (tensorFun f₂))) with hM₀
  have hsgn : ∀ (U : Finset ℤ) (j : ℤ), ‖((sgnU U j : ℝ) : ℂ)‖ ≤ 1 := by
    intro U j
    rw [Complex.norm_real, Real.norm_eq_abs]
    unfold sgnU; split_ifs <;> simp
  have hη1 : ∀ (U : Finset ℤ) (j : ℤ), ‖((sgnU U j : ℝ) : ℂ)‖ ≤ 1 := hsgn
  have hlam1 : ∀ (U : Finset ℤ) (k : ℤ), ‖((sgnU U k : ℝ) : ℂ) * (starRingEnd ℂ) (c k)‖ ≤ 1 := by
    intro U k
    rw [norm_mul, Complex.norm_conj]
    calc ‖((sgnU U k : ℝ) : ℂ)‖ * ‖c k‖ ≤ 1 * 1 :=
          mul_le_mul (hsgn U k) (hc k) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hbound : ∀ U : Finset ℤ, ‖triL T f₀
        (tmS (fun ξ => ∑ j ∈ js, ((sgnU U j : ℝ) : ℂ) * σ₂ j ξ) f₁)
        (tmS (fun ξ => ∑ k ∈ js, (((sgnU U k : ℝ) : ℂ) * (starRingEnd ℂ) (c k)) * σ₃ k ξ) f₂)‖ₑ ≤ M₀ := by
    intro U
    set Sy₂ : ℝ → ℂ := fun ξ => ∑ j ∈ js, ((sgnU U j : ℝ) : ℂ) * σ₂ j ξ with hSy₂
    set Sy₃ : ℝ → ℂ := fun ξ => ∑ k ∈ js, (((sgnU U k : ℝ) : ℂ) * (starRingEnd ℂ) (c k)) * σ₃ k ξ with hSy₃
    have hSy₂t : Sy₂.HasTemperateGrowth := hasTemperateGrowth_sum_mul js _ hσ₂
    have hSy₃t : Sy₃.HasTemperateGrowth := hasTemperateGrowth_sum_mul js _ hσ₃
    have e₂ : mixedENorm p₁ 2 (tensorFun (tmS Sy₂ f₁)) ≤
        ENNReal.ofReal (Cs₁ * B₂) * mixedENorm p₁ 2 (tensorFun f₁) := by
      rw [← tensorMult_eq_tensorFun hSy₂t]
      exact hC₁ P B₂ Sy₂ (hB₂ _ (hη1 U)) f₁
    have e₃ : mixedENorm p₂ u (tensorFun (tmS Sy₃ f₂)) ≤
        ENNReal.ofReal (Cs₂ * B₃) * mixedENorm p₂ u (tensorFun f₂) := by
      rw [← tensorMult_eq_tensorFun hSy₃t]
      exact hC₂ P B₃ Sy₃ (hB₃ _ (hlam1 U)) f₂
    refine (enorm_triL_holder_le (by linarith) hT hp₀ (by linarith) (by linarith) hsum _ _ _).trans ?_
    rw [hM₀]
    refine mul_le_mul' le_rfl ?_
    calc mixedENorm p₀ 2 (tensorFun f₀) * mixedENorm p₁ 2 (tensorFun (tmS Sy₂ f₁)) *
          mixedENorm p₂ u (tensorFun (tmS Sy₃ f₂))
        ≤ mixedENorm p₀ 2 (tensorFun f₀) * (ENNReal.ofReal (Cs₁ * B₂) * mixedENorm p₁ 2 (tensorFun f₁)) *
          (ENNReal.ofReal (Cs₂ * B₃) * mixedENorm p₂ u (tensorFun f₂)) := by gcongr
      _ = _ := by ring
  have hid := sum_sign_triL T f₀ f₁ f₂ js c σ₂ σ₃ hσ₂ hσ₃
  set S := ∑ j ∈ js, c j * triL T f₀ (tmS (σ₂ j) f₁) (tmS (σ₃ j) f₂) with hS
  have hN0 : ENNReal.ofReal ((2 : ℝ) ^ js.card) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hNtop : ENNReal.ofReal ((2 : ℝ) ^ js.card) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← ENNReal.mul_le_mul_iff_right hN0 hNtop]
  have hcard : ENNReal.ofReal ((2 : ℝ) ^ js.card) = (js.powerset.card : ℝ≥0∞) := by
    rw [Finset.card_powerset, ENNReal.ofReal_pow (by norm_num)]
    simp
  calc ENNReal.ofReal ((2 : ℝ) ^ js.card) * ‖S‖ₑ
      = ‖(((2 : ℝ) ^ js.card : ℝ) : ℂ) * S‖ₑ := by
        rw [enorm_mul, ← ofReal_norm (((2 : ℝ) ^ js.card : ℝ) : ℂ), Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
    _ = ‖∑ U ∈ js.powerset, triL T f₀
        (tmS (fun ξ => ∑ j ∈ js, ((sgnU U j : ℝ) : ℂ) * σ₂ j ξ) f₁)
        (tmS (fun ξ => ∑ k ∈ js, (((sgnU U k : ℝ) : ℂ) * (starRingEnd ℂ) (c k)) * σ₃ k ξ) f₂)‖ₑ := by
        rw [hid]
    _ ≤ ∑ U ∈ js.powerset, ‖triL T f₀
        (tmS (fun ξ => ∑ j ∈ js, ((sgnU U j : ℝ) : ℂ) * σ₂ j ξ) f₁)
        (tmS (fun ξ => ∑ k ∈ js, (((sgnU U k : ℝ) : ℂ) * (starRingEnd ℂ) (c k)) * σ₃ k ξ) f₂)‖ₑ :=
        enorm_sum_le _ _
    _ ≤ ∑ U ∈ js.powerset, M₀ := Finset.sum_le_sum fun U _ => hbound U
    _ = ENNReal.ofReal ((2 : ℝ) ^ js.card) * M₀ := by
        rw [Finset.sum_const, hcard]; simp

end Decouple

end PrimeBHT.TimeFrequency.X2
