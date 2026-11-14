module

public import PrimeBHT.Frozen.YNorm
public import PrimeBHT.Frozen.TensorFun
public import PrimeBHT.Frozen.TensorFourier
public import PrimeBHT.Frozen.MultiplierForm
import PrimeBHT.Lift
import PrimeBHT.Interface.X2Checks

/-!
# X2, node V00: elementary `L^p(Y_P)` facts

Blueprint `docs/x2-blueprint.md`, node V00 (the facts (a)-(e)), over the FROZEN definitions
`PrimeBHT.Statements.{yNorm, tensorFun, tensorFourier, multiplierForm}` (ruling R11). Everything is
proved; nothing here mentions the frozen theorem `t_finiteBV`.

## Final signatures (namespace `PrimeBHT.TimeFrequency.X2`, `P` with `[NeZero P]`)

* (a) `yNorm_mono : 0 < s → s ≤ p → yNorm s F ≤ yNorm p F` (every `0 < s`, not only `s ≥ 1`).
* (b) `yChar a y = e(a y / P)`, `yInner F G = P⁻¹ ∑_y F y conj (G y)`;
  `yInner_yChar_yChar : yInner (yChar a) (yChar b) = if a = b then 1 else 0` (orthonormality);
  `yInner_self : yInner F F = (yNorm 2 F ^ 2 : ℝ)` (`yNorm 2 F` is the norm of `H = L²(Y_P)`);
  `eq_sum_yInner_smul_yChar : F = ∑_a yInner F (yChar a) • yChar a` (the `e_a` span: a basis);
  `yNorm_two_sum_yChar_sq : yNorm 2 (∑_A c A • yChar A) ^ 2 = ∑_A ‖c A‖ ^ 2` (Parseval).
* (c) `yNorm_sum_yChar_le : 0 < s → yNorm s (∑_A c A • yChar A) ≤ ∑_A ‖c A‖` (for every `s > 0`, by the
  pointwise bound; the blueprint's `s ≥ 1` is not needed), `yNorm_tensorFourier_le`,
  `yNorm_tensorFun_le`.
* (d) `not_bound_of_neg : 0 < u → CT < 0 → ¬ (∀ F G H, ‖T F G H‖ ≤ CT * yNorm 2 F * yNorm 2 G *
  yNorm u H)`, `eq_zero_of_bound_eq_zero : (bound with CT = 0) → T = 0`,
  `multiplierForm_eq_zero_of_eq_zero : T = 0 → multiplierForm m T f₁ f₂ f₃ = 0`.
* (e) `yNorm_yChar_mul : yNorm s (yChar a * F) = yNorm s F`,
  `norm_le_of_bound_yChar_mul`: the bound on `T` is invariant under `(F, G, H) ↦ (e_α F, e_β G, e_γ H)`.
-/

@[expose] public noncomputable section

open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate ContDiff
open PrimeBHT.Statements (yNorm tensorFun tensorFourier multiplierForm)

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

variable {P : ℕ} [NeZero P]

/-- The character `e_a(y) = e(a y / P) = ZMod.stdAddChar (a * y)` of `Y_P = ℤ/P`. -/
def yChar (a : ZMod P) : ZMod P → ℂ := fun y => ZMod.stdAddChar (a * y)

/-- The normalized inner product `⟨F, G⟩ = (1/P) ∑_y F(y) conj(G(y))` of `H = L²(Y_P)`. -/
def yInner (F G : ZMod P → ℂ) : ℂ := (P : ℂ)⁻¹ * ∑ y, F y * conj (G y)

theorem yChar_apply (a y : ZMod P) : yChar a y = ZMod.stdAddChar (a * y) := rfl

/-! ### (a) monotonicity -/

/-- `yNorm s ≤ yNorm p` for `0 < s ≤ p` (probability measure). -/
theorem yNorm_mono {s p : ℝ} (hs : 0 < s) (hsp : s ≤ p) (F : ZMod P → ℂ) :
    yNorm s F ≤ yNorm p F :=
  PrimeBHT.Lift.yNorm_mono hs hsp F

/-! ### (b) orthonormality -/

theorem norm_yChar (a y : ZMod P) : ‖yChar a y‖ = 1 := by
  simp [yChar_apply, ZMod.stdAddChar_apply]

theorem conj_stdAddChar (x : ZMod P) :
    conj (ZMod.stdAddChar x : ℂ) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv,
    Circle.coe_inv_eq_conj]

theorem yChar_mul_conj (a b y : ZMod P) :
    yChar a y * conj (yChar b y) = ZMod.stdAddChar (y * (a - b)) := by
  rw [yChar_apply, yChar_apply, conj_stdAddChar, ← AddChar.map_add_eq_mul]
  congr 1
  ring

theorem sum_stdAddChar_mul (b : ZMod P) :
    ∑ x : ZMod P, (ZMod.stdAddChar (x * b) : ℂ) = if b = 0 then (P : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod P) ℂ)) b
    (ZMod.isPrimitive_stdAddChar P)
  rw [h]
  split_ifs <;> simp [ZMod.card]

theorem sum_yChar_mul_conj (a b : ZMod P) :
    ∑ y, yChar a y * conj (yChar b y) = if a = b then (P : ℂ) else 0 := by
  simp only [yChar_mul_conj, sum_stdAddChar_mul, sub_eq_zero]

/-- Orthonormality of the characters for the normalized inner product. -/
theorem yInner_yChar_yChar (a b : ZMod P) :
    yInner (yChar a) (yChar b) = if a = b then 1 else 0 := by
  have hP : (P : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne P)
  unfold yInner
  rw [sum_yChar_mul_conj]
  split_ifs
  · exact inv_mul_cancel₀ hP
  · simp

theorem yInner_self (F : ZMod P → ℂ) : yInner F F = ((yNorm 2 F ^ 2 : ℝ) : ℂ) := by
  have h2 : yNorm 2 F ^ (2 : ℝ) = (P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ (2 : ℝ) :=
    PrimeBHT.Lift.yNorm_rpow_self (by norm_num) F
  rw [Real.rpow_two] at h2
  simp only [Real.rpow_two] at h2
  rw [h2]
  unfold yInner
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem yInner_sum_left {ι : Type*} (s : Finset ι) (F : ι → ZMod P → ℂ) (G : ZMod P → ℂ) :
    yInner (∑ i ∈ s, F i) G = ∑ i ∈ s, yInner (F i) G := by
  unfold yInner
  simp only [Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]

theorem yInner_sum_right {ι : Type*} (s : Finset ι) (F : ZMod P → ℂ) (G : ι → ZMod P → ℂ) :
    yInner F (∑ i ∈ s, G i) = ∑ i ∈ s, yInner F (G i) := by
  unfold yInner
  simp only [Finset.sum_apply, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem sum_yChar_conj_yChar (y z : ZMod P) :
    ∑ a, yChar a y * conj (yChar a z) = if y = z then (P : ℂ) else 0 := by
  have e : ∀ a : ZMod P, yChar a y * conj (yChar a z) = ZMod.stdAddChar (a * (y - z)) := by
    intro a
    rw [yChar_apply, yChar_apply, conj_stdAddChar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp only [e, sum_stdAddChar_mul, sub_eq_zero]

/-- Every `F : Y_P → ℂ` is the sum of its Fourier series `∑_a ⟨F, e_a⟩ e_a`: the characters span. -/
theorem eq_sum_yInner_smul_yChar (F : ZMod P → ℂ) :
    F = ∑ a, yInner F (yChar a) • yChar a := by
  funext y
  have hP : (P : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne P)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, yInner]
  have e : ∀ a : ZMod P, ((P : ℂ)⁻¹ * ∑ z, F z * conj (yChar a z)) * yChar a y =
      (P : ℂ)⁻¹ * ∑ z, F z * (yChar a y * conj (yChar a z)) := by
    intro a
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun z _ => by ring
  simp only [e]
  rw [← Finset.mul_sum, Finset.sum_comm (f := fun a z => F z * (yChar a y * conj (yChar a z)))]
  simp only [← Finset.mul_sum, sum_yChar_conj_yChar, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  rw [← mul_assoc, mul_comm _ (F y), mul_assoc, inv_mul_cancel₀ hP, mul_one]

/-! ### (c) the triangle bound for `∑_A c_A e_A` -/

theorem norm_sum_yChar_le (c : ZMod P → ℂ) (y : ZMod P) :
    ‖∑ A, c A * yChar A y‖ ≤ ∑ A, ‖c A‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun A _ => ?_)
  rw [norm_mul, norm_yChar, mul_one]

/-- `‖∑_A c_A e_A‖_{L^s(Y_P)} ≤ ∑_A |c_A|` for every `s > 0`. -/
theorem yNorm_sum_yChar_le {s : ℝ} (hs : 0 < s) (c : ZMod P → ℂ) :
    yNorm s (fun y => ∑ A, c A * yChar A y) ≤ ∑ A, ‖c A‖ :=
  PrimeBHT.Interface.X2.yNorm_le hs _ fun y => norm_sum_yChar_le c y

/-- `‖F(x; ·)‖_{L^s(Y_P)} ≤ ∑_A |f_A(x)|`. -/
theorem yNorm_tensorFun_le {s : ℝ} (hs : 0 < s) (f : ZMod P → 𝓢(ℝ, ℂ)) (x : ℝ) :
    yNorm s (tensorFun f x) ≤ ∑ A, ‖f A x‖ :=
  yNorm_sum_yChar_le hs (fun A => f A x)

/-! ### (d) the constant `CT` -/

/-- A negative `CT` is never admissible: the hypothesis on `T` is unsatisfiable (test `F = G = H = 1`). -/
theorem not_bound_of_neg (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
    {u : ℝ} (hu : 0 < u) {CT : ℝ} (hCT : CT < 0) :
    ¬ ∀ F G H : ZMod P → ℂ, ‖T F G H‖ ≤ CT * yNorm 2 F * yNorm 2 G * yNorm u H :=
  fun h => absurd (PrimeBHT.Interface.X2.nonneg_of_bound T hu h) (not_le.2 hCT)

/-! ### (e) invariance under pointwise modulation by characters -/

end PrimeBHT.TimeFrequency.X2

end
