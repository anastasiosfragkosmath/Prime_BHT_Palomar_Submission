module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Analysis.Real.Sqrt

/-!
# Normalized norms on a finite type
-/

@[expose] public section

namespace PrimeBHT.Periodic

open Finset
open scoped BigOperators ComplexConjugate

variable {X : Type*} [Fintype X]

/-- The `L¹` norm for the normalized counting measure: `E_x ‖F x‖`. -/
noncomputable def l1 {E : Type*} [Norm E] (F : X → E) : ℝ := 𝔼 x, ‖F x‖

/-- The `L²` norm for the normalized counting measure: `(E_x ‖F x‖²)^{1/2}`. -/
noncomputable def l2 {E : Type*} [Norm E] (F : X → E) : ℝ := √(𝔼 x, ‖F x‖ ^ 2)

/-- The normalized inner product `⟨F, G⟩ = E_x F x * conj (G x)`. -/
noncomputable def ip (F G : X → ℂ) : ℂ := 𝔼 x, F x * conj (G x)

theorem l1_nonneg {E : Type*} [SeminormedAddCommGroup E] (F : X → E) : 0 ≤ l1 F :=
  expect_nonneg fun _ _ => norm_nonneg _

theorem l2_nonneg {E : Type*} [Norm E] (F : X → E) : 0 ≤ l2 F := Real.sqrt_nonneg _

theorem l2_sq {E : Type*} [Norm E] (F : X → E) : l2 F ^ 2 = 𝔼 x, ‖F x‖ ^ 2 :=
  Real.sq_sqrt (expect_nonneg fun _ _ => sq_nonneg _)

/-- Cauchy-Schwarz for the normalized counting measure. -/
theorem expect_norm_mul_le {E E' : Type*} [Norm E] [Norm E'] (F : X → E) (G : X → E') :
    𝔼 x, ‖F x‖ * ‖G x‖ ≤ l2 F * l2 G := by
  have h := expect_mul_sq_le_sq_mul_sq (Finset.univ : Finset X) (fun x => ‖F x‖) (fun x => ‖G x‖)
  unfold l2
  rw [← Real.sqrt_mul (expect_nonneg fun _ _ => sq_nonneg _)]
  exact Real.le_sqrt_of_sq_le h

/-- `L¹ ≤ L²` for the normalized counting measure on a nonempty finite type. -/
theorem l1_le_l2 [Nonempty X] {E : Type*} [Norm E] (F : X → E) : l1 F ≤ l2 F := by
  have h := expect_mul_sq_le_sq_mul_sq (Finset.univ : Finset X) (fun x => ‖F x‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, expect_const univ_nonempty] at h
  unfold l1 l2
  exact Real.le_sqrt_of_sq_le (by simpa using h)

/-- Invariance of the `L¹` norm under a bijection of the index type. -/
theorem l1_comp_equiv {Y : Type*} [Fintype Y] {E : Type*} [Norm E] (e : X ≃ Y) (F : Y → E) :
    l1 (F ∘ e) = l1 F :=
  Fintype.expect_equiv e _ _ fun _ => rfl

/-- Invariance of the `L²` norm under a bijection of the index type. -/
theorem l2_comp_equiv {Y : Type*} [Fintype Y] {E : Type*} [Norm E] (e : X ≃ Y) (F : Y → E) :
    l2 (F ∘ e) = l2 F := by
  unfold l2
  rw [Fintype.expect_equiv e (fun x => ‖(F ∘ e) x‖ ^ 2) (fun y => ‖F y‖ ^ 2) fun _ => rfl]

/-- Invariance of the normalized inner product under a bijection of the index type. -/
theorem ip_comp_equiv {Y : Type*} [Fintype Y] (e : X ≃ Y) (F G : Y → ℂ) :
    ip (F ∘ e) (G ∘ e) = ip F G :=
  Fintype.expect_equiv e _ _ fun _ => rfl

end PrimeBHT.Periodic
