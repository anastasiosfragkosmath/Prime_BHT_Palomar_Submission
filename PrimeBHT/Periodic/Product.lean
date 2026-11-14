module

public import PrimeBHT.Periodic.Fibre

/-!
# The product model `A × Y_D`

This is the Chinese-remainder model `Y_N ≅ Y_d × Y_D` of `blueprint.md` §5.0, with `Y_d` replaced by
an arbitrary finite type `A`.  Everything is fibrewise in the first coordinate `α : A`.

* `fibMax F α = max_ξ ‖F_D (F_α) (ξ)‖` (the fibre maximal function `M_d F`, as a function of `α`).
* `avgP F G (α, β) = E_λ F(α, β - λ) G(α, β + λ)`.
* `l1_avgP_le` (blueprint N32): `‖avgP F G‖_{L¹} ≤ √2 ‖fibMax F‖_{L²} ‖G‖_{L²}`.
* `atom v ϑ (α, β) = v(α) e_D(ϑ(α) β)`, and the inverse theorem for `fibMax` (`exists_atom`,
  the key step of blueprint N35).
-/

@[expose] public section

namespace PrimeBHT.Periodic

open Finset
open scoped BigOperators ComplexConjugate

section Prod

variable {A : Type*} [Fintype A] {D : ℕ} [NeZero D]

/-- Expectation over a product type is the iterated expectation. -/
theorem expect_prod' {B M : Type*} [Fintype B] [AddCommMonoid M] [Module ℚ≥0 M]
    (f : A × B → M) : 𝔼 p, f p = 𝔼 a, 𝔼 b, f (a, b) := by
  rw [← Finset.univ_product_univ, Finset.expect_product]

/-- A function depending only on the first coordinate has the same `L²` norm on the product. -/
theorem l2_comp_fst {B E : Type*} [Fintype B] [Nonempty B] [Norm E] (φ : A → E) :
    l2 (fun p : A × B => φ p.1) = l2 φ := by
  unfold l2
  rw [expect_prod']
  simp only [Finset.expect_const (Finset.univ_nonempty : (Finset.univ : Finset B).Nonempty)]

/-- The fibre `F_α = F(α, ·) : Y_D → ℂ`. -/
def fibreOf (F : A × ZMod D → ℂ) (α : A) : ZMod D → ℂ := fun β => F (α, β)

/-- The fibre maximal function `α ↦ max_ξ ‖F_D (F_α) (ξ)‖`. -/
noncomputable def fibMax (F : A × ZMod D → ℂ) (α : A) : ℝ := fibreMax (fibreOf F α)

omit [Fintype A] in
theorem fibMax_nonneg (F : A × ZMod D → ℂ) (α : A) : 0 ≤ fibMax F α := fibreMax_nonneg _

/-- The fibrewise unweighted average `E_λ F(α, β - λ) G(α, β + λ)`. -/
noncomputable def avgP (F G : A × ZMod D → ℂ) (p : A × ZMod D) : ℂ :=
  𝔼 l : ZMod D, F (p.1, p.2 - l) * G (p.1, p.2 + l)

omit [Fintype A] in
theorem avgP_eq (F G : A × ZMod D → ℂ) (α : A) (β : ZMod D) :
    avgP F G (α, β) = avgFibre (fibreOf F α) (fibreOf G α) β := rfl

/-- **N32 in the product model.**
`‖E_λ F(·, · - λ) G(·, · + λ)‖_{L¹(A × Y_D)} ≤ √2 ‖fibMax F‖_{L²(A)} ‖G‖_{L²(A × Y_D)}`. -/
theorem l1_avgP_le (F G : A × ZMod D → ℂ) :
    l1 (avgP F G) ≤ √2 * l2 (fibMax F) * l2 G := by
  set g : A → ℝ := fun α => l2 (fibreOf G α) with hg
  have hl2g : l2 g = l2 G := by
    have h1 : l2 g ^ 2 = l2 G ^ 2 := by
      rw [l2_sq, l2_sq, expect_prod']
      refine Finset.expect_congr rfl fun α _ => ?_
      rw [hg, Real.norm_of_nonneg (l2_nonneg _), l2_sq]
      rfl
    exact (sq_eq_sq₀ (l2_nonneg _) (l2_nonneg _)).1 h1
  have h2 : l1 (avgP F G) ≤ 𝔼 α : A, √2 * (‖fibMax F α‖ * ‖g α‖) := by
    unfold l1
    rw [expect_prod']
    refine Finset.expect_le_expect fun α _ => ?_
    have := l1_avgFibre_le (fibreOf F α) (fibreOf G α)
    rw [Real.norm_of_nonneg (fibMax_nonneg F α), Real.norm_of_nonneg (l2_nonneg _)]
    unfold l1 at this
    simpa only [avgP_eq, fibMax, mul_assoc] using this
  rw [← Finset.mul_expect] at h2
  calc l1 (avgP F G) ≤ √2 * 𝔼 α : A, ‖fibMax F α‖ * ‖g α‖ := h2
    _ ≤ √2 * (l2 (fibMax F) * l2 g) :=
        mul_le_mul_of_nonneg_left (expect_norm_mul_le _ _) (Real.sqrt_nonneg _)
    _ = √2 * l2 (fibMax F) * l2 G := by rw [hl2g, mul_assoc]

/-- The structured atom `Φ(α, β) = v(α) e_D(ϑ(α) β)`. -/
noncomputable def atom (v : A → ℂ) (ϑ : A → ZMod D) (p : A × ZMod D) : ℂ :=
  v p.1 * eD (ϑ p.1 * p.2)

theorem l2_atom (v : A → ℂ) (ϑ : A → ZMod D) : l2 (atom v ϑ) = l2 v := by
  rw [← l2_comp_fst (B := ZMod D) v]
  unfold l2
  congr 1
  refine Finset.expect_congr rfl fun p _ => ?_
  simp [atom, norm_eD]

/-- **Inverse theorem for `fibMax`** (key step of blueprint N35): if `‖fibMax R‖_{L²} > 0`, there is
a structured atom `Φ(α, β) = v(α) e_D(ϑ(α) β)` with `‖v‖_{L²} = 1` and
`⟨R, Φ⟩ = ‖fibMax R‖_{L²}`. -/
theorem exists_atom [Nonempty A] (R : A × ZMod D → ℂ) (hR : 0 < l2 (fibMax R)) :
    ∃ (v : A → ℂ) (ϑ : A → ZMod D), l2 v = 1 ∧ ip R (atom v ϑ) = ((l2 (fibMax R) : ℝ) : ℂ) := by
  classical
  set m : ℝ := l2 (fibMax R) with hm
  have hm0 : m ≠ 0 := hR.ne'
  choose ϑ hϑ using fun α => exists_norm_dft_eq_fibreMax (fibreOf R α)
  have hm2 : 𝔼 α : A, fibMax R α ^ 2 = m ^ 2 := by
    rw [hm, l2_sq]
    refine Finset.expect_congr rfl fun α _ => ?_
    rw [Real.norm_of_nonneg (fibMax_nonneg R α)]
  refine ⟨fun α => dft (fibreOf R α) (ϑ α) / (m : ℂ), ϑ, ?_, ?_⟩
  · have h1 : ∀ α : A, ‖dft (fibreOf R α) (ϑ α) / (m : ℂ)‖ = fibMax R α / m := by
      intro α
      rw [norm_div, hϑ α, Complex.norm_real, Real.norm_of_nonneg hR.le]
      rfl
    have h2 : l2 (fun α => dft (fibreOf R α) (ϑ α) / (m : ℂ)) ^ 2 = 1 := by
      rw [l2_sq]
      simp_rw [h1, div_pow]
      rw [← Finset.expect_div, hm2]
      exact div_self (pow_ne_zero 2 hm0)
    exact (pow_eq_one_iff_of_nonneg (l2_nonneg _) two_ne_zero).1 h2
  · unfold ip
    rw [expect_prod']
    have h3 : ∀ α : A, 𝔼 β : ZMod D, R (α, β) * conj (atom
        (fun α => dft (fibreOf R α) (ϑ α) / (m : ℂ)) ϑ (α, β)) =
        ((fibMax R α ^ 2 / m : ℝ) : ℂ) := by
      intro α
      have h4 : ∀ β : ZMod D, R (α, β) * conj (atom
          (fun α => dft (fibreOf R α) (ϑ α) / (m : ℂ)) ϑ (α, β)) =
          conj (dft (fibreOf R α) (ϑ α) / (m : ℂ)) *
            (fibreOf R α β * eD (-(ϑ α * β))) := by
        intro β
        simp only [atom, map_mul, ← eD_neg, fibreOf]
        ring
      simp_rw [h4]
      rw [← Finset.mul_expect]
      change conj (dft (fibreOf R α) (ϑ α) / (m : ℂ)) * dft (fibreOf R α) (ϑ α) = _
      rw [map_div₀, Complex.conj_ofReal, mul_comm, ← mul_div_assoc, Complex.mul_conj', hϑ α]
      push_cast
      rfl
    simp_rw [h3]
    rw [← Complex.ofReal_expect, ← Finset.expect_div, hm2]
    congr 1
    field_simp

end Prod

end PrimeBHT.Periodic
