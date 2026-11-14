module

public import PrimeBHT.U3MaxMod.Chain
public import PrimeCarleson.Proof.Paper.P2.Normalization

/-!
# `l:U3maxmod`, part 3: the Gowers norm side

(G2) `∑_{h,k} |∑_n Δ_{h,k} W(n)|² = ‖W‖_{U³(ℤ)}⁸` and (G5) `‖1_{[N]}‖_{U³(ℤ)}⁸ ≤ 8 N⁴`.
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeBHT.U3MaxMod

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Paper

lemma multDiff_three_eq (a b k : ℤ) (F : ℤ → ℂ) (x : ℤ) :
    multDiff 3 ![a, b, k] F x = conjDiff k (multDiff 2 ![a, b] F) x := by
  have h : Fin.init ![a, b, k] = ![a, b] := by
    funext i; fin_cases i <;> rfl
  show multDiff 2 (Fin.init ![a, b, k]) F x *
      conj (multDiff 2 (Fin.init ![a, b, k]) F (x + ![a, b, k] (Fin.last 2))) = _
  rw [h]
  rfl

/-- **(G2)**: `∑_{h,k} |∑_n Δ_{h,k} F(n)|² = ‖F‖_{U³(ℤ)}⁸`. -/
theorem sum_sq_AF_eq (F : ℤ →₀ ℂ) (I D : Finset ℤ) (hI : ∀ x, F x ≠ 0 → x ∈ I)
    (hD : ∀ x ∈ I, ∀ y ∈ I, y - x ∈ D) :
    ∑ h ∈ D, ∑ k ∈ D, ‖AF I (⇑F) h k‖ ^ 2 = gowersNorm 3 F ^ 8 := by
  have h8 := gowersLp_pow_eight_eq F I D hI hD
  have step : ∀ a ∈ D, ∀ b ∈ D, ∑ x ∈ I, ∑ k ∈ D, multDiff 3 ![a, b, k] (⇑F) x =
      ((‖AF I (⇑F) a b‖ ^ 2 : ℝ) : ℂ) := by
    intro a _ b _
    unfold AF
    rw [norm_sq_sum_eq_sum_conjDiff I D hD (multDiff 2 ![a, b] ⇑F) (fun y hy => by
      by_contra hne
      exact hy (hI y (multDiff_ne_zero _ _ y hne).1))]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun k _ => multDiff_three_eq a b k _ x
  have key : ((gowersNorm 3 F ^ 8 : ℝ) : ℂ) = ((∑ h ∈ D, ∑ k ∈ D, ‖AF I (⇑F) h k‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [h8]
    calc ∑ x ∈ I, ∑ a ∈ D, ∑ b ∈ D, ∑ k ∈ D, multDiff 3 ![a, b, k] (⇑F) x
        = ∑ a ∈ D, ∑ x ∈ I, ∑ b ∈ D, ∑ k ∈ D, multDiff 3 ![a, b, k] (⇑F) x := Finset.sum_comm
      _ = ∑ a ∈ D, ∑ b ∈ D, ∑ x ∈ I, ∑ k ∈ D, multDiff 3 ![a, b, k] (⇑F) x :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => by
          rw [step a ha b hb]; push_cast; rfl
  exact_mod_cast key.symm

/-- **(G5)** (upper bound): `‖1_{[N]}‖_{U³(ℤ)}⁸ ≤ 8 N⁴`. -/
theorem gowersNorm_one_pow_eight_le (N : ℕ+) :
    gowersNorm 3 (restrictInterval N 1) ^ 8 ≤ 8 * (N : ℝ) ^ 4 := by
  set I : Finset ℤ := Finset.Icc (1 : ℤ) N with hI
  set D : Finset ℤ := Finset.Icc (1 - (N : ℤ)) (N - 1) with hD
  have hIs : ∀ x, restrictInterval N 1 x ≠ 0 → x ∈ I := fun x hx => by
    by_contra hxI
    exact hx (by simp [restrictInterval, Finsupp.indicator_apply, show x ∉ Finset.Icc (1 : ℤ) N from hxI])
  have hDs : ∀ x ∈ I, ∀ y ∈ I, y - x ∈ D := fun x hx y hy => by
    simp only [hI, hD, Finset.mem_Icc] at hx hy ⊢
    omega
  have h8 := gowersLp_pow_eight_eq (restrictInterval N 1) I D hIs hDs
  have hcard : ((I.card : ℝ)) * (D.card : ℝ) ^ 3 ≤ 8 * (N : ℝ) ^ 4 := by
    have h1 : I.card = N := by simp [hI]
    have h2 : D.card ≤ 2 * N := by
      simp only [hD, Int.card_Icc]
      omega
    have h3 : (D.card : ℝ) ≤ 2 * N := by exact_mod_cast h2
    rw [h1]
    calc (N : ℝ) * (D.card : ℝ) ^ 3 ≤ N * (2 * N) ^ 3 := by gcongr
      _ = 8 * (N : ℝ) ^ 4 := by ring
  have hnorm : ‖((gowersNorm 3 (restrictInterval N 1) : ℝ) : ℂ) ^ 8‖ ≤
      (I.card : ℝ) * (D.card : ℝ) ^ 3 := by
    rw [h8]
    calc ‖∑ x ∈ I, ∑ a ∈ D, ∑ b ∈ D, ∑ k ∈ D, multDiff 3 ![a, b, k] (⇑(restrictInterval N 1)) x‖
        ≤ ∑ x ∈ I, ∑ a ∈ D, ∑ b ∈ D, ∑ k ∈ D, (1 : ℝ) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          exact norm_multDiff_indicator_le_one I 3 ![a, b, k] x
      _ = (I.card : ℝ) * (D.card : ℝ) ^ 3 := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]; ring
  rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (gowersNorm_nonneg _ _)] at hnorm
  exact hnorm.trans hcard

end PrimeBHT.U3MaxMod
