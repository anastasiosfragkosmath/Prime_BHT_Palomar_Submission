module

public import PrimeBHT.Periodic.Basic

/-!
# The energy-decrement loop (abstract form)

This is the greedy loop of blueprint node N35 (`p:greedy`), stated for an arbitrary finite measure
space `X` (normalized counting measure) and an abstract family of "maximal functionals" `Mx s`
indexed by a finite set `S`, each equipped with an "inverse theorem" (`key`): whenever
`Mx s R > 0` there is a unit atom `Φ` with `⟨R, Φ⟩ = Mx s R`.

Conclusion: for every `t > 0` and `F` there are `J ≤ t⁻²` atoms and real coefficients `c_j > 0`
with `∑ c_j² ≤ ‖F‖²` such that the remainder `R = F - ∑ c_j Φ_j` has `Mx s R ≤ t ‖F‖` for all `s ∈ S`.
-/

@[expose] public section

namespace PrimeBHT.Periodic

open Finset
open scoped BigOperators ComplexConjugate

variable {X : Type*} [Fintype X]

/-- Energy identity: if `‖Φ‖ = 1` and `⟨R, Φ⟩ = c` is real, then `‖R - cΦ‖² = ‖R‖² - c²`. -/
theorem l2_sq_sub_smul (R Φ : X → ℂ) (c : ℝ) (hΦ : l2 Φ = 1) (hip : ip R Φ = (c : ℂ)) :
    l2 (R - (c : ℂ) • Φ) ^ 2 = l2 R ^ 2 - c ^ 2 := by
  have hpt : ∀ x, ‖(R - (c : ℂ) • Φ) x‖ ^ 2 =
      ‖R x‖ ^ 2 - 2 * c * (R x * conj (Φ x)).re + c ^ 2 * ‖Φ x‖ ^ 2 := by
    intro x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.sq_norm, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  have hre : (𝔼 x, (R x * conj (Φ x)).re) = c := by
    rw [← Complex.re_expect]
    have : (𝔼 x, R x * conj (Φ x)) = (c : ℂ) := hip
    rw [this, Complex.ofReal_re]
  have hΦ2 : 𝔼 x, ‖Φ x‖ ^ 2 = 1 := by
    have := l2_sq Φ
    rw [hΦ] at this
    linarith
  rw [l2_sq, l2_sq]
  simp_rw [hpt]
  rw [expect_add_distrib, expect_sub_distrib, ← Finset.mul_expect, ← Finset.mul_expect, hre, hΦ2]
  ring

section Greedy

variable {ι : Type*}

/-- **Greedy decomposition** (energy decrement), abstract form of blueprint N35. -/
theorem exists_greedy_decomposition_abstract (S : Finset ι) (Mx : ι → (X → ℂ) → ℝ)
    (Atom : ι → (X → ℂ) → Prop)
    (key : ∀ s ∈ S, ∀ R : X → ℂ, 0 < Mx s R →
      ∃ Φ : X → ℂ, Atom s Φ ∧ l2 Φ = 1 ∧ ip R Φ = (Mx s R : ℂ))
    {t : ℝ} (ht : 0 < t) (F : X → ℂ) :
    ∃ (J : ℕ) (s : Fin J → ι) (Φ : Fin J → X → ℂ) (c : Fin J → ℝ),
      (J : ℝ) ≤ t⁻¹ ^ 2 ∧ (∀ j, s j ∈ S) ∧ (∀ j, Atom (s j) (Φ j)) ∧ (∀ j, l2 (Φ j) = 1) ∧
      (∀ j, 0 < c j) ∧ ∑ j, c j ^ 2 ≤ l2 F ^ 2 ∧
      ∀ s' ∈ S, Mx s' (F - ∑ j, (c j : ℂ) • Φ j) ≤ t * l2 F := by
  have hF0 : 0 ≤ t * l2 F := mul_nonneg ht.le (l2_nonneg F)
  -- the invariant of a partial decomposition
  let Inv : (J : ℕ) → (Fin J → ι) → (Fin J → X → ℂ) → (Fin J → ℝ) → Prop :=
    fun J s Φ c => (∀ j, s j ∈ S ∧ Atom (s j) (Φ j) ∧ l2 (Φ j) = 1 ∧ t * l2 F < c j) ∧
      l2 (F - ∑ j, (c j : ℂ) • Φ j) ^ 2 + ∑ j, c j ^ 2 = l2 F ^ 2
  -- induction on the fuel `n`
  have main : ∀ n : ℕ, ∃ (J : ℕ) (s : Fin J → ι) (Φ : Fin J → X → ℂ) (c : Fin J → ℝ),
      Inv J s Φ c ∧ (J = n ∨ ∀ s' ∈ S, Mx s' (F - ∑ j, (c j : ℂ) • Φ j) ≤ t * l2 F) := by
    intro n
    induction n with
    | zero =>
      refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ⟨fun j => j.elim0, ?_⟩, Or.inl rfl⟩
      simp
    | succ n ih =>
      obtain ⟨J, s, Φ, c, hInv, hcase⟩ := ih
      by_cases hstop : ∀ s' ∈ S, Mx s' (F - ∑ j, (c j : ℂ) • Φ j) ≤ t * l2 F
      · exact ⟨J, s, Φ, c, hInv, Or.inr hstop⟩
      · have hJ : J = n := hcase.resolve_right hstop
        push Not at hstop
        obtain ⟨s0, hs0, hlt⟩ := hstop
        have hpos : 0 < Mx s0 (F - ∑ j, (c j : ℂ) • Φ j) := lt_of_le_of_lt hF0 hlt
        obtain ⟨Φ0, hA0, hΦ0, hip0⟩ := key s0 hs0 _ hpos
        refine ⟨J + 1, Fin.cons s0 s, Fin.cons Φ0 Φ, Fin.cons (Mx s0 (F - ∑ j, (c j : ℂ) • Φ j)) c,
          ⟨?_, ?_⟩, Or.inl (by omega)⟩
        · intro j
          refine Fin.cases ?_ (fun i => ?_) j
          · simpa using ⟨hs0, hA0, hΦ0, hlt⟩
          · simpa using hInv.1 i
        · have hsum : (F - ∑ j : Fin (J + 1), ((Fin.cons (Mx s0 (F - ∑ j, (c j : ℂ) • Φ j)) c :
              Fin (J + 1) → ℝ) j : ℂ) • (Fin.cons Φ0 Φ : Fin (J + 1) → X → ℂ) j) =
              (F - ∑ j, (c j : ℂ) • Φ j) -
                ((Mx s0 (F - ∑ j, (c j : ℂ) • Φ j) : ℝ) : ℂ) • Φ0 := by
            rw [Fin.sum_univ_succ]
            simp only [Fin.cons_zero, Fin.cons_succ]
            abel
          rw [hsum, l2_sq_sub_smul _ Φ0 _ hΦ0 hip0, Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          linarith [hInv.2]
  -- choose the fuel large enough
  obtain ⟨J, s, Φ, c, hInv, hcase⟩ := main (⌈t⁻¹ ^ 2⌉₊ + 1)
  obtain ⟨hmem, henergy⟩ := hInv
  have hcpos : ∀ j, 0 < c j := fun j => lt_of_le_of_lt hF0 (hmem j).2.2.2
  have hsum_le : ∑ j, c j ^ 2 ≤ l2 F ^ 2 := by
    have := sq_nonneg (l2 (F - ∑ j, (c j : ℂ) • Φ j))
    linarith
  have hJbound : (J : ℝ) ≤ t⁻¹ ^ 2 := by
    rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
    · subst hJ0
      simp only [Nat.cast_zero]
      positivity
    · have hne : (Finset.univ : Finset (Fin J)).Nonempty :=
        ⟨⟨0, hJ0⟩, Finset.mem_univ _⟩
      have h1 : ∑ j : Fin J, (t * l2 F) ^ 2 < ∑ j : Fin J, c j ^ 2 :=
        Finset.sum_lt_sum_of_nonempty hne fun j _ =>
          pow_lt_pow_left₀ (hmem j).2.2.2 hF0 two_ne_zero
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
      have h2 : (J : ℝ) * t ^ 2 * l2 F ^ 2 < 1 * l2 F ^ 2 := by
        have : (J : ℝ) * (t * l2 F) ^ 2 < l2 F ^ 2 := lt_of_lt_of_le h1 hsum_le
        nlinarith [this]
      have h3 : (J : ℝ) * t ^ 2 < 1 := lt_of_mul_lt_mul_right h2 (sq_nonneg _)
      have h4 : (J : ℝ) < t⁻¹ ^ 2 := by
        rw [inv_pow, ← one_div, lt_div_iff₀ (by positivity)]
        exact h3
      exact h4.le
  have hstop : ∀ s' ∈ S, Mx s' (F - ∑ j, (c j : ℂ) • Φ j) ≤ t * l2 F := by
    rcases hcase with hJ | h
    · exfalso
      have h1 : (⌈t⁻¹ ^ 2⌉₊ : ℝ) < J := by
        rw [hJ]; push_cast; linarith
      have h2 : t⁻¹ ^ 2 ≤ (⌈t⁻¹ ^ 2⌉₊ : ℝ) := Nat.le_ceil _
      linarith
    · exact h
  exact ⟨J, s, Φ, c, hJbound, fun j => (hmem j).1, fun j => (hmem j).2.1,
    fun j => (hmem j).2.2.1, hcpos, hsum_le, hstop⟩

end Greedy

end PrimeBHT.Periodic
