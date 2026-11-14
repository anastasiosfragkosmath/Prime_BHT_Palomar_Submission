module

public import PrimeBHT.Periodic.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Fourier analysis on `ZMod D` and the unweighted fibre estimate

`blueprint.md` §5.0 and node N32 (`l:unweighted-fibre`), on the fibre `Y_D = ZMod D`
(normalized counting measure).

* `eD x = exp(2πi x / D)` (`ZMod.stdAddChar`).
* The *normalized* Fourier transform `dft h ξ = E_β h β * eD (-(ξ β))`.
* Fourier inversion `h x = ∑_ξ dft h ξ * eD (ξ x)` and Parseval `E_β ‖h β‖² = ∑_ξ ‖dft h ξ‖²`.
* `fibreMax h = max_ξ ‖dft h ξ‖`.
* `avgFibre f g β = E_λ f (β - λ) * g (β + λ)`; the main estimate
  `E_β ‖avgFibre f g β‖ ≤ √2 * fibreMax f * (E_β ‖g β‖²)^{1/2}`.
-/

@[expose] public section

namespace PrimeBHT.Periodic

open Finset
open scoped BigOperators ComplexConjugate

variable {D : ℕ} [NeZero D]

/-- The additive character `e_D(x) = exp(2πi x/D)` of `ZMod D`. -/
noncomputable def eD (x : ZMod D) : ℂ := ZMod.stdAddChar x

theorem eD_add (x y : ZMod D) : eD (x + y) = eD x * eD y := AddChar.map_add_eq_mul _ _ _

theorem eD_neg (x : ZMod D) : eD (-x) = conj (eD x) := AddChar.map_neg_eq_conj _ _

theorem norm_eD (x : ZMod D) : ‖eD x‖ = 1 := AddChar.norm_apply _ _

/-- Orthogonality: `E_β e_D(k β) = 1_{k = 0}`. -/
theorem expect_eD_mul (k : ZMod D) : 𝔼 β : ZMod D, eD (k * β) = if k = 0 then 1 else 0 := by
  classical
  have h := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod D) ℂ)) k
    (ZMod.isPrimitive_stdAddChar D)
  rw [Fintype.expect_eq_sum_div_card]
  have h' : ∑ β : ZMod D, eD (k * β) = if k = 0 then (D : ℂ) else 0 := by
    simp only [eD]
    simp_rw [mul_comm k]
    rw [h]
    simp [ZMod.card]
  rw [h']
  have hD : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne D)
  split_ifs
  · simp only [ZMod.card]
    exact div_self hD
  · simp

/-- Orthogonality: `∑_ξ e_D(ξ x) = D * 1_{x = 0}`. -/
theorem sum_eD_mul (x : ZMod D) : ∑ ξ : ZMod D, eD (ξ * x) = if x = 0 then (D : ℂ) else 0 := by
  classical
  have h := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod D) ℂ)) x
    (ZMod.isPrimitive_stdAddChar D)
  simp only [eD]
  rw [h]
  simp [ZMod.card]

/-- The normalized Fourier transform on `ZMod D`: `F_D h (ξ) = E_β h(β) e_D(-ξβ)`. -/
noncomputable def dft (h : ZMod D → ℂ) (ξ : ZMod D) : ℂ := 𝔼 β : ZMod D, h β * eD (-(ξ * β))

/-- Fourier inversion for the normalized transform. -/
theorem dft_inversion (h : ZMod D → ℂ) (x : ZMod D) :
    h x = ∑ ξ : ZMod D, dft h ξ * eD (ξ * x) := by
  classical
  have hD : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne D)
  have h1 : ∀ ξ : ZMod D, dft h ξ * eD (ξ * x) = 𝔼 β : ZMod D, h β * eD (ξ * (x - β)) := by
    intro ξ
    unfold dft
    rw [Finset.expect_mul]
    refine Finset.expect_congr rfl fun β _ => ?_
    rw [mul_assoc, ← eD_add]
    congr 2
    ring
  simp_rw [h1]
  rw [← Finset.expect_sum_comm]
  have h2 : ∀ β : ZMod D, ∑ ξ : ZMod D, h β * eD (ξ * (x - β)) =
      if β = x then h β * (D : ℂ) else 0 := by
    intro β
    rw [← Finset.mul_sum, sum_eD_mul]
    by_cases hb : β = x
    · simp [hb]
    · have : x - β ≠ 0 := fun h0 => hb (sub_eq_zero.1 h0).symm
      simp [hb, this]
  simp_rw [h2]
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, ZMod.card]
  field_simp

theorem conj_expect {ι : Type*} [Fintype ι] (f : ι → ℂ) : conj (𝔼 i, f i) = 𝔼 i, conj (f i) := by
  simp only [Fintype.expect_eq_sum_div_card, map_div₀, map_sum, map_natCast]

theorem conj_dft (h : ZMod D → ℂ) (ξ : ZMod D) :
    conj (dft h ξ) = 𝔼 β : ZMod D, conj (h β) * eD (ξ * β) := by
  unfold dft
  rw [conj_expect]
  refine Finset.expect_congr rfl fun β _ => ?_
  rw [map_mul, ← eD_neg, neg_neg]

/-- Parseval for the normalized transform. -/
theorem parseval (h : ZMod D → ℂ) : 𝔼 β : ZMod D, ‖h β‖ ^ 2 = ∑ ξ : ZMod D, ‖dft h ξ‖ ^ 2 := by
  classical
  apply Complex.ofReal_injective
  push_cast
  have e1 : ∀ z : ℂ, (‖z‖ : ℂ) ^ 2 = z * conj z := fun z => (Complex.mul_conj' z).symm
  simp_rw [e1]
  calc 𝔼 β : ZMod D, h β * conj (h β)
      = 𝔼 β : ZMod D, (∑ ξ : ZMod D, dft h ξ * eD (ξ * β)) * conj (h β) := by
        refine Finset.expect_congr rfl fun β _ => ?_
        rw [← dft_inversion h β]
    _ = ∑ ξ : ZMod D, dft h ξ * conj (dft h ξ) := by
        simp_rw [Finset.sum_mul]
        rw [Finset.expect_sum_comm]
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [conj_dft, Finset.mul_expect]
        refine Finset.expect_congr rfl fun β _ => ?_
        ring

/-- The fibre maximal function `max_ξ ‖F_D h (ξ)‖`. -/
noncomputable def fibreMax (h : ZMod D → ℂ) : ℝ := ⨆ ξ : ZMod D, ‖dft h ξ‖

theorem norm_dft_le_fibreMax (h : ZMod D → ℂ) (ξ : ZMod D) : ‖dft h ξ‖ ≤ fibreMax h :=
  le_ciSup (f := fun ξ : ZMod D => ‖dft h ξ‖) (Set.finite_range _).bddAbove ξ

theorem fibreMax_nonneg (h : ZMod D → ℂ) : 0 ≤ fibreMax h :=
  (norm_nonneg _).trans (norm_dft_le_fibreMax h 0)

/-- The supremum defining `fibreMax` is attained. -/
theorem exists_norm_dft_eq_fibreMax (h : ZMod D → ℂ) : ∃ ξ, ‖dft h ξ‖ = fibreMax h :=
  exists_eq_ciSup_of_finite

/-- The unweighted bilinear average on `Y_D`: `E_λ f(β - λ) g(β + λ)`. -/
noncomputable def avgFibre (f g : ZMod D → ℂ) (β : ZMod D) : ℂ :=
  𝔼 l : ZMod D, f (β - l) * g (β + l)

/-- Fourier expansion of the average (blueprint N32, step 1). -/
theorem avgFibre_eq (f g : ZMod D → ℂ) (β : ZMod D) :
    avgFibre f g β = ∑ ξ : ZMod D, (dft f ξ * dft g ξ) * eD (2 * ξ * β) := by
  classical
  unfold avgFibre
  have hf : ∀ l, f (β - l) = ∑ ξ : ZMod D, dft f ξ * eD (ξ * (β - l)) :=
    fun l => dft_inversion f _
  have hg : ∀ l, g (β + l) = ∑ ξ : ZMod D, dft g ξ * eD (ξ * (β + l)) :=
    fun l => dft_inversion g _
  simp_rw [hf, hg, Finset.sum_mul_sum]
  simp_rw [Finset.expect_sum_comm]
  have key : ∀ ξ ξ' : ZMod D,
      𝔼 l : ZMod D, (dft f ξ * eD (ξ * (β - l))) * (dft g ξ' * eD (ξ' * (β + l))) =
        if ξ' = ξ then (dft f ξ * dft g ξ) * eD (2 * ξ * β) else 0 := by
    intro ξ ξ'
    have e1 : ∀ l : ZMod D, (dft f ξ * eD (ξ * (β - l))) * (dft g ξ' * eD (ξ' * (β + l))) =
        (dft f ξ * dft g ξ' * eD ((ξ + ξ') * β)) * eD ((ξ' - ξ) * l) := by
      intro l
      have e2 : eD (ξ * (β - l)) * eD (ξ' * (β + l)) = eD ((ξ + ξ') * β) * eD ((ξ' - ξ) * l) := by
        rw [← eD_add, ← eD_add]; congr 1; ring
      calc (dft f ξ * eD (ξ * (β - l))) * (dft g ξ' * eD (ξ' * (β + l)))
          = (dft f ξ * dft g ξ') * (eD (ξ * (β - l)) * eD (ξ' * (β + l))) := by ring
        _ = _ := by rw [e2]; ring
    simp_rw [e1]
    rw [← Finset.mul_expect, expect_eD_mul]
    by_cases hξ : ξ' = ξ
    · subst hξ
      have : (ξ' + ξ') * β = 2 * ξ' * β := by ring
      simp [this]
    · have : ξ' - ξ ≠ 0 := fun h0 => hξ (sub_eq_zero.1 h0)
      simp [hξ, this]
  simp_rw [key]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- The kernel of the doubling map `ξ ↦ 2ξ` on `ZMod D` is `{0, D/2}`. -/
theorem eq_zero_or_eq_half_of_two_mul_eq_zero (k : ZMod D) (hk : 2 * k = 0) :
    k = 0 ∨ k = ((D / 2 : ℕ) : ZMod D) := by
  have h1 : ((2 * k.val : ℕ) : ZMod D) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact hk
  rw [ZMod.natCast_eq_zero_iff] at h1
  obtain ⟨c, hc⟩ := h1
  have hlt := ZMod.val_lt k
  have hc2 : c < 2 := by
    by_contra hcc
    have := Nat.mul_le_mul_left D (not_lt.1 hcc)
    omega
  interval_cases c
  · left
    have : k.val = 0 := by omega
    exact (ZMod.val_eq_zero k).1 this
  · right
    have : k.val = D / 2 := by omega
    rw [← this, ZMod.natCast_zmod_val]

/-- For each `a`, at most two `b` satisfy `2 (a - b) = 0` in `ZMod D`. -/
theorem card_filter_two_mul_sub_le (a : ZMod D) :
    (Finset.univ.filter fun b : ZMod D => 2 * (a - b) = 0).card ≤ 2 := by
  classical
  have hsub : (Finset.univ.filter fun b : ZMod D => 2 * (a - b) = 0) ⊆
      {a, a - ((D / 2 : ℕ) : ZMod D)} := by
    intro b hb
    rw [Finset.mem_filter] at hb
    rcases eq_zero_or_eq_half_of_two_mul_eq_zero _ hb.2 with h | h
    · have : b = a := by rw [sub_eq_zero] at h; exact h.symm
      simp [this]
    · have : b = a - ((D / 2 : ℕ) : ZMod D) := by rw [← h]; ring
      simp [this]
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

/-- The weights `1_{2(ξ - ξ') = 0}` have row sums at most two. -/
theorem sum_delta_le (ξ : ZMod D) :
    ∑ ξ' : ZMod D, (if 2 * (ξ - ξ') = 0 then (1 : ℝ) else 0) ≤ 2 := by
  classical
  rw [Finset.sum_boole]
  exact_mod_cast card_filter_two_mul_sub_le ξ

/-- The weights `1_{2(ξ - ξ') = 0}` have column sums at most two. -/
theorem sum_delta_le' (ξ' : ZMod D) :
    ∑ ξ : ZMod D, (if 2 * (ξ - ξ') = 0 then (1 : ℝ) else 0) ≤ 2 := by
  classical
  have : ∀ ξ : ZMod D, (2 * (ξ - ξ') = 0 ↔ 2 * (ξ' - ξ) = 0) := by
    intro ξ
    rw [show 2 * (ξ' - ξ) = -(2 * (ξ - ξ')) by ring, neg_eq_zero]
  simp_rw [this]
  exact sum_delta_le ξ'

/-- Orthogonality estimate for the doubled characters (blueprint N32, step 2): the doubling map
has fibres of size at most two, so `E_β ‖∑_ξ c_ξ e_D(2ξβ)‖² ≤ 2 ∑_ξ ‖c_ξ‖²`. -/
theorem expect_norm_sq_le (c : ZMod D → ℂ) :
    𝔼 β : ZMod D, ‖∑ ξ : ZMod D, c ξ * eD (2 * ξ * β)‖ ^ 2 ≤ 2 * ∑ ξ : ZMod D, ‖c ξ‖ ^ 2 := by
  classical
  set X : ℝ := 𝔼 β : ZMod D, ‖∑ ξ : ZMod D, c ξ * eD (2 * ξ * β)‖ ^ 2 with hX
  have h1 : ∀ β : ZMod D, (‖∑ ξ : ZMod D, c ξ * eD (2 * ξ * β)‖ : ℂ) ^ 2 =
      ∑ ξ : ZMod D, ∑ ξ' : ZMod D, c ξ * conj (c ξ') * eD ((2 * (ξ - ξ')) * β) := by
    intro β
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun ξ' _ => ?_
    have e2 : eD (2 * ξ * β) * eD (-(2 * ξ' * β)) = eD ((2 * (ξ - ξ')) * β) := by
      rw [← eD_add]; congr 1; ring
    rw [map_mul, ← eD_neg, ← e2]
    ring
  have h2 : (X : ℂ) = ∑ ξ : ZMod D, ∑ ξ' : ZMod D,
      c ξ * conj (c ξ') * (if 2 * (ξ - ξ') = 0 then (1 : ℂ) else 0) := by
    rw [hX, Complex.ofReal_expect]
    push_cast
    simp_rw [h1]
    simp_rw [Finset.expect_sum_comm]
    refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun ξ' _ => ?_
    rw [← Finset.mul_expect, expect_eD_mul]
  have hX0 : 0 ≤ X := expect_nonneg fun _ _ => sq_nonneg _
  have h3 : X ≤ ∑ ξ : ZMod D, ∑ ξ' : ZMod D,
      ‖c ξ‖ * ‖c ξ'‖ * (if 2 * (ξ - ξ') = 0 then (1 : ℝ) else 0) := by
    have h4 : ‖(X : ℂ)‖ = X := by
      rw [Complex.norm_real, Real.norm_of_nonneg hX0]
    rw [← h4, h2]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ξ _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ξ' _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_conj]
    by_cases h : 2 * (ξ - ξ') = 0 <;> simp [h]
  have h5 : ∑ ξ : ZMod D, ∑ ξ' : ZMod D,
      ‖c ξ‖ * ‖c ξ'‖ * (if 2 * (ξ - ξ') = 0 then (1 : ℝ) else 0) ≤
      ∑ ξ : ZMod D, ∑ ξ' : ZMod D, ((‖c ξ‖ ^ 2 / 2) * (if 2 * (ξ - ξ') = 0 then (1 : ℝ) else 0) +
        (‖c ξ'‖ ^ 2 / 2) * (if 2 * (ξ - ξ') = 0 then (1 : ℝ) else 0)) := by
    refine Finset.sum_le_sum fun ξ _ => Finset.sum_le_sum fun ξ' _ => ?_
    have hd : (0 : ℝ) ≤ (if 2 * (ξ - ξ') = 0 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    rw [← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ hd
    nlinarith [sq_nonneg (‖c ξ‖ - ‖c ξ'‖)]
  have h6 : ∑ ξ : ZMod D, ∑ ξ' : ZMod D, (‖c ξ‖ ^ 2 / 2) *
      (if 2 * (ξ - ξ') = 0 then (1 : ℝ) else 0) ≤ ∑ ξ : ZMod D, ‖c ξ‖ ^ 2 := by
    calc _ = ∑ ξ : ZMod D, (‖c ξ‖ ^ 2 / 2) * ∑ ξ' : ZMod D,
          (if 2 * (ξ - ξ') = 0 then (1 : ℝ) else 0) := by
          simp_rw [Finset.mul_sum]
      _ ≤ ∑ ξ : ZMod D, (‖c ξ‖ ^ 2 / 2) * 2 :=
          Finset.sum_le_sum fun ξ _ =>
            mul_le_mul_of_nonneg_left (sum_delta_le ξ) (by positivity)
      _ = ∑ ξ : ZMod D, ‖c ξ‖ ^ 2 := Finset.sum_congr rfl fun ξ _ => by ring
  have h7 : ∑ ξ : ZMod D, ∑ ξ' : ZMod D, (‖c ξ'‖ ^ 2 / 2) *
      (if 2 * (ξ - ξ') = 0 then (1 : ℝ) else 0) ≤ ∑ ξ : ZMod D, ‖c ξ‖ ^ 2 := by
    rw [Finset.sum_comm]
    calc _ = ∑ ξ' : ZMod D, (‖c ξ'‖ ^ 2 / 2) * ∑ ξ : ZMod D,
          (if 2 * (ξ - ξ') = 0 then (1 : ℝ) else 0) := by
          simp_rw [Finset.mul_sum]
      _ ≤ ∑ ξ' : ZMod D, (‖c ξ'‖ ^ 2 / 2) * 2 :=
          Finset.sum_le_sum fun ξ' _ =>
            mul_le_mul_of_nonneg_left (sum_delta_le' ξ') (by positivity)
      _ = ∑ ξ : ZMod D, ‖c ξ‖ ^ 2 := Finset.sum_congr rfl fun ξ _ => by ring
  have h8 : ∑ ξ : ZMod D, ∑ ξ' : ZMod D, ((‖c ξ‖ ^ 2 / 2) *
      (if 2 * (ξ - ξ') = 0 then (1 : ℝ) else 0) + (‖c ξ'‖ ^ 2 / 2) *
      (if 2 * (ξ - ξ') = 0 then (1 : ℝ) else 0)) =
      (∑ ξ : ZMod D, ∑ ξ' : ZMod D, (‖c ξ‖ ^ 2 / 2) * (if 2 * (ξ - ξ') = 0 then (1 : ℝ) else 0)) +
      ∑ ξ : ZMod D, ∑ ξ' : ZMod D, (‖c ξ'‖ ^ 2 / 2) * (if 2 * (ξ - ξ') = 0 then (1 : ℝ) else 0) := by
    simp_rw [Finset.sum_add_distrib]
  linarith

/-- The `L²` bound for the fibre average (blueprint N32, step 2):
`E_β ‖E_λ f(β-λ) g(β+λ)‖² ≤ 2 (max_ξ ‖F_D f(ξ)‖)² E_β ‖g β‖²`. -/
theorem expect_norm_sq_avgFibre_le (f g : ZMod D → ℂ) :
    𝔼 β : ZMod D, ‖avgFibre f g β‖ ^ 2 ≤ 2 * fibreMax f ^ 2 * 𝔼 β : ZMod D, ‖g β‖ ^ 2 := by
  simp_rw [avgFibre_eq]
  refine (expect_norm_sq_le _).trans ?_
  have h1 : ∀ ξ : ZMod D, ‖dft f ξ * dft g ξ‖ ^ 2 ≤ fibreMax f ^ 2 * ‖dft g ξ‖ ^ 2 := by
    intro ξ
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (norm_dft_le_fibreMax f ξ) 2) (sq_nonneg _)
  calc 2 * ∑ ξ : ZMod D, ‖dft f ξ * dft g ξ‖ ^ 2
      ≤ 2 * ∑ ξ : ZMod D, fibreMax f ^ 2 * ‖dft g ξ‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ξ _ => h1 ξ) (by norm_num)
    _ = 2 * fibreMax f ^ 2 * 𝔼 β : ZMod D, ‖g β‖ ^ 2 := by
        rw [parseval g, ← Finset.mul_sum, mul_assoc]

/-- The `L¹` bound for the fibre average (blueprint N32, step 3, in one fibre):
`E_β ‖E_λ f(β-λ) g(β+λ)‖ ≤ √2 (max_ξ ‖F_D f(ξ)‖) (E_β ‖g β‖²)^{1/2}`. -/
theorem l1_avgFibre_le (f g : ZMod D → ℂ) :
    l1 (avgFibre f g) ≤ √2 * fibreMax f * l2 g := by
  refine (l1_le_l2 _).trans ?_
  unfold l2
  have h := expect_norm_sq_avgFibre_le f g
  calc √(𝔼 β : ZMod D, ‖avgFibre f g β‖ ^ 2)
      ≤ √(2 * fibreMax f ^ 2 * 𝔼 β : ZMod D, ‖g β‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = √2 * fibreMax f * √(𝔼 β : ZMod D, ‖g β‖ ^ 2) := by
        rw [Real.sqrt_mul (x := 2 * fibreMax f ^ 2) (by positivity),
          Real.sqrt_mul (x := 2) (by norm_num), Real.sqrt_sq (fibreMax_nonneg f)]

end PrimeBHT.Periodic
