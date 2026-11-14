module

public import PrimeBHT.TimeFrequency.X2.Psp.O2Decomp

/-!
# X2, V13 O2 (h): the fine part `D_fine` (MTT2 (d5), (d6))

`Dfine_eq`: `D_fine = - Σ_{τ<σ} (Σ_{x ∈ leftEnds τ} Err^ℓ_{τ,x} - Σ_{x ∈ rightEnds τ} Err^r_{τ,x})`, `Err_{τ,x} = H_x S_τF - e(θ ·) β_x c_τ(x)`;
`fine_bound_abstract`: `‖∫ K(x₀ - ·) D_fine‖ ≤ Σ_{τ<σ} Σ_{x ∈ ∂Ẽ_τ} C (A_g + A_c) 2^{-2(σ-τ)} ⟨(x₀ - x)/2^σ⟩^{-M}` from the single-endpoint
estimate `err_endpoint_theta`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform ContDiff Real Convolution
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

theorem disjoint_leftEnds_rightEnds (TA : Finset TriTile) (W : ℤ × ℤ) (τ : ℤ) :
    Disjoint (leftEnds TA W τ) (rightEnds TA W τ) := by
  rw [Finset.disjoint_left]
  intro x hxl hxr
  obtain ⟨v, hv, hv1, rfl⟩ := mem_leftEndsOf.1 hxl
  obtain ⟨w, hw, hw1, hwe⟩ := mem_rightEndsOf.1 hxr
  have hp := zpow_two_pos τ
  have : (v : ℝ) = (w : ℝ) + 1 := by
    have h2 : (2 : ℝ) ^ τ * (v : ℝ) = (2 : ℝ) ^ τ * ((w : ℝ) + 1) := hwe.symm
    exact mul_left_cancel₀ hp.ne' h2
  have hvw : v = w + 1 := by exact_mod_cast this
  exact hv1 (by rw [hvw]; simpa using hw)

section Fine

variable {P : ℕ} [NeZero P]

omit [NeZero P] in
theorem ovS_bdd (J : ℕ) (θ : ℝ) (τ : ℤ) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {B : ℝ} (hB : ∀ z y, ‖F z y‖ ≤ B) :
    ∃ Bs : ℝ, ∀ z y, ‖ovS J θ τ F z y‖ ≤ Bs := by
  have h1 : ∀ τ' : ℤ, ∃ B' : ℝ, ∀ z y, ‖tmult (lowSym θ τ') F z y‖ ≤ B' := fun τ' => by
    have hc := contDiff_lowSym θ τ'
    have hs : HasCompactSupport (lowSym θ τ') :=
      hasCompactSupport_of_far (c := θ) (r := 17 / 4 * (2 : ℝ) ^ (-τ')) fun ξ hξ => lowSym_eq_zero hξ.le
    exact ⟨B * ∫ w, ‖𝓕⁻ (lowSym θ τ') w‖, fun z y =>
      norm_tm_le_gen hc hs (measurable_pi_iff.1 hF y) (fun w => hB w y) z⟩
  obtain ⟨B1, hB1⟩ := h1 τ
  obtain ⟨B2, hB2⟩ := h1 (τ + (J : ℤ))
  refine ⟨B1 + B2, fun z y => ?_⟩
  unfold ovS
  simp only [Pi.sub_apply]
  exact (norm_sub_le _ _).trans (add_le_add (hB1 z y) (hB2 z y))

/-- the endpoint error integrand -/
def errAt (J : ℕ) (θ : ℝ) (F : ℝ → ZMod P → ℂ) (τ : ℤ) (x : ℝ) (β : ℝ → ℝ) (z : ℝ) : ZMod P → ℂ :=
  fun y => ((heav (z - x) : ℝ) : ℂ) * ovS J θ τ F z y - ovPhase θ z * ((β z : ℝ) : ℂ) * ovCoef J θ F τ x y

theorem measurable_errAt (J : ℕ) (θ : ℝ) (F : ℝ → ZMod P → ℂ) (hF : Measurable F) (τ : ℤ) (x : ℝ) {β : ℝ → ℝ}
    (hβ : Measurable β) : Measurable (errAt J θ F τ x β) := by
  refine measurable_pi_iff.2 fun y => ?_
  unfold errAt
  have h1 : Measurable (fun z : ℝ => ((heav (z - x) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (measurable_heav.comp (measurable_id.sub measurable_const))
  have h2 := (measurable_pi_iff.1 (measurable_ovS J θ τ hF)) y
  have h3 : Measurable (ovPhase θ) := (continuous_ovPhase θ).measurable
  have h4 : Measurable (fun z : ℝ => ((β z : ℝ) : ℂ)) := Complex.measurable_ofReal.comp hβ
  exact (h1.mul h2).sub ((h3.mul h4).mul measurable_const)

omit [NeZero P] in
theorem norm_errAt_le (J : ℕ) (θ : ℝ) (F : ℝ → ZMod P → ℂ) (τ : ℤ) (x : ℝ) {β : ℝ → ℝ} {Bs : ℝ}
    (hBs : ∀ z y, ‖ovS J θ τ F z y‖ ≤ Bs) (hβ : ∀ z, |β z| ≤ 8) (z : ℝ) (y : ZMod P) :
    ‖errAt J θ F τ x β z y‖ ≤ Bs + 8 * ‖ovCoef J θ F τ x y‖ := by
  unfold errAt
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    calc ‖((heav (z - x) : ℝ) : ℂ)‖ * ‖ovS J θ τ F z y‖ ≤ 1 * Bs :=
          mul_le_mul (norm_heav _) (hBs z y) (norm_nonneg _) zero_le_one
      _ = Bs := one_mul _
  · rw [norm_mul, norm_mul, norm_ovPhase, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hβ z) (norm_nonneg _)

omit [NeZero P] in
/-- `Dfine = - Σ_τ (Σ_left Err^ℓ - Σ_right Err^r)` -/
theorem Dfine_eq {J : ℕ} {s₀ lo : ℤ} (TA : Finset TriTile) (W : ℤ × ℤ) (θ : ℝ) (F : ℝ → ZMod P → ℂ) (σ : ℤ) (z : ℝ) :
    Dfine J s₀ lo TA W θ F (fun τ x => ovCoef J θ F τ x) (fun τ x => -ovCoef J θ F τ x) σ z =
      -∑ τ ∈ (ovScales J s₀ lo W.1).filter (fun τ => τ < σ),
        ((∑ x ∈ leftEnds TA W τ, errAt J θ F τ x (leftPhi τ x) z) -
          ∑ x ∈ rightEnds TA W τ, errAt J θ F τ x (rightPhi τ x) z) := by
  unfold Dfine
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hind : (eTil TA W τ).indicator (ovS J θ τ F) z =
      (∑ x ∈ leftEnds TA W τ, ((heav (z - x) : ℝ) : ℂ) • ovS J θ τ F z) -
        ∑ x ∈ rightEnds TA W τ, ((heav (z - x) : ℝ) : ℂ) • ovS J θ τ F z := by
    have h := indicator_eTil_eq_heaviside TA W τ z
    rw [← Finset.sum_smul, ← Finset.sum_smul, ← sub_smul]
    have : ((∑ x ∈ leftEnds TA W τ, ((heav (z - x) : ℝ) : ℂ)) - ∑ x ∈ rightEnds TA W τ, ((heav (z - x) : ℝ) : ℂ)) =
        (((if z ∈ eTil TA W τ then (1 : ℝ) else 0 : ℝ)) : ℂ) := by
      rw [h]; push_cast; rfl
    rw [this]
    by_cases hz : z ∈ eTil TA W τ
    · simp [hz]
    · simp [hz]
  unfold bumpAt
  rw [hind]
  have e1 : ∀ x : ℝ, errAt J θ F τ x (leftPhi τ x) z =
      ((heav (z - x) : ℝ) : ℂ) • ovS J θ τ F z - (ovPhase θ z * ((leftPhi τ x z : ℝ) : ℂ)) • ovCoef J θ F τ x := by
    intro x; funext y; unfold errAt; simp [smul_eq_mul]
  have e2 : ∀ x : ℝ, errAt J θ F τ x (rightPhi τ x) z =
      ((heav (z - x) : ℝ) : ℂ) • ovS J θ τ F z - (ovPhase θ z * ((rightPhi τ x z : ℝ) : ℂ)) • ovCoef J θ F τ x := by
    intro x; funext y; unfold errAt; simp [smul_eq_mul]
  simp only [e1, e2, Finset.sum_sub_distrib, smul_neg, Finset.sum_neg_distrib]
  abel

theorem integrable_K_errAt {m₀ : ℝ → ℂ} (hm₀ : ContDiff ℝ ∞ m₀) (hm₀c : HasCompactSupport m₀) (J : ℕ) (θ : ℝ)
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {BF : ℝ} (hBF : ∀ z y, ‖F z y‖ ≤ BF) (τ : ℤ) (x : ℝ) {β : ℝ → ℝ}
    (hβ : Measurable β) (hβ8 : ∀ z, |β z| ≤ 8) (x₀ : ℝ) (y : ZMod P) :
    Integrable (fun z => 𝓕⁻ m₀ (x₀ - z) * errAt J θ F τ x β z y) := by
  obtain ⟨hkc, hki⟩ := kernel_facts hm₀ hm₀c
  obtain ⟨Bs, hBs⟩ := ovS_bdd J θ τ hF hBF
  exact integrable_kmul hki (f := fun z => errAt J θ F τ x β z y)
    ((measurable_pi_iff.1 (measurable_errAt J θ F hF τ x hβ)) y) (B := Bs + 8 * ‖ovCoef J θ F τ x y‖)
    (fun z => norm_errAt_le J θ F τ x hBs hβ8 z y) x₀ hkc

theorem integrable_K_Dfine {m : ℝ → ℂ} (hm : ContDiff ℝ ∞ m) (hmc : HasCompactSupport m) (J : ℕ) (s₀ lo : ℤ)
    (TA : Finset TriTile) (W : ℤ × ℤ) (θ : ℝ) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {BF : ℝ}
    (hBF : ∀ z y, ‖F z y‖ ≤ BF) (σ : ℤ) (x₀ : ℝ) (y : ZMod P) :
    Integrable (fun z => 𝓕⁻ m (x₀ - z) *
      Dfine J s₀ lo TA W θ F (fun τ x => ovCoef J θ F τ x) (fun τ x => -ovCoef J θ F τ x) σ z y) := by
  have hbl : ∀ τ x, Integrable (fun z => 𝓕⁻ m (x₀ - z) * errAt J θ F τ x (leftPhi τ x) z y) := fun τ x =>
    integrable_K_errAt hm hmc J θ hF hBF τ x (continuous_leftPhi τ x).measurable (fun z => by
      rw [abs_of_nonneg (leftPhi_nonneg τ x z)]; exact leftPhi_le τ x z) x₀ y
  have hbr : ∀ τ x, Integrable (fun z => 𝓕⁻ m (x₀ - z) * errAt J θ F τ x (rightPhi τ x) z y) := fun τ x =>
    integrable_K_errAt hm hmc J θ hF hBF τ x (continuous_rightPhi τ x).measurable (fun z => by
      rw [abs_of_nonneg (rightPhi_nonneg τ x z)]; exact rightPhi_le τ x z) x₀ y
  have e : (fun z => 𝓕⁻ m (x₀ - z) *
      Dfine J s₀ lo TA W θ F (fun τ x => ovCoef J θ F τ x) (fun τ x => -ovCoef J θ F τ x) σ z y) =
      fun z => -∑ τ ∈ (ovScales J s₀ lo W.1).filter (fun τ => τ < σ),
        ((∑ x ∈ leftEnds TA W τ, 𝓕⁻ m (x₀ - z) * errAt J θ F τ x (leftPhi τ x) z y) -
          ∑ x ∈ rightEnds TA W τ, 𝓕⁻ m (x₀ - z) * errAt J θ F τ x (rightPhi τ x) z y) := by
    funext z
    rw [Dfine_eq]
    simp only [Pi.neg_apply, Finset.sum_apply, Pi.sub_apply, mul_neg, Finset.mul_sum, mul_sub]
  rw [e]
  refine Integrable.neg (integrable_finsetSum _ fun τ _ => ?_)
  exact (integrable_finsetSum _ fun x _ => hbl τ x).sub (integrable_finsetSum _ fun x _ => hbr τ x)

/-- **The fine part (MTT2 (d5), (d6)).** -/
theorem fine_bound_abstract {J : ℕ} (_hJ : 0 < J) {s₀ lo : ℤ} (TA : Finset TriTile) (W : ℤ × ℤ) {θ : ℝ}
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {BF : ℝ} (hBF : ∀ z y, ‖F z y‖ ≤ BF) {σ : ℤ} {M : ℕ} {C₀ : ℝ}
    {m : ℝ → ℂ} (hm : Sym0 σ M C₀ (fun ξ => m (ξ + θ))) {Ag N A₁ : ℝ} (hAg : 0 ≤ Ag) (hN : 0 ≤ N) (hA₁ : 0 ≤ A₁)
    {q : ℕ} (hq : N + 2 * ((M : ℝ) + 3) ≤ q)
    (hτσ : ∀ τ ∈ (ovScales J s₀ lo W.1).filter (fun τ => τ < σ), τ + (J : ℤ) ≤ σ)
    (hgrow : ∀ τ ∈ (ovScales J s₀ lo W.1).filter (fun τ => τ < σ), ∀ x ∈ bdryEnds TA W τ, ∀ b,
      yNorm 2 (ovS J θ τ F b) ≤ Ag * jb ((b - x) / (2 : ℝ) ^ τ) ^ N)
    (hcn : ∀ τ ∈ (ovScales J s₀ lo W.1).filter (fun τ => τ < σ), ∀ x ∈ bdryEnds TA W τ,
      yNorm 2 (ovCoef J θ F τ x) ≤ A₁) (x₀ : ℝ) :
    yNorm 2 (fun y => ∫ z, 𝓕⁻ m (x₀ - z) *
        Dfine J s₀ lo TA W θ F (fun τ x => ovCoef J θ F τ x) (fun τ x => -ovCoef J θ F τ x) σ z y) ≤
      ∑ τ ∈ (ovScales J s₀ lo W.1).filter (fun τ => τ < σ), ∑ x ∈ bdryEnds TA W τ,
        (endC3 M C₀ * 2 ^ M * (2 * endQ J M q N * ((2 : ℝ) ^ ((J : ℤ) + 1)) ^ 2 + 1)) * (Ag + A₁) *
          ((2 : ℝ) ^ (τ - σ)) ^ 2 * jb ((x₀ - x) / (2 : ℝ) ^ σ) ^ (-(M : ℝ)) := by
  set Lm := (ovScales J s₀ lo W.1).filter (fun τ => τ < σ) with hLm
  -- the vectors `I(τ, x, β)`
  set Iv : ℤ → ℝ → (ℝ → ℝ) → ZMod P → ℂ := fun τ x β y =>
    ∫ z, 𝓕⁻ m (x₀ - z) * errAt J θ F τ x β z y with hIv
  -- `m` as a shifted multiplier
  set m₀ : ℝ → ℂ := fun ξ => m (ξ + θ) with hm₀
  have hmm : m = fun ξ => m₀ (ξ - θ) := funext fun ξ => by simp [hm₀]
  have hm₀c : HasCompactSupport m₀ := hm.compact
  have hKint : ∀ τ x (β : ℝ → ℝ), Measurable β → (∀ z, |β z| ≤ 8) → ∀ y,
      Integrable (fun z => 𝓕⁻ m (x₀ - z) * errAt J θ F τ x β z y) := by
    intro τ x β hβm hβ8 y
    have hmc : ContDiff ℝ ∞ m := by
      rw [hmm]; exact hm.smooth.comp (contDiff_id.sub contDiff_const)
    have hmcs : HasCompactSupport m := by
      rw [hmm]
      have : HasCompactSupport (fun ξ => m₀ (ξ - θ)) := by
        have := hm.compact
        exact this.comp_homeomorph (Homeomorph.subRight θ)
      exact this
    exact integrable_K_errAt hmc hmcs J θ hF hBF τ x hβm hβ8 x₀ y
  have hcoord : ∀ y, ∫ z, 𝓕⁻ m (x₀ - z) *
        Dfine J s₀ lo TA W θ F (fun τ x => ovCoef J θ F τ x) (fun τ x => -ovCoef J θ F τ x) σ z y =
      -∑ τ ∈ Lm, ((∑ x ∈ leftEnds TA W τ, Iv τ x (leftPhi τ x) y) - ∑ x ∈ rightEnds TA W τ, Iv τ x (rightPhi τ x) y) := by
    intro y
    have e : (fun z => 𝓕⁻ m (x₀ - z) *
        Dfine J s₀ lo TA W θ F (fun τ x => ovCoef J θ F τ x) (fun τ x => -ovCoef J θ F τ x) σ z y) =
        fun z => -∑ τ ∈ Lm, ((∑ x ∈ leftEnds TA W τ, 𝓕⁻ m (x₀ - z) * errAt J θ F τ x (leftPhi τ x) z y) -
          ∑ x ∈ rightEnds TA W τ, 𝓕⁻ m (x₀ - z) * errAt J θ F τ x (rightPhi τ x) z y) := by
      funext z
      rw [Dfine_eq]
      simp only [Pi.neg_apply, Finset.sum_apply, Pi.sub_apply, mul_neg, Finset.mul_sum, mul_sub]
      rfl
    have hbl : ∀ τ x, Integrable (fun z => 𝓕⁻ m (x₀ - z) * errAt J θ F τ x (leftPhi τ x) z y) := fun τ x =>
      hKint τ x (leftPhi τ x) (continuous_leftPhi τ x).measurable (fun z => by
        rw [abs_of_nonneg (leftPhi_nonneg τ x z)]; exact leftPhi_le τ x z) y
    have hbr : ∀ τ x, Integrable (fun z => 𝓕⁻ m (x₀ - z) * errAt J θ F τ x (rightPhi τ x) z y) := fun τ x =>
      hKint τ x (rightPhi τ x) (continuous_rightPhi τ x).measurable (fun z => by
        rw [abs_of_nonneg (rightPhi_nonneg τ x z)]; exact rightPhi_le τ x z) y
    have hSL : ∀ τ, Integrable (fun z => ∑ x ∈ leftEnds TA W τ, 𝓕⁻ m (x₀ - z) * errAt J θ F τ x (leftPhi τ x) z y) :=
      fun τ => integrable_finsetSum _ (fun x _ => hbl τ x)
    have hSR : ∀ τ, Integrable (fun z => ∑ x ∈ rightEnds TA W τ, 𝓕⁻ m (x₀ - z) * errAt J θ F τ x (rightPhi τ x) z y) :=
      fun τ => integrable_finsetSum _ (fun x _ => hbr τ x)
    have hST : ∀ τ, Integrable (fun z => (∑ x ∈ leftEnds TA W τ, 𝓕⁻ m (x₀ - z) * errAt J θ F τ x (leftPhi τ x) z y) -
        ∑ x ∈ rightEnds TA W τ, 𝓕⁻ m (x₀ - z) * errAt J θ F τ x (rightPhi τ x) z y) := fun τ => (hSL τ).sub (hSR τ)
    rw [e, integral_neg]
    congr 1
    rw [integral_finsetSum _ (fun τ _ => hST τ)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [integral_sub (hSL τ) (hSR τ), integral_finsetSum _ (fun x _ => hbl τ x), integral_finsetSum _ (fun x _ => hbr τ x)]
  have hvec : (fun y => ∫ z, 𝓕⁻ m (x₀ - z) *
        Dfine J s₀ lo TA W θ F (fun τ x => ovCoef J θ F τ x) (fun τ x => -ovCoef J θ F τ x) σ z y) =
      -∑ τ ∈ Lm, ((∑ x ∈ leftEnds TA W τ, Iv τ x (leftPhi τ x)) - ∑ x ∈ rightEnds TA W τ, Iv τ x (rightPhi τ x)) := by
    funext y
    rw [hcoord y]
    simp only [Pi.neg_apply, Finset.sum_apply, Pi.sub_apply]
  rw [hvec, yNorm_neg_ov (by norm_num)]
  -- the bound for a single endpoint
  have hbd : ∀ τ ∈ Lm, ∀ x ∈ bdryEnds TA W τ, ∀ (β : ℝ → ℝ), BumpData ((2 : ℝ) ^ τ) x β →
      yNorm 2 (Iv τ x β) ≤ (endC3 M C₀ * 2 ^ M * (2 * endQ J M q N * ((2 : ℝ) ^ ((J : ℤ) + 1)) ^ 2 + 1)) * (Ag + A₁) *
          ((2 : ℝ) ^ (τ - σ)) ^ 2 * jb ((x₀ - x) / (2 : ℝ) ^ σ) ^ (-(M : ℝ)) := by
    intro τ hτ x hx β hβ
    have := err_endpoint_theta (J := J) (τ := τ) (σ := σ) (hτσ τ hτ) hm hF hBF hAg hN hA₁ hq (hgrow τ hτ x hx)
      (hcn τ hτ x hx) hβ x₀
    have e : Iv τ x β = fun y => ∫ z, 𝓕⁻ m (x₀ - z) *
        (((heav (z - x) : ℝ) : ℂ) * ovS J θ τ F z y - ovPhase θ z * ((β z : ℝ) : ℂ) * ovCoef J θ F τ x y) := rfl
    rw [e]
    exact this
  have hsum : ∀ τ ∈ Lm, yNorm 2 ((∑ x ∈ leftEnds TA W τ, Iv τ x (leftPhi τ x)) - ∑ x ∈ rightEnds TA W τ, Iv τ x (rightPhi τ x)) ≤
      ∑ x ∈ bdryEnds TA W τ, (endC3 M C₀ * 2 ^ M * (2 * endQ J M q N * ((2 : ℝ) ^ ((J : ℤ) + 1)) ^ 2 + 1)) * (Ag + A₁) *
          ((2 : ℝ) ^ (τ - σ)) ^ 2 * jb ((x₀ - x) / (2 : ℝ) ^ σ) ^ (-(M : ℝ)) := by
    intro τ hτ
    refine (yNorm_sub_ov (by norm_num) _ _).trans ?_
    refine (add_le_add (CZ.yNorm_sum_le (by norm_num) _ _) (CZ.yNorm_sum_le (by norm_num) _ _)).trans ?_
    unfold bdryEnds
    rw [Finset.sum_union (disjoint_leftEnds_rightEnds TA W τ)]
    refine add_le_add (Finset.sum_le_sum fun x hx => ?_) (Finset.sum_le_sum fun x hx => ?_)
    · exact hbd τ hτ x (Finset.mem_union_left _ hx) _ (bumpData_leftPhi τ x)
    · exact hbd τ hτ x (Finset.mem_union_right _ hx) _ (bumpData_rightPhi τ x)
  exact (CZ.yNorm_sum_le (by norm_num) _ _).trans (Finset.sum_le_sum hsum)

end Fine

end PrimeBHT.TimeFrequency.X2
