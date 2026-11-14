module

public import PrimeBHT.TimeFrequency.X2.Disc.Parseval
public import PrimeBHT.TimeFrequency.X2.Disc.Mult
public import PrimeBHT.TimeFrequency.X2.Disc.WhitneyForm

/-!
# X2, node V05 (R4a): the Whitney pair terms as model integrals

For a scale `k`, a V04 index `n` and a Whitney pair `(n₁, n₂ = n₁ + d)` the pair term
`pairTerm … = ∫∫ φ(ξ₁/b - n₁) φ(ξ₂/b - n₂) Π(F̂₁(τ_a ·), F̂₂(τ_{-a} ·), F̂₃)` (`b = 2^{k-7}`, `a = n 2^{-k}/8`) equals the
x-space integral `∫ Π(T_{μ₁}F₁, T_{μ₂}F₂, T_{μ₃}F₃)` with the unit multipliers
`μ₁ = φ(·/b - n₁) e^{-2πi a ·}`, `μ₂ = φ(·/b - n₂) e^{2πi a ·}`, `μ₃ = φ₃(·/b - n₁ - n₂)` (`pairTerm_eq_integral`).
-/

@[expose] public noncomputable section

open MeasureTheory Complex
open scoped FourierTransform SchwartzMap ComplexConjugate Real ContDiff
open PrimeBHT.Statements (yNorm tensorFun tensorFourier multiplierForm)

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Disc

/-- The bump scale `b_k = 2^{k-7}` (`ℓ = 4 b_k = 2^{k-5}`, box scale `5 - k`). -/
def bk (k : ℤ) : ℝ := (2 : ℝ) ^ (k - 7)

theorem bk_pos (k : ℤ) : 0 < bk k := zpow_pos (by norm_num) _

theorem bk_eq_ell (k : ℤ) : ell (5 - k) / 4 = bk k := by
  unfold ell bk
  rw [show -(5 - k) = (k - 7) + 2 by ring, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num

/-- Unit multipliers of a pair term. -/
def mu1 (k n n₁ : ℤ) (ξ : ℝ) : ℂ :=
  (wphi (ξ / bk k - n₁) : ℂ) * Complex.exp (((-2 * π * symbolShift (k, n) * ξ : ℝ) : ℂ) * Complex.I)

def mu2 (k n n₁ d : ℤ) (ξ : ℝ) : ℂ :=
  (wphi (ξ / bk k - ((n₁ + d : ℤ) : ℝ)) : ℂ) * Complex.exp (((2 * π * symbolShift (k, n) * ξ : ℝ) : ℂ) * Complex.I)

def mu3 (k n₁ d : ℤ) (ξ : ℝ) : ℂ := (wphi3 (ξ / bk k - ((n₁ + (n₁ + d) : ℤ) : ℝ)) : ℂ)

/-- The pair term (Fourier side). -/
def pairTerm {P : ℕ} [NeZero P] (T : Form P) (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) (k n n₁ d : ℤ) : ℂ :=
  ∫ ξ : ℝ × ℝ, ((wphi (ξ.1 / bk k - n₁) * wphi (ξ.2 / bk k - ((n₁ + d : ℤ) : ℝ)) : ℝ) : ℂ) *
    T (tensorFourier (fun A => schwartzTranslate (symbolShift (k, n)) (f₁ A)) ξ.1)
      (tensorFourier (fun A => schwartzTranslate (-symbolShift (k, n)) (f₂ A)) ξ.2)
      (tensorFourier f₃ (ξ.1 + ξ.2))

theorem hasCompactSupport_wphi_comp (b n : ℝ) (hb : 0 < b) :
    HasCompactSupport (fun ξ : ℝ => wphi (ξ / b - n)) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := b * (n - 1 / 2)) (b := b * (n + 3 / 2))) fun ξ hξ => ?_
  by_contra h
  obtain ⟨h1, h2⟩ := wphi_ne_zero h
  apply hξ
  constructor
  · have := mul_le_mul_of_nonneg_left (show n - 1 / 2 ≤ ξ / b by linarith) hb.le
    rwa [mul_div_cancel₀ _ hb.ne'] at this
  · have := mul_le_mul_of_nonneg_left (show ξ / b ≤ n + 3 / 2 by linarith) hb.le
    rwa [mul_div_cancel₀ _ hb.ne'] at this

theorem hasCompactSupport_wphi3_comp (b n : ℝ) (hb : 0 < b) :
    HasCompactSupport (fun ξ : ℝ => wphi3 (ξ / b - n)) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := b * (n - 3 / 2)) (b := b * (n + 7 / 2))) fun ξ hξ => ?_
  by_contra h
  obtain ⟨h1, h2⟩ := wphi3_ne_zero h
  apply hξ
  constructor
  · have := mul_le_mul_of_nonneg_left (show n - 3 / 2 ≤ ξ / b by linarith) hb.le
    rwa [mul_div_cancel₀ _ hb.ne'] at this
  · have := mul_le_mul_of_nonneg_left (show ξ / b ≤ n + 7 / 2 by linarith) hb.le
    rwa [mul_div_cancel₀ _ hb.ne'] at this

theorem contDiff_mu1 (k n n₁ : ℤ) : ContDiff ℝ ∞ (mu1 k n n₁) := by
  unfold mu1
  have h1 : ContDiff ℝ ∞ (fun ξ : ℝ => (wphi (ξ / bk k - n₁) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_wphi.comp ((contDiff_id.div_const _).sub contDiff_const))
  have h2 : ContDiff ℝ ∞ (fun ξ : ℝ => Complex.exp (((-2 * π * symbolShift (k, n) * ξ : ℝ) : ℂ) * Complex.I)) :=
    Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const)
  exact h1.mul h2

theorem contDiff_mu2 (k n n₁ d : ℤ) : ContDiff ℝ ∞ (mu2 k n n₁ d) := by
  unfold mu2
  have h1 : ContDiff ℝ ∞ (fun ξ : ℝ => (wphi (ξ / bk k - ((n₁ + d : ℤ) : ℝ)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_wphi.comp ((contDiff_id.div_const _).sub contDiff_const))
  have h2 : ContDiff ℝ ∞ (fun ξ : ℝ => Complex.exp (((2 * π * symbolShift (k, n) * ξ : ℝ) : ℂ) * Complex.I)) :=
    Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const)
  exact h1.mul h2

theorem contDiff_mu3 (k n₁ d : ℤ) : ContDiff ℝ ∞ (mu3 k n₁ d) := by
  unfold mu3
  exact Complex.ofRealCLM.contDiff.comp (contDiff_wphi3.comp ((contDiff_id.div_const _).sub contDiff_const))

theorem hasCompactSupport_mu1 (k n n₁ : ℤ) : HasCompactSupport (mu1 k n n₁) := by
  have := (hasCompactSupport_wphi_comp (bk k) n₁ (bk_pos k)).comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero
  exact this.mul_right

theorem hasCompactSupport_mu2 (k n n₁ d : ℤ) : HasCompactSupport (mu2 k n n₁ d) := by
  have := (hasCompactSupport_wphi_comp (bk k) ((n₁ + d : ℤ) : ℝ) (bk_pos k)).comp_left
    (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero
  exact this.mul_right

theorem hasCompactSupport_mu3 (k n₁ d : ℤ) : HasCompactSupport (mu3 k n₁ d) := by
  exact (hasCompactSupport_wphi3_comp (bk k) ((n₁ + (n₁ + d) : ℤ) : ℝ) (bk_pos k)).comp_left
    (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero

/-- **R4a.**  The pair term is the model integral with the unit multipliers. -/
theorem pairTerm_eq_integral {P : ℕ} [NeZero P] (T : Form P) (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) (k n n₁ d : ℤ) :
    pairTerm T f₁ f₂ f₃ k n n₁ d =
      ∫ x, T (tmult (mu1 k n n₁) (tensorFun f₁) x) (tmult (mu2 k n n₁ d) (tensorFun f₂) x)
        (tmult (mu3 k n₁ d) (tensorFun f₃) x) := by
  rw [integral_form_tmult T (contDiff_mu1 k n n₁) (hasCompactSupport_mu1 k n n₁)
    (contDiff_mu2 k n n₁ d) (hasCompactSupport_mu2 k n n₁ d) (contDiff_mu3 k n₁ d) (hasCompactSupport_mu3 k n₁ d)]
  unfold pairTerm
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [tensorFourier_schwartzTranslate, tensorFourier_schwartzTranslate]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  by_cases h0 : wphi (ξ.1 / bk k - n₁) * wphi (ξ.2 / bk k - ((n₁ + d : ℤ) : ℝ)) = 0
  · rw [h0]
    rcases mul_eq_zero.1 h0 with h | h
    · simp only [mu1, h, Complex.ofReal_zero, zero_mul, Complex.ofReal_zero]
    · simp only [mu2, h, Complex.ofReal_zero, zero_mul, mul_zero, Complex.ofReal_zero]
  · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h0
    obtain ⟨a1, a2⟩ := wphi_ne_zero h1
    obtain ⟨b1, b2⟩ := wphi_ne_zero h2
    have h3 : wphi3 ((ξ.1 + ξ.2) / bk k - ((n₁ + (n₁ + d) : ℤ) : ℝ)) = 1 := by
      apply wphi3_eq_one
      · push_cast at b1 ⊢; rw [add_div]; linarith
      · push_cast at b2 ⊢; rw [add_div]; linarith
    simp only [mu1, mu2, mu3, h3, Complex.ofReal_one, map_one, mul_one]
    push_cast
    ring

end PrimeBHT.TimeFrequency.X2.Disc
