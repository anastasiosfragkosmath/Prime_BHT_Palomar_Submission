module

public import PrimeCarleson.Frozen.BlockWeight
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# The periodic block: setting and the Cauchy-Schwarz bound (blueprint N30, first half)

`Y_N = ZMod N` with the normalized counting measure `𝔼`. `lam B N` is `Λ_B` on `Y_N`: the
vendored (audited) `blockWeight B` evaluated at `r.val`. For `q ∣ N` for all `q ∈ B` it is the
`N`-periodic function (`lam_intCast`).

`trilinForm Λ F G H = 𝔼_{y,t} Λ(t) F(y-t) G(y+t) conj(H(y))` is `Π_B(F,G,H)` of the blueprint;
`norm_trilinForm_le` is the Cauchy-Schwarz step of N30, and `l2_bilinAvg_le` the resulting
`L² × L² → L²` bound (duality with `H = A_B(F,G)`).
-/

@[expose] public section

namespace PrimeBHT.PeriodicBlock

open Finset PrimeCarleson
open scoped BigOperators ComplexConjugate

/-- The `L²` norm for the normalized counting measure on a finite type: `(𝔼_x ‖F x‖²)^{1/2}`. -/
noncomputable def l2 {X : Type*} [Fintype X] (F : X → ℂ) : ℝ := √(𝔼 x, ‖F x‖ ^ 2)

theorem l2_nonneg {X : Type*} [Fintype X] (F : X → ℂ) : 0 ≤ l2 F := Real.sqrt_nonneg _

theorem l2_sq {X : Type*} [Fintype X] (F : X → ℂ) : l2 F ^ 2 = 𝔼 x, ‖F x‖ ^ 2 :=
  Real.sq_sqrt (expect_nonneg fun _ _ => sq_nonneg _)

/-- `Λ_B` as a function on `Y_N = ℤ/N`: the audited weight `blockWeight B` at the representative
`r.val`. -/
noncomputable def lam (B : Finset ℕ) (N : ℕ) (r : ZMod N) : ℂ := blockWeight B (r.val : ℤ)

/-- `A_B(F,G)(y) = 𝔼_{r ∈ Y_N} Λ(r) F(y - r) G(y + r)` for a weight `Λ` on `Y_N`. -/
noncomputable def bilinAvg {N : ℕ} [NeZero N] (Λ F G : ZMod N → ℂ) (y : ZMod N) : ℂ :=
  𝔼 r, Λ r * F (y - r) * G (y + r)

/-- `Π_B(F,G,H) = 𝔼_y A_B(F,G)(y) conj(H(y))` for a weight `Λ` on `Y_N`. -/
noncomputable def trilinForm {N : ℕ} [NeZero N] (Λ F G H : ZMod N → ℂ) : ℂ :=
  𝔼 y, bilinAvg Λ F G y * conj (H y)

theorem trilinForm_eq {N : ℕ} [NeZero N] (Λ F G H : ZMod N → ℂ) :
    trilinForm Λ F G H = 𝔼 y, 𝔼 t, Λ t * F (y - t) * G (y + t) * conj (H y) := by
  unfold trilinForm bilinAvg
  refine Finset.expect_congr rfl fun y _ => ?_
  rw [Finset.expect_mul]

section CauchySchwarz

variable {N : ℕ} [NeZero N]

theorem expect_sq_shift_sub (F : ZMod N → ℂ) (t : ZMod N) :
    𝔼 y, ‖F (y - t)‖ ^ 2 = 𝔼 y, ‖F y‖ ^ 2 :=
  Fintype.expect_equiv (Equiv.subRight t) _ _ fun _ => rfl

theorem expect_sq_shift_add (F : ZMod N → ℂ) (y : ZMod N) :
    𝔼 t, ‖F (y + t)‖ ^ 2 = 𝔼 t, ‖F t‖ ^ 2 :=
  Fintype.expect_equiv (Equiv.addLeft y) _ _ fun _ => rfl

theorem expect_pair {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M] (f : ZMod N × ZMod N → M) :
    𝔼 p, f p = 𝔼 y, 𝔼 t, f (y, t) := by
  rw [← Finset.univ_product_univ, Finset.expect_product]

theorem expect_sq_a (Λ F : ZMod N → ℂ) :
    𝔼 p : ZMod N × ZMod N, (‖Λ p.2‖ * ‖F (p.1 - p.2)‖) ^ 2 = l2 Λ ^ 2 * l2 F ^ 2 := by
  rw [l2_sq, l2_sq, expect_pair, Finset.expect_comm]
  simp_rw [mul_pow, ← Finset.mul_expect, expect_sq_shift_sub]
  rw [← Finset.expect_mul]

theorem expect_sq_b (G H : ZMod N → ℂ) :
    𝔼 p : ZMod N × ZMod N, (‖G (p.1 + p.2)‖ * ‖H p.1‖) ^ 2 = l2 G ^ 2 * l2 H ^ 2 := by
  rw [l2_sq, l2_sq, expect_pair]
  simp_rw [mul_pow, ← Finset.expect_mul, expect_sq_shift_add]
  rw [← Finset.mul_expect]

/-- **N30, Cauchy-Schwarz step.** `|Π_B(F,G,H)| ≤ ‖Λ‖_{L²} ‖F‖_{L²} ‖G‖_{L²} ‖H‖_{L²}`. -/
theorem norm_trilinForm_le (Λ F G H : ZMod N → ℂ) :
    ‖trilinForm Λ F G H‖ ≤ l2 Λ * l2 F * l2 G * l2 H := by
  have h1 : ‖trilinForm Λ F G H‖ ≤
      𝔼 p : ZMod N × ZMod N, (‖Λ p.2‖ * ‖F (p.1 - p.2)‖) * (‖G (p.1 + p.2)‖ * ‖H p.1‖) := by
    rw [trilinForm_eq, expect_pair]
    refine (RCLike.norm_expect_le (K := ℂ)).trans ?_
    refine Finset.expect_le_expect fun y _ => ?_
    refine (RCLike.norm_expect_le (K := ℂ)).trans (le_of_eq ?_)
    refine Finset.expect_congr rfl fun t _ => ?_
    simp only [norm_mul, Complex.norm_conj]
    ring
  have h2 := expect_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod N × ZMod N))
    (fun p => ‖Λ p.2‖ * ‖F (p.1 - p.2)‖) (fun p => ‖G (p.1 + p.2)‖ * ‖H p.1‖)
  rw [expect_sq_a, expect_sq_b] at h2
  have h3 : ‖trilinForm Λ F G H‖ ^ 2 ≤ (l2 Λ * l2 F * l2 G * l2 H) ^ 2 := by
    have h4 : 0 ≤ 𝔼 p : ZMod N × ZMod N,
        (‖Λ p.2‖ * ‖F (p.1 - p.2)‖) * (‖G (p.1 + p.2)‖ * ‖H p.1‖) :=
      Finset.expect_nonneg fun _ _ => by positivity
    calc ‖trilinForm Λ F G H‖ ^ 2 ≤ (𝔼 p : ZMod N × ZMod N,
          (‖Λ p.2‖ * ‖F (p.1 - p.2)‖) * (‖G (p.1 + p.2)‖ * ‖H p.1‖)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by have := l2_nonneg Λ; have := l2_nonneg F
                                       have := l2_nonneg G; have := l2_nonneg H; positivity)).1 h3

/-- **N30, `L² × L² → L²` bound** (duality, `H = A_B(F,G)`):
`‖A_B(F,G)‖_{L²} ≤ ‖Λ‖_{L²} ‖F‖_{L²} ‖G‖_{L²}`. -/
theorem l2_bilinAvg_le (Λ F G : ZMod N → ℂ) :
    l2 (bilinAvg Λ F G) ≤ l2 Λ * l2 F * l2 G := by
  set A := bilinAvg Λ F G with hA
  have h1 : trilinForm Λ F G A = ((l2 A ^ 2 : ℝ) : ℂ) := by
    rw [l2_sq, show (((𝔼 x, ‖A x‖ ^ 2 : ℝ)) : ℂ) = 𝔼 x, ((‖A x‖ ^ 2 : ℝ) : ℂ) from
      RCLike.ofReal_expect (K := ℂ) _ _]
    unfold trilinForm
    refine Finset.expect_congr rfl fun y _ => ?_
    rw [Complex.mul_conj']
    push_cast
    rfl
  have h2 := norm_trilinForm_le Λ F G A
  rw [h1, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at h2
  rcases (l2_nonneg A).eq_or_lt with h0 | hpos
  · rw [← h0]
    have := l2_nonneg Λ; have := l2_nonneg F; have := l2_nonneg G
    positivity
  · have h3 : l2 A * l2 A ≤ (l2 Λ * l2 F * l2 G) * l2 A := by nlinarith
    exact le_of_mul_le_mul_right h3 hpos

end CauchySchwarz

end PrimeBHT.PeriodicBlock
