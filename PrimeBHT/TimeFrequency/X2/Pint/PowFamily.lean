module

public import PrimeBHT.Interpolation
public import PrimeBHT.Frozen.YNorm

/-!
# X2, V11 / TB-4 shared core, part 1: the power family on the lattice `L^s(Y_P)`

`docs/audits/X2-V11-TB4-plan.md` §4a.  For a vector `v : ZMod P → ℂ` and real parameters `a b a' b'`, the analytic
family `famVec s a b a' b' v z = powFamily (a + b z) (v ·) * (yNorm s v)^(a' + b' z)` (Stein-Weiss change of density in the
fibre `Y_P`, entire in `z`).  With `θ = 2/qX`, `1/s = (1-θ)/s₀ + θ/2` and
`a = s/s₀`, `b = s/2 - s/s₀`, `a' = -s/s₀`, `b' = (qX - s)/2 + s/s₀` one has (`famVec_theta`, `yNorm_famVec`):

* `famVec … θ = v`;
* `yNorm s₀ (famVec … (it)) = 1` (if `v ≠ 0`);
* `yNorm 2 (famVec … (1 + it)) = (yNorm s v) ^ (qX/2)`;

the last two INDEPENDENT of `t`.  The dual family `famVec s' α β α' β' h` of a norming vector `h` (`yNorm s' h = 1`) has
`yNorm s₀' = 1` on `re z = 0` and `yNorm 2 = 1` on `re z = 1` (same lemma with `a' = b' = 0`).

Only the fibre `Y_P` is involved here; the `x`-dependence (`v = F x`) is added in `SingleOp.lean`.
-/

@[expose] public noncomputable section

open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.Interpolation Complex

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Pint

variable {P : ℕ} [NeZero P]

/-- The power family of a vector of `L^s(Y_P)`: `y ↦ powFamily (a + b z) (v y) * (yNorm s v)^(a' + b' z)`. -/
def famVec (s a b a' b' : ℝ) (v : ZMod P → ℂ) (z : ℂ) : ZMod P → ℂ :=
  fun y => powFamily ((a : ℂ) + b * z) (v y) * ((yNorm s v : ℂ) ^ ((a' : ℂ) + b' * z))

theorem famVec_apply (s a b a' b' : ℝ) (v : ZMod P → ℂ) (z : ℂ) (y : ZMod P) :
    famVec s a b a' b' v z y = powFamily ((a : ℂ) + b * z) (v y) * ((yNorm s v : ℂ) ^ ((a' : ℂ) + b' * z)) :=
  rfl

/-- At the point `z = θ` with `a + bθ = 1`, `a' + b'θ = 0` the family is the vector itself. -/
theorem famVec_theta {s a b a' b' : ℝ} (v : ZMod P → ℂ) {θ : ℂ} (h1 : (a : ℂ) + b * θ = 1)
    (h2 : (a' : ℂ) + b' * θ = 0) : famVec s a b a' b' v θ = v := by
  funext y
  rw [famVec_apply, h1, h2, powFamily_one, cpow_zero, mul_one]

theorem yNorm_nonneg (s : ℝ) (v : ZMod P → ℂ) : 0 ≤ yNorm s v := by
  unfold yNorm; positivity

/-- `(yNorm s v)^s = P⁻¹ ∑ ‖v y‖^s` for `s ≠ 0`. -/
theorem yNorm_rpow_self {s : ℝ} (hs : s ≠ 0) (v : ZMod P → ℂ) :
    yNorm s v ^ s = (P : ℝ)⁻¹ * ∑ y, ‖v y‖ ^ s := by
  unfold yNorm
  exact Real.rpow_inv_rpow (by positivity) hs

theorem famVec_of_eq_zero (s a b a' b' : ℝ) {v : ZMod P → ℂ} (hv : v = 0) (z : ℂ) :
    famVec s a b a' b' v z = 0 := by
  funext y
  simp [famVec_apply, hv, powFamily_zero]

theorem re_add_mul (a b : ℝ) (z : ℂ) : ((a : ℂ) + b * z).re = a + b * z.re := by simp

/-- The norm of a member of the family (`v ≠ 0`, `0 < a + b re z`). -/
theorem norm_famVec_apply {s a b a' b' : ℝ} {v : ZMod P → ℂ} (hv : 0 < yNorm s v) {z : ℂ}
    (hz : 0 < a + b * z.re) (y : ZMod P) :
    ‖famVec s a b a' b' v z y‖ = ‖v y‖ ^ (a + b * z.re) * yNorm s v ^ (a' + b' * z.re) := by
  rw [famVec_apply, norm_mul, norm_powFamily (by rw [re_add_mul]; exact hz), re_add_mul,
    norm_cpow_eq_rpow_re_of_pos hv, re_add_mul]

/-- **The mixed-norm identity**: if `(a + b re z) p = s` then `yNorm p (famVec … z) = (yNorm s v)^(s/p + a' + b' re z)`. -/
theorem yNorm_famVec {s a b a' b' p : ℝ} (hp : 0 < p) (hs : s ≠ 0) {v : ZMod P → ℂ} (hv : 0 < yNorm s v)
    {z : ℂ} (hz : 0 < a + b * z.re) (hps : (a + b * z.re) * p = s) :
    yNorm p (famVec s a b a' b' v z) = yNorm s v ^ (s / p + a' + b' * z.re) := by
  set n := yNorm s v with hn
  have hn0 : 0 ≤ n := hv.le
  have hterm : ∀ y, ‖famVec s a b a' b' v z y‖ ^ p = ‖v y‖ ^ s * n ^ ((a' + b' * z.re) * p) := by
    intro y
    rw [norm_famVec_apply hv hz, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (norm_nonneg _),
      hps, ← Real.rpow_mul hn0]
  have hsum : (P : ℝ)⁻¹ * ∑ y, ‖famVec s a b a' b' v z y‖ ^ p = n ^ ((a' + b' * z.re) * p + s) := by
    simp_rw [hterm]
    rw [← Finset.sum_mul, ← mul_assoc, ← yNorm_rpow_self hs v, ← hn, ← Real.rpow_add hv]
    congr 1
    ring
  unfold yNorm
  rw [hsum, ← Real.rpow_mul hn0]
  congr 1
  field_simp
  ring

/-- The family is entire in `z` (for every `y`). -/
theorem yNorm_pos_of_ne_zero (s : ℝ) {v : ZMod P → ℂ} {y : ZMod P} (h0 : v y ≠ 0) :
    0 < yNorm s v := by
  unfold yNorm
  apply Real.rpow_pos_of_pos
  refine mul_pos (inv_pos.2 (Nat.cast_pos.2 (NeZero.pos P))) ?_
  exact Finset.sum_pos' (fun y _ => by positivity)
    ⟨y, Finset.mem_univ _, Real.rpow_pos_of_pos (norm_pos_iff.2 h0) s⟩

theorem differentiable_famVec (s a b a' b' : ℝ) (v : ZMod P → ℂ) (y : ZMod P) :
    Differentiable ℂ (fun z => famVec s a b a' b' v z y) := by
  simp only [famVec_apply]
  rcases eq_or_ne (v y) 0 with h0 | h0
  · simp only [h0, powFamily_zero, zero_mul]
    exact differentiable_const 0
  have hv : 0 < yNorm s v := yNorm_pos_of_ne_zero s h0
  exact (differentiable_powFamily _ _ _).mul
    (Differentiable.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hv.ne')))

end PrimeBHT.TimeFrequency.X2.Pint
