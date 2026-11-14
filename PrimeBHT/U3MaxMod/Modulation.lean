module

public import PrimeBHT.U3MaxMod.Bridge
public import PrimeCarleson.Proof.Goal0.Basic

/-!
# `l:U3maxmod`, part 6: modulation invariance (G3) and the modulated bound

`‖(e(θ ·) W)‖_{U³([N])} = ‖W‖_{U³([N])}`, hence the plain-average bound holds for
`W(n) e(θ n)` with the same constant.
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeBHT.U3MaxMod

open PrimeCarleson PrimeCarleson.Proof.Goal0

/-- The quadratic phase identity: the phase of `Δ_{a,b}` of a linear phase is trivial. -/
lemma e_quad (θ : ℝ) (x a b : ℤ) :
    e (θ * x) * conj (e (θ * ((x + a : ℤ) : ℝ))) * conj (e (θ * ((x + b : ℤ) : ℝ))) *
      e (θ * ((x + b + a : ℤ) : ℝ)) = 1 := by
  rw [← e_neg, ← e_neg, ← e_add, ← e_add, ← e_add]
  have : θ * (x : ℝ) + -(θ * ((x + a : ℤ) : ℝ)) + -(θ * ((x + b : ℤ) : ℝ)) +
      θ * ((x + b + a : ℤ) : ℝ) = 0 := by push_cast; ring
  rw [this, e_zero]

lemma multDiff_two_mod (θ : ℝ) (F : ℤ → ℂ) (h : Fin 2 → ℤ) (x : ℤ) :
    multDiff 2 h (fun n => e (θ * n) * F n) x = multDiff 2 h F x := by
  have h2 := e_quad θ x (h 0) (h 1)
  have : ∀ G : ℤ → ℂ, multDiff 2 h G x =
      G x * conj (G (x + h 0)) * conj (G (x + h 1) * conj (G (x + h 1 + h 0))) := fun G => rfl
  rw [this, this]
  simp only [map_mul, Complex.conj_conj]
  linear_combination (F x * conj (F (x + h 0)) * conj (F (x + h 1)) * F (x + h 1 + h 0)) * h2

lemma multDiff_three_mod (θ : ℝ) (F : ℤ → ℂ) (h : Fin 3 → ℤ) (x : ℤ) :
    multDiff 3 h (fun n => e (θ * n) * F n) x = multDiff 3 h F x := by
  show multDiff 2 (Fin.init h) _ x * conj (multDiff 2 (Fin.init h) _ (x + h (Fin.last 2))) =
    multDiff 2 (Fin.init h) F x * conj (multDiff 2 (Fin.init h) F (x + h (Fin.last 2)))
  rw [multDiff_two_mod, multDiff_two_mod]

lemma gowersNorm_mod (θ : ℝ) (N : ℕ+) (W : ℤ → ℂ) :
    gowersNorm 3 (restrictInterval N (fun n => e (θ * n) * W n)) =
      gowersNorm 3 (restrictInterval N W) := by
  unfold gowersNorm
  have hfun : ⇑(restrictInterval N (fun n => e (θ * n) * W n)) =
      fun n : ℤ => e (θ * (n : ℝ)) * ⇑(restrictInterval N W) n := by
    funext n
    by_cases hn : n ∈ Finset.Icc (1 : ℤ) N <;> simp [restrictInterval, Finsupp.indicator_apply, hn]
  have : ∀ p : ℤ × (Fin 3 → ℤ),
      multDiff 3 p.2 ⇑(restrictInterval N (fun n => e (θ * n) * W n)) p.1 =
        multDiff 3 p.2 ⇑(restrictInterval N W) p.1 := fun p => by
    rw [hfun, multDiff_three_mod]
  exact congrArg (fun z : ℝ => z ^ ((1 : ℝ) / 2 ^ ((3 : ℕ+) : ℕ)))
    (congrArg Complex.re (tsum_congr fun p => this p))

/-- **(G3)**: modulation by `e(θ n)` preserves `‖·‖_{U³([N])}`. -/
theorem gowersNormInterval_mod (θ : ℝ) (N : ℕ+) (W : ℤ → ℂ) :
    gowersNormInterval 3 N (fun n => e (θ * n) * W n) = gowersNormInterval 3 N W := by
  unfold gowersNormInterval
  rw [gowersNorm_mod]

end PrimeBHT.U3MaxMod
