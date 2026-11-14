module

public import PrimeBHT.U3MaxMod.Smooth

/-!
# Node N10: `l:U3maxmod`

Let `N ≥ 1`, `f, g : ℤ →₀ ℂ` finitely supported. Write `‖·‖_{ℓ^p}` for `eLpNorm · p Measure.count` and
`‖W‖_{U³([N])} = PrimeCarleson.gowersNormInterval 3 N W` (the normalized norm of the sealed project).

* `PrimeBHT.U3MaxMod.eLpNorm_bilin_le_gowersNorm` (blueprint (a), unnormalized): for a finitely
  supported `F` with support in `[N]`,
  `‖x ↦ ∑_{n ∈ [N]} F(n) f(x-n) g(x+n)‖_{ℓ²} ≤ √(2N) ‖F‖_{U³(ℤ)} ‖f‖_{ℓ⁴} ‖g‖_{ℓ⁴}`.
* `PrimeBHT.U3MaxMod.eLpNorm_bilinAvg_le` (blueprint (a), normalized): for `W : ℤ → ℂ`,
  `‖x ↦ N⁻¹ ∑_{n ∈ [N]} W(n) f(x-n) g(x+n)‖_{ℓ²} ≤ 2 ‖W‖_{U³([N])} ‖f‖_{ℓ⁴} ‖g‖_{ℓ⁴}`.
* `PrimeBHT.U3MaxMod.eLpNorm_smooth_le` / `eLpNorm_smooth_le_one` (blueprint (b)): for `φ ∈ C²`,
  `supp φ ⊆ [0,1]`, `‖φ‖_∞, ‖φ''‖_∞ ≤ M`: the weight `N⁻¹ φ(n/N)` costs the constant `8 M` instead of `2`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ComplexConjugate ENNReal

set_option autoImplicit false

namespace PrimeBHT.U3MaxMod

open PrimeCarleson

lemma deriv_deriv_ofReal {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) :
    deriv (deriv (fun t => (φ t : ℂ))) = fun t => ((deriv (deriv φ) t : ℝ) : ℂ) := by
  have h1 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have h2 : Differentiable ℝ (deriv φ) := by
    have h := (contDiff_succ_iff_deriv (n := 1) (f := φ)).1 (by exact hφ)
    exact h.2.2.differentiable (by norm_num)
  have e1 : deriv (fun t => (φ t : ℂ)) = fun t => ((deriv φ t : ℝ) : ℂ) := by
    funext t; exact (h1 t).hasDerivAt.ofReal_comp.deriv
  rw [e1]
  funext t; exact (h2 t).hasDerivAt.ofReal_comp.deriv

/-- **`l:U3maxmod` (b)** for a real-valued `φ ∈ C²(ℝ)` with `supp φ ⊆ [0,1]` and
`‖φ‖_∞, ‖φ''‖_∞ ≤ M` (the case `M = 1` is the blueprint's `‖φ‖_{C²} ≤ 1`). -/
theorem eLpNorm_smooth_le_real (N : ℕ+) (W : ℤ → ℂ) (f g : ℤ →₀ ℂ) {φ : ℝ → ℝ} {M : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : Function.support φ ⊆ Set.Icc 0 1) (h0 : ∀ t, |φ t| ≤ M)
    (h2 : ∀ t, |deriv (deriv φ) t| ≤ M) :
    eLpNorm (fun x : ℤ => ∑ n ∈ Finset.Icc (1 : ℤ) N,
        (((N : ℕ) : ℂ)⁻¹ * (φ ((n : ℝ) / (N : ℕ)) : ℂ)) * W n * f (x - n) * g (x + n)) 2
        Measure.count ≤
      ENNReal.ofReal (8 * M * gowersNormInterval 3 N W) * eLpNorm (⇑f) 4 Measure.count *
        eLpNorm (⇑g) 4 Measure.count := by
  refine eLpNorm_smooth_le N W f g (φ := fun t => (φ t : ℂ)) (M := M)
    (by exact Complex.ofRealCLM.contDiff.comp hφ) ?_ (fun t => by simpa using h0 t) ?_
  · intro t ht
    exact hsupp (by simpa using ht)
  · intro t
    rw [deriv_deriv_ofReal hφ]
    simpa using h2 t

end PrimeBHT.U3MaxMod
