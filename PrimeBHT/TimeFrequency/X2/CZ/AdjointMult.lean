module

public import PrimeBHT.TimeFrequency.X2.CZ.KernelDuality
public import PrimeBHT.TimeFrequency.X2.CZ.MikhlinStrong

/-!
# V08 phase 3: the adjoint of a (truncated, normalized) multiplier kernel

* `IsMikhlin.conj`: `σ ∈ IsMikhlin a₀ B` implies `conj σ ∈ IsMikhlin a₀ B` (the adjoint multiplier is again
  Mikhlin with the same constant);
* `kernelTrunc_conj`: `conj K^N_σ(-x) = K^N_{conj σ}(x)`;
* `adjKernel_normKernel`: the adjoint of the normalized truncated kernel of `σ` is the normalized truncated
  kernel of `conj σ`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology Real ComplexConjugate FourierTransform

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

open PrimeBHT.Statements

theorem iteratedDeriv_conj (a : ℕ) (σ : ℝ → ℂ) (ξ : ℝ) :
    iteratedDeriv a (fun ξ => (starRingEnd ℂ) (σ ξ)) ξ = (starRingEnd ℂ) (iteratedDeriv a σ ξ) := by
  have h := Complex.conjCLE.iteratedFDeriv_comp_left (f := σ) (x := ξ) (i := a)
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
  have h' : iteratedFDeriv ℝ a (fun ξ => (starRingEnd ℂ) (σ ξ)) ξ = _ := h
  rw [h']
  rfl

theorem IsMikhlin.conj {a₀ : ℕ} {B : ℝ} {σ : ℝ → ℂ} (hσ : IsMikhlin a₀ B σ) :
    IsMikhlin a₀ B (fun ξ => (starRingEnd ℂ) (σ ξ)) := by
  refine ⟨Complex.conjCLE.contDiff.comp_contDiffOn hσ.1, fun a ha ξ hξ => ?_⟩
  rw [iteratedDeriv_conj, Complex.norm_conj]
  exact hσ.2 a ha ξ hξ

theorem kernelTrunc_conj (σ : ℝ → ℂ) (N : ℕ) (x : ℝ) :
    (starRingEnd ℂ) (kernelTrunc σ N (-x)) = kernelTrunc (fun ξ => (starRingEnd ℂ) (σ ξ)) N x := by
  unfold kernelTrunc
  rw [Real.fourierInv_eq', Real.fourierInv_eq', ← integral_conj]
  congr 1; ext v
  simp only [symbolTrunc, smul_eq_mul, map_mul, Complex.conj_ofReal]
  congr 1
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, inner_neg_right]
  congr 1
  push_cast
  ring

theorem adjKernel_normKernel (σ : ℝ → ℂ) (B : ℝ) (N : ℕ) :
    adjKernel (normKernel σ B N) = normKernel (fun ξ => (starRingEnd ℂ) (σ ξ)) B N := by
  ext u x
  simp only [adjKernel, normKernel, map_mul, map_inv₀, Complex.conj_ofReal]
  rw [← kernelTrunc_conj]
  congr 2
  ring_nf

end PrimeBHT.TimeFrequency.X2.CZ
