module

public import PrimeBHT.TimeFrequency.X2.Psp.TreeConvErr

/-!
# X2, V15 (assembly), step 3a: the Cauchy-Schwarz sum over the layers

`cs_sum`: `Σ_σ ∫ u₀σ u₁σ v_σ ≤ M A₀ A₁` when `v ≤ M` pointwise and `Σ_σ ∫ u_kσ² ≤ A_k²` (`k = 0, 1`) — the estimate behind the
cases `B = ∅`, `B = {3}` of the route check §4 step 3 (Cauchy-Schwarz in `σ` with the two Hilbert slots, then in `x`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

theorem cs_sum {S : Finset ℤ} {u₀ u₁ v : ℤ → ℝ → ℝ≥0∞} (h₀ : ∀ σ ∈ S, Measurable (u₀ σ)) (h₁ : ∀ σ ∈ S, Measurable (u₁ σ))
    {M A₀ A₁ : ℝ≥0∞} (hv : ∀ σ ∈ S, ∀ x, v σ x ≤ M) (hA₀ : ∑ σ ∈ S, ∫⁻ x, u₀ σ x ^ (2 : ℝ) ≤ A₀ ^ (2 : ℝ))
    (hA₁ : ∑ σ ∈ S, ∫⁻ x, u₁ σ x ^ (2 : ℝ) ≤ A₁ ^ (2 : ℝ)) :
    ∑ σ ∈ S, ∫⁻ x, u₀ σ x * u₁ σ x * v σ x ≤ M * (A₀ * A₁) := by
  have step1 : ∑ σ ∈ S, ∫⁻ x, u₀ σ x * u₁ σ x * v σ x ≤ ∑ σ ∈ S, ∫⁻ x, u₀ σ x * u₁ σ x * M :=
    Finset.sum_le_sum fun σ hσ => lintegral_mono fun x => mul_le_mul' le_rfl (hv σ hσ x)
  have step2 : ∑ σ ∈ S, ∫⁻ x, u₀ σ x * u₁ σ x * M = M * ∫⁻ x, ∑ σ ∈ S, u₀ σ x * u₁ σ x := by
    have hm : ∀ σ ∈ S, Measurable (fun x => u₀ σ x * u₁ σ x) := fun σ hσ => (h₀ σ hσ).mul (h₁ σ hσ)
    rw [lintegral_finsetSum S hm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    exact (lintegral_congr fun x => by ring : ∫⁻ x, u₀ σ x * u₁ σ x * M = ∫⁻ x, M * (u₀ σ x * u₁ σ x)).trans
      (lintegral_const_mul (μ := volume) M (f := fun x => u₀ σ x * u₁ σ x) ((h₀ σ hσ).mul (h₁ σ hσ)))
  have step3 : ∀ x, ∑ σ ∈ S, u₀ σ x * u₁ σ x ≤
      (∑ σ ∈ S, u₀ σ x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∑ σ ∈ S, u₁ σ x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := fun x =>
    ENNReal.inner_le_Lp_mul_Lq S (fun σ => u₀ σ x) (fun σ => u₁ σ x) Real.HolderConjugate.two_two
  have hm₀ : Measurable (fun x => (∑ σ ∈ S, u₀ σ x ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) :=
    (Finset.measurable_sum _ fun σ hσ => (h₀ σ hσ).pow_const _).pow_const _
  have hm₁ : Measurable (fun x => (∑ σ ∈ S, u₁ σ x ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) :=
    (Finset.measurable_sum _ fun σ hσ => (h₁ σ hσ).pow_const _).pow_const _
  have step4 : ∫⁻ x, ∑ σ ∈ S, u₀ σ x * u₁ σ x ≤ A₀ * A₁ := by
    calc ∫⁻ x, ∑ σ ∈ S, u₀ σ x * u₁ σ x
        ≤ ∫⁻ x, (∑ σ ∈ S, u₀ σ x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∑ σ ∈ S, u₁ σ x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
          lintegral_mono step3
      _ ≤ (∫⁻ x, ((∑ σ ∈ S, u₀ σ x ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ x, ((∑ σ ∈ S, u₁ σ x ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
          ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hm₀.aemeasurable hm₁.aemeasurable
      _ = (∫⁻ x, ∑ σ ∈ S, u₀ σ x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∫⁻ x, ∑ σ ∈ S, u₁ σ x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
          congr 2
          · refine lintegral_congr fun x => ?_
            rw [← ENNReal.rpow_mul]; norm_num
          · refine lintegral_congr fun x => ?_
            rw [← ENNReal.rpow_mul]; norm_num
      _ = (∑ σ ∈ S, ∫⁻ x, u₀ σ x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∑ σ ∈ S, ∫⁻ x, u₁ σ x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
          rw [lintegral_finsetSum _ fun σ hσ => (h₀ σ hσ).pow_const _, lintegral_finsetSum _ fun σ hσ => (h₁ σ hσ).pow_const _]
      _ ≤ (A₀ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (A₁ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
          mul_le_mul' (ENNReal.rpow_le_rpow hA₀ (by norm_num)) (ENNReal.rpow_le_rpow hA₁ (by norm_num))
      _ = A₀ * A₁ := by
          rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]; norm_num
  calc ∑ σ ∈ S, ∫⁻ x, u₀ σ x * u₁ σ x * v σ x ≤ _ := step1
    _ = _ := step2
    _ ≤ M * (A₀ * A₁) := mul_le_mul' le_rfl step4

end PrimeBHT.TimeFrequency.X2
