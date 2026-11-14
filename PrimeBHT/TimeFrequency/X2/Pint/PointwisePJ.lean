module

public import PrimeBHT.Interpolation

/-!
# X2, V11 / TB-4 shared core, part 2: the pointwise Poisson-Jensen power lemma

`docs/audits/X2-V11-TB4-plan.md` §4b.  From the strip Poisson-Jensen inequality (`PrimeBHT.Interpolation.stripPoissonJensen`,
proved): for `θ ∈ (0,1)` there is ONE probability measure `ν₁` on `ℝ` (the harmonic measure of `θ` on the line `re z = 1`,
normalized) such that every bounded continuous `G` on the closed strip, holomorphic inside, with `‖G(it)‖ ≤ M₀` for all `t`,
satisfies `‖G θ‖^(2/θ) ≤ M₀^(2/θ - 2) ∫ ‖G(1 + it)‖² dν₁(t)`.

This is the form used pointwise in `x` (and per operator) in `SingleOp.lean`: the right side is then integrated in `x` and summed
over the operators by Tonelli, which the SUP form of Hadamard's three-lines theorem would not allow (the sup over `t` of a
maximal function is unbounded).
-/

@[expose] public noncomputable section

open MeasureTheory Complex Complex.HadamardThreeLines
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Pint

/-- **Pointwise Poisson-Jensen power lemma.** -/
theorem exists_pointwisePJ {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ ν₁ : Measure ℝ, IsProbabilityMeasure ν₁ ∧
      ∀ (G : ℂ → ℂ), DiffContOnCl ℂ G (verticalStrip 0 1) →
        BddAbove ((fun z => ‖G z‖) '' verticalClosedStrip 0 1) →
        ∀ {M₀ : ℝ}, 0 ≤ M₀ → (∀ t : ℝ, ‖G (t * I)‖ ≤ M₀) →
          ‖G θ‖ₑ ^ (2 / θ) ≤
            ENNReal.ofReal (M₀ ^ (2 / θ - 2)) * ∫⁻ t, ‖G (1 + t * I)‖ₑ ^ (2 : ℝ) ∂ν₁ := by
  obtain ⟨ν₀, ν₁, hν₀, hν₁, hSJ⟩ := PrimeBHT.Interpolation.stripPoissonJensen hθ
  refine ⟨ν₁, hν₁, fun G hG hB M₀ hM₀ hG0 => ?_⟩
  obtain ⟨hθ0, hθ1⟩ := hθ
  have h := hSJ G hG hB 1 2 one_pos two_pos
  have h0 : ∫⁻ t, ‖G (t * I)‖ₑ ^ (1 : ℝ) ∂ν₀ ≤ ENNReal.ofReal M₀ := by
    calc ∫⁻ t, ‖G (t * I)‖ₑ ^ (1 : ℝ) ∂ν₀ ≤ ∫⁻ _, ENNReal.ofReal M₀ ∂ν₀ := by
          refine lintegral_mono fun t => ?_
          rw [ENNReal.rpow_one, ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hG0 t)
      _ = ENNReal.ofReal M₀ := by simp
  have hR : 0 < 2 / θ := by positivity
  have he1 : (1 - θ) / 1 * (2 / θ) = 2 / θ - 2 := by field_simp
  have he2 : θ / 2 * (2 / θ) = 1 := by field_simp
  have he0 : 0 ≤ 2 / θ - 2 := by
    rw [sub_nonneg, le_div_iff₀ hθ0]; linarith
  calc ‖G θ‖ₑ ^ (2 / θ)
      ≤ ((∫⁻ t, ‖G (t * I)‖ₑ ^ (1 : ℝ) ∂ν₀) ^ ((1 - θ) / 1) *
          (∫⁻ t, ‖G (1 + t * I)‖ₑ ^ (2 : ℝ) ∂ν₁) ^ (θ / 2)) ^ (2 / θ) :=
        ENNReal.rpow_le_rpow h hR.le
    _ = (∫⁻ t, ‖G (t * I)‖ₑ ^ (1 : ℝ) ∂ν₀) ^ ((1 - θ) / 1 * (2 / θ)) *
          (∫⁻ t, ‖G (1 + t * I)‖ₑ ^ (2 : ℝ) ∂ν₁) ^ (θ / 2 * (2 / θ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hR.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    _ ≤ (ENNReal.ofReal M₀) ^ (2 / θ - 2) * (∫⁻ t, ‖G (1 + t * I)‖ₑ ^ (2 : ℝ) ∂ν₁) ^ (1 : ℝ) := by
        rw [he1, he2]
        gcongr
    _ = ENNReal.ofReal (M₀ ^ (2 / θ - 2)) * ∫⁻ t, ‖G (1 + t * I)‖ₑ ^ (2 : ℝ) ∂ν₁ := by
        rw [ENNReal.rpow_one, ENNReal.ofReal_rpow_of_nonneg hM₀ he0]

end PrimeBHT.TimeFrequency.X2.Pint
