module

public import PrimeBHT.TimeFrequency.Interp.Hull.Chain

/-!
# R6b for the tri-tile model operator (`hRS` of R6c-I) from `M1Prop`

NOT BUILT, NOT PART OF THE LIBRARY (suffix `.lean.txt`).  It compiles (checked in a scratch tree, axioms
`propext, Classical.choice, Quot.sound`) only against the `Operator.lean` patched by
`Operator-InReg.patch.txt` (the `hhull` hypotheses of R6b restricted to `InReg`); once that patch is
applied, rename this file to `Hull/ChainR6b.lean` and add it to `Hull.lean`.

`hRS_modelOp_of_m1`: for `η > 0` there are `N` and `C > 0` such that for all valid `ν`, finite
`P ⊆ triIdx s' α`, packets adapted with exponent `N`, `(p₁, p₂, r, δ₀)` with `B(1/p, 2δ₀) ⊆ InReg η`
and `1/r = 1/p₁ + 1/p₂`, the model operator `Π_P` satisfies the hypothesis `hRS` of
`eLpNorm_le_of_restrictedStrong` (R6c-I) with the single constant
`rsConst (1/r) (η/2) W W`, `W = weakBound (η/2) C`: instance of `hRS_of_hullBound` with `Λ` the
conjugated form `conjForm (triForm P φ)`, `C := fun _ _ => C`, `hhull` from `hullBound_alphaOf_of_m1`
at `η/4`, `hdom` from `isDominated_modelOp_of_adapted`.
-/

@[expose] public section

namespace PrimeBHT.TimeFrequency.Interp.Hull

open MeasureTheory
open PrimeBHT.Statements
open PrimeBHT.TimeFrequency.Interp.Restricted

theorem hRS_modelOp_of_m1 (hM1 : M1Prop) {η : ℝ} (hη : 0 < η) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧
      ∀ (a b s' α : ℤ), TriValid a b s' α →
        ∀ (P : Finset (ℤ × ℤ × ℤ)), (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α →
          ∀ φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ,
            (∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) →
            ∀ {p₁ p₂ r δ₀ : ℝ}, 1 / r = 1 / p₁ + 1 / p₂ →
              η + 2 * δ₀ ≤ 1 / p₁ → η + 2 * δ₀ ≤ 1 / p₂ → 1 / p₁ + 2 * δ₀ ≤ 1 - η →
              1 / p₂ + 2 * δ₀ ≤ 1 - η → 1 / r ≤ 3 / 2 - η →
              ∀ t : ℝ, |t| < 2 * δ₀ → ∀ E₁ E₂ : Set ℝ, MeasurableSet E₁ → MeasurableSet E₂ →
                volume E₁ < ⊤ → volume E₂ < ⊤ → ∀ g₁ g₂ : ℝ → ℂ, Measurable g₁ → Measurable g₂ →
                (∀ x, ‖g₁ x‖ ≤ E₁.indicator (fun _ => (1 : ℝ)) x) →
                (∀ x, ‖g₂ x‖ ≤ E₂.indicator (fun _ => (1 : ℝ)) x) →
                eLpNorm (modelOp P φ g₁ g₂) (ENNReal.ofReal r) volume ≤
                  ENNReal.ofReal (rsConst (1 / r) (η / 2) (weakBound (η / 2) C)
                    (weakBound (η / 2) C)) * volume E₁ ^ (1 / p₁ + t) *
                    volume E₂ ^ (1 / p₂ - t) := by
  obtain ⟨N, C, hC, H⟩ := hullBound_alphaOf_of_m1 hM1 (η := η / 4) (by linarith)
  refine ⟨N, C, hC, fun a b s' α hν P hP φ hφ p₁ p₂ r δ₀ hpr h₁ h₂ h₃ h₄ hs => ?_⟩
  exact hRS_of_hullBound (Λ := conjForm (triForm P φ)) (T := modelOp P φ) (C := fun _ _ => C)
    (isSubadditive_triForm_of_adapted hφ).conjForm (isSmall_triForm_of_adapted hφ).conjForm
    (fun _ _ => hC.le) hpr hη
    (fun b₁ b₂ hb => (H a b s' α hν P hP φ hφ b₁ b₂ (by simpa using hb)).conjForm)
    (isDominated_modelOp_of_adapted hφ)
    (fun f₁ f₂ _ _ => measurable_modelOp_of_adapted hφ f₁ f₂) h₁ h₂ h₃ h₄ hs
    (fun _ _ _ => le_rfl)

end PrimeBHT.TimeFrequency.Interp.Hull
