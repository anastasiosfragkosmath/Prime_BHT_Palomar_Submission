module

public import PrimeBHT.TimeFrequency.Interp.Hull.Glue
public import PrimeBHT.TimeFrequency.Interp.Hull.ModelForm

/-!
# `M1(ε)` through the abstract chain: R6a and the hypothesis `hRT` of R6c-II for `Λ_P`

Blueprint `docs/x1-blueprint.md`, nodes C11 and R6a (`RL.rt_form`), and the plug-in into
`PrimeBHT.TimeFrequency.Interp.Strong.form_le_of_restrictedType` (R6c-II).  All results are conditional
on `M1Prop` (the type of the frozen M1(ε)) and named `…_of_m1`.

* `restrictedType_triForm_of_m1` (**R6a for X1**): for `ε ∈ (0, 1/2)` there are `N` and `C > 0` such
  that for all valid `ν`, finite `P ⊆ triIdx s' α`, packets adapted with exponent `N`, every exponent
  `x` of the closed `ε`-hexagon with `x_i ≥ m > 0`, and measurable `h_i` with `|h_i| ≤ 1_{E_i}`
  (`E_i` measurable of finite measure, no ordering):
  `Λ_P(h) ≤ C/(1 - 2^{-m}) Π_i |E_i|^{x_i}`.  `restrictedType_of_hullBound` with the glue
  `hullBound_triForm_of_m1`, `isSubadditive_triForm_of_adapted`, `isSmall_triForm_of_adapted`.
* `hRT_triForm_of_m1`: the hypothesis `hRT` of `form_le_of_restrictedType` / `eLpNorm_le_of_restrictedType`
  (R6c-II, `Σ 1/p_i = 1`) for `Λ' f g h := triForm P φ ![f, g, h]`, with the single constant
  `C/(1 - 2^{-η})`, provided `ε ≤ 2η` and `η + δ₀ ≤ 1/p_i`.  It is the exact analogue of
  `restrictedType_of_hullBound_hRT` of `Operator.lean`, but only needs `HullBound` on the closed
  `ε`-hexagon.
* `hullBound_alphaOf_of_m1`: the hull family that R6b consumes, on the compact part `InReg η` of `U_*`
  (`alphaOf b ∈ InHexagon (min η (1/4))` for `b ∈ InReg η`), with ONE constant `C` and ONE exponent `N`.

## Interface note for the consumer of `Operator.lean` (R6b)

The theorems of `Operator.lean` (`weak_core`, `weak_type_of_hullBound`, `eLpNorm_le_of_hullBound`,
`eLpNorm_le_of_hullBound_of_inReg`, `restrictedType_of_hullBound_hRT`, `hRS_of_hullBound`) assume
`hhull : ∀ b₁ b₂, InUstar b₁ b₂ → HullBound μ Λ (alphaOf b₁ b₂) (C b₁ b₂)`.  For `Λ = triForm P φ`
this cannot be supplied from `M1Prop` with packets adapted with one fixed exponent `N`: M1(ε) gives an
`N = N(ε)` that may grow as `ε → 0`, and `epsOf (alphaOf b) → 0` at the boundary of `U_*`; the model
bound (MB) of R5 is for packets adapted with a single `N`.  What `M1Prop` does give, with one `(N, C)`,
is `HullBound` on every compact subset of `U_*` (`hullBound_alphaOf_of_m1`).  The proofs of
`Operator.lean` use `hhull` only on `InReg (η/4)` when the conclusion is at `a ∈ InReg η` (compare
`weakConst_le_weakBound` and `eLpNorm_le_of_hullBound_of_inReg`: the constants are evaluated at
`a`, `a ± (η/2, 0)` and the points `b` of sub-case 2, all in `InReg (η/4)`), so `hhull` there should be
weakened to `∀ b₁ b₂, InReg (η/4) b₁ b₂ → HullBound …`.  A verified patch doing exactly that is
`Hull/Operator-InReg.patch.txt` (a diff against `Operator.lean`, not applied; it compiles and keeps all
proofs), and `Hull/ChainR6b.lean.txt` is then the R6b instance for `Π_P` (`hRS_modelOp_of_m1`).  The
R6a-based `hRT` (R6c-II, `r > 1`) needs no such change and is `hRT_triForm_of_m1` below.
-/

@[expose] public section

namespace PrimeBHT.TimeFrequency.Interp.Hull

open MeasureTheory
open PrimeBHT.Statements
open PrimeBHT.TimeFrequency.Interp.Restricted

/-- **R6a for the tri-tile form** (conditional on `M1Prop`): see the module docstring. -/
theorem restrictedType_triForm_of_m1 (hM1 : M1Prop) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧
      ∀ (a b s' α : ℤ), TriValid a b s' α →
        ∀ (P : Finset (ℤ × ℤ × ℤ)), (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α →
          ∀ φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ,
            (∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) →
            ∀ (x : Fin 3 → ℝ) (m : ℝ), InHexagon ε x → 0 < m → (∀ i, m ≤ x i) →
            ∀ E : Fin 3 → Set ℝ, (∀ i, MeasurableSet (E i)) → (∀ i, volume (E i) < ⊤) →
            ∀ h : Fin 3 → ℝ → ℂ, (∀ i, Measurable (h i)) → (∀ i, DominatedBy (E i) (h i)) →
              triForm P φ h ≤ C / (1 - (2 : ℝ) ^ (-m)) * ∏ i, (volume (E i)).toReal ^ x i := by
  obtain ⟨N, C, hC, H⟩ := hullBound_triForm_of_m1 hM1 hε hε'
  refine ⟨N, C, hC, fun a b s' α hν P hP φ hφ x m hx hm hmx E hEm hEf h hhm hhd => ?_⟩
  exact restrictedType_of_hullBound hmx hm hC.le (isSubadditive_triForm_of_adapted hφ)
    (isSmall_triForm_of_adapted hφ) (H a b s' α hν P hP φ hφ x hx) hEm hEf hhm hhd

/-- **The hypothesis `hRT` of R6c-II for `Λ_P`** (conditional on `M1Prop`): see the module docstring.
The conclusion is literally the `hRT` of `Strong.lean` for `Λ f g h := triForm P φ ![f, g, h]`, with
`K = C`, up to the factor `1/(1 - 2^{-η})`. -/
theorem hRT_triForm_of_m1 (hM1 : M1Prop) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧
      ∀ (a b s' α : ℤ), TriValid a b s' α →
        ∀ (P : Finset (ℤ × ℤ × ℤ)), (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α →
          ∀ φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ,
            (∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) →
            ∀ {p₁ p₂ p₃ δ₀ η : ℝ}, 1 / p₁ + 1 / p₂ + 1 / p₃ = 1 → 0 < η → ε ≤ 2 * η → 0 ≤ δ₀ →
              η + δ₀ ≤ 1 / p₁ → η + δ₀ ≤ 1 / p₂ → η + δ₀ ≤ 1 / p₃ →
              ∀ d₁ d₂ d₃ : ℝ, d₁ + d₂ + d₃ = 0 → |d₁| ≤ δ₀ → |d₂| ≤ δ₀ → |d₃| ≤ δ₀ →
                ∀ E₁ E₂ E₃ : Set ℝ, MeasurableSet E₁ → MeasurableSet E₂ → MeasurableSet E₃ →
                volume E₁ < ⊤ → volume E₂ < ⊤ → volume E₃ < ⊤ →
                ∀ g₁ g₂ g₃ : ℝ → ℂ, Measurable g₁ → Measurable g₂ → Measurable g₃ →
                DominatedBy E₁ g₁ → DominatedBy E₂ g₂ → DominatedBy E₃ g₃ →
                  triForm P φ ![g₁, g₂, g₃] ≤ C / (1 - (2 : ℝ) ^ (-η)) *
                    (volume E₁).toReal ^ (1 / p₁ + d₁) * (volume E₂).toReal ^ (1 / p₂ + d₂) *
                    (volume E₃).toReal ^ (1 / p₃ + d₃) := by
  obtain ⟨N, C, hC, H⟩ := restrictedType_triForm_of_m1 hM1 hε hε'
  refine ⟨N, C, hC, fun a b s' α hν P hP φ hφ p₁ p₂ p₃ δ₀ η hp hη hεη hδ h₁ h₂ h₃ d₁ d₂ d₃ hd
    hd₁ hd₂ hd₃ E₁ E₂ E₃ hE₁m hE₂m hE₃m hE₁f hE₂f hE₃f g₁ g₂ g₃ hg₁m hg₂m hg₃m hg₁ hg₂ hg₃ => ?_⟩
  have a1 := abs_le.1 hd₁
  have a2 := abs_le.1 hd₂
  have a3 := abs_le.1 hd₃
  set x : Fin 3 → ℝ := ![1 / p₁ + d₁, 1 / p₂ + d₂, 1 / p₃ + d₃] with hx
  have hxsum : x 0 + x 1 + x 2 = 1 := by
    show 1 / p₁ + d₁ + (1 / p₂ + d₂) + (1 / p₃ + d₃) = 1
    linarith
  have hxlow : ∀ i, η ≤ x i := by
    intro i
    fin_cases i
    · show η ≤ 1 / p₁ + d₁
      linarith
    · show η ≤ 1 / p₂ + d₂
      linarith
    · show η ≤ 1 / p₃ + d₃
      linarith
  have hxhex : InHexagon ε x := by
    refine ⟨hxsum, fun i => ⟨?_, ?_⟩⟩
    · have := hxlow i
      linarith
    · have h0 := hxlow 0
      have h1 := hxlow 1
      have h2 := hxlow 2
      fin_cases i
      · show x 0 ≤ 1 - ε
        linarith
      · show x 1 ≤ 1 - ε
        linarith
      · show x 2 ≤ 1 - ε
        linarith
  have hR := H a b s' α hν P hP φ hφ x η hxhex hη hxlow ![E₁, E₂, E₃]
    (forall_vec3 hE₁m hE₂m hE₃m) (forall_vec3 (P := fun S => volume S < ⊤) hE₁f hE₂f hE₃f)
    ![g₁, g₂, g₃] (forall_vec3 hg₁m hg₂m hg₃m) (forall_vec3₂ (P := DominatedBy) hg₁ hg₂ hg₃)
  rw [prod_vec3] at hR
  have hR' : triForm P φ ![g₁, g₂, g₃] ≤ C / (1 - (2 : ℝ) ^ (-η)) *
      ((volume E₁).toReal ^ (1 / p₁ + d₁) * (volume E₂).toReal ^ (1 / p₂ + d₂) *
        (volume E₃).toReal ^ (1 / p₃ + d₃)) := hR
  refine hR'.trans (le_of_eq ?_)
  ring

/-- `alphaOf b` lies in the closed `min η (1/4)`-hexagon for `b ∈ InReg η`. -/
lemma inHexagon_alphaOf_of_inReg {η b₁ b₂ : ℝ} (hη : 0 < η) (h : InReg η b₁ b₂) :
    InHexagon (min η (1 / 4)) (alphaOf b₁ b₂) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hε := min_le_left η (1 / 4)
  have hε' := min_le_right η (1 / 4)
  refine ⟨?_, fun i => ?_⟩
  · show b₁ + b₂ + (1 - b₁ - b₂) = 1
    ring
  · fin_cases i
    · constructor
      · show -(1 : ℝ) / 2 + min η (1 / 4) ≤ b₁
        linarith
      · show b₁ ≤ 1 - min η (1 / 4)
        linarith
    · constructor
      · show -(1 : ℝ) / 2 + min η (1 / 4) ≤ b₂
        linarith
      · show b₂ ≤ 1 - min η (1 / 4)
        linarith
    · constructor
      · show -(1 : ℝ) / 2 + min η (1 / 4) ≤ 1 - b₁ - b₂
        linarith
      · show 1 - b₁ - b₂ ≤ 1 - min η (1 / 4)
        linarith

/-- **The hull family of R6b on `InReg η`** (conditional on `M1Prop`): one exponent `N` and one constant
`C > 0` (those of `M1Prop` at `ε = min η (1/4)`), independent of `ν, P, φ`, such that
`HullBound volume (triForm P φ) (alphaOf b₁ b₂) C` for every `b ∈ InReg η`. -/
theorem hullBound_alphaOf_of_m1 (hM1 : M1Prop) {η : ℝ} (hη : 0 < η) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧
      ∀ (a b s' α : ℤ), TriValid a b s' α →
        ∀ (P : Finset (ℤ × ℤ × ℤ)), (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α →
          ∀ φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ,
            (∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) →
            ∀ b₁ b₂ : ℝ, InReg η b₁ b₂ →
              HullBound volume (triForm P φ) (alphaOf b₁ b₂) C := by
  obtain ⟨N, C, hC, H⟩ := hullBound_triForm_of_m1 hM1 (ε := min η (1 / 4))
    (lt_min hη (by norm_num)) ((min_le_right _ _).trans_lt (by norm_num))
  exact ⟨N, C, hC, fun a b s' α hν P hP φ hφ b₁ b₂ hb =>
    H a b s' α hν P hP φ hφ _ (inHexagon_alphaOf_of_inReg hη hb)⟩

end PrimeBHT.TimeFrequency.Interp.Hull
