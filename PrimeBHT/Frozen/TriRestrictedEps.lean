-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Fin.VecNotation
public import PrimeBHT.Frozen.TriValid
public import PrimeBHT.Frozen.TriIdx
public import PrimeBHT.Frozen.TimeInt
public import PrimeBHT.Frozen.FreqNum
public import PrimeBHT.Frozen.FreqInt
public import PrimeBHT.Frozen.IntervalCentre
public import PrimeBHT.Frozen.IsAdapted
public import PrimeBHT.Frozen.Pairing
public import PrimeBHT.Frozen.TriForm
import PrimeBHT.Proof.M1

/-!
# Frozen: `PrimeBHT.Statements.tri_restricted_eps`

The statement exactly as the author approved it (ruling R16, 2026-11-09) before any proof was
written. It is the only declaration in this file; only the proof between the `FROZEN_ANCHOR`
marker comments is filled in afterwards. While the state is `DRAFT_SORRY` the body is the single
authorized `by sorry`, and the statement is frozen but unproved: nothing may consume it.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

set_option autoImplicit false

namespace PrimeBHT.Statements

/-- **M1(ε)** (generalized restricted-type estimate for the unshifted tri-tile form, with an `ε`-loss; NOT the
corner bound printed in BD26 L625-635). For every `ε ∈ (0, 1/2)` there are `N : ℕ` and `C > 0` (depending on
`ε` only) such that for every permutation `σ` of the slots and all measurable `E₀, E₁, E₂ ⊆ ℝ` of finite positive
measure with `|E_{σ0}| ≤ |E_{σ1}| ≤ |E_{σ2}|` there is a measurable `Ẽ ⊆ E_{σ2}` with `2|Ẽ| ≥ |E_{σ2}|` (a major
subset, depending on `ε, σ, E` only; NOT on `ν`, `P`, the packets or `h`) such that for every parameter `ν = (a, b, s', α)`,
every finite `P ⊆ Idx_ν`, every packet family adapted with exponent `N` to the tri-tiles of `P`, and every family
of measurable `h_i` with `|h_i| ≤ 1_{E_i}` (`i ≠ σ 2`) and `|h_{σ2}| ≤ 1_Ẽ`:
`Λ_P(h) ≤ C |E_{σ0}|^{1-ε} |E_{σ1}|^{1/2} |E_{σ2}|^{-1/2+ε}`. -/
theorem tri_restricted_eps (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧
      ∀ (σ : Equiv.Perm (Fin 3)) (E : Fin 3 → Set ℝ), (∀ i, MeasurableSet (E i)) →
        (∀ i, 0 < volume (E i) ∧ volume (E i) < ⊤) →
        volume (E (σ 0)) ≤ volume (E (σ 1)) → volume (E (σ 1)) ≤ volume (E (σ 2)) →
        ∃ Et : Set ℝ, MeasurableSet Et ∧ Et ⊆ E (σ 2) ∧ volume (E (σ 2)) ≤ 2 * volume Et ∧
          ∀ (a b s' α : ℤ), TriValid a b s' α →
          ∀ (P : Finset (ℤ × ℤ × ℤ)), (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α →
            ∀ φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ,
              (∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) →
              ∀ h : Fin 3 → ℝ → ℂ, (∀ i, Measurable (h i)) →
                (∀ i, i ≠ σ 2 → ∀ x, ‖h i x‖ ≤ (E i).indicator (1 : ℝ → ℝ) x) →
                (∀ x, ‖h (σ 2) x‖ ≤ Et.indicator (1 : ℝ → ℝ) x) →
                triForm P φ h ≤ C * (volume (E (σ 0))).toReal ^ (1 - ε) *
                  (volume (E (σ 1))).toReal ^ ((1 : ℝ) / 2) *
                  (volume (E (σ 2))).toReal ^ (-(1 : ℝ) / 2 + ε) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact PrimeBHT.Proof.tri_restricted_eps
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end PrimeBHT.Statements
-- FROZEN_ANCHOR_SUFFIX_END
