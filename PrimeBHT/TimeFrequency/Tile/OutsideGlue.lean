module

public import PrimeBHT.TimeFrequency.Tile.Outside
public import PrimeBHT.TimeFrequency.Tile.Bessel

/-!
# C4 discharges the hypothesis of C10a

`Outside.lean` (C10a) is conditional on `hC4 : WeakBesselHyp a b s' α N C`; `Bessel.lean` (C4) proves it
(`weakBessel_forall`, `N ≥ 3`, `C = weakBesselConst N`). This file composes them: the estimate outside the
exceptional set, unconditionally.
-/

@[expose] public section

namespace PrimeBHT.TimeFrequency.Tile

open MeasureTheory
open PrimeBHT.Statements

/-- **C10a, unconditional** (`N ≥ 4`): outside the exceptional set,
`Λ_{P_out}(g') ≤ 96 C⁺ K_N (3 + 1/ε) |E (σ 0)|^{1/2-ε}` with `C = weakBesselConst N`. -/
theorem triForm_filter_outside_le_orth {a b s' α : ℤ} (hν : TriValid a b s' α) {N : ℕ}
    (hN : 4 ≤ N) (σ : Equiv.Perm (Fin 3))
    {E : Fin 3 → Set ℝ} {h : Fin 3 → ℝ → ℂ} (hEm : ∀ k, MeasurableSet (E k))
    (h01 : volume (E (σ 0)) ≤ volume (E (σ 1))) (h12 : volume (E (σ 1)) ≤ volume (E (σ 2)))
    (hE0 : volume (E (σ 0)) ≠ 0) (hhalf : 1 / 2 < (volume (E (σ 2))).toReal)
    (hone : (volume (E (σ 2))).toReal ≤ 1) (hhm : ∀ k, Measurable (h k))
    (hdom : ∀ k x, ‖h k x‖ ≤ (E k).indicator (1 : ℝ → ℝ) x)
    {P : Finset (ℤ × ℤ × ℤ)} (hP : (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    [DecidablePred fun t : ℤ × ℤ × ℤ => ¬ timeInt t ⊆ refExceptional (E (σ 0)) (E (σ 1))]
    {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hφ : ∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) {ε : ℝ} (hε : 0 < ε) :
    triForm (P.filter fun t => ¬ timeInt t ⊆ refExceptional (E (σ 0)) (E (σ 1))) φ (refG' E h) ≤
      96 * max (weakBesselConst N) 0 * refSizeConst (orthSizeConst N) (sameScaleConst N) * (3 + 1 / ε) *
        (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2 - ε) :=
  triForm_filter_outside_le_orth_of_hC4 hν hN (weakBessel_forall (by omega)) σ hEm h01 h12 hE0 hhalf
    hone hhm hdom hP hφ hε

end PrimeBHT.TimeFrequency.Tile
