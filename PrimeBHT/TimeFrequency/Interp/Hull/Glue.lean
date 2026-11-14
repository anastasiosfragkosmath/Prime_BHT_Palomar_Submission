module

public import PrimeBHT.Frozen.TriValid
public import PrimeBHT.Frozen.TriIdx
public import PrimeBHT.Frozen.TimeInt
public import PrimeBHT.Frozen.FreqNum
public import PrimeBHT.Frozen.FreqInt
public import PrimeBHT.Frozen.IntervalCentre
public import PrimeBHT.Frozen.IsAdapted
public import PrimeBHT.Frozen.Pairing
public import PrimeBHT.Frozen.TriForm
public import PrimeBHT.TimeFrequency.Interp.Restricted.Form
public import PrimeBHT.TimeFrequency.Interp.Hull.Exponents

/-!
# C11, the glue: `M1(ε)` implies the hull bound `HullBound` of the abstract chain

Blueprint `docs/x1-blueprint.md`, node C11 (`TT.hull`), item (c), and its connection to the abstract
R6a/R6b chain (`PrimeBHT.TimeFrequency.Interp.Restricted.{Form, Operator}`).

`M1Prop` is the type of the frozen theorem `PrimeBHT.Statements.tri_restricted_eps` (ruling R16),
copied from the approved text `scripts/data/approved/M1-approved.lean.txt` over the frozen definitions
`PrimeBHT.Statements.{TriValid, triIdx, timeInt, freqInt, IsAdapted, pairing, triForm}`.  This file
does not import the frozen theorem (it is `DRAFT_SORRY`-quarantined): everything here is conditional on
`M1Prop` and named `…_of_m1`.  That `M1Prop` is the frozen type is checked by `rfl` in
`scripts/interface_check`.

## Main results

* `hullBound_triForm_of_m1`: for `ε ∈ (0, 1/2)` there are `N` and `C > 0` (those of `M1Prop` at `ε`)
  such that for every valid `ν = (a, b, s', α)`, finite `P ⊆ triIdx s' α` and packets `φ` adapted with
  exponent `N` to the tri-tiles of `P`, the form `Λ = triForm P φ` on `(ℝ, volume)` satisfies
  `HullBound volume Λ x C` for **every** exponent `x` in the closed `ε`-hexagon `InHexagon ε`.
  `N` and `C` do not depend on `ν, P, φ`, nor on `x`.
* `hullBound_triForm_of_m1_of_mem_openHexagon`: the same for a single `x ∈ openHexagon`, with
  `ε = epsOf x`.
* `hullBound_triForm_of_m1_of_isCompact`: one pair `(N, C)` for all `x` in a compact subset of the open
  hexagon; `hullBound_triForm_of_m1_eventually`: one pair `(N, C)` on a neighbourhood of any `x` of the
  open hexagon (the "locally bounded in `α`" of the blueprint).

## About the quantifiers

`HullBound μ Λ x C` is `∀ E (measurable, positive and finite measure), ∀ j (index of a largest set),
∃ Et ⊆ E j (measurable, μ (E j) ≤ 2 μ Et), ∀ h, … → Λ h ≤ C Π μ(E_i)^{x_i}`, with `Λ` (that is
`ν, P, φ`) fixed *before* everything else.  M1(ε) is stronger on the order of quantifiers: the major
subset `Et` is chosen after `ε` and `(σ, E)` only, i.e. before the parameters `ν`, the tile set `P`, the
packets and the test functions; so `Et` is a function of `(E, j)` only and in particular does not depend
on `Λ`.  `HullBound` only needs `Et` to depend on `E` and `j` (not on `h`).  For a given pair `(E, j)`
with `μ (E j)` maximal, `exists_perm_last_eq` gives a permutation `σ` with `σ 2 = j` and the other two
sets ordered; M1(ε) applies to `(σ, E)` and gives `Et ⊆ E j`.  The bound
`C |E_{σ0}|^{1-ε} |E_{σ1}|^{1/2} |E_{σ2}|^{-1/2+ε}` is then at most `C Π_i |E_i|^{x_i}` by
`corner_le_rpow_mul` with `α_k = x_{σ k}` (reindexing the product by `σ`).
-/

@[expose] public section

namespace PrimeBHT.TimeFrequency.Interp.Hull

open MeasureTheory
open PrimeBHT.Statements
open PrimeBHT.TimeFrequency.Interp.Restricted

/-- **M1(ε)** as a `Prop`: the type of the frozen theorem `PrimeBHT.Statements.tri_restricted_eps`
(ruling R16), copied from `scripts/data/approved/M1-approved.lean.txt`. -/
def M1Prop : Prop :=
  ∀ (ε : ℝ), 0 < ε → ε < 1 / 2 →
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
                  (volume (E (σ 2))).toReal ^ (-(1 : ℝ) / 2 + ε)

/-- For a largest index `j` there is a permutation with `σ 2 = j` sorting the sets: the other two
indices are ordered by a swap if needed. -/
lemma exists_perm_last_eq {β : Type*} [LinearOrder β] (f : Fin 3 → β) (j : Fin 3)
    (hj : ∀ i, f i ≤ f j) :
    ∃ σ : Equiv.Perm (Fin 3), σ 2 = j ∧ f (σ 0) ≤ f (σ 1) ∧ f (σ 1) ≤ f (σ 2) := by
  set σ₀ : Equiv.Perm (Fin 3) := Equiv.swap 2 j with hσ₀
  have h2 : σ₀ 2 = j := by simp [hσ₀]
  rcases le_total (f (σ₀ 0)) (f (σ₀ 1)) with h | h
  · refine ⟨σ₀, h2, h, ?_⟩
    rw [h2]
    exact hj _
  · set τ : Equiv.Perm (Fin 3) := σ₀ * Equiv.swap (0 : Fin 3) 1 with hτ
    have hτ0 : τ 0 = σ₀ 1 := by simp [hτ, Equiv.Perm.mul_apply]
    have hτ1 : τ 1 = σ₀ 0 := by simp [hτ, Equiv.Perm.mul_apply]
    have hτ2 : τ 2 = j := by
      have : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
      simp [hτ, Equiv.Perm.mul_apply, this, h2]
    refine ⟨τ, hτ2, ?_, ?_⟩
    · rw [hτ0, hτ1]; exact h
    · rw [hτ2]; exact hj _

/-- **C11(c) / the glue** (conditional on `M1Prop`): see the module docstring. -/
theorem hullBound_triForm_of_m1 (hM1 : M1Prop) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧
      ∀ (a b s' α : ℤ), TriValid a b s' α →
        ∀ (P : Finset (ℤ × ℤ × ℤ)), (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α →
          ∀ φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ,
            (∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) →
            ∀ x : Fin 3 → ℝ, InHexagon ε x → HullBound volume (triForm P φ) x C := by
  obtain ⟨N, C, hC, H⟩ := hM1 ε hε hε'
  refine ⟨N, C, hC, fun a b s' α hν P hP φ hφ x hx E hEm hEpos hEfin j hjmax => ?_⟩
  obtain ⟨σ, hσ2, h01, h12⟩ := exists_perm_last_eq (fun i => volume (E i)) j hjmax
  obtain ⟨Et, hEtm, hEtsub, hEt2, hbound⟩ := H σ E hEm (fun i => ⟨hEpos i, hEfin i⟩) h01 h12
  rw [hσ2] at hEtsub hEt2
  refine ⟨Et, hEtm, hEtsub, hEt2, fun h hhm hhd hhj => ?_⟩
  have hM := hbound a b s' α hν P hP φ hφ h hhm
    (fun i hi y => hhd i (fun e => hi (e.trans hσ2.symm)) y)
    (fun y => by rw [hσ2]; exact hhj y)
  -- the three measures, ordered
  set u : Fin 3 → ℝ := fun i => (volume (E i)).toReal with hu
  have hupos : ∀ i, 0 < u i := fun i =>
    ENNReal.toReal_pos (hEpos i).ne' (hEfin i).ne
  have hu01 : u (σ 0) ≤ u (σ 1) := ENNReal.toReal_mono (hEfin _).ne h01
  have hu12 : u (σ 1) ≤ u (σ 2) := ENNReal.toReal_mono (hEfin _).ne h12
  have hsumσ : x (σ 0) + x (σ 1) + x (σ 2) = 1 := by
    have h3 : ∑ k, x (σ k) = ∑ i, x i := Equiv.sum_comp σ x
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at h3
    rw [h3]
    exact hx.1
  have halg := corner_le_rpow_mul (hupos (σ 0)) hu01 hu12 hsumσ (hx.2 (σ 0)).2 (hx.2 (σ 2)).1
  have hprod : ∏ i, u i ^ x i = u (σ 0) ^ x (σ 0) * u (σ 1) ^ x (σ 1) * u (σ 2) ^ x (σ 2) := by
    rw [← Equiv.prod_comp σ (fun i => u i ^ x i), Fin.prod_univ_three]
  calc triForm P φ h ≤ C * (volume (E (σ 0))).toReal ^ (1 - ε) *
        (volume (E (σ 1))).toReal ^ ((1 : ℝ) / 2) *
        (volume (E (σ 2))).toReal ^ (-(1 : ℝ) / 2 + ε) := hM
    _ = C * (u (σ 0) ^ (1 - ε) * u (σ 1) ^ ((1 : ℝ) / 2) * u (σ 2) ^ (-(1 : ℝ) / 2 + ε)) := by
        simp only [hu]
        ring
    _ ≤ C * (u (σ 0) ^ x (σ 0) * u (σ 1) ^ x (σ 1) * u (σ 2) ^ x (σ 2)) :=
        mul_le_mul_of_nonneg_left halg hC.le
    _ = C * ∏ i, (volume (E i)).toReal ^ x i := by
        rw [← hprod]

end PrimeBHT.TimeFrequency.Interp.Hull
