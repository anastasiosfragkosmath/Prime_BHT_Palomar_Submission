module

public import PrimeBHT.TimeFrequency.X2.EngTail.Single

/-!
# X2, node B5-top: `engTop ≤ C sup λ_M` (corrected statement)

`engTop_le_tailMass` proves the REV2 node B5-top: the energy of the top operators is bounded by the tail masses of
`‖F‖` at the top intervals `W`.  It holds under the hypothesis `M ≤ 𝔭.D` (NEW, see below).

## Correction of the printed statement

`EngTopLeTailMassStatement` of `X2/V16/Hyps.lean` has the hypothesis `M + 100 ≤ 𝔭.N` only.  The kernel of a multiplier
`m ∈ M(𝔭)` (resp. a top multiplier) decays like `|w|^{-D}` and in general not faster: the class controls `D`
derivatives only.  A multiplier with a singularity `|η - a|^{D + 1/2}` (smoothed at an arbitrarily small scale, which
keeps the `D` controlled derivatives uniformly bounded) has a kernel of size `≈ |w|^{-(D + 3/2)}`; testing against
`F = 1_E` (`E` a unit-length interval at distance `d` from `I`) gives a left side `≳ d^{-(D+3/2)}`, while the right
side is `≲ C d^{-M}`.  So the printed statement is FALSE for `M > D + 3/2` (e.g. `D = 400`, `M = 𝔭.N - 100`), and the correct
hypothesis is `M ≤ 𝔭.D` (the number of controlled derivatives dominates the tail order).  The same holds for B5.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform ComplexConjugate ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- Kernel decay of order `M ≤ D` of a top multiplier: `‖𝓕⁻ m w‖ ≤ 2^{M+1} (24 · 2^{-W.1}) C (1 + 2^{-W.1}|w|)^{-M}`. -/
theorem norm_fourierInv_inTopMult_le_pow {𝔭 : Params} {M : ℕ} (hM : M ≤ 𝔭.D) {W : ℤ × ℤ} {ξ : ℝ}
    {k : Fin 3} {m : ℝ → ℂ} (hm : InTopMult 𝔭 W ξ k m) (w : ℝ) :
    ‖𝓕⁻ m w‖ ≤ 2 ^ (M + 1) * (2 * (topRad * (2 : ℝ) ^ (-W.1))) * 𝔭.C *
      ((1 + (2 : ℝ) ^ (-W.1) * |w|)⁻¹) ^ M := by
  obtain ⟨hsm, hsupp, -, hder⟩ := hm
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-W.1) := zpow_pos (by norm_num) _
  have htop : (0 : ℝ) ≤ topRad * (2 : ℝ) ^ (-W.1) := by unfold topRad; positivity
  exact norm_fourierInv_le_pow (n := m) (c := ξ * freqDir k) (r := topRad * (2 : ℝ) ^ (-W.1))
    (A := 𝔭.C) (l := (2 : ℝ) ^ (-W.1)) M htop hl (hsm.of_le (by exact_mod_cast le_top)) hsupp
    (fun η => by simpa using hder 0 (Nat.zero_le _) η)
    (fun η => by
      have h := hder M hM η
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      linarith) w

theorem continuous_fourierInv_inTopMult {𝔭 : Params} {W : ℤ × ℤ} {ξ : ℝ} {k : Fin 3} {m : ℝ → ℂ}
    (hm : InTopMult 𝔭 W ξ k m) : Continuous (𝓕⁻ m) :=
  continuous_fourierInv_of_integrable' (integrable_of_far hm.1.continuous hm.2.1)

/-- The bound of `norm_fourierInv_inTopMult_le_pow` in the form used by the single-operator lemma
(real exponent `M ≤ ⌈M⌉`, `R = 2^{W.1}`). -/
theorem kernel_inTopMult_le {𝔭 : Params} {M : ℝ} (hM : M ≤ 𝔭.D) {W : ℤ × ℤ} {ξ : ℝ} {k : Fin 3}
    {m : ℝ → ℂ} (hm : InTopMult 𝔭 W ξ k m) (w : ℝ) :
    ‖𝓕⁻ m w‖ ≤ (2 ^ (⌈M⌉₊ + 1) * (2 * topRad) * 𝔭.C) *
      (((2 : ℝ) ^ W.1)⁻¹ * (1 + |w| / (2 : ℝ) ^ W.1) ^ (-M)) := by
  have hMc : ⌈M⌉₊ ≤ 𝔭.D := Nat.ceil_le.2 hM
  have h1 := norm_fourierInv_inTopMult_le_pow hMc hm w
  have hR : (0 : ℝ) < (2 : ℝ) ^ W.1 := zpow_pos (by norm_num) _
  have hl : (2 : ℝ) ^ (-W.1) = ((2 : ℝ) ^ W.1)⁻¹ := zpow_neg _ _
  have hb : (1 : ℝ) ≤ 1 + |w| / (2 : ℝ) ^ W.1 := by
    have := div_nonneg (abs_nonneg w) hR.le; linarith
  have e1 : ((1 + (2 : ℝ) ^ (-W.1) * |w|)⁻¹) ^ ⌈M⌉₊ = (1 + |w| / (2 : ℝ) ^ W.1) ^ (-(⌈M⌉₊ : ℝ)) := by
    rw [hl, Real.rpow_neg (by positivity), Real.rpow_natCast, inv_pow]
    congr 2
    field_simp
  have e2 : (1 + |w| / (2 : ℝ) ^ W.1) ^ (-(⌈M⌉₊ : ℝ)) ≤ (1 + |w| / (2 : ℝ) ^ W.1) ^ (-M) :=
    Real.rpow_le_rpow_of_exponent_le hb (by linarith [Nat.le_ceil M])
  have hC : 0 ≤ 𝔭.C := by
    have := hm.2.2.2 0 (Nat.zero_le _) 0
    simp only [pow_zero, one_mul, iteratedDeriv_zero] at this
    exact (norm_nonneg _).trans this
  refine h1.trans ?_
  rw [e1, hl]
  have : 2 ^ (⌈M⌉₊ + 1) * (2 * (topRad * ((2 : ℝ) ^ W.1)⁻¹)) * 𝔭.C =
      (2 ^ (⌈M⌉₊ + 1) * (2 * topRad) * 𝔭.C) * ((2 : ℝ) ^ W.1)⁻¹ := by ring
  rw [this, mul_assoc]
  have htr : (0 : ℝ) ≤ topRad := by unfold topRad; norm_num
  have hc0 : 0 ≤ (2 : ℝ) ^ (⌈M⌉₊ + 1) * (2 * topRad) * 𝔭.C := by positivity
  gcongr


/-- `InPsi` in the form used by the single-operator lemma, for the dyadic interval `I = dyadicInt sc v`. -/
theorem inPsi_decay_dyadicInt {𝔭 : Params} {sc v : ℤ} {ψ : ℝ → ℂ} (hψ : InPsi 𝔭 sc v ψ) (x : ℝ) :
    ‖ψ x‖ ≤ 𝔭.C * (1 + |x - intervalCentre (dyadicInt sc v)| / (volume (dyadicInt sc v)).toReal) ^
      (-(𝔭.N : ℝ)) := by
  have h := hψ.2.1 x
  have hR : (0 : ℝ) < (2 : ℝ) ^ sc := zpow_pos (by norm_num) _
  rw [toReal_volume_dyadicInt, intervalCentre_dyadicInt]
  have e : jb ((x - dyCentre sc v) / (2 : ℝ) ^ sc) = 1 + |x - (2 : ℝ) ^ sc * ((v : ℝ) + 1 / 2)| / (2 : ℝ) ^ sc := by
    unfold jb dyCentre
    rw [abs_div, abs_of_pos hR]
  rwa [e] at h

/-- **The top single-operator bound** for one top datum `(W, ξ)`:
`topOpNorm ≤ K λ_M(‖F‖; I_W)`, `K = K(𝔭, q, M)`. -/
theorem topOpNorm_le_tailMass {𝔭 : Params} (h𝔭 : 𝔭.Admissible) {s q M : ℝ} (hs : 1 < s) (hq : 1 ≤ q)
    (hM : 1 < M) (hN : M + 2 ≤ 𝔭.N) (hD : M ≤ 𝔭.D) {P : ℕ} [NeZero P] (k : Fin 3)
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) (hFb : ∀ x, yNorm s (F x) ≤ 1) (W : ℤ × ℤ) (ξ : ℝ) :
    topOpNorm 𝔭 s q k F W ξ ≤
      ENNReal.ofReal (𝔭.C * (2 ^ (⌈M⌉₊ + 1) * (2 * topRad) * 𝔭.C) * (2 / ((𝔭.N - M) * q - 1)) ^ (1 / q)) *
        ENNReal.ofReal (V16.tailMass M (fun y => yNorm s (F y)) (dyadicInt W.1 W.2)) := by
  obtain ⟨-, -, -, -, -, hβ, -, hC1⟩ := h𝔭
  have hNM : 1 < ((𝔭.N : ℝ) - M) * q := by nlinarith
  have hC : 0 ≤ 𝔭.C := by linarith
  have hc0 : 0 < 2 ^ (⌈M⌉₊ + 1) * (2 * topRad) * 𝔭.C := by unfold topRad; positivity
  unfold topOpNorm
  refine iSup₂_le fun ψ m => iSup₂_le fun hψ hm => ?_
  have hR : (0 : ℝ) < (volume (dyadicInt W.1 W.2)).toReal := by
    rw [toReal_volume_dyadicInt]; exact zpow_pos (by norm_num) _
  have key := eLpNorm_psi_tmult_le (s := s) (q := q) (M := M) (N := (𝔭.N : ℝ)) hs.le hq hM hNM hR hC hc0
    hψ.1 (inPsi_decay_dyadicInt hψ) (continuous_fourierInv_inTopMult hm)
    (by
      intro w
      rw [toReal_volume_dyadicInt]
      exact kernel_inTopMult_le hD hm w) hF hFb
  rw [toReal_volume_dyadicInt] at key
  exact key


/-- **B5-top, corrected statement**: the printed `EngTopLeTailMassStatement` plus the hypothesis `M ≤ 𝔭.D`
(see the module docstring: without it the statement is false). -/
def EngTopLeTailMassStatementD : Prop :=
  ∀ (𝔭 : Params), 𝔭.Admissible → ∀ {s q M : ℝ}, 1 < s → 2 ≤ q → 3 ≤ M → M + 100 ≤ 𝔭.N → M ≤ 𝔭.D →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (Cs : Finset TriTile) (k : Fin 3) (F : ℝ → ZMod P → ℂ),
      Measurable F → (∀ x, yNorm s (F x) ≤ 1) →
        engTop 𝔭 s k F Cs q ≤ ENNReal.ofReal C *
          ⨆ (W : ℤ × ℤ) (ξ : ℝ) (_ : IsTopDatum 𝔭.J Cs W ξ),
            ENNReal.ofReal (V16.tailMass M (fun y => yNorm s (F y)) (dyadicInt W.1 W.2))

/-- **B5-top** (proved). -/
theorem engTopLeTailMass : EngTopLeTailMassStatementD := by
  intro 𝔭 h𝔭 s q M hs hq hM hN hD
  have hC1 : 1 ≤ 𝔭.C := h𝔭.2.2.2.2.2.2.2
  refine ⟨𝔭.C * (2 ^ (⌈M⌉₊ + 1) * (2 * topRad) * 𝔭.C) * (2 / ((𝔭.N - M) * q - 1)) ^ (1 / q), ?_, ?_⟩
  · have hNM : 0 < ((𝔭.N : ℝ) - M) * q - 1 := by nlinarith
    have : 0 ≤ 2 / (((𝔭.N : ℝ) - M) * q - 1) := by positivity
    unfold topRad
    positivity
  · intro P _ Cs k F hF hFb
    unfold engTop
    refine iSup₂_le fun W ξ => iSup_le fun hd => ?_
    refine (topOpNorm_le_tailMass h𝔭 hs (by linarith) (by linarith) (by linarith) hD k hF hFb W ξ).trans ?_
    refine mul_le_mul' le_rfl ?_
    exact le_iSup_of_le W (le_iSup_of_le ξ (le_iSup_of_le hd le_rfl))

end PrimeBHT.TimeFrequency.X2
