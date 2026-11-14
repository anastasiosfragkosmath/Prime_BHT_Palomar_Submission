module

public import PrimeBHT.TimeFrequency.X2.TopEnergy.Defs
public import PrimeBHT.TimeFrequency.X2.TopEnergy.Duals
public import PrimeBHT.TimeFrequency.X2.Ortho.TileBasic
public import PrimeBHT.TimeFrequency.X2.Ortho.TileDualsProof
public import PrimeBHT.TimeFrequency.X2.CZ.Minkowski

/-!
# X2, node V12-top: the one-sided values `valS`, the split `topOpNorm ≤ valS 1 + valS (-1)`, and `ĉ`

* `valS σ`: the `σ`-side value `sup |W|^{-1/2} ‖ψ T_m F‖_{L²(ℝ;L²(Y))}` over one-sided top multipliers (Hilbert slots,
  `s = q = 2`); `valS_le_topOpNorm`, `topOpNorm_le_valS_add`;
* `ofReal_val_eq`: the normalized norm of one operator is `ĉ = ℓ^{-1/2} · va ψ m F`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform ComplexConjugate ContDiff Real
open PrimeBHT.TimeFrequency.Tile PrimeBHT.Statements

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

variable {P : ℕ} [NeZero P]

/-- The `σ`-side value of the top datum `(W, ξ)` (Hilbert slots). -/
def valS (𝔭 : Params) (σ : ℝ) (k : Fin 3) (F : ℝ → ZMod P → ℂ) (W : ℤ × ℤ) (ξ : ℝ) : ℝ≥0∞ :=
  ⨆ (ψ : ℝ → ℂ) (m : ℝ → ℂ) (_ : InPsi 𝔭 W.1 W.2 ψ) (_ : InTopMultS 𝔭 σ W ξ k m),
    ENNReal.ofReal (((2 : ℝ) ^ W.1) ^ (-1 / (2 : ℝ))) *
      eLpNorm (fun x => yNorm 2 (ψ x • tmult m F x)) (ENNReal.ofReal 2) volume

theorem valS_le_topOpNorm (𝔭 : Params) (σ : ℝ) (k : Fin 3) (F : ℝ → ZMod P → ℂ) (W : ℤ × ℤ) (ξ : ℝ) :
    valS 𝔭 σ k F W ξ ≤ topOpNorm 𝔭 2 2 k F W ξ := by
  refine iSup₂_le fun ψ m => iSup₂_le fun hψ hm => ?_
  exact le_iSup₂_of_le ψ m (le_iSup₂_of_le hψ hm.1 le_rfl)

/-- Measurability of `x ↦ yNorm 2 (ψ x • T_m F x)` for a top multiplier. -/
theorem measurable_yNorm_psi_tmult {𝔭 : Params} {W : ℤ × ℤ} {ξ : ℝ} {k : Fin 3} {ψ m : ℝ → ℂ}
    (hψ : InPsi 𝔭 W.1 W.2 ψ) (hm : InTopMult 𝔭 W ξ k m) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) :
    Measurable fun x => yNorm 2 (ψ x • tmult m F x) := by
  have h1 : Measurable (tmult m F) := measurable_tmult_of_cont (continuous_fourierInv_inTopMult hm) hF
  have h2 : Measurable fun x => ψ x • tmult m F x :=
    measurable_pi_iff.2 fun y => (hψ.1.measurable.mul ((measurable_pi_apply y).comp h1))
  exact (measurable_yNorm_fun 2).comp h2

/-- **The split**: `topOpNorm ≤ valS 1 + valS (-1)` (the hole of a top multiplier separates the two sides). -/
theorem topOpNorm_le_valS_add (𝔭 : Params) (k : Fin 3) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {B : ℝ}
    (hB : ∀ x, yNorm 2 (F x) ≤ B) (W : ℤ × ℤ) (ξ : ℝ) :
    topOpNorm 𝔭 2 2 k F W ξ ≤ valS 𝔭 1 k F W ξ + valS 𝔭 (-1) k F W ξ := by
  have hbdd : IsBddC F := (isBddV_iff (by norm_num : (0 : ℝ) < 2)).1 ⟨hF, B, hB⟩
  refine iSup₂_le fun ψ m => iSup₂_le fun hψ hm => ?_
  have hp := inTopMultS_partPlus hm
  have hq := inTopMultS_partMinus hm
  set mp := partPlus (ξ * freqDir k) m with hmp
  set mn := partMinus (ξ * freqDir k) m with hmn
  have hh : ∀ η, |η - ξ * freqDir k| < topHole * (2 : ℝ) ^ (-W.1) → m η = 0 := fun η h => hm.2.2.1 η h
  have ha : (0 : ℝ) < topHole * (2 : ℝ) ^ (-W.1) := mul_pos topHole_pos (zpow_pos (by norm_num) _)
  have hsum : m = fun η => mp η + mn η := funext fun η => (partPlus_add_partMinus hh ha η).symm
  have hadd : tmult m F = tmult mp F + tmult mn F := by
    rw [hsum]
    exact tmult_add_mult (goodKernel_inTopMult hp.1) (goodKernel_inTopMult hq.1)
      (integrable_inTopMult hp.1) (integrable_inTopMult hq.1) hbdd
  have hpt : ∀ x, yNorm 2 (ψ x • tmult m F x) ≤
      yNorm 2 (ψ x • tmult mp F x) + yNorm 2 (ψ x • tmult mn F x) := by
    intro x
    rw [hadd]
    simp only [Pi.add_apply, smul_add]
    exact CZ.yNorm_add_le (by norm_num) _ _
  have hm1 := measurable_yNorm_psi_tmult hψ hp.1 hF
  have hm2 := measurable_yNorm_psi_tmult hψ hq.1 hF
  have hle : eLpNorm (fun x => yNorm 2 (ψ x • tmult m F x)) (ENNReal.ofReal 2) volume ≤
      eLpNorm (fun x => yNorm 2 (ψ x • tmult mp F x)) (ENNReal.ofReal 2) volume +
        eLpNorm (fun x => yNorm 2 (ψ x • tmult mn F x)) (ENNReal.ofReal 2) volume := by
    have h1 : eLpNorm (fun x => yNorm 2 (ψ x • tmult m F x)) (ENNReal.ofReal 2) volume ≤
        eLpNorm ((fun x => yNorm 2 (ψ x • tmult mp F x)) + fun x => yNorm 2 (ψ x • tmult mn F x))
          (ENNReal.ofReal 2) volume := by
      refine eLpNorm_mono (measurable_yNorm_psi_tmult hψ hm hF).aestronglyMeasurable fun x => ?_
      have h0 : 0 ≤ yNorm 2 (ψ x • tmult m F x) := by unfold yNorm; positivity
      have h0' : 0 ≤ yNorm 2 (ψ x • tmult mp F x) + yNorm 2 (ψ x • tmult mn F x) := by
        unfold yNorm; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      simp only [Pi.add_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg h0']
      exact hpt x
    refine h1.trans (eLpNorm_add_le ?_)
    rw [ENNReal.ofReal_ofNat]; exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2)
  have hv1 : ENNReal.ofReal (((2 : ℝ) ^ W.1) ^ (-1 / (2 : ℝ))) *
      eLpNorm (fun x => yNorm 2 (ψ x • tmult mp F x)) (ENNReal.ofReal 2) volume ≤ valS 𝔭 1 k F W ξ :=
    le_iSup₂_of_le ψ mp (le_iSup₂_of_le hψ hp le_rfl)
  have hv2 : ENNReal.ofReal (((2 : ℝ) ^ W.1) ^ (-1 / (2 : ℝ))) *
      eLpNorm (fun x => yNorm 2 (ψ x • tmult mn F x)) (ENNReal.ofReal 2) volume ≤ valS 𝔭 (-1) k F W ξ :=
    le_iSup₂_of_le ψ mn (le_iSup₂_of_le hψ hq le_rfl)
  calc ENNReal.ofReal (((2 : ℝ) ^ W.1) ^ (-1 / (2 : ℝ))) *
        eLpNorm (fun x => yNorm 2 (ψ x • tmult m F x)) (ENNReal.ofReal 2) volume
      ≤ ENNReal.ofReal (((2 : ℝ) ^ W.1) ^ (-1 / (2 : ℝ))) *
        (eLpNorm (fun x => yNorm 2 (ψ x • tmult mp F x)) (ENNReal.ofReal 2) volume +
          eLpNorm (fun x => yNorm 2 (ψ x • tmult mn F x)) (ENNReal.ofReal 2) volume) :=
        mul_le_mul_right hle _
    _ = _ := mul_add _ _ _
    _ ≤ _ := add_le_add hv1 hv2

/-- The normalized norm of one operator: `|W|^{-1/2} ‖ψ T_m F‖_{L²(ℝ;L²(Y))} = ofReal (ℓ^{-1/2} va ψ m F)`. -/
theorem ofReal_val_eq {𝔭 : Params} {s v : ℤ} {c : ℝ} {ψ m : ℝ → ℂ} {F : ℝ → ZMod P → ℂ} (hN : 12 ≤ 𝔭.N)
    (hD : 12 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ) (hm : InMult 𝔭 s c m) (hF : Measurable F) {B : ℝ}
    (hB : ∀ x, yNorm 2 (F x) ≤ B) :
    ENNReal.ofReal (((2 : ℝ) ^ s) ^ (-1 / (2 : ℝ))) *
      eLpNorm (fun x => yNorm 2 (ψ x • tmult m F x)) (ENNReal.ofReal 2) volume =
        ENNReal.ofReal (((2 : ℝ) ^ s) ^ (-(1 : ℝ) / 2) * va ψ m F) := by
  have hmeas : Measurable fun x => ψ x • tmult m F x := measurable_psi_smul_tmult hψ hm hF
  have hmN : AEStronglyMeasurable (fun x => yNorm 2 (ψ x • tmult m F x)) volume :=
    ((measurable_yNorm_fun 2).comp hmeas).aestronglyMeasurable
  have hint := integrable_piece_sq hN hD hβ hψ hm hF hB
  have he2 := eLpNorm_sq_eq hmN hint
  have hva := va_nonneg ψ m F
  have hsq : va ψ m F ^ 2 = ∫ x, yNorm 2 (ψ x • tmult m F x) ^ 2 :=
    Real.sq_sqrt (integral_nonneg fun x => by unfold yNorm; positivity)
  have he : eLpNorm (fun x => yNorm 2 (ψ x • tmult m F x)) (ENNReal.ofReal 2) volume =
      ENNReal.ofReal (va ψ m F) := by
    set e := eLpNorm (fun x => yNorm 2 (ψ x • tmult m F x)) (ENNReal.ofReal 2) volume
    have h1 : e = (e ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by rw [← ENNReal.rpow_mul]; norm_num
    rw [h1, he2, ← hsq, ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq hva]
  rw [he, ← ENNReal.ofReal_mul (Real.rpow_nonneg (zpow_pos (by norm_num) _).le _)]

end PrimeBHT.TimeFrequency.X2
