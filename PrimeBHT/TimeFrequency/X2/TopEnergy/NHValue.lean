module

public import PrimeBHT.TimeFrequency.X2.TopEnergy.Main
public import PrimeBHT.TimeFrequency.X2.TopEnergy.PintTop
public import PrimeBHT.TimeFrequency.X2.EngTail.Top
public import PrimeBHT.TimeFrequency.X2.Pint.TheoremIMeas
public import PrimeBHT.TimeFrequency.Tile.Gram.Pair

/-!
# X2, TB-4b: one-sided top values at `(s, qX)` and top operators as kernel operators

* `valSq`: the `σ`-side value at the mixed norm `L^{qX}(L^s)`; `topOpNorm ≤ valSq 1 + valSq (-1)` (the `±` split of
  `Main.lean`, with Minkowski in `L^{qX}(L^s)`);
* `topKer ψ m x w = ψ x · 𝓕⁻m (x - w)`: `kernelOp (topKer ψ m) G = ψ • tmult m G`, jointly continuous, with the
  `L¹` bound `∫ ‖topKer ψ m x ·‖ ≤ topCinf 𝔭 = 768 𝔭.C²` (two derivatives of the multiplier);
* `val_rpow_eq`: `(|W|^{-1/q} ‖f‖_q)^q = |W|⁻¹ ∫ f^q`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform
open PrimeBHT.Statements

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

variable {P : ℕ} [NeZero P]

/-- The `σ`-side value of the top datum `(W, ξ)` at `L^{qX}(L^s)`. -/
def valSq (𝔭 : Params) (s qX σ : ℝ) (k : Fin 3) (F : ℝ → ZMod P → ℂ) (W : ℤ × ℤ) (ξ : ℝ) : ℝ≥0∞ :=
  ⨆ (ψ : ℝ → ℂ) (m : ℝ → ℂ) (_ : InPsi 𝔭 W.1 W.2 ψ) (_ : InTopMultS 𝔭 σ W ξ k m),
    ENNReal.ofReal (((2 : ℝ) ^ W.1) ^ (-1 / qX)) *
      eLpNorm (fun x => yNorm s (ψ x • tmult m F x)) (ENNReal.ofReal qX) volume

theorem measurable_yNorm_psi_tmult' {𝔭 : Params} {W : ℤ × ℤ} {ξ : ℝ} {k : Fin 3} {ψ m : ℝ → ℂ} (s : ℝ)
    (hψ : InPsi 𝔭 W.1 W.2 ψ) (hm : InTopMult 𝔭 W ξ k m) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) :
    Measurable fun x => yNorm s (ψ x • tmult m F x) := by
  have h1 : Measurable (tmult m F) := measurable_tmult_of_cont (continuous_fourierInv_inTopMult hm) hF
  have h2 : Measurable fun x => ψ x • tmult m F x :=
    measurable_pi_iff.2 fun y => (hψ.1.measurable.mul ((measurable_pi_apply y).comp h1))
  exact (measurable_yNorm_fun s).comp h2

theorem topOpNorm_le_valSq_add (𝔭 : Params) {s qX : ℝ} (hs : 1 ≤ s) (hq : 1 ≤ qX) (k : Fin 3)
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {B : ℝ} (hB : ∀ x, yNorm s (F x) ≤ B) (W : ℤ × ℤ) (ξ : ℝ) :
    topOpNorm 𝔭 s qX k F W ξ ≤ valSq 𝔭 s qX 1 k F W ξ + valSq 𝔭 s qX (-1) k F W ξ := by
  have hbdd : IsBddC F := (isBddV_iff (by linarith : (0 : ℝ) < s)).1 ⟨hF, B, hB⟩
  refine iSup₂_le fun ψ m => iSup₂_le fun hψ hm => ?_
  have hp := inTopMultS_partPlus hm
  have hq' := inTopMultS_partMinus hm
  set mp := partPlus (ξ * freqDir k) m with hmp
  set mn := partMinus (ξ * freqDir k) m with hmn
  have hh : ∀ η, |η - ξ * freqDir k| < topHole * (2 : ℝ) ^ (-W.1) → m η = 0 := fun η h => hm.2.2.1 η h
  have ha : (0 : ℝ) < topHole * (2 : ℝ) ^ (-W.1) := mul_pos topHole_pos (zpow_pos (by norm_num) _)
  have hsum : m = fun η => mp η + mn η := funext fun η => (partPlus_add_partMinus hh ha η).symm
  have hadd : tmult m F = tmult mp F + tmult mn F := by
    rw [hsum]
    exact tmult_add_mult (goodKernel_inTopMult hp.1) (goodKernel_inTopMult hq'.1)
      (integrable_inTopMult hp.1) (integrable_inTopMult hq'.1) hbdd
  have hpt : ∀ x, yNorm s (ψ x • tmult m F x) ≤
      yNorm s (ψ x • tmult mp F x) + yNorm s (ψ x • tmult mn F x) := by
    intro x
    rw [hadd]
    simp only [Pi.add_apply, smul_add]
    exact CZ.yNorm_add_le hs _ _
  have hle : eLpNorm (fun x => yNorm s (ψ x • tmult m F x)) (ENNReal.ofReal qX) volume ≤
      eLpNorm (fun x => yNorm s (ψ x • tmult mp F x)) (ENNReal.ofReal qX) volume +
        eLpNorm (fun x => yNorm s (ψ x • tmult mn F x)) (ENNReal.ofReal qX) volume := by
    have h1 : eLpNorm (fun x => yNorm s (ψ x • tmult m F x)) (ENNReal.ofReal qX) volume ≤
        eLpNorm ((fun x => yNorm s (ψ x • tmult mp F x)) + fun x => yNorm s (ψ x • tmult mn F x))
          (ENNReal.ofReal qX) volume := by
      refine eLpNorm_mono (measurable_yNorm_psi_tmult' s hψ hm hF).aestronglyMeasurable fun x => ?_
      have h0 : 0 ≤ yNorm s (ψ x • tmult m F x) := Pint.yNorm_nonneg _ _
      have h0' : 0 ≤ yNorm s (ψ x • tmult mp F x) + yNorm s (ψ x • tmult mn F x) :=
        add_nonneg (Pint.yNorm_nonneg _ _) (Pint.yNorm_nonneg _ _)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      simp only [Pi.add_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg h0']
      exact hpt x
    refine h1.trans (eLpNorm_add_le ?_)
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq
  have hv1 : ENNReal.ofReal (((2 : ℝ) ^ W.1) ^ (-1 / qX)) *
      eLpNorm (fun x => yNorm s (ψ x • tmult mp F x)) (ENNReal.ofReal qX) volume ≤
        valSq 𝔭 s qX 1 k F W ξ :=
    le_iSup₂_of_le ψ mp (le_iSup₂_of_le hψ hp le_rfl)
  have hv2 : ENNReal.ofReal (((2 : ℝ) ^ W.1) ^ (-1 / qX)) *
      eLpNorm (fun x => yNorm s (ψ x • tmult mn F x)) (ENNReal.ofReal qX) volume ≤
        valSq 𝔭 s qX (-1) k F W ξ :=
    le_iSup₂_of_le ψ mn (le_iSup₂_of_le hψ hq' le_rfl)
  calc ENNReal.ofReal (((2 : ℝ) ^ W.1) ^ (-1 / qX)) *
        eLpNorm (fun x => yNorm s (ψ x • tmult m F x)) (ENNReal.ofReal qX) volume
      ≤ ENNReal.ofReal (((2 : ℝ) ^ W.1) ^ (-1 / qX)) *
        (eLpNorm (fun x => yNorm s (ψ x • tmult mp F x)) (ENNReal.ofReal qX) volume +
          eLpNorm (fun x => yNorm s (ψ x • tmult mn F x)) (ENNReal.ofReal qX) volume) :=
        mul_le_mul_right hle _
    _ = _ := mul_add _ _ _
    _ ≤ _ := add_le_add hv1 hv2

/-- `(L^{-1/q} ‖f‖_q)^q = L⁻¹ ∫ f^q` for nonnegative measurable `f`. -/
theorem val_rpow_eq {q : ℝ} (hq : 0 < q) {f : ℝ → ℝ} (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {L : ℝ}
    (hL : 0 < L) :
    (ENNReal.ofReal (L ^ (-1 / q)) * eLpNorm f (ENNReal.ofReal q) volume) ^ q =
      ENNReal.ofReal L⁻¹ * ∫⁻ x, ENNReal.ofReal (f x ^ q) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hL.le _) hq.le,
    ← Real.rpow_mul hL.le, show -1 / q * q = -1 by field_simp, Real.rpow_neg_one,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq) ENNReal.ofReal_ne_top hfm.aestronglyMeasurable,
    ENNReal.toReal_ofReal hq.le, ← ENNReal.rpow_mul, show 1 / q * q = 1 by field_simp, ENNReal.rpow_one]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal (hf0 x), ENNReal.ofReal_rpow_of_nonneg (hf0 x) hq.le]

/-! ## Top operators as kernel operators -/

/-- The kernel of `ψ · T_m`. -/
def topKer (ψ m : ℝ → ℂ) : ℝ → ℝ → ℂ := fun x w => ψ x * 𝓕⁻ m (x - w)

omit [NeZero P] in
theorem kernelOp_topKer (ψ m : ℝ → ℂ) (G : ℝ → ZMod P → ℂ) (x : ℝ) :
    Pint.kernelOp (topKer ψ m) G x = ψ x • tmult m G x := by
  funext y
  simp only [Pint.kernelOp, topKer, Pi.smul_apply, smul_eq_mul, tmult_apply, ← integral_const_mul, mul_assoc]

theorem stronglyMeasurable_topKer {ψ m : ℝ → ℂ} (hψ : Continuous ψ) (hm : Continuous (𝓕⁻ m)) :
    StronglyMeasurable (Function.uncurry (topKer ψ m)) :=
  (by unfold topKer; fun_prop : Continuous (Function.uncurry (topKer ψ m))).stronglyMeasurable

/-- The `L¹` constant of top kernels. -/
def topCinf (𝔭 : Params) : ℝ := 𝔭.C * (2 ^ (⌈(2 : ℝ)⌉₊ + 1) * (2 * topRad) * 𝔭.C) * 2

theorem lintegral_topKer_le {𝔭 : Params} (hD : 2 ≤ 𝔭.D) (hC : 0 ≤ 𝔭.C) {W : ℤ × ℤ} {ξ : ℝ} {k : Fin 3}
    {ψ m : ℝ → ℂ} (hψ : InPsi 𝔭 W.1 W.2 ψ) (hm : InTopMult 𝔭 W ξ k m) (x : ℝ) :
    ∫⁻ w, ‖topKer ψ m x w‖ₑ ≤ ENNReal.ofReal (topCinf 𝔭) := by
  set L : ℝ := (2 : ℝ) ^ W.1 with hL
  have hL0 : 0 < L := zpow_pos (by norm_num) _
  set c0 : ℝ := 2 ^ (⌈(2 : ℝ)⌉₊ + 1) * (2 * topRad) * 𝔭.C with hc0
  have hc00 : 0 ≤ c0 := by unfold topRad at hc0; rw [hc0]; positivity
  have hk : ∀ w, ‖topKer ψ m x w‖ ≤ 𝔭.C * (c0 * (L⁻¹ * (1 + |w - x| / L) ^ (-(2 : ℝ)))) := by
    intro w
    rw [topKer, norm_mul]
    have h1 := kernel_inTopMult_le (M := 2) (by exact_mod_cast hD) hm (x - w)
    rw [abs_sub_comm] at h1
    exact mul_le_mul (norm_psi_le hψ x) h1 (norm_nonneg _) hC
  have hint : Integrable fun w : ℝ => 𝔭.C * (c0 * (L⁻¹ * (1 + |w - x| / L) ^ (-(2 : ℝ)))) :=
    (((Tile.integrable_one_add_abs_sub_div_rpow (by norm_num : (1 : ℝ) < 2) x hL0).const_mul _).const_mul
      _).const_mul _
  calc ∫⁻ w, ‖topKer ψ m x w‖ₑ ≤ ∫⁻ w, ENNReal.ofReal (𝔭.C * (c0 * (L⁻¹ * (1 + |w - x| / L) ^ (-(2 : ℝ))))) :=
        lintegral_mono fun w => by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hk w)
    _ = ENNReal.ofReal (∫ w, 𝔭.C * (c0 * (L⁻¹ * (1 + |w - x| / L) ^ (-(2 : ℝ))))) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun w => by positivity)).symm
    _ = ENNReal.ofReal (topCinf 𝔭) := by
        rw [integral_const_mul, integral_const_mul, integral_const_mul,
          Tile.integral_one_add_abs_sub_div_rpow (by norm_num : (1 : ℝ) < 2) x hL0, topCinf, ← hc0]
        congr 1
        field_simp
        ring

theorem topCinf_nonneg {𝔭 : Params} (hC : 0 ≤ 𝔭.C) : 0 ≤ topCinf 𝔭 := by
  unfold topCinf topRad; positivity

end PrimeBHT.TimeFrequency.X2
