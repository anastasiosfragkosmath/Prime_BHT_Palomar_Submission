module

public import PrimeBHT.TimeFrequency.X2.Paraproduct.Symbols
public import PrimeBHT.TimeFrequency.X2.Paraproduct.Tensor
public import PrimeBHT.TimeFrequency.X2.ClassKernel
public import PrimeBHT.TimeFrequency.Tile.Maximal

/-!
# V14 (paraproduct): the single-scale bound by the Hardy-Littlewood maximal function

For an adapted symbol (`IsAdaptedSymbol A J j σ`) the vector multiplier `tmult σ` (convolution with the
Schwartz kernel `𝓕⁻ σ`) satisfies, for `s ≥ 1`, measurable `F : ℝ → (ZMod P → ℂ)` and every `x`,
`ofReal (yNorm s (tmult σ F x)) ≤ 60 · 2^{2J} · M(ofReal ∘ yNorm s ∘ F)(x)`
(`ofReal_yNorm_tmult_le_adapted`; copy of the proof of `ClassLemmas.ofReal_yNorm_tmult_le` with the
kernel bound `|𝓕⁻ σ(w)| ≤ 6 · 2^{2J} 2^{Jj} (1 + 2^{Jj}|w|)⁻²` taken from the adapted-symbol class instead of
`Params.Admissible`: the symbols of V14 have support `2^{2J}` times the scale, outside `β ≤ 3`).
The maximal theorem (`eLpNorm_maximalHLR_le`) then gives the `L^p` bound `eLpNorm_sup_tmult_le`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform ComplexConjugate Real ContDiff
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- Pointwise bound of the vector multiplier by a kernel `K₀ R⁻¹ (1 + |x - z|/R)⁻²` (copy of
`ClassLemmas.ofReal_yNorm_tmult_le` with the kernel bound as hypothesis). -/
theorem ofReal_yNorm_tmult_le_of_kernel {s : ℝ} (hs : 1 ≤ s) {P : ℕ} [NeZero P] {m : ℝ → ℂ} {R K₀ : ℝ}
    (hR : 0 < R) (hK₀ : 0 < K₀) (hcont : Continuous (𝓕⁻ m))
    (hk : ∀ w, ‖𝓕⁻ m w‖ ≤ K₀ * (R⁻¹ * (1 + |w| / R) ^ (-2 : ℤ))) {F : ℝ → ZMod P → ℂ}
    (hF : Measurable F) (x : ℝ) :
    ENNReal.ofReal (yNorm s (tmult m F x)) ≤ ENNReal.ofReal K₀ *
      ∫⁻ z, ENNReal.ofReal (R⁻¹ * (1 + |x - z| / R) ^ (-2 : ℤ)) * ENNReal.ofReal (yNorm s (F z)) := by
  have hs0 : 0 < s := by linarith
  set Kf : ℝ → ℂ := 𝓕⁻ m with hKf
  set kern : ℝ → ℝ := fun z => R⁻¹ * (1 + |x - z| / R) ^ (-2 : ℤ) with hkern
  have hkern_nn : ∀ z, 0 ≤ kern z := fun z => by simp only [hkern]; positivity
  set I : ℝ≥0∞ := ∫⁻ z, ENNReal.ofReal (kern z) * ENNReal.ofReal (yNorm s (F z)) with hI
  by_cases hItop : I = ⊤
  · rw [hItop, ENNReal.mul_top (by simpa using hK₀)]
    exact le_top
  have hg_meas : Measurable fun z => yNorm s (F z) := (measurable_yNorm_fun s).comp hF
  have hKmeas : Continuous fun z => Kf (x - z) := hcont.comp (continuous_const.sub continuous_id)
  have hprod_meas : AEStronglyMeasurable (fun z => ‖Kf (x - z)‖ * yNorm s (F z)) volume :=
    (hKmeas.norm.aestronglyMeasurable).mul hg_meas.aestronglyMeasurable
  have hpt : ∀ z, ENNReal.ofReal (‖Kf (x - z)‖ * yNorm s (F z)) ≤
      ENNReal.ofReal K₀ * (ENNReal.ofReal (kern z) * ENNReal.ofReal (yNorm s (F z))) := by
    intro z
    rw [← ENNReal.ofReal_mul (hkern_nn z), ← ENNReal.ofReal_mul hK₀.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hk (x - z)
    calc ‖Kf (x - z)‖ * yNorm s (F z) ≤ (K₀ * kern z) * yNorm s (F z) :=
          mul_le_mul_of_nonneg_right this (yNorm_nonneg' s _)
      _ = _ := by ring
  have hlint : ∫⁻ z, ENNReal.ofReal (‖Kf (x - z)‖ * yNorm s (F z)) ≤ ENNReal.ofReal K₀ * I := by
    calc _ ≤ ∫⁻ z, ENNReal.ofReal K₀ * (ENNReal.ofReal (kern z) * ENNReal.ofReal (yNorm s (F z))) :=
          lintegral_mono hpt
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hlint_fin : ∫⁻ z, ENNReal.ofReal (‖Kf (x - z)‖ * yNorm s (F z)) < ⊤ :=
    lt_of_le_of_lt hlint (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hItop))
  have hint : Integrable (fun z => ‖Kf (x - z)‖ * yNorm s (F z)) volume :=
    ⟨hprod_meas, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun z => mul_nonneg (norm_nonneg _) (yNorm_nonneg' s _))).2 hlint_fin⟩
  have hV : ∀ y, Integrable (fun z => Kf (x - z) * F z y) volume := by
    intro y
    refine (hint.const_mul ((P : ℝ) ^ s⁻¹)).mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact hKmeas.aestronglyMeasurable.mul ((measurable_pi_apply y).comp hF).aestronglyMeasurable
    · rw [norm_mul]
      calc ‖Kf (x - z)‖ * ‖F z y‖ ≤ ‖Kf (x - z)‖ * ((P : ℝ) ^ s⁻¹ * yNorm s (F z)) :=
            mul_le_mul_of_nonneg_left (norm_apply_le_rpow_mul_yNorm hs0 _ _) (norm_nonneg _)
        _ = (P : ℝ) ^ s⁻¹ * (‖Kf (x - z)‖ * yNorm s (F z)) := by ring
  have hMink := yNorm_integral_le_of_one_le hs (fun z y => Kf (x - z) * F z y) hV
  have h1 : yNorm s (tmult m F x) ≤ ∫ z, ‖Kf (x - z)‖ * yNorm s (F z) := by
    refine hMink.trans (le_of_eq (integral_congr_ae (Eventually.of_forall fun z => ?_)))
    exact yNorm_fun_const_mul hs0 _ _
  calc ENNReal.ofReal (yNorm s (tmult m F x))
      ≤ ENNReal.ofReal (∫ z, ‖Kf (x - z)‖ * yNorm s (F z)) := ENNReal.ofReal_le_ofReal h1
    _ = ∫⁻ z, ENNReal.ofReal (‖Kf (x - z)‖ * yNorm s (F z)) :=
        ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun z => mul_nonneg (norm_nonneg _) (yNorm_nonneg' s _))
    _ ≤ _ := hlint

/-- The kernel of an adapted symbol: `‖𝓕⁻ σ(w)‖ ≤ 6 · 2^{2J} · (2^{Jj})⁻¹⁻¹ (1 + |w| 2^{Jj})⁻²`. -/
theorem norm_fourierInv_adapted_le {A : ℝ} (hA : 0 < A) {J : ℕ} {j : ℤ} {σ : ℝ → ℂ} (hσ : IsAdaptedSymbol A J j σ) (w : ℝ) :
    ‖𝓕⁻ σ w‖ ≤ (6 * (2 : ℝ) ^ (2 * J)) *
      (((fscale A J j)⁻¹)⁻¹ * (1 + |w| / (fscale A J j)⁻¹) ^ (-2 : ℤ)) := by
  have hL := fscale_pos hA J j
  have h := norm_fourierInv_le (n := σ) (c := 0) (r := (2 : ℝ) ^ (2 * J) * fscale A J j) (A := 1)
    (l := fscale A J j) (by positivity) hL (hσ.1.of_le (by norm_cast))
    (fun ξ hξ => hσ.2.1 ξ (by simpa using hξ))
    (fun ξ => by simpa using hσ.2.2 0 (Nat.zero_le _) ξ)
    (fun ξ => by
      have h2 := hσ.2.2 2 le_rfl ξ
      rw [one_mul, inv_pow]
      calc ‖iteratedDeriv 2 σ ξ‖ = (fscale A J j ^ 2)⁻¹ * (fscale A J j ^ 2 * ‖iteratedDeriv 2 σ ξ‖) := by
            field_simp
        _ ≤ (fscale A J j ^ 2)⁻¹ * 1 := by gcongr
        _ = (fscale A J j ^ 2)⁻¹ := mul_one _) w
  refine h.trans (le_of_eq ?_)
  rw [inv_inv, div_inv_eq_mul, zpow_neg, zpow_ofNat, inv_pow]
  ring

/-- **Single-scale domination**: `ofReal (yNorm s (tmult σ F x)) ≤ 60 · 2^{2J} · M(ofReal ∘ yNorm s ∘ F)(x)`. -/
theorem ofReal_yNorm_tmult_le_adapted {A : ℝ} (hA : 0 < A) {J : ℕ} {j : ℤ} {σ : ℝ → ℂ} (hσ : IsAdaptedSymbol A J j σ) {s : ℝ}
    (hs : 1 ≤ s) {P : ℕ} [NeZero P] {F : ℝ → ZMod P → ℂ} (hF : Measurable F) (x : ℝ) :
    ENNReal.ofReal (yNorm s (tmult σ F x)) ≤ ENNReal.ofReal (60 * (2 : ℝ) ^ (2 * J)) *
      PrimeCarleson.Proof.Common.maximalHLR (fun z => ENNReal.ofReal (yNorm s (F z))) x := by
  have hL := fscale_pos hA J j
  have hint : Integrable σ volume := hσ.1.continuous.integrable_of_hasCompactSupport hσ.hasCompactSupport
  have hK : 0 < 6 * (2 : ℝ) ^ (2 * J) := by positivity
  have hA := ofReal_yNorm_tmult_le_of_kernel hs (inv_pos.2 hL) hK (continuous_fourierInv_of_integrable' hint)
    (norm_fourierInv_adapted_le hA hσ) hF x
  have hW : Measurable fun z => ENNReal.ofReal (yNorm s (F z)) :=
    ENNReal.measurable_ofReal.comp ((measurable_yNorm_fun s).comp hF)
  have hHLR := PrimeBHT.TimeFrequency.Tile.lintegral_kernel_le_maximalHLR (inv_pos.2 hL) x hW
  calc ENNReal.ofReal (yNorm s (tmult σ F x))
      ≤ ENNReal.ofReal (6 * (2 : ℝ) ^ (2 * J)) * (10 * PrimeCarleson.Proof.Common.maximalHLR
        (fun z => ENNReal.ofReal (yNorm s (F z))) x) := hA.trans (by gcongr)
    _ = ENNReal.ofReal (60 * (2 : ℝ) ^ (2 * J)) *
        PrimeCarleson.Proof.Common.maximalHLR (fun z => ENNReal.ofReal (yNorm s (F z))) x := by
      rw [← mul_assoc, show (60 * (2 : ℝ) ^ (2 * J)) = 6 * (2 : ℝ) ^ (2 * J) * 10 by ring,
        ENNReal.ofReal_mul hK.le]
      norm_num

/-- The `ℝ≥0∞`-valued function `ofReal ∘ yNorm s ∘ F` has the same `L^q` norm as `yNorm s ∘ F`. -/
theorem eLpNorm_ofReal_yNorm {P : ℕ} [NeZero P] (q s : ℝ) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) :
    eLpNorm (fun z => ENNReal.ofReal (yNorm s (F z))) (ENNReal.ofReal q) volume =
      eLpNorm (fun z => yNorm s (F z)) (ENNReal.ofReal q) volume := by
  have hm : Measurable fun z => yNorm s (F z) := (measurable_yNorm_fun s).comp hF
  refine eLpNorm_congr_enorm_ae hm.ennreal_ofReal.aestronglyMeasurable hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [enorm_eq_self, Real.enorm_eq_ofReal (yNorm_nonneg' s _)]

/-- **Maximal theorem for the single-scale bound**: `‖M(ofReal ∘ yNorm s ∘ F)‖_{L^p} ≤ C_p ‖yNorm s ∘ F‖_{L^p}`. -/
theorem eLpNorm_maximal_yNorm_le {p : ℝ} (hp : 1 < p) (s : ℝ) {P : ℕ} [NeZero P] {F : ℝ → ZMod P → ℂ}
    (hF : Measurable F) :
    eLpNorm (PrimeCarleson.Proof.Common.maximalHLR (fun z => ENNReal.ofReal (yNorm s (F z))))
        (ENNReal.ofReal p) volume ≤
      PrimeCarleson.Proof.Common.maximalHLRConst (ENNReal.ofReal p) *
        eLpNorm (fun z => yNorm s (F z)) (ENNReal.ofReal p) volume := by
  have h1 : (1 : ℝ≥0∞) < ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hp
  have := PrimeCarleson.Proof.Common.eLpNorm_maximalHLR_le h1 (fun z => ENNReal.ofReal (yNorm s (F z)))
  rwa [eLpNorm_ofReal_yNorm p s hF] at this

end PrimeBHT.TimeFrequency.X2
