module

public import PrimeBHT.TimeFrequency.X2.Classes
public import PrimeBHT.TimeFrequency.Tile.Maximal
import PrimeBHT.TimeFrequency.X2.ClassKernel
import PrimeBHT.TimeFrequency.Tile.Inside
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# X2, node V07: the two lemmas about the adapted classes

Definitions are in `X2/Classes.lean`, the analytic toolbox in `X2/ClassKernel.lean`.

## Final statements (namespace `PrimeBHT.TimeFrequency.X2`)

* `norm_singleTile_le` (DPLMV e:singlescaleM with explicit decay): for admissible `𝔭` and `1 ≤ s` there is `K ≥ 0`
  such that for every `P`, scale `sc`, `ψ ∈ Ψ_I(𝔭)`, `m ∈ M_ω(𝔭)`, measurable `F : ℝ → (ZMod P → ℂ)`:
  `ofReal (yNorm s (ψ x • tmult m F x)) ≤ ofReal (K ⟨(x - c_I)/|I|⟩^{-N}) * maximalHLR (ofReal ∘ yNorm s ∘ F) x`.
  Proof: kernel decay `|𝓕⁻ m (w)| ≤ 3βC l (1 + l|w|)⁻²` (two derivatives, Fourier transform of `m''`),
  Minkowski's integral inequality for `yNorm s` and `lintegral_kernel_le_maximalHLR`; `K = 30 β C²`.
* `treeOp_locPoly` (B6', route check (M2)): the tree operator applied to `p_W g` is `K ∑_{b ≤ 100}` tree operators
  of the class `𝔭.loc`, `K = 1 + 2^100`.  Proof: exact Taylor expansion `p_W(z) = ∑_b a_b(x) (z - x)^b`, the kernel
  identity `𝓕⁻ (m_b) = (-w)^b 𝓕⁻ m` with `m_b = (2πi)^{-b} m^{(b)}`, the estimate
  `|a_b(x)| |I|^b ≤ (1 + 2^100) ⟨(x - c_I)/|I|⟩^{100}` for `I ⊆ W`, and that multiplying by `(x - a)^k` preserves
  the Fourier support (`fourier_pow_mul_eq_zero`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform ComplexConjugate ContDiff Real SchwartzMap
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-! ### `norm_singleTile_le` -/


theorem norm_fourierInv_inMult_le {𝔭 : Params} (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) {s : ℤ} {c : ℝ}
    {m : ℝ → ℂ} (hm : InMult 𝔭 s c m) (w : ℝ) :
    ‖𝓕⁻ m w‖ ≤ 3 * 𝔭.β * 𝔭.C * (((2 : ℝ) ^ s)⁻¹ * (1 + |w| / (2 : ℝ) ^ s) ^ (-2 : ℤ)) := by
  obtain ⟨hsm, hsupp, hder⟩ := hm
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-s) := zpow_pos (by norm_num) _
  have hC : 0 ≤ 𝔭.C := by
    have := hder 0 (Nat.zero_le _) 0
    simp only [pow_zero, one_mul, iteratedDeriv_zero] at this
    exact (norm_nonneg _).trans this
  have hk := norm_fourierInv_le (n := m) (c := c) (r := 𝔭.β * (2 : ℝ) ^ (-s) / 2) (A := 𝔭.C)
    (l := (2 : ℝ) ^ (-s)) (by positivity) hl (hsm.of_le (by simp)) hsupp
    (fun ξ => by simpa using hder 0 (Nat.zero_le _) ξ)
    (fun ξ => by
      have h := hder 2 hD ξ
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      linarith) w
  refine hk.trans (le_of_eq ?_)
  have e1 : (2 : ℝ) ^ (-s) = ((2 : ℝ) ^ s)⁻¹ := zpow_neg _ _
  rw [e1, zpow_neg, zpow_ofNat, inv_pow, div_eq_inv_mul]
  ring_nf

theorem Params.Admissible.bounds {𝔭 : Params} (h : 𝔭.Admissible) :
    400 ≤ 𝔭.N ∧ 400 ≤ 𝔭.D ∧ 1 ≤ 𝔭.β ∧ 1 ≤ 𝔭.C := by
  obtain ⟨-, hN, hD, -, -, hβ, -, hC⟩ := h
  exact ⟨classFloor_ge.trans hN, classFloor_ge.trans hD, hβ, hC⟩

/-- Pointwise bound of the vector multiplier by the kernel `R⁻¹ (1 + |x - z|/R)⁻²`. -/
theorem ofReal_yNorm_tmult_le {𝔭 : Params} (h𝔭 : 𝔭.Admissible) {s : ℝ} (hs : 1 ≤ s) {P : ℕ}
    [NeZero P] {sc : ℤ} {c : ℝ} {m : ℝ → ℂ} (hm : InMult 𝔭 sc c m) {F : ℝ → ZMod P → ℂ}
    (hF : Measurable F) (x : ℝ) :
    ENNReal.ofReal (yNorm s (tmult m F x)) ≤ ENNReal.ofReal (3 * 𝔭.β * 𝔭.C) *
      ∫⁻ z, ENNReal.ofReal (((2 : ℝ) ^ sc)⁻¹ * (1 + |x - z| / (2 : ℝ) ^ sc) ^ (-2 : ℤ)) *
        ENNReal.ofReal (yNorm s (F z)) := by
  obtain ⟨-, hD, hβ, hC⟩ := h𝔭.bounds
  have hs0 : 0 < s := by linarith
  set R : ℝ := (2 : ℝ) ^ sc with hRdef
  have hR : 0 < R := zpow_pos (by norm_num) _
  have hconst : 0 < 3 * 𝔭.β * 𝔭.C := by positivity
  set Kf : ℝ → ℂ := 𝓕⁻ m with hKf
  have hcont : Continuous Kf :=
    continuous_fourierInv_of_integrable' (integrable_of_far hm.1.continuous hm.2.1)
  have hk : ∀ w, ‖Kf w‖ ≤ 3 * 𝔭.β * 𝔭.C * (R⁻¹ * (1 + |w| / R) ^ (-2 : ℤ)) :=
    fun w => norm_fourierInv_inMult_le (by omega) (by linarith) hm w
  set kern : ℝ → ℝ := fun z => R⁻¹ * (1 + |x - z| / R) ^ (-2 : ℤ) with hkern
  have hkern_nn : ∀ z, 0 ≤ kern z := fun z => by simp only [hkern]; positivity
  set I : ℝ≥0∞ := ∫⁻ z, ENNReal.ofReal (kern z) * ENNReal.ofReal (yNorm s (F z)) with hI
  by_cases hItop : I = ⊤
  · rw [hItop, ENNReal.mul_top (by simpa using hconst)]
    exact le_top
  have hg_meas : Measurable fun z => yNorm s (F z) := (measurable_yNorm_fun s).comp hF
  have hKmeas : Continuous fun z => Kf (x - z) := hcont.comp (continuous_const.sub continuous_id)
  have hprod_meas : AEStronglyMeasurable (fun z => ‖Kf (x - z)‖ * yNorm s (F z)) volume :=
    (hKmeas.norm.aestronglyMeasurable).mul hg_meas.aestronglyMeasurable
  have hpt : ∀ z, ENNReal.ofReal (‖Kf (x - z)‖ * yNorm s (F z)) ≤
      ENNReal.ofReal (3 * 𝔭.β * 𝔭.C) *
        (ENNReal.ofReal (kern z) * ENNReal.ofReal (yNorm s (F z))) := by
    intro z
    rw [← ENNReal.ofReal_mul (hkern_nn z), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hk (x - z)
    calc ‖Kf (x - z)‖ * yNorm s (F z) ≤ (3 * 𝔭.β * 𝔭.C * kern z) * yNorm s (F z) :=
          mul_le_mul_of_nonneg_right this (yNorm_nonneg' s _)
      _ = _ := by ring
  have hlint : ∫⁻ z, ENNReal.ofReal (‖Kf (x - z)‖ * yNorm s (F z)) ≤
      ENNReal.ofReal (3 * 𝔭.β * 𝔭.C) * I := by
    calc _ ≤ ∫⁻ z, ENNReal.ofReal (3 * 𝔭.β * 𝔭.C) *
          (ENNReal.ofReal (kern z) * ENNReal.ofReal (yNorm s (F z))) := lintegral_mono hpt
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

/-- **V07(a)** pointwise maximal bound (DPLMV e:singlescaleM), with the decay order kept explicit:
`yNorm s (ψ · T_m F)(x) ≤ K ⟨(x - c_I)/|I|⟩^{-N} · M(yNorm s ∘ F)(x)`. -/
theorem norm_singleTile_le (𝔭 : Params) (h𝔭 : 𝔭.Admissible) {s : ℝ} (hs : 1 ≤ s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (P : ℕ) [NeZero P] (sc v : ℤ) (c : ℝ) (ψ m : ℝ → ℂ), InPsi 𝔭 sc v ψ →
      InMult 𝔭 sc c m → ∀ F : ℝ → ZMod P → ℂ, Measurable F → ∀ x,
        ENNReal.ofReal (yNorm s (ψ x • tmult m F x)) ≤
          ENNReal.ofReal (K * jb ((x - dyCentre sc v) / (2 : ℝ) ^ sc) ^ (-(𝔭.N : ℝ))) *
            PrimeCarleson.Proof.Common.maximalHLR (fun z => ENNReal.ofReal (yNorm s (F z))) x := by
  obtain ⟨-, -, hβ, hC⟩ := h𝔭.bounds
  have hs0 : 0 < s := by linarith
  refine ⟨30 * 𝔭.β * 𝔭.C ^ 2, by positivity, ?_⟩
  intro P _ sc v c ψ m hψ hm F hF x
  have hA := ofReal_yNorm_tmult_le h𝔭 hs hm hF x
  have hR : (0 : ℝ) < (2 : ℝ) ^ sc := zpow_pos (by norm_num) _
  have hW : Measurable fun z => ENNReal.ofReal (yNorm s (F z)) :=
    ENNReal.measurable_ofReal.comp ((measurable_yNorm_fun s).comp hF)
  have hHLR := PrimeBHT.TimeFrequency.Tile.lintegral_kernel_le_maximalHLR hR x hW
  set t := (x - dyCentre sc v) / (2 : ℝ) ^ sc with ht
  have hjb : 0 < jb t := jb_pos t
  have hnorm : yNorm s (ψ x • tmult m F x) = ‖ψ x‖ * yNorm s (tmult m F x) :=
    yNorm_fun_const_mul hs0 (ψ x) (tmult m F x)
  have hB : ENNReal.ofReal (yNorm s (tmult m F x)) ≤ ENNReal.ofReal (3 * 𝔭.β * 𝔭.C) *
      (10 * PrimeCarleson.Proof.Common.maximalHLR (fun z => ENNReal.ofReal (yNorm s (F z))) x) :=
    hA.trans (by gcongr)
  have e : ENNReal.ofReal (30 * 𝔭.β * 𝔭.C ^ 2 * jb t ^ (-(𝔭.N : ℝ))) =
      ENNReal.ofReal (𝔭.C * jb t ^ (-(𝔭.N : ℝ))) * (ENNReal.ofReal (3 * 𝔭.β * 𝔭.C) * 10) := by
    rw [← ENNReal.ofReal_ofNat 10, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by have := Real.rpow_nonneg hjb.le (-(𝔭.N : ℝ)); positivity)]
    congr 1; ring
  calc ENNReal.ofReal (yNorm s (ψ x • tmult m F x))
      = ENNReal.ofReal ‖ψ x‖ * ENNReal.ofReal (yNorm s (tmult m F x)) := by
        rw [hnorm, ENNReal.ofReal_mul (norm_nonneg _)]
    _ ≤ ENNReal.ofReal (𝔭.C * jb t ^ (-(𝔭.N : ℝ))) * (ENNReal.ofReal (3 * 𝔭.β * 𝔭.C) *
          (10 * PrimeCarleson.Proof.Common.maximalHLR (fun z => ENNReal.ofReal (yNorm s (F z))) x)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (hψ.2.1 x)) hB
    _ = _ := by rw [e]; ring


/-! ### `treeOp_locPoly` -/


/-- `m_b = (2πi)^{-b} m^{(b)}`, whose kernel is `(-w)^b 𝓕⁻ m (w)` (Taylor expansion of the convolution). -/
def dmult (b : ℕ) (m : ℝ → ℂ) : ℝ → ℂ := fun ξ => ((2 * π * Complex.I)⁻¹) ^ b * iteratedDeriv b m ξ

theorem contDiff_dmult {n : ℝ → ℂ} (hn : ContDiff ℝ ∞ n) (b : ℕ) : ContDiff ℝ ∞ (dmult b n) := by
  have h : ContDiff ℝ ∞ (iteratedDeriv b n) := by
    rw [iteratedDeriv_eq_iterate]; exact ContDiff.iterate_deriv b hn
  exact contDiff_const.mul h

theorem dmult_eq_zero_of_far {n : ℝ → ℂ} {c r : ℝ} (hsupp : ∀ ξ, r < |ξ - c| → n ξ = 0) (b : ℕ)
    {ξ : ℝ} (hξ : r < |ξ - c|) : dmult b n ξ = 0 := by
  simp [dmult, iteratedDeriv_eq_zero_of_far hsupp b hξ]

theorem integrable_fourierInv_of_smooth {n : ℝ → ℂ} {c r : ℝ} (hn : ContDiff ℝ ∞ n)
    (hsupp : ∀ ξ, r < |ξ - c| → n ξ = 0) : Integrable (𝓕⁻ n) := by
  let S : 𝓢(ℝ, ℂ) := (hasCompactSupport_of_far hsupp).toSchwartzMap hn
  have h1 : Integrable (⇑(𝓕⁻ S : 𝓢(ℝ, ℂ))) := (𝓕⁻ S : 𝓢(ℝ, ℂ)).integrable
  have h2 : (⇑(𝓕⁻ S : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = 𝓕⁻ n := SchwartzMap.fourierInv_coe S
  rwa [h2] at h1

theorem fourierInv_iteratedDeriv {n : ℝ → ℂ} {c r : ℝ} (hn : ContDiff ℝ ∞ n)
    (hsupp : ∀ ξ, r < |ξ - c| → n ξ = 0) (b : ℕ) (w : ℝ) :
    𝓕⁻ (iteratedDeriv b n) w = (-2 * π * Complex.I * w) ^ b * 𝓕⁻ n w := by
  have hint : ∀ k : ℕ, (k : ℕ∞) ≤ (b : ℕ∞) → Integrable (iteratedDeriv k n) := fun k _ =>
    integrable_of_far (hn.continuous_iteratedDeriv k (by exact_mod_cast le_top))
      (fun ξ hξ => iteratedDeriv_eq_zero_of_far hsupp k hξ)
  have h := Real.fourier_iteratedDeriv (N := (b : ℕ∞)) (n := b) (f := n)
    (hn.of_le (by exact_mod_cast le_top)) hint le_rfl
  rw [Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg, h]
  simp only [smul_eq_mul]
  congr 1
  push_cast
  ring

theorem fourierInv_dmult {n : ℝ → ℂ} {c r : ℝ} (hn : ContDiff ℝ ∞ n)
    (hsupp : ∀ ξ, r < |ξ - c| → n ξ = 0) (b : ℕ) (w : ℝ) :
    𝓕⁻ (dmult b n) w = ((-w : ℝ) : ℂ) ^ b * 𝓕⁻ n w := by
  have h1 : 𝓕⁻ (dmult b n) w = ((2 * π * Complex.I)⁻¹) ^ b * 𝓕⁻ (iteratedDeriv b n) w := by
    rw [Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg]
    exact fourier_const_mul' _ _ _
  rw [h1, fourierInv_iteratedDeriv hn hsupp, ← mul_assoc, ← mul_pow]
  have hne : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    simp [this]
  congr 2
  push_cast
  field_simp

/-- The Taylor coefficients of `p_W` at `x`: `p_W(z) = Σ_b locCoef W x b (z - x)^b`. -/
def locCoef (W : ℤ × ℤ) (x : ℝ) (b : ℕ) : ℝ :=
  (if b = 0 then 1 else 0) + (((2 : ℝ) ^ W.1)⁻¹) ^ locLoss *
    ((x - dyCentre W.1 W.2) ^ (locLoss - b) * (Nat.choose locLoss b : ℝ))

theorem locPoly_taylor (W : ℤ × ℤ) (x z : ℝ) :
    locPoly W z = ∑ b ∈ Finset.range (locLoss + 1), locCoef W x b * (z - x) ^ b := by
  set L : ℝ := (2 : ℝ) ^ W.1 with hL
  set c : ℝ := dyCentre W.1 W.2 with hc
  have h1 : ((z - c) / L) ^ locLoss = ∑ b ∈ Finset.range (locLoss + 1),
      (L⁻¹) ^ locLoss * ((x - c) ^ (locLoss - b) * (Nat.choose locLoss b : ℝ)) * (z - x) ^ b := by
    have : z - c = (z - x) + (x - c) := by ring
    rw [div_eq_inv_mul, mul_pow, this, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have h2 : (1 : ℝ) = ∑ b ∈ Finset.range (locLoss + 1), (if b = 0 then (1 : ℝ) else 0) * (z - x) ^ b := by
    simp [Finset.sum_ite_eq']
  unfold locPoly
  rw [← hL, ← hc, h1]
  conv_lhs => rw [h2]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold locCoef
  ring

theorem tmult_const_mul {P : ℕ} (c : ℂ) (n : ℝ → ℂ) (g : ℝ → ZMod P → ℂ) (x : ℝ) :
    tmult (fun ξ => c * n ξ) g x = c • tmult n g x := by
  funext y
  simp only [tmult, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [Real.fourierInv_eq_fourier_neg, fourier_const_mul', ← Real.fourierInv_eq_fourier_neg]
  ring

theorem tmult_locPoly_expand {n : ℝ → ℂ} {c r : ℝ} (hn : ContDiff ℝ ∞ n)
    (hsupp : ∀ ξ, r < |ξ - c| → n ξ = 0) (W : ℤ × ℤ) {P : ℕ} [NeZero P] (g : ℝ → ZMod P → ℂ)
    (hg : Measurable g) (B : ℝ) (hB : ∀ x, yNorm 2 (g x) ≤ B) (x : ℝ) :
    tmult n (fun z => ((locPoly W z : ℝ) : ℂ) • g z) x =
      ∑ b ∈ Finset.range (locLoss + 1), ((locCoef W x b : ℝ) : ℂ) • tmult (dmult b n) g x := by
  funext y
  obtain ⟨C0, hC0⟩ : ∃ C, ∀ z, ‖g z y‖ ≤ C := by
    refine ⟨(P : ℝ) ^ (2 : ℝ)⁻¹ * B, fun z => ?_⟩
    refine (norm_apply_le_rpow_mul_yNorm (s := 2) (by norm_num) (g z) y).trans ?_
    exact mul_le_mul_of_nonneg_left (hB z) (by positivity)
  have hgy : Measurable fun z => g z y := (measurable_pi_apply y).comp hg
  have hKint : ∀ b, Integrable (fun z => 𝓕⁻ (dmult b n) (x - z) * g z y) := by
    intro b
    have hI : Integrable (𝓕⁻ (dmult b n)) :=
      integrable_fourierInv_of_smooth (contDiff_dmult hn b)
        (fun ξ hξ => dmult_eq_zero_of_far hsupp b hξ)
    have hI' : Integrable (fun z => 𝓕⁻ (dmult b n) (x - z)) := hI.comp_sub_left x
    exact hI'.mul_bdd hgy.aestronglyMeasurable (Eventually.of_forall hC0)
  have hpt : ∀ z, 𝓕⁻ n (x - z) * (((locPoly W z : ℝ) : ℂ) * g z y) =
      ∑ b ∈ Finset.range (locLoss + 1),
        ((locCoef W x b : ℝ) : ℂ) * (𝓕⁻ (dmult b n) (x - z) * g z y) := by
    intro z
    have h1 : ((locPoly W z : ℝ) : ℂ) =
        ∑ b ∈ Finset.range (locLoss + 1), ((locCoef W x b : ℝ) : ℂ) * ((z - x : ℝ) : ℂ) ^ b := by
      rw [locPoly_taylor W x z]; push_cast; rfl
    rw [h1, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [fourierInv_dmult hn hsupp b (x - z)]
    have : -(x - z) = z - x := by ring
    rw [this]
    ring
  simp only [tmult, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun b _ => (hKint b).const_mul _)]
  simp only [integral_const_mul]

/-- Elementary estimate on the Taylor coefficients of `p_W` for a tile interval inside `W`. -/
theorem locCoef_mul_pow_le {W : ℤ × ℤ} {s v : ℤ} (hQ : dyadicInt s v ⊆ dyadicInt W.1 W.2) (x : ℝ)
    {b : ℕ} (hb : b ≤ locLoss) :
    |locCoef W x b| * ((2 : ℝ) ^ s) ^ b ≤
      (1 + 2 ^ locLoss) * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ locLoss := by
  set ℓ : ℝ := (2 : ℝ) ^ s with hℓdef
  set L : ℝ := (2 : ℝ) ^ W.1 with hLdef
  have hℓ : 0 < ℓ := zpow_pos (by norm_num) _
  have hL : 0 < L := zpow_pos (by norm_num) _
  have hℓL : ℓ ≤ L := zpow_le_zpow_right₀ (by norm_num) (scale_le_of_dyadicInt_subset hQ)
  have hmem : dyCentre s v ∈ dyadicInt s v := by
    refine ⟨?_, ?_⟩
    · unfold dyCentre; rw [← hℓdef]; nlinarith
    · unfold dyCentre; rw [← hℓdef]; nlinarith
  have hcQ := hQ hmem
  obtain ⟨hc1, hc2⟩ := hcQ
  rw [← hLdef] at hc1 hc2
  set cQ := dyCentre s v with hcQdef
  set cW := dyCentre W.1 W.2 with hcWdef
  have hcW : cW = L * ((W.2 : ℝ) + 1 / 2) := by rw [hcWdef]; unfold dyCentre; rw [← hLdef]
  set t := (x - cQ) / ℓ with htdef
  have hjb1 : 1 ≤ jb t := one_le_jb t
  have hxQ : |x - cQ| = ℓ * |t| := by
    rw [htdef, abs_div, abs_of_pos hℓ]; field_simp
  have hcc : |cQ - cW| ≤ L / 2 := by
    rw [abs_le]; constructor <;> nlinarith
  have hxW : |x - cW| ≤ L * jb t := by
    have h1 : |x - cW| ≤ |x - cQ| + |cQ - cW| := by
      have := abs_sub_le x cQ cW; linarith
    unfold jb
    nlinarith [abs_nonneg t, mul_le_mul_of_nonneg_right hℓL (abs_nonneg t)]
  have hN : (0 : ℕ) ≤ locLoss := Nat.zero_le _
  -- the second summand
  have h2 : (L⁻¹) ^ locLoss * (|x - cW| ^ (locLoss - b) * (Nat.choose locLoss b : ℝ)) * ℓ ^ b ≤
      2 ^ locLoss * jb t ^ locLoss := by
    have hpow : |x - cW| ^ (locLoss - b) ≤ (L * jb t) ^ (locLoss - b) :=
      pow_le_pow_left₀ (abs_nonneg _) hxW _
    have hch : (Nat.choose locLoss b : ℝ) ≤ 2 ^ locLoss := by exact_mod_cast Nat.choose_le_two_pow locLoss b
    have hjbN : jb t ^ (locLoss - b) ≤ jb t ^ locLoss := pow_le_pow_right₀ hjb1 (Nat.sub_le _ _)
    have hLpow : (L⁻¹) ^ locLoss * L ^ (locLoss - b) = (L⁻¹) ^ b := by
      obtain ⟨k, hk⟩ : ∃ k, locLoss = k + b := ⟨locLoss - b, by omega⟩
      have hk' : locLoss - b = k := by omega
      rw [hk', hk]
      have h1 : (L⁻¹) ^ k * L ^ k = 1 := by rw [← mul_pow, inv_mul_cancel₀ hL.ne', one_pow]
      calc (L⁻¹) ^ (k + b) * L ^ k = (L⁻¹) ^ b * ((L⁻¹) ^ k * L ^ k) := by ring
        _ = _ := by rw [h1, mul_one]
    have hratio : (L⁻¹) ^ b * ℓ ^ b ≤ 1 := by
      rw [← mul_pow]
      exact pow_le_one₀ (by positivity) (by rw [inv_mul_le_iff₀ hL]; linarith)
    calc (L⁻¹) ^ locLoss * (|x - cW| ^ (locLoss - b) * (Nat.choose locLoss b : ℝ)) * ℓ ^ b
        ≤ (L⁻¹) ^ locLoss * ((L * jb t) ^ (locLoss - b) * 2 ^ locLoss) * ℓ ^ b := by gcongr
      _ = ((L⁻¹) ^ locLoss * L ^ (locLoss - b)) * ℓ ^ b * (jb t ^ (locLoss - b) * 2 ^ locLoss) := by
          rw [mul_pow]; ring
      _ = ((L⁻¹) ^ b * ℓ ^ b) * (jb t ^ (locLoss - b) * 2 ^ locLoss) := by rw [hLpow]
      _ ≤ 1 * (jb t ^ locLoss * 2 ^ locLoss) := by gcongr
      _ = 2 ^ locLoss * jb t ^ locLoss := by ring
  have h1 : |(if b = 0 then (1 : ℝ) else 0)| * ℓ ^ b ≤ jb t ^ locLoss := by
    split_ifs with hb0
    · subst hb0; simp only [abs_one, pow_zero, mul_one]; exact one_le_pow₀ hjb1
    · simp; positivity
  calc |locCoef W x b| * ℓ ^ b
      ≤ (|(if b = 0 then (1 : ℝ) else 0)| + |(L⁻¹) ^ locLoss *
          ((x - cW) ^ (locLoss - b) * (Nat.choose locLoss b : ℝ))|) * ℓ ^ b := by
        unfold locCoef
        gcongr
        exact abs_add_le _ _
    _ = |(if b = 0 then (1 : ℝ) else 0)| * ℓ ^ b + (L⁻¹) ^ locLoss *
          (|x - cW| ^ (locLoss - b) * (Nat.choose locLoss b : ℝ)) * ℓ ^ b := by
        rw [add_mul]
        congr 1
        rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_pos (inv_pos.2 hL), Nat.abs_cast]
    _ ≤ jb t ^ locLoss + 2 ^ locLoss * jb t ^ locLoss := add_le_add h1 h2
    _ = _ := by ring

/-- The constant `K = 1 + 2^{locLoss}` of `treeOp_locPoly`. -/
def locK : ℝ := 1 + 2 ^ locLoss

theorem locK_pos : 0 < locK := by unfold locK; positivity

theorem inMult_loc {𝔭 : Params} (hD : locLoss ≤ 𝔭.D) {s : ℤ} {c : ℝ} {m : ℝ → ℂ}
    (hm : InMult 𝔭 s c m) {b : ℕ} (hb : b ≤ locLoss) :
    InMult 𝔭.loc s c (fun ξ => ((((2 : ℝ) ^ (-s)) ^ b : ℝ) : ℂ) * dmult b m ξ) := by
  obtain ⟨hsm, hsupp, hder⟩ := hm
  refine ⟨contDiff_const.mul (contDiff_dmult hsm b), ?_, ?_⟩
  · intro ξ hξ
    simp only [Params.loc_β] at hξ
    show _ * dmult b m ξ = 0
    rw [dmult_eq_zero_of_far hsupp b hξ, mul_zero]
  · intro a ha ξ
    have hab : a + b ≤ 𝔭.D := by simp only [Params.loc_D] at ha; omega
    have e : iteratedDeriv a (fun ξ => ((((2 : ℝ) ^ (-s)) ^ b : ℝ) : ℂ) * dmult b m ξ) ξ =
        (((((2 : ℝ) ^ (-s)) ^ b : ℝ) : ℂ) * ((2 * π * Complex.I)⁻¹) ^ b) *
          iteratedDeriv (a + b) m ξ := by
      have h1 : (fun ξ => ((((2 : ℝ) ^ (-s)) ^ b : ℝ) : ℂ) * dmult b m ξ) =
          fun ξ => ((((((2 : ℝ) ^ (-s)) ^ b : ℝ) : ℂ) * ((2 * π * Complex.I)⁻¹) ^ b) •
            iteratedDeriv b m ξ) := by
        ext ξ; simp only [dmult, smul_eq_mul]; ring
      rw [h1, iteratedDeriv_fun_const_smul_field, smul_eq_mul]
      congr 1
      simp only [iteratedDeriv_eq_iterate]
      rw [← Function.iterate_add_apply]
    have hl : (0 : ℝ) < (2 : ℝ) ^ (-s) := zpow_pos (by norm_num) _
    have hn : ‖((((2 : ℝ) ^ (-s)) ^ b : ℝ) : ℂ) * ((2 * π * Complex.I)⁻¹) ^ b‖ ≤
        ((2 : ℝ) ^ (-s)) ^ b := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos hl b), norm_pow,
        norm_inv]
      have h2 : (1 : ℝ) ≤ ‖2 * (π : ℂ) * Complex.I‖ := by
        simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_one,
          Complex.norm_ofNat, abs_of_pos Real.pi_pos]
        have := Real.pi_gt_three
        linarith
      have h3 : ‖2 * (π : ℂ) * Complex.I‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2
      have h4 : (‖2 * (π : ℂ) * Complex.I‖⁻¹) ^ b ≤ 1 := pow_le_one₀ (by positivity) h3
      calc ((2 : ℝ) ^ (-s)) ^ b * (‖2 * (π : ℂ) * Complex.I‖⁻¹) ^ b ≤ ((2 : ℝ) ^ (-s)) ^ b * 1 :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = _ := mul_one _
    simp only [Params.loc_C]
    rw [e, norm_mul]
    calc ((2 : ℝ) ^ (-s)) ^ a * (‖((((2 : ℝ) ^ (-s)) ^ b : ℝ) : ℂ) * ((2 * π * Complex.I)⁻¹) ^ b‖ *
          ‖iteratedDeriv (a + b) m ξ‖)
        ≤ ((2 : ℝ) ^ (-s)) ^ a * (((2 : ℝ) ^ (-s)) ^ b * ‖iteratedDeriv (a + b) m ξ‖) := by
          gcongr
      _ = ((2 : ℝ) ^ (-s)) ^ (a + b) * ‖iteratedDeriv (a + b) m ξ‖ := by rw [pow_add]; ring
      _ ≤ 𝔭.C := hder (a + b) hab ξ

theorem inPsi_loc {𝔭 : Params} (h𝔭 : 𝔭.loc.Admissible) {W : ℤ × ℤ} {s v : ℤ}
    (hQ : dyadicInt s v ⊆ dyadicInt W.1 W.2) {ψ : ℝ → ℂ} (hψ : InPsi 𝔭 s v ψ) {b : ℕ}
    (hb : b ≤ locLoss) :
    InPsi 𝔭.loc s v (fun x => ((locK⁻¹ * locCoef W x b * ((2 : ℝ) ^ s) ^ b : ℝ) : ℂ) * ψ x) := by
  obtain ⟨hψc, hψb, hψF⟩ := hψ
  have hN : 500 ≤ 𝔭.N := by
    have := h𝔭.2.1
    simp only [Params.loc_N, classFloor, locLoss] at this
    omega
  have hNR : (500 : ℝ) ≤ 𝔭.N := by exact_mod_cast hN
  have hL : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  refine ⟨?_, ?_, ?_⟩
  · refine Complex.continuous_ofReal.comp ?_ |>.mul hψc
    unfold locCoef
    fun_prop
  · intro x
    simp only [Params.loc_C, Params.loc_N]
    set t := (x - dyCentre s v) / (2 : ℝ) ^ s with ht
    have hjb : 0 < jb t := jb_pos t
    have hc := locCoef_mul_pow_le hQ x hb
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hℓb : 0 < ((2 : ℝ) ^ s) ^ b := pow_pos hL b
    have habs : |locK⁻¹ * locCoef W x b * ((2 : ℝ) ^ s) ^ b| ≤ jb t ^ locLoss := by
      rw [abs_mul, abs_mul, abs_of_pos (inv_pos.2 locK_pos), abs_of_pos hℓb]
      calc locK⁻¹ * |locCoef W x b| * ((2 : ℝ) ^ s) ^ b
          = locK⁻¹ * (|locCoef W x b| * ((2 : ℝ) ^ s) ^ b) := by ring
        _ ≤ locK⁻¹ * (locK * jb t ^ locLoss) :=
            mul_le_mul_of_nonneg_left (by unfold locK; exact hc) (inv_nonneg.2 locK_pos.le)
        _ = jb t ^ locLoss := by field_simp [locK_pos.ne']
    have hexp : jb t ^ locLoss * jb t ^ (-(𝔭.N : ℝ)) = jb t ^ (-((𝔭.N - locLoss : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hjb]
      congr 1
      rw [Nat.cast_sub (by simp only [locLoss]; omega)]
      ring
    calc |locK⁻¹ * locCoef W x b * ((2 : ℝ) ^ s) ^ b| * ‖ψ x‖
        ≤ jb t ^ locLoss * (𝔭.C * jb t ^ (-(𝔭.N : ℝ))) :=
          mul_le_mul habs (hψb x) (norm_nonneg _) (by positivity)
      _ = 𝔭.C * (jb t ^ locLoss * jb t ^ (-(𝔭.N : ℝ))) := by ring
      _ = _ := by rw [hexp]
  · intro ξ hξ
    simp only [Params.loc_δ] at hξ
    set ℓ : ℝ := (2 : ℝ) ^ s with hℓ
    have e : (fun x => ((locK⁻¹ * locCoef W x b * ℓ ^ b : ℝ) : ℂ) * ψ x) = fun x =>
        ((locK⁻¹ * ((if b = 0 then (1 : ℝ) else 0) * ℓ ^ b) : ℝ) : ℂ) * ψ x +
        ((locK⁻¹ * ((((2 : ℝ) ^ W.1)⁻¹) ^ locLoss * (Nat.choose locLoss b : ℝ) * ℓ ^ b) : ℝ) : ℂ) *
          ((((x - dyCentre W.1 W.2) ^ (locLoss - b) : ℝ) : ℂ) * ψ x) := by
      ext x
      unfold locCoef
      push_cast
      ring
    have hψi : Integrable ψ := by
      have := integrable_pow_mul_jb (c := dyCentre s v) (a := 0) hL (N := (𝔭.N : ℝ)) 0
        (by push_cast; linarith) hψc hψb
      simpa using this
    have hk : ((locLoss - b : ℕ) : ℝ) + 1 < (𝔭.N : ℝ) := by
      have h1 : locLoss - b ≤ 100 := by simp only [locLoss]; omega
      have h2 : ((locLoss - b : ℕ) : ℝ) ≤ 100 := by exact_mod_cast h1
      linarith
    have hfi : Integrable
        (fun x : ℝ => (((x - dyCentre W.1 W.2) ^ (locLoss - b) : ℝ) : ℂ) * ψ x) :=
      integrable_pow_mul_jb (c := dyCentre s v) hL (locLoss - b) hk hψc hψb
    rw [e, fourier_add' (hψi.const_mul _) (hfi.const_mul _), fourier_const_mul', fourier_const_mul',
      hψF ξ hξ, fourier_pow_mul_eq_zero hL hψc hψb hψF (dyCentre W.1 W.2) (locLoss - b) hk ξ hξ]
    simp

/-- **V07(loc)**, the input of B6' (route check (M2)), polynomial version: for `I_Q ⊆ W` for all
`Q ∈ Tr`, the tree operator applied to `p_W · g` is a sum of `locLoss + 1` tree operators of the
class `𝔭.loc`, times a constant `K(𝔭)`.  Proof: `T_m(p g)(x) = Σ_{b ≤ 100} p^{(b)}(x)/b! · T_{m_b} g(x)`,
`m_b ∝ ∂^b m` (exact Taylor identity for a polynomial), and `ψ_Q |I_Q|^b p_W^{(b)} / b! ∈ Ψ_{I_Q}` with
decay `N - 100` and the SAME Fourier support (multiplying by a polynomial does not move `supp 𝓕ψ`). -/
theorem treeOp_locPoly (𝔭 : Params) (h𝔭 : 𝔭.loc.Admissible) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (P : ℕ) [NeZero P] (k : Fin 3) (Tr : Finset TriTile) (ψ m : TriTile → ℝ → ℂ),
      IsTreeOpData 𝔭 k Tr ψ m → ∀ W : ℤ × ℤ, (∀ Q ∈ Tr, Q.I ⊆ dyadicInt W.1 W.2) →
        ∃ ψ' m' : Fin (locLoss + 1) → TriTile → ℝ → ℂ,
          (∀ b, IsTreeOpData 𝔭.loc k Tr (ψ' b) (m' b)) ∧
          ∀ g : ℝ → ZMod P → ℂ, Measurable g → (∃ B, ∀ x, yNorm 2 (g x) ≤ B) → ∀ x,
            treeOp Tr ψ m (fun z => ((locPoly W z : ℝ) : ℂ) • g z) x =
              (K : ℂ) • ∑ b, treeOp Tr (ψ' b) (m' b) g x := by
  refine ⟨locK, locK_pos.le, ?_⟩
  intro P _ k Tr ψ m hdata W hW
  obtain ⟨hdata1, hdata2⟩ := hdata
  have hD : locLoss ≤ 𝔭.D := by
    have := h𝔭.2.2.1
    simp only [Params.loc_D, classFloor, locLoss] at this ⊢
    omega
  refine ⟨fun b Q x => ((locK⁻¹ * locCoef W x b * ((2 : ℝ) ^ Q.box.scale) ^ (b : ℕ) : ℝ) : ℂ) * ψ Q x,
    fun b Q ξ => ((((2 : ℝ) ^ (-Q.box.scale)) ^ (b : ℕ) : ℝ) : ℂ) * dmult b (m Q) ξ, ?_, ?_⟩
  · intro b
    have hb : (b : ℕ) ≤ locLoss := Nat.lt_succ_iff.1 b.2
    refine ⟨fun Q hQ => ⟨inPsi_loc h𝔭 (hW Q hQ) (hdata1 Q hQ).1 hb,
      inMult_loc hD (hdata1 Q hQ).2 hb⟩, ?_⟩
    intro Q hQ Q' hQ' hbox
    have hm := hdata2 Q hQ Q' hQ' hbox
    funext ξ
    simp only [hm, hbox]
  · intro g hg hB x
    obtain ⟨B, hB⟩ := hB
    have hexp : ∀ Q ∈ Tr, tmult (m Q) (fun z => ((locPoly W z : ℝ) : ℂ) • g z) x =
        ∑ b ∈ Finset.range (locLoss + 1), ((locCoef W x b : ℝ) : ℂ) • tmult (dmult b (m Q)) g x :=
      fun Q hQ => tmult_locPoly_expand (hdata1 Q hQ).2.1 (hdata1 Q hQ).2.2.1 W g hg B hB x
    have hterm : ∀ Q ∈ Tr, ∀ b : ℕ,
        (locK : ℂ) • ((((locK⁻¹ * locCoef W x b * ((2 : ℝ) ^ Q.box.scale) ^ b : ℝ) : ℂ) * ψ Q x) •
          tmult (fun ξ => ((((2 : ℝ) ^ (-Q.box.scale)) ^ b : ℝ) : ℂ) * dmult b (m Q) ξ) g x) =
        (ψ Q x * ((locCoef W x b : ℝ) : ℂ)) • tmult (dmult b (m Q)) g x := by
      intro Q hQ b
      rw [tmult_const_mul, smul_smul, smul_smul]
      congr 1
      have hℓ : (2 : ℝ) ^ (-Q.box.scale) = ((2 : ℝ) ^ Q.box.scale)⁻¹ := zpow_neg _ _
      have hpos : (0 : ℝ) < (2 : ℝ) ^ Q.box.scale := zpow_pos (by norm_num) _
      have hK : (locK : ℂ) ≠ 0 := by exact_mod_cast locK_pos.ne'
      have hpos' : (2 : ℂ) ^ Q.box.scale ≠ 0 := zpow_ne_zero _ (by norm_num)
      rw [hℓ]
      push_cast
      field_simp
      rw [one_div, inv_pow]
      have h2 : ((2 : ℂ) ^ Q.box.scale) ^ b ≠ 0 := pow_ne_zero _ hpos'
      calc _ = ((locCoef W x b : ℝ) : ℂ) * ψ Q x *
            (((2 : ℂ) ^ Q.box.scale) ^ b * (((2 : ℂ) ^ Q.box.scale) ^ b)⁻¹) := by ring
        _ = _ := by rw [mul_inv_cancel₀ h2, mul_one]
    unfold treeOp
    rw [Finset.smul_sum]
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    rw [hexp Q hQ, Finset.smul_sum]
    rw [Fin.sum_univ_eq_sum_range (fun n => (locK : ℂ) •
      ((((locK⁻¹ * locCoef W x n * ((2 : ℝ) ^ Q.box.scale) ^ n : ℝ) : ℂ) * ψ Q x) •
        tmult (fun ξ => ((((2 : ℝ) ^ (-Q.box.scale)) ^ n : ℝ) : ℂ) * dmult n (m Q) ξ) g x))
      (locLoss + 1)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hterm Q hQ b, smul_smul]


end PrimeBHT.TimeFrequency.X2
