module

public import PrimeBHT.TimeFrequency.X2.Classes
public import PrimeBHT.TimeFrequency.X2.ClassKernel
public import PrimeBHT.TimeFrequency.X2.ClassLemmas
public import PrimeBHT.TimeFrequency.Tile.Gram.Pair
import Mathlib.Analysis.Convolution

/-!
# X2, node V10: scalar Fourier analysis of the tile pieces `g = ψ · (𝓕⁻m * f)`

For a bounded measurable `f`, `ψ ∈ Ψ_I(𝔭)`, `m ∈ M_ω(𝔭)` (`l = 2^{-s}` the length of `ω`, centre `c`):

* `g = ψ · tm m f` is integrable and continuous (`integrable_gfun`, `continuous_gfun`);
* `𝓕 g` vanishes outside `[c - (β/2 + δ) l, c + (β/2 + δ) l]` (`fourier_gfun_eq_zero`: Fubini and the
  definition of `𝓕⁻ m`);
* hence two such pieces with `3ω ∩ 3ω' = ∅` are orthogonal in `L²(ℝ)` (`gfun_orthogonal`, from the X1 lemma
  `pairing_eq_zero_of_fourier_Icc`), provided `β + 2 δ ≤ 3`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform ComplexConjugate ContDiff Real
open PrimeBHT.TimeFrequency.Tile PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- Scalar multiplier operator `T_m f = 𝓕⁻ m * f` (the `y`-coordinate of `tmult`). -/
def tm (m : ℝ → ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ := ∫ z, 𝓕⁻ m (x - z) * f z

theorem tmult_apply_eq_tm {P : ℕ} (m : ℝ → ℂ) (F : ℝ → ZMod P → ℂ) (x : ℝ) (y : ZMod P) :
    tmult m F x y = tm m (fun z => F z y) x := rfl

section Kernel

variable {𝔭 : Params} {s : ℤ} {c : ℝ} {m : ℝ → ℂ}

theorem integrable_fourierInv_inMult (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hm : InMult 𝔭 s c m) :
    Integrable (𝓕⁻ m) := by
  have hcont : Continuous (𝓕⁻ m) :=
    continuous_fourierInv_of_integrable' (integrable_of_far hm.1.continuous hm.2.1)
  have hL : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  have hC : 0 ≤ 𝔭.C := by
    have := hm.2.2 0 (Nat.zero_le _) 0
    simp only [pow_zero, one_mul, iteratedDeriv_zero] at this
    exact (norm_nonneg _).trans this
  have hint : Integrable (fun w : ℝ => 3 * 𝔭.β * 𝔭.C * (((2 : ℝ) ^ s)⁻¹ *
      (1 + |w - 0| / (2 : ℝ) ^ s) ^ (-(2 : ℝ)))) :=
    (integrable_one_add_abs_sub_div_rpow (p := 2) (by norm_num) 0 hL).const_mul _ |>.const_mul _
  refine hint.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun w => ?_)
  refine (norm_fourierInv_inMult_le hD hβ hm w).trans (le_of_eq ?_)
  rw [sub_zero]
  congr 2
  rw [← Real.rpow_intCast]; norm_num

theorem norm_tm_le (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hm : InMult 𝔭 s c m) {f : ℝ → ℂ} {B : ℝ}
    (hB : ∀ z, ‖f z‖ ≤ B) (x : ℝ) : ‖tm m f x‖ ≤ B * ∫ w, ‖𝓕⁻ m w‖ := by
  have hK := integrable_fourierInv_inMult hD hβ hm
  unfold tm
  refine (norm_integral_le_integral_norm _).trans ?_
  have h1 : ∫ z, ‖𝓕⁻ m (x - z) * f z‖ ≤ ∫ z, ‖𝓕⁻ m (x - z)‖ * B := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun z => norm_nonneg _) ?_
      (Eventually.of_forall fun z => ?_)
    · exact (hK.norm.comp_sub_left x).mul_const B
    · dsimp only; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB z) (norm_nonneg _)
  refine h1.trans (le_of_eq ?_)
  rw [integral_mul_const, integral_sub_left_eq_self (fun w => ‖𝓕⁻ m w‖) volume x, mul_comm]

theorem continuous_tm (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hm : InMult 𝔭 s c m) {f : ℝ → ℂ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) : Continuous (tm m f) := by
  have hK := integrable_fourierInv_inMult hD hβ hm
  have hKc : Continuous (𝓕⁻ m) :=
    continuous_fourierInv_of_integrable' (integrable_of_far hm.1.continuous hm.2.1)
  -- `tm m f x = ∫ w, K w * f (x - w)`; continuity of `x ↦ K w * f(x - w)` fails, so use the form with `K(x - z)`
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have hL : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  set l : ℝ := (2 : ℝ) ^ (-s) with hl
  have hl0 : 0 < l := zpow_pos (by norm_num) _
  -- the dominating function: `‖K(x - z)‖ ≤ A (1 + l|x - z|)^{-2} ≤ A (1 + l)² (1 + l|x₀ - z|)^{-2}` for `|x - x₀| ≤ 1`
  set A : ℝ := 3 * 𝔭.β * 𝔭.C * l with hA
  have hA0 : 0 ≤ A := by
    have hC : 0 ≤ 𝔭.C := by
      have := hm.2.2 0 (Nat.zero_le _) 0
      simp only [pow_zero, one_mul, iteratedDeriv_zero] at this
      exact (norm_nonneg _).trans this
    positivity
  have hdec : ∀ w, ‖𝓕⁻ m w‖ ≤ A * (1 + l * |w|) ^ (-(2 : ℝ)) := by
    intro w
    refine (norm_fourierInv_inMult_le hD hβ hm w).trans (le_of_eq ?_)
    have e1 : ((2 : ℝ) ^ s)⁻¹ = l := by rw [hl, zpow_neg]
    have e2 : |w| / (2 : ℝ) ^ s = l * |w| := by rw [div_eq_mul_inv, mul_comm, e1]
    rw [e2, e1, hA, ← Real.rpow_intCast]; norm_num; ring
  have hbound : Integrable (fun z : ℝ => B * (A * (1 + l) ^ 2 * (1 + l * |x₀ - z|) ^ (-(2 : ℝ)))) := by
    have := (integrable_one_add_abs_sub_div_rpow (p := 2) (by norm_num) x₀ (L := 1 / l) (by positivity))
    refine (this.const_mul (B * (A * (1 + l) ^ 2))).congr (Eventually.of_forall fun z => ?_)
    simp only
    rw [show |z - x₀| / (1 / l) = l * |x₀ - z| by rw [abs_sub_comm]; field_simp]
    ring
  refine continuousAt_of_dominated (bound := fun z => B * (A * (1 + l) ^ 2 * (1 + l * |x₀ - z|) ^ (-(2 : ℝ))))
    (Eventually.of_forall fun x => ?_) ?_ hbound ?_
  · exact (hKc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hf.aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
    refine Eventually.of_forall fun z => ?_
    rw [norm_mul]
    have hx1 : |x - x₀| < 1 := by simpa [Real.dist_eq] using hx
    have h1 : 1 + l * |x₀ - z| ≤ (1 + l) * (1 + l * |x - z|) := by
      have : |x₀ - z| ≤ |x₀ - x| + |x - z| := abs_sub_le x₀ x z
      have h2 : |x₀ - x| ≤ 1 := by rw [abs_sub_comm]; exact hx1.le
      nlinarith [abs_nonneg (x - z), mul_nonneg hl0.le (abs_nonneg (x - z))]
    have h3 : (1 + l * |x - z|) ^ (-(2 : ℝ)) ≤ (1 + l) ^ 2 * (1 + l * |x₀ - z|) ^ (-(2 : ℝ)) := by
      have hpos : 0 < 1 + l * |x - z| := by positivity
      have hpos₀ : 0 < 1 + l * |x₀ - z| := by positivity
      rw [Real.rpow_neg hpos.le, Real.rpow_neg hpos₀.le, Real.rpow_two, Real.rpow_two]
      rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h1, hpos, hpos₀]
    calc ‖𝓕⁻ m (x - z)‖ * ‖f z‖ ≤ (A * (1 + l * |x - z|) ^ (-(2 : ℝ))) * B :=
          mul_le_mul (hdec _) (hB z) (norm_nonneg _) (by positivity)
      _ ≤ (A * ((1 + l) ^ 2 * (1 + l * |x₀ - z|) ^ (-(2 : ℝ)))) * B := by
          have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
          gcongr
      _ = B * (A * (1 + l) ^ 2 * (1 + l * |x₀ - z|) ^ (-(2 : ℝ))) := by ring
  · refine Eventually.of_forall fun z => ?_
    exact (hKc.comp (continuous_id.sub continuous_const)).mul continuous_const |>.continuousAt

end Kernel

section Pieces

variable {𝔭 : Params} {s v : ℤ} {c : ℝ} {ψ m : ℝ → ℂ}

theorem integrable_psi (hN : 2 ≤ 𝔭.N) (hψ : InPsi 𝔭 s v ψ) : Integrable ψ := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  have h1 := (integrable_jb_rpow (c := dyCentre s v) hL (r := (𝔭.N : ℝ)) (by
    have : (2 : ℝ) ≤ 𝔭.N := by exact_mod_cast hN
    linarith)).const_mul 𝔭.C
  exact h1.mono' hψ.1.aestronglyMeasurable (Eventually.of_forall hψ.2.1)

/-- The `x`-Fourier transform of `ψ(x) 𝓕⁻m(x - z)` vanishes away from `ω`. -/
theorem fourier_kernel_piece_eq_zero (hN : 2 ≤ 𝔭.N)
    (hψ : InPsi 𝔭 s v ψ) (hm : InMult 𝔭 s c m) (z ζ : ℝ)
    (hζ : 𝔭.β * (2 : ℝ) ^ (-s) / 2 + 𝔭.δ * (2 : ℝ) ^ (-s) < |ζ - c|) :
    𝓕 (fun x => ψ x * 𝓕⁻ m (x - z)) ζ = 0 := by
  have hψi := integrable_psi hN hψ
  have hmi : Integrable m := integrable_of_far hm.1.continuous hm.2.1
  have hmc : Continuous m := hm.1.continuous
  -- the kernel as an integral
  have hK : ∀ w : ℝ, 𝓕⁻ m w = ∫ ξ, Complex.exp (↑(2 * π * ξ * w) * Complex.I) * m ξ := by
    intro w
    rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [smul_eq_mul]
    congr 3; ring_nf
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [hK, smul_eq_mul, ← integral_const_mul]
  -- Fubini in `(x, ξ)`
  have hint : Integrable (Function.uncurry fun (x ξ : ℝ) => Complex.exp (↑(-2 * π * x * ζ) * Complex.I) *
      (ψ x * (Complex.exp (↑(2 * π * ξ * (x - z)) * Complex.I) * m ξ))) (volume.prod volume) := by
    have hb : Integrable (fun p : ℝ × ℝ => ‖ψ p.1‖ * ‖m p.2‖) (volume.prod volume) :=
      Integrable.mul_prod hψi.norm hmi.norm
    refine hb.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have : Continuous fun p : ℝ × ℝ => Complex.exp (↑(-2 * π * p.1 * ζ) * Complex.I) *
          (ψ p.1 * (Complex.exp (↑(2 * π * p.2 * (p.1 - z)) * Complex.I) * m p.2)) := by
        have := hψ.1
        fun_prop
      exact this.aestronglyMeasurable
    · simp only [Function.uncurry, norm_mul]
      rw [Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]
      ring_nf
      exact le_rfl
  rw [integral_integral_swap hint]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun ξ => ?_)
  simp only [Pi.zero_apply]
  by_cases hmξ : m ξ = 0
  · simp [hmξ]
  · have hξ : |ξ - c| ≤ 𝔭.β * (2 : ℝ) ^ (-s) / 2 := by
      by_contra h
      exact hmξ (hm.2.1 ξ (not_le.1 h))
    have hF : 𝓕 ψ (ζ - ξ) = 0 := by
      refine hψ.2.2 (ζ - ξ) ?_
      have : |ζ - c| ≤ |ζ - ξ| + |ξ - c| := by
        have := abs_add_le (ζ - ξ) (ξ - c); simpa using this
      linarith
    have hpt : ∀ x : ℝ, Complex.exp (↑(-2 * π * x * ζ) * Complex.I) *
        (ψ x * (Complex.exp (↑(2 * π * ξ * (x - z)) * Complex.I) * m ξ)) =
        (Complex.exp (↑(-2 * π * ξ * z) * Complex.I) * m ξ) *
          (Complex.exp (↑(-2 * π * x * (ζ - ξ)) * Complex.I) * ψ x) := by
      intro x
      have : Complex.exp (↑(-2 * π * x * ζ) * Complex.I) * Complex.exp (↑(2 * π * ξ * (x - z)) * Complex.I) =
          Complex.exp (↑(-2 * π * ξ * z) * Complex.I) * Complex.exp (↑(-2 * π * x * (ζ - ξ)) * Complex.I) := by
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast; ring
      calc _ = (Complex.exp (↑(-2 * π * x * ζ) * Complex.I) * Complex.exp (↑(2 * π * ξ * (x - z)) * Complex.I)) *
            (ψ x * m ξ) := by ring
        _ = _ := by rw [this]; ring
    simp_rw [hpt, integral_const_mul]
    have := hF
    rw [Real.fourier_real_eq_integral_exp_smul] at this
    simp only [smul_eq_mul] at this
    rw [this, mul_zero]

/-- The tile piece `g = ψ · (𝓕⁻m * f)`. -/
def gfun (ψ m f : ℝ → ℂ) (x : ℝ) : ℂ := ψ x * tm m f x

theorem integrable_gfun (hN : 2 ≤ 𝔭.N) (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ)
    (hm : InMult 𝔭 s c m) {f : ℝ → ℂ} (hf : Measurable f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) :
    Integrable (gfun ψ m f) := by
  have hc := continuous_tm hD hβ hm hf hB
  have := (integrable_psi hN hψ).bdd_mul (c := B * ∫ w, ‖𝓕⁻ m w‖) hc.aestronglyMeasurable
    (Eventually.of_forall fun x => norm_tm_le hD hβ hm hB x)
  exact this.congr (Eventually.of_forall fun x => by simp [gfun, mul_comm])

theorem continuous_gfun (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ) (hm : InMult 𝔭 s c m)
    {f : ℝ → ℂ} (hf : Measurable f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) : Continuous (gfun ψ m f) :=
  hψ.1.mul (continuous_tm hD hβ hm hf hB)

/-- `𝓕 g` vanishes away from `ω` (radius `β l / 2 + δ l`). -/
theorem fourier_gfun_eq_zero (hN : 2 ≤ 𝔭.N) (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ)
    (hm : InMult 𝔭 s c m) {f : ℝ → ℂ} (hf : Measurable f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) (ζ : ℝ)
    (hζ : 𝔭.β * (2 : ℝ) ^ (-s) / 2 + 𝔭.δ * (2 : ℝ) ^ (-s) < |ζ - c|) :
    𝓕 (gfun ψ m f) ζ = 0 := by
  have hψi := integrable_psi hN hψ
  have hK := integrable_fourierInv_inMult hD hβ hm
  have hKc : Continuous (𝓕⁻ m) :=
    continuous_fourierInv_of_integrable' (integrable_of_far hm.1.continuous hm.2.1)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [gfun, tm, smul_eq_mul]
  simp_rw [← integral_const_mul]
  -- Fubini in `(x, z)`
  have hb' : Integrable (fun p : ℝ × ℝ => ‖ψ p.2‖ * ‖𝓕⁻ m (-(p.1 - p.2))‖) (volume.prod volume) := by
    have := Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) (μ := volume) (ν := volume)
      hψi.norm (hK.norm.comp_neg)
    simpa using this
  have hb := hb'.swap
  have hint : Integrable (Function.uncurry fun (x z : ℝ) => Complex.exp (↑(-2 * π * x * ζ) * Complex.I) *
      (ψ x * (𝓕⁻ m (x - z) * f z))) (volume.prod volume) := by
    refine (hb.const_mul B).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have : Measurable fun p : ℝ × ℝ => Complex.exp (↑(-2 * π * p.1 * ζ) * Complex.I) *
          (ψ p.1 * (𝓕⁻ m (p.1 - p.2) * f p.2)) := by
        have h1 := hψ.1.measurable
        have h2 := hKc.measurable
        fun_prop
      exact this.aestronglyMeasurable
    · simp only [Function.uncurry, norm_mul]
      rw [Complex.norm_exp_ofReal_mul_I]
      simp only [neg_sub, one_mul]
      calc ‖ψ p.1‖ * (‖𝓕⁻ m (p.1 - p.2)‖ * ‖f p.2‖) ≤ ‖ψ p.1‖ * (‖𝓕⁻ m (p.1 - p.2)‖ * B) := by
            gcongr; exact hB _
        _ = B * (‖ψ p.1‖ * ‖𝓕⁻ m (p.1 - p.2)‖) := by ring
  rw [integral_integral_swap hint]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun z => ?_)
  simp only [Pi.zero_apply]
  have hu := fourier_kernel_piece_eq_zero hN hψ hm z ζ hζ
  rw [Real.fourier_real_eq_integral_exp_smul] at hu
  simp only [smul_eq_mul] at hu
  have : ∀ x : ℝ, Complex.exp (↑(-2 * π * x * ζ) * Complex.I) * (ψ x * (𝓕⁻ m (x - z) * f z)) =
      f z * (Complex.exp (↑(-2 * π * x * ζ) * Complex.I) * (ψ x * 𝓕⁻ m (x - z))) := fun x => by ring
  simp_rw [this, integral_const_mul, hu, mul_zero]

/-- **Orthogonality of tile pieces with disjoint `3ω`** (needs `β + 2δ ≤ 3`). -/
theorem gfun_orthogonal {s' v' : ℤ} {c' : ℝ} {ψ' m' : ℝ → ℂ} (hN : 2 ≤ 𝔭.N) (hD : 2 ≤ 𝔭.D)
    (hβ : 0 ≤ 𝔭.β) (hβδ : 𝔭.β + 2 * 𝔭.δ ≤ 3) (hψ : InPsi 𝔭 s v ψ)
    (hψ' : InPsi 𝔭 s' v' ψ') (hm : InMult 𝔭 s c m) (hm' : InMult 𝔭 s' c' m') {f f' : ℝ → ℂ}
    (hf : Measurable f) (hf' : Measurable f') {B B' : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) (hB' : ∀ z, ‖f' z‖ ≤ B')
    (hdisj : Disjoint (Set.Ico (c - 3 * (2 : ℝ) ^ (-s) / 2) (c + 3 * (2 : ℝ) ^ (-s) / 2))
      (Set.Ico (c' - 3 * (2 : ℝ) ^ (-s') / 2) (c' + 3 * (2 : ℝ) ^ (-s') / 2))) :
    ∫ x, gfun ψ m f x * (starRingEnd ℂ) (gfun ψ' m' f' x) = 0 := by
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-s) := zpow_pos (by norm_num) _
  have hl' : (0 : ℝ) < (2 : ℝ) ^ (-s') := zpow_pos (by norm_num) _
  have key := pairing_eq_zero_of_fourier_Icc (u := gfun ψ m f) (v := gfun ψ' m' f')
    (integrable_gfun hN hD hβ hψ hm hf hB) (continuous_gfun hD hβ hψ' hm' hf' hB')
    (integrable_gfun hN hD hβ hψ' hm' hf' hB')
    (a := c - 3 * (2 : ℝ) ^ (-s) / 2) (b := c + 3 * (2 : ℝ) ^ (-s) / 2)
    (a' := c' - 3 * (2 : ℝ) ^ (-s') / 2) (b' := c' + 3 * (2 : ℝ) ^ (-s') / 2)
    (fun ξ hξ => by
      refine fourier_gfun_eq_zero hN hD hβ hψ hm hf hB ξ ?_
      have : 3 * (2 : ℝ) ^ (-s) / 2 < |ξ - c| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hξ
        rw [lt_abs]
        rcases hξ with h | h
        · right; linarith
        · left; linarith
      nlinarith)
    (fun ξ hξ => by
      refine fourier_gfun_eq_zero hN hD hβ hψ' hm' hf' hB' ξ ?_
      have : 3 * (2 : ℝ) ^ (-s') / 2 < |ξ - c'| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hξ
        rw [lt_abs]
        rcases hξ with h | h
        · right; linarith
        · left; linarith
      nlinarith) hdisj
  exact key

end Pieces

end PrimeBHT.TimeFrequency.X2
