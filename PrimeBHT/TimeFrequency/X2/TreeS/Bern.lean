module

public import PrimeBHT.TimeFrequency.X2.FourierSupport
public import PrimeBHT.TimeFrequency.X2.Ortho.Duals
public import PrimeBHT.TimeFrequency.X2.EngTail.Single
import Mathlib.Analysis.Convolution

/-!
# X2, node V15s: Bernstein's inequality for `T_m F` with bounded `F`

`tm_eq_bernstein`: for `m ∈ M_ω(𝔭)` (support `|ξ - c| ≤ β 2^{-s}/2`, `β ≤ 3`) and a bounded measurable `f` (not necessarily
integrable),
`T_m f (x) = ∫ K(x - z) T_m f(z) dz`, `K = 𝓕⁻(bernN c (2^s/3))`.  (`FourierSupport.lean` has this for integrable band-limited
functions; here `K_m * K = K_m` and the associativity of the convolution give it for `T_m f = f * K_m`.)
`yNorm_tmult_le_integral_bernstein`: the vector pointwise form.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform Convolution Real ComplexConjugate
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

section Bern

variable {𝔭 : Params} {s : ℤ} {c : ℝ} {m : ℝ → ℂ}

theorem integrable_fourierInv_bernN (c L : ℝ) (hL : 0 < L) : Integrable (𝓕⁻ (bernN c L)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_fourierInv_bernN_le 2
  have hKc : Continuous (𝓕⁻ (bernN c L)) :=
    continuous_fourierInv_of_integrable' (integrable_of_far (contDiff_bernN c L).continuous
      (fun ξ hξ => bernN_eq_zero hL (c := c) (ξ := ξ) (by simpa using hξ)) (c := c) (r := 1 / L))
  have hint := (integrable_one_add_abs_sub_div_rpow (p := 2) (by norm_num) 0 hL).const_mul (C * L⁻¹)
  refine hint.mono' hKc.aestronglyMeasurable (Eventually.of_forall fun w => ?_)
  have := hC c L hL w
  simp only [Nat.cast_ofNat, sub_zero] at this ⊢
  calc ‖𝓕⁻ (bernN c L) w‖ ≤ C * L⁻¹ * (1 + |w| / L) ^ (-(2 : ℝ)) := this
    _ = _ := by ring

theorem continuous_fourierInv_bernN (c L : ℝ) (hL : 0 < L) : Continuous (𝓕⁻ (bernN c L)) :=
  continuous_fourierInv_of_integrable' (integrable_of_far (contDiff_bernN c L).continuous
    (fun ξ hξ => bernN_eq_zero hL (c := c) (ξ := ξ) (by simpa using hξ)) (c := c) (r := 1 / L))

/-- `𝓕⁻ m` is a band-limited function with Fourier support in `[c ± 3/(2 · 2^s)]`. -/
theorem isBandLimited_fourierInv_inMult (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hβ3 : 𝔭.β ≤ 3) (hm : InMult 𝔭 s c m) :
    IsBandLimited (𝓕⁻ m) (Icc (c - 1 / (2 * ((2 : ℝ) ^ s / 3))) (c + 1 / (2 * ((2 : ℝ) ^ s / 3)))) := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  have hK : 𝓕 (𝓕⁻ m) = m :=
    Continuous.fourier_fourierInv_eq hm.1.continuous (integrable_of_far hm.1.continuous hm.2.1)
      (integrable_fourier_inMult hD hβ hm)
  refine ⟨continuous_fourierInv_of_integrable' (integrable_of_far hm.1.continuous hm.2.1),
    integrable_fourierInv_inMult hD hβ hm, Metric.isBounded_Icc _ _, fun ξ hξ => ?_⟩
  rw [hK]
  refine hm.2.1 ξ ?_
  simp only [mem_Icc, not_and_or, not_le] at hξ
  have e : 1 / (2 * ((2 : ℝ) ^ s / 3)) = 3 / 2 * (2 : ℝ) ^ (-s) := by
    rw [zpow_neg]; field_simp
  rw [e] at hξ
  have h1 : 𝔭.β * (2 : ℝ) ^ (-s) / 2 ≤ 3 / 2 * (2 : ℝ) ^ (-s) := by
    have := zpow_pos (by norm_num : (0 : ℝ) < 2) (-s)
    nlinarith
  rcases hξ with h | h
  · have : ξ - c < 0 := by
      have := zpow_pos (by norm_num : (0 : ℝ) < 2) (-s); linarith
    rw [abs_of_neg this]; linarith
  · have : 0 ≤ ξ - c := by
      have := zpow_pos (by norm_num : (0 : ℝ) < 2) (-s); linarith
    rw [abs_of_nonneg this]; linarith


/-- **Bernstein for `T_m f`, `f` bounded**: `T_m f (x) = ∫ K(x - z) T_m f(z) dz`. -/
theorem tm_eq_bernstein (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hβ3 : 𝔭.β ≤ 3) (hm : InMult 𝔭 s c m) {f : ℝ → ℂ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) (x : ℝ) :
    tm m f x = ∫ z, 𝓕⁻ (bernN c ((2 : ℝ) ^ s / 3)) (x - z) * tm m f z := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ s / 3 := by have := zpow_pos (by norm_num : (0 : ℝ) < 2) s; positivity
  set L : ℝ := (2 : ℝ) ^ s / 3 with hLdef
  set Km : ℝ → ℂ := 𝓕⁻ m with hKm
  set Kn : ℝ → ℂ := 𝓕⁻ (bernN c L) with hKn
  have hKmi : Integrable Km := integrable_fourierInv_inMult hD hβ hm
  have hKni : Integrable Kn := integrable_fourierInv_bernN c L hL
  have hkern : ∀ w, ∫ t, Kn t * Km (w - t) = Km w := by
    intro w
    have h1 : Km w = ∫ z, Kn (w - z) * Km z :=
      (isBandLimited_fourierInv_inMult hD hβ hβ3 hm).bernstein_reproduce (c := c) (L := L) hL (subset_refl _) w
    rw [h1]
    rw [← integral_sub_left_eq_self (fun z => Kn (w - z) * Km z) volume w]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [sub_sub_cancel]
  have hfx : ∀ x₀ : ℝ, Measurable fun t => f (x₀ - t) := fun x₀ => hf.comp (measurable_const.sub measurable_id)
  set L₀ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ with hL₀
  have hfg : ∀ᵐ y ∂(volume : Measure ℝ), ConvolutionExistsAt Kn Km y L₀ volume :=
    Integrable.ae_convolution_exists L₀ hKni hKmi
  have hgk : ∀ᵐ y ∂(volume : Measure ℝ), ConvolutionExistsAt Km f y L₀ volume := by
    refine Eventually.of_forall fun y => ?_
    have := hKmi.bdd_mul (c := B) (hfx y).aestronglyMeasurable (Eventually.of_forall fun t => hB _)
    exact this.congr (Eventually.of_forall fun t => by simp [L₀, mul_comm])
  have hi : Integrable (Function.uncurry fun a b : ℝ => (L₀ (Kn b)) ((L₀ (Km (a - b))) (f (x - a)))) (volume.prod volume) := by
    have h1 := hKni.convolution_integrand L₀ hKmi
    have h2 := h1.bdd_mul (c := B) (f := fun p : ℝ × ℝ => f (x - p.1))
      ((hfx x).comp measurable_fst |>.aestronglyMeasurable) (Eventually.of_forall fun p => hB _)
    refine h2.congr (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, L₀, ContinuousLinearMap.mul_apply']
    ring
  have hassoc := convolution_assoc' L₀ L₀ L₀ L₀ (fun a b c => mul_assoc a b c) (f := Kn) (g := Km) (k := f)
    (x₀ := x) hfg hgk hi
  have e1 : (Kn ⋆[L₀, volume] Km) = Km := by
    funext w
    rw [convolution_def]
    simpa [L₀] using hkern w
  have e2 : ∀ z, (Km ⋆[L₀, volume] f) z = tm m f z := by
    intro z
    rw [convolution_def]
    unfold tm
    rw [← integral_sub_left_eq_self (fun t => 𝓕⁻ m (z - t) * f t) volume z]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp [L₀, hKm, mul_comm]
  rw [e1] at hassoc
  rw [e2 x] at hassoc
  rw [hassoc, convolution_def]
  rw [← integral_sub_left_eq_self (fun z => Kn (x - z) * tm m f z) volume x]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [sub_sub_cancel, L₀, ContinuousLinearMap.mul_apply', e2]


/-- **Bernstein, vector pointwise form**: `‖T_m F (x)‖_{L^{s'}(Y)} ≤ ∫ |K(x - z)| ‖T_m F (z)‖_{L^{s'}(Y)} dz`. -/
theorem yNorm_tmult_le_integral_bernstein {P : ℕ} [NeZero P] {s' : ℝ} (hs' : 1 ≤ s')
    (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hβ3 : 𝔭.β ≤ 3) (hm : InMult 𝔭 s c m) {F : ℝ → ZMod P → ℂ}
    (hF : Measurable F) {B : ℝ} (hB : ∀ z y, ‖F z y‖ ≤ B) (x : ℝ) :
    yNorm s' (tmult m F x) ≤ ∫ z, ‖𝓕⁻ (bernN c ((2 : ℝ) ^ s / 3)) (x - z)‖ * yNorm s' (tmult m F z) := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ s / 3 := by have := zpow_pos (by norm_num : (0 : ℝ) < 2) s; positivity
  set L : ℝ := (2 : ℝ) ^ s / 3 with hLdef
  have hKni : Integrable (𝓕⁻ (bernN c L)) := integrable_fourierInv_bernN c L hL
  have hKmc : Continuous (𝓕⁻ m) :=
    continuous_fourierInv_of_integrable' (integrable_of_far hm.1.continuous hm.2.1)
  have hTm : Measurable (tmult m F) := measurable_tmult_of_cont hKmc hF
  have hTb : ∀ z y, ‖tmult m F z y‖ ≤ B * ∫ w, ‖𝓕⁻ m w‖ := fun z y =>
    norm_tm_le hD hβ hm (fun z' => hB z' y) z
  have hrep : tmult m F x = fun y => ∫ z, 𝓕⁻ (bernN c L) (x - z) * tmult m F z y := by
    funext y
    exact tm_eq_bernstein hD hβ hβ3 hm (hF.comp measurable_id |> fun h => (measurable_pi_apply y).comp hF)
      (fun z => hB z y) x
  have hV : ∀ y, Integrable (fun z => 𝓕⁻ (bernN c L) (x - z) * tmult m F z y) volume := by
    intro y
    have := (hKni.comp_sub_left x).bdd_mul (c := B * ∫ w, ‖𝓕⁻ m w‖)
      ((measurable_pi_apply y).comp hTm).aestronglyMeasurable (Eventually.of_forall fun z => hTb z y)
    exact this.congr (Eventually.of_forall fun z => by simp [mul_comm])
  have hs0 : 0 < s' := by linarith
  rw [hrep]
  refine (yNorm_integral_le_of_one_le hs' (fun z y => 𝓕⁻ (bernN c L) (x - z) * tmult m F z y) hV).trans ?_
  refine le_of_eq (integral_congr_ae (Eventually.of_forall fun z => ?_))
  exact yNorm_fun_const_mul hs0 _ _

end Bern

end PrimeBHT.TimeFrequency.X2
