module

public import PrimeBHT.TimeFrequency.X2.Psp.Defs
public import PrimeBHT.TimeFrequency.X2.ClassKernel
public import PrimeBHT.TimeFrequency.X2.ClassLemmas
public import PrimeBHT.TimeFrequency.X2.Energy
import Mathlib.Analysis.Fourier.Convolution

/-!
# X2, V13: domination by lower-bounded cutoffs (D-1 .. D-4)

`docs/audits/X2-V13-route-check.md` §2.2.

* **D-1** `tileCutoff_le`, `le_tileCutoff`: for `IsEtaCut 𝔭 η` the cutoff `θ_I = tileCutoff η s v = 1_I * η_s` satisfies
  `K⁻¹ ⟨(x - c_I)/|I|⟩^{-N} ≤ θ_I(x) ≤ K ⟨(x - c_I)/|I|⟩^{-N}`, `K = 𝔭.C (3/2)^N`; `inX_tileCutoff` (class membership,
  conditional on the profile `η` of V05-1: `IsEtaCut`, V05's `exists_eta` has not landed).
* **D-2** `norm_le_of_lower_bound`, `eLpNorm_dominated`: a weight `|w| ≤ A ⟨(x - c_I)/|I|⟩^{-N'}`, `N' ≥ N`, is dominated
  by `A K θ_I`, hence `‖w T_m F‖_p ≤ A K ‖θ_I T_m F‖_p` (no Fourier support of a product is ever needed).
* **D-3** `peetre_D3`: `⟨n⟩^a ⟨x - c₀⟩^{-N₀} ⟨x - c_P⟩^{-N} ≤ ⟨x - c_P⟩^{-(N - a)}` for `N₀ ≥ a`, `n = c₀ - c_P`.
* **D-4** `layerCut_le`, `layerCut_rpow_le`: `χ̃_σ(x) ≤ K Σ_{R ∈ T(σ)} ⟨(x - c_R)/2^σ⟩^{-N}`, and the `a`-th power
  (`0 < a ≤ 1`, subadditivity) `≤ K^a Σ_R ⟨…⟩^{-N a}`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform Convolution Real ContDiff
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-! ## D-3: Peetre -/

theorem jb_add_le (a b : ℝ) : jb (a + b) ≤ jb a * jb b := by
  unfold jb
  nlinarith [abs_add_le a b, abs_nonneg a, abs_nonneg b, mul_nonneg (abs_nonneg a) (abs_nonneg b)]

/-! ## Subadditivity of `t ↦ t^a` -/

theorem rpow_add_le_add_rpow_real {x y a : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (x + y) ^ a ≤ x ^ a + y ^ a := by
  have := NNReal.rpow_add_le_add_rpow ⟨x, hx⟩ ⟨y, hy⟩ ha0 ha1
  exact_mod_cast this

theorem rpow_sum_le_sum_rpow {ι : Type*} (S : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ S, 0 ≤ f i) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1) : (∑ i ∈ S, f i) ^ a ≤ ∑ i ∈ S, f i ^ a := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [Real.zero_rpow ha0.ne']
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have h1 : 0 ≤ ∑ j ∈ S, f j := Finset.sum_nonneg fun j hj => hf j (Finset.mem_insert_of_mem hj)
    calc (f i + ∑ j ∈ S, f j) ^ a ≤ f i ^ a + (∑ j ∈ S, f j) ^ a :=
          rpow_add_le_add_rpow_real (hf i (Finset.mem_insert_self _ _)) h1 ha0.le ha1
      _ ≤ _ := by
          gcongr
          exact ih fun j hj => hf j (Finset.mem_insert_of_mem hj)

/-! ## D-1: the cutoffs `θ_I = 1_I * η_s` -/

section Cutoff

variable {𝔭 : Params} {η : ℝ → ℝ}

/-- The constant `K = 𝔭.C (3/2)^N` of the two-sided bound of `tileCutoff`. -/
def cutK (𝔭 : Params) : ℝ := 𝔭.C * ((3 : ℝ) / 2) ^ (𝔭.N : ℝ)

theorem cutK_pos (hC : 0 < 𝔭.C) : 0 < cutK 𝔭 := by
  unfold cutK; positivity

theorem jb_le_three_halves_mul {a u : ℝ} (h : |a - u| ≤ 1 / 2) : jb a ≤ 3 / 2 * jb u := by
  unfold jb
  have := abs_sub_abs_le_abs_sub a u
  nlinarith [abs_nonneg u, abs_nonneg a]

theorem eta_le_pt (hη : IsEtaCut 𝔭 η) {a u : ℝ} (h : |a - u| ≤ 1 / 2) :
    η u ≤ cutK 𝔭 * jb a ^ (-(𝔭.N : ℝ)) := by
  have h1 := jb_le_three_halves_mul h
  have hu : 0 < jb u := jb_pos u
  have ha : 0 < jb a := jb_pos a
  have h2 : 2 / 3 * jb a ≤ jb u := by linarith
  have h3 : jb u ^ (-(𝔭.N : ℝ)) ≤ ((3 : ℝ) / 2) ^ (𝔭.N : ℝ) * jb a ^ (-(𝔭.N : ℝ)) := by
    calc jb u ^ (-(𝔭.N : ℝ)) ≤ (2 / 3 * jb a) ^ (-(𝔭.N : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by simp)
      _ = (2 / 3 : ℝ) ^ (-(𝔭.N : ℝ)) * jb a ^ (-(𝔭.N : ℝ)) := Real.mul_rpow (by norm_num) ha.le
      _ = _ := by
          congr 1
          rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)]
          norm_num
  have hC : 0 ≤ 𝔭.C := by
    by_contra hC
    push Not at hC
    have h0 := hη.2.2.2.1 0
    have h00 := hη.2.1 0
    have : 𝔭.C * jb 0 ^ (-(𝔭.N : ℝ)) < 0 :=
      mul_neg_of_neg_of_pos hC (Real.rpow_pos_of_pos (jb_pos 0) _)
    linarith
  calc η u ≤ 𝔭.C * jb u ^ (-(𝔭.N : ℝ)) := hη.2.2.2.1 u
    _ ≤ 𝔭.C * (((3 : ℝ) / 2) ^ (𝔭.N : ℝ) * jb a ^ (-(𝔭.N : ℝ))) := by gcongr
    _ = _ := by unfold cutK; ring

theorem le_eta_pt (hη : IsEtaCut 𝔭 η) (hC : 0 < 𝔭.C) {a u : ℝ} (h : |a - u| ≤ 1 / 2) :
    (cutK 𝔭)⁻¹ * jb a ^ (-(𝔭.N : ℝ)) ≤ η u := by
  have h1 : jb u ≤ 3 / 2 * jb a := by
    have := jb_le_three_halves_mul (a := u) (u := a) (by rwa [abs_sub_comm])
    exact this
  have hu : 0 < jb u := jb_pos u
  have ha : 0 < jb a := jb_pos a
  have h3 : ((3 : ℝ) / 2) ^ (-(𝔭.N : ℝ)) * jb a ^ (-(𝔭.N : ℝ)) ≤ jb u ^ (-(𝔭.N : ℝ)) := by
    calc ((3 : ℝ) / 2) ^ (-(𝔭.N : ℝ)) * jb a ^ (-(𝔭.N : ℝ)) = (3 / 2 * jb a) ^ (-(𝔭.N : ℝ)) :=
          (Real.mul_rpow (by norm_num) ha.le).symm
      _ ≤ jb u ^ (-(𝔭.N : ℝ)) := Real.rpow_le_rpow_of_nonpos hu h1 (by simp)
  have e : (cutK 𝔭)⁻¹ = 𝔭.C⁻¹ * ((3 : ℝ) / 2) ^ (-(𝔭.N : ℝ)) := by
    unfold cutK
    rw [mul_inv, Real.rpow_neg (by norm_num)]
  calc (cutK 𝔭)⁻¹ * jb a ^ (-(𝔭.N : ℝ))
      = 𝔭.C⁻¹ * (((3 : ℝ) / 2) ^ (-(𝔭.N : ℝ)) * jb a ^ (-(𝔭.N : ℝ))) := by rw [e]; ring
    _ ≤ 𝔭.C⁻¹ * jb u ^ (-(𝔭.N : ℝ)) := by gcongr
    _ ≤ η u := hη.2.2.2.2.1 u

theorem abs_centre_sub_le {s v : ℤ} {x y : ℝ} (hy : y ∈ dyadicInt s v) :
    |(x - dyCentre s v) / (2 : ℝ) ^ s - (x - y) / (2 : ℝ) ^ s| ≤ 1 / 2 := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  obtain ⟨h1, h2⟩ := hy
  unfold dyCentre
  have e : (x - (2 : ℝ) ^ s * ((v : ℝ) + 1 / 2)) / (2 : ℝ) ^ s - (x - y) / (2 : ℝ) ^ s =
      (y - (2 : ℝ) ^ s * ((v : ℝ) + 1 / 2)) / (2 : ℝ) ^ s := by field_simp; ring
  rw [e, abs_div, abs_of_pos hp, div_le_iff₀ hp, abs_le]
  constructor <;> nlinarith

theorem integrableOn_cutoff_integrand (hη : IsEtaCut 𝔭 η) (s v : ℤ) (x : ℝ) :
    IntegrableOn (fun y => (2 : ℝ) ^ (-s) * η ((x - y) / (2 : ℝ) ^ s)) (dyadicInt s v) := by
  have hc : Continuous (fun y : ℝ => (2 : ℝ) ^ (-s) * η ((x - y) / (2 : ℝ) ^ s)) :=
    continuous_const.mul (hη.1.comp ((continuous_const.sub continuous_id).div_const _))
  exact hc.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self

/-- **D-1 (upper bound)**: `θ_I(x) ≤ K ⟨(x - c_I)/|I|⟩^{-N}`. -/
theorem tileCutoff_le (hη : IsEtaCut 𝔭 η) (s v : ℤ) (x : ℝ) :
    tileCutoff η s v x ≤ cutK 𝔭 * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-(𝔭.N : ℝ)) := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  have hq : (2 : ℝ) ^ (-s) * (2 : ℝ) ^ s = 1 := by rw [← zpow_add₀ (by norm_num)]; simp
  unfold tileCutoff
  have hmono : ∫ y in dyadicInt s v, (2 : ℝ) ^ (-s) * η ((x - y) / (2 : ℝ) ^ s) ≤
      ∫ y in dyadicInt s v, (2 : ℝ) ^ (-s) *
        (cutK 𝔭 * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-(𝔭.N : ℝ))) := by
    refine setIntegral_mono_on (integrableOn_cutoff_integrand hη s v x) (integrableOn_const (by
      rw [volume_dyadicInt]; exact ENNReal.ofReal_ne_top)) (measurableSet_dyadicInt s v) fun y hy => ?_
    exact mul_le_mul_of_nonneg_left (eta_le_pt hη (abs_centre_sub_le hy)) (zpow_pos (by norm_num) _).le
  refine hmono.trans (le_of_eq ?_)
  rw [setIntegral_const, smul_eq_mul]
  have : volume.real (dyadicInt s v) = (2 : ℝ) ^ s := by
    rw [Measure.real, toReal_volume_dyadicInt]
  rw [this]
  calc (2 : ℝ) ^ s * ((2 : ℝ) ^ (-s) * (cutK 𝔭 * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-(𝔭.N : ℝ))))
      = ((2 : ℝ) ^ s * (2 : ℝ) ^ (-s)) * (cutK 𝔭 * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-(𝔭.N : ℝ))) := by
        ring
    _ = _ := by rw [mul_comm ((2 : ℝ) ^ s), hq, one_mul]

/-- **D-1 (lower bound)**: `θ_I(x) ≥ K⁻¹ ⟨(x - c_I)/|I|⟩^{-N}`. -/
theorem le_tileCutoff (hη : IsEtaCut 𝔭 η) (hC : 0 < 𝔭.C) (s v : ℤ) (x : ℝ) :
    (cutK 𝔭)⁻¹ * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-(𝔭.N : ℝ)) ≤ tileCutoff η s v x := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  have hq : (2 : ℝ) ^ (-s) * (2 : ℝ) ^ s = 1 := by rw [← zpow_add₀ (by norm_num)]; simp
  unfold tileCutoff
  have hmono : ∫ y in dyadicInt s v, (2 : ℝ) ^ (-s) *
        ((cutK 𝔭)⁻¹ * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-(𝔭.N : ℝ))) ≤
      ∫ y in dyadicInt s v, (2 : ℝ) ^ (-s) * η ((x - y) / (2 : ℝ) ^ s) := by
    refine setIntegral_mono_on (integrableOn_const (by
      rw [volume_dyadicInt]; exact ENNReal.ofReal_ne_top)) (integrableOn_cutoff_integrand hη s v x)
      (measurableSet_dyadicInt s v) fun y hy => ?_
    exact mul_le_mul_of_nonneg_left (le_eta_pt hη hC (abs_centre_sub_le hy)) (zpow_pos (by norm_num) _).le
  refine le_trans (le_of_eq ?_) hmono
  rw [setIntegral_const, smul_eq_mul]
  have : volume.real (dyadicInt s v) = (2 : ℝ) ^ s := by
    rw [Measure.real, toReal_volume_dyadicInt]
  rw [this]
  calc (cutK 𝔭)⁻¹ * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-(𝔭.N : ℝ))
      = ((2 : ℝ) ^ s * (2 : ℝ) ^ (-s)) *
          ((cutK 𝔭)⁻¹ * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-(𝔭.N : ℝ))) := by
        rw [mul_comm ((2 : ℝ) ^ s), hq, one_mul]
    _ = _ := by ring

theorem tileCutoff_nonneg (hη : IsEtaCut 𝔭 η) (s v : ℤ) (x : ℝ) : 0 ≤ tileCutoff η s v x := by
  unfold tileCutoff
  exact setIntegral_nonneg (measurableSet_dyadicInt s v) fun y _ =>
    mul_nonneg (zpow_pos (by norm_num) _).le (hη.2.1 _)

end Cutoff

/-! ## D-1: the cutoff is in the class `X_I` (conditional on the profile `η`) -/

section ClassMembership

variable {𝔭 : Params} {η : ℝ → ℝ}

theorem continuous_tileCutoff (hη : IsEtaCut 𝔭 η) (s v : ℤ) : Continuous (tileCutoff η s v) := by
  have hab : (2 : ℝ) ^ s * v ≤ (2 : ℝ) ^ s * (v + 1) := by
    have hp : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
    nlinarith
  have hf : Continuous (fun p : ℝ × ℝ => (2 : ℝ) ^ (-s) * η ((p.1 - p.2) / (2 : ℝ) ^ s)) :=
    continuous_const.mul (hη.1.comp ((continuous_fst.sub continuous_snd).div_const _))
  have := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    (f := fun x y => (2 : ℝ) ^ (-s) * η ((x - y) / (2 : ℝ) ^ s)) hf ((2 : ℝ) ^ s * v) ((2 : ℝ) ^ s * (v + 1))
  refine this.congr fun x => ?_
  rw [intervalIntegral.integral_of_le hab, ← integral_Ico_eq_integral_Ioc]
  rfl

theorem integrable_eta_scaled (hη : IsEtaCut 𝔭 η) (hN : 2 ≤ 𝔭.N) (s : ℤ) :
    Integrable (fun x : ℝ => ((2 : ℝ) ^ (-s) * η (x / (2 : ℝ) ^ s) : ℝ)) volume := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  have hC : 0 ≤ 𝔭.C := by
    by_contra hC
    push Not at hC
    have h0 := hη.2.2.2.1 0
    have h00 := hη.2.1 0
    have : 𝔭.C * jb 0 ^ (-(𝔭.N : ℝ)) < 0 :=
      mul_neg_of_neg_of_pos hC (Real.rpow_pos_of_pos (jb_pos 0) _)
    linarith
  have h1 := (integrable_jb_rpow (c := 0) hL (r := (𝔭.N : ℝ)) (by
    have : (2 : ℝ) ≤ 𝔭.N := by exact_mod_cast hN
    linarith)).const_mul (𝔭.C * (2 : ℝ) ^ (-s))
  refine h1.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (continuous_const.mul (hη.1.comp (continuous_id.div_const _))).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (zpow_pos (by norm_num) _).le (hη.2.1 _))]
    have := hη.2.2.2.1 (x / (2 : ℝ) ^ s)
    have e : jb (x / (2 : ℝ) ^ s) = jb ((x - 0) / (2 : ℝ) ^ s) := by rw [sub_zero]
    rw [e] at this
    calc (2 : ℝ) ^ (-s) * η (x / (2 : ℝ) ^ s)
        ≤ (2 : ℝ) ^ (-s) * (𝔭.C * jb ((x - 0) / (2 : ℝ) ^ s) ^ (-(𝔭.N : ℝ))) :=
          mul_le_mul_of_nonneg_left this (zpow_pos (by norm_num) _).le
      _ = _ := by ring

/-- `𝓕 (η_s) ξ = 𝓕 η (2^s ξ)` for `η_s x = 2^{-s} η (x / 2^s)`. -/
theorem fourier_eta_scaled (η : ℝ → ℝ) (s : ℤ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (((2 : ℝ) ^ (-s) * η (x / (2 : ℝ) ^ s) : ℝ) : ℂ)) ξ =
      𝓕 (fun x : ℝ => (η x : ℂ)) ((2 : ℝ) ^ s * ξ) := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  set L : ℝ := (2 : ℝ) ^ s with hLdef
  have hq : (2 : ℝ) ^ (-s) * L = 1 := by rw [hLdef, ← zpow_add₀ (by norm_num)]; simp
  have e : ∀ x : ℝ, Complex.exp (↑(-2 * π * x * ξ) * Complex.I) • (((2 : ℝ) ^ (-s) * η (x / L) : ℝ) : ℂ) =
      (((2 : ℝ) ^ (-s) : ℝ) : ℂ) • (fun u : ℝ => Complex.exp (↑(-2 * π * u * (L * ξ)) * Complex.I) • (η u : ℂ)) (x / L) := by
    intro x
    simp only [smul_eq_mul]
    have : (-2 * π * (x / L) * (L * ξ)) = -2 * π * x * ξ := by field_simp
    rw [this]
    push_cast
    ring
  set g : ℝ → ℂ := fun u : ℝ => Complex.exp (↑(-2 * π * u * (L * ξ)) * Complex.I) • (η u : ℂ) with hg
  have h1 : (∫ x : ℝ, Complex.exp (↑(-2 * π * x * ξ) * Complex.I) • (((2 : ℝ) ^ (-s) * η (x / L) : ℝ) : ℂ)) =
      ∫ x : ℝ, (((2 : ℝ) ^ (-s) : ℝ) : ℂ) • (g (x / L)) := integral_congr_ae (Filter.Eventually.of_forall e)
  rw [h1, integral_smul, Measure.integral_comp_div g L, abs_of_pos hL]
  have : (((2 : ℝ) ^ (-s) : ℝ) : ℂ) * ((L : ℝ) : ℂ) = 1 := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hq
    simpa using this
  simp only [Complex.real_smul, smul_eq_mul]
  rw [← mul_assoc, this, one_mul]

/-- **D-1 (class membership, conditional on the profile)**: for `IsEtaCut 𝔭 η` with `N ≥ 2`, the cutoff
`θ_I = 1_I * η_s` of every dyadic interval is in `X_I` of the class with the amplitude constant `K = 𝔭.C (3/2)^N`
(`cutK`).  V05-1's `exists_eta` (not yet landed) provides `η` at decay `N/8`. -/
theorem inX_tileCutoff (hη : IsEtaCut 𝔭 η) (hC : 0 < 𝔭.C) (hN : 2 ≤ 𝔭.N) (s v : ℤ) :
    InX { 𝔭 with C := cutK 𝔭 } s v (tileCutoff η s v) := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  refine ⟨⟨Complex.continuous_ofReal.comp (continuous_tileCutoff hη s v), fun x => ?_, fun ξ hξ => ?_⟩,
    fun x => ?_⟩
  · show ‖((tileCutoff η s v x : ℝ) : ℂ)‖ ≤ cutK 𝔭 * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-(𝔭.N : ℝ))
    rw [Complex.norm_real, Real.norm_of_nonneg (tileCutoff_nonneg hη s v x)]
    exact tileCutoff_le hη s v x
  · -- Fourier support: `𝓕 (1_I * η_s) = 𝓕 1_I · 𝓕 η_s`
    change 𝔭.δ * (2 : ℝ) ^ (-s) < |ξ| at hξ
    show 𝓕 (fun x => (tileCutoff η s v x : ℂ)) ξ = 0
    set f₁ : ℝ → ℂ := (dyadicInt s v).indicator (fun _ => (1 : ℂ)) with hf₁
    set f₂ : ℝ → ℂ := fun x => (((2 : ℝ) ^ (-s) * η (x / (2 : ℝ) ^ s) : ℝ) : ℂ) with hf₂
    have h1 : Integrable f₁ := by
      refine (integrableOn_const (μ := volume) (s := dyadicInt s v) (C := (1 : ℂ)) (by
        rw [volume_dyadicInt]; exact ENNReal.ofReal_ne_top)).integrable_indicator (measurableSet_dyadicInt s v)
    have h2 : Integrable f₂ := (integrable_eta_scaled hη hN s).ofReal
    have hconv : (fun x => (tileCutoff η s v x : ℂ)) = f₁ ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] f₂ := by
      funext x
      rw [convolution_def]
      simp only [ContinuousLinearMap.mul_apply', hf₁, hf₂]
      have : ∀ y, (dyadicInt s v).indicator (fun _ => (1 : ℂ)) y * ((((2 : ℝ) ^ (-s) * η ((x - y) / (2 : ℝ) ^ s) : ℝ)) : ℂ) =
          (dyadicInt s v).indicator (fun y => ((((2 : ℝ) ^ (-s) * η ((x - y) / (2 : ℝ) ^ s) : ℝ)) : ℂ)) y := by
        intro y
        by_cases hy : y ∈ dyadicInt s v <;> simp [Set.indicator, hy]
      simp_rw [this]
      rw [integral_indicator (measurableSet_dyadicInt s v)]
      unfold tileCutoff
      exact (integral_ofReal (𝕜 := ℂ)).symm
    rw [hconv, Real.fourier_mul_convolution_eq h1 h2, hf₂, fourier_eta_scaled]
    have : 𝓕 (fun x : ℝ => (η x : ℂ)) ((2 : ℝ) ^ s * ξ) = 0 := by
      refine hη.2.2.2.2.2 _ ?_
      rw [abs_mul, abs_of_pos hL]
      have : 𝔭.δ = 𝔭.δ * ((2 : ℝ) ^ (-s) * (2 : ℝ) ^ s) := by
        rw [← zpow_add₀ (by norm_num)]; simp
      calc 𝔭.δ = 𝔭.δ * (2 : ℝ) ^ (-s) * (2 : ℝ) ^ s := by rw [mul_assoc]; exact this
        _ < |ξ| * (2 : ℝ) ^ s := by gcongr
        _ = _ := mul_comm _ _
    rw [this, mul_zero]
  · exact le_tileCutoff hη hC s v x

end ClassMembership

/-! ## D-2: domination -/

section Domination

/-- **D-2 (pointwise)**: a weight `|w| ≤ A ⟨(x - c)/L⟩^{-N'}` with `N' ≥ N` is dominated by `A K θ` for every `θ`
with the lower bound `θ ≥ K⁻¹ ⟨(x - c)/L⟩^{-N}`. -/
theorem norm_le_of_lower {N N' A K c L : ℝ} (hN : N ≤ N') (hA : 0 ≤ A) (hK : 0 < K) {w : ℝ → ℂ} {θ : ℝ → ℝ}
    (hw : ∀ x, ‖w x‖ ≤ A * jb ((x - c) / L) ^ (-N'))
    (hθ : ∀ x, K⁻¹ * jb ((x - c) / L) ^ (-N) ≤ θ x) (x : ℝ) : ‖w x‖ ≤ A * K * θ x := by
  have h1 : jb ((x - c) / L) ^ (-N') ≤ jb ((x - c) / L) ^ (-N) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_jb _) (by linarith)
  calc ‖w x‖ ≤ A * jb ((x - c) / L) ^ (-N') := hw x
    _ ≤ A * jb ((x - c) / L) ^ (-N) := by gcongr
    _ = A * K * (K⁻¹ * jb ((x - c) / L) ^ (-N)) := by field_simp
    _ ≤ A * K * θ x := by gcongr; exact hθ x

/-- **D-2 (`L^p` form)**: if `|w| ≤ C |θ|` pointwise then `‖w T_m F‖_{L^p(L^s)} ≤ C ‖θ T_m F‖_{L^p(L^s)}`
(`hmeas`: measurability of `x ↦ ‖w T_m F(x)‖_{L^s(Y)}`, needed because `eLpNorm` of a non-measurable function is `⊤`). -/
theorem eLpNorm_dominated {P : ℕ} [NeZero P] {s : ℝ} (hs : 0 < s) (m : ℝ → ℂ) (F : ℝ → ZMod P → ℂ)
    {w θ : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C) (hdom : ∀ x, ‖w x‖ ≤ C * ‖θ x‖) (p : ℝ≥0∞)
    (hmeas : AEStronglyMeasurable (fun x => yNorm s (w x • tmult m F x)) volume) :
    eLpNorm (fun x => yNorm s (w x • tmult m F x)) p volume ≤
      ENNReal.ofReal C * eLpNorm (fun x => yNorm s (θ x • tmult m F x)) p volume := by
  have h1 : eLpNorm (fun x => yNorm s (w x • tmult m F x)) p volume ≤
      eLpNorm (fun x => C * yNorm s (θ x • tmult m F x)) p volume := by
    refine eLpNorm_mono hmeas fun x => ?_
    have e1 : yNorm s (w x • tmult m F x) = ‖w x‖ * yNorm s (tmult m F x) := yNorm_fun_const_mul hs _ _
    have e2 : yNorm s (θ x • tmult m F x) = ‖θ x‖ * yNorm s (tmult m F x) := yNorm_fun_const_mul hs _ _
    have hy : 0 ≤ yNorm s (tmult m F x) := by unfold yNorm; positivity
    have h0 : 0 ≤ yNorm s (θ x • tmult m F x) := by unfold yNorm; positivity
    rw [Real.norm_of_nonneg (by unfold yNorm; positivity), Real.norm_of_nonneg (by positivity), e1, e2]
    calc ‖w x‖ * yNorm s (tmult m F x) ≤ (C * ‖θ x‖) * yNorm s (tmult m F x) :=
          mul_le_mul_of_nonneg_right (hdom x) hy
      _ = _ := by ring
  refine h1.trans (le_of_eq ?_)
  have := eLpNorm_const_smul (μ := volume) (p := p) (c := C) (f := fun x => yNorm s (θ x • tmult m F x))
  simp only [Real.enorm_eq_ofReal hC] at this
  exact this

/-- **D-2 (single tile)**: the single-tile operator `θ T_m` of a tile `R ∈ Cs` (cutoff `θ ∈ Ψ_{I_R}`, multiplier in
`M_{ω_{R,k}}`, any top frequency `ξ ∈ hull R`) is bounded by the energy: its normalized `L^q(L^s)` norm is `≤ eng`. -/
theorem single_tile_le_eng {𝔭 : Params} {P : ℕ} [NeZero P] {s q : ℝ} {k : Fin 3} {F : ℝ → ZMod P → ℂ}
    {Cs : Finset TriTile} {R : TriTile} (hR : R ∈ Cs) {ξ : ℝ} (hξ : ξ ∈ R.box.hull) {θ m : ℝ → ℂ}
    (hθ : InPsi 𝔭 R.box.scale R.pos θ) (hm : InMult 𝔭 R.box.scale (R.box.centre k) m) :
    ENNReal.ofReal (((2 : ℝ) ^ R.box.scale) ^ (-1 / q)) *
        eLpNorm (fun x => yNorm s (θ x • tmult m F x)) (ENNReal.ofReal q) volume ≤ eng 𝔭 s k F Cs q := by
  set t : Top := ((R.box.scale, R.pos), ξ) with ht
  have hsub : ({R} : Finset TriTile) ⊆ Cs := by simpa using hR
  have htree : IsTree ({R} : Finset TriTile) t := by
    intro R' hR'
    rw [Finset.mem_singleton] at hR'
    subst hR'
    exact ⟨subset_rfl, hξ⟩
  have hlac : IsLacunary k ({R} : Finset TriTile) := by
    intro R' hR' R'' hR'' hne
    rw [Finset.mem_singleton] at hR' hR''
    subst hR' hR''
    exact absurd rfl hne
  have hdata : IsTreeOpData 𝔭 k ({R} : Finset TriTile) (fun _ => θ) (fun _ => m) := by
    refine ⟨fun Q hQ => ?_, fun Q hQ Q' hQ' _ => rfl⟩
    rw [Finset.mem_singleton] at hQ
    subst hQ
    exact ⟨hθ, hm⟩
  have h1 := le_topNorm (s := s) (k := k) (F := F) (q := q) (t := t) hdata
  have h2 := topNorm_le_eng (𝔭 := 𝔭) (s := s) (k := k) (F := F) (q := q) hsub htree hlac
  refine le_trans (le_of_eq ?_) (h1.trans h2)
  unfold treeOpNorm
  simp only [treeOp, Finset.sum_singleton, ht]

end Domination

/-! ## D-4: the layer cutoff -/

section Layer

variable {𝔭 : Params} {η : ℝ → ℝ}

theorem layerCut_nonneg (hη : IsEtaCut 𝔭 η) (Tr : Finset TriTile) (σ : ℤ) (x : ℝ) : 0 ≤ layerCut η Tr σ x :=
  Finset.sum_nonneg fun R _ => tileCutoff_nonneg hη σ R.pos x

/-- **D-4**: `χ̃_σ(x) ≤ K Σ_{R ∈ T(σ)} ⟨(x - c_R)/2^σ⟩^{-N}`. -/
theorem layerCut_le (hη : IsEtaCut 𝔭 η) (Tr : Finset TriTile) (σ : ℤ) (x : ℝ) :
    layerCut η Tr σ x ≤
      cutK 𝔭 * ∑ R ∈ layer' Tr σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-(𝔭.N : ℝ)) := by
  unfold layerCut
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun R _ => tileCutoff_le hη σ R.pos x

/-- **D-4 (`a`-th power)**: `χ̃_σ^a ≤ K^a Σ_R ⟨(x - c_R)/2^σ⟩^{-N a}` for `0 < a ≤ 1` (subadditivity of `t ↦ t^a`).
With `a = 1/6` and D-2 (energy class `N/8`): `N/6 - N/8 ≥ 2` iff `N ≥ 48`. -/
theorem layerCut_rpow_le (hη : IsEtaCut 𝔭 η) (hC : 0 < 𝔭.C) (Tr : Finset TriTile) (σ : ℤ) (x : ℝ) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1) :
    layerCut η Tr σ x ^ a ≤
      cutK 𝔭 ^ a * ∑ R ∈ layer' Tr σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-((𝔭.N : ℝ) * a)) := by
  have hK := cutK_pos hC
  have h1 : layerCut η Tr σ x ^ a ≤
      (cutK 𝔭 * ∑ R ∈ layer' Tr σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-(𝔭.N : ℝ))) ^ a :=
    Real.rpow_le_rpow (layerCut_nonneg hη Tr σ x) (layerCut_le hη Tr σ x) ha0.le
  have hS : ∀ R ∈ layer' Tr σ, 0 ≤ jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-(𝔭.N : ℝ)) :=
    fun R _ => (Real.rpow_pos_of_pos (jb_pos _) _).le
  have h2 := rpow_sum_le_sum_rpow (layer' Tr σ)
    (fun R => jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-(𝔭.N : ℝ))) hS ha0 ha1
  calc layerCut η Tr σ x ^ a ≤ _ := h1
    _ = cutK 𝔭 ^ a * (∑ R ∈ layer' Tr σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-(𝔭.N : ℝ))) ^ a :=
        Real.mul_rpow hK.le (Finset.sum_nonneg hS)
    _ ≤ cutK 𝔭 ^ a * ∑ R ∈ layer' Tr σ, (jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-(𝔭.N : ℝ))) ^ a := by
        gcongr
    _ = _ := by
        congr 1
        refine Finset.sum_congr rfl fun R _ => ?_
        rw [← Real.rpow_mul (jb_pos _).le]
        congr 1; ring

/-- Tiles of one scale of a tree (one box per scale) have distinct positions: sums over `layer'` are sums over the keys. -/
theorem sum_layer'_eq_sum_keys {Tr : Finset TriTile}
    (hb : ∀ R ∈ Tr, ∀ R' ∈ Tr, R.box.scale = R'.box.scale → R.box = R'.box) (σ : ℤ) (f : ℤ → ℝ) :
    ∑ R ∈ layer' Tr σ, f R.pos = ∑ v ∈ layerKeys Tr σ, f v := by
  unfold layerKeys
  rw [Finset.sum_image]
  intro R hR R' hR' hpos
  have hR := mem_layer'_iff.1 (Finset.mem_coe.1 hR)
  have hR' := mem_layer'_iff.1 (Finset.mem_coe.1 hR')
  have hbox := hb R hR.1 R' hR'.1 (by rw [hR.2, hR'.2])
  cases R; cases R'
  simp_all

end Layer

/-! ## D-1/D-2 glue: the scaled cutoff in `Ψ_I(𝔭)` -/

section Scaled

variable {𝔭 : Params} {η : ℝ → ℝ}

/-- `(3/2)^{-N}`. -/
def cutScale (𝔭 : Params) : ℝ := ((3 : ℝ) / 2) ^ (-(𝔭.N : ℝ))

theorem cutScale_pos (𝔭 : Params) : 0 < cutScale 𝔭 := Real.rpow_pos_of_pos (by norm_num) _

theorem cutScale_mul_cutK (hC : 0 < 𝔭.C) : cutScale 𝔭 * cutK 𝔭 = 𝔭.C := by
  unfold cutScale cutK
  rw [Real.rpow_neg (by norm_num)]
  have : (0 : ℝ) < ((3 : ℝ) / 2) ^ (𝔭.N : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  field_simp

/-- The scaled cutoff `θ'_I = (3/2)^{-N} θ_I` (`θ_I = 1_I * η_s`): it is in `Ψ_I(𝔭)` for the SAME class `𝔭` as the
profile `η` (`IsEtaCut 𝔭 η`), so single-tile operators `θ'_I T_m` are bounded by the energy of class `𝔭`
(`single_tile_le_eng`). -/
def cutoffPsi (𝔭 : Params) (η : ℝ → ℝ) (s v : ℤ) : ℝ → ℂ :=
  fun x => ((cutScale 𝔭 * tileCutoff η s v x : ℝ) : ℂ)

theorem inPsi_cutoffPsi (hη : IsEtaCut 𝔭 η) (hC : 0 < 𝔭.C) (hN : 2 ≤ 𝔭.N) (s v : ℤ) :
    InPsi 𝔭 s v (cutoffPsi 𝔭 η s v) := by
  have h0 := (inX_tileCutoff hη hC hN s v).1
  have hK := cutScale_mul_cutK hC
  have hp := (cutScale_pos 𝔭).le
  refine ⟨?_, fun x => ?_, fun ξ hξ => ?_⟩
  · exact Complex.continuous_ofReal.comp (continuous_const.mul (continuous_tileCutoff hη s v))
  · unfold cutoffPsi
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hp (tileCutoff_nonneg hη s v x))]
    calc cutScale 𝔭 * tileCutoff η s v x
        ≤ cutScale 𝔭 * (cutK 𝔭 * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-(𝔭.N : ℝ))) :=
          mul_le_mul_of_nonneg_left (tileCutoff_le hη s v x) hp
      _ = _ := by rw [← mul_assoc, hK]
  · have h1 : 𝓕 (fun x => ((tileCutoff η s v x : ℝ) : ℂ)) ξ = 0 := h0.2.2 ξ hξ
    have e : cutoffPsi 𝔭 η s v = fun x => ((cutScale 𝔭 : ℝ) : ℂ) * ((tileCutoff η s v x : ℝ) : ℂ) := by
      funext x; unfold cutoffPsi; push_cast; rfl
    show 𝓕 (cutoffPsi 𝔭 η s v) ξ = 0
    rw [e, fourier_const_mul', h1, mul_zero]

/-- **D-2 for the scaled cutoff**: a weight `|w| ≤ A ⟨(x - c_I)/|I|⟩^{-N'}`, `N' ≥ N`, is dominated by
`A 𝔭.C (3/2)^{2N} |θ'_I|`, so `‖w T_m F‖_p ≤ A 𝔭.C (3/2)^{2N} ‖θ'_I T_m F‖_p` (`eLpNorm_dominated`) and the right side is a
single-tile operator of the class `𝔭` (`single_tile_le_eng`). -/
theorem norm_le_cutoffPsi (hη : IsEtaCut 𝔭 η) (hC : 0 < 𝔭.C) {N' A : ℝ} (hN' : (𝔭.N : ℝ) ≤ N') (hA : 0 ≤ A)
    {s v : ℤ} {w : ℝ → ℂ} (hw : ∀ x, ‖w x‖ ≤ A * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-N')) (x : ℝ) :
    ‖w x‖ ≤ A * (𝔭.C * ((3 : ℝ) / 2) ^ (2 * (𝔭.N : ℝ))) * ‖cutoffPsi 𝔭 η s v x‖ := by
  have hg : (0 : ℝ) < ((3 : ℝ) / 2) ^ (𝔭.N : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have e2 : ((3 : ℝ) / 2) ^ (2 * (𝔭.N : ℝ)) = (((3 : ℝ) / 2) ^ (𝔭.N : ℝ)) ^ 2 := by
    rw [show 2 * (𝔭.N : ℝ) = (𝔭.N : ℝ) + (𝔭.N : ℝ) by ring, Real.rpow_add (by norm_num)]; ring
  have hK : 0 < 𝔭.C * ((3 : ℝ) / 2) ^ (2 * (𝔭.N : ℝ)) := by positivity
  have hθ : ∀ x : ℝ, (𝔭.C * ((3 : ℝ) / 2) ^ (2 * (𝔭.N : ℝ)))⁻¹ *
      jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-(𝔭.N : ℝ)) ≤ cutScale 𝔭 * tileCutoff η s v x := by
    intro x
    have h1 := le_tileCutoff hη hC s v x
    have e : (𝔭.C * ((3 : ℝ) / 2) ^ (2 * (𝔭.N : ℝ)))⁻¹ = cutScale 𝔭 * (cutK 𝔭)⁻¹ := by
      unfold cutScale cutK
      rw [e2, Real.rpow_neg (by norm_num)]
      field_simp
    rw [e, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (cutScale_pos 𝔭).le
  have := norm_le_of_lower (N := (𝔭.N : ℝ)) (N' := N') (A := A) (K := 𝔭.C * ((3 : ℝ) / 2) ^ (2 * (𝔭.N : ℝ)))
    (c := dyCentre s v) (L := (2 : ℝ) ^ s) hN' hA hK hw
    (θ := fun x => cutScale 𝔭 * tileCutoff η s v x) hθ x
  refine this.trans (le_of_eq ?_)
  unfold cutoffPsi
  rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (cutScale_pos 𝔭).le (tileCutoff_nonneg hη s v x))]

end Scaled

end PrimeBHT.TimeFrequency.X2
