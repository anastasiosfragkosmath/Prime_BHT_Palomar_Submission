module

public import PrimeBHT.TimeFrequency.X2.EngTail.FamSum
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# X2, V11-b: the Fefferman-Stein inequality (good-`λ` form, arbitrary intervals)

`fefferman_stein`: for `g ≥ 0` measurable, integrable, with `∫ g^R < ∞` (`R > 1`), and a measurable `h : ℝ → ℝ≥0∞` such
that for every interval `[a, b)` and every `x ∈ [a, b)` some constant `c` has `∫_{[a,b)} |g - c| ≤ (b - a) h(x)`
(i.e. `h ≥` the sharp function of `g`), `∫ g^R ≤ fsConst R · ∫ h^R`.

Proof: good-`λ` inequality `|{g > 4t}| ≤ γ |{M g > t}| + |{h > γ t}|` from the Calderón-Zygmund intervals of `g` at
level `t` (`CZ.exists_cz_intervals`), the layer-cake formula and the Hardy-Littlewood maximal theorem; absorption with
`γ = fsGamma R`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open PrimeCarleson.Proof.Common

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Pint

/-- Upper layer cake for an `ℝ≥0∞`-valued function with finite `R`-th moment. -/
theorem layer_le {R : ℝ} (hR : 0 < R) {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) (hfin : ∫⁻ x, φ x ^ R ≠ ⊤) :
    ENNReal.ofReal R * ∫⁻ t in Ioi (0 : ℝ), volume {x | ENNReal.ofReal t < φ x} * ENNReal.ofReal (t ^ (R - 1)) ≤
      ∫⁻ x, φ x ^ R := by
  have hnull : volume {x | φ x = ⊤} = 0 := by
    by_contra h
    apply hfin
    refine eq_top_iff.2 ?_
    calc (⊤ : ℝ≥0∞) = ∫⁻ x in {x | φ x = ⊤}, ⊤ := by rw [setLIntegral_const, ENNReal.top_mul h]
      _ ≤ ∫⁻ x in {x | φ x = ⊤}, φ x ^ R :=
          setLIntegral_mono' (hφ (measurableSet_singleton ⊤)) fun x hx => by
            rw [show φ x = ⊤ from hx, ENNReal.top_rpow_of_pos hR]
      _ ≤ _ := setLIntegral_le_lintegral _ _
  have h1 := lintegral_rpow_eq_lintegral_meas_lt_mul (μ := volume) (f := fun x => (φ x).toReal)
    (ae_of_all _ fun x => ENNReal.toReal_nonneg) hφ.ennreal_toReal.aemeasurable hR
  calc _ ≤ ENNReal.ofReal R * ∫⁻ t in Ioi (0 : ℝ), volume {x | t < (φ x).toReal} * ENNReal.ofReal (t ^ (R - 1)) := by
        refine mul_le_mul_of_nonneg_left (lintegral_mono fun t => mul_le_mul_of_nonneg_right ?_ zero_le) zero_le
        calc volume {x | ENNReal.ofReal t < φ x} ≤ volume ({x | t < (φ x).toReal} ∪ {x | φ x = ⊤}) := by
              refine measure_mono fun x hx => ?_
              by_cases htop : φ x = ⊤
              · exact Or.inr htop
              · left
                show t < (φ x).toReal
                rcases lt_or_ge t 0 with ht | ht
                · exact ht.trans_le ENNReal.toReal_nonneg
                · exact (ENNReal.ofReal_lt_iff_lt_toReal ht htop).1 hx
          _ ≤ volume {x | t < (φ x).toReal} + volume {x | φ x = ⊤} := measure_union_le _ _
          _ = _ := by rw [hnull, add_zero]
    _ = ∫⁻ x, ENNReal.ofReal ((φ x).toReal ^ R) := h1.symm
    _ ≤ _ := lintegral_mono fun x => by
        by_cases htop : φ x = ⊤
        · rw [htop, ENNReal.top_rpow_of_pos hR]; exact le_top
        · rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hR.le, ENNReal.ofReal_toReal htop]

section GoodLambda

variable {g : ℝ → ℝ} (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g) {h : ℝ → ℝ≥0∞}
  (hh : Measurable h)
  (hosc : ∀ a b : ℝ, a < b → ∀ x ∈ Ico a b, ∃ c : ℝ,
    ∫⁻ y in Ico a b, ENNReal.ofReal |g y - c| ≤ ENNReal.ofReal (b - a) * h x)
include hgm hg0 hgi hh hosc

/-- The good-`λ` estimate on one Calderón-Zygmund interval. -/
theorem good_lambda_piece {γ t : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (ht : 0 < t) {a b : ℝ} (hab : a < b)
    (hup : ∫ x in Ico a b, g x ≤ 2 * t * (b - a)) :
    volume (Ico a b ∩ {x | 4 * t < g x}) ≤
      ENNReal.ofReal γ * volume (Ico a b) + volume (Ico a b ∩ {x | ENNReal.ofReal (γ * t) < h x}) := by
  by_cases hex : ∃ x0 ∈ Ico a b, h x0 ≤ ENNReal.ofReal (γ * t)
  · obtain ⟨x0, hx0, hhx0⟩ := hex
    obtain ⟨c, hc⟩ := hosc a b hab x0 hx0
    have hba : 0 < b - a := sub_pos.2 hab
    have hc' : ∫⁻ y in Ico a b, ENNReal.ofReal |g y - c| ≤ ENNReal.ofReal ((b - a) * (γ * t)) :=
      hc.trans (by rw [ENNReal.ofReal_mul hba.le]; gcongr)
    have hgI : ∫⁻ y in Ico a b, ENNReal.ofReal (g y) = ENNReal.ofReal (∫ y in Ico a b, g y) :=
      (ofReal_integral_eq_lintegral_ofReal hgi.integrableOn (ae_of_all _ fun y => hg0 y)).symm
    have habsm : Measurable fun y => ENNReal.ofReal |g y - c| :=
      (continuous_abs.measurable.comp (hgm.sub_const c)).ennreal_ofReal
    have hc3 : c ≤ 3 * t := by
      by_contra hcon
      push Not at hcon
      have hle : ∫⁻ _y in Ico a b, ENNReal.ofReal c ≤
          (∫⁻ y in Ico a b, ENNReal.ofReal |g y - c|) + ∫⁻ y in Ico a b, ENNReal.ofReal (g y) := by
        rw [← lintegral_add_left habsm]
        refine lintegral_mono fun y => ?_
        rw [← ENNReal.ofReal_add (abs_nonneg _) (hg0 y)]
        refine ENNReal.ofReal_le_ofReal ?_
        have := neg_abs_le (g y - c)
        linarith
      rw [setLIntegral_const, Real.volume_Ico, hgI, ← ENNReal.ofReal_mul (by linarith)] at hle
      have h2 := hle.trans (add_le_add hc' (ENNReal.ofReal_le_ofReal hup))
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at h2
      have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
      have h4 := mul_lt_mul_of_pos_right hcon hba
      have h5 : (b - a) * (γ * t) ≤ (b - a) * t := by
        have := mul_le_mul_of_nonneg_right hγ1 ht.le
        nlinarith
      linarith
    have hsub : Ico a b ∩ {x | 4 * t < g x} ⊆ {x | ENNReal.ofReal t ≤ ENNReal.ofReal |g x - c|} ∩ Ico a b := by
      rintro x ⟨hxI, hx⟩
      refine ⟨ENNReal.ofReal_le_ofReal ?_, hxI⟩
      have hx' : 4 * t < g x := hx
      have := le_abs_self (g x - c)
      linarith
    have hcheb := mul_meas_ge_le_lintegral₀ (μ := volume.restrict (Ico a b))
      (continuous_abs.measurable.comp (hgm.sub_const c)).ennreal_ofReal.aemeasurable (ENNReal.ofReal t)
    rw [Measure.restrict_apply' measurableSet_Ico] at hcheb
    have hv : volume ({x | ENNReal.ofReal t ≤ ENNReal.ofReal |g x - c|} ∩ Ico a b) ≤
        ENNReal.ofReal γ * volume (Ico a b) := by
      have ht0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.2 ht).ne'
      rw [← ENNReal.mul_le_mul_iff_right ht0 ENNReal.ofReal_ne_top]
      refine (hcheb.trans hc').trans (le_of_eq ?_)
      rw [Real.volume_Ico, ← ENNReal.ofReal_mul hγ0.le, ← ENNReal.ofReal_mul ht.le]
      congr 1; ring
    exact (measure_mono hsub).trans (hv.trans le_self_add)
  · push Not at hex
    refine le_add_left (measure_mono ?_)
    rintro x ⟨hxI, -⟩
    exact ⟨hxI, hex x hxI⟩

/-- **The good-`λ` inequality** `|{g > 4t}| ≤ γ |{M g > t}| + |{h > γ t}|`. -/
theorem good_lambda {γ t : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (ht : 0 < t) :
    volume {x | 4 * t < g x} ≤
      ENNReal.ofReal γ * volume {x | ENNReal.ofReal t < maximalHLR (fun y => ENNReal.ofReal (g y)) x} +
        volume {x | ENNReal.ofReal (γ * t) < h x} := by
  obtain ⟨ι, hι, a, b, hab, hdisj, hlow, hup, hae, -, -⟩ := CZ.exists_cz_intervals hg0 hgi ht
  have := hι
  set Q : ι → Set ℝ := fun i => Ico (a i) (b i) with hQ
  set H : Set ℝ := {x | ENNReal.ofReal (γ * t) < h x} with hH
  have hHm : MeasurableSet H := measurableSet_lt measurable_const hh
  have hnull : volume {x | x ∉ ⋃ i, Q i ∧ t < g x} = 0 := by
    rw [ae_iff] at hae
    refine measure_mono_null (fun x hx => ?_) hae
    simp only [mem_ofPred_eq, not_imp, not_le] at hx ⊢
    exact hx
  have hcover : {x | 4 * t < g x} ⊆ (⋃ i, Q i ∩ {x | 4 * t < g x}) ∪ {x | x ∉ ⋃ i, Q i ∧ t < g x} := by
    intro x hx
    by_cases hxQ : x ∈ ⋃ i, Q i
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hxQ
      exact Or.inl (mem_iUnion.2 ⟨i, hi, hx⟩)
    · have hx' : 4 * t < g x := hx
      exact Or.inr ⟨hxQ, by linarith⟩
  have hQM : (⋃ i, Q i) ⊆ {x | ENNReal.ofReal t < maximalHLR (fun y => ENNReal.ofReal (g y)) x} := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    have hba : 0 < b i - a i := sub_pos.2 (hab i)
    have h1 := PrimeBHT.TimeFrequency.Tile.lintegral_Icc_le_mul_maximalHLR (fun y => ENNReal.ofReal (g y))
      (hab i) (Ico_subset_Icc_self hi)
    simp only [enorm_eq_self] at h1
    have h2 : ENNReal.ofReal (t * (b i - a i)) < ∫⁻ y in Ico (a i) (b i), ENNReal.ofReal (g y) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hgi.integrableOn (ae_of_all _ fun y => hg0 y)]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 (hlow i)
    have h3 := h2.trans_le ((lintegral_mono_set Ico_subset_Icc_self).trans h1)
    rw [mul_comm t, ENNReal.ofReal_mul hba.le] at h3
    exact (ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_pos.2 hba).ne' ENNReal.ofReal_ne_top).1 h3
  calc volume {x | 4 * t < g x}
      ≤ volume ((⋃ i, Q i ∩ {x | 4 * t < g x}) ∪ {x | x ∉ ⋃ i, Q i ∧ t < g x}) := measure_mono hcover
    _ ≤ volume (⋃ i, Q i ∩ {x | 4 * t < g x}) + 0 := (measure_union_le _ _).trans_eq (by rw [hnull])
    _ ≤ ∑' i, volume (Q i ∩ {x | 4 * t < g x}) := by rw [add_zero]; exact measure_iUnion_le _
    _ ≤ ∑' i, (ENNReal.ofReal γ * volume (Q i) + volume (Q i ∩ H)) :=
        ENNReal.tsum_le_tsum fun i =>
          good_lambda_piece hgm hg0 hgi hh hosc hγ0 hγ1 ht (hab i) (hup i)
    _ = ENNReal.ofReal γ * volume (⋃ i, Q i) + volume (⋃ i, Q i ∩ H) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, measure_iUnion hdisj fun i => measurableSet_Ico,
          measure_iUnion (fun i j hij => (hdisj hij).mono inter_subset_left inter_subset_left)
            fun i => measurableSet_Ico.inter hHm]
    _ ≤ _ := by
        gcongr
        exact iUnion_subset fun i => inter_subset_right

end GoodLambda

/-- The absorption parameter of the good-`λ` argument. -/
def fsGamma (R : ℝ) : ℝ := 1 / (2 * 4 ^ R * max 1 ((maximalHLRConst (ENNReal.ofReal R) : ℝ) ^ R))

/-- The Fefferman-Stein constant. -/
def fsConst (R : ℝ) : ℝ := 2 * 4 ^ R * (fsGamma R)⁻¹ ^ R

theorem fsGamma_pos (R : ℝ) : 0 < fsGamma R := by
  unfold fsGamma
  have : (0 : ℝ) < max 1 ((maximalHLRConst (ENNReal.ofReal R) : ℝ) ^ R) := lt_max_of_lt_left one_pos
  positivity

theorem fsConst_pos (R : ℝ) : 0 < fsConst R := by
  unfold fsConst
  have := fsGamma_pos R
  positivity

/-- **Fefferman-Stein** (sharp-function majorant on all intervals). -/
theorem fefferman_stein {R : ℝ} (hR : 1 < R) {g : ℝ → ℝ} (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hgi : Integrable g) (hfin : ∫⁻ x, ENNReal.ofReal (g x ^ R) ≠ ⊤) {h : ℝ → ℝ≥0∞} (hh : Measurable h)
    (hosc : ∀ a b : ℝ, a < b → ∀ x ∈ Ico a b, ∃ c : ℝ,
      ∫⁻ y in Ico a b, ENNReal.ofReal |g y - c| ≤ ENNReal.ofReal (b - a) * h x) :
    ∫⁻ x, ENNReal.ofReal (g x ^ R) ≤ ENNReal.ofReal (fsConst R) * ∫⁻ x, h x ^ R := by
  have hR0 : 0 < R := by linarith
  set X := ∫⁻ x, ENNReal.ofReal (g x ^ R) with hX
  set H := ∫⁻ x, h x ^ R with hHdef
  by_cases hH : H = ⊤
  · rw [hH, ENNReal.mul_top (ENNReal.ofReal_pos.2 (fsConst_pos R)).ne']; exact le_top
  set M := maximalHLR (fun y => ENNReal.ofReal (g y)) with hMdef
  have hMm : Measurable M := measurable_maximalHLR _
  set CM : ℝ := (maximalHLRConst (ENNReal.ofReal R) : ℝ) with hCM
  set Km : ℝ := max 1 (CM ^ R) with hKm
  have hCM0 : 0 ≤ CM := NNReal.coe_nonneg _
  have hKm1 : 1 ≤ Km := le_max_left _ _
  have hWR : ∫⁻ x, ENNReal.ofReal (g x) ^ R = X :=
    lintegral_congr fun x => ENNReal.ofReal_rpow_of_nonneg (hg0 x) hR0.le
  -- the maximal theorem
  have hM : ∫⁻ x, M x ^ R ≤ ENNReal.ofReal Km * X := by
    have h1 := lintegral_maximal_rpow_le hR (hgm.ennreal_ofReal)
    rw [hWR] at h1
    have h2 := ENNReal.rpow_le_rpow h1 hR0.le
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hR0.ne', ENNReal.rpow_one,
      ENNReal.mul_rpow_of_nonneg _ _ hR0.le, ← ENNReal.rpow_mul, one_div_mul_cancel hR0.ne',
      ENNReal.rpow_one] at h2
    refine h2.trans (mul_le_mul_left ?_ X)
    rw [show ((maximalHLRConst (ENNReal.ofReal R) : ℝ≥0∞)) = ENNReal.ofReal CM from
      (ENNReal.ofReal_coe_nnreal).symm, ENNReal.ofReal_rpow_of_nonneg hCM0 hR0.le]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hMfin : ∫⁻ x, M x ^ R ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hM
  set γ := fsGamma R with hγ
  have hγ0 : 0 < γ := fsGamma_pos R
  have hγKm : γ * Km = 1 / (2 * 4 ^ R) := by
    rw [hγ, fsGamma, ← hCM, ← hKm]; field_simp
  have hγ1 : γ ≤ 1 := by
    have h4 : (1 : ℝ) ≤ 4 ^ R := Real.one_le_rpow (by norm_num) hR0.le
    have h5 : 1 ≤ 2 * 4 ^ R * Km := by nlinarith
    rw [hγ, fsGamma, ← hCM, ← hKm, div_le_one (by positivity)]
    exact h5
  -- layer cake for `g / 4`
  have hL1 := lintegral_rpow_eq_lintegral_meas_lt_mul (μ := volume) (f := fun x => g x / 4)
    (ae_of_all _ fun x => div_nonneg (hg0 x) (by norm_num)) (hgm.div_const 4).aemeasurable hR0
  have hgl : ∀ t ∈ Ioi (0 : ℝ), volume {x | t < g x / 4} * ENNReal.ofReal (t ^ (R - 1)) ≤
      ENNReal.ofReal γ * (volume {x | ENNReal.ofReal t < M x} * ENNReal.ofReal (t ^ (R - 1))) +
        volume {x | ENNReal.ofReal t < ENNReal.ofReal γ⁻¹ * h x} * ENNReal.ofReal (t ^ (R - 1)) := by
    intro t ht
    have hset : {x | t < g x / 4} = {x | 4 * t < g x} := by
      ext x; simp only [mem_ofPred_eq, lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)]; constructor <;> intro h <;> linarith
    have hsub : {x | ENNReal.ofReal (γ * t) < h x} ⊆ {x | ENNReal.ofReal t < ENNReal.ofReal γ⁻¹ * h x} := by
      intro x hx
      have hx' : ENNReal.ofReal (γ * t) < h x := hx
      show ENNReal.ofReal t < ENNReal.ofReal γ⁻¹ * h x
      have e : ENNReal.ofReal t = ENNReal.ofReal γ⁻¹ * ENNReal.ofReal (γ * t) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp
      rw [e]
      exact (ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_pos.2 (inv_pos.2 hγ0)).ne' ENNReal.ofReal_ne_top).2 hx'
    rw [hset, ← mul_assoc, ← add_mul]
    gcongr
    exact (good_lambda hgm hg0 hgi hh hosc hγ0 hγ1 ht).trans (add_le_add le_rfl (measure_mono hsub))
  have hanti : ∀ φ : ℝ → ℝ≥0∞, Measurable fun t : ℝ => volume {x | ENNReal.ofReal t < φ x} := by
    intro φ
    refine Antitone.measurable fun t t' htt' => measure_mono fun x hx => ?_
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal htt') hx
  have hφm : Measurable fun x => ENNReal.ofReal γ⁻¹ * h x := measurable_const.mul hh
  have hφfin : ∫⁻ x, (ENNReal.ofReal γ⁻¹ * h x) ^ R = ENNReal.ofReal (γ⁻¹ ^ R) * H := by
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hR0.le]
    rw [lintegral_const_mul _ (hh.pow_const R), ENNReal.ofReal_rpow_of_nonneg (by positivity) hR0.le]
  have hmain : ENNReal.ofReal (4 ^ (-R)) * X ≤ ENNReal.ofReal (1 / (2 * 4 ^ R)) * X +
      ENNReal.ofReal (γ⁻¹ ^ R) * H := by
    have e4 : ∫⁻ x, ENNReal.ofReal ((g x / 4) ^ R) = ENNReal.ofReal (4 ^ (-R)) * X := by
      rw [hX, ← lintegral_const_mul _ ((hgm.pow_const R).ennreal_ofReal)]
      refine lintegral_congr fun x => ?_
      rw [← ENNReal.ofReal_mul (by positivity), Real.div_rpow (hg0 x) (by norm_num), Real.rpow_neg (by norm_num)]
      congr 1; ring
    rw [← e4, hL1]
    calc ENNReal.ofReal R * ∫⁻ t in Ioi 0, volume {a | t < g a / 4} * ENNReal.ofReal (t ^ (R - 1))
        ≤ ENNReal.ofReal R * ∫⁻ t in Ioi 0, (ENNReal.ofReal γ * (volume {x | ENNReal.ofReal t < M x} *
            ENNReal.ofReal (t ^ (R - 1))) + volume {x | ENNReal.ofReal t < ENNReal.ofReal γ⁻¹ * h x} *
              ENNReal.ofReal (t ^ (R - 1))) := by
          exact mul_le_mul_of_nonneg_left (setLIntegral_mono' measurableSet_Ioi hgl) zero_le
      _ = ENNReal.ofReal γ * (ENNReal.ofReal R * ∫⁻ t in Ioi 0, volume {x | ENNReal.ofReal t < M x} *
            ENNReal.ofReal (t ^ (R - 1))) + ENNReal.ofReal R * ∫⁻ t in Ioi 0,
              volume {x | ENNReal.ofReal t < ENNReal.ofReal γ⁻¹ * h x} * ENNReal.ofReal (t ^ (R - 1)) := by
          have hB : Measurable fun t : ℝ => volume {x | ENNReal.ofReal t < M x} * ENNReal.ofReal (t ^ (R - 1)) :=
            (hanti M).mul (measurable_id.pow_const _).ennreal_ofReal
          have hA : Measurable fun t : ℝ => ENNReal.ofReal γ * (volume {x | ENNReal.ofReal t < M x} *
              ENNReal.ofReal (t ^ (R - 1))) := measurable_const.mul hB
          rw [lintegral_add_left hA, lintegral_const_mul _ hB, mul_add]
          ring
      _ ≤ ENNReal.ofReal γ * (∫⁻ x, M x ^ R) + ∫⁻ x, (ENNReal.ofReal γ⁻¹ * h x) ^ R := by
          have hl1 := layer_le hR0 hMm hMfin
          have hl2 := layer_le hR0 hφm (by rw [hφfin]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hH)
          exact add_le_add (mul_le_mul_right hl1 _) hl2
      _ ≤ ENNReal.ofReal γ * (ENNReal.ofReal Km * X) + ENNReal.ofReal (γ⁻¹ ^ R) * H := by
          rw [hφfin]; exact add_le_add (mul_le_mul_right hM _) le_rfl
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hγ0.le, hγKm]
  -- conclusion in real numbers
  have hXr : X = ENNReal.ofReal X.toReal := (ENNReal.ofReal_toReal hfin).symm
  have hHr : H = ENNReal.ofReal H.toReal := (ENNReal.ofReal_toReal hH).symm
  rw [hXr, hHr, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hmain
  rw [hXr, hHr, ← ENNReal.ofReal_mul (fsConst_pos R).le]
  refine ENNReal.ofReal_le_ofReal ?_
  have h4 : (4 : ℝ) ^ (-R) = 1 / 4 ^ R := by rw [Real.rpow_neg (by norm_num), one_div]
  rw [h4] at hmain
  have h4p : (0 : ℝ) < 4 ^ R := by positivity
  have hx0 : 0 ≤ X.toReal := ENNReal.toReal_nonneg
  have key : X.toReal ≤ 2 * 4 ^ R * (γ⁻¹ ^ R * H.toReal) := by
    have e : 1 / 4 ^ R * X.toReal = 2 * (1 / (2 * 4 ^ R) * X.toReal) := by field_simp
    have h5 : 1 / (2 * 4 ^ R) * X.toReal ≤ γ⁻¹ ^ R * H.toReal := by linarith
    have h6 : X.toReal = 2 * 4 ^ R * (1 / (2 * 4 ^ R) * X.toReal) := by field_simp
    rw [h6]; gcongr
  rw [fsConst, ← hγ]
  linarith [key]

end PrimeBHT.TimeFrequency.X2.Pint
