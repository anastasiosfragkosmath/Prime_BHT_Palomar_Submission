module

public import PrimeBHT.TimeFrequency.X2.Psp.O2Fine

/-!
# X2, V13 O2 (i): the lower bound of `a = |I₀|⁻¹ ∫ w_{I₀} μ_σ` (MTT2 `muj-lower`)

For a lattice scale `σ' ≤ σ` and a point `y₀`: `∫ w_{I₀}(y) ⟨(y - y₀)/2^{σ'}⟩^{-100} dy ≥ 2^{-101} 2^{σ'} ⟨(y₀ - c_{I₀})/2^σ⟩^{-2}`;
hence `∫ w_{I₀} μ_σ ≥ 2^{-101} Σ_{σ' ≤ σ, σ' ∈ S} Σ_{y₀ ∈ ∂Ẽ_{σ'}} 2^{-|σ - σ'|/(100J)} 2^{σ'} ⟨(y₀ - c_{I₀})/2^σ⟩^{-2}`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform ContDiff Real Convolution
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

theorem jb_add_le_o2 (a b : ℝ) : jb (a + b) ≤ jb a * jb b := by
  unfold jb
  nlinarith [abs_add_le a b, abs_nonneg a, abs_nonneg b]

theorem jb_div_add_le (a b T : ℝ) (_hT : 0 < T) : jb ((a + b) / T) ≤ jb (a / T) * jb (b / T) := by
  rw [add_div]; exact jb_add_le_o2 _ _

theorem lower_weight (c y₀ : ℝ) {T L : ℝ} (hT : 0 < T) (hL : 0 < L) (hLT : L ≤ T) :
    (2 : ℝ) ^ (-(101 : ℝ)) * L * jb ((y₀ - c) / T) ^ (-(2 : ℝ)) ≤
      ∫ y, jb ((y - c) / T) ^ (-(2 : ℝ)) * jb ((y - y₀) / L) ^ (-(100 : ℝ)) := by
  set f : ℝ → ℝ := fun y => jb ((y - c) / T) ^ (-(2 : ℝ)) * jb ((y - y₀) / L) ^ (-(100 : ℝ)) with hf
  have hf0 : ∀ y, 0 ≤ f y := fun y => by
    have := jb_pos ((y - c) / T); have := jb_pos ((y - y₀) / L); positivity
  have hfc : Continuous f := by
    have h1 : Continuous fun y : ℝ => jb ((y - c) / T) := by unfold jb; fun_prop
    have h2 : Continuous fun y : ℝ => jb ((y - y₀) / L) := by unfold jb; fun_prop
    exact (h1.rpow_const (fun y => Or.inl (jb_pos _).ne')).mul (h2.rpow_const (fun y => Or.inl (jb_pos _).ne'))
  have hfi : Integrable f := by
    have hint := integrable_jb_rpow (c := y₀) hL (r := 100) (by norm_num)
    refine hint.mono' hfc.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (hf0 y)]
    have h1 : jb ((y - c) / T) ^ (-(2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (one_le_jb _) (by norm_num)
    calc f y ≤ 1 * jb ((y - y₀) / L) ^ (-(100 : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (by have := jb_pos ((y - y₀) / L); positivity)
      _ = _ := one_mul _
  set B : Set ℝ := Set.Icc (y₀ - L) (y₀ + L) with hB
  have hBm : MeasurableSet B := measurableSet_Icc
  have hlow : ∀ y ∈ B, (2 : ℝ) ^ (-(100 : ℝ)) * ((1 / 4) * jb ((y₀ - c) / T) ^ (-(2 : ℝ))) ≤ f y := by
    intro y hy
    have hyy : |y - y₀| ≤ L := abs_le.2 ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hj1 : jb ((y - y₀) / L) ≤ 2 := by
      unfold jb; rw [abs_div, abs_of_pos hL]
      have : |y - y₀| / L ≤ 1 := (div_le_one hL).2 hyy
      linarith
    have hj1' : (2 : ℝ) ^ (-(100 : ℝ)) ≤ jb ((y - y₀) / L) ^ (-(100 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (jb_pos _) hj1 (by norm_num)
    have hj2 : jb ((y - c) / T) ≤ 2 * jb ((y₀ - c) / T) := by
      have e : y - c = (y₀ - c) + (y - y₀) := by ring
      rw [e]
      refine (jb_div_add_le _ _ T hT).trans ?_
      have : jb ((y - y₀) / T) ≤ 2 := by
        unfold jb; rw [abs_div, abs_of_pos hT]
        have : |y - y₀| / T ≤ 1 := (div_le_one hT).2 (hyy.trans hLT)
        linarith
      have h0 := (jb_pos ((y₀ - c) / T)).le
      nlinarith
    have hj2' : (2 * jb ((y₀ - c) / T)) ^ (-(2 : ℝ)) ≤ jb ((y - c) / T) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (jb_pos _) hj2 (by norm_num)
    have e2 : (2 * jb ((y₀ - c) / T)) ^ (-(2 : ℝ)) = (1 / 4) * jb ((y₀ - c) / T) ^ (-(2 : ℝ)) := by
      rw [Real.mul_rpow (by norm_num) (jb_pos _).le]
      have : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
        rw [Real.rpow_neg (by norm_num)]; norm_num
      rw [this]
    rw [e2] at hj2'
    have h3 : 0 ≤ (1 / 4) * jb ((y₀ - c) / T) ^ (-(2 : ℝ)) := by have := jb_pos ((y₀ - c) / T); positivity
    calc (2 : ℝ) ^ (-(100 : ℝ)) * ((1 / 4) * jb ((y₀ - c) / T) ^ (-(2 : ℝ)))
        = ((1 / 4) * jb ((y₀ - c) / T) ^ (-(2 : ℝ))) * (2 : ℝ) ^ (-(100 : ℝ)) := by ring
      _ ≤ jb ((y - c) / T) ^ (-(2 : ℝ)) * jb ((y - y₀) / L) ^ (-(100 : ℝ)) :=
          mul_le_mul hj2' hj1' (by positivity) (by have := jb_pos ((y - c) / T); positivity)
  have hIB : ∫ y in B, f y ≤ ∫ y, f y := setIntegral_le_integral hfi (Filter.Eventually.of_forall hf0)
  have hIB2 : (2 : ℝ) ^ (-(100 : ℝ)) * ((1 / 4) * jb ((y₀ - c) / T) ^ (-(2 : ℝ))) * (2 * L) ≤ ∫ y in B, f y := by
    have hc : ∫ y in B, (2 : ℝ) ^ (-(100 : ℝ)) * ((1 / 4) * jb ((y₀ - c) / T) ^ (-(2 : ℝ))) =
        (volume B).toReal • ((2 : ℝ) ^ (-(100 : ℝ)) * ((1 / 4) * jb ((y₀ - c) / T) ^ (-(2 : ℝ)))) := setIntegral_const _
    have hvol : (volume B).toReal = 2 * L := by
      rw [hB, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; ring
    have hmono := setIntegral_mono_on (μ := volume) (s := B)
      (f := fun _ => (2 : ℝ) ^ (-(100 : ℝ)) * ((1 / 4) * jb ((y₀ - c) / T) ^ (-(2 : ℝ)))) (g := f)
      (integrableOn_const (by simp [hB, Real.volume_Icc])) hfi.integrableOn hBm hlow
    rw [hc, hvol, smul_eq_mul] at hmono
    linarith
  have e3 : (2 : ℝ) ^ (-(100 : ℝ)) * ((1 / 4) * jb ((y₀ - c) / T) ^ (-(2 : ℝ))) * (2 * L) =
      (2 : ℝ) ^ (-(101 : ℝ)) * L * jb ((y₀ - c) / T) ^ (-(2 : ℝ)) := by
    have : (2 : ℝ) ^ (-(101 : ℝ)) = (2 : ℝ) ^ (-(100 : ℝ)) * (1 / 2) := by
      rw [show (-(101 : ℝ)) = -(100 : ℝ) + (-1) by norm_num, Real.rpow_add (by norm_num), Real.rpow_neg_one]
      norm_num
    rw [this]; ring
  linarith

theorem integrable_weight_mul (σ v σ' : ℤ) (y₀ : ℝ) :
    Integrable (fun x => ovWeight 2 σ v x * jb ((x - y₀) / (2 : ℝ) ^ σ') ^ (-(100 : ℝ))) := by
  have hL := zpow_two_pos σ'
  have hint := integrable_jb_rpow (c := y₀) hL (r := 100) (by norm_num)
  have hc : Continuous fun x : ℝ => ovWeight 2 σ v x * jb ((x - y₀) / (2 : ℝ) ^ σ') ^ (-(100 : ℝ)) := by
    unfold ovWeight jb
    refine Continuous.mul ?_ ?_
    · exact (by fun_prop : Continuous fun x : ℝ => 1 + |(x - (2 : ℝ) ^ σ * ((v : ℝ) + 1 / 2)) / (2 : ℝ) ^ σ|).rpow_const
        (fun x => Or.inl (by positivity))
    · exact (by fun_prop : Continuous fun x : ℝ => 1 + |(x - y₀) / (2 : ℝ) ^ σ'|).rpow_const
        (fun x => Or.inl (by positivity))
  refine hint.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have h0 : 0 ≤ ovWeight 2 σ v x := by unfold ovWeight; have := jb_pos ((x - (2 : ℝ) ^ σ * ((v : ℝ) + 1 / 2)) / (2 : ℝ) ^ σ); positivity
  have h1 : ovWeight 2 σ v x ≤ 1 := by
    unfold ovWeight
    exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_jb _) (by norm_num)
  have h2 : 0 ≤ jb ((x - y₀) / (2 : ℝ) ^ σ') ^ (-(100 : ℝ)) := by have := jb_pos ((x - y₀) / (2 : ℝ) ^ σ'); positivity
  rw [Real.norm_of_nonneg (mul_nonneg h0 h2)]
  calc ovWeight 2 σ v x * jb ((x - y₀) / (2 : ℝ) ^ σ') ^ (-(100 : ℝ)) ≤ 1 * jb ((x - y₀) / (2 : ℝ) ^ σ') ^ (-(100 : ℝ)) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = _ := one_mul _

/-- **`muj-lower`**: `∫ w_{I₀} μ_σ ≥ 2^{-101} Σ_{σ' ≤ σ} Σ_{y₀ ∈ ends σ'} 2^{-|σ-σ'|/(100J)} 2^{σ'} ⟨(y₀ - c)/2^σ⟩^{-2}`. -/
theorem integral_ovWeight_muW_lower (J : ℕ) (S : Finset ℤ) (ends : ℤ → Finset ℝ) (σ v : ℤ) :
    ∑ σ' ∈ S.filter (fun σ' => σ' ≤ σ), ∑ y₀ ∈ ends σ',
      (2 : ℝ) ^ (-((|σ - σ'| : ℤ) : ℝ) / (100 * (J : ℝ))) *
        ((2 : ℝ) ^ (-(101 : ℝ)) * (2 : ℝ) ^ σ' * jb ((y₀ - dyCentre σ v) / (2 : ℝ) ^ σ) ^ (-(2 : ℝ))) ≤
      ∫ y, ovWeight 2 σ v y * muW J S ends σ y := by
  have hT := zpow_two_pos σ
  have hc : ∀ σ' ∈ S, (0 : ℝ) ≤ (2 : ℝ) ^ (-((|σ - σ'| : ℤ) : ℝ) / (100 * (J : ℝ))) := fun σ' _ =>
    Real.rpow_nonneg (by norm_num) _
  have e : ∀ x, ovWeight 2 σ v x * muW J S ends σ x = ∑ σ' ∈ S, ∑ y₀ ∈ ends σ',
      (2 : ℝ) ^ (-((|σ - σ'| : ℤ) : ℝ) / (100 * (J : ℝ))) *
        (ovWeight 2 σ v x * jb ((x - y₀) / (2 : ℝ) ^ σ') ^ (-(100 : ℝ))) := by
    intro x
    unfold muW
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ' _ => ?_
    rw [mul_left_comm, Finset.mul_sum, Finset.mul_sum]
  have hint : ∀ σ' y₀, Integrable (fun x => (2 : ℝ) ^ (-((|σ - σ'| : ℤ) : ℝ) / (100 * (J : ℝ))) *
      (ovWeight 2 σ v x * jb ((x - y₀) / (2 : ℝ) ^ σ') ^ (-(100 : ℝ)))) := fun σ' y₀ =>
    (integrable_weight_mul σ v σ' y₀).const_mul _
  have hInt : ∫ y, ovWeight 2 σ v y * muW J S ends σ y = ∑ σ' ∈ S, ∑ y₀ ∈ ends σ',
      (2 : ℝ) ^ (-((|σ - σ'| : ℤ) : ℝ) / (100 * (J : ℝ))) *
        ∫ x, ovWeight 2 σ v x * jb ((x - y₀) / (2 : ℝ) ^ σ') ^ (-(100 : ℝ)) := by
    simp_rw [e]
    rw [integral_finsetSum _ (fun σ' _ => integrable_finsetSum _ (fun y₀ _ => hint σ' y₀))]
    refine Finset.sum_congr rfl fun σ' _ => ?_
    rw [integral_finsetSum _ (fun y₀ _ => hint σ' y₀)]
    refine Finset.sum_congr rfl fun y₀ _ => ?_
    rw [integral_const_mul]
  rw [hInt]
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset (fun σ' : ℤ => σ' ≤ σ) S) (fun σ' hσ' _ =>
    Finset.sum_nonneg fun y₀ _ => mul_nonneg (hc σ' hσ') (integral_nonneg fun x => by
      have h0 : 0 ≤ ovWeight 2 σ v x := by
        unfold ovWeight; have := jb_pos ((x - (2 : ℝ) ^ σ * ((v : ℝ) + 1 / 2)) / (2 : ℝ) ^ σ); positivity
      have : 0 ≤ jb ((x - y₀) / (2 : ℝ) ^ σ') ^ (-(100 : ℝ)) := by
        have := jb_pos ((x - y₀) / (2 : ℝ) ^ σ'); positivity
      exact mul_nonneg h0 this)))
  refine Finset.sum_le_sum fun σ' hσ' => Finset.sum_le_sum fun y₀ _ => ?_
  have hσ'σ : σ' ≤ σ := (Finset.mem_filter.1 hσ').2
  have hL := zpow_two_pos σ'
  have hLT : (2 : ℝ) ^ σ' ≤ (2 : ℝ) ^ σ := zpow_le_zpow_right₀ (by norm_num) hσ'σ
  have := lower_weight (dyCentre σ v) y₀ hT hL hLT
  have e2 : ∫ x, ovWeight 2 σ v x * jb ((x - y₀) / (2 : ℝ) ^ σ') ^ (-(100 : ℝ)) =
      ∫ y, jb ((y - dyCentre σ v) / (2 : ℝ) ^ σ) ^ (-(2 : ℝ)) * jb ((y - y₀) / (2 : ℝ) ^ σ') ^ (-(100 : ℝ)) := rfl
  rw [e2]
  exact mul_le_mul_of_nonneg_left this (Real.rpow_nonneg (by norm_num) _)

theorem abs_sub_dyCentre_le {σ v : ℤ} {x₀ : ℝ} (hx₀ : x₀ ∈ dyadicInt σ v) : |x₀ - dyCentre σ v| ≤ (2 : ℝ) ^ σ / 2 := by
  have hp := zpow_two_pos σ
  unfold dyCentre
  obtain ⟨h1, h2⟩ := hx₀
  rw [abs_le]
  constructor <;> nlinarith

/-- **The fine sum is controlled by `a`.** -/
theorem fine_sum_le {J : ℕ} (hJ : 0 < J) (S : Finset ℤ) (ends : ℤ → Finset ℝ) (σ v : ℤ) (Lm : Finset ℤ)
    (hLm : ∀ τ ∈ Lm, τ + (J : ℤ) ≤ σ) (hS : ∀ τ ∈ Lm, (ends τ).Nonempty → τ ∈ S) {M : ℕ} (hM : 2 ≤ M) {x₀ : ℝ}
    (hx₀ : x₀ ∈ dyadicInt σ v) {Cc : ℝ} (hCc : 0 ≤ Cc) :
    ∑ τ ∈ Lm, ∑ x ∈ ends τ, Cc * ((2 : ℝ) ^ (τ - σ)) ^ 2 * jb ((x₀ - x) / (2 : ℝ) ^ σ) ^ (-(M : ℝ)) ≤
      Cc * ((2 : ℝ) ^ 101 * (3 / 2) ^ M) * ((2 : ℝ) ^ σ)⁻¹ * ∫ y, ovWeight 2 σ v y * muW J S ends σ y := by
  have hT := zpow_two_pos σ
  have hJ' : (0 : ℤ) < J := by exact_mod_cast hJ
  have hlow := integral_ovWeight_muW_lower J S ends σ v
  set c := dyCentre σ v with hc
  have hxc := abs_sub_dyCentre_le hx₀
  have hjc : jb ((x₀ - c) / (2 : ℝ) ^ σ) ≤ 3 / 2 := by
    unfold jb; rw [abs_div, abs_of_pos hT]
    have : |x₀ - c| / (2 : ℝ) ^ σ ≤ 1 / 2 := by
      rw [div_le_iff₀ hT]; linarith
    linarith
  -- per-term bound
  have hterm : ∀ τ ∈ Lm, ∀ x ∈ ends τ,
      Cc * ((2 : ℝ) ^ (τ - σ)) ^ 2 * jb ((x₀ - x) / (2 : ℝ) ^ σ) ^ (-(M : ℝ)) ≤
        (Cc * ((2 : ℝ) ^ 101 * (3 / 2) ^ M) * ((2 : ℝ) ^ σ)⁻¹) *
          ((2 : ℝ) ^ (-((|σ - τ| : ℤ) : ℝ) / (100 * (J : ℝ))) *
            ((2 : ℝ) ^ (-(101 : ℝ)) * (2 : ℝ) ^ τ * jb ((x - c) / (2 : ℝ) ^ σ) ^ (-(2 : ℝ)))) := by
    intro τ hτ x hx
    have hτσ := hLm τ hτ
    have hρ : (2 : ℝ) ^ (τ - σ) = (2 : ℝ) ^ τ * ((2 : ℝ) ^ σ)⁻¹ := by
      rw [zpow_sub₀ (by norm_num), div_eq_mul_inv]
    -- `(2^{τ-σ})^2 ≤ 2^{τ-σ} 2^{-|σ-τ|/(100J)}`
    have hexp : ((2 : ℝ) ^ (τ - σ)) ^ 2 ≤ (2 : ℝ) ^ (τ - σ) * (2 : ℝ) ^ (-((|σ - τ| : ℤ) : ℝ) / (100 * (J : ℝ))) := by
      have habs : |σ - τ| = σ - τ := abs_of_nonneg (by omega)
      rw [habs, sq]
      refine mul_le_mul_of_nonneg_left ?_ (zpow_nonneg (by norm_num) _)
      have h1 : (2 : ℝ) ^ (τ - σ) = (2 : ℝ) ^ (-((σ - τ : ℤ) : ℝ)) := by
        rw [← Real.rpow_intCast]; congr 1; push_cast; ring
      rw [h1]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hστ : (1 : ℝ) ≤ ((σ - τ : ℤ) : ℝ) := by
        have : (1 : ℤ) ≤ σ - τ := by omega
        exact_mod_cast this
      have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
      have hd : ((σ - τ : ℤ) : ℝ) / (100 * (J : ℝ)) ≤ ((σ - τ : ℤ) : ℝ) := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      rw [neg_div]
      linarith
    -- `⟨(x₀ - x)/T⟩^{-M} ≤ (3/2)^M ⟨(x - c)/T⟩^{-2}`
    have hjb : jb ((x - c) / (2 : ℝ) ^ σ) ≤ (3 / 2) * jb ((x₀ - x) / (2 : ℝ) ^ σ) := by
      have e : x - c = (x - x₀) + (x₀ - c) := by ring
      rw [e]
      refine (jb_div_add_le _ _ _ hT).trans ?_
      rw [jb_sub_comm x x₀]
      have := jb_pos ((x₀ - x) / (2 : ℝ) ^ σ)
      nlinarith
    have hjx : jb ((x₀ - x) / (2 : ℝ) ^ σ) ^ (-(M : ℝ)) ≤ (3 / 2) ^ M * jb ((x - c) / (2 : ℝ) ^ σ) ^ (-(2 : ℝ)) := by
      have h1 : jb ((x₀ - x) / (2 : ℝ) ^ σ) ≥ (2 / 3) * jb ((x - c) / (2 : ℝ) ^ σ) := by linarith
      have hp0 := jb_pos ((x - c) / (2 : ℝ) ^ σ)
      have h2 : jb ((x₀ - x) / (2 : ℝ) ^ σ) ^ (-(M : ℝ)) ≤ ((2 / 3) * jb ((x - c) / (2 : ℝ) ^ σ)) ^ (-(M : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by have := M.cast_nonneg (α := ℝ); linarith)
      refine h2.trans ?_
      rw [Real.mul_rpow (by norm_num) hp0.le]
      have h3 : ((2 : ℝ) / 3) ^ (-(M : ℝ)) = (3 / 2) ^ M := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]; rw [← inv_pow]; norm_num
      rw [h3]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
      exact Real.rpow_le_rpow_of_exponent_le (one_le_jb _) (by linarith)
    have hj0 := jb_pos ((x - c) / (2 : ℝ) ^ σ)
    have h101 : (2 : ℝ) ^ 101 * (2 : ℝ) ^ (-(101 : ℝ)) = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]; norm_num
    calc Cc * ((2 : ℝ) ^ (τ - σ)) ^ 2 * jb ((x₀ - x) / (2 : ℝ) ^ σ) ^ (-(M : ℝ))
        ≤ Cc * ((2 : ℝ) ^ (τ - σ) * (2 : ℝ) ^ (-((|σ - τ| : ℤ) : ℝ) / (100 * (J : ℝ)))) *
            ((3 / 2) ^ M * jb ((x - c) / (2 : ℝ) ^ σ) ^ (-(2 : ℝ))) := by
          have h0 : 0 ≤ jb ((x₀ - x) / (2 : ℝ) ^ σ) ^ (-(M : ℝ)) := by
            have := jb_pos ((x₀ - x) / (2 : ℝ) ^ σ); positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left hexp hCc) hjx h0 (by positivity)
      _ = (Cc * ((2 : ℝ) ^ 101 * (3 / 2) ^ M) * ((2 : ℝ) ^ σ)⁻¹) *
          ((2 : ℝ) ^ (-((|σ - τ| : ℤ) : ℝ) / (100 * (J : ℝ))) *
            ((2 : ℝ) ^ (-(101 : ℝ)) * (2 : ℝ) ^ τ * jb ((x - c) / (2 : ℝ) ^ σ) ^ (-(2 : ℝ)))) := by
          rw [hρ]
          have : (2 : ℝ) ^ 101 * (2 : ℝ) ^ (-(101 : ℝ)) = 1 := h101
          calc _ = Cc * ((3 / 2) ^ M) * ((2 : ℝ) ^ τ * ((2 : ℝ) ^ σ)⁻¹) *
                  ((2 : ℝ) ^ (-((|σ - τ| : ℤ) : ℝ) / (100 * (J : ℝ)))) * jb ((x - c) / (2 : ℝ) ^ σ) ^ (-(2 : ℝ)) := by ring
            _ = Cc * ((3 / 2) ^ M) * ((2 : ℝ) ^ τ * ((2 : ℝ) ^ σ)⁻¹) *
                  ((2 : ℝ) ^ (-((|σ - τ| : ℤ) : ℝ) / (100 * (J : ℝ)))) * jb ((x - c) / (2 : ℝ) ^ σ) ^ (-(2 : ℝ)) *
                  ((2 : ℝ) ^ 101 * (2 : ℝ) ^ (-(101 : ℝ))) := by rw [this, mul_one]
            _ = _ := by ring
  -- restrict to scales in `S`
  have hsub : ∑ τ ∈ Lm, ∑ x ∈ ends τ, Cc * ((2 : ℝ) ^ (τ - σ)) ^ 2 * jb ((x₀ - x) / (2 : ℝ) ^ σ) ^ (-(M : ℝ)) =
      ∑ τ ∈ Lm.filter (fun τ => τ ∈ S), ∑ x ∈ ends τ, Cc * ((2 : ℝ) ^ (τ - σ)) ^ 2 * jb ((x₀ - x) / (2 : ℝ) ^ σ) ^ (-(M : ℝ)) := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun τ hτ hτS => ?_
    have : ends τ = ∅ := by
      by_contra h
      exact hτS (Finset.mem_filter.2 ⟨hτ, hS τ hτ (Finset.nonempty_iff_ne_empty.2 h)⟩)
    simp [this]
  rw [hsub]
  have hpos : 0 ≤ (Cc * ((2 : ℝ) ^ 101 * (3 / 2) ^ M) * ((2 : ℝ) ^ σ)⁻¹) := by positivity
  calc ∑ τ ∈ Lm.filter (fun τ => τ ∈ S), ∑ x ∈ ends τ,
        Cc * ((2 : ℝ) ^ (τ - σ)) ^ 2 * jb ((x₀ - x) / (2 : ℝ) ^ σ) ^ (-(M : ℝ))
      ≤ ∑ τ ∈ Lm.filter (fun τ => τ ∈ S), ∑ x ∈ ends τ, (Cc * ((2 : ℝ) ^ 101 * (3 / 2) ^ M) * ((2 : ℝ) ^ σ)⁻¹) *
          ((2 : ℝ) ^ (-((|σ - τ| : ℤ) : ℝ) / (100 * (J : ℝ))) *
            ((2 : ℝ) ^ (-(101 : ℝ)) * (2 : ℝ) ^ τ * jb ((x - c) / (2 : ℝ) ^ σ) ^ (-(2 : ℝ)))) :=
        Finset.sum_le_sum fun τ hτ => Finset.sum_le_sum fun x hx => hterm τ (Finset.mem_filter.1 hτ).1 x hx
    _ = (Cc * ((2 : ℝ) ^ 101 * (3 / 2) ^ M) * ((2 : ℝ) ^ σ)⁻¹) *
        ∑ τ ∈ Lm.filter (fun τ => τ ∈ S), ∑ x ∈ ends τ, (2 : ℝ) ^ (-((|σ - τ| : ℤ) : ℝ) / (100 * (J : ℝ))) *
          ((2 : ℝ) ^ (-(101 : ℝ)) * (2 : ℝ) ^ τ * jb ((x - c) / (2 : ℝ) ^ σ) ^ (-(2 : ℝ))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Finset.mul_sum]
    _ ≤ (Cc * ((2 : ℝ) ^ 101 * (3 / 2) ^ M) * ((2 : ℝ) ^ σ)⁻¹) *
        ∑ τ ∈ S.filter (fun τ => τ ≤ σ), ∑ x ∈ ends τ, (2 : ℝ) ^ (-((|σ - τ| : ℤ) : ℝ) / (100 * (J : ℝ))) *
          ((2 : ℝ) ^ (-(101 : ℝ)) * (2 : ℝ) ^ τ * jb ((x - c) / (2 : ℝ) ^ σ) ^ (-(2 : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ hpos
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun τ _ _ => Finset.sum_nonneg fun x _ => by
          have := jb_pos ((x - c) / (2 : ℝ) ^ σ)
          positivity)
        intro τ hτ
        obtain ⟨hτL, hτS⟩ := Finset.mem_filter.1 hτ
        exact Finset.mem_filter.2 ⟨hτS, by have := hLm τ hτL; omega⟩
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow hpos

end PrimeBHT.TimeFrequency.X2
