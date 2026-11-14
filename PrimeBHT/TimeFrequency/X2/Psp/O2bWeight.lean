module

public import PrimeBHT.TimeFrequency.X2.Psp.TreeHardMu
public import PrimeBHT.TimeFrequency.X2.Psp.OverlapStmt

/-!
# X2, V13 O2 (b-weight): the arithmetic of the weight `a = ovFactor` and the reduction of `OvBound` to its sup conjunct

`docs/audits/X2-O2-coordination.md` §1 (C1), (C2).  Owner: V13 (this file); the analytic core (d1)-(d6) is V05's.

* `ovBound_of_sup`: `OvBound s q C a E σ v U` follows from its sup conjunct (the `L^q` conjunct is `|I₀|^{1/q}` times the sup);
* `ovSup_trivial_top`: the sup conjunct is trivial for `E = ⊤` when `C > 0` and `a > 0`; `ovFactor_pos`: `a > 0` when `σ ∈ S` and `∂Ẽ_σ ≠ ∅`;
* `ovFactor_eq_sum`: `a` as a sum over the scales `σ' ∈ S` and the endpoints `z ∈ ∂Ẽ_{σ'}`;
* `integral_ovWeight_mul_ge`: `∫ w_{I₀}(y) ⟨(y - z)/2^{σ'}⟩^{-100} dy ≥ 2^{-101} 2^{σ'} w_{I₀}(z)` for `σ' ≤ σ`;
* `sum_endpoint_le_ovFactor`: for `x₀ ∈ I₀`, `M ≥ 2`, `J ≥ 1`:
  `Σ_{σ' ∈ S, σ' ≤ σ} Σ_{z ∈ ends σ'} (2^{σ'-σ})² ⟨(x₀ - z)/2^σ⟩^{-M} ≤ 2^{103} a`
  (the sum of the `endpoint_bound` terms is controlled by the factor `a` of `OverlapO2Ovg`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-- **C1**: the `L^q(I₀)` conjunct of `OvBound` follows from the sup conjunct (and measurability of `‖U‖`). -/
theorem ovBound_of_sup {P : ℕ} [NeZero P] {s q C a : ℝ} (hq : 0 < q) (hC : 0 ≤ C) (ha : 0 ≤ a) {E : ℝ≥0∞} {σ v : ℤ}
    {U : ℝ → ZMod P → ℂ} (hU : Measurable fun x => yNorm s (U x))
    (hsup : ∀ x ∈ dyadicInt σ v, ENNReal.ofReal (yNorm s (U x)) ≤ ENNReal.ofReal (C * a) * E) :
    OvBound s q C a E σ v U := by
  refine ⟨hsup, ?_⟩
  set B : ℝ≥0∞ := ENNReal.ofReal (C * a) * E with hB
  have hp := zpow_two_pos σ
  have ht : 0 < ((2 : ℝ) ^ σ) ^ (1 / q) := Real.rpow_pos_of_pos hp _
  have hRHS : ENNReal.ofReal (C * a * ((2 : ℝ) ^ σ) ^ (1 / q)) * E = B * ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (1 / q)) := by
    rw [ENNReal.ofReal_mul (mul_nonneg hC ha), hB]; ring
  rw [hRHS]
  by_cases hBtop : B = ⊤
  · rw [hBtop, ENNReal.top_mul (ENNReal.ofReal_pos.2 ht).ne']
    exact le_top
  · have hb0 : 0 ≤ B.toReal := ENNReal.toReal_nonneg
    have hBe : B = ENNReal.ofReal B.toReal := (ENNReal.ofReal_toReal hBtop).symm
    have hae : ∀ᵐ x ∂(volume.restrict (dyadicInt σ v)), ‖yNorm s (U x)‖ ≤ B.toReal := by
      refine (ae_restrict_iff' (measurableSet_dyadicInt σ v)).2 (Filter.Eventually.of_forall fun x hx => ?_)
      rw [Real.norm_of_nonneg (yNorm_nonneg' _ _)]
      exact (ENNReal.ofReal_le_ofReal_iff hb0).1 ((hsup x hx).trans (le_of_eq hBe))
    have h1 : eLpNorm (fun x => (dyadicInt σ v).indicator (fun x => yNorm s (U x)) x) (ENNReal.ofReal q) volume =
        eLpNorm (fun x => yNorm s (U x)) (ENNReal.ofReal q) (volume.restrict (dyadicInt σ v)) :=
      eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_dyadicInt σ v).nullMeasurableSet
    rw [h1]
    refine (eLpNorm_le_of_ae_bound hU.aestronglyMeasurable hae).trans ?_
    rw [Measure.restrict_apply_univ, volume_dyadicInt, ENNReal.toReal_ofReal hq.le, one_div,
      ENNReal.ofReal_rpow_of_pos hp, mul_comm, ← hBe]

/-- The sup conjunct is trivial for `E = ⊤` (needs `C a > 0`; `ofReal 0 * ⊤ = 0`). -/
theorem ovSup_trivial_top {P : ℕ} [NeZero P] {s C a : ℝ} (hC : 0 < C) (ha : 0 < a) {σ v : ℤ} {U : ℝ → ZMod P → ℂ} :
    ∀ x ∈ dyadicInt σ v, ENNReal.ofReal (yNorm s (U x)) ≤ ENNReal.ofReal (C * a) * (⊤ : ℝ≥0∞) := by
  intro x _
  rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 (mul_pos hC ha)).ne']
  exact le_top

theorem jb_rpow_neg_nat (t : ℝ) (n : ℕ) : jb t ^ (-(n : ℝ)) = (jb t ^ n)⁻¹ := by
  rw [Real.rpow_neg (jb_pos t).le, Real.rpow_natCast]

theorem ovWeight_eq (σ v : ℤ) (y : ℝ) :
    ovWeight 2 σ v y = (jb ((y - (2 : ℝ) ^ σ * ((v : ℝ) + 1 / 2)) / (2 : ℝ) ^ σ) ^ 2)⁻¹ := by
  unfold ovWeight
  rw [Real.rpow_neg (jb_pos _).le, Real.rpow_two]

theorem jb_le_two_of_abs_le {t : ℝ} (h : |t| ≤ 1) : jb t ≤ 2 := by unfold jb; linarith

theorem ovWeight_ge_of_near {σ v σ' : ℤ} (hle : σ' ≤ σ) {z y : ℝ} (hy : |y - z| ≤ (2 : ℝ) ^ σ') :
    (1 / 4) * ovWeight 2 σ v z ≤ ovWeight 2 σ v y := by
  have hp := zpow_two_pos σ
  set c : ℝ := (2 : ℝ) ^ σ * ((v : ℝ) + 1 / 2) with hc
  have hab : (y - c) / (2 : ℝ) ^ σ = (z - c) / (2 : ℝ) ^ σ + (y - z) / (2 : ℝ) ^ σ := by field_simp; ring
  have hb : |(y - z) / (2 : ℝ) ^ σ| ≤ 1 := by
    rw [abs_div, abs_of_pos hp, div_le_one hp]
    exact hy.trans (zpow_le_zpow_right₀ (by norm_num) hle)
  have h1 : jb ((y - c) / (2 : ℝ) ^ σ) ≤ 2 * jb ((z - c) / (2 : ℝ) ^ σ) := by
    rw [hab]
    calc jb ((z - c) / (2 : ℝ) ^ σ + (y - z) / (2 : ℝ) ^ σ) ≤ jb ((z - c) / (2 : ℝ) ^ σ) * jb ((y - z) / (2 : ℝ) ^ σ) :=
          jb_add_le _ _
      _ ≤ jb ((z - c) / (2 : ℝ) ^ σ) * 2 :=
          mul_le_mul_of_nonneg_left (jb_le_two_of_abs_le hb) (jb_pos _).le
      _ = _ := by ring
  rw [ovWeight_eq, ovWeight_eq]
  have h2 : jb ((y - c) / (2 : ℝ) ^ σ) ^ 2 ≤ 4 * jb ((z - c) / (2 : ℝ) ^ σ) ^ 2 := by
    calc jb ((y - c) / (2 : ℝ) ^ σ) ^ 2 ≤ (2 * jb ((z - c) / (2 : ℝ) ^ σ)) ^ 2 :=
          pow_le_pow_left₀ (jb_pos _).le h1 2
      _ = _ := by ring
  have h3 : (4 * jb ((z - c) / (2 : ℝ) ^ σ) ^ 2)⁻¹ ≤ (jb ((y - c) / (2 : ℝ) ^ σ) ^ 2)⁻¹ :=
    inv_anti₀ (pow_pos (jb_pos _) 2) h2
  calc 1 / 4 * (jb ((z - c) / (2 : ℝ) ^ σ) ^ 2)⁻¹ = (4 * jb ((z - c) / (2 : ℝ) ^ σ) ^ 2)⁻¹ := by
        rw [mul_inv]; ring
    _ ≤ _ := h3

theorem integrable_ovWeight_mul (σ v σ' : ℤ) (z : ℝ) :
    Integrable (fun y => ovWeight 2 σ v y * jb ((y - z) / (2 : ℝ) ^ σ') ^ (-100 : ℝ)) := by
  have hint := integrable_jb_inv_pow z (zpow_two_pos σ')
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · refine Measurable.aestronglyMeasurable (Measurable.mul ?_ (continuous_jb_rpow _ _ _).measurable)
    unfold ovWeight
    exact (continuous_jb_rpow _ _ _).measurable
  · have h1 : ovWeight 2 σ v y ≤ 1 := by
      rw [ovWeight_eq]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (one_le_jb _))
    have h0 := ovWeight_nonneg 2 σ v y
    have h2 : 0 ≤ jb ((y - z) / (2 : ℝ) ^ σ') ^ (-100 : ℝ) := Real.rpow_nonneg (jb_pos _).le _
    rw [Real.norm_of_nonneg (mul_nonneg h0 h2)]
    exact mul_le_of_le_one_left h2 h1

/-- Lower bound of the `μ_σ`-integral against ONE endpoint `z` of scale `σ' ≤ σ`. -/
theorem integral_ovWeight_mul_ge {σ v σ' : ℤ} (hle : σ' ≤ σ) (z : ℝ) :
    (1 / 2 ^ 101) * (2 : ℝ) ^ σ' * ovWeight 2 σ v z ≤
      ∫ y, ovWeight 2 σ v y * jb ((y - z) / (2 : ℝ) ^ σ') ^ (-100 : ℝ) := by
  have hp' := zpow_two_pos σ'
  have hint := integrable_ovWeight_mul σ v σ' z
  have hnn : ∀ y, 0 ≤ ovWeight 2 σ v y * jb ((y - z) / (2 : ℝ) ^ σ') ^ (-100 : ℝ) := fun y =>
    mul_nonneg (ovWeight_nonneg 2 σ v y) (Real.rpow_nonneg (jb_pos _).le _)
  set s : Set ℝ := Set.Icc (z - (2 : ℝ) ^ σ') (z + (2 : ℝ) ^ σ') with hs
  have h1 : ∫ y in s, ovWeight 2 σ v y * jb ((y - z) / (2 : ℝ) ^ σ') ^ (-100 : ℝ) ≤
      ∫ y, ovWeight 2 σ v y * jb ((y - z) / (2 : ℝ) ^ σ') ^ (-100 : ℝ) :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)
  refine le_trans ?_ h1
  set k : ℝ := (1 / 2 ^ 100) * ((1 / 4) * ovWeight 2 σ v z) with hk
  have h2 : ∫ y in s, k ≤ ∫ y in s, ovWeight 2 σ v y * jb ((y - z) / (2 : ℝ) ^ σ') ^ (-100 : ℝ) := by
    refine setIntegral_mono_on (integrableOn_const (by simp [hs])) hint.integrableOn measurableSet_Icc fun y hy => ?_
    have hyz : |y - z| ≤ (2 : ℝ) ^ σ' := by
      rw [abs_le]; constructor <;> [linarith [hy.1]; linarith [hy.2]]
    have hjb : jb ((y - z) / (2 : ℝ) ^ σ') ≤ 2 := by
      refine jb_le_two_of_abs_le ?_
      rw [abs_div, abs_of_pos hp', div_le_one hp']; exact hyz
    have hw := ovWeight_ge_of_near (v := v) hle hyz
    have h100 : 1 / 2 ^ 100 ≤ jb ((y - z) / (2 : ℝ) ^ σ') ^ (-100 : ℝ) := by
      have := jb_rpow_neg_nat ((y - z) / (2 : ℝ) ^ σ') 100
      rw [show (-(100 : ℝ)) = -((100 : ℕ) : ℝ) by norm_num] at *
      rw [this, one_div]
      exact inv_anti₀ (pow_pos (jb_pos _) 100) (pow_le_pow_left₀ (jb_pos _).le hjb 100)
    calc k = (1 / 2 ^ 100) * ((1 / 4) * ovWeight 2 σ v z) := rfl
      _ ≤ jb ((y - z) / (2 : ℝ) ^ σ') ^ (-100 : ℝ) * ovWeight 2 σ v y :=
          mul_le_mul h100 hw (by have := ovWeight_nonneg 2 σ v z; positivity)
            (Real.rpow_nonneg (jb_pos _).le _)
      _ = _ := by ring
  refine le_trans (le_of_eq ?_) h2
  rw [setIntegral_const, hs, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, hk]
  field_simp
  ring

/-- `ovFactor` as a sum over the endpoints. -/
theorem ovFactor_eq_sum (J : ℕ) (S : Finset ℤ) (ends : ℤ → Finset ℝ) (σ v : ℤ) :
    ovFactor J S ends σ v = ((2 : ℝ) ^ σ)⁻¹ * ∑ σ' ∈ S, (2 : ℝ) ^ (-((|σ - σ'| : ℤ) : ℝ) / (100 * (J : ℝ))) *
      ∑ z ∈ ends σ', ∫ y, ovWeight 2 σ v y * jb ((y - z) / (2 : ℝ) ^ σ') ^ (-100 : ℝ) := by
  unfold ovFactor
  congr 1
  have hf : ∀ y, ovWeight 2 σ v y * muW J S ends σ y = ∑ σ' ∈ S, ∑ z ∈ ends σ',
      (2 : ℝ) ^ (-((|σ - σ'| : ℤ) : ℝ) / (100 * (J : ℝ))) * (ovWeight 2 σ v y * jb ((y - z) / (2 : ℝ) ^ σ') ^ (-100 : ℝ)) := by
    intro y
    unfold muW
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ' _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring
  simp_rw [hf]
  rw [integral_finsetSum _ (fun σ' _ => integrable_finsetSum _ (fun z _ =>
    (integrable_ovWeight_mul σ v σ' z).const_mul _))]
  refine Finset.sum_congr rfl fun σ' _ => ?_
  rw [integral_finsetSum _ (fun z _ => (integrable_ovWeight_mul σ v σ' z).const_mul _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [integral_const_mul]

/-- `a = ovFactor > 0` when `σ ∈ S` and `∂Ẽ_σ ≠ ∅`. -/
theorem ovFactor_pos (J : ℕ) {S : Finset ℤ} {ends : ℤ → Finset ℝ} {σ v : ℤ} (hσ : σ ∈ S) (hne : (ends σ).Nonempty) :
    0 < ovFactor J S ends σ v := by
  obtain ⟨z, hz⟩ := hne
  have hp := zpow_two_pos σ
  rw [ovFactor_eq_sum]
  refine mul_pos (inv_pos.2 hp) ?_
  set g : ℤ → ℝ := fun σ' => (2 : ℝ) ^ (-((|σ - σ'| : ℤ) : ℝ) / (100 * (J : ℝ))) *
    ∑ z ∈ ends σ', ∫ y, ovWeight 2 σ v y * jb ((y - z) / (2 : ℝ) ^ σ') ^ (-100 : ℝ) with hg
  have hg0 : ∀ σ' ∈ S, 0 ≤ g σ' := fun σ' _ =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Finset.sum_nonneg fun z _ => integral_nonneg fun y =>
      mul_nonneg (ovWeight_nonneg 2 σ v y) (Real.rpow_nonneg (jb_pos _).le _))
  have h1 : g σ ≤ ∑ σ' ∈ S, g σ' := Finset.single_le_sum hg0 hσ
  refine lt_of_lt_of_le ?_ h1
  have hI := integral_ovWeight_mul_ge (v := v) (le_refl σ) z
  set f : ℝ → ℝ := fun z => ∫ y, ovWeight 2 σ v y * jb ((y - z) / (2 : ℝ) ^ σ) ^ (-100 : ℝ) with hf
  have hf0 : ∀ z ∈ ends σ, 0 ≤ f z := fun z _ => integral_nonneg fun y =>
    mul_nonneg (ovWeight_nonneg 2 σ v y) (Real.rpow_nonneg (jb_pos _).le _)
  have h2 : f z ≤ ∑ z ∈ ends σ, f z := Finset.single_le_sum hf0 hz
  have how : 0 < ovWeight 2 σ v z := by rw [ovWeight_eq]; exact inv_pos.2 (pow_pos (jb_pos _) 2)
  have h3 : 0 < f z := lt_of_lt_of_le (by positivity) hI
  have hc : 0 < (2 : ℝ) ^ (-((|σ - σ| : ℤ) : ℝ) / (100 * (J : ℝ))) := Real.rpow_pos_of_pos (by norm_num) _
  show 0 < (2 : ℝ) ^ (-((|σ - σ| : ℤ) : ℝ) / (100 * (J : ℝ))) * ∑ z ∈ ends σ, f z
  exact mul_pos hc (lt_of_lt_of_le h3 h2)

/-- `a = ovFactor ≥ 2^{-101} w_{I₀}(z)` for every endpoint `z ∈ ∂Ẽ_σ` of the layer scale `σ ∈ S` (the `σ' = σ` term). -/
theorem ovFactor_ge_self (J : ℕ) {S : Finset ℤ} {ends : ℤ → Finset ℝ} {σ v : ℤ} (hσ : σ ∈ S) {z : ℝ} (hz : z ∈ ends σ) :
    (1 / 2 ^ 101) * ovWeight 2 σ v z ≤ ovFactor J S ends σ v := by
  have hp := zpow_two_pos σ
  rw [ovFactor_eq_sum]
  set g : ℤ → ℝ := fun σ' => (2 : ℝ) ^ (-((|σ - σ'| : ℤ) : ℝ) / (100 * (J : ℝ))) *
    ∑ z ∈ ends σ', ∫ y, ovWeight 2 σ v y * jb ((y - z) / (2 : ℝ) ^ σ') ^ (-100 : ℝ) with hg
  have hg0 : ∀ σ' ∈ S, 0 ≤ g σ' := fun σ' _ =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Finset.sum_nonneg fun z _ => integral_nonneg fun y =>
      mul_nonneg (ovWeight_nonneg 2 σ v y) (Real.rpow_nonneg (jb_pos _).le _))
  have h1 : g σ ≤ ∑ σ' ∈ S, g σ' := Finset.single_le_sum hg0 hσ
  set f : ℝ → ℝ := fun z => ∫ y, ovWeight 2 σ v y * jb ((y - z) / (2 : ℝ) ^ σ) ^ (-100 : ℝ) with hf
  have hf0 : ∀ z ∈ ends σ, 0 ≤ f z := fun z _ => integral_nonneg fun y =>
    mul_nonneg (ovWeight_nonneg 2 σ v y) (Real.rpow_nonneg (jb_pos _).le _)
  have h2 : f z ≤ ∑ z ∈ ends σ, f z := Finset.single_le_sum hf0 hz
  have hI := integral_ovWeight_mul_ge (v := v) (le_refl σ) z
  have hgσ : g σ = ∑ z ∈ ends σ, f z := by
    show (2 : ℝ) ^ (-((|σ - σ| : ℤ) : ℝ) / (100 * (J : ℝ))) * ∑ z ∈ ends σ, f z = _
    simp
  have h3 : (1 / 2 ^ 101) * (2 : ℝ) ^ σ * ovWeight 2 σ v z ≤ g σ := by rw [hgσ]; exact hI.trans h2
  calc (1 / 2 ^ 101) * ovWeight 2 σ v z = ((2 : ℝ) ^ σ)⁻¹ * ((1 / 2 ^ 101) * (2 : ℝ) ^ σ * ovWeight 2 σ v z) := by
        field_simp
    _ ≤ ((2 : ℝ) ^ σ)⁻¹ * ∑ σ' ∈ S, g σ' := by gcongr; exact h3.trans h1

end PrimeBHT.TimeFrequency.X2
