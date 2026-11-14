module

public import PrimeBHT.TimeFrequency.X2.Psp.TreeHardAsm

/-!
# X2, V15 (assembly), step 8: the `μ_σ` sum of ERR₁

`sum_a_le`: with `a σ v = 2^{-σ} ∫ w_{I₀} μ_σ` (`I₀ = dyadicInt σ v`, the O2 factor) and `μ_σ = muW`,
`Σ_{σ ∈ S} Σ_v 2^σ a σ v ≤ C_w (24/99) muConst |I_t|`, `C_w = 2^2 Σ_{j ∈ ℤ} ⟨j⟩^{-2}`  (`Σ_v w_{I₀} ≤ C_w`, G-6).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

theorem ovWeight_nonneg (K₀ : ℝ) (σ v : ℤ) (y : ℝ) : 0 ≤ ovWeight K₀ σ v y :=
  Real.rpow_nonneg (jb_pos _).le _

theorem ovWeight_two_eq (σ v : ℤ) (y : ℝ) :
    ovWeight 2 σ v y = jb ((y / (2 : ℝ) ^ σ - 1 / 2) - (v : ℝ)) ^ (-(2 : ℝ)) := by
  unfold ovWeight
  have hp := zpow_two_pos σ
  congr 2
  field_simp
  ring

/-- `Σ_{v ∈ ℤ} w_{I₀(σ, v)}(y) ≤ C_w` (`K₀ = 2`). -/
theorem tsum_ovWeight_le (σ : ℤ) (y : ℝ) :
    ∑' v : ℤ, ENNReal.ofReal (ovWeight 2 σ v y) ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 : ℝ) * jbConst 2) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun V => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun v _ => ovWeight_nonneg 2 σ v y]
  refine ENNReal.ofReal_le_ofReal ?_
  simp_rw [ovWeight_two_eq]
  exact sum_jb_le (by norm_num) V _

theorem muW_nonneg (J : ℕ) (S : Finset ℤ) (ends : ℤ → Finset ℝ) (σ : ℤ) (x : ℝ) : 0 ≤ muW J S ends σ x := by
  unfold muW
  exact Finset.sum_nonneg fun σ' _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Finset.sum_nonneg fun y _ => Real.rpow_nonneg (jb_pos _).le _)

theorem integrable_muW (J : ℕ) (S : Finset ℤ) (ends : ℤ → Finset ℝ) (σ : ℤ) : Integrable (muW J S ends σ) := by
  unfold muW
  exact integrable_finsetSum _ fun σ' _ => (integrable_finsetSum _ fun y _ =>
    integrable_jb_inv_pow y (zpow_two_pos σ')).const_mul _

theorem continuous_muW (J : ℕ) (S : Finset ℤ) (ends : ℤ → Finset ℝ) (σ : ℤ) : Continuous (muW J S ends σ) := by
  unfold muW
  refine continuous_finsetSum _ fun σ' _ => continuous_const.mul (continuous_finsetSum _ fun y _ => ?_)
  exact continuous_jb_rpow y _ _

/-- The O2 factor. -/
def ovFactor (J : ℕ) (S : Finset ℤ) (ends : ℤ → Finset ℝ) (σ v : ℤ) : ℝ :=
  ((2 : ℝ) ^ σ)⁻¹ * ∫ y, ovWeight 2 σ v y * muW J S ends σ y

theorem ovFactor_nonneg (J : ℕ) (S : Finset ℤ) (ends : ℤ → Finset ℝ) (σ v : ℤ) : 0 ≤ ovFactor J S ends σ v :=
  mul_nonneg (inv_nonneg.2 (zpow_two_pos σ).le)
    (integral_nonneg fun y => mul_nonneg (ovWeight_nonneg 2 σ v y) (muW_nonneg J S ends σ y))

theorem sum_a_le {J : ℕ} (hJ : 0 < J) {s₀ : ℤ} {S : Finset ℤ} (hS : ∀ σ ∈ S, (J : ℤ) ∣ σ - s₀)
    (ends : ℤ → Finset ℝ) {T : Finset ℤ} (hT : T ⊆ S) (Tr : Finset TriTile) (W : ℤ × ℤ) (hends : ends = bdryEnds Tr W) :
    ∑ σ ∈ T, ∑' v : ℤ, ENNReal.ofReal ((2 : ℝ) ^ σ * ovFactor J S ends σ v) ≤
      ENNReal.ofReal (((2 : ℝ) ^ (2 : ℝ) * jbConst 2) * ((24 / 99) * muConst * (2 : ℝ) ^ W.1)) := by
  set Cw : ℝ := (2 : ℝ) ^ (2 : ℝ) * jbConst 2 with hCw
  have hCw0 : 0 ≤ Cw := by have := jbConst_nonneg 2; positivity
  have hloc : ∀ σ ∈ T, ∑' v : ℤ, ENNReal.ofReal ((2 : ℝ) ^ σ * ovFactor J S ends σ v) ≤
      ENNReal.ofReal (Cw * ∫ y, muW J S ends σ y) := by
    intro σ hσ
    have hp := zpow_two_pos σ
    have e : ∀ v : ℤ, (2 : ℝ) ^ σ * ovFactor J S ends σ v = ∫ y, ovWeight 2 σ v y * muW J S ends σ y := by
      intro v; unfold ovFactor; rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
    simp_rw [e]
    calc ∑' v : ℤ, ENNReal.ofReal (∫ y, ovWeight 2 σ v y * muW J S ends σ y)
        ≤ ∑' v : ℤ, ∫⁻ y, ENNReal.ofReal (ovWeight 2 σ v y * muW J S ends σ y) :=
          ENNReal.tsum_le_tsum fun v => ofReal_integral_le_lintegral fun y =>
            mul_nonneg (ovWeight_nonneg 2 σ v y) (muW_nonneg J S ends σ y)
      _ = ∫⁻ y, ∑' v : ℤ, ENNReal.ofReal (ovWeight 2 σ v y * muW J S ends σ y) := by
          rw [lintegral_tsum]
          intro v
          refine ENNReal.measurable_ofReal.comp ?_ |>.aemeasurable
          refine Measurable.mul ?_ (continuous_muW J S ends σ).measurable
          unfold ovWeight
          exact (continuous_jb_rpow _ _ _).measurable
      _ ≤ ∫⁻ y, ENNReal.ofReal (Cw * muW J S ends σ y) := by
          refine lintegral_mono fun y => ?_
          have : ∀ v : ℤ, ENNReal.ofReal (ovWeight 2 σ v y * muW J S ends σ y) =
              ENNReal.ofReal (ovWeight 2 σ v y) * ENNReal.ofReal (muW J S ends σ y) := fun v =>
            ENNReal.ofReal_mul (ovWeight_nonneg 2 σ v y)
          simp_rw [this]
          rw [ENNReal.tsum_mul_right, ENNReal.ofReal_mul hCw0]
          exact mul_le_mul' (tsum_ovWeight_le σ y) le_rfl
      _ = ENNReal.ofReal (∫ y, Cw * muW J S ends σ y) :=
          (ofReal_integral_eq_lintegral_ofReal ((integrable_muW J S ends σ).const_mul Cw)
            (Filter.Eventually.of_forall fun y => mul_nonneg hCw0 (muW_nonneg J S ends σ y))).symm
      _ = _ := by rw [integral_const_mul]
  calc ∑ σ ∈ T, ∑' v : ℤ, ENNReal.ofReal ((2 : ℝ) ^ σ * ovFactor J S ends σ v)
      ≤ ∑ σ ∈ T, ENNReal.ofReal (Cw * ∫ y, muW J S ends σ y) := Finset.sum_le_sum hloc
    _ = ENNReal.ofReal (∑ σ ∈ T, Cw * ∫ y, muW J S ends σ y) :=
        (ENNReal.ofReal_sum_of_nonneg fun σ _ => mul_nonneg hCw0
          (integral_nonneg fun y => muW_nonneg J S ends σ y)).symm
    _ ≤ ENNReal.ofReal (Cw * ((24 / 99) * muConst * (2 : ℝ) ^ W.1)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ hCw0
        calc ∑ σ ∈ T, ∫ y, muW J S ends σ y ≤ ∑ σ ∈ S, ∫ y, muW J S ends σ y :=
              Finset.sum_le_sum_of_subset_of_nonneg hT fun σ _ _ => integral_nonneg fun y => muW_nonneg J S ends σ y
          _ ≤ _ := by rw [hends]; exact sum_integral_muW_le_tree hJ hS Tr W

end PrimeBHT.TimeFrequency.X2
