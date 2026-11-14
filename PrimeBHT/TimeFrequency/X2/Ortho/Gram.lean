module

public import PrimeBHT.TimeFrequency.X2.Ortho.Weights

/-!
# X2, node V10: the Gram integrals `J(R,R') = ∫ w_R w_{R'}`, `w = wt 6 c ℓ`

* `J_le`: `∫ wt 6 c ℓ · wt 6 c' ℓ' ≤ 8 ℓ' wt 3 c ℓ (y)` for `ℓ' ≤ ℓ`, `|y - c'| ≤ ℓ'` (localization);
* `J_le_setIntegral`: for `c' = a + ℓ'/2` the centre of `I' = [a, a + ℓ')`: `J ≤ 8 ∫_{I'} wt 3 c ℓ`;
* `J_same`: same length, `J ≤ 8 ℓ wt 3 c ℓ (c')`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

theorem wt_six_le_three (c ℓ x : ℝ) (hℓ : 0 < ℓ) : wt 6 c ℓ x ≤ wt 3 c ℓ x := by
  unfold wt
  have h : 1 ≤ 1 + |x - c| / ℓ := by have := div_nonneg (abs_nonneg (x - c)) hℓ.le; linarith
  exact Real.rpow_le_rpow_of_exponent_le h (by norm_num)

/-- Localization of the Gram integral. -/
theorem J_le {c ℓ c' ℓ' y : ℝ} (hℓ' : 0 < ℓ') (hle : ℓ' ≤ ℓ) (hy : |y - c'| ≤ ℓ') :
    ∫ x, wt 6 c ℓ x * wt 6 c' ℓ' x ≤ 8 * ℓ' * wt 3 c ℓ y := by
  have hℓ : 0 < ℓ := lt_of_lt_of_le hℓ' hle
  have h1 := integral_wt_mul_le (q := 3) (by norm_num) hℓ' hle hy (c := c) (c' := c')
  have e : (2 : ℝ) * 3 = 6 := by norm_num
  rw [e] at h1
  have h2 : 2 ^ (3 : ℝ) * (2 * ℓ' / (3 - 1)) = 8 * ℓ' := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  rw [h2] at h1
  refine le_trans ?_ h1
  refine integral_mono ?_ ?_ fun x => ?_
  · refine Integrable.mono' ((integrable_wt (q := 3) (by norm_num) c hℓ))
      ((continuous_wt 6 c ℓ hℓ).mul (continuous_wt 6 c' ℓ' hℓ')).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (wt_pos _ _ _ _ hℓ).le (wt_pos _ _ _ _ hℓ').le)]
    calc wt 6 c ℓ x * wt 6 c' ℓ' x ≤ wt 3 c ℓ x * 1 :=
          mul_le_mul (wt_six_le_three c ℓ x hℓ) (wt_le_one (by norm_num) _ _ _ hℓ') (wt_pos _ _ _ _ hℓ').le
            (wt_pos _ _ _ _ hℓ).le
      _ = wt 3 c ℓ x := mul_one _
  · -- integrable majorant: `wt 3 c ℓ · wt 6 c' ℓ'`
    refine Integrable.mono' (integrable_wt (q := 3) (by norm_num) c hℓ)
      ((continuous_wt 3 c ℓ hℓ).mul (continuous_wt 6 c' ℓ' hℓ')).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (wt_pos _ _ _ _ hℓ).le (wt_pos _ _ _ _ hℓ').le)]
    calc wt 3 c ℓ x * wt 6 c' ℓ' x ≤ wt 3 c ℓ x * 1 :=
          mul_le_mul_of_nonneg_left (wt_le_one (by norm_num) _ _ _ hℓ') (wt_pos _ _ _ _ hℓ).le
      _ = wt 3 c ℓ x := mul_one _
  · exact mul_le_mul_of_nonneg_right (wt_six_le_three c ℓ x hℓ) (wt_pos _ _ _ _ hℓ').le

theorem J_same {c ℓ c' : ℝ} (hℓ : 0 < ℓ) :
    ∫ x, wt 6 c ℓ x * wt 6 c' ℓ x ≤ 8 * ℓ * wt 3 c ℓ c' :=
  J_le hℓ le_rfl (by simp [hℓ.le])

/-- `J ≤ 8 ∫_{I'} wt 3 c ℓ` for `I' = [a, a + ℓ')` with centre `c'`, `ℓ' ≤ ℓ`. -/
theorem J_le_setIntegral {c ℓ a ℓ' : ℝ} (hℓ' : 0 < ℓ') (hle : ℓ' ≤ ℓ) :
    ∫ x, wt 6 c ℓ x * wt 6 (a + ℓ' / 2) ℓ' x ≤ 8 * ∫ y in Set.Ico a (a + ℓ'), wt 3 c ℓ y := by
  have hℓ : 0 < ℓ := lt_of_lt_of_le hℓ' hle
  set J := ∫ x, wt 6 c ℓ x * wt 6 (a + ℓ' / 2) ℓ' x with hJ
  have hpt : ∀ y ∈ Set.Ico a (a + ℓ'), J ≤ 8 * ℓ' * wt 3 c ℓ y := by
    intro y hy
    refine J_le hℓ' hle ?_
    rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
  have hvol : (volume (Set.Ico a (a + ℓ'))).toReal = ℓ' := by
    rw [Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]; ring
  have hint : IntegrableOn (wt 3 c ℓ) (Set.Ico a (a + ℓ')) :=
    (integrable_wt (q := 3) (by norm_num) c hℓ).integrableOn
  have h1 : ∫ y in Set.Ico a (a + ℓ'), J ≤ ∫ y in Set.Ico a (a + ℓ'), 8 * ℓ' * wt 3 c ℓ y := by
    refine setIntegral_mono_on (by simp [Real.volume_Ico]) (hint.const_mul _) measurableSet_Ico hpt
  rw [setIntegral_const, integral_const_mul, Measure.real, hvol, smul_eq_mul] at h1
  have : ℓ' * J ≤ ℓ' * (8 * ∫ y in Set.Ico a (a + ℓ'), wt 3 c ℓ y) := by linarith
  exact le_of_mul_le_mul_left this hℓ'

end PrimeBHT.TimeFrequency.X2

namespace PrimeBHT.TimeFrequency.X2

/-- Intervals of multiplicity `≤ 2` disjoint from `S`: `∑ ∫_{I_i} w ≤ 2 ∫_{Sᶜ} w`. -/
theorem sum_setIntegral_le {ι : Type*} [DecidableEq ι] (N : Finset ι) (I : ι → Set ℝ) (S : Set ℝ)
    {w : ℝ → ℝ} (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x) (hI : ∀ i ∈ N, MeasurableSet (I i))
    (hS : MeasurableSet S) (hdisj : ∀ i ∈ N, Disjoint (I i) S)
    (hmult : ∀ x, ∀ a ∈ N, ∀ b ∈ N, ∀ c ∈ N, a ≠ b → a ≠ c → b ≠ c → x ∈ I a → x ∈ I b → x ∈ I c → False) :
    ∑ i ∈ N, ∫ x in I i, w x ≤ 2 * ∫ x in Sᶜ, w x := by
  classical
  have h1 : ∀ i ∈ N, ∫ x in I i, w x = ∫ x, (I i).indicator w x := fun i hi =>
    (integral_indicator (hI i hi)).symm
  rw [Finset.sum_congr rfl h1, ← integral_finsetSum _ fun i hi => hw.indicator (hI i hi),
    ← integral_indicator hS.compl, ← integral_const_mul]
  refine integral_mono (integrable_finsetSum _ fun i hi => hw.indicator (hI i hi))
    ((hw.indicator hS.compl).const_mul 2) fun x => ?_
  by_cases hx : x ∈ S
  · have : ∀ i ∈ N, (I i).indicator w x = 0 := fun i hi =>
      Set.indicator_of_notMem (fun h => Set.disjoint_left.1 (hdisj i hi) h hx) _
    rw [Finset.sum_eq_zero this, Set.indicator_of_notMem (by simpa using hx)]
    exact le_of_eq (by ring)
  · rw [Set.indicator_of_mem (by simpa using hx)]
    have hcard : (N.filter (fun i => x ∈ I i)).card ≤ 2 := by
      by_contra hc
      push Not at hc
      obtain ⟨a, b, c, ha, hb, hc', hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 hc
      simp only [Finset.mem_filter] at ha hb hc'
      exact hmult x a ha.1 b hb.1 c hc'.1 hab hac hbc ha.2 hb.2 hc'.2
    have : ∑ i ∈ N, (I i).indicator w x = (N.filter (fun i => x ∈ I i)).card * w x := by
      rw [Finset.sum_congr rfl (fun i _ => (Set.indicator_apply (I i) w x))]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [this]
    have hc2 : ((N.filter (fun i => x ∈ I i)).card : ℝ) ≤ 2 := by exact_mod_cast hcard
    exact mul_le_mul_of_nonneg_right hc2 (hw0 x)

end PrimeBHT.TimeFrequency.X2
