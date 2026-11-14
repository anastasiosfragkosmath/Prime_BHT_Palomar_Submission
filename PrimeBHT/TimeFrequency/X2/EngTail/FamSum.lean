module

public import PrimeBHT.TimeFrequency.Tile.Maximal
public import PrimeBHT.TimeFrequency.Tile.Gram.Pair
public import PrimeBHT.TimeFrequency.X2.CZ.CZDecomp
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# X2, node B5: the family-sum (Hardy-Littlewood) lemma

For pairwise disjoint intervals `J_i = [c_i - ℓ_i/2, c_i + ℓ_i/2)` and `a_i ≥ 0`,
`Φ = ∑_i a_i (1 + |x - c_i|/ℓ_i)^{-2}` satisfies `‖Φ‖_{L^q} ≤ C_q (∑_i a_i^q ℓ_i)^{1/q}` (`1 < q < ∞`).

Proof: dual form `∫ Φ W ≤ 23 ∫ A · M W` (`∫ φ_i W ≤ 23 ∫_{J_i} M W`, kernel domination by the maximal function), Hölder and the
maximal theorem, then `W = Φ^{q-1}` (self-duality).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

open PrimeCarleson.Proof.Common
open PrimeBHT.TimeFrequency.Tile

/-- The family kernel `φ_{c,ℓ}(y) = (1 + |y - c|/ℓ)^{-2}`. -/
def famK (c ℓ y : ℝ) : ℝ := (1 + |y - c| / ℓ) ^ (-(2 : ℝ))

theorem famK_nonneg (c y : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) : 0 ≤ famK c ℓ y := by
  unfold famK; positivity

/-- `∫ φ_{c,ℓ} W ≤ 23 ℓ M W(x')` for every `x'` in the interval `[c - ℓ/2, c + ℓ/2)`. -/
theorem lintegral_famK_mul_le {c ℓ : ℝ} (hℓ : 0 < ℓ) {W : ℝ → ℝ≥0∞} (hW : Measurable W) {x' : ℝ}
    (hx' : x' ∈ Ico (c - ℓ / 2) (c + ℓ / 2)) :
    ∫⁻ y, ENNReal.ofReal (famK c ℓ y) * W y ≤ ENNReal.ofReal (23 * ℓ) * maximalHLR W x' := by
  have h := PrimeBHT.TimeFrequency.Tile.lintegral_kernel_le_maximalHLR hℓ x' hW
  have hxc : |x' - c| ≤ ℓ / 2 := by
    rw [abs_le]; constructor <;> linarith [hx'.1, hx'.2]
  have hpt : ∀ y, ENNReal.ofReal (famK c ℓ y) ≤ ENNReal.ofReal (9 / 4 * ℓ) *
      ENNReal.ofReal (ℓ⁻¹ * (1 + |x' - y| / ℓ) ^ (-2 : ℤ)) := by
    intro y
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold famK
    have h1 : 0 < 1 + |y - c| / ℓ := by positivity
    have h2 : 0 < 1 + |x' - y| / ℓ := by positivity
    have hle : (2 / 3) * (1 + |x' - y| / ℓ) ≤ 1 + |y - c| / ℓ := by
      have h3 : |x' - y| ≤ |y - c| + |x' - c| := by
        calc |x' - y| = |(x' - c) - (y - c)| := by ring_nf
          _ ≤ |x' - c| + |y - c| := abs_sub _ _
          _ = |y - c| + |x' - c| := add_comm _ _
      have h4 : |x' - y| / ℓ ≤ |y - c| / ℓ + 1 / 2 := by
        rw [div_le_iff₀ hℓ]
        have : (|y - c| / ℓ + 1 / 2) * ℓ = |y - c| + ℓ / 2 := by field_simp
        rw [this]; linarith
      have h5 : 0 ≤ |y - c| / ℓ := by positivity
      linarith
    have hr : (1 + |y - c| / ℓ) ^ (-(2 : ℝ)) ≤ ((2 / 3) * (1 + |x' - y| / ℓ)) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hle (by norm_num : (-(2 : ℝ)) ≤ 0)
    refine hr.trans (le_of_eq ?_)
    rw [Real.mul_rpow (by norm_num) h2.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2 / 3),
      Real.rpow_neg h2.le, zpow_neg, zpow_ofNat, Real.rpow_two, Real.rpow_two]
    field_simp
    norm_num
  calc ∫⁻ y, ENNReal.ofReal (famK c ℓ y) * W y
      ≤ ∫⁻ y, ENNReal.ofReal (9 / 4 * ℓ) * (ENNReal.ofReal (ℓ⁻¹ * (1 + |x' - y| / ℓ) ^ (-2 : ℤ)) * W y) := by
        refine lintegral_mono fun y => ?_
        rw [← mul_assoc]
        exact mul_le_mul' (hpt y) le_rfl
    _ = ENNReal.ofReal (9 / 4 * ℓ) * ∫⁻ y, ENNReal.ofReal (ℓ⁻¹ * (1 + |x' - y| / ℓ) ^ (-2 : ℤ)) * W y :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (9 / 4 * ℓ) * (10 * maximalHLR W x') := mul_le_mul' le_rfl h
    _ = ENNReal.ofReal (9 / 4 * ℓ * 10) * maximalHLR W x' := by
        rw [← mul_assoc, ← ENNReal.ofReal_ofNat 10, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (23 * ℓ) * maximalHLR W x' := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        nlinarith


theorem measurable_famK {c ℓ : ℝ} (hℓ : 0 < ℓ) : Measurable (famK c ℓ) := by
  unfold famK
  exact (Continuous.rpow_const (by fun_prop) fun y => Or.inl (by positivity)).measurable

/-- `∫ φ_{c,ℓ} W ≤ 23 ∫_{J} M W` over the interval `J = [c - ℓ/2, c + ℓ/2)`. -/
theorem lintegral_famK_le_set {c ℓ : ℝ} (hℓ : 0 < ℓ) {W : ℝ → ℝ≥0∞} (hW : Measurable W) :
    ∫⁻ y, ENNReal.ofReal (famK c ℓ y) * W y ≤
      ENNReal.ofReal 23 * ∫⁻ x in Ico (c - ℓ / 2) (c + ℓ / 2), maximalHLR W x := by
  have hMW : Measurable (maximalHLR W) := measurable_maximalHLR W
  set J : Set ℝ := Ico (c - ℓ / 2) (c + ℓ / 2) with hJ
  have hvol : volume J = ENNReal.ofReal ℓ := by
    rw [hJ, Real.volume_Ico]; congr 1; ring
  set X : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (famK c ℓ y) * W y with hX
  have hpt : ∀ x' ∈ J, X ≤ ENNReal.ofReal (23 * ℓ) * maximalHLR W x' := fun x' hx' =>
    lintegral_famK_mul_le hℓ hW hx'
  have hint : ENNReal.ofReal ℓ * X ≤ ENNReal.ofReal ℓ * (ENNReal.ofReal 23 * ∫⁻ x in J, maximalHLR W x) := by
    calc ENNReal.ofReal ℓ * X = ∫⁻ x in J, X := by rw [setLIntegral_const, hvol, mul_comm]
      _ ≤ ∫⁻ x in J, ENNReal.ofReal (23 * ℓ) * maximalHLR W x :=
          setLIntegral_mono (hMW.const_mul _) (fun x' hx' => hpt x' hx')
      _ = ENNReal.ofReal (23 * ℓ) * ∫⁻ x in J, maximalHLR W x := lintegral_const_mul _ hMW
      _ = ENNReal.ofReal ℓ * (ENNReal.ofReal 23 * ∫⁻ x in J, maximalHLR W x) := by
          rw [mul_comm 23 ℓ, ENNReal.ofReal_mul hℓ.le, mul_assoc]
  have h1 : ENNReal.ofReal ℓ ≠ 0 := by simpa using hℓ
  exact (ENNReal.mul_le_mul_iff_right h1 ENNReal.ofReal_ne_top).1 hint

section Family

variable {ι : Type*} (c ℓ a : ι → ℝ)

/-- The partial sum of the family kernels. -/
def famPhi (F : Finset ι) (x : ℝ) : ℝ≥0∞ := ∑ i ∈ F, ENNReal.ofReal (a i * famK (c i) (ℓ i) x)

/-- The coefficient function `∑_i a_i 1_{J_i}`. -/
def famA (F : Finset ι) (x : ℝ) : ℝ≥0∞ :=
  ∑ i ∈ F, ENNReal.ofReal (a i) * (Ico (c i - ℓ i / 2) (c i + ℓ i / 2)).indicator (fun _ => (1 : ℝ≥0∞)) x

variable {c ℓ a}

theorem measurable_famPhi (hℓ : ∀ i, 0 < ℓ i) (F : Finset ι) : Measurable (famPhi c ℓ a F) := by
  unfold famPhi
  exact Finset.measurable_sum _ fun i _ => ENNReal.measurable_ofReal.comp
    (measurable_const.mul (measurable_famK (hℓ i)))

theorem measurable_famA (F : Finset ι) : Measurable (famA c ℓ a F) := by
  unfold famA
  exact Finset.measurable_sum _ fun i _ => measurable_const.mul
    (measurable_const.indicator measurableSet_Ico)

/-- Dual inequality: `∫ Φ_F W ≤ 23 ∫ A_F · M W`. -/
theorem lintegral_famPhi_mul_le (hℓ : ∀ i, 0 < ℓ i) (ha : ∀ i, 0 ≤ a i) (F : Finset ι) {W : ℝ → ℝ≥0∞}
    (hW : Measurable W) :
    ∫⁻ x, famPhi c ℓ a F x * W x ≤ ENNReal.ofReal 23 * ∫⁻ x, famA c ℓ a F x * maximalHLR W x := by
  have hMW : Measurable (maximalHLR W) := measurable_maximalHLR W
  have hterm : ∀ i ∈ F, ∫⁻ x, ENNReal.ofReal (a i * famK (c i) (ℓ i) x) * W x ≤
      ENNReal.ofReal (a i) * (ENNReal.ofReal 23 * ∫⁻ x in Ico (c i - ℓ i / 2) (c i + ℓ i / 2), maximalHLR W x) := by
    intro i _
    have hKm : Measurable fun y => ENNReal.ofReal (famK (c i) (ℓ i) y) :=
      ENNReal.measurable_ofReal.comp (measurable_famK (hℓ i))
    have hm : Measurable fun x => ENNReal.ofReal (famK (c i) (ℓ i) x) * W x := hKm.mul hW
    calc ∫⁻ x, ENNReal.ofReal (a i * famK (c i) (ℓ i) x) * W x
        = ENNReal.ofReal (a i) * ∫⁻ x, ENNReal.ofReal (famK (c i) (ℓ i) x) * W x := by
          rw [← lintegral_const_mul _ hm]
          refine lintegral_congr fun x => ?_
          rw [ENNReal.ofReal_mul (ha i), mul_assoc]
      _ ≤ _ := mul_le_mul' le_rfl (lintegral_famK_le_set (hℓ i) hW)
  have e : ∫⁻ x, famA c ℓ a F x * maximalHLR W x =
      ∑ i ∈ F, ENNReal.ofReal (a i) * ∫⁻ x in Ico (c i - ℓ i / 2) (c i + ℓ i / 2), maximalHLR W x := by
    unfold famA
    simp_rw [Finset.sum_mul]
    have hm1 : ∀ i, Measurable fun x => ENNReal.ofReal (a i) *
        (Ico (c i - ℓ i / 2) (c i + ℓ i / 2)).indicator (fun _ => (1 : ℝ≥0∞)) x * maximalHLR W x :=
      fun i => (measurable_const.mul (measurable_const.indicator measurableSet_Ico)).mul hMW
    rw [lintegral_finsetSum _ (fun i _ => hm1 i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hm2 : Measurable fun x => (Ico (c i - ℓ i / 2) (c i + ℓ i / 2)).indicator (fun _ => (1 : ℝ≥0∞)) x *
        maximalHLR W x := (measurable_const.indicator measurableSet_Ico).mul hMW
    simp_rw [mul_assoc]
    rw [lintegral_const_mul _ hm2]
    congr 1
    rw [← lintegral_indicator measurableSet_Ico]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Ico (c i - ℓ i / 2) (c i + ℓ i / 2) <;> simp [hx, Set.indicator]
  unfold famPhi
  simp_rw [Finset.sum_mul]
  have hm3 : ∀ i, Measurable fun x => ENNReal.ofReal (a i * famK (c i) (ℓ i) x) * W x :=
    fun i => (ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_famK (hℓ i)))).mul hW
  rw [lintegral_finsetSum _ (fun i _ => hm3 i), e, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  refine (hterm i hi).trans (le_of_eq ?_)
  ring

end Family


/-- The Hardy-Littlewood maximal theorem in `lintegral` form. -/
theorem lintegral_maximal_rpow_le {p : ℝ} (hp : 1 < p) {W : ℝ → ℝ≥0∞} (hW : Measurable W) :
    (∫⁻ x, maximalHLR W x ^ p) ^ (1 / p) ≤
      (maximalHLRConst (ENNReal.ofReal p) : ℝ≥0∞) * (∫⁻ x, W x ^ p) ^ (1 / p) := by
  have h1 : (1 : ℝ≥0∞) < ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hp
  have := eLpNorm_maximalHLR_le h1 W
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using (by linarith : 0 < p)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top (measurable_maximalHLR W).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hW.aestronglyMeasurable,
    ENNReal.toReal_ofReal (by linarith)] at this
  simpa only [enorm_eq_self] using this

/-- Hölder + maximal theorem: `∫ A · M W ≤ C ‖A‖_q ‖W‖_{q'}`. -/
theorem lintegral_mul_maximal_le {q : ℝ} (hq : 1 < q) {A W : ℝ → ℝ≥0∞} (hA : Measurable A) (hW : Measurable W) :
    ∫⁻ x, A x * maximalHLR W x ≤ (∫⁻ x, A x ^ q) ^ (1 / q) *
      ((maximalHLRConst (ENNReal.ofReal (Real.conjExponent q)) : ℝ≥0∞) *
        (∫⁻ x, W x ^ Real.conjExponent q) ^ (1 / Real.conjExponent q)) := by
  have hpq : q.HolderConjugate (Real.conjExponent q) := Real.HolderConjugate.conjExponent hq
  have h1 := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hA.aemeasurable (measurable_maximalHLR W).aemeasurable
  refine h1.trans ?_
  exact mul_le_mul' le_rfl (lintegral_maximal_rpow_le (by
    have := hpq.symm.lt; exact this) hW)


section Finite

variable {ι : Type*} {c ℓ a : ι → ℝ}

theorem famK_le_one {c ℓ : ℝ} (hℓ : 0 < ℓ) (y : ℝ) : famK c ℓ y ≤ 1 := by
  unfold famK
  exact Real.rpow_le_one_of_one_le_of_nonpos (by have := div_nonneg (abs_nonneg (y - c)) hℓ.le; linarith)
    (by norm_num)

theorem integrable_famK {c ℓ : ℝ} (hℓ : 0 < ℓ) : Integrable (famK c ℓ) := by
  have := integrable_one_add_abs_sub_div_rpow (p := 2) (by norm_num) c hℓ
  exact this.congr (Filter.Eventually.of_forall fun y => by
    simp only [famK])

theorem lintegral_famPhi_rpow_lt_top {q : ℝ} (hq : 1 < q) (hℓ : ∀ i, 0 < ℓ i) (ha : ∀ i, 0 ≤ a i) (F : Finset ι) :
    ∫⁻ x, famPhi c ℓ a F x ^ q < ⊤ := by
  set K : ℝ≥0∞ := ∑ i ∈ F, ENNReal.ofReal (a i) with hK
  have hKtop : K ≠ ⊤ := ENNReal.sum_ne_top.2 fun i _ => ENNReal.ofReal_ne_top
  have hle1 : ∀ x, famPhi c ℓ a F x ≤ K := fun x => by
    unfold famPhi
    refine Finset.sum_le_sum fun i _ => ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have := famK_le_one (c := c i) (hℓ i) x
    nlinarith [ha i, famK_nonneg (c i) x (hℓ i)]
  have hpt : ∀ x, famPhi c ℓ a F x ^ q ≤ K ^ (q - 1) * famPhi c ℓ a F x := fun x => by
    have : famPhi c ℓ a F x ^ q = famPhi c ℓ a F x ^ (q - 1) * famPhi c ℓ a F x := by
      conv_lhs => rw [show q = (q - 1) + 1 by ring]
      rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
    rw [this]
    exact mul_le_mul' (ENNReal.rpow_le_rpow (hle1 x) (by linarith)) le_rfl
  have hint : ∫⁻ x, famPhi c ℓ a F x < ⊤ := by
    unfold famPhi
    have hm3 : ∀ i, Measurable fun x => ENNReal.ofReal (a i * famK (c i) (ℓ i) x) :=
      fun i => ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_famK (hℓ i)))
    rw [lintegral_finsetSum _ (fun i _ => hm3 i)]
    refine ENNReal.sum_lt_top.2 fun i _ => ?_
    have := ((integrable_famK (c := c i) (hℓ i)).const_mul (a i))
    have h2 := this.lintegral_lt_top
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) h2
    exact le_rfl
  calc ∫⁻ x, famPhi c ℓ a F x ^ q ≤ ∫⁻ x, K ^ (q - 1) * famPhi c ℓ a F x := lintegral_mono hpt
    _ = K ^ (q - 1) * ∫⁻ x, famPhi c ℓ a F x :=
        lintegral_const_mul _ (measurable_famPhi hℓ F)
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by linarith) hKtop) hint

end Finite


section FiniteMain

variable {ι : Type*} {c ℓ a : ι → ℝ}

theorem famA_rpow {q : ℝ} (hq : 0 < q) (F : Finset ι)
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (Ico (c i - ℓ i / 2) (c i + ℓ i / 2)) (Ico (c j - ℓ j / 2) (c j + ℓ j / 2)))
    (x : ℝ) :
    famA c ℓ a F x ^ q = ∑ i ∈ F, ENNReal.ofReal (a i) ^ q *
      (Ico (c i - ℓ i / 2) (c i + ℓ i / 2)).indicator (fun _ => (1 : ℝ≥0∞)) x := by
  by_cases hx : ∃ j ∈ F, x ∈ Ico (c j - ℓ j / 2) (c j + ℓ j / 2)
  · obtain ⟨j, hjF, hxj⟩ := hx
    have hz : ∀ i ∈ F, i ≠ j → x ∉ Ico (c i - ℓ i / 2) (c i + ℓ i / 2) := fun i hi hij hxi =>
      (Set.disjoint_left.1 (hdisj i hi j hjF hij)) hxi hxj
    have e1 : famA c ℓ a F x = ENNReal.ofReal (a j) := by
      unfold famA
      rw [Finset.sum_eq_single j (fun i hi hij => by rw [Set.indicator_of_notMem (hz i hi hij)]; simp)
        (fun h => absurd hjF h), Set.indicator_of_mem hxj]
      simp
    have e2 : ∑ i ∈ F, ENNReal.ofReal (a i) ^ q *
        (Ico (c i - ℓ i / 2) (c i + ℓ i / 2)).indicator (fun _ => (1 : ℝ≥0∞)) x = ENNReal.ofReal (a j) ^ q := by
      rw [Finset.sum_eq_single j (fun i hi hij => by rw [Set.indicator_of_notMem (hz i hi hij)]; simp)
        (fun h => absurd hjF h), Set.indicator_of_mem hxj]
      simp
    rw [e1, e2]
  · push Not at hx
    have e1 : famA c ℓ a F x = 0 := by
      unfold famA
      exact Finset.sum_eq_zero fun i hi => by rw [Set.indicator_of_notMem (hx i hi)]; simp
    have e2 : ∑ i ∈ F, ENNReal.ofReal (a i) ^ q *
        (Ico (c i - ℓ i / 2) (c i + ℓ i / 2)).indicator (fun _ => (1 : ℝ≥0∞)) x = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [Set.indicator_of_notMem (hx i hi)]; simp
    rw [e1, e2, ENNReal.zero_rpow_of_pos hq]

theorem lintegral_famA_rpow {q : ℝ} (hq : 0 < q) (_hℓ : ∀ i, 0 < ℓ i) (F : Finset ι)
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (Ico (c i - ℓ i / 2) (c i + ℓ i / 2)) (Ico (c j - ℓ j / 2) (c j + ℓ j / 2))) :
    ∫⁻ x, famA c ℓ a F x ^ q = ∑ i ∈ F, ENNReal.ofReal (a i) ^ q * ENNReal.ofReal (ℓ i) := by
  simp_rw [famA_rpow hq F hdisj]
  have hm : ∀ i, Measurable fun x => ENNReal.ofReal (a i) ^ q *
      (Ico (c i - ℓ i / 2) (c i + ℓ i / 2)).indicator (fun _ => (1 : ℝ≥0∞)) x :=
    fun i => measurable_const.mul (measurable_const.indicator measurableSet_Ico)
  rw [lintegral_finsetSum _ (fun i _ => hm i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_const_mul _ (measurable_const.indicator measurableSet_Ico), lintegral_indicator_const measurableSet_Ico,
    one_mul, Real.volume_Ico]
  congr 2; ring

/-- The constant of the family-sum lemma. -/
def famConst (q : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal 23 * (maximalHLRConst (ENNReal.ofReal (Real.conjExponent q)) : ℝ≥0∞)

/-- **The family-sum lemma, finite families.** -/
theorem famPhi_norm_le {q : ℝ} (hq : 1 < q) (hℓ : ∀ i, 0 < ℓ i) (ha : ∀ i, 0 ≤ a i) (F : Finset ι)
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (Ico (c i - ℓ i / 2) (c i + ℓ i / 2)) (Ico (c j - ℓ j / 2) (c j + ℓ j / 2))) :
    (∫⁻ x, famPhi c ℓ a F x ^ q) ^ (1 / q) ≤
      famConst q * (∑ i ∈ F, ENNReal.ofReal (a i) ^ q * ENNReal.ofReal (ℓ i)) ^ (1 / q) := by
  set q' := Real.conjExponent q with hq'
  have hpq : q.HolderConjugate q' := Real.HolderConjugate.conjExponent hq
  have hq'1 : 1 < q' := hpq.symm.lt
  have hq0 : 0 < q := by linarith
  set X : ℝ≥0∞ := ∫⁻ x, famPhi c ℓ a F x ^ q with hX
  have hXtop : X ≠ ⊤ := (lintegral_famPhi_rpow_lt_top hq hℓ ha F).ne
  set B : ℝ≥0∞ := ∑ i ∈ F, ENNReal.ofReal (a i) ^ q * ENNReal.ofReal (ℓ i) with hB
  have hBeq : ∫⁻ x, famA c ℓ a F x ^ q = B := lintegral_famA_rpow hq0 hℓ F hdisj
  set W : ℝ → ℝ≥0∞ := fun x => famPhi c ℓ a F x ^ (q - 1) with hW
  have hWm : Measurable W := (measurable_famPhi hℓ F).pow_const _
  have hΦW : ∀ x, famPhi c ℓ a F x * W x = famPhi c ℓ a F x ^ q := fun x => by
    simp only [hW]
    conv_rhs => rw [show q = 1 + (q - 1) by ring]
    rw [ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by linarith), ENNReal.rpow_one]
  have hqq : (q - 1) * q' = q := by
    simp only [hq', Real.conjExponent]
    have : q - 1 ≠ 0 := by linarith
    field_simp
  have hWq : ∀ x, W x ^ q' = famPhi c ℓ a F x ^ q := fun x => by
    simp only [hW]
    rw [← ENNReal.rpow_mul, hqq]
  have hdual := lintegral_famPhi_mul_le (c := c) hℓ ha F hWm
  have hhold := lintegral_mul_maximal_le hq (measurable_famA (c := c) (ℓ := ℓ) (a := a) F) hWm
  simp_rw [hΦW] at hdual
  rw [← hq'] at hhold
  simp_rw [hWq] at hhold
  rw [hBeq] at hhold
  have hmain : X ≤ ENNReal.ofReal 23 * (B ^ (1 / q) * ((maximalHLRConst (ENNReal.ofReal q') : ℝ≥0∞) * X ^ (1 / q'))) :=
    hdual.trans (mul_le_mul' le_rfl hhold)
  by_cases hX0 : X = 0
  · rw [hX0, ENNReal.zero_rpow_of_pos (by positivity)]; exact zero_le
  · have hsplit : X = X ^ (1 / q) * X ^ (1 / q') := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
      have : 1 / q + 1 / q' = 1 := by simpa [one_div] using hpq.inv_add_inv_eq_one
      rw [this, ENNReal.rpow_one]
    have hq'top : X ^ (1 / q') ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hXtop
    have hq'0 : X ^ (1 / q') ≠ 0 := by
      intro h
      rcases ENNReal.rpow_eq_zero_iff.1 h with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact hX0 h1
      · linarith [one_div_pos.2 (by linarith : 0 < q')]
    have : X ^ (1 / q) * X ^ (1 / q') ≤ (famConst q * B ^ (1 / q)) * X ^ (1 / q') := by
      rw [← hsplit]
      refine hmain.trans (le_of_eq ?_)
      unfold famConst
      ring
    exact (ENNReal.mul_le_mul_iff_left hq'0 hq'top).1 this |>.trans (le_of_eq (by simp only [hB]))

end FiniteMain


section Countable

variable {ι : Type*} [Countable ι] {c ℓ a : ι → ℝ}

/-- The full family sum. -/
def famPhiT (c ℓ a : ι → ℝ) (x : ℝ) : ℝ≥0∞ := ∑' i, ENNReal.ofReal (a i * famK (c i) (ℓ i) x)

omit [Countable ι] in
theorem famPhiT_eq_iSup (c ℓ a : ι → ℝ) (x : ℝ) : famPhiT c ℓ a x = ⨆ F : Finset ι, famPhi c ℓ a F x := by
  unfold famPhiT famPhi
  exact ENNReal.tsum_eq_iSup_sum

omit [Countable ι] in
theorem monotone_famPhi (c ℓ a : ι → ℝ) (x : ℝ) : Monotone fun F : Finset ι => famPhi c ℓ a F x :=
  fun _F _F' h => Finset.sum_le_sum_of_subset h

/-- **The family-sum lemma**: for pairwise disjoint intervals `[c_i - ℓ_i/2, c_i + ℓ_i/2)`,
`‖∑ a_i (1 + |x - c_i|/ℓ_i)^{-2}‖_{L^q} ≤ C_q (∑ a_i^q ℓ_i)^{1/q}`. -/
theorem famPhiT_norm_le {q : ℝ} (hq : 1 < q) (hℓ : ∀ i, 0 < ℓ i) (ha : ∀ i, 0 ≤ a i)
    (hdisj : Pairwise fun i j => Disjoint (Ico (c i - ℓ i / 2) (c i + ℓ i / 2)) (Ico (c j - ℓ j / 2) (c j + ℓ j / 2))) :
    (∫⁻ x, famPhiT c ℓ a x ^ q) ^ (1 / q) ≤
      famConst q * (∑' i, ENNReal.ofReal (a i) ^ q * ENNReal.ofReal (ℓ i)) ^ (1 / q) := by
  classical
  have hq0 : 0 < q := by linarith
  have hdirected : Directed (· ≤ ·) fun F : Finset ι => fun x => famPhi c ℓ a F x ^ q := by
    intro F F'
    refine ⟨F ∪ F', fun x => ?_, fun x => ?_⟩
    · exact ENNReal.rpow_le_rpow (monotone_famPhi c ℓ a x Finset.subset_union_left) hq0.le
    · exact ENNReal.rpow_le_rpow (monotone_famPhi c ℓ a x Finset.subset_union_right) hq0.le
  have hpt : ∀ x, famPhiT c ℓ a x ^ q = ⨆ F : Finset ι, famPhi c ℓ a F x ^ q := by
    intro x
    rw [famPhiT_eq_iSup]
    exact Monotone.map_iSup_of_continuousAt (f := fun t : ℝ≥0∞ => t ^ q)
      (ENNReal.continuous_rpow_const.continuousAt) (ENNReal.monotone_rpow_of_nonneg hq0.le)
      (by simp [ENNReal.zero_rpow_of_pos hq0])
  have hint : ∫⁻ x, famPhiT c ℓ a x ^ q = ⨆ F : Finset ι, ∫⁻ x, famPhi c ℓ a F x ^ q := by
    simp_rw [hpt]
    exact lintegral_iSup_directed (fun F => ((measurable_famPhi hℓ F).pow_const _).aemeasurable) hdirected
  have hF : ∀ F : Finset ι, ∫⁻ x, famPhi c ℓ a F x ^ q ≤
      famConst q ^ q * ∑' i, ENNReal.ofReal (a i) ^ q * ENNReal.ofReal (ℓ i) := by
    intro F
    have h := famPhi_norm_le hq hℓ ha F (fun i _ j _ hij => hdisj hij)
    have h2 : (∫⁻ x, famPhi c ℓ a F x ^ q) ≤
        (famConst q * (∑ i ∈ F, ENNReal.ofReal (a i) ^ q * ENNReal.ofReal (ℓ i)) ^ (1 / q)) ^ q := by
      have := ENNReal.rpow_le_rpow h hq0.le
      rwa [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one] at this
    refine h2.trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne',
      ENNReal.rpow_one]
    exact mul_le_mul' le_rfl (ENNReal.sum_le_tsum F)
  have hfin : ∫⁻ x, famPhiT c ℓ a x ^ q ≤ famConst q ^ q * ∑' i, ENNReal.ofReal (a i) ^ q * ENNReal.ofReal (ℓ i) := by
    rw [hint]; exact iSup_le hF
  have := ENNReal.rpow_le_rpow hfin (by positivity : (0 : ℝ) ≤ 1 / q)
  refine this.trans (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne',
    ENNReal.rpow_one]

end Countable

end PrimeBHT.TimeFrequency.X2
