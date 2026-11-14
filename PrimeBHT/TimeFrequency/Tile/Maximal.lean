module

public import PrimeCarleson.Proof.Common.HardyLittlewoodR
public import PrimeBHT.Frozen.IsAdapted
public import PrimeBHT.Frozen.Pairing

/-!
# Node C6 of the X1 blueprint: the maximal function and its facts

The blueprint's maximal function `M` is taken to be the uncentered Hardy-Littlewood maximal function
`PrimeCarleson.Proof.Common.maximalHLR` of the earlier project (`ℝ≥0∞`-valued, closed intervals): the
supremum over the intervals containing `x` of the average of `‖f‖ₑ`. Import closure: 34 modules (33 of them
the vendored `Carleson` slice). `PrimeCarleson.Proof.Oplus.External.THMaximal` (57 modules) and
`TreeLarge.Maximal` (81 modules) are *not* imported: the general-kernel bound is copied (attribution below)
and the weight integrals are derived from it.

* (M1) `weak_type_one_one`, `volume_superlevel_le`: weak type `(1,1)` with constant `4`;
* (M2) `isOpen_superlevel`, `isOpen_exceptionalSet`: superlevel sets are open (for every `f`);
* (M3), `q = 2`: `maximalHLR_le_rpow_maximalHLR_sq` (Jensen), `weak_type_sq`;
* (M4) `volume_exceptionalSet_le`: `|{M 1_E > C₀ |E|}| ≤ 4/C₀`;
* the exceptional set `F = {M 1_{E₁} > C₀ |E₁|} ∪ {M 1_{E₂} > C₀ |E₂|}` of C9:
  `volume_exceptionalSet_union_le` (`≤ 8/C₀`), `volume_exceptionalSet_union_lt_one_twelfth` (`C₀ > 96`),
  `exists_mem_notMem_exceptionalSet_of_not_subset`, and the bounds on `M g` / `M ‖g‖²` for `g` dominated
  by `a 1_E` outside the exceptional set (`maximalHLR_le_of_notMem_exceptionalSet_L1`, `..._L2`);
* (M5) packet domination for packets adapted in the sense of the frozen `IsAdapted` (ruling R16):
  first moment `enorm_pairing_le_maximalHLR` (general measurable `g`; any base point `x₀` with
  `|x₀ - c(I)| ≤ R K |I|`), the `L²`-weight bound `lintegral_weight_enorm_sq_le_maximalHLR`, their forms
  for `x₀ ∈ I` (`..._of_mem`), for `‖g‖ ≤ a 1_E` (`..._indicator`), and for `x₀` in an interval `J ⊇ I`
  with `|J| ≤ 2 K |I|` (`..._of_subset`, C10b with `K = 2^d`), with real-valued corollaries.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open PrimeCarleson.Proof.Common
open PrimeBHT.Statements
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Tile

/-! ### Monotonicity and homogeneity of the maximal function -/

/-- The maximal function is monotone in `‖f‖ₑ`. -/
theorem maximalHLR_mono {E F : Type*} [ENorm E] [ENorm F] {f : ℝ → E} {g : ℝ → F}
    (h : ∀ y, ‖f y‖ₑ ≤ ‖g y‖ₑ) (x : ℝ) : maximalHLR f x ≤ maximalHLR g x := by
  refine iSup₂_le fun a b => iSup_le fun hab => iSup_le fun hx => ?_
  refine le_iSup₂_of_le a b <| le_iSup₂_of_le hab hx ?_
  exact setLAverage_mono_ae _ (Eventually.of_forall h)

/-- `M f ≤ a · M g` when `‖f‖ₑ ≤ a ‖g‖ₑ` pointwise (`a ≠ ∞`). -/
theorem maximalHLR_le_mul {E F : Type*} [ENorm E] [ENorm F] {f : ℝ → E} {g : ℝ → F} {a : ℝ≥0∞}
    (ha : a ≠ ∞) (h : ∀ y, ‖f y‖ₑ ≤ a * ‖g y‖ₑ) (x : ℝ) :
    maximalHLR f x ≤ a * maximalHLR g x := by
  refine iSup₂_le fun s t => iSup_le fun hst => iSup_le fun hx => ?_
  calc ⨍⁻ y in Icc s t, ‖f y‖ₑ ∂volume ≤ ⨍⁻ y in Icc s t, a * ‖g y‖ₑ ∂volume :=
        setLAverage_mono_ae _ (Eventually.of_forall h)
    _ = a * ⨍⁻ y in Icc s t, ‖g y‖ₑ ∂volume := by
        rw [setLAverage_eq, setLAverage_eq, lintegral_const_mul' _ _ ha, mul_div_assoc]
    _ ≤ a * maximalHLR g x := by
        gcongr
        exact le_iSup₂_of_le s t <| le_iSup₂_of_le hst hx le_rfl

/-- `M f ≤ c` when `‖f‖ₑ ≤ c` pointwise. -/
theorem maximalHLR_le_of_enorm_le {E : Type*} [ENorm E] {f : ℝ → E} {c : ℝ≥0∞}
    (h : ∀ y, ‖f y‖ₑ ≤ c) (x : ℝ) : maximalHLR f x ≤ c := by
  refine iSup₂_le fun s t => iSup_le fun hst => iSup_le fun hx => ?_
  calc ⨍⁻ y in Icc s t, ‖f y‖ₑ ∂volume ≤ ⨍⁻ _y in Icc s t, c ∂volume :=
        setLAverage_mono_ae _ (Eventually.of_forall h)
    _ = c := by
        refine setLAverage_const ?_ ?_ c
        · rw [Real.volume_Icc]; exact (ENNReal.ofReal_pos.2 (sub_pos.2 hst)).ne'
        · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top

/-- `M f` depends on `f` only through `‖f‖ₑ` (e.g. `M (e^{-2πiξ·} g) = M g`). -/
theorem maximalHLR_congr_enorm {E F : Type*} [ENorm E] [ENorm F] {f : ℝ → E} {g : ℝ → F}
    (h : ∀ y, ‖f y‖ₑ = ‖g y‖ₑ) (x : ℝ) : maximalHLR f x = maximalHLR g x :=
  le_antisymm (maximalHLR_mono (fun y => (h y).le) x) (maximalHLR_mono (fun y => (h y).ge) x)

/-- The average over a nondegenerate interval containing `x` is at most `M f (x)`, in the form
`∫_{[a,b]} ‖f‖ₑ ≤ (b - a) · M f (x)` (e.g. `∫_{8I}|f|² ≲ |I| M(|f|²)(x)` for `x ∈ I`). -/
theorem lintegral_Icc_le_mul_maximalHLR {E : Type*} [ENorm E] (f : ℝ → E) {a b x : ℝ}
    (hab : a < b) (hx : x ∈ Icc a b) :
    ∫⁻ y in Icc a b, ‖f y‖ₑ ≤ ENNReal.ofReal (b - a) * maximalHLR f x := by
  have h : ⨍⁻ y in Icc a b, ‖f y‖ₑ ∂volume ≤ maximalHLR f x :=
    le_iSup₂_of_le a b <| le_iSup₂_of_le hab hx le_rfl
  rw [setLAverage_eq, Real.volume_Icc] at h
  have hpos : ENNReal.ofReal (b - a) ≠ 0 := (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'
  rw [ENNReal.div_le_iff hpos ENNReal.ofReal_ne_top, mul_comm] at h
  exact h

/-! ### The general kernel bound (copy)

The following lemma is a verbatim copy of `PrimeCarleson.Proof.Oplus.lintegral_kernel_le_maximalHLR`
(`PrimeCarleson/Proof/Oplus/TreeLarge/Maximal.lean`, earlier project, not edited), copied so that the
81-module closure of that file (`Lepingle`, `SquareFunction`, ...) is not imported. -/

/-- The geometric kernel `R⁻¹ (1 + |x' - y|/R)^{-2}` is dominated by `10 M[W](x')`. -/
theorem lintegral_kernel_le_maximalHLR {R : ℝ} (hR : 0 < R) (x' : ℝ) {W : ℝ → ℝ≥0∞}
    (hW : Measurable W) :
    ∫⁻ y, ENNReal.ofReal (R⁻¹ * (1 + |x' - y| / R) ^ (-2 : ℤ)) * W y ≤
      10 * maximalHLR W x' := by
  set M := maximalHLR W x' with hM
  -- the dyadic majorant
  set b : ℕ → ℝ := fun n => if n = 0 then 1 else (1 / 4 : ℝ) ^ (n - 1) with hb
  have hb_zero : b 0 = 1 := by simp [hb]
  have hb_succ : ∀ n, b (n + 1) = (1 / 4 : ℝ) ^ n := fun n => by simp [hb]
  have hb0 : ∀ n, 0 ≤ b n := fun n => by
    cases n
    · rw [hb_zero]; norm_num
    · rw [hb_succ]; positivity
  set B : ℕ → Set ℝ := fun n => Ioo (x' - 2 ^ n * R) (x' + 2 ^ n * R) with hBdef
  have hBm : ∀ n, MeasurableSet (B n) := fun n => measurableSet_Ioo
  have hpt : ∀ y, ENNReal.ofReal (R⁻¹ * (1 + |x' - y| / R) ^ (-2 : ℤ)) ≤
      ∑' n, ENNReal.ofReal (R⁻¹ * b n) * (B n).indicator (fun _ => (1 : ℝ≥0∞)) y := by
    intro y
    set u : ℝ := |x' - y| / R with hu
    have hu0 : 0 ≤ u := by positivity
    have hmemB : ∀ n : ℕ, u < 2 ^ n → y ∈ B n := by
      intro n hn
      have : |x' - y| < 2 ^ n * R := by
        rw [hu, div_lt_iff₀ hR] at hn; linarith
      rw [abs_lt] at this
      exact ⟨by linarith, by linarith⟩
    rcases lt_or_ge u 1 with h1 | h1
    · refine le_trans ?_ (ENNReal.le_tsum 0)
      have hy : y ∈ B 0 := hmemB 0 (by simpa using h1)
      rw [Set.indicator_of_mem hy, mul_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have : (1 + u) ^ (-2 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ (by linarith) (by norm_num)
      rw [hb_zero]
      nlinarith [inv_pos.2 hR]
    · obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near h1 (by norm_num : (1 : ℝ) < 2)
      refine le_trans ?_ (ENNReal.le_tsum (n + 1))
      have hy : y ∈ B (n + 1) := hmemB (n + 1) hn2
      rw [Set.indicator_of_mem hy, mul_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 : (1 + u) ^ (-2 : ℤ) ≤ (1 / 4 : ℝ) ^ n := by
        have e0 : (1 + u) ^ (-2 : ℤ) = ((1 + u) ^ 2)⁻¹ := by rw [zpow_neg]; norm_cast
        rw [e0]
        have h3 : (4 : ℝ) ^ n ≤ (1 + u) ^ 2 := by
          have h4 : (2 : ℝ) ^ n ≤ u := hn1
          have : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num
          rw [this]
          have : (2 : ℝ) ^ n ≤ 1 + u := by linarith
          exact pow_le_pow_left₀ (by positivity) this 2
        rw [one_div, inv_pow]
        exact inv_anti₀ (by positivity) h3
      rw [hb_succ]
      nlinarith [inv_pos.2 hR]
  -- averages
  have hint : ∀ n : ℕ, ∫⁻ y in B n, W y ≤ ENNReal.ofReal (2 * 2 ^ n * R) * M := by
    intro n
    have hpos : 0 < (2 : ℝ) ^ n * R := by positivity
    have hab : x' - 2 ^ n * R < x' + 2 ^ n * R := by linarith
    have hx : x' ∈ B n := ⟨by linarith, by linarith⟩
    have h := laverage_le_maximalHLR W hab (subset_refl _) Ioo_subset_Icc_self hx
    rw [setLAverage_eq] at h
    simp only [enorm_eq_self] at h
    have hvol : volume (B n) = ENNReal.ofReal (2 * 2 ^ n * R) := by
      rw [hBdef]
      simp only [Real.volume_Ioo]
      congr 1; ring
    have h2 : (volume (B n)) ≠ 0 := by
      rw [hvol]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have h3 : (volume (B n)) ≠ ⊤ := by rw [hvol]; exact ENNReal.ofReal_ne_top
    have h4 := (ENNReal.div_le_iff h2 h3).1 h
    rw [hvol] at h4
    rw [mul_comm]
    exact h4
  have hsumb : ∑' n : ℕ, ENNReal.ofReal (R⁻¹ * b n) * ENNReal.ofReal (2 * 2 ^ n * R) ≤ 10 := by
    have e : ∀ n : ℕ, ENNReal.ofReal (R⁻¹ * b n) * ENNReal.ofReal (2 * 2 ^ n * R) =
        ENNReal.ofReal (2 * b n * 2 ^ n) := by
      intro n
      rw [← ENNReal.ofReal_mul (by have := hb0 n; positivity)]
      congr 1
      field_simp
    simp_rw [e]
    set t : ℕ → ℝ := fun n => 2 * b n * 2 ^ n with ht
    have ht0 : ∀ n, 0 ≤ t n := fun n => by have := hb0 n; simp only [ht]; positivity
    have hts : ∀ n, t (n + 1) = 4 * (1 / 2 : ℝ) ^ n := by
      intro n
      simp only [ht, hb_succ]
      have h1 : (1 / 4 : ℝ) ^ n * 2 ^ n = (1 / 2) ^ n := by rw [← mul_pow]; norm_num
      calc 2 * (1 / 4 : ℝ) ^ n * 2 ^ (n + 1) = 4 * ((1 / 4 : ℝ) ^ n * 2 ^ n) := by ring
        _ = 4 * (1 / 2 : ℝ) ^ n := by rw [h1]
    have hsum : Summable t := by
      rw [← summable_nat_add_iff 1]
      simp_rw [hts]
      exact (summable_geometric_two).mul_left 4
    rw [← ENNReal.ofReal_tsum_of_nonneg ht0 hsum]
    rw [hsum.tsum_eq_zero_add]
    simp_rw [hts]
    rw [tsum_mul_left, tsum_geometric_two]
    have : t 0 = 2 := by simp [ht, hb_zero]
    rw [this]
    have : (2 : ℝ) + 4 * 2 = 10 := by norm_num
    rw [this]
    simp
  calc ∫⁻ y, ENNReal.ofReal (R⁻¹ * (1 + |x' - y| / R) ^ (-2 : ℤ)) * W y
      ≤ ∫⁻ y, (∑' n, ENNReal.ofReal (R⁻¹ * b n) * (B n).indicator (fun _ => (1 : ℝ≥0∞)) y) *
          W y := lintegral_mono fun y => mul_le_mul_left (hpt y) _
    _ = ∫⁻ y, ∑' n, ENNReal.ofReal (R⁻¹ * b n) *
          ((B n).indicator (fun _ => (1 : ℝ≥0∞)) y * W y) := by
        refine lintegral_congr fun y => ?_
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun n => ?_
        ring
    _ = ∑' n, ∫⁻ y, ENNReal.ofReal (R⁻¹ * b n) *
          ((B n).indicator (fun _ => (1 : ℝ≥0∞)) y * W y) :=
        lintegral_tsum fun n => (measurable_const.mul
          ((measurable_const.indicator (hBm n)).mul hW)).aemeasurable
    _ = ∑' n, ENNReal.ofReal (R⁻¹ * b n) * ∫⁻ y in B n, W y := by
        refine tsum_congr fun n => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        rw [← lintegral_indicator (hBm n)]
        refine lintegral_congr fun y => ?_
        by_cases hy : y ∈ B n
        · simp [Set.indicator_of_mem hy]
        · simp [Set.indicator_of_notMem hy]
    _ ≤ ∑' n, ENNReal.ofReal (R⁻¹ * b n) * (ENNReal.ofReal (2 * 2 ^ n * R) * M) :=
        ENNReal.tsum_le_tsum fun n => mul_le_mul_right (hint n) _
    _ = (∑' n : ℕ, ENNReal.ofReal (R⁻¹ * b n) * ENNReal.ofReal (2 * 2 ^ n * R)) * M := by
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun n => ?_
        ring
    _ ≤ 10 * M := mul_le_mul_left hsumb _


/-! ### (M1), (M2): weak type `(1,1)` and openness of the superlevel sets -/

/-- `M f` is the same function as `M ‖f‖ₑ`. -/
theorem maximalHLR_enorm {E : Type*} [ENorm E] (f : ℝ → E) (x : ℝ) :
    maximalHLR (fun y => ‖f y‖ₑ) x = maximalHLR f x :=
  le_antisymm (maximalHLR_mono (fun y => by simp) x) (maximalHLR_mono (fun y => by simp) x)

/-- **(M2)** The superlevel sets `{M f > t}` are open (`M f` is lower semicontinuous), for every `f`. -/
theorem isOpen_superlevel {E : Type*} [ENorm E] (f : ℝ → E) (t : ℝ≥0∞) :
    IsOpen {x | t < maximalHLR f x} :=
  lowerSemicontinuous_iff_isOpen_preimage.1 (lowerSemicontinuous_maximalHLR f) t

/-! ### (M4) and the exceptional set of C9 -/

/-- The set `{M 1_E > C₀ |E|}` (blueprint C9/C6 (M4)): the maximal function of the indicator `1_E`
exceeds `C₀ · volume E` (`ℝ≥0∞`-valued comparison; `C₀ : ℝ`). -/
def exceptionalSet (E : Set ℝ) (C₀ : ℝ) : Set ℝ :=
  {x | ENNReal.ofReal C₀ * volume E < maximalHLR (E.indicator (1 : ℝ → ℝ)) x}

/-- **(M2)** for the exceptional set: it is open. -/
theorem isOpen_exceptionalSet (E : Set ℝ) (C₀ : ℝ) : IsOpen (exceptionalSet E C₀) :=
  isOpen_superlevel _ _

/-- A point outside the exceptional set has `M 1_E x ≤ C₀ |E|`. -/
theorem maximalHLR_indicator_le_of_notMem {E : Set ℝ} {C₀ : ℝ} {x : ℝ}
    (hx : x ∉ exceptionalSet E C₀) :
    maximalHLR (E.indicator (1 : ℝ → ℝ)) x ≤ ENNReal.ofReal C₀ * volume E :=
  not_lt.1 hx

/-- **(M4)** For measurable `E` of finite positive measure and `C₀ > 0`:
`|{M 1_E > C₀ |E|}| ≤ 4 / C₀` (the weak `(1,1)` constant is `4`). -/
theorem volume_exceptionalSet_le {E : Set ℝ} (hE : MeasurableSet E) (h0 : volume E ≠ 0)
    (htop : volume E ≠ ⊤) {C₀ : ℝ} (hC : 0 < C₀) :
    volume (exceptionalSet E C₀) ≤ ENNReal.ofReal (4 / C₀) := by
  have hC' : ENNReal.ofReal C₀ ≠ 0 := (ENNReal.ofReal_pos.2 hC).ne'
  have ht : ENNReal.ofReal C₀ * volume E ≠ 0 := mul_ne_zero hC' h0
  refine (volume_maximalHLR_indicator_gt_le hE ht).trans ?_
  rw [ENNReal.mul_div_mul_right _ _ h0 htop, ENNReal.ofReal_div_of_pos hC]
  simp

/-- `|F| ≤ 8 / C₀` for the exceptional set of C9. -/
theorem volume_exceptionalSet_union_le {E₁ E₂ : Set ℝ} (hE₁ : MeasurableSet E₁)
    (hE₂ : MeasurableSet E₂) (h₁ : volume E₁ ≠ 0) (h₂ : volume E₂ ≠ 0) (t₁ : volume E₁ ≠ ⊤)
    (t₂ : volume E₂ ≠ ⊤) {C₀ : ℝ} (hC : 0 < C₀) :
    volume (exceptionalSet E₁ C₀ ∪ exceptionalSet E₂ C₀) ≤ ENNReal.ofReal (8 / C₀) := by
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add (volume_exceptionalSet_le hE₁ h₁ t₁ hC)
    (volume_exceptionalSet_le hE₂ h₂ t₂ hC)).trans_eq ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- `|F| < 1/12` for `C₀ > 96` (e.g. `C₀ = 100`, i.e. `25 C_w` with `C_w = 4`). -/
theorem volume_exceptionalSet_union_lt_one_twelfth {E₁ E₂ : Set ℝ} (hE₁ : MeasurableSet E₁)
    (hE₂ : MeasurableSet E₂) (h₁ : volume E₁ ≠ 0) (h₂ : volume E₂ ≠ 0) (t₁ : volume E₁ ≠ ⊤)
    (t₂ : volume E₂ ≠ ⊤) {C₀ : ℝ} (hC : 96 < C₀) :
    volume (exceptionalSet E₁ C₀ ∪ exceptionalSet E₂ C₀) < ENNReal.ofReal (1 / 12) := by
  have hC0 : 0 < C₀ := by linarith
  refine (volume_exceptionalSet_union_le hE₁ hE₂ h₁ h₂ t₁ t₂ hC0).trans_lt ?_
  rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  rw [div_lt_div_iff₀ hC0 (by norm_num)]
  linarith

/-- If `I ⊄ F` for the exceptional set `F` of C9, there is a point `x ∈ I` outside both parts
of `F` (the form in which C9 uses `I_t ⊄ F`); there `M 1_{E_k}(x) ≤ C₀ |E_k|` for `k = 1, 2`
(`maximalHLR_indicator_le_of_notMem`). -/
theorem exists_mem_notMem_exceptionalSet_of_not_subset {E₁ E₂ : Set ℝ} {C₀ : ℝ} {I : Set ℝ}
    (hI : ¬ I ⊆ exceptionalSet E₁ C₀ ∪ exceptionalSet E₂ C₀) :
    ∃ x ∈ I, x ∉ exceptionalSet E₁ C₀ ∧ x ∉ exceptionalSet E₂ C₀ := by
  obtain ⟨x, hxI, hx⟩ := Set.not_subset.1 hI
  rw [Set.mem_union, not_or] at hx
  exact ⟨x, hxI, hx⟩

/-! ### The weight bound (M5, weight form) -/

/-- Pointwise comparison of the weight centred at `c` and scale `L` with the weight centred at `x₀` and
scale `L' ≥ L`, when `|x₀ - c| ≤ R L'`: `(1 + |y - c|/L)^{-2} ≤ (1 + R)² (1 + |x₀ - y|/L')^{-2}`. -/
theorem weight_le_mul_weight {L L' R c x₀ y : ℝ} (hL : 0 < L) (hLL : L ≤ L') (hR : 0 ≤ R)
    (hx₀ : |x₀ - c| ≤ R * L') :
    (1 + |y - c| / L) ^ (-2 : ℤ) ≤ (1 + R) ^ 2 * (1 + |x₀ - y| / L') ^ (-2 : ℤ) := by
  have hL' : 0 < L' := hL.trans_le hLL
  have ht : 0 ≤ |y - c| / L := by positivity
  have hs : 0 ≤ |x₀ - y| / L' := by positivity
  have hu1 : 1 ≤ 1 + |y - c| / L := by linarith
  have hv0 : 0 < 1 + |x₀ - y| / L' := by linarith
  have h1 : |x₀ - y| ≤ |x₀ - c| + |y - c| := by
    calc |x₀ - y| = |(x₀ - c) - (y - c)| := by ring_nf
      _ ≤ |x₀ - c| + |y - c| := abs_sub _ _
  have h4 : |y - c| ≤ |y - c| / L * L' := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hL]
    exact mul_le_mul_of_nonneg_left hLL (abs_nonneg _)
  have h2 : |x₀ - y| / L' ≤ R + |y - c| / L := by
    rw [div_le_iff₀ hL', add_mul]
    linarith
  have hvu : 1 + |x₀ - y| / L' ≤ (1 + R) * (1 + |y - c| / L) := by
    have h3 : 0 ≤ R * (|y - c| / L) := mul_nonneg hR ht
    nlinarith
  have hsq : (1 + |x₀ - y| / L') ^ 2 ≤ (1 + R) ^ 2 * (1 + |y - c| / L) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hv0.le hvu 2
  rw [zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat, inv_eq_one_div, ← div_eq_mul_inv,
    div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- **(M5), weight form.** For measurable `W ≥ 0`, scales `0 < L ≤ L'`, and `x₀` with
`|x₀ - c| ≤ R L'`:
`∫ (1 + |y - c|/L)^{-2} W(y) dy ≤ 10 (1 + R)² L' · M W (x₀)`.
(With `L = L' = |I|`, `c = c(I)`, `x₀ ∈ I`, `R = 1/2` the constant is `22.5 |I|`; for C10b take `L = |I|`,
`L' = 2^d |I|`.) -/
theorem lintegral_weight_le_maximalHLR {L L' R c x₀ : ℝ} (hL : 0 < L) (hLL : L ≤ L') (hR : 0 ≤ R)
    (hx₀ : |x₀ - c| ≤ R * L') {W : ℝ → ℝ≥0∞} (hW : Measurable W) :
    ∫⁻ y, ENNReal.ofReal ((1 + |y - c| / L) ^ (-2 : ℤ)) * W y ≤
      ENNReal.ofReal (10 * (1 + R) ^ 2 * L') * maximalHLR W x₀ := by
  have hL' : 0 < L' := hL.trans_le hLL
  have hpt : ∀ y, ENNReal.ofReal ((1 + |y - c| / L) ^ (-2 : ℤ)) ≤
      ENNReal.ofReal ((1 + R) ^ 2 * L') *
        ENNReal.ofReal (L'⁻¹ * (1 + |x₀ - y| / L') ^ (-2 : ℤ)) := by
    intro y
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (1 + |y - c| / L) ^ (-2 : ℤ) ≤ (1 + R) ^ 2 * (1 + |x₀ - y| / L') ^ (-2 : ℤ) :=
          weight_le_mul_weight hL hLL hR hx₀
      _ = (1 + R) ^ 2 * L' * (L'⁻¹ * (1 + |x₀ - y| / L') ^ (-2 : ℤ)) := by
          field_simp
  have hc : ENNReal.ofReal (10 * (1 + R) ^ 2 * L') =
      ENNReal.ofReal ((1 + R) ^ 2 * L') * 10 := by
    rw [show 10 * (1 + R) ^ 2 * L' = ((1 + R) ^ 2 * L') * 10 by ring,
      ENNReal.ofReal_mul (by positivity)]
    simp
  calc ∫⁻ y, ENNReal.ofReal ((1 + |y - c| / L) ^ (-2 : ℤ)) * W y
      ≤ ∫⁻ y, (ENNReal.ofReal ((1 + R) ^ 2 * L') *
          ENNReal.ofReal (L'⁻¹ * (1 + |x₀ - y| / L') ^ (-2 : ℤ))) * W y :=
        lintegral_mono fun y => mul_le_mul_left (hpt y) _
    _ = ENNReal.ofReal ((1 + R) ^ 2 * L') *
          ∫⁻ y, ENNReal.ofReal (L'⁻¹ * (1 + |x₀ - y| / L') ^ (-2 : ℤ)) * W y := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun y => mul_assoc _ _ _
    _ ≤ ENNReal.ofReal ((1 + R) ^ 2 * L') * (10 * maximalHLR W x₀) := by
        gcongr
        exact lintegral_kernel_le_maximalHLR hL' x₀ hW
    _ = ENNReal.ofReal (10 * (1 + R) ^ 2 * L') * maximalHLR W x₀ := by
        rw [hc]; ring

/-- The weight bound for `W = ‖g‖ₑ²` (the `L²` form of (M5)): for measurable `g`,
`∫ (1 + |y - c|/L)^{-2} ‖g(y)‖² dy ≤ 10 (1 + R)² L' · M(‖g‖²)(x₀)`. -/
theorem lintegral_weight_enorm_sq_le_maximalHLR {L L' R c x₀ : ℝ} (hL : 0 < L) (hLL : L ≤ L')
    (hR : 0 ≤ R) (hx₀ : |x₀ - c| ≤ R * L') {g : ℝ → ℂ} (hg : Measurable g) :
    ∫⁻ y, ENNReal.ofReal ((1 + |y - c| / L) ^ (-2 : ℤ)) * ‖g y‖ₑ ^ 2 ≤
      ENNReal.ofReal (10 * (1 + R) ^ 2 * L') * maximalHLR (fun y => ‖g y‖ₑ ^ 2) x₀ :=
  lintegral_weight_le_maximalHLR (W := fun y => ‖g y‖ₑ ^ 2) hL hLL hR hx₀ (hg.enorm.pow_const 2)

/-! ### Adapted packets: pointwise decay and the pairing bound -/

/-- Pointwise decay of an adapted packet (the `n = 0` case of `IsAdapted`; `|e^{-2πi c(ω) x}| = 1`):
`|φ(x)| ≤ |I|^{-1/2} (1 + |x - c(I)|/|I|)^{-N}`. -/
theorem norm_le_of_isAdapted {N : ℕ} {I ω : Set ℝ} {φ : ℝ → ℂ} (h : IsAdapted N I ω φ) (x : ℝ) :
    ‖φ x‖ ≤ (volume I).toReal ^ (-(1 : ℝ) / 2) *
      (1 + |x - intervalCentre I| / (volume I).toReal) ^ (-(N : ℝ)) := by
  have h0 := h.2.2.2 0 (Nat.zero_le _) x
  rw [iteratedDeriv_zero] at h0
  have hn : ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (intervalCentre ω : ℂ) * (x : ℂ))) *
      φ x‖ = ‖φ x‖ := by
    rw [norm_mul, Complex.norm_exp]
    simp
  have hexp : (-((0 : ℕ) : ℝ) - 1 / 2) = -(1 : ℝ) / 2 := by norm_num
  simp only [hexp] at h0
  rw [← hn]
  exact h0

/-- For `N ≥ 2`, `‖φ(x)‖ₑ ≤ |I|^{-1/2} (1 + |x - c(I)|/|I|)^{-2}` (`ℝ≥0∞`-valued). -/
theorem enorm_le_of_isAdapted {N : ℕ} (hN : 2 ≤ N) {I ω : Set ℝ} {φ : ℝ → ℂ}
    (h : IsAdapted N I ω φ) (x : ℝ) :
    ‖φ x‖ₑ ≤ ENNReal.ofReal ((volume I).toReal ^ (-(1 : ℝ) / 2)) *
      ENNReal.ofReal ((1 + |x - intervalCentre I| / (volume I).toReal) ^ (-2 : ℤ)) := by
  rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ((norm_le_of_isAdapted h x).trans ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hb : (1 : ℝ) ≤ 1 + |x - intervalCentre I| / (volume I).toReal := by
    have : 0 ≤ |x - intervalCentre I| / (volume I).toReal := by positivity
    linarith
  rw [← Real.rpow_intCast]
  refine Real.rpow_le_rpow_of_exponent_le hb ?_
  have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  push_cast
  linarith

/-- `‖⟨g, φ⟩‖ₑ ≤ |I|^{-1/2} ∫ (1 + |y - c(I)|/|I|)^{-2} ‖g(y)‖ₑ dy` for `φ` adapted with exponent `N ≥ 2`
(`⟨g, φ⟩ = ∫ g conj φ`). -/
theorem enorm_pairing_le_lintegral {N : ℕ} (hN : 2 ≤ N) {I ω : Set ℝ} {φ : ℝ → ℂ}
    (hφ : IsAdapted N I ω φ) (g : ℝ → ℂ) :
    ‖pairing g φ‖ₑ ≤ ENNReal.ofReal ((volume I).toReal ^ (-(1 : ℝ) / 2)) *
      ∫⁻ y, ENNReal.ofReal ((1 + |y - intervalCentre I| / (volume I).toReal) ^ (-2 : ℤ)) *
        ‖g y‖ₑ := by
  unfold pairing
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  rw [enorm_mul, RCLike.enorm_conj]
  calc ‖g y‖ₑ * ‖φ y‖ₑ
      ≤ ‖g y‖ₑ * (ENNReal.ofReal ((volume I).toReal ^ (-(1 : ℝ) / 2)) *
          ENNReal.ofReal ((1 + |y - intervalCentre I| / (volume I).toReal) ^ (-2 : ℤ))) := by
        gcongr
        exact enorm_le_of_isAdapted hN hφ y
    _ = _ := by ring

/-- **(M5), packet domination.** For `φ` adapted to `(I, ω)` with exponent `N ≥ 2`, `0 < |I| < ∞`,
measurable `g`, a scale factor `K ≥ 1` and `R ≥ 0`, and a base point `x₀` with
`|x₀ - c(I)| ≤ R · K |I|`:
`|I|^{-1/2} |⟨g, φ⟩| ≤ 10 (1 + R)² K · M g (x₀)`.
For `x₀ ∈ I` take `K = 1`, `R = 1/2` (`enorm_pairing_le_maximalHLR_of_mem`); for the base point of C10b at
distance `≤ 2^{d+1}|I|` take `K = 2^d`, `R = 2`. -/
theorem enorm_pairing_le_maximalHLR {N : ℕ} (hN : 2 ≤ N) {I ω : Set ℝ} {φ : ℝ → ℂ}
    (hφ : IsAdapted N I ω φ) (hL : 0 < (volume I).toReal) {g : ℝ → ℂ} (hg : Measurable g)
    {K R x₀ : ℝ} (hK : 1 ≤ K) (hR : 0 ≤ R)
    (hx₀ : |x₀ - intervalCentre I| ≤ R * (K * (volume I).toReal)) :
    ENNReal.ofReal ((volume I).toReal ^ (-(1 : ℝ) / 2)) * ‖pairing g φ‖ₑ ≤
      ENNReal.ofReal (10 * (1 + R) ^ 2 * K) * maximalHLR g x₀ := by
  set L : ℝ := (volume I).toReal with hLdef
  have hKL : L ≤ K * L := by nlinarith
  have hint := lintegral_weight_le_maximalHLR (c := intervalCentre I) hL hKL hR hx₀
    (W := fun y => ‖g y‖ₑ) hg.enorm
  rw [maximalHLR_enorm] at hint
  have hp := enorm_pairing_le_lintegral hN hφ g
  have ha : L ^ (-(1 : ℝ) / 2) * L ^ (-(1 : ℝ) / 2) = L⁻¹ := by
    rw [← Real.rpow_add hL]
    norm_num [Real.rpow_neg_one]
  calc ENNReal.ofReal (L ^ (-(1 : ℝ) / 2)) * ‖pairing g φ‖ₑ
      ≤ ENNReal.ofReal (L ^ (-(1 : ℝ) / 2)) * (ENNReal.ofReal (L ^ (-(1 : ℝ) / 2)) *
          (ENNReal.ofReal (10 * (1 + R) ^ 2 * (K * L)) * maximalHLR g x₀)) := by
        gcongr
        exact hp.trans (mul_le_mul' le_rfl hint)
    _ = (ENNReal.ofReal (L ^ (-(1 : ℝ) / 2)) * ENNReal.ofReal (L ^ (-(1 : ℝ) / 2)) *
          ENNReal.ofReal (10 * (1 + R) ^ 2 * (K * L))) * maximalHLR g x₀ := by ring
    _ = ENNReal.ofReal (10 * (1 + R) ^ 2 * K) * maximalHLR g x₀ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ha]
        congr 2
        field_simp

/-! ### Functions dominated by `a · 1_E` -/

/-- `‖g‖ ≤ a · 1_E` gives `‖g y‖ₑ ≤ a · ‖1_E y‖ₑ` in `ℝ≥0∞`. -/
theorem enorm_le_mul_enorm_indicator {E : Set ℝ} {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℂ}
    (hg : ∀ y, ‖g y‖ ≤ a * E.indicator (1 : ℝ → ℝ) y) (y : ℝ) :
    ‖g y‖ₑ ≤ ENNReal.ofReal a * ‖E.indicator (1 : ℝ → ℝ) y‖ₑ := by
  have h0 : 0 ≤ E.indicator (1 : ℝ → ℝ) y := Set.indicator_nonneg (fun _ _ => by simp) y
  rw [Real.enorm_eq_ofReal h0, ← ENNReal.ofReal_mul ha, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hg y)

/-- The identity behind the `M²` bookkeeping: `M g ≤ a · M 1_E` if `‖g‖ ≤ a 1_E`. -/
theorem maximalHLR_le_mul_indicator {E : Set ℝ} {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℂ}
    (hg : ∀ y, ‖g y‖ ≤ a * E.indicator (1 : ℝ → ℝ) y) (x : ℝ) :
    maximalHLR g x ≤ ENNReal.ofReal a * maximalHLR (E.indicator (1 : ℝ → ℝ)) x :=
  maximalHLR_le_mul ENNReal.ofReal_ne_top (enorm_le_mul_enorm_indicator ha hg) x

/-- `M(‖g‖²) ≤ a² · M 1_E` if `‖g‖ ≤ a 1_E` (for indicators `(M²g)² = M(‖g‖²)`, no Jensen needed). -/
theorem maximalHLR_enorm_sq_le_mul_indicator {E : Set ℝ} {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℂ}
    (hg : ∀ y, ‖g y‖ ≤ a * E.indicator (1 : ℝ → ℝ) y) (x : ℝ) :
    maximalHLR (fun y => ‖g y‖ₑ ^ 2) x ≤
      ENNReal.ofReal (a ^ 2) * maximalHLR (E.indicator (1 : ℝ → ℝ)) x := by
  refine maximalHLR_le_mul ENNReal.ofReal_ne_top (fun y => ?_) x
  have h1 := enorm_le_mul_enorm_indicator ha hg y
  have hind : ‖E.indicator (1 : ℝ → ℝ) y‖ₑ ^ 2 = ‖E.indicator (1 : ℝ → ℝ) y‖ₑ := by
    by_cases hy : y ∈ E <;> simp [hy]
  show ‖(‖g y‖ₑ ^ 2 : ℝ≥0∞)‖ₑ ≤ _
  rw [enorm_eq_self]
  calc ‖g y‖ₑ ^ 2 ≤ (ENNReal.ofReal a * ‖E.indicator (1 : ℝ → ℝ) y‖ₑ) ^ 2 := by gcongr
    _ = ENNReal.ofReal (a ^ 2) * ‖E.indicator (1 : ℝ → ℝ) y‖ₑ := by
        rw [mul_pow, hind, ENNReal.ofReal_pow ha]

/-- `M g ≤ c` if `‖g‖ ≤ c` (for the bounded function `g₃`, `|g₃| ≤ √2`). -/
theorem maximalHLR_le_of_norm_le {g : ℝ → ℂ} {c : ℝ} (h : ∀ y, ‖g y‖ ≤ c) (x : ℝ) :
    maximalHLR g x ≤ ENNReal.ofReal c :=
  maximalHLR_le_of_enorm_le (fun y => by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (h y)) x

/-- `M(‖g‖²) ≤ c²` if `‖g‖ ≤ c`. -/
theorem maximalHLR_enorm_sq_le_of_norm_le {g : ℝ → ℂ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ y, ‖g y‖ ≤ c)
    (x : ℝ) : maximalHLR (fun y => ‖g y‖ₑ ^ 2) x ≤ ENNReal.ofReal (c ^ 2) := by
  refine maximalHLR_le_of_enorm_le (fun y => ?_) x
  show ‖(‖g y‖ₑ ^ 2 : ℝ≥0∞)‖ₑ ≤ _
  rw [enorm_eq_self, ENNReal.ofReal_pow hc]
  gcongr
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (h y)

/-- **(M5), packet domination for `‖g‖ ≤ a 1_E`**: with the hypotheses of `enorm_pairing_le_maximalHLR`,
`|I|^{-1/2} |⟨g, φ⟩| ≤ 10 (1 + R)² K a · M 1_E (x₀)`. -/
theorem enorm_pairing_le_maximalHLR_indicator {N : ℕ} (hN : 2 ≤ N) {I ω : Set ℝ} {φ : ℝ → ℂ}
    (hφ : IsAdapted N I ω φ) (hL : 0 < (volume I).toReal) {E : Set ℝ} {a : ℝ} (ha : 0 ≤ a)
    {g : ℝ → ℂ} (hg : Measurable g) (hdom : ∀ y, ‖g y‖ ≤ a * E.indicator (1 : ℝ → ℝ) y)
    {K R x₀ : ℝ} (hK : 1 ≤ K) (hR : 0 ≤ R)
    (hx₀ : |x₀ - intervalCentre I| ≤ R * (K * (volume I).toReal)) :
    ENNReal.ofReal ((volume I).toReal ^ (-(1 : ℝ) / 2)) * ‖pairing g φ‖ₑ ≤
      ENNReal.ofReal (10 * (1 + R) ^ 2 * K * a) *
        maximalHLR (E.indicator (1 : ℝ → ℝ)) x₀ := by
  refine (enorm_pairing_le_maximalHLR hN hφ hL hg hK hR hx₀).trans ?_
  calc ENNReal.ofReal (10 * (1 + R) ^ 2 * K) * maximalHLR g x₀
      ≤ ENNReal.ofReal (10 * (1 + R) ^ 2 * K) *
          (ENNReal.ofReal a * maximalHLR (E.indicator (1 : ℝ → ℝ)) x₀) :=
        mul_le_mul' le_rfl (maximalHLR_le_mul_indicator ha hdom x₀)
    _ = ENNReal.ofReal (10 * (1 + R) ^ 2 * K * a) * maximalHLR (E.indicator (1 : ℝ → ℝ)) x₀ := by
        have hK0 : 0 ≤ K := by linarith
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

/-- **(M5), `L²`-weight bound for `‖g‖ ≤ a 1_E`**:
`∫ (1 + |y - c|/L)^{-2} ‖g(y)‖² dy ≤ 10 (1 + R)² L' a² · M 1_E (x₀)`
(for `g = |E|^{-1/2} h`, `|h| ≤ 1_E`: `≤ 10 (1 + R)² L' |E|^{-1} M 1_E (x₀)`, the bound `D_k` of C10b). -/
theorem lintegral_weight_enorm_sq_le_maximalHLR_indicator {L L' R c x₀ : ℝ} (hL : 0 < L)
    (hLL : L ≤ L') (hR : 0 ≤ R) (hx₀ : |x₀ - c| ≤ R * L') {E : Set ℝ} {a : ℝ} (ha : 0 ≤ a)
    {g : ℝ → ℂ} (hg : Measurable g) (hdom : ∀ y, ‖g y‖ ≤ a * E.indicator (1 : ℝ → ℝ) y) :
    ∫⁻ y, ENNReal.ofReal ((1 + |y - c| / L) ^ (-2 : ℤ)) * ‖g y‖ₑ ^ 2 ≤
      ENNReal.ofReal (10 * (1 + R) ^ 2 * L' * a ^ 2) *
        maximalHLR (E.indicator (1 : ℝ → ℝ)) x₀ := by
  refine (lintegral_weight_enorm_sq_le_maximalHLR hL hLL hR hx₀ hg).trans ?_
  calc ENNReal.ofReal (10 * (1 + R) ^ 2 * L') * maximalHLR (fun y => ‖g y‖ₑ ^ 2) x₀
      ≤ ENNReal.ofReal (10 * (1 + R) ^ 2 * L') *
          (ENNReal.ofReal (a ^ 2) * maximalHLR (E.indicator (1 : ℝ → ℝ)) x₀) :=
        mul_le_mul' le_rfl (maximalHLR_enorm_sq_le_mul_indicator ha hdom x₀)
    _ = ENNReal.ofReal (10 * (1 + R) ^ 2 * L' * a ^ 2) *
          maximalHLR (E.indicator (1 : ℝ → ℝ)) x₀ := by
        have hL' : 0 ≤ L' := (hL.trans_le hLL).le
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

/-! ### The facts about `g_k` used by C9 -/

/-- If `x ∉ exceptionalSet E C₀` and `‖g‖ ≤ a 1_E` then `M g (x) ≤ a C₀ |E|` (`a = |E|^{-1}` gives `C₀`,
`a = |E|^{-1/2}` gives `C₀ |E|^{1/2}`). -/
theorem maximalHLR_le_of_notMem_exceptionalSet {E : Set ℝ} {C₀ a : ℝ} {x : ℝ}
    (hx : x ∉ exceptionalSet E C₀) (hC : 0 ≤ C₀) (ha : 0 ≤ a) (htop : volume E ≠ ⊤) {g : ℝ → ℂ}
    (hdom : ∀ y, ‖g y‖ ≤ a * E.indicator (1 : ℝ → ℝ) y) :
    maximalHLR g x ≤ ENNReal.ofReal (a * C₀ * (volume E).toReal) := by
  calc maximalHLR g x ≤ ENNReal.ofReal a * maximalHLR (E.indicator (1 : ℝ → ℝ)) x :=
        maximalHLR_le_mul_indicator ha hdom x
    _ ≤ ENNReal.ofReal a * (ENNReal.ofReal C₀ * volume E) :=
        mul_le_mul' le_rfl (maximalHLR_indicator_le_of_notMem hx)
    _ = ENNReal.ofReal (a * C₀ * (volume E).toReal) := by
        rw [ENNReal.ofReal_mul (mul_nonneg ha hC), ENNReal.ofReal_mul ha,
          ENNReal.ofReal_toReal htop, mul_assoc]

/-- `M(‖g‖²)(x) ≤ a² C₀ |E|` for `x ∉ exceptionalSet E C₀` and `‖g‖ ≤ a 1_E`. -/
theorem maximalHLR_enorm_sq_le_of_notMem_exceptionalSet {E : Set ℝ} {C₀ a : ℝ} {x : ℝ}
    (hx : x ∉ exceptionalSet E C₀) (hC : 0 ≤ C₀) (ha : 0 ≤ a) (htop : volume E ≠ ⊤) {g : ℝ → ℂ}
    (hdom : ∀ y, ‖g y‖ ≤ a * E.indicator (1 : ℝ → ℝ) y) :
    maximalHLR (fun y => ‖g y‖ₑ ^ 2) x ≤ ENNReal.ofReal (a ^ 2 * C₀ * (volume E).toReal) := by
  calc maximalHLR (fun y => ‖g y‖ₑ ^ 2) x
      ≤ ENNReal.ofReal (a ^ 2) * maximalHLR (E.indicator (1 : ℝ → ℝ)) x :=
        maximalHLR_enorm_sq_le_mul_indicator ha hdom x
    _ ≤ ENNReal.ofReal (a ^ 2) * (ENNReal.ofReal C₀ * volume E) :=
        mul_le_mul' le_rfl (maximalHLR_indicator_le_of_notMem hx)
    _ = ENNReal.ofReal (a ^ 2 * C₀ * (volume E).toReal) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg a) hC), ENNReal.ofReal_mul (sq_nonneg a),
          ENNReal.ofReal_toReal htop, mul_assoc]

/-- `L¹`-normalization (`g₁ = |E₁|^{-1} h₁`): `M g (x) ≤ C₀` for `x ∉ exceptionalSet E C₀`. -/
theorem maximalHLR_le_of_notMem_exceptionalSet_L1 {E : Set ℝ} {C₀ : ℝ} {x : ℝ}
    (hx : x ∉ exceptionalSet E C₀) (hC : 0 ≤ C₀) (h0 : volume E ≠ 0) (htop : volume E ≠ ⊤)
    {g : ℝ → ℂ} (hdom : ∀ y, ‖g y‖ ≤ (volume E).toReal⁻¹ * E.indicator (1 : ℝ → ℝ) y) :
    maximalHLR g x ≤ ENNReal.ofReal C₀ := by
  have hpos : 0 < (volume E).toReal := ENNReal.toReal_pos h0 htop
  refine (maximalHLR_le_of_notMem_exceptionalSet hx hC (by positivity) htop hdom).trans_eq ?_
  congr 1
  field_simp

/-- `L²`-normalization (`g₂ = |E₂|^{-1/2} h₂`): `M(‖g‖²)(x) ≤ C₀` for `x ∉ exceptionalSet E C₀`
(that is, `(M² g)² ≤ C₀`). -/
theorem maximalHLR_enorm_sq_le_of_notMem_exceptionalSet_L2 {E : Set ℝ} {C₀ : ℝ} {x : ℝ}
    (hx : x ∉ exceptionalSet E C₀) (hC : 0 ≤ C₀) (h0 : volume E ≠ 0) (htop : volume E ≠ ⊤)
    {g : ℝ → ℂ}
    (hdom : ∀ y, ‖g y‖ ≤ (volume E).toReal ^ (-(1 : ℝ) / 2) * E.indicator (1 : ℝ → ℝ) y) :
    maximalHLR (fun y => ‖g y‖ₑ ^ 2) x ≤ ENNReal.ofReal C₀ := by
  have hpos : 0 < (volume E).toReal := ENNReal.toReal_pos h0 htop
  refine (maximalHLR_enorm_sq_le_of_notMem_exceptionalSet hx hC (by positivity) htop hdom).trans_eq ?_
  congr 1
  have : ((volume E).toReal ^ (-(1 : ℝ) / 2)) ^ 2 = (volume E).toReal⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num [Real.rpow_neg_one]
  rw [this]
  field_simp

/-! ### Base point `x₀ ∈ I`, real-valued corollaries -/

/-- An order-connected set of finite positive measure is bounded, and its measure is `sup - inf`. -/
theorem ordConnected_bounds {I : Set ℝ} (hI : I.OrdConnected) (hL : 0 < (volume I).toReal) :
    BddAbove I ∧ BddBelow I ∧ (volume I).toReal = sSup I - sInf I := by
  have hfin : volume I ≠ ⊤ := (ENNReal.toReal_pos_iff.1 hL).2.ne
  have hne : I.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at hL
    simp at hL
  obtain ⟨x, hx⟩ := hne
  have hbA : BddAbove I := by
    by_contra hnb
    rw [not_bddAbove_iff] at hnb
    obtain ⟨y, hy, hlt⟩ := hnb (x + (volume I).toReal + 1)
    have h1 : volume (Icc x y) ≤ volume I := measure_mono (hI.out hx hy)
    rw [Real.volume_Icc] at h1
    have h2 := ENNReal.toReal_mono hfin h1
    rw [ENNReal.toReal_ofReal (by linarith)] at h2
    linarith
  have hbB : BddBelow I := by
    by_contra hnb
    rw [not_bddBelow_iff] at hnb
    obtain ⟨y, hy, hlt⟩ := hnb (x - (volume I).toReal - 1)
    have h1 : volume (Icc y x) ≤ volume I := measure_mono (hI.out hy hx)
    rw [Real.volume_Icc] at h1
    have h2 := ENNReal.toReal_mono hfin h1
    rw [ENNReal.toReal_ofReal (by linarith)] at h2
    linarith
  have hxi : sInf I ≤ x := csInf_le hbB hx
  have hxs : x ≤ sSup I := le_csSup hbA hx
  have hsub1 : I ⊆ Icc (sInf I) (sSup I) := fun z hz => ⟨csInf_le hbB hz, le_csSup hbA hz⟩
  have hsub2 : Ioo (sInf I) (sSup I) ⊆ I := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := exists_lt_of_csInf_lt ⟨x, hx⟩ hz.1
    obtain ⟨y', hy', hzy⟩ := exists_lt_of_lt_csSup ⟨x, hx⟩ hz.2
    exact hI.out hy hy' ⟨hyz.le, hzy.le⟩
  refine ⟨hbA, hbB, le_antisymm ?_ ?_⟩
  · have h1 := measure_mono (μ := volume) hsub1
    rw [Real.volume_Icc] at h1
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h1).trans_eq
      (ENNReal.toReal_ofReal (by linarith))
  · have h1 := measure_mono (μ := volume) hsub2
    rw [Real.volume_Ioo] at h1
    have h2 := ENNReal.toReal_mono hfin h1
    rwa [ENNReal.toReal_ofReal (by linarith)] at h2

/-- A point of an interval `I` (order-connected, of finite positive length) lies within `|I|/2` of its
centre `c(I) = (inf I + sup I)/2`. -/
theorem abs_sub_intervalCentre_le_of_mem {I : Set ℝ} (hI : I.OrdConnected)
    (hL : 0 < (volume I).toReal) {x : ℝ} (hx : x ∈ I) :
    |x - intervalCentre I| ≤ (volume I).toReal / 2 := by
  obtain ⟨hbA, hbB, hvol⟩ := ordConnected_bounds hI hL
  have hxi : sInf I ≤ x := csInf_le hbB hx
  have hxs : x ≤ sSup I := le_csSup hbA hx
  unfold intervalCentre
  rw [abs_le]
  constructor <;> linarith

/-- If an interval `I` lies in an interval `J'` (both order-connected of finite positive length) and
`x ∈ J'`, then `|x - c(I)| ≤ |J'|` (the base point of C10b: `I ⊆ J ⊆ Ĵ`, `x₀ ∈ Ĵ`). -/
theorem abs_sub_intervalCentre_le_of_subset {I J : Set ℝ} (hI : I.OrdConnected)
    (hIL : 0 < (volume I).toReal) (hJ : J.OrdConnected) (hJL : 0 < (volume J).toReal)
    (hIJ : I ⊆ J) {x : ℝ} (hx : x ∈ J) : |x - intervalCentre I| ≤ (volume J).toReal := by
  obtain ⟨hbA, hbB, hvol⟩ := ordConnected_bounds hJ hJL
  obtain ⟨hbA', hbB', -⟩ := ordConnected_bounds hI hIL
  have hne : I.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at hIL
    simp at hIL
  have h1 : sInf J ≤ sInf I := csInf_le_csInf hbB hne hIJ
  have h2 : sSup I ≤ sSup J := csSup_le_csSup hbA hne hIJ
  have h3 : sInf I ≤ sSup I := csInf_le_csSup hne hbB' hbA'
  have hxi : sInf J ≤ x := csInf_le hbB hx
  have hxs : x ≤ sSup J := le_csSup hbA hx
  unfold intervalCentre
  rw [abs_le]
  constructor <;> linarith

/-- **(M5) for `x₀ ∈ I`**: `|I|^{-1/2} |⟨g, φ⟩| ≤ (45/2) · M g (x₀)` (`K = 1`, `R = 1/2`; the constant is
independent of `N`). -/
theorem enorm_pairing_le_maximalHLR_of_mem {N : ℕ} (hN : 2 ≤ N) {I ω : Set ℝ} {φ : ℝ → ℂ}
    (hφ : IsAdapted N I ω φ) (hI : I.OrdConnected) (hL : 0 < (volume I).toReal) {g : ℝ → ℂ}
    (hg : Measurable g) {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    ENNReal.ofReal ((volume I).toReal ^ (-(1 : ℝ) / 2)) * ‖pairing g φ‖ₑ ≤
      ENNReal.ofReal (45 / 2) * maximalHLR g x₀ := by
  have h := enorm_pairing_le_maximalHLR hN hφ hL hg (K := 1) (R := 1 / 2) le_rfl (by norm_num)
    (x₀ := x₀) (by rw [one_mul]; exact (abs_sub_intervalCentre_le_of_mem hI hL hx₀).trans_eq (by ring))
  have e : 10 * (1 + 1 / 2 : ℝ) ^ 2 * 1 = 45 / 2 := by norm_num
  rwa [e] at h

/-- Real form of (M5) for `‖g‖ ≤ a 1_E`: if `M 1_E (x₀) ≤ μ` then
`|I|^{-1/2} |⟨g, φ⟩| ≤ 10 (1 + R)² K a μ`. -/
theorem norm_pairing_le_of_maximalHLR_indicator_le {N : ℕ} (hN : 2 ≤ N) {I ω : Set ℝ}
    {φ : ℝ → ℂ} (hφ : IsAdapted N I ω φ) (hL : 0 < (volume I).toReal) {E : Set ℝ} {a : ℝ}
    (ha : 0 ≤ a) {g : ℝ → ℂ} (hg : Measurable g)
    (hdom : ∀ y, ‖g y‖ ≤ a * E.indicator (1 : ℝ → ℝ) y) {K R x₀ μ : ℝ} (hK : 1 ≤ K) (hR : 0 ≤ R)
    (hx₀ : |x₀ - intervalCentre I| ≤ R * (K * (volume I).toReal)) (hμ : 0 ≤ μ)
    (hM : maximalHLR (E.indicator (1 : ℝ → ℝ)) x₀ ≤ ENNReal.ofReal μ) :
    (volume I).toReal ^ (-(1 : ℝ) / 2) * ‖pairing g φ‖ ≤ 10 * (1 + R) ^ 2 * K * a * μ := by
  have hK0 : 0 ≤ K := by linarith
  have h := (enorm_pairing_le_maximalHLR_indicator hN hφ hL ha hg hdom hK hR hx₀).trans
    (mul_le_mul' le_rfl hM)
  rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  exact h

/-- Real form of the `L²`-weight bound: for `‖g‖ ≤ a 1_E` with `M 1_E (x₀) ≤ μ`,
`∫ (1 + |y - c|/L)^{-2} ‖g(y)‖² dy ≤ 10 (1 + R)² L' a² μ`. -/
theorem integral_weight_norm_sq_le_of_maximalHLR_indicator_le {L L' R c x₀ μ : ℝ} (hL : 0 < L)
    (hLL : L ≤ L') (hR : 0 ≤ R) (hx₀ : |x₀ - c| ≤ R * L') {E : Set ℝ} {a : ℝ} (ha : 0 ≤ a)
    {g : ℝ → ℂ} (hg : Measurable g) (hdom : ∀ y, ‖g y‖ ≤ a * E.indicator (1 : ℝ → ℝ) y)
    (hμ : 0 ≤ μ) (hM : maximalHLR (E.indicator (1 : ℝ → ℝ)) x₀ ≤ ENNReal.ofReal μ) :
    ∫ y, (1 + |y - c| / L) ^ (-2 : ℤ) * ‖g y‖ ^ 2 ≤ 10 * (1 + R) ^ 2 * L' * a ^ 2 * μ := by
  have hL' : 0 ≤ L' := (hL.trans_le hLL).le
  have hnn : 0 ≤ᵐ[volume] fun y : ℝ => (1 + |y - c| / L) ^ (-2 : ℤ) * ‖g y‖ ^ 2 :=
    Eventually.of_forall fun y => by positivity
  have hmeas : Measurable fun y : ℝ => (1 + |y - c| / L) ^ (-2 : ℤ) * ‖g y‖ ^ 2 := by
    have : Measurable fun y : ℝ => (1 + |y - c| / L) ^ (-2 : ℤ) := by fun_prop
    exact this.mul (hg.norm.pow_const 2)
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  have h := (lintegral_weight_enorm_sq_le_maximalHLR_indicator hL hLL hR hx₀ ha hg hdom).trans
    (mul_le_mul' le_rfl hM)
  rw [← ENNReal.ofReal_mul (by positivity)] at h
  refine le_trans (le_of_eq ?_) h
  refine lintegral_congr fun y => ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-! ### Base points in an interval containing `I` (C10b) and the `N`-weight for `x₀ ∈ J` (C7') -/

/-- The weight bound with base point `x₀ ∈ J`, centre `c(J)` and scale `|J|` (`J` order-connected):
`|J|^{-1} ∫ (1 + |y - c(J)|/|J|)^{-2} W(y) dy ≤ (45/2) · M W (x₀)`. -/
theorem lintegral_weight_le_maximalHLR_of_mem {J : Set ℝ} (hJ : J.OrdConnected)
    (hL : 0 < (volume J).toReal) {x₀ : ℝ} (hx₀ : x₀ ∈ J) {W : ℝ → ℝ≥0∞} (hW : Measurable W) :
    ∫⁻ y, ENNReal.ofReal ((1 + |y - intervalCentre J| / (volume J).toReal) ^ (-2 : ℤ)) * W y ≤
      ENNReal.ofReal (45 / 2 * (volume J).toReal) * maximalHLR W x₀ := by
  have h := lintegral_weight_le_maximalHLR (c := intervalCentre J) hL le_rfl
    (R := 1 / 2) (by norm_num) (x₀ := x₀)
    (by rw [mul_comm]; exact (abs_sub_intervalCentre_le_of_mem hJ hL hx₀).trans_eq (by ring)) hW
  have e : 10 * (1 + 1 / 2 : ℝ) ^ 2 * (volume J).toReal = 45 / 2 * (volume J).toReal := by ring
  rwa [e] at h

/-! ### Real-valued forms for the base points of C9 and C10b -/

/-- Real form of (M5) for `x₀ ∈ I`: if `M g (x₀) ≤ μ` then `|I|^{-1/2} |⟨g, φ⟩| ≤ (45/2) μ`. -/
theorem norm_pairing_le_of_maximalHLR_le_of_mem {N : ℕ} (hN : 2 ≤ N) {I ω : Set ℝ} {φ : ℝ → ℂ}
    (hφ : IsAdapted N I ω φ) (hI : I.OrdConnected) (hL : 0 < (volume I).toReal) {g : ℝ → ℂ}
    (hg : Measurable g) {x₀ μ : ℝ} (hx₀ : x₀ ∈ I) (hμ : 0 ≤ μ)
    (hM : maximalHLR g x₀ ≤ ENNReal.ofReal μ) :
    (volume I).toReal ^ (-(1 : ℝ) / 2) * ‖pairing g φ‖ ≤ 45 / 2 * μ := by
  have h := (enorm_pairing_le_maximalHLR_of_mem hN hφ hI hL hg hx₀).trans (mul_le_mul' le_rfl hM)
  rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  exact h

/-- **C10b, `S_k`-bound**: `x₀ ∈ J ∖ exceptionalSet E C₀` with `I ⊆ J` intervals, `|J| ≤ 2 K |I|`,
`φ` adapted to `(I, ω)` with `N ≥ 2`, and `‖g‖ ≤ |E|^{-1/2} 1_E` (`g = |E|^{-1/2} h`, `|h| ≤ 1_E`):
`|I|^{-1/2} |⟨g, φ⟩| ≤ 90 K C₀ |E|^{1/2}`. -/
theorem norm_pairing_le_of_notMem_exceptionalSet_of_subset {N : ℕ} (hN : 2 ≤ N) {I J ω : Set ℝ}
    {φ : ℝ → ℂ} (hφ : IsAdapted N I ω φ) (hI : I.OrdConnected) (hL : 0 < (volume I).toReal)
    (hJ : J.OrdConnected) (hJL : 0 < (volume J).toReal) (hIJ : I ⊆ J) {E : Set ℝ} {C₀ : ℝ}
    (h0 : volume E ≠ 0) (htop : volume E ≠ ⊤) (hC : 0 ≤ C₀) {g : ℝ → ℂ} (hg : Measurable g)
    (hdom : ∀ y, ‖g y‖ ≤ (volume E).toReal ^ (-(1 : ℝ) / 2) * E.indicator (1 : ℝ → ℝ) y)
    {x₀ K : ℝ} (hK : 1 ≤ K) (hx₀ : x₀ ∈ J) (hxE : x₀ ∉ exceptionalSet E C₀)
    (hJK : (volume J).toReal ≤ 2 * (K * (volume I).toReal)) :
    (volume I).toReal ^ (-(1 : ℝ) / 2) * ‖pairing g φ‖ ≤
      90 * K * C₀ * (volume E).toReal ^ ((1 : ℝ) / 2) := by
  have hpos : 0 < (volume E).toReal := ENNReal.toReal_pos h0 htop
  have hK0 : 0 ≤ K := by linarith
  have ha : 0 ≤ (volume E).toReal ^ (-(1 : ℝ) / 2) := by positivity
  have hM : maximalHLR (E.indicator (1 : ℝ → ℝ)) x₀ ≤ ENNReal.ofReal (C₀ * (volume E).toReal) := by
    rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal htop]
    exact maximalHLR_indicator_le_of_notMem hxE
  have h := norm_pairing_le_of_maximalHLR_indicator_le hN hφ hL ha hg hdom hK (R := 2)
    (by norm_num) (x₀ := x₀) ((abs_sub_intervalCentre_le_of_subset hI hL hJ hJL hIJ hx₀).trans hJK)
    (μ := C₀ * (volume E).toReal) (by positivity) hM
  refine h.trans_eq ?_
  have e : (volume E).toReal ^ ((1 : ℝ) / 2) =
      (volume E).toReal ^ (-(1 : ℝ) / 2) * (volume E).toReal := by
    rw [← Real.rpow_add_one hpos.ne']
    norm_num
  rw [e]
  ring

/-- **C10b, `D_k`-bound**: under the same hypotheses on `I, J, x₀, E`, and `‖g‖ ≤ |E|^{-1/2} 1_E`,
`∫ (1 + |y - c(I)|/|I|)^{-2} ‖g(y)‖² dy ≤ 90 K |I| C₀`. -/
theorem integral_weight_norm_sq_le_of_notMem_exceptionalSet_of_subset {I J : Set ℝ}
    (hI : I.OrdConnected) (hL : 0 < (volume I).toReal) (hJ : J.OrdConnected)
    (hJL : 0 < (volume J).toReal) (hIJ : I ⊆ J) {E : Set ℝ} {C₀ : ℝ} (h0 : volume E ≠ 0)
    (htop : volume E ≠ ⊤) (hC : 0 ≤ C₀) {g : ℝ → ℂ} (hg : Measurable g)
    (hdom : ∀ y, ‖g y‖ ≤ (volume E).toReal ^ (-(1 : ℝ) / 2) * E.indicator (1 : ℝ → ℝ) y)
    {x₀ K : ℝ} (hK : 1 ≤ K) (hx₀ : x₀ ∈ J) (hxE : x₀ ∉ exceptionalSet E C₀)
    (hJK : (volume J).toReal ≤ 2 * (K * (volume I).toReal)) :
    ∫ y, (1 + |y - intervalCentre I| / (volume I).toReal) ^ (-2 : ℤ) * ‖g y‖ ^ 2 ≤
      90 * K * (volume I).toReal * C₀ := by
  have hpos : 0 < (volume E).toReal := ENNReal.toReal_pos h0 htop
  have hK0 : 0 ≤ K := by linarith
  have ha : 0 ≤ (volume E).toReal ^ (-(1 : ℝ) / 2) := by positivity
  have hKL : (volume I).toReal ≤ K * (volume I).toReal := by nlinarith
  have hM : maximalHLR (E.indicator (1 : ℝ → ℝ)) x₀ ≤ ENNReal.ofReal (C₀ * (volume E).toReal) := by
    rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal htop]
    exact maximalHLR_indicator_le_of_notMem hxE
  have h := integral_weight_norm_sq_le_of_maximalHLR_indicator_le hL hKL (R := 2) (by norm_num)
    (x₀ := x₀) (c := intervalCentre I)
    ((abs_sub_intervalCentre_le_of_subset hI hL hJ hJL hIJ hx₀).trans hJK) ha hg hdom
    (μ := C₀ * (volume E).toReal) (by positivity) hM
  refine h.trans_eq ?_
  have e : ((volume E).toReal ^ (-(1 : ℝ) / 2)) ^ 2 = (volume E).toReal⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num [Real.rpow_neg_one]
  rw [e]
  field_simp
  ring

/-! ### `L²`-weight bounds for a base point `x₀ ∈ I` (C8(b), C9) -/

/-! ### (M3) for `q = 2`: Jensen and weak type `(2,2)` -/

end PrimeBHT.TimeFrequency.Tile
