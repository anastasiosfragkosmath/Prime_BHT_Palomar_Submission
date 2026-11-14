module

public import PrimeBHT.TimeFrequency.X2.Psp.OverlapSup
public import PrimeBHT.TimeFrequency.X2.CZ.Minkowski

/-!
# X2, V13 part 2 (B): the overlapping construction `G = Π̃F - Σ cφ` and (O1) from the coefficient bound

`docs/audits/X2-V13-route-check.md` §2.6, MTT2 §8.  For a part `TA` of a good tree (top `W`), lattice scales `L`, the slot frequency
`θ = ξ_T f_k` and a bounded measurable `F`:

* `overlapA`, `overlapPi`: `Π̃F(y) = T_{σ(y)} F(y)`, `σ(y)` the finest lattice scale in `L` with `y ∈ Ẽ_σ` (`T_σ = tmult (lowSym θ σ)`);
* `leftPhi`, `rightPhi`: tent bumps of height `8` on `leftBump σ x` / `rightBump σ x` (`∫ φ = 2^σ`);
* `overlapBumps`, `overlapG`: `G = Π̃F - Σ_{σ ∈ L} Σ_{x ∈ ∂Ẽ_σ} (c^ℓ_x φ^ℓ_x + c^r_x φ^r_x)` for ANY coefficient families `cL, cR`;
* `overlap_O1_of_coeff` (O1): if `‖c‖_{L^s(Y)} ≤ C_c engTop` (the coefficient bound O-b), then `G` is measurable, bounded by `C engTop`
  and vanishes off `3 I_t`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-! ## Tent bumps -/

/-- The tent function of height `h` on `[a, b]`. -/
def tent (a b h y : ℝ) : ℝ := h * max 0 (1 - |y - (a + b) / 2| / ((b - a) / 2))

theorem tent_nonneg {a b h : ℝ} (hh : 0 ≤ h) (y : ℝ) : 0 ≤ tent a b h y :=
  mul_nonneg hh (le_max_left _ _)

theorem tent_le {a b h : ℝ} (hab : a < b) (hh : 0 ≤ h) (y : ℝ) : tent a b h y ≤ h := by
  unfold tent
  have hp : 0 < (b - a) / 2 := by linarith
  have : max 0 (1 - |y - (a + b) / 2| / ((b - a) / 2)) ≤ 1 := by
    refine max_le (by norm_num) ?_
    have : 0 ≤ |y - (a + b) / 2| / ((b - a) / 2) := by positivity
    linarith
  nlinarith

theorem continuous_tent (a b h : ℝ) : Continuous (tent a b h) := by
  unfold tent; fun_prop

theorem tent_eq_zero {a b h y : ℝ} (hab : a < b) (hy : y ∉ Ioo a b) : tent a b h y = 0 := by
  unfold tent
  have hp : 0 < (b - a) / 2 := by linarith
  have : 1 - |y - (a + b) / 2| / ((b - a) / 2) ≤ 0 := by
    have h1 : (b - a) / 2 ≤ |y - (a + b) / 2| := by
      by_contra hc
      push Not at hc
      rw [abs_lt] at hc
      exact hy ⟨by linarith [hc.1], by linarith [hc.2]⟩
    have : 1 ≤ |y - (a + b) / 2| / ((b - a) / 2) := by rw [le_div_iff₀ hp]; linarith
    linarith
  rw [max_eq_left this, mul_zero]

/-- The bump at a left endpoint: height `8` on `leftBump σ x` (`∫ = 2^σ`). -/
def leftPhi (σ : ℤ) (x : ℝ) : ℝ → ℝ := tent (x - (2 : ℝ) ^ (σ - 1)) (x - (2 : ℝ) ^ (σ - 2)) 8

/-- The bump at a right endpoint. -/
def rightPhi (σ : ℤ) (x : ℝ) : ℝ → ℝ := tent (x + (2 : ℝ) ^ (σ - 2)) (x + (2 : ℝ) ^ (σ - 1)) 8

theorem leftBump_lt (σ : ℤ) (x : ℝ) : x - (2 : ℝ) ^ (σ - 1) < x - (2 : ℝ) ^ (σ - 2) := by
  have := zpow_two_pos (σ - 2)
  have e := zpow_sub_one_eq σ
  linarith

theorem rightBump_lt (σ : ℤ) (x : ℝ) : x + (2 : ℝ) ^ (σ - 2) < x + (2 : ℝ) ^ (σ - 1) := by
  have := zpow_two_pos (σ - 2)
  have e := zpow_sub_one_eq σ
  linarith

theorem leftPhi_nonneg (σ : ℤ) (x y : ℝ) : 0 ≤ leftPhi σ x y := tent_nonneg (by norm_num) y
theorem leftPhi_le (σ : ℤ) (x y : ℝ) : leftPhi σ x y ≤ 8 := tent_le (leftBump_lt σ x) (by norm_num) y
theorem rightPhi_nonneg (σ : ℤ) (x y : ℝ) : 0 ≤ rightPhi σ x y := tent_nonneg (by norm_num) y
theorem rightPhi_le (σ : ℤ) (x y : ℝ) : rightPhi σ x y ≤ 8 := tent_le (rightBump_lt σ x) (by norm_num) y

theorem leftPhi_eq_zero {σ : ℤ} {x y : ℝ} (hy : y ∉ leftBump σ x) : leftPhi σ x y = 0 :=
  tent_eq_zero (leftBump_lt σ x) hy

theorem rightPhi_eq_zero {σ : ℤ} {x y : ℝ} (hy : y ∉ rightBump σ x) : rightPhi σ x y = 0 :=
  tent_eq_zero (rightBump_lt σ x) hy

theorem continuous_leftPhi (σ : ℤ) (x : ℝ) : Continuous (leftPhi σ x) := continuous_tent _ _ _
theorem continuous_rightPhi (σ : ℤ) (x : ℝ) : Continuous (rightPhi σ x) := continuous_tent _ _ _

/-! ## The phase `e(θ y)` (the bumps live in the frame centred at `θ`) -/

/-- The phase `e(θ y) = exp(2π i θ y)`: the correction bumps are `e(θ y) φ(y)` (MTT2 normalises `ξ_T = 0` by modulation). -/
def ovPhase (θ y : ℝ) : ℂ := Complex.exp (((2 * π * θ * y : ℝ) : ℂ) * Complex.I)

theorem norm_ovPhase (θ y : ℝ) : ‖ovPhase θ y‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem continuous_ovPhase (θ : ℝ) : Continuous (ovPhase θ) := by
  unfold ovPhase; fun_prop

/-! ## `Π̃F` -/

theorem yNorm_zero_ov {P : ℕ} [NeZero P] {s : ℝ} (hs : 0 < s) : yNorm s (0 : ZMod P → ℂ) = 0 := by
  unfold yNorm
  simp [Real.zero_rpow hs.ne', Real.zero_rpow (inv_ne_zero hs.ne')]

section Pi

variable {P : ℕ} [NeZero P]

/-- `A_σ = Ẽ_σ ∖ ⋃_{σ' < σ} Ẽ_{σ'}`: the points whose finest lattice scale is `σ`. -/
def overlapA (TA : Finset TriTile) (W : ℤ × ℤ) (L : Finset ℤ) (σ : ℤ) : Set ℝ :=
  eTil TA W σ \ ⋃ σ' ∈ L.filter (fun τ => τ < σ), eTil TA W σ'

/-- `Π̃F(y) = T_{σ(y)} F(y)`, `σ(y)` the finest lattice scale in `L` with `y ∈ Ẽ_σ` (`0` if there is none). -/
def overlapPi (TA : Finset TriTile) (W : ℤ × ℤ) (L : Finset ℤ) (θ : ℝ) (F : ℝ → ZMod P → ℂ) : ℝ → ZMod P → ℂ :=
  fun y => ∑ σ ∈ L, (overlapA TA W L σ).indicator (fun y => tmult (lowSym θ σ) F y) y

theorem measurableSet_eTil (TA : Finset TriTile) (W : ℤ × ℤ) (σ : ℤ) : MeasurableSet (eTil TA W σ) := by
  unfold eTil
  exact MeasurableSet.biUnion (Set.to_countable _) fun v _ => measurableSet_dyadicInt σ v

theorem measurableSet_overlapA (TA : Finset TriTile) (W : ℤ × ℤ) (L : Finset ℤ) (σ : ℤ) :
    MeasurableSet (overlapA TA W L σ) := by
  unfold overlapA
  exact (measurableSet_eTil _ _ _).diff
    (MeasurableSet.biUnion (Finset.countable_toSet _) fun τ _ => measurableSet_eTil _ _ _)

theorem overlapA_subset_eTil (TA : Finset TriTile) (W : ℤ × ℤ) (L : Finset ℤ) (σ : ℤ) :
    overlapA TA W L σ ⊆ eTil TA W σ := fun _ h => h.1

theorem overlapA_disjoint (TA : Finset TriTile) (W : ℤ × ℤ) {L : Finset ℤ} {σ σ' : ℤ} (hσ : σ ∈ L) (hσ' : σ' ∈ L)
    (hne : σ ≠ σ') {y : ℝ} (hy : y ∈ overlapA TA W L σ) : y ∉ overlapA TA W L σ' := by
  intro hy'
  rcases lt_or_gt_of_ne hne with h | h
  · -- `σ < σ'`: `y ∈ A_σ' ` excludes `Ẽ_σ`
    exact hy'.2 (Set.mem_biUnion (x := σ) (Finset.mem_filter.2 ⟨hσ, h⟩) hy.1)
  · exact hy.2 (Set.mem_biUnion (x := σ') (Finset.mem_filter.2 ⟨hσ', h⟩) hy'.1)

omit [NeZero P] in
theorem measurable_tmult_of_cont_kernel {m : ℝ → ℂ} (hK : Continuous (𝓕⁻ m)) {F : ℝ → ZMod P → ℂ}
    (hF : Measurable F) : Measurable (tmult m F) := by
  refine measurable_pi_iff.2 fun y => ?_
  have h1 : StronglyMeasurable (Function.uncurry fun (x z : ℝ) => 𝓕⁻ m (x - z) * F z y) :=
    ((hK.comp (continuous_fst.sub continuous_snd)).stronglyMeasurable).mul
      ((((measurable_pi_apply y).comp hF).comp measurable_snd).stronglyMeasurable)
  exact (h1.integral_prod_right).measurable

theorem continuous_fourierInv_lowSym (θ : ℝ) (σ : ℤ) : Continuous (𝓕⁻ (lowSym θ σ)) :=
  continuous_fourierInv_of_integrable' (integrable_of_far (contDiff_lowSym θ σ).continuous (c := θ)
    (r := 17 / 4 * (2 : ℝ) ^ (-σ)) (fun _ξ hξ => lowSym_eq_zero hξ.le))

theorem measurable_tmult_lowSym (θ : ℝ) (σ : ℤ) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) :
    Measurable (tmult (lowSym θ σ) F) :=
  measurable_tmult_of_cont_kernel (continuous_fourierInv_lowSym θ σ) hF

theorem measurable_overlapPi (TA : Finset TriTile) (W : ℤ × ℤ) (L : Finset ℤ) (θ : ℝ) {F : ℝ → ZMod P → ℂ}
    (hF : Measurable F) : Measurable (overlapPi TA W L θ F) := by
  unfold overlapPi
  exact Finset.measurable_sum L fun σ _ =>
    (measurable_tmult_lowSym θ σ hF).indicator (measurableSet_overlapA TA W L σ)

omit [NeZero P] in
theorem overlapPi_eq {TA : Finset TriTile} {W : ℤ × ℤ} {L : Finset ℤ} {θ : ℝ} {F : ℝ → ZMod P → ℂ} {σ : ℤ}
    (hσ : σ ∈ L) {y : ℝ} (hy : y ∈ overlapA TA W L σ) :
    overlapPi TA W L θ F y = tmult (lowSym θ σ) F y := by
  unfold overlapPi
  rw [Finset.sum_eq_single_of_mem σ hσ]
  · rw [Set.indicator_of_mem hy]
  · intro σ' hσ' hne
    rw [Set.indicator_of_notMem (overlapA_disjoint TA W hσ hσ' hne.symm hy)]

omit [NeZero P] in
theorem overlapPi_eq_zero {TA : Finset TriTile} {W : ℤ × ℤ} {L : Finset ℤ} {θ : ℝ} {F : ℝ → ZMod P → ℂ} {y : ℝ}
    (hy : ∀ σ ∈ L, y ∉ overlapA TA W L σ) : overlapPi TA W L θ F y = 0 := by
  unfold overlapPi
  exact Finset.sum_eq_zero fun σ hσ => Set.indicator_of_notMem (hy σ hσ) _

/-- `Π̃F` is bounded by `engTop` (O-a at the finest scale `σ(y)`). -/
theorem overlapPi_bound {𝔭 : Params} (h𝔭 : 𝔭.Admissible) (hJ2 : 2 ≤ 𝔭.J) {η' : ℝ → ℝ} (hη' : IsEtaCut 𝔭 η')
    {s q : ℝ} (hs : 1 ≤ s) (hq : 1 < q) {k : Fin 3} {F : ℝ → ZMod P → ℂ} (hF : Measurable F)
    (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) {TA Cs : Finset TriTile} (hsub : TA ⊆ Cs) {t : Top}
    (hov : ∀ R ∈ TA, IsOvSlot t k R.box) {L : Finset ℤ} (hlat : ∀ σ ∈ L, ∀ R ∈ TA, (𝔭.J : ℤ) ∣ R.box.scale - σ)
    (y : ℝ) :
    ENNReal.ofReal (yNorm s (overlapPi TA t.1 L (t.2 * freqDir k) F y)) ≤
      ENNReal.ofReal (oaConst 𝔭 q) * engTop 𝔭 s k F Cs q := by
  by_cases hy : ∃ σ ∈ L, y ∈ overlapA TA t.1 L σ
  · obtain ⟨σ, hσ, hyσ⟩ := hy
    rw [overlapPi_eq hσ hyσ]
    obtain ⟨v, hv, hyv⟩ := Set.mem_iUnion₂.1 (show y ∈ ⋃ v ∈ eTilKeys TA t.1 σ, dyadicInt σ v from hyσ.1)
    exact overlap_Oa h𝔭 hJ2 hη' hs hq hF hFb hsub hov (hlat σ hσ)
      ⟨y, dyadicInt_subset_dilate (by norm_num) σ v hyv, hyσ.1⟩ hyv
  · push Not at hy
    rw [overlapPi_eq_zero hy, yNorm_zero_ov (by linarith)]
    simp

/-! ## The bump part and `G = Π̃F - Σ cφ` -/

/-- `Σ_{σ ∈ L} Σ_{x ∈ ∂Ẽ_σ} (c^ℓ_x φ^ℓ_x + c^r_x φ^r_x)` for arbitrary (`Y`-valued) coefficient families. -/
def overlapBumps (TA : Finset TriTile) (W : ℤ × ℤ) (L : Finset ℤ) (θ : ℝ) (cL cR : ℤ → ℝ → ZMod P → ℂ) :
    ℝ → ZMod P → ℂ := fun y =>
  (∑ p ∈ L.sigma (fun σ => leftEnds TA W σ), (ovPhase θ y * ((leftPhi p.1 p.2 y : ℝ) : ℂ)) • cL p.1 p.2) +
    ∑ p ∈ L.sigma (fun σ => rightEnds TA W σ), (ovPhase θ y * ((rightPhi p.1 p.2 y : ℝ) : ℂ)) • cR p.1 p.2

/-- **MTT2's `G = Π̃F - Σ c φ`**, for arbitrary coefficient families `cL cR`. -/
def overlapG (TA : Finset TriTile) (W : ℤ × ℤ) (L : Finset ℤ) (θ : ℝ) (F : ℝ → ZMod P → ℂ)
    (cL cR : ℤ → ℝ → ZMod P → ℂ) : ℝ → ZMod P → ℂ :=
  fun y => overlapPi TA W L θ F y - overlapBumps TA W L θ cL cR y

omit [NeZero P] in
theorem measurable_overlapBumps (TA : Finset TriTile) (W : ℤ × ℤ) (L : Finset ℤ) (θ : ℝ)
    (cL cR : ℤ → ℝ → ZMod P → ℂ) : Measurable (overlapBumps TA W L θ cL cR) := by
  have hA : Measurable (fun y : ℝ => ∑ p ∈ L.sigma (fun σ => leftEnds TA W σ),
      (ovPhase θ y * ((leftPhi p.1 p.2 y : ℝ) : ℂ)) • cL p.1 p.2) := by
    refine Finset.measurable_sum _ fun (p : Σ _ : ℤ, ℝ) _ => ?_
    exact ((continuous_ovPhase θ).measurable.mul
      (Complex.measurable_ofReal.comp (continuous_leftPhi p.1 p.2).measurable)).smul_const (cL p.1 p.2)
  have hB : Measurable (fun y : ℝ => ∑ p ∈ L.sigma (fun σ => rightEnds TA W σ),
      (ovPhase θ y * ((rightPhi p.1 p.2 y : ℝ) : ℂ)) • cR p.1 p.2) := by
    refine Finset.measurable_sum _ fun (p : Σ _ : ℤ, ℝ) _ => ?_
    exact ((continuous_ovPhase θ).measurable.mul
      (Complex.measurable_ofReal.comp (continuous_rightPhi p.1 p.2).measurable)).smul_const (cR p.1 p.2)
  exact hA.add hB

theorem measurable_overlapG (TA : Finset TriTile) (W : ℤ × ℤ) (L : Finset ℤ) (θ : ℝ) {F : ℝ → ZMod P → ℂ}
    (hF : Measurable F) (cL cR : ℤ → ℝ → ZMod P → ℂ) : Measurable (overlapG TA W L θ F cL cR) :=
  (measurable_overlapPi TA W L θ hF).sub (measurable_overlapBumps TA W L θ cL cR)

theorem yNorm_real_smul_le {s : ℝ} (hs : 0 < s) (a : ℝ) (v : ZMod P → ℂ) :
    yNorm s (((a : ℝ) : ℂ) • v) = |a| * yNorm s v := by
  have : (((a : ℝ) : ℂ) • v) = fun y => ((a : ℝ) : ℂ) * v y := by
    funext y; simp [smul_eq_mul]
  rw [this, yNorm_fun_const_mul hs]
  simp

theorem yNorm_csmul {s : ℝ} (hs : 0 < s) (c : ℂ) (v : ZMod P → ℂ) : yNorm s (c • v) = ‖c‖ * yNorm s v := by
  have : (c • v) = fun y => c * v y := by funext y; simp [smul_eq_mul]
  rw [this, yNorm_fun_const_mul hs]

/-- At every point at most one left bump is nonzero: the left-bump sum is bounded by `8 B`. -/
theorem yNorm_leftBumps_le {TA : Finset TriTile} {W : ℤ × ℤ} {L : Finset ℤ} {cL : ℤ → ℝ → ZMod P → ℂ} {s : ℝ}
    (hs : 1 ≤ s) {B : ℝ} (hB : 0 ≤ B) (hc : ∀ σ ∈ L, ∀ x ∈ leftEnds TA W σ, yNorm s (cL σ x) ≤ B) (θ y : ℝ) :
    yNorm s (∑ p ∈ L.sigma (fun σ => leftEnds TA W σ), (ovPhase θ y * ((leftPhi p.1 p.2 y : ℝ) : ℂ)) • cL p.1 p.2) ≤ 8 * B := by
  have hs0 : 0 < s := by linarith
  by_cases h : ∃ p ∈ L.sigma (fun σ => leftEnds TA W σ), y ∈ leftBump p.1 p.2
  · obtain ⟨p, hp, hyp⟩ := h
    rw [Finset.sum_eq_single_of_mem p hp]
    · rw [yNorm_csmul hs0, norm_mul, norm_ovPhase, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |leftPhi p.1 p.2 y| ≤ 8 := by
        rw [abs_of_nonneg (leftPhi_nonneg _ _ _)]; exact leftPhi_le _ _ _
      have h2 := hc p.1 (Finset.mem_sigma.1 hp).1 p.2 (Finset.mem_sigma.1 hp).2
      exact mul_le_mul h1 h2 (yNorm_nonneg' _ _) (by norm_num)
    · intro p' hp' hne
      have hd := leftBump_pairwiseDisjoint_eTil (Tr := TA) (W := W) L (by simpa using hp) (by simpa using hp')
        (Ne.symm hne)
      have : leftPhi p'.1 p'.2 y = 0 :=
        leftPhi_eq_zero fun hy' => (Set.disjoint_left.1 hd) hyp hy'
      simp [this]
  · push Not at h
    have : ∑ p ∈ L.sigma (fun σ => leftEnds TA W σ), (ovPhase θ y * ((leftPhi p.1 p.2 y : ℝ) : ℂ)) • cL p.1 p.2 = 0 :=
      Finset.sum_eq_zero fun p hp => by simp [leftPhi_eq_zero (h p hp)]
    rw [this, yNorm_zero_ov hs0]
    linarith

theorem yNorm_rightBumps_le {TA : Finset TriTile} {W : ℤ × ℤ} {L : Finset ℤ} {cR : ℤ → ℝ → ZMod P → ℂ} {s : ℝ}
    (hs : 1 ≤ s) {B : ℝ} (hB : 0 ≤ B) (hc : ∀ σ ∈ L, ∀ x ∈ rightEnds TA W σ, yNorm s (cR σ x) ≤ B) (θ y : ℝ) :
    yNorm s (∑ p ∈ L.sigma (fun σ => rightEnds TA W σ), (ovPhase θ y * ((rightPhi p.1 p.2 y : ℝ) : ℂ)) • cR p.1 p.2) ≤ 8 * B := by
  have hs0 : 0 < s := by linarith
  by_cases h : ∃ p ∈ L.sigma (fun σ => rightEnds TA W σ), y ∈ rightBump p.1 p.2
  · obtain ⟨p, hp, hyp⟩ := h
    rw [Finset.sum_eq_single_of_mem p hp]
    · rw [yNorm_csmul hs0, norm_mul, norm_ovPhase, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |rightPhi p.1 p.2 y| ≤ 8 := by
        rw [abs_of_nonneg (rightPhi_nonneg _ _ _)]; exact rightPhi_le _ _ _
      have h2 := hc p.1 (Finset.mem_sigma.1 hp).1 p.2 (Finset.mem_sigma.1 hp).2
      exact mul_le_mul h1 h2 (yNorm_nonneg' _ _) (by norm_num)
    · intro p' hp' hne
      have hd := rightBump_pairwiseDisjoint_eTil (Tr := TA) (W := W) L (by simpa using hp) (by simpa using hp')
        (Ne.symm hne)
      have : rightPhi p'.1 p'.2 y = 0 :=
        rightPhi_eq_zero fun hy' => (Set.disjoint_left.1 hd) hyp hy'
      simp [this]
  · push Not at h
    have : ∑ p ∈ L.sigma (fun σ => rightEnds TA W σ), (ovPhase θ y * ((rightPhi p.1 p.2 y : ℝ) : ℂ)) • cR p.1 p.2 = 0 :=
      Finset.sum_eq_zero fun p hp => by simp [rightPhi_eq_zero (h p hp)]
    rw [this, yNorm_zero_ov hs0]
    linarith

/-! ## Support and the `L^∞` bound -/

theorem overlapPi_eq_zero_of_not_mem {TA : Finset TriTile} {W : ℤ × ℤ} {L : Finset ℤ} {θ : ℝ} {F : ℝ → ZMod P → ℂ}
    {y : ℝ} (hy : y ∉ dilate 3 (dyadicInt W.1 W.2)) : overlapPi TA W L θ F y = 0 := by
  refine overlapPi_eq_zero fun σ _ hyσ => hy ?_
  exact dyadicInt_subset_dilate (by norm_num) W.1 W.2 (eTil_subset σ (overlapA_subset_eTil TA W L σ hyσ))

omit [NeZero P] in
theorem overlapBumps_eq_zero_of_not_mem {TA : Finset TriTile} {W : ℤ × ℤ} {L : Finset ℤ}
    {θ : ℝ} {cL cR : ℤ → ℝ → ZMod P → ℂ} {y : ℝ} (hy : y ∉ dilate 3 (dyadicInt W.1 W.2)) :
    overlapBumps TA W L θ cL cR y = 0 := by
  unfold overlapBumps
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro p hp
    have hx := (Finset.mem_sigma.1 hp).2
    have : rightPhi p.1 p.2 y = 0 :=
      rightPhi_eq_zero fun h => hy (rightBump_subset_dilate_three hx h)
    simp [this]
  · intro p hp
    have hx := (Finset.mem_sigma.1 hp).2
    have : leftPhi p.1 p.2 y = 0 :=
      leftPhi_eq_zero fun h => hy (leftBump_subset_dilate_three hx h)
    simp [this]

theorem overlapG_eq_zero_of_not_mem {TA : Finset TriTile} {W : ℤ × ℤ} {L : Finset ℤ} {θ : ℝ}
    {F : ℝ → ZMod P → ℂ} {cL cR : ℤ → ℝ → ZMod P → ℂ} {y : ℝ} (hy : y ∉ dilate 3 (dyadicInt W.1 W.2)) :
    overlapG TA W L θ F cL cR y = 0 := by
  unfold overlapG
  rw [overlapPi_eq_zero_of_not_mem hy, overlapBumps_eq_zero_of_not_mem hy, sub_zero]

theorem yNorm_sub_ov {s : ℝ} (hs : 1 ≤ s) (u v : ZMod P → ℂ) : yNorm s (u - v) ≤ yNorm s u + yNorm s v := by
  have h : u - v = u + (((-1 : ℝ) : ℂ) • v) := by
    funext y; simp [sub_eq_add_neg]
  rw [h]
  refine (CZ.yNorm_add_le hs _ _).trans ?_
  rw [yNorm_real_smul_le (by linarith)]
  simp

/-- **`L^∞` bound of `G` for real coefficient bounds**: `‖G(y)‖ ≤ C_oa engTop + 16 B'` when `‖c‖ ≤ B'`. -/
theorem overlapG_bound_real {𝔭 : Params} (h𝔭 : 𝔭.Admissible) (hJ2 : 2 ≤ 𝔭.J) {η' : ℝ → ℝ}
    (hη' : IsEtaCut 𝔭 η') {s q : ℝ} (hs : 1 ≤ s) (hq : 1 < q) {k : Fin 3} {F : ℝ → ZMod P → ℂ} (hF : Measurable F)
    (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) {TA Cs : Finset TriTile} (hsub : TA ⊆ Cs) {t : Top}
    (hov : ∀ R ∈ TA, IsOvSlot t k R.box) {L : Finset ℤ}
    (hlat : ∀ σ ∈ L, ∀ R ∈ TA, (𝔭.J : ℤ) ∣ R.box.scale - σ) {cL cR : ℤ → ℝ → ZMod P → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hcL : ∀ σ ∈ L, ∀ x ∈ leftEnds TA t.1 σ, yNorm s (cL σ x) ≤ B)
    (hcR : ∀ σ ∈ L, ∀ x ∈ rightEnds TA t.1 σ, yNorm s (cR σ x) ≤ B) (y : ℝ) :
    ENNReal.ofReal (yNorm s (overlapG TA t.1 L (t.2 * freqDir k) F cL cR y)) ≤
      ENNReal.ofReal (oaConst 𝔭 q) * engTop 𝔭 s k F Cs q + ENNReal.ofReal (16 * B) := by
  have h1 := overlapPi_bound h𝔭 hJ2 hη' hs hq hF hFb hsub hov hlat y
  have h2 : yNorm s (overlapBumps TA t.1 L (t.2 * freqDir k) cL cR y) ≤ 16 * B := by
    unfold overlapBumps
    refine (CZ.yNorm_add_le hs _ _).trans ?_
    linarith [yNorm_leftBumps_le (TA := TA) (W := t.1) (L := L) hs hB hcL (t.2 * freqDir k) y,
      yNorm_rightBumps_le (TA := TA) (W := t.1) (L := L) hs hB hcR (t.2 * freqDir k) y]
  calc ENNReal.ofReal (yNorm s (overlapG TA t.1 L (t.2 * freqDir k) F cL cR y))
      ≤ ENNReal.ofReal (yNorm s (overlapPi TA t.1 L (t.2 * freqDir k) F y) + 16 * B) := by
        refine ENNReal.ofReal_le_ofReal ((yNorm_sub_ov hs _ _).trans ?_)
        linarith
    _ ≤ ENNReal.ofReal (yNorm s (overlapPi TA t.1 L (t.2 * freqDir k) F y)) + ENNReal.ofReal (16 * B) :=
        ENNReal.ofReal_add_le
    _ ≤ _ := by gcongr

/-- **(O1) for the construction**: for ANY finite set `L` of lattice scales and any coefficient families bounded in `L^s(Y)` by
`B · engTop` (the coefficient bound O-b), `G = Π̃F - Σ cφ` is measurable, bounded by `C · engTop`, and vanishes off `3 I_t`.
(`C = max(C_oa, 0) + 16 B + 1`; the `+ 1` only makes the constant positive, so that the case `engTop = ∞` is trivial.) -/
theorem overlap_O1_of_coeff {𝔭 : Params} (h𝔭 : 𝔭.Admissible) (hJ2 : 2 ≤ 𝔭.J) {η' : ℝ → ℝ}
    (hη' : IsEtaCut 𝔭 η') {s q : ℝ} (hs : 1 ≤ s) (hq : 1 < q) {k : Fin 3} {F : ℝ → ZMod P → ℂ} (hF : Measurable F)
    (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) {TA Cs : Finset TriTile} (hsub : TA ⊆ Cs) {t : Top}
    (hov : ∀ R ∈ TA, IsOvSlot t k R.box) {L : Finset ℤ}
    (hlat : ∀ σ ∈ L, ∀ R ∈ TA, (𝔭.J : ℤ) ∣ R.box.scale - σ) {cL cR : ℤ → ℝ → ZMod P → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hcL : ∀ σ ∈ L, ∀ x ∈ leftEnds TA t.1 σ,
      ENNReal.ofReal (yNorm s (cL σ x)) ≤ ENNReal.ofReal B * engTop 𝔭 s k F Cs q)
    (hcR : ∀ σ ∈ L, ∀ x ∈ rightEnds TA t.1 σ,
      ENNReal.ofReal (yNorm s (cR σ x)) ≤ ENNReal.ofReal B * engTop 𝔭 s k F Cs q) :
    Measurable (overlapG TA t.1 L (t.2 * freqDir k) F cL cR) ∧
      (∀ y, ENNReal.ofReal (yNorm s (overlapG TA t.1 L (t.2 * freqDir k) F cL cR y)) ≤
        ENNReal.ofReal (max (oaConst 𝔭 q) 0 + 16 * B + 1) * engTop 𝔭 s k F Cs q) ∧
      ∀ y, y ∉ dilate 3 (dyadicInt t.1.1 t.1.2) → overlapG TA t.1 L (t.2 * freqDir k) F cL cR y = 0 := by
  refine ⟨measurable_overlapG _ _ _ _ hF _ _, fun y => ?_, fun y hy => overlapG_eq_zero_of_not_mem hy⟩
  have hpos : 0 < max (oaConst 𝔭 q) 0 + 16 * B + 1 := by
    have := le_max_right (oaConst 𝔭 q) 0
    linarith
  by_cases hE : engTop 𝔭 s k F Cs q = ⊤
  · rw [hE, ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
    exact le_top
  · set E := engTop 𝔭 s k F Cs q with hEdef
    have hE' : E = ENNReal.ofReal E.toReal := (ENNReal.ofReal_toReal hE).symm
    set e := E.toReal with hedef
    have he : 0 ≤ e := ENNReal.toReal_nonneg
    have hc : ∀ {a : ℝ}, ENNReal.ofReal a ≤ ENNReal.ofReal B * E → a ≤ B * e := by
      intro a h
      rw [hE', ← ENNReal.ofReal_mul hB] at h
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
    have hb := overlapG_bound_real h𝔭 hJ2 hη' hs hq hF hFb hsub hov hlat (B := B * e) (by positivity)
      (fun σ hσ x hx => hc (hcL σ hσ x hx)) (fun σ hσ x hx => hc (hcR σ hσ x hx)) y
    rw [← hEdef, hE'] at hb
    refine hb.trans ?_
    rw [hE']
    have hC' : max (oaConst 𝔭 q) 0 + 16 * B + 1 = max (oaConst 𝔭 q) 0 + (16 * B + 1) := by ring
    calc ENNReal.ofReal (oaConst 𝔭 q) * ENNReal.ofReal e + ENNReal.ofReal (16 * (B * e))
        ≤ ENNReal.ofReal (max (oaConst 𝔭 q) 0) * ENNReal.ofReal e + ENNReal.ofReal ((16 * B + 1) * e) :=
          add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl)
            (ENNReal.ofReal_le_ofReal (by nlinarith))
      _ = ENNReal.ofReal ((max (oaConst 𝔭 q) 0 + (16 * B + 1)) * e) := by
          rw [← ENNReal.ofReal_mul (le_max_right _ _), ← ENNReal.ofReal_add (mul_nonneg (le_max_right _ _) he)
            (mul_nonneg (by linarith) he)]
          ring_nf
      _ = ENNReal.ofReal (max (oaConst 𝔭 q) 0 + 16 * B + 1) * ENNReal.ofReal e := by
          rw [hC', ENNReal.ofReal_mul (by linarith)]

end Pi

end PrimeBHT.TimeFrequency.X2
