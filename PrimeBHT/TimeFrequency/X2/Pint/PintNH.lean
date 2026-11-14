module

public import PrimeBHT.TimeFrequency.X2.Pint.PintNHAux
public import PrimeBHT.TimeFrequency.X2.TopEnergy.StepG

/-!
# X2, node V11: `pint` at the non-Hilbert exponents — `pint_nonHilbert_O : PintStatementOFor NonHilbertExp`

For `1 < s < qX`, `s/(s-1) < qX`, `0 < α < 1`, uniformly in `P`, in the rank-one box set and in the
`IsStronglyDisjointO` family `𝒯` of lacunary trees (class margin `(𝔭.decN 10).Admissible`):
`∑_T |I_T| topNorm(F;T;qX)^{qX} ≤ C (‖F‖_{L^{qX}(L^s)}^{qX} + (B^{qX} ∑_T|I_T|)^{1-α} ‖F‖^{α qX})`.

Proof (plan `docs/audits/X2-V11-TB4-plan.md` §4d-4e): sum of suprema ≤ sup of selection sums (`finsetSum_iSup_le`);
for one selection of data per tree, the tree operators are the kernel operators `selKer` (`kernelOp_treeKer`); then
`Pint.theoremII_meas` with the BMO endpoint `treeKer_bmo` (at `s₀ = s / rF s qX`) and the Hilbert endpoint `pint_two_O`
in HLC's intersection form (Young with parameter `ε`), and the `ε`-optimisation `eps_opt`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

variable {P : ℕ} [NeZero P]

omit [NeZero P] in
theorem measurable_stepFun' {κ : Type*} [Fintype κ] {E : κ → Set ℝ} (hE : ∀ k, MeasurableSet (E k))
    (v : κ → ZMod P → ℂ) : Measurable (Pint.stepFun E v) :=
  measurable_pi_iff.2 fun _y => Finset.measurable_sum _ fun k _ =>
    (measurable_const.indicator (hE k)).mul measurable_const

theorem yNorm_stepFun_rpow' {κ : Type*} [Fintype κ] {E : κ → Set ℝ}
    (hd : Pairwise fun k k' => Disjoint (E k) (E k')) (v : κ → ZMod P → ℂ) {p q : ℝ} (hp : 0 < p) (hq : q ≠ 0)
    (w : ℝ) : yNorm p (Pint.stepFun E v w) ^ q = ∑ k, (E k).indicator (fun _ => yNorm p (v k) ^ q) w := by
  by_cases h : ∃ k, w ∈ E k
  · obtain ⟨k, hk⟩ := h
    rw [Pint.stepFun_eq_of_mem hd _ hk, Finset.sum_eq_single k]
    · rw [Set.indicator_of_mem hk]
    · intro j _ hj
      exact Set.indicator_of_notMem (fun h => Set.disjoint_left.1 (hd hj) h hk) _
    · simp
  · push Not at h
    rw [Pint.stepFun_eq_zero _ h, yNorm_zero_of_pos hp, Real.zero_rpow hq]
    exact (Finset.sum_eq_zero fun k _ => Set.indicator_of_notMem (h k) _).symm

theorem integrable_yNorm_stepFun_rpow' {κ : Type*} [Fintype κ] {E : κ → Set ℝ} (hE : Pint.IsStepData E)
    (v : κ → ZMod P → ℂ) {p q : ℝ} (hp : 0 < p) (hq : q ≠ 0) :
    Integrable fun w => yNorm p (Pint.stepFun E v w) ^ q := by
  simp_rw [yNorm_stepFun_rpow' hE.2.2 v hp hq]
  exact integrable_finset_sum _ fun k _ =>
    (integrable_indicator_iff (hE.1 k)).2 (integrableOn_const (hE.2.1 k).ne)

/-- **The Hilbert endpoint in HLC's intersection form** for one selection of data per tree (step functions). -/
theorem hilbert_selection {𝔭 : Params} (_h𝔭 : (𝔭.decN 10).Admissible) {α C2 : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hC2 : 0 ≤ C2)
    (hpint2 : ∀ (P : ℕ) [NeZero P] (Qs : Set Box), IsRankOne 𝔭.J Qs →
      ∀ (k : Fin 3) (𝒯 : List (Finset TriTile × Top)), IsStronglyDisjointO k 𝒯 →
        (∀ T ∈ 𝒯, ∀ R ∈ T.1, R.box ∈ Qs) → ∀ (F : ℝ → ZMod P → ℂ) (B : ℝ), Measurable F →
          (∀ x, yNorm 2 (F x) ≤ B) →
            (𝒯.map (fun T => ENNReal.ofReal ((2 : ℝ) ^ T.2.1.1) *
                topNorm 𝔭 2 k F T.1 T.2 2 ^ (2 : ℝ))).sum ≤
              ENNReal.ofReal C2 * (mixedPow 2 2 F +
                (ENNReal.ofReal (B ^ 2) * topSum 𝒯) ^ (1 - α) * mixedPow 2 2 F ^ α))
    {Qs : Set Box} (hQ : IsRankOne 𝔭.J Qs) {k : Fin 3} {𝒯 : List (Finset TriTile × Top)}
    (hSD : IsStronglyDisjointO k 𝒯) (hbox : ∀ T ∈ 𝒯, ∀ R ∈ T.1, R.box ∈ Qs) {Cφ Cκ : ℝ}
    (hTBi : ∀ i : Fin 𝒯.length, ∀ d : TD 𝔭 k 𝒯[i.1].1, ∀ R ∈ 𝒯[i.1].1, TileBound (𝔭.N : ℝ) 3 Cφ Cκ R.box.scale R.pos
      (d.1.1 R) (kernelDemod (𝒯[i.1].2.2 * freqDir k) (d.1.2 R)))
    (g : ∀ i : Fin 𝒯.length, Option (TD 𝔭 k 𝒯[i.1].1)) {ε : ℝ} (hε : 0 < ε)
    {κ : Type} [Fintype κ] {E : κ → Set ℝ} (hEd : Pint.IsStepData E) (v : κ → ZMod P → ℂ) (B₀ : ℝ)
    (hB₀ : ∀ w, yNorm 2 (Pint.stepFun E v w) ≤ B₀) :
    ∑ i, ∫⁻ x, ENNReal.ofReal (yNorm 2 (Pint.kernelOp (selKer 𝔭 k 𝒯[i.1] (g i)) (Pint.stepFun E v) x) ^ 2) ≤
      ENNReal.ofReal ((Real.sqrt (C2 * ε * (topSum 𝒯).toReal) * B₀ +
        Real.sqrt (C2 * (1 + ε ^ (-((1 - α) / α)))) *
          (∫ x, yNorm 2 (Pint.stepFun E v x) ^ 2) ^ ((1 : ℝ) / 2)) ^ 2) := by
  classical
  set G := Pint.stepFun E v with hGdef
  have hGm : Measurable G := measurable_stepFun' hEd.1 v
  have hB₀0 : 0 ≤ B₀ := (Pint.yNorm_nonneg _ _).trans (hB₀ 0)
  have hGb : ∀ z y, ‖G z y‖ ≤ (P : ℝ) ^ (2 : ℝ)⁻¹ * B₀ := fun z y =>
    (Pint.norm_apply_le_yNorm two_pos _ y).trans (mul_le_mul_of_nonneg_left (hB₀ z) (by positivity))
  have hGi := integrable_yNorm_stepFun_rpow' hEd v (p := 2) (q := 2) two_pos two_ne_zero
  set F2 := ∫ x, yNorm 2 (G x) ^ (2 : ℝ) with hF2
  have hF20 : 0 ≤ F2 := integral_nonneg fun x => Real.rpow_nonneg (Pint.yNorm_nonneg _ _) _
  have hmix : mixedPow 2 2 G = ENNReal.ofReal F2 :=
    (ofReal_integral_eq_lintegral_ofReal hGi (ae_of_all _ fun x => Real.rpow_nonneg (Pint.yNorm_nonneg _ _) _)).symm
  have hF2' : ∫ x, yNorm 2 (G x) ^ 2 = F2 := by
    rw [hF2]; congr 1; funext x; rw [Real.rpow_two]
  set Λ := (topSum 𝒯).toReal with hΛ
  have hΛ0 : 0 ≤ Λ := ENNReal.toReal_nonneg
  have hT : topSum 𝒯 = ENNReal.ofReal Λ := (ENNReal.ofReal_toReal (topSum_ne_top 𝒯)).symm
  -- from selections to `topNorm`
  have h1 : ∑ i, ∫⁻ x, ENNReal.ofReal (yNorm 2 (Pint.kernelOp (selKer 𝔭 k 𝒯[i.1] (g i)) G x) ^ 2) ≤
      (𝒯.map (fun T => ENNReal.ofReal ((2 : ℝ) ^ T.2.1.1) * topNorm 𝔭 2 k G T.1 T.2 2 ^ (2 : ℝ))).sum := by
    rw [← Fin.sum_univ_fun_getElem]
    refine Finset.sum_le_sum fun i _ => ?_
    have e := lintegral_selKer (hTBi i) two_pos two_pos hGm hGb (g i)
    simp only [Real.rpow_two] at e
    rw [e]
    exact selVal_le zero_le_two (g i)
  have h2 := hpint2 P Qs hQ k 𝒯 hSD hbox G B₀ hGm hB₀
  rw [hmix, hT, ← ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
    ENNReal.ofReal_rpow_of_nonneg hF20 hα0.le, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add hF20 (by positivity), ← ENNReal.ofReal_mul hC2] at h2
  refine h1.trans (h2.trans (ENNReal.ofReal_le_ofReal ?_))
  rw [hF2']
  have hy := young_split' (x := B₀ ^ 2 * Λ) (y := F2) (by positivity) hF20 hε hα0 hα1
  set eβ := ε ^ (-((1 - α) / α)) with heβ
  have heβ0 : 0 ≤ eβ := (Real.rpow_pos_of_pos hε _).le
  have hsq1 : Real.sqrt (C2 * ε * Λ) ^ 2 = C2 * ε * Λ := Real.sq_sqrt (by positivity)
  have hsq2 : Real.sqrt (C2 * (1 + eβ)) ^ 2 = C2 * (1 + eβ) := Real.sq_sqrt (by positivity)
  have hsq3 : (F2 ^ ((1 : ℝ) / 2)) ^ 2 = F2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hF20]; norm_num
  have hx0 : 0 ≤ Real.sqrt (C2 * ε * Λ) * B₀ := by positivity
  have hy0 : 0 ≤ Real.sqrt (C2 * (1 + eβ)) * F2 ^ ((1 : ℝ) / 2) := by positivity
  calc C2 * (F2 + (B₀ ^ 2 * Λ) ^ (1 - α) * F2 ^ α) ≤ C2 * (F2 + (ε * (B₀ ^ 2 * Λ) + eβ * F2)) := by gcongr
    _ = (Real.sqrt (C2 * ε * Λ) * B₀) ^ 2 + (Real.sqrt (C2 * (1 + eβ)) * F2 ^ ((1 : ℝ) / 2)) ^ 2 := by
        rw [mul_pow, mul_pow, hsq1, hsq2, hsq3]; ring
    _ ≤ _ := by nlinarith [mul_nonneg hx0 hy0]

theorem mixedPow_eq_ofReal'' {s qX : ℝ} {F : ℝ → ZMod P → ℂ} (hF : Measurable F)
    (hM : mixedPow qX s F ≠ ⊤) : mixedPow qX s F = ENNReal.ofReal (∫ x, yNorm s (F x) ^ qX) := by
  have hFint : Integrable (fun x => yNorm s (F x) ^ qX) :=
    ⟨(((measurable_yNorm_fun s).comp hF).pow_const qX).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => Real.rpow_nonneg (Pint.yNorm_nonneg _ _) _)).2
        (lt_top_iff_ne_top.2 hM)⟩
  exact (ofReal_integral_eq_lintegral_ofReal hFint
    (ae_of_all _ fun x => Real.rpow_nonneg (Pint.yNorm_nonneg _ _) _)).symm

/-- **V11: `pint` at the non-Hilbert exponents** (`IsStronglyDisjointO` families, class margin
`(𝔭.decN 10).Admissible`). -/
theorem pint_nonHilbert_O : PintStatementOFor NonHilbertExp := by
  intro 𝔭 h𝔭 s qX α hE hα0 hα1
  classical
  have h𝔭0 : 𝔭.Admissible := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h𝔭
    exact ⟨h1, le_trans h2 (Nat.sub_le _ _), h3, h4, h5, h6, h7, h8⟩
  have hq2 := Pint.two_lt_qX hE
  have hq0 : 0 < qX := by linarith
  have hs0 : 0 < s := by linarith [hE.1]
  have hs₀ : 1 < s / Pint.rF s qX := by
    rw [lt_div_iff₀ (Pint.rF_pos hE), one_mul]; exact Pint.rF_lt hE
  obtain ⟨C2, hC2, hpint2⟩ := pint_two_O 𝔭 h𝔭 hα0 hα1
  obtain ⟨Cb, hCb, hbmo⟩ := treeKer_bmo h𝔭0 hs₀
  obtain ⟨Cφ, Cκ, -, -, hTB⟩ := exists_treeBounds h𝔭0
  have hN : (0 : ℝ) ≤ 𝔭.N := Nat.cast_nonneg _
  set CII := Pint.iiConst qX Cb with hCIIdef
  have hCII : 0 ≤ CII := by
    have := Pint.fsConst_pos qX
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) qX
    have := Real.rpow_nonneg hCb (qX - 2)
    rw [hCIIdef, Pint.iiConst]; positivity
  refine ⟨4 * CII * C2 + 1, by positivity, ?_⟩
  intro P _ Qs hQ k 𝒯 hSD hbox F B hF hB
  have hB0 : 0 ≤ B := (Pint.yNorm_nonneg _ _).trans (hB 0)
  by_cases hMt : mixedPow qX s F = ⊤
  · rw [hMt, top_add, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']; exact le_top
  have hTmem : ∀ i : Fin 𝒯.length, 𝒯[i.1] ∈ 𝒯 := fun i => List.getElem_mem _
  have hTBi : ∀ i : Fin 𝒯.length, ∀ d : TD 𝔭 k 𝒯[i.1].1, ∀ R ∈ 𝒯[i.1].1, TileBound (𝔭.N : ℝ) 3 Cφ Cκ
      R.box.scale R.pos (d.1.1 R) (kernelDemod (𝒯[i.1].2.2 * freqDir k) (d.1.2 R)) := fun i d =>
    (hTB Qs hQ k 𝒯[i.1].1 𝒯[i.1].2 (hbox _ (hTmem i)) (hSD.1 _ (hTmem i)).1 d.1.1 d.1.2 d.2).1
  have hFb : ∀ z y, ‖F z y‖ ≤ (P : ℝ) ^ s⁻¹ * B := fun z y =>
    (Pint.norm_apply_le_yNorm hs0 _ y).trans (mul_le_mul_of_nonneg_left (hB z) (by positivity))
  -- the right side in real numbers
  set M := ∫ x, yNorm s (F x) ^ qX with hMdef
  have hM0 : 0 ≤ M := integral_nonneg fun x => Real.rpow_nonneg (Pint.yNorm_nonneg _ _) _
  have hmix : mixedPow qX s F = ENNReal.ofReal M := mixedPow_eq_ofReal'' hF hMt
  set Λ := (topSum 𝒯).toReal with hΛ
  have hΛ0 : 0 ≤ Λ := ENNReal.toReal_nonneg
  have hT : topSum 𝒯 = ENNReal.ofReal Λ := (ENNReal.ofReal_toReal (topSum_ne_top 𝒯)).symm
  have hRHS : ENNReal.ofReal (4 * CII * C2 + 1) * (mixedPow qX s F +
      (ENNReal.ofReal (B ^ qX) * topSum 𝒯) ^ (1 - α) * mixedPow qX s F ^ α) =
      ENNReal.ofReal ((4 * CII * C2 + 1) * (M + (B ^ qX * Λ) ^ (1 - α) * M ^ α)) := by
    rw [hmix, hT, ← ENNReal.ofReal_mul (Real.rpow_nonneg hB0 _),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith), ENNReal.ofReal_rpow_of_nonneg hM0 hα0.le,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hM0 (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
  rw [hRHS, ← Fin.sum_univ_fun_getElem]
  refine (Finset.sum_le_sum fun i _ => le_iSup_selVal hq0).trans ?_
  refine finsetSum_iSup_le _ _ fun g => ?_
  -- one selection of data per tree
  set K : Fin 𝒯.length → ℝ → ℝ → ℂ := fun i => selKer 𝔭 k 𝒯[i.1] (g i) with hK
  have hval : ∑ i, selVal 𝔭 s qX k 𝒯[i.1] F (g i) =
      ∑ i, ∫⁻ x, ENNReal.ofReal (yNorm s (Pint.kernelOp (K i) F x) ^ qX) :=
    Finset.sum_congr rfl fun i _ => (lintegral_selKer (hTBi i) hs0 hq0 hF hFb (g i)).symm
  rw [hval]
  choose Cr hCr0 hrow hcol using fun i => selKer_rowcol hN (hTBi i) (g i)
  set Cloc := ∑ i, Cr i with hCloc
  have hCloc0 : 0 ≤ Cloc := Finset.sum_nonneg fun i _ => hCr0 i
  have hCri : ∀ i, ENNReal.ofReal (Cr i) ≤ ENNReal.ofReal Cloc := fun i =>
    ENNReal.ofReal_le_ofReal (Finset.single_le_sum (f := Cr) (fun j _ => hCr0 j) (Finset.mem_univ i))
  have hKm : ∀ i, StronglyMeasurable (Function.uncurry (K i)) := fun i => stronglyMeasurable_selKer (hTBi i) (g i)
  have hBMO : ∀ (κ : Type) [Fintype κ] (E : κ → Set ℝ), Pint.IsStepData E → ∀ i (v' : κ → ZMod P → ℂ),
      (∀ w, yNorm (s / Pint.rF s qX) (Pint.stepFun E v' w) ≤ 1) → ∀ a b : ℝ, a < b →
      ∫⁻ x in Ico a b, ENNReal.ofReal (yNorm (s / Pint.rF s qX)
        (Pint.kernelOp (K i) (Pint.stepFun E v') x - Pint.avgOn a b (Pint.kernelOp (K i) (Pint.stepFun E v')))) ≤
          ENNReal.ofReal (Cb * (b - a)) := by
    intro κ _ E hEd i v' hv' a b hab
    simp only [hK]
    rcases hgi : g i with _ | d
    · have h0 : Pint.kernelOp (selKer 𝔭 k 𝒯[i.1] none) (Pint.stepFun E v') = 0 := by
        funext x y; simp [Pint.kernelOp, selKer]
      have h0' : Pint.avgOn a b (0 : ℝ → ZMod P → ℂ) = 0 := by funext y; simp [Pint.avgOn]
      simp only [h0, h0', sub_zero, Pi.zero_apply, yNorm_zero_of_pos (by linarith : (0 : ℝ) < s / Pint.rF s qX),
        ENNReal.ofReal_zero, lintegral_zero]
      exact zero_le
    · exact hbmo P Qs hQ k 𝒯[i.1].1 𝒯[i.1].2 (hbox _ (hTmem i)) (hSD.1 _ (hTmem i)).1 (hSD.1 _ (hTmem i)).2
        d.1.1 d.1.2 d.2 _ (measurable_stepFun' hEd.1 v') hv' a b hab
  -- the bound for every `ε > 0`
  set Xe := ∑ i, ∫⁻ x, ENNReal.ofReal (yNorm s (Pint.kernelOp (K i) F x) ^ qX) with hXe
  have hεbound : ∀ ε : ℝ, 0 < ε → Xe ≤ ENNReal.ofReal (2 * CII * C2 * (ε * (B ^ qX * Λ) +
      (1 + ε ^ (-((1 - α) / α))) * M)) := by
    intro ε hε
    set A := Real.sqrt (C2 * ε * Λ) with hA
    set B₂ := Real.sqrt (C2 * (1 + ε ^ (-((1 - α) / α)))) with hB₂
    have hII := Pint.theoremII_meas hE hCloc0 hCb hKm (fun i x => (hrow i x).trans (hCri i))
      (fun i w => (hcol i w).trans (hCri i)) hBMO (A := A) (B₂ := B₂)
      (fun κ _ E hEd v' B₀ hB₀ => hilbert_selection h𝔭 hα0 hα1 hC2 hpint2 hQ hSD hbox hTBi g hε hEd v' B₀ hB₀)
      hF hB hMt
    refine hII.trans ?_
    rw [← ENNReal.ofReal_mul hCII]
    refine ENNReal.ofReal_le_ofReal ?_
    have heβ0 : 0 ≤ ε ^ (-((1 - α) / α)) := (Real.rpow_pos_of_pos hε _).le
    have hA2 : A ^ 2 = C2 * ε * Λ := Real.sq_sqrt (by positivity)
    have hB2 : B₂ ^ 2 = C2 * (1 + ε ^ (-((1 - α) / α))) := Real.sq_sqrt (by positivity)
    have hBq : (B ^ (qX / 2)) ^ 2 = B ^ qX := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hB0]; norm_num
    have hMh : (M ^ ((1 : ℝ) / 2)) ^ 2 = M := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hM0]; norm_num
    have hsq : (A * B ^ (qX / 2) + B₂ * M ^ ((1 : ℝ) / 2)) ^ 2 ≤
        2 * ((A * B ^ (qX / 2)) ^ 2 + (B₂ * M ^ ((1 : ℝ) / 2)) ^ 2) := add_sq_le
    rw [mul_pow, mul_pow, hA2, hB2, hBq, hMh] at hsq
    calc CII * (A * B ^ (qX / 2) + B₂ * M ^ ((1 : ℝ) / 2)) ^ 2
        ≤ CII * (2 * (C2 * ε * Λ * B ^ qX + C2 * (1 + ε ^ (-((1 - α) / α))) * M)) :=
          mul_le_mul_of_nonneg_left hsq hCII
      _ = _ := by ring
  have hXfin : Xe ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hεbound 1 one_pos)
  have hX := eps_opt (X := Xe.toReal) (K := 2 * CII * C2) (L := B ^ qX * Λ) (M := M) (by positivity)
    (by positivity) hM0 hα0 hα1 fun ε hε => by
      have := hεbound ε hε
      rw [← ENNReal.ofReal_toReal hXfin, ENNReal.ofReal_le_ofReal_iff (by
        have := (Real.rpow_pos_of_pos hε (-((1 - α) / α))).le
        positivity)] at this
      linarith
  rw [← ENNReal.ofReal_toReal hXfin]
  refine ENNReal.ofReal_le_ofReal (hX.trans ?_)
  have h5 : 0 ≤ M + (B ^ qX * Λ) ^ (1 - α) * M ^ α := by positivity
  nlinarith

end PrimeBHT.TimeFrequency.X2
