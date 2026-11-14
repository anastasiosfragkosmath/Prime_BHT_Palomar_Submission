module

public import PrimeBHT.TimeFrequency.X2.TopEnergy.FamilyNH
public import PrimeBHT.TimeFrequency.X2.TopEnergy.StepG

/-!
# X2, TB-4: V12-top at slot 3 (the non-Hilbert exponents) — `energyLemmaTopG_nonHilbert`

The same two-round greedy selection as `energyLemmaTopG_two` (`exists_greedy`, maximal `ξ` first, the `±` split), with
candidates `valSq σ > e/4` at `L^{qX}(L^s)`; the count of each round is `family_count` (Theorem I + TB-4a), the scale
bound of the candidates is `family_count` for a single datum, and the size of `e` is bounded by B5-top
(`topOpNorm_le_tailMass`).  Consequently `EnergyLemmaTopGStatement` holds for all `IsEnergyExponent`
(`energyLemmaTopG_of_two energyLemmaTopG_nonHilbert`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

variable {P : ℕ} [NeZero P]

/-- Candidates of a round at `(s, qX)`. -/
def candSq (𝔭 : Params) (s qX σ : ℝ) (k : Fin 3) (F : ℝ → ZMod P → ℂ) (e : ℝ≥0∞) : ℤ × ℤ → ℝ → Prop :=
  fun W ξ' => e / 4 < valSq 𝔭 s qX σ k F W (σ * ξ')

theorem candSq_data {𝔭 : Params} {s qX σ : ℝ} (hq : 0 < qX) {k : Fin 3} {F : ℝ → ZMod P → ℂ}
    (hF : Measurable F) {e : ℝ≥0∞} (heT : e ≠ ⊤) {W : ℤ × ℤ} {ξ' : ℝ} (h : candSq 𝔭 s qX σ k F e W ξ') :
    ∃ ψ m : ℝ → ℂ, InPsi 𝔭 W.1 W.2 ψ ∧ InTopMultS 𝔭 σ W (σ * ξ') k m ∧
      ENNReal.ofReal ((2 : ℝ) ^ W.1 * (e.toReal / 4) ^ qX) ≤
        ∫⁻ x, ENNReal.ofReal (yNorm s (ψ x • tmult m F x) ^ qX) := by
  unfold candSq valSq at h
  obtain ⟨ψ, h1⟩ := lt_iSup_iff.1 h
  obtain ⟨m, h2⟩ := lt_iSup_iff.1 h1
  obtain ⟨hψ, h3⟩ := lt_iSup_iff.1 h2
  obtain ⟨hm, h4⟩ := lt_iSup_iff.1 h3
  refine ⟨ψ, m, hψ, hm, ?_⟩
  have hL : (0 : ℝ) < (2 : ℝ) ^ W.1 := zpow_pos (by norm_num) _
  have h5 := ENNReal.rpow_le_rpow h4.le hq.le
  rw [val_rpow_eq hq (measurable_yNorm_psi_tmult' s hψ hm.1 hF) (fun x => Pint.yNorm_nonneg _ _) hL] at h5
  have he4 : e / 4 = ENNReal.ofReal (e.toReal / 4) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_toReal heT]; simp
  rw [he4, ENNReal.ofReal_rpow_of_nonneg (by positivity) hq.le] at h5
  calc ENNReal.ofReal ((2 : ℝ) ^ W.1 * (e.toReal / 4) ^ qX)
      = ENNReal.ofReal ((2 : ℝ) ^ W.1) * ENNReal.ofReal ((e.toReal / 4) ^ qX) :=
        ENNReal.ofReal_mul hL.le
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ W.1) * (ENNReal.ofReal ((2 : ℝ) ^ W.1)⁻¹ *
          ∫⁻ x, ENNReal.ofReal (yNorm s (ψ x • tmult m F x) ^ qX)) := by gcongr
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hL.le, mul_inv_cancel₀ hL.ne', ENNReal.ofReal_one, one_mul]

theorem shellSep_singleton (σ : ℝ) (k : Fin 3) (V : TopSel) : ShellSep σ k {V} := by
  intro i _ j hj j' hj' hne
  rw [Finset.mem_singleton] at hj hj'
  exact absurd (hj.trans hj'.symm) hne

/-- **One round at `(s, qX)`** (side `σ`). -/
theorem round_selection_NH (𝔭 : Params) (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) (hjf : jFloor ≤ 𝔭.J)
    (hC1 : 1 ≤ 𝔭.C) {Qs : Set Box} (hQ : IsRankOne 𝔭.J Qs) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (k : Fin 3)
    {s qX q : ℝ} (hE : 1 < s ∧ s < qX ∧ s / (s - 1) < qX) (hq : qX < q)
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) (hB : ∀ x, yNorm s (F x) ≤ 1) (hM : mixedPow qX s F ≠ ⊤)
    (C₀ : Finset TriTile) (hbox : ∀ R ∈ C₀, R.box ∈ Qs)
    {e : ℝ≥0∞} (he0 : e ≠ 0) (heT : e ≠ ⊤) {dmax : ℝ} (hdm : (e.toReal / 4) ^ qX ≤ dmax) :
    ∃ ts : List TopSel,
      (∀ W ξ', candSq 𝔭 s qX σ k F e W ξ' → ¬ IsTopDatumH (Hσ σ) fatRad 𝔭.J (resH (Hσ σ) C₀ ts) W ξ') ∧
      (ts.map fun V => ENNReal.ofReal ((2 : ℝ) ^ V.W.1)).sum ≤
        ENNReal.ofReal (topFamC 𝔭 qX q dmax * (∫ x, yNorm s (F x) ^ qX) / ((e.toReal / 4) ^ qX) ^ (q / qX)) := by
  have hq0 : 0 < qX := by linarith [Pint.two_lt_qX hE]
  have he_r : 0 < e.toReal := ENNReal.toReal_pos he0 heT
  set d := (e.toReal / 4) ^ qX with hd
  have hd0 : 0 < d := Real.rpow_pos_of_pos (by positivity) _
  have hdq : 0 < d ^ (q / qX) := Real.rpow_pos_of_pos hd0 _
  set L₀ := topFamC 𝔭 qX q dmax * (∫ x, yNorm s (F x) ^ qX) / d ^ (q / qX) with hL₀
  have hρ : (0 : ℝ) ≤ fatRad := by unfold fatRad; norm_num
  have hL : ∀ W ξ', candSq 𝔭 s qX σ k F e W ξ' → (2 : ℝ) ^ W.1 ≤ L₀ := by
    intro W ξ' h
    obtain ⟨ψ, m, hψ, hm, hgt⟩ := candSq_data hq0 hF heT h
    have hc := family_count 𝔭 hN hD hC1 hE hq hσ k (𝒮 := {⟨W, ξ', 0⟩}) (ψ := fun _ => ψ) (m := fun _ => m)
      (fun V hV => by rw [Finset.mem_singleton.1 hV]; exact hψ)
      (fun V hV => by rw [Finset.mem_singleton.1 hV]; exact hm) (shellSep_singleton σ k _) hF hB hM hd0 hdm
      (fun V hV => by rw [Finset.mem_singleton.1 hV]; exact hgt)
    rw [Finset.sum_singleton] at hc
    rw [hL₀, le_div_iff₀ hdq]
    exact hc
  obtain ⟨M, hM0, hMb⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ R ∈ C₀, ∀ x ∈ Hσ σ R.box, |x| ≤ M := by
    have hb : Bornology.IsBounded (⋃ R ∈ C₀, Box.hull R.box) :=
      (Bornology.isBounded_biUnion_finset C₀).2 fun R _ => by unfold Box.hull; exact Metric.isBounded_Icc _ _
    obtain ⟨M', hM'⟩ := isBounded_iff_forall_norm_le.1 hb
    refine ⟨max M' 0, le_max_right _ _, fun R hR x hx => ?_⟩
    have h1 : σ * x ∈ Box.hull R.box := hx
    have h2 := hM' (σ * x) (Set.mem_biUnion hR h1)
    have h3 : |σ * x| = |x| := by rcases hσ with rfl | rfl <;> simp
    rw [Real.norm_eq_abs, h3] at h2
    exact h2.trans (le_max_left _ _)
  have hfin : {p : (ℤ × ℤ) × ℝ | candSq 𝔭 s qX σ k F e p.1 p.2 ∧
      IsTopDatumH (Hσ σ) fatRad 𝔭.J C₀ p.1 p.2}.Finite :=
    (finite_topData hρ 𝔭.J C₀ hM0 hMb L₀).subset fun p hp => ⟨hp.2, hL p.1 p.2 hp.1⟩
  obtain ⟨ts, hsel, hres⟩ := exists_greedy (Hσ σ) hρ 𝔭.J (candSq 𝔭 s qX σ k F e) C₀.card C₀ le_rfl hfin
  refine ⟨ts, hres, ?_⟩
  have hmono : ∀ C C' W ξ ζ, C ⊆ C' → AdmH (Hσ σ) fatRad 𝔭.J C W ξ ζ → AdmH (Hσ σ) fatRad 𝔭.J C' W ξ ζ :=
    fun C C' W ξ ζ h hd => hd.mono h
  have hadm := hsel.adm_cand hmono
  have hnodup := hsel.nodup hρ
  have hdata : ∀ V ∈ ts, ∃ ψ m : ℝ → ℂ, InPsi 𝔭 V.W.1 V.W.2 ψ ∧ InTopMultS 𝔭 σ V.W (σ * V.ξ) k m ∧
      ENNReal.ofReal ((2 : ℝ) ^ V.W.1 * d) ≤ ∫⁻ x, ENNReal.ofReal (yNorm s (ψ x • tmult m F x) ^ qX) :=
    fun V hV => candSq_data hq0 hF heT (hadm V hV).2
  choose! ψ m hψ hm hgt using hdata
  set 𝒮 : Finset TopSel := ts.toFinset with h𝒮
  have hmem : ∀ V ∈ 𝒮, V ∈ ts := fun V hV => List.mem_toFinset.1 hV
  have hsep : ShellSep σ k 𝒮 := by
    intro i hi j hj j' hj' hne ⟨x, hx1, hx2⟩ ⟨x', hx1', hx2'⟩ hlj hlj'
    rw [Ico_dyCentre, Ico_dyCentre]
    have h0 : j.W.1 ≤ i.W.1 := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 hlj
    have h0' : j'.W.1 ≤ i.W.1 := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 hlj'
    exact top_separation_pair_H (H := Hσ σ) (ρ := fatRad) (by unfold fatRad; norm_num) hjf hQ hbox hsel
      (one_le_freqDir k) i (hmem j hj) (hmem j' hj') hne h0 h0'
      ⟨σ * x, (mem_Icc_shell_iff hσ k i.W i.ξ x).1 hx1, (mem_Icc_shell_iff hσ k j.W j.ξ x).1 hx2⟩
      ⟨σ * x', (mem_Icc_shell_iff hσ k i.W i.ξ x').1 hx1', (mem_Icc_shell_iff hσ k j'.W j'.ξ x').1 hx2'⟩
  have hc := family_count 𝔭 hN hD hC1 hE hq hσ k (𝒮 := 𝒮) (ψ := ψ) (m := m)
    (fun V hV => hψ V (hmem V hV)) (fun V hV => hm V (hmem V hV)) hsep hF hB hM hd0 hdm
    (fun V hV => hgt V (hmem V hV))
  have hsum : ∑ V ∈ 𝒮, (2 : ℝ) ^ V.W.1 ≤ L₀ := by rw [hL₀, le_div_iff₀ hdq]; exact hc
  rw [← List.sum_toFinset (fun V : TopSel => ENNReal.ofReal ((2 : ℝ) ^ V.W.1)) hnodup,
    ← ENNReal.ofReal_sum_of_nonneg (fun V _ => (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le)]
  exact ENNReal.ofReal_le_ofReal hsum

/-- The size bound of the slot-3 top energy (B5-top with `M = 2` and `tailMass ≤ tailConst`). -/
def topEmax (𝔭 : Params) (qX : ℝ) : ℝ :=
  𝔭.C * (2 ^ (⌈(2 : ℝ)⌉₊ + 1) * (2 * topRad) * 𝔭.C) * (2 / ((𝔭.N - 2) * qX - 1)) ^ (1 / qX) *
    V16.tailConst 2

theorem engTop_le_topEmax {𝔭 : Params} (h𝔭 : 𝔭.Admissible) {s qX : ℝ} (hs : 1 < s) (hq : 1 ≤ qX)
    (k : Fin 3) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) (hB : ∀ x, yNorm s (F x) ≤ 1)
    (Cs : Finset TriTile) : engTop 𝔭 s k F Cs qX ≤ ENNReal.ofReal (topEmax 𝔭 qX) := by
  have hN : (2 : ℝ) + 2 ≤ 𝔭.N := by
    have h1 : classFloor ≤ 𝔭.N := h𝔭.2.1
    have : (400 : ℝ) ≤ 𝔭.N := by exact_mod_cast h1
    linarith
  have hD : (2 : ℝ) ≤ 𝔭.D := by
    have h1 : classFloor ≤ 𝔭.D := h𝔭.2.2.1
    have : (400 : ℝ) ≤ 𝔭.D := by exact_mod_cast h1
    linarith
  refine iSup₂_le fun W ξ => iSup_le fun _ => ?_
  refine (topOpNorm_le_tailMass h𝔭 hs hq (by norm_num : (1 : ℝ) < 2) hN hD k hF hB W ξ).trans ?_
  have ht := V16.tailMass_le_tailConst (by norm_num : (1 : ℝ) < 2) (f := fun y => yNorm s (F y))
    (I := dyadicInt W.1 W.2) (by rw [toReal_volume_dyadicInt]; exact zpow_pos (by norm_num) _)
    (fun x => by rw [Real.norm_of_nonneg (Pint.yNorm_nonneg _ _)]; exact hB x)
  rw [topEmax, ENNReal.ofReal_mul' (V16.tailConst_pos (by norm_num : (1 : ℝ) < 2)).le]
  gcongr

theorem mixedPow_eq_ofReal' {s qX : ℝ} {F : ℝ → ZMod P → ℂ} (hF : Measurable F)
    (hM : mixedPow qX s F ≠ ⊤) : mixedPow qX s F = ENNReal.ofReal (∫ x, yNorm s (F x) ^ qX) := by
  have hFint : Integrable (fun x => yNorm s (F x) ^ qX) :=
    ⟨(((measurable_yNorm_fun s).comp hF).pow_const qX).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => Real.rpow_nonneg (Pint.yNorm_nonneg _ _) _)).2
        (lt_top_iff_ne_top.2 hM)⟩
  exact (ofReal_integral_eq_lintegral_ofReal hFint
    (ae_of_all _ fun x => Real.rpow_nonneg (Pint.yNorm_nonneg _ _) _)).symm

/-- **TB-4: V12-top at slot 3, global part** (halving and the global count at the non-Hilbert exponents). -/
theorem energyLemmaTopG_nonHilbert : EnergyLemmaTopGStatementFor NonHilbertExp := by
  intro 𝔭 h𝔭 s qX q hE hq
  have hE' : 1 < s ∧ s < qX ∧ s / (s - 1) < qX := hE
  obtain ⟨hJ, hNf, hDf, hδ0, hδ1, hβ1, hβ2, hC1⟩ := h𝔭
  have hcf : classFloor = 400 := rfl
  have hll : locLoss = 100 := rfl
  simp only [Params.loc_N] at hNf
  simp only [Params.loc_D] at hDf
  have hN : 12 ≤ 𝔭.N := by omega
  have hD : 12 ≤ 𝔭.D := by omega
  have hjf : jFloor ≤ 𝔭.J := by simpa using hJ
  have hC1' : 1 ≤ 𝔭.C := by simpa using hC1
  have hadm : 𝔭.Admissible := ⟨hjf, by omega, by omega, by simpa using hδ0, by simpa using hδ1,
    by simpa using hβ1, by simpa using hβ2, hC1'⟩
  have hq2 := Pint.two_lt_qX hE'
  have hq0 : 0 < qX := by linarith
  have hqq : 0 < q := by linarith
  set emax := topEmax 𝔭 qX with hemax
  set dmax := (max emax 0 / 4) ^ qX with hdmax
  have hdmax0 : 0 ≤ dmax := Real.rpow_nonneg (by positivity) _
  have hK0 : 0 ≤ topFamK 𝔭 qX q := by
    unfold topFamK
    have := topLevelC_nonneg (topC₁ 𝔭) ((div_lt_one hqq).2 hq)
    have : 0 ≤ topCinf 𝔭 ^ (qX - 2) := Real.rpow_nonneg (topCinf_nonneg (by linarith)) _
    positivity
  have hfC0 : 0 ≤ topFamC 𝔭 qX q dmax := by
    unfold topFamC
    have := Real.rpow_nonneg hdmax0 (q / qX - 1)
    have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * topFamK 𝔭 qX q) (q / qX - 1)
    positivity
  refine ⟨2 * 4 ^ q * topFamC 𝔭 qX q dmax + 1, by positivity, ?_⟩
  intro P _ Qs hQ Cs₀ Cs hbox hTC hres k F hF hB
  have hbox' : ∀ R ∈ Cs, R.box ∈ Qs := fun R hR => hbox R (by
    obtain ⟨ts, rfl⟩ := hres
    exact removeTrees_subset _ _ hR)
  set e := engTop 𝔭 s k F Cs qX with he
  have heB : e ≤ ENNReal.ofReal emax := engTop_le_topEmax hadm hE'.1 (by linarith) k hF hB Cs
  have heT : e ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top heB
  by_cases he0 : e = 0
  · refine ⟨[], ?_, ?_⟩
    · show engTop 𝔭 s k F Cs qX ≤ engTop 𝔭 s k F Cs qX / 2
      have h0 : engTop 𝔭 s k F Cs qX = 0 := he0
      rw [h0]; simp
    · show topSum [] * _ ≤ _
      rw [topSum_nil, zero_mul]; exact zero_le
  by_cases hmp : mixedPow qX s F = ⊤
  · obtain ⟨ts, hts⟩ := removeTrees_all Cs
    refine ⟨ts, ?_, ?_⟩
    · rw [hts, engTop_empty]; exact zero_le
    · rw [hmp, ENNReal.mul_top]
      · exact le_top
      · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have he_r : 0 < e.toReal := ENNReal.toReal_pos he0 heT
  have he_le : e.toReal ≤ max emax 0 :=
    ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) (heB.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hdm : (e.toReal / 4) ^ qX ≤ dmax :=
    Real.rpow_le_rpow (by positivity) (by linarith) hq0.le
  have h1 : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1 := Or.inl rfl
  have h2 : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1 := Or.inr rfl
  obtain ⟨ts₁, hres₁, hcnt₁⟩ := round_selection_NH 𝔭 hN hD hjf hC1' hQ h1 k hE' hq hF hB hmp Cs hbox' he0 heT hdm
  set Cs₁ := resH (Hσ 1) Cs ts₁ with hCs₁
  have hCs₁sub : Cs₁ ⊆ Cs := resH_subset _ _ _
  obtain ⟨ts₂, hres₂, hcnt₂⟩ := round_selection_NH 𝔭 hN hD hjf hC1' hQ h2 k hE' hq hF hB hmp Cs₁
    (fun R hR => hbox' R (hCs₁sub hR)) he0 heT hdm
  set Cs₂ := resH (Hσ (-1)) Cs₁ ts₂ with hCs₂
  have hCs₂sub : Cs₂ ⊆ Cs₁ := resH_subset _ _ _
  refine ⟨ts₁.map (toTop 1) ++ ts₂.map (toTop (-1)), ?_, ?_⟩
  · have hrem : removeTrees Cs (ts₁.map (toTop 1) ++ ts₂.map (toTop (-1))) = Cs₂ := by
      rw [← removeTrees_removeTrees, removeTrees_map_toTop h1, removeTrees_map_toTop h2]
    rw [hrem]
    refine iSup₂_le fun W ξ => iSup_le fun hd => ?_
    refine (topOpNorm_le_valSq_add 𝔭 hE'.1.le (by linarith) k hF hB W ξ).trans ?_
    have hv1 : valSq 𝔭 s qX 1 k F W ξ ≤ e / 4 := by
      by_contra hcon
      rw [not_le] at hcon
      have hc : candSq 𝔭 s qX 1 k F e W ξ := by unfold candSq; simpa using hcon
      have hdat : IsTopDatumH (Hσ 1) fatRad 𝔭.J Cs₁ W ξ := by
        rw [isTopDatumH_Hσ h1]
        have hd' : IsTopDatumH Box.hull fatRad 𝔭.J Cs₁ W ξ := IsTopDatumH.mono hCs₂sub hd
        simpa using hd'
      exact hres₁ W ξ hc hdat
    have hv2 : valSq 𝔭 s qX (-1) k F W ξ ≤ e / 4 := by
      by_contra hcon
      rw [not_le] at hcon
      have hc : candSq 𝔭 s qX (-1) k F e W (-ξ) := by unfold candSq; simpa using hcon
      have hdat : IsTopDatumH (Hσ (-1)) fatRad 𝔭.J Cs₂ W (-ξ) := by
        rw [isTopDatumH_Hσ h2]
        have hd' : IsTopDatumH Box.hull fatRad 𝔭.J Cs₂ W ξ := hd
        simpa using hd'
      exact hres₂ W (-ξ) hc hdat
    exact (add_le_add hv1 hv2).trans (le_of_eq (ennreal_div_four_add e))
  · set M := ∫ x, yNorm s (F x) ^ qX with hM
    have hM0 : 0 ≤ M := integral_nonneg fun x => Real.rpow_nonneg (Pint.yNorm_nonneg _ _) _
    set R := topFamC 𝔭 qX q dmax * M / ((e.toReal / 4) ^ qX) ^ (q / qX) with hR
    have hR0 : 0 ≤ R := by positivity
    have hsum : topSum (removedTrees Cs (ts₁.map (toTop 1) ++ ts₂.map (toTop (-1)))) ≤
        ENNReal.ofReal (2 * R) := by
      rw [removedTrees_append, topSum_append, removeTrees_map_toTop h1, removedTrees_map_toTop h1,
        removedTrees_map_toTop h2]
      refine (add_le_add hcnt₁ hcnt₂).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_add hR0 hR0]
      congr 1; ring
    have heq : e ^ q = ENNReal.ofReal (e.toReal ^ q) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg he_r.le hqq.le, ENNReal.ofReal_toReal heT]
    have hd' : ((e.toReal / 4) ^ qX) ^ (q / qX) = e.toReal ^ q / 4 ^ q := by
      rw [← Real.rpow_mul (by positivity), show qX * (q / qX) = q by field_simp,
        Real.div_rpow he_r.le (by norm_num)]
    calc topSum (removedTrees Cs (ts₁.map (toTop 1) ++ ts₂.map (toTop (-1)))) * engTop 𝔭 s k F Cs qX ^ q
        ≤ ENNReal.ofReal (2 * R) * e ^ q := mul_le_mul' hsum le_rfl
      _ = ENNReal.ofReal (2 * R * e.toReal ^ q) := by
          rw [heq, ← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (2 * 4 ^ q * topFamC 𝔭 qX q dmax * M) := by
          congr 1
          rw [hR, hd']
          have : 0 < e.toReal ^ q := Real.rpow_pos_of_pos he_r _
          have : 0 < (4 : ℝ) ^ q := Real.rpow_pos_of_pos (by norm_num) _
          field_simp
      _ ≤ ENNReal.ofReal ((2 * 4 ^ q * topFamC 𝔭 qX q dmax + 1) * M) :=
          ENNReal.ofReal_le_ofReal (by nlinarith)
      _ = ENNReal.ofReal (2 * 4 ^ q * topFamC 𝔭 qX q dmax + 1) * mixedPow qX s F := by
          rw [mixedPow_eq_ofReal' hF hmp, ← ENNReal.ofReal_mul (by positivity)]

end PrimeBHT.TimeFrequency.X2
