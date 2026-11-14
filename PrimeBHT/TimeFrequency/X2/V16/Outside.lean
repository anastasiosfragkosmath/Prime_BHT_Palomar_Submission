module

public import PrimeBHT.TimeFrequency.X2.V16.Assemble

/-!
# X2, node V16: B10 (the outside part)

`outside_le_of_energy`: for a window-full `Ps`, model data in `𝔭`, `β` in the corner region and hull data `(E, τ, h)`,
the form over `outsidePart Ps Ω`, `Ω = exceptionalOmega 48 E τ`, is at most `C · CT · ∏ |E_i|^{β_i}`.
GENERIC in an energy family `e` and an interval family `ints` (see `V16/Hyps.lean`): conditional on the abstract B5 (`EnergyTailBound`), V12
(`EnergyStepG`, the global count), V15 (`EnergyTree`) and `EnergyMono e`.

Proof (route check B10): `form_le_of_energy` (B7) on `Cs := outsidePart Ps Ω` (TC by `IsWindowFull.hasTC`,
`HasTC.outsidePart`; admissible collections are the residuals of `Cs`); `Λb_v` from B5 and B2(a)
(`tailMass_indicator_le_excMass_of_not_subset`, `v ≠ τ`) resp. `tailMass_le_tailConst` (`v = τ`); counts
`Ar_v = Ca |E_v|` from the global count of V12; then `tsum_min_le_region` at `θ = 0` (B9 + B8).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.V16

/-- A dyadic interval is an interval of positive length. -/
theorem dyadicInt_ordConnected (W : ℤ × ℤ) : (dyadicInt W.1 W.2).OrdConnected := by
  unfold dyadicInt; exact Set.ordConnected_Ico

theorem dyadicInt_toReal_volume_pos (W : ℤ × ℤ) : 0 < (volume (dyadicInt W.1 W.2)).toReal := by
  rw [toReal_volume_dyadicInt]; positivity

/-- From B5 to a bound by a pointwise bound on the tail masses. -/
theorem le_ofReal_of_tailMass_le {x : ℝ≥0∞} {M C bound : ℝ} (hC : 0 ≤ C) {f : ℝ → ℝ}
    {S : Set (ℤ × ℤ)}
    (hB : x ≤ ENNReal.ofReal C * ⨆ W ∈ S, ENNReal.ofReal (tailMass M f (dyadicInt W.1 W.2)))
    (hbound : ∀ W ∈ S, tailMass M f (dyadicInt W.1 W.2) ≤ bound) : x ≤ ENNReal.ofReal (C * bound) := by
  refine hB.trans ?_
  rw [ENNReal.ofReal_mul hC]
  exact mul_le_mul_right (iSup₂_le fun W hW => ENNReal.ofReal_le_ofReal (hbound W hW)) _

/-- The mass of a function dominated by `1_S` is at most that of `1_S`. -/
theorem tailMass_slot_le {P : ℕ} [NeZero P] {M : ℝ} (hM : 1 < M) {s : ℝ} {S : Set ℝ}
    (hS : MeasurableSet S) {F : ℝ → ZMod P → ℂ}
    (hF : ∀ x, yNorm s (F x) ≤ S.indicator (fun _ => (1 : ℝ)) x) {I : Set ℝ}
    (hL : 0 < (volume I).toReal) :
    tailMass M (fun y => yNorm s (F y)) I ≤ tailMass M (S.indicator (1 : ℝ → ℝ)) I :=
  tailMass_le_tailMass_indicator hM hS hL fun x => by
    rw [Real.norm_of_nonneg (yNorm_nonneg' _ _)]
    exact hF x

theorem tailMass_slot_le_tailConst {P : ℕ} [NeZero P] {M : ℝ} (hM : 1 < M) {s : ℝ}
    {F : ℝ → ZMod P → ℂ} (hF : ∀ x, yNorm s (F x) ≤ 1) {I : Set ℝ} (hL : 0 < (volume I).toReal) :
    tailMass M (fun y => yNorm s (F y)) I ≤ tailConst M :=
  tailMass_le_tailConst hM hL fun x => by
    rw [Real.norm_of_nonneg (yNorm_nonneg' _ _)]
    exact hF x

/-- **`EnergyStep` without its localized conjunct (REV4)**: one halving step by removing maximal trees, with the GLOBAL
count only.  B10 uses only this part.  The localized count (B6') is FALSE for the top energy `engTop` (a top operator is
localized at its own interval `W ⊇ I_R`, not at the tiles, so it sees far-away mass: `docs/audits/X2-V12-top` report), so
the outside family `eO` needs exactly `EnergyStepG`; the localized count is needed only for the tile family of B11. -/
def EnergyStepG (e : EnergyFamily) (u : ℝ) (𝔭 : Params) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (Qs : Set Box), IsRankOne 𝔭.J Qs →
    ∀ (Cs₀ Cs : Finset TriTile), (∀ R ∈ Cs₀, R.box ∈ Qs) → HasTC Cs₀ → IsResidual Cs₀ Cs →
    ∀ (h : Fin 3 → ℝ → ZMod P → ℂ), (∀ i, Measurable (h i)) → (∀ v x, yNorm (slotExp u v) (h v x) ≤ 1) →
    ∀ v : Fin 3, ∃ ts : List Top,
      e P h v (removeTrees Cs ts) ≤ e P h v Cs / 2 ∧
      topSum (removedTrees Cs ts) * e P h v Cs ^ V16.qPlus (Rof u) v ≤
        ENNReal.ofReal C * mixedPow (qX (Rof u) v) (slotExp u v) (h v)

/-- **B10 (outside)**, generic in the energy family `e`: conditional on the abstract B5 (`EnergyTailBound`), V12
(`EnergyStepG`: halving and GLOBAL count), V15 (`EnergyTree`) and monotonicity of `e`.  `M ≥ 2` is the tail order of B5. -/
theorem outside_le_of_energy {u : ℝ} (hu : 1 < u) (𝔭 : Params) {e : EnergyFamily} {ints : IntFamily}
    {M : ℝ} (hM : 2 ≤ M) (hints : IntsContain ints)
    (hmono : EnergyMono e) (htail : EnergyTailBound e ints u 𝔭 M) (hstep : EnergyStepG e u 𝔭)
    (htree : EnergyTree e u 𝔭) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (T : Form P) (CT : ℝ), FormBound u T CT →
      ∀ (Qs : Set Box), IsRankOne 𝔭.J Qs → ∀ (Ps : Finset TriTile), IsWindowFull Qs Ps →
      ∀ (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ), IsModelData 𝔭 Ps χ m →
      ∀ (β : Fin 3 → ℝ), Interp.InCornerNbhd (Rof u) β → ∀ (E : Fin 3 → Set ℝ) (τ : Fin 3)
        (h : Fin 3 → ℝ → ZMod P → ℂ), IsHullData u E τ h →
          ‖modelForm T (outsidePart Ps (exceptionalOmega 48 E τ)) χ m (h 0) (h 1) (h 2)‖ ≤
            C * CT * ∏ i, (volume (E i)).toReal ^ β i := by
  have hR4 : 4 ≤ Rof u := four_le_Rof hu
  obtain ⟨C5, hC5nn, hC5⟩ := htail
  obtain ⟨CE, hCEnn, hCE⟩ := hstep
  obtain ⟨Cf, hCf0, hCf⟩ := form_le_of_energy hu hmono htree
  set Ca : ℝ := CE + 1 with hCa
  have hCa1 : 1 ≤ Ca := by linarith
  set cm : Fin 3 → ℝ := fun _ => max (max 1 (C5 * 45 * 48)) (C5 * tailConst M) with hcm
  have hcm1 : ∀ v, 1 ≤ cm v := fun v => (le_max_left _ _).trans (le_max_left _ _)
  have hcm0 : ∀ v, 0 ≤ cm v := fun v => by linarith [hcm1 v]
  refine ⟨Cf * (∏ v, cm v) * (countConst (Rof u) * Ca), ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg hCf0 (Finset.prod_nonneg fun v _ => hcm0 v))
      (mul_nonneg (countConst_nonneg hR4) (by linarith))
  intro P _ T CT hT Qs hQ Ps hPs χ m hmd β hβ E τ h hH
  obtain ⟨hβsum, hβ0, hβ1⟩ := hβ
  have hβsum' : ∑ v, β v = 1 := by rw [Fin.sum_univ_three]; exact hβsum
  have hCT : 0 ≤ CT := not_lt.1 fun hneg => not_bound_of_neg T (by linarith) hneg hT
  have hEm : ∀ i, MeasurableSet (E i) := hH.1
  have hEpos : ∀ i, 0 < volume (E i) := hH.2.1
  have hEfin : ∀ i, volume (E i) < ⊤ := hH.2.2.1
  have hEmax : ∀ i, volume (E i) ≤ volume (E τ) := hH.2.2.2.1
  have hhm : ∀ i, Measurable (h i) := hH.2.2.2.2.1
  have hbdd := hH.yNorm_le_one
  -- the collection
  set Ω := exceptionalOmega 48 E τ with hΩ
  set Cs := outsidePart Ps Ω with hCs
  have hboxPs : ∀ R' ∈ Ps, R'.box ∈ Qs := by
    obtain ⟨Q, W, hQ0, hP⟩ := hPs
    intro R' hR'
    exact hQ0 ((hP R').1 hR').1
  have hboxCs : ∀ R' ∈ Cs, R'.box ∈ Qs := fun R' hR' => hboxPs R' (mem_outsidePart.1 hR').1
  have hTCCs : HasTC Cs := hPs.hasTC.outsidePart Ω
  have hmdCs : IsModelData 𝔭 Cs χ m := hmd.mono (fun R' hR' => (mem_outsidePart.1 hR').1)
  -- the counts
  have hvolpos : ∀ v, 0 < (volume (E v)).toReal := fun v =>
    ENNReal.toReal_pos (hEpos v).ne' (hEfin v).ne
  set Ar : Fin 3 → ℝ := fun v => Ca * (volume (E v)).toReal with hAr
  have hArpos : ∀ v, 0 < Ar v := fun v => mul_pos (by linarith) (hvolpos v)
  have hArτ : ∀ v, Ar v ≤ Ar τ := fun v =>
    mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (hEfin τ).ne (hEmax v)) (by linarith)
  have hratio : ∀ v, Ar v / Ar τ = (volume (E v)).toReal / (volume (E τ)).toReal := fun v => by
    simp only [hAr]; rw [mul_div_mul_left _ _ (by linarith : Ca ≠ 0)]
  -- the energy bounds
  set Λr : Fin 3 → ℝ := fun v => cm v * (if v = τ then 1 else Ar v / Ar τ) with hΛr
  have hΛr0 : ∀ v, 0 ≤ Λr v := fun v => by
    simp only [hΛr]
    refine mul_nonneg (hcm0 v) ?_
    split_ifs
    · exact zero_le_one
    · exact (div_pos (hArpos v) (hArpos τ)).le
  have hΛ : ∀ v, e P h v Cs ≤ ENNReal.ofReal (Λr v) := by
    intro v
    have hB := hC5 P Qs hQ Cs hboxCs h hhm hbdd v
    by_cases hv : v = τ
    · subst hv
      refine (le_ofReal_of_tailMass_le (bound := tailConst M) hC5nn hB
        fun W hW => tailMass_slot_le_tailConst (by linarith) (hbdd v) (dyadicInt_toReal_volume_pos W)).trans ?_
      refine ENNReal.ofReal_le_ofReal ?_
      simp only [hΛr, hcm, ite_true, mul_one]
      exact le_max_right _ _
    · have hdomv : ∀ x, yNorm (slotExp u v) (h v x) ≤ (E v).indicator (fun _ => (1 : ℝ)) x := by
        have := hH.dom v
        simp only [domSet, hv, ite_false] at this
        exact this
      refine (le_ofReal_of_tailMass_le (bound := 45 * excMass 48 E τ v) hC5nn hB
        fun W hW => ?_).trans ?_
      · obtain ⟨R', hR', hRW⟩ := hints Cs W hW
        have hnot : ¬ dyadicInt W.1 W.2 ⊆ Ω := fun hsub => (mem_outsidePart.1 hR').2 (hRW.trans hsub)
        refine (tailMass_slot_le (by linarith) (hEm v) hdomv (dyadicInt_toReal_volume_pos W)).trans ?_
        exact tailMass_indicator_le_excMass_of_not_subset (by linarith) (by norm_num) hv (hEm v)
          (hEfin v).ne (dyadicInt_ordConnected W) (dyadicInt_toReal_volume_pos W) hnot
      · refine ENNReal.ofReal_le_ofReal ?_
        have hex : excMass 48 E τ v = 48 * (Ar v / Ar τ) := by
          rw [hratio]; unfold excMass; ring
        simp only [hΛr, hcm, hv, ite_false]
        rw [hex]
        have hr0 : 0 ≤ Ar v / Ar τ := (div_pos (hArpos v) (hArpos τ)).le
        have h1 : C5 * 45 * 48 ≤ max (max 1 (C5 * 45 * 48)) (C5 * tailConst M) :=
          (le_max_right _ _).trans (le_max_left _ _)
        calc C5 * (45 * (48 * (Ar v / Ar τ))) = (C5 * 45 * 48) * (Ar v / Ar τ) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right h1 hr0
  -- the counts of V12
  have hstepE : ∀ (v : Fin 3) (S : Finset TriTile), IsResidual Cs S → ∃ ts : List Top,
      e P h v (removeTrees S ts) ≤ e P h v S / 2 ∧
      topSum (removedTrees S ts) * e P h v S ^ qPlus (Rof u) v ≤ ENNReal.ofReal (Ar v) := by
    intro v S hS
    obtain ⟨ts, h1, h2⟩ := hCE P Qs hQ Cs S hboxCs hTCCs hS h hhm hbdd v
    refine ⟨ts, h1, h2.trans ?_⟩
    have hmp : mixedPow (qX (Rof u) v) (slotExp u v) (h v) ≤ volume (E v) :=
      (mixedPow_le_volume (by linarith [two_le_qX hR4 v]) (measurableSet_domSet hEm τ v)
        (hH.dom v)).trans (measure_mono (domSet_subset E τ v))
    calc ENNReal.ofReal CE * mixedPow (qX (Rof u) v) (slotExp u v) (h v)
        ≤ ENNReal.ofReal CE * ENNReal.ofReal (volume (E v)).toReal := by
          gcongr
          rw [ENNReal.ofReal_toReal (hEfin v).ne]; exact hmp
      _ = ENNReal.ofReal (CE * (volume (E v)).toReal) := (ENNReal.ofReal_mul hCEnn).symm
      _ ≤ ENNReal.ofReal (Ar v) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) ENNReal.toReal_nonneg)
  have hmainB := hCf P T CT hT Qs hQ Cs hboxCs hTCCs (fun _ _ => trivial) χ m hmdCs h hhm hbdd
    (fun v => ENNReal.ofReal (Λr v)) (fun v => ENNReal.ofReal_lt_top) hΛ Ar hArpos hstepE
  have hη : 0 ≤ etaR (Rof u) := by unfold etaR; positivity
  have hts := tsum_min_le_region (R := Rof u) (θ := 0) hR4 le_rfl hη τ Ar hArpos hArτ hβsum' hβ0 hβ1
    Λr cm 1 hΛr0 hcm1 zero_le_one le_rfl (fun v => le_rfl)
  have hfin := hmainB.trans (mul_le_mul_right hts _)
  rw [← ENNReal.ofReal_mul (mul_nonneg hCf0 hCT), ← ofReal_norm] at hfin
  have hprodA : ∏ v, Ar v ^ β v = Ca * ∏ v, (volume (E v)).toReal ^ β v := by
    simp only [hAr]
    rw [Finset.prod_congr rfl fun v _ => Real.mul_rpow (by linarith : (0 : ℝ) ≤ Ca) ENNReal.toReal_nonneg,
      Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos (by linarith : 0 < Ca), hβsum', Real.rpow_one]
  have hnn : 0 ≤ Cf * CT * ((∏ v, cm v) * 1 ^ (0 : ℝ) * (countConst (Rof u) * ∏ v, Ar v ^ β v)) := by
    refine mul_nonneg (mul_nonneg hCf0 hCT) (mul_nonneg (mul_nonneg (Finset.prod_nonneg fun v _ => hcm0 v)
      (by simp)) (mul_nonneg (countConst_nonneg hR4) (Finset.prod_nonneg fun v _ =>
        Real.rpow_nonneg (hArpos v).le _)))
  refine ((ENNReal.ofReal_le_ofReal_iff hnn).1 hfin).trans_eq ?_
  rw [hprodA, Real.one_rpow]
  ring

end PrimeBHT.TimeFrequency.X2.V16
