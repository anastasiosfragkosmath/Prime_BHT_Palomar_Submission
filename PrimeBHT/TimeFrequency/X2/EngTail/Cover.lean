module

public import PrimeBHT.TimeFrequency.X2.EngTail.Near
public import PrimeBHT.TimeFrequency.Tile.Grid

/-!
# X2, node B5: the covering geometry of a family of tiles

For a finite family `S` of tiles `i` with time intervals `I_i = [2^{j i} v_i, 2^{j i}(v_i + 1))` (injective labels), let
`W(S) = ⋃_{i ∈ S} 3 I_i`.  This file shows: `W(S)` is measurable of finite measure (positive if `S ≠ ∅`); the maximal intervals
`I_L` (`L` in a sub-family `Lm`) are pairwise disjoint and cover; `3 I_i ⊆ 3 I_L` for `I_i ⊆ I_L`; `∑_L |I_L| ≤ |W(S)|`;
and, for a function `0 ≤ u ≤ 1` whose tile densities `|I_i|⁻¹ ∫ u (1 + |z - c_i|/|I_i|)^{-M}` are at most `λ`,
`∫_{W(S)} u ≤ (5/2)^M λ |W(S)|`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

section Cover

variable {ι : Type*}

/-- `3 I_i` (centre `c_i = 2^{j i}(v i + 1/2)`, length `3 · 2^{j i}`). -/
def dil3 (j v : ι → ℤ) (i : ι) : Set ℝ :=
  Ico ((2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2) - 3 * (2 : ℝ) ^ (j i) / 2)
    ((2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2) + 3 * (2 : ℝ) ^ (j i) / 2)

/-- `W(S) = ⋃_{i ∈ S} 3 I_i`. -/
def Wset (S : Finset ι) (j v : ι → ℤ) : Set ℝ := ⋃ i ∈ S, dil3 j v i

theorem measurableSet_dil3 (j v : ι → ℤ) (i : ι) : MeasurableSet (dil3 j v i) := measurableSet_Ico

theorem measurableSet_Wset (S : Finset ι) (j v : ι → ℤ) : MeasurableSet (Wset S j v) :=
  Finset.measurableSet_biUnion S fun i _ => measurableSet_dil3 j v i

theorem volume_dil3 (j v : ι → ℤ) (i : ι) : volume (dil3 j v i) = ENNReal.ofReal (3 * (2 : ℝ) ^ (j i)) := by
  unfold dil3
  rw [Real.volume_Ico]
  congr 1; ring

theorem volume_Wset_lt_top (S : Finset ι) (j v : ι → ℤ) : volume (Wset S j v) < ⊤ := by
  refine (measure_biUnion_finset_le S (dil3 j v)).trans_lt ?_
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  rw [volume_dil3]; exact ENNReal.ofReal_lt_top

theorem dil3_subset_Wset {S : Finset ι} {j v : ι → ℤ} {i : ι} (hi : i ∈ S) : dil3 j v i ⊆ Wset S j v :=
  fun _z hz => mem_iUnion₂.2 ⟨i, hi, hz⟩

theorem volume_Wset_pos {S : Finset ι} (j v : ι → ℤ) (hS : S.Nonempty) : 0 < volume (Wset S j v) := by
  obtain ⟨i, hi⟩ := hS
  refine lt_of_lt_of_le ?_ (measure_mono (dil3_subset_Wset (j := j) (v := v) hi))
  rw [volume_dil3]
  exact ENNReal.ofReal_pos.2 (by have := two_zpow_pos' (j i); positivity)

/-- Geometry of nested dyadic intervals: `I ⊆ I'` gives `s ≤ s'` and `|c - c'| ≤ (|I'| - |I|)/2`. -/
theorem dyadicInt_subset_geom {s v s' v' : ℤ} (h : dyadicInt s v ⊆ dyadicInt s' v') :
    s ≤ s' ∧ |(2 : ℝ) ^ s * ((v : ℝ) + 1 / 2) - (2 : ℝ) ^ s' * ((v' : ℝ) + 1 / 2)| ≤
      ((2 : ℝ) ^ s' - (2 : ℝ) ^ s) / 2 := by
  refine ⟨scale_le_of_dyadicInt_subset h, ?_⟩
  have hs : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) s
  have hlt : (2 : ℝ) ^ s * v < (2 : ℝ) ^ s * (v + 1) := by nlinarith
  unfold dyadicInt at h
  have h2 := (Set.Ico_subset_Ico_iff hlt).1 h
  rw [abs_le]
  constructor <;> nlinarith [h2.1, h2.2]

theorem dil3_subset_of_dyadicInt_subset {j v : ι → ℤ} {i L : ι}
    (h : dyadicInt (j i) (v i) ⊆ dyadicInt (j L) (v L)) : dil3 j v i ⊆ dil3 j v L := by
  obtain ⟨-, hg⟩ := dyadicInt_subset_geom h
  have hs : (0 : ℝ) < (2 : ℝ) ^ (j i) := zpow_pos (by norm_num) _
  rw [abs_le] at hg
  unfold dil3
  refine Ico_subset_Ico ?_ ?_ <;> nlinarith [hg.1, hg.2, abs_nonneg ((2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2) -
    (2 : ℝ) ^ (j L) * ((v L : ℝ) + 1 / 2))]

theorem dyadicInt_subset_dil3 (j v : ι → ℤ) (i : ι) : dyadicInt (j i) (v i) ⊆ dil3 j v i := by
  have hs : (0 : ℝ) < (2 : ℝ) ^ (j i) := zpow_pos (by norm_num) _
  unfold dyadicInt dil3
  refine Ico_subset_Ico ?_ ?_ <;> nlinarith

/-- **Maximal tiles**: a sub-family `Lm ⊆ S` whose time intervals are pairwise disjoint and cover those of `S`. -/
theorem exists_maximal [DecidableEq ι] (S : Finset ι) (j v : ι → ℤ)
    (hinj : Set.InjOn (fun i => (j i, v i)) (S : Set ι)) :
    ∃ Lm : Finset ι, Lm ⊆ S ∧ (∀ i ∈ S, ∃ L ∈ Lm, dyadicInt (j i) (v i) ⊆ dyadicInt (j L) (v L)) ∧
      ∀ L ∈ Lm, ∀ L' ∈ Lm, L ≠ L' → Disjoint (dyadicInt (j L) (v L)) (dyadicInt (j L') (v L')) := by
  classical
  refine ⟨S.filter (fun L => ∀ i ∈ S, dyadicInt (j L) (v L) ⊆ dyadicInt (j i) (v i) →
      dyadicInt (j i) (v i) ⊆ dyadicInt (j L) (v L)), Finset.filter_subset _ _, ?_, ?_⟩
  · intro i hi
    set T := S.filter (fun i' => dyadicInt (j i) (v i) ⊆ dyadicInt (j i') (v i')) with hT
    have hiT : i ∈ T := Finset.mem_filter.2 ⟨hi, subset_rfl⟩
    obtain ⟨L, hLT, hLmax⟩ := Finset.exists_max_image T j ⟨i, hiT⟩
    have hLS : L ∈ S := (Finset.mem_filter.1 hLT).1
    have hiL : dyadicInt (j i) (v i) ⊆ dyadicInt (j L) (v L) := (Finset.mem_filter.1 hLT).2
    refine ⟨L, Finset.mem_filter.2 ⟨hLS, fun i'' hi'' hLi'' => ?_⟩, hiL⟩
    have hi''T : i'' ∈ T := Finset.mem_filter.2 ⟨hi'', hiL.trans hLi''⟩
    have h1 : j i'' ≤ j L := hLmax i'' hi''T
    have h2 : j L ≤ j i'' := scale_le_of_dyadicInt_subset hLi''
    have hj : j L = j i'' := le_antisymm h2 h1
    have h3 : v L = v i'' := index_eq_of_dyadicInt_subset hj hLi''
    rw [← hj, ← h3]
  · intro L hL L' hL' hne
    simp only [Finset.mem_filter] at hL hL'
    rcases dyadicInt_nested_or_disjoint (j L) (v L) (j L') (v L') with h | h | h
    · exfalso
      have h' := hL.2 L' hL'.1 h
      have heq : dyadicInt (j L) (v L) = dyadicInt (j L') (v L') := Subset.antisymm h h'
      rw [dyadicInt_eq_iff] at heq
      exact hne (hinj hL.1 hL'.1 (Prod.ext heq.1 heq.2))
    · exfalso
      have h' := hL'.2 L hL.1 h
      have heq : dyadicInt (j L') (v L') = dyadicInt (j L) (v L) := Subset.antisymm h h'
      rw [dyadicInt_eq_iff] at heq
      exact hne (hinj hL.1 hL'.1 (Prod.ext heq.1.symm heq.2.symm))
    · exact h

theorem Wset_subset_max {S : Finset ι} {j v : ι → ℤ} {Lm : Finset ι}
    (hcov : ∀ i ∈ S, ∃ L ∈ Lm, dyadicInt (j i) (v i) ⊆ dyadicInt (j L) (v L)) :
    Wset S j v ⊆ ⋃ L ∈ Lm, dil3 j v L := fun z hz => by
  obtain ⟨i, hi, hz⟩ := mem_iUnion₂.1 hz
  obtain ⟨L, hL, hiL⟩ := hcov i hi
  exact mem_iUnion₂.2 ⟨L, hL, dil3_subset_of_dyadicInt_subset hiL hz⟩

/-- `∑_{L ∈ Lm} |I_L| ≤ |W(S)|` for pairwise disjoint `I_L ⊆ W(S)`. -/
theorem sum_len_le_volume {S : Finset ι} {j v : ι → ℤ} {Lm : Finset ι} (hLm : Lm ⊆ S)
    (hdisj : ∀ L ∈ Lm, ∀ L' ∈ Lm, L ≠ L' → Disjoint (dyadicInt (j L) (v L)) (dyadicInt (j L') (v L'))) :
    ∑ L ∈ Lm, (2 : ℝ) ^ (j L) ≤ (volume (Wset S j v)).toReal := by
  have hpd : (Lm : Set ι).PairwiseDisjoint (fun L => dyadicInt (j L) (v L)) :=
    fun L hL L' hL' hne => hdisj L hL L' hL' hne
  have h1 : ENNReal.ofReal (∑ L ∈ Lm, (2 : ℝ) ^ (j L)) ≤ volume (Wset S j v) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun L _ => (two_zpow_pos' (j L)).le)]
    calc ∑ L ∈ Lm, ENNReal.ofReal ((2 : ℝ) ^ (j L)) = ∑ L ∈ Lm, volume (dyadicInt (j L) (v L)) := by
          refine Finset.sum_congr rfl fun L _ => ?_
          rw [volume_dyadicInt]
      _ = volume (⋃ L ∈ Lm, dyadicInt (j L) (v L)) :=
          (measure_biUnion_finset hpd fun L _ => measurableSet_Ico).symm
      _ ≤ volume (Wset S j v) := by
          refine measure_mono fun z hz => ?_
          obtain ⟨L, hL, hz⟩ := mem_iUnion₂.1 hz
          exact dil3_subset_Wset (hLm hL) (dyadicInt_subset_dil3 j v L hz)
  exact (ENNReal.ofReal_le_iff_le_toReal (volume_Wset_lt_top S j v).ne).1 h1

/-- Mass of `u` on `3 I`: `∫_{3I} u ≤ (5/2)^M λ |I|` from the tile density. -/
theorem integral_dil3_le {M lam : ℝ} (hM : 1 < M) (j v : ℤ) {u : ℝ → ℝ} (hum : Measurable u)
    (hu0 : ∀ z, 0 ≤ u z) (hu1 : ∀ z, u z ≤ 1)
    (hd : ∫ z, ((2 : ℝ) ^ j)⁻¹ * (1 + |z - (2 : ℝ) ^ j * ((v : ℝ) + 1 / 2)| / (2 : ℝ) ^ j) ^ (-M) * u z ≤ lam) :
    ∫ z in Ico ((2 : ℝ) ^ j * ((v : ℝ) + 1 / 2) - 3 * (2 : ℝ) ^ j / 2)
        ((2 : ℝ) ^ j * ((v : ℝ) + 1 / 2) + 3 * (2 : ℝ) ^ j / 2), u z ≤ (5 / 2) ^ M * lam * (2 : ℝ) ^ j := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ j := two_zpow_pos' j
  set L : ℝ := (2 : ℝ) ^ j with hLdef
  set c : ℝ := (2 : ℝ) ^ j * ((v : ℝ) + 1 / 2) with hc
  set w : ℝ → ℝ := fun z => (1 + |z - c| / L) ^ (-M) * u z with hw
  have hint : Integrable (fun z : ℝ => (1 + |z - c| / L) ^ (-M)) := integrable_one_add_abs_sub_div_rpow hM c hL
  have hwi : Integrable w := by
    refine hint.mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact ((measurable_const.add ((continuous_abs.measurable.comp (measurable_id.sub_const c)).div_const L)).pow_const _
        |>.mul hum).aestronglyMeasurable
    · simp only [hw]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hu0 z))]
      calc _ ≤ (1 + |z - c| / L) ^ (-M) * 1 := mul_le_mul_of_nonneg_left (hu1 z) (by positivity)
        _ = _ := mul_one _
  have hw0 : ∀ z, 0 ≤ w z := fun z => by simp only [hw]; exact mul_nonneg (by positivity) (hu0 z)
  have h1 : ∫ z in Ico (c - 3 * L / 2) (c + 3 * L / 2), u z ≤
      ∫ z in Ico (c - 3 * L / 2) (c + 3 * L / 2), (5 / 2) ^ M * w z := by
    refine setIntegral_mono_on ?_ (hwi.const_mul _).integrableOn measurableSet_Ico fun z hz => ?_
    · refine Measure.integrableOn_of_bounded (M := 1) (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top) hum.aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ico).2 (Eventually.of_forall fun z _ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hu0 z)]; exact hu1 z
    · obtain ⟨h1, h2⟩ := hz
      have hz2 : |z - c| ≤ 3 * L / 2 := by rw [abs_le]; constructor <;> linarith
      have hb : 1 + |z - c| / L ≤ 5 / 2 := by
        have : |z - c| / L ≤ 3 / 2 := by rw [div_le_iff₀ hL]; linarith
        linarith
      have hb0 : (0 : ℝ) < 1 + |z - c| / L := by positivity
      have : (5 / 2 : ℝ) ^ (-M) ≤ (1 + |z - c| / L) ^ (-M) :=
        Real.rpow_le_rpow_of_nonpos hb0 hb (by linarith)
      have h52 : (5 / 2 : ℝ) ^ M * (5 / 2 : ℝ) ^ (-M) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; simp
      have hu := hu0 z
      simp only [hw]
      calc u z = ((5 / 2 : ℝ) ^ M * (5 / 2 : ℝ) ^ (-M)) * u z := by rw [h52, one_mul]
        _ ≤ ((5 / 2 : ℝ) ^ M * (1 + |z - c| / L) ^ (-M)) * u z := by
          gcongr
        _ = _ := by ring
  have h2 : ∫ z in Ico (c - 3 * L / 2) (c + 3 * L / 2), (5 / 2) ^ M * w z ≤ ∫ z, (5 / 2) ^ M * w z :=
    setIntegral_le_integral (hwi.const_mul _) (Eventually.of_forall fun z => mul_nonneg (by positivity) (hw0 z))
  have h3 : ∫ z, w z ≤ lam * L := by
    have e : ∫ z, L⁻¹ * (1 + |z - c| / L) ^ (-M) * u z = L⁻¹ * ∫ z, w z := by
      rw [← integral_const_mul]
      congr 1; ext z; simp only [hw]; ring
    rw [e] at hd
    have := mul_le_mul_of_nonneg_left hd hL.le
    rw [← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul] at this
    linarith
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ = (5 / 2) ^ M * ∫ z, w z := integral_const_mul _ _
    _ ≤ (5 / 2) ^ M * (lam * L) := by gcongr
    _ = (5 / 2) ^ M * lam * L := by ring

/-- **Mass of `u` on `W(S)`**: `∫_{W(S)} u ≤ (5/2)^M λ |W(S)|`. -/
theorem integral_Wset_le [DecidableEq ι] {M lam : ℝ} (hM : 1 < M) (hlam : 0 ≤ lam) (S : Finset ι) (j v : ι → ℤ)
    (hinj : Set.InjOn (fun i => (j i, v i)) (S : Set ι)) {u : ℝ → ℝ} (hum : Measurable u)
    (hu0 : ∀ z, 0 ≤ u z) (hu1 : ∀ z, u z ≤ 1)
    (hdens : ∀ i ∈ S, ∫ z, ((2 : ℝ) ^ (j i))⁻¹ *
      (1 + |z - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j i)) ^ (-M) * u z ≤ lam) :
    ∫ z in Wset S j v, u z ≤ (5 / 2) ^ M * lam * (volume (Wset S j v)).toReal := by
  obtain ⟨Lm, hLmS, hcov, hdisj⟩ := exists_maximal S j v hinj
  have hum' : ∀ L : ι, IntegrableOn u (dil3 j v L) := fun L => by
    refine Measure.integrableOn_of_bounded (M := 1) (by rw [volume_dil3]; exact ENNReal.ofReal_ne_top)
      hum.aestronglyMeasurable ?_
    refine (ae_restrict_iff' (measurableSet_dil3 j v L)).2 (Eventually.of_forall fun z _ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hu0 z)]; exact hu1 z
  have h1 : ∫ z in Wset S j v, u z ≤ ∑ L ∈ Lm, ∫ z in dil3 j v L, u z := by
    rw [← integral_indicator (measurableSet_Wset S j v)]
    have hsum : ∑ L ∈ Lm, ∫ z in dil3 j v L, u z = ∫ z, ∑ L ∈ Lm, (dil3 j v L).indicator u z := by
      rw [integral_finsetSum _ fun L _ => (integrable_indicator_iff (measurableSet_dil3 j v L)).2 (hum' L)]
      refine Finset.sum_congr rfl fun L _ => ?_
      rw [integral_indicator (measurableSet_dil3 j v L)]
    rw [hsum]
    refine integral_mono_of_nonneg (Eventually.of_forall fun z => indicator_nonneg (fun z _ => hu0 z) z)
      (integrable_finsetSum _ fun L _ => (integrable_indicator_iff (measurableSet_dil3 j v L)).2 (hum' L))
      (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ Wset S j v
    · obtain ⟨L, hL, hzL⟩ := mem_iUnion₂.1 (Wset_subset_max hcov hz)
      rw [indicator_of_mem hz]
      calc u z = (dil3 j v L).indicator u z := by rw [indicator_of_mem hzL]
        _ ≤ ∑ L ∈ Lm, (dil3 j v L).indicator u z :=
          Finset.single_le_sum (f := fun L => (dil3 j v L).indicator u z)
            (fun L _ => indicator_nonneg (fun z _ => hu0 z) z) hL
    · rw [indicator_of_notMem hz]
      exact Finset.sum_nonneg fun L _ => indicator_nonneg (fun z _ => hu0 z) z
  have h2 : ∀ L ∈ Lm, ∫ z in dil3 j v L, u z ≤ (5 / 2) ^ M * lam * (2 : ℝ) ^ (j L) := fun L hL =>
    integral_dil3_le hM (j L) (v L) hum hu0 hu1 (hdens L (hLmS hL))
  calc ∫ z in Wset S j v, u z ≤ ∑ L ∈ Lm, ∫ z in dil3 j v L, u z := h1
    _ ≤ ∑ L ∈ Lm, (5 / 2) ^ M * lam * (2 : ℝ) ^ (j L) := Finset.sum_le_sum h2
    _ = (5 / 2) ^ M * lam * ∑ L ∈ Lm, (2 : ℝ) ^ (j L) := by rw [← Finset.mul_sum]
    _ ≤ (5 / 2) ^ M * lam * (volume (Wset S j v)).toReal := by
        have : 0 ≤ (5 / 2 : ℝ) ^ M * lam := by positivity
        exact mul_le_mul_of_nonneg_left (sum_len_le_volume hLmS hdisj) this

end Cover

end PrimeBHT.TimeFrequency.X2
