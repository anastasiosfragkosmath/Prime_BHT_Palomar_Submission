module

public import PrimeBHT.TimeFrequency.Tile.Inside
public import PrimeBHT.TimeFrequency.Tile.OutsideGlue
public import PrimeBHT.TimeFrequency.Tile.Dilation

/-!
# Assembly of M1(ε) (blueprint C10, final step)

`InsideBound` (C10b, `Inside.lean`) bounds the form over the tiles with `I_t ⊆ F = refExceptional (E σ0) (E σ1)`
and fixes the major subset `Ẽ`; `triForm_filter_outside_le_orth` (C10a, `OutsideGlue.lean`) bounds the form over
the remaining tiles. Splitting `P` into these two parts gives `Λ_P(g') ≲ |E_{σ0}|^{1/2-ε}` for the `L²`-normalized
`g' = refG' E h`, and rescaling (`triForm_eq_prod_mul_triForm_refG'`) gives `NormM1 ε N C`; the normalization
reduction `exists_m1Statement_of_exists_normM1` (`Dilation.lean`) removes the restriction `1/2 < |E_{σ2}| ≤ 1`.

## Main results

* `normM1_of_le`: `NormM1 ε N (insideConst + outsideConst N ε)` for `0 < ε ≤ 1`, `N ≥ ⌈1/(2ε)⌉ + 11`.
* `exists_m1Statement`: for `0 < ε ≤ 1` there are `N, C > 0` with `M1Statement ε N C`
  (the body of the frozen `tri_restricted_eps ε`).
-/

@[expose] public section

namespace PrimeBHT.TimeFrequency.Tile

open MeasureTheory
open PrimeBHT.Statements

/-- The constant of the outside bound of `triForm_filter_outside_le_orth`. -/
noncomputable def outsideConst (N : ℕ) (ε : ℝ) : ℝ :=
  96 * max (weakBesselConst N) 0 * refSizeConst (orthSizeConst N) (sameScaleConst N) * (3 + 1 / ε)

theorem outsideConst_nonneg (N : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 ≤ outsideConst N ε := by
  unfold outsideConst refSizeConst orthSizeConst
  have h1 : 0 ≤ max (weakBesselConst N) 0 := le_max_right _ _
  have h2 : 0 ≤ Real.sqrt (16 * sameScaleConst N + 720) := Real.sqrt_nonneg _
  have h3 : 0 ≤ Real.sqrt (energyConst (sameScaleConst N)) := Real.sqrt_nonneg _
  have h4 : 0 ≤ 1 / ε := by positivity
  have h5 : 0 ≤ 2250 + 10 * Real.sqrt (16 * sameScaleConst N + 720) +
      100 * Real.sqrt (energyConst (sameScaleConst N)) := by positivity
  positivity

theorem rpow_half_le_rpow_neg_half_add {c ε : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hε : ε ≤ 1) :
    c ^ ((1 : ℝ) / 2) ≤ c ^ (-(1 : ℝ) / 2 + ε) :=
  Real.rpow_le_rpow_of_exponent_ge hc0 hc1 (by linarith)

/-- **The tri-tile estimate in normalized form**: `NormM1 ε N C` with `C = insideConst + outsideConst N ε`,
for `0 < ε ≤ 1` and `N ≥ ⌈1/(2ε)⌉ + 11`. -/
theorem normM1_of_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {N : ℕ}
    (hN : ⌈1 / (2 * ε)⌉₊ + 11 ≤ N) : NormM1 ε N (insideConst + outsideConst N ε) := by
  intro σ E hEm hE h01 h12 hhalf hone
  have hE0 : volume (E (σ 0)) ≠ 0 := (hE _).1.ne'
  obtain ⟨Et, hEtm, hEtsub, hEt2, hmain⟩ :=
    insideBound_of_le hε hN σ E hEm h01 h12 hE0 hhalf hone
  refine ⟨Et, hEtm, hEtsub, hEt2, ?_⟩
  intro a b s' α hν P hP φ hφ h hhm hdom1 hdom2
  classical
  have hdom : ∀ k x, ‖h k x‖ ≤ (E k).indicator (1 : ℝ → ℝ) x := by
    intro k x
    by_cases hk : k = σ 2
    · subst hk
      exact (hdom2 x).trans
        (Set.indicator_le_indicator_of_subset hEtsub (fun _ => zero_le_one) x)
    · exact hdom1 k hk x
  have hpos : ∀ k, 0 < (volume (E k)).toReal := fun k =>
    ENNReal.toReal_pos (hE k).1.ne' (hE k).2.ne
  have hin := hmain a b s' α hν P hP φ hφ h hhm hdom1 hdom2
  have hout := triForm_filter_outside_le_orth hν (by omega : 4 ≤ N) σ hEm h01 h12 hE0 hhalf hone
    hhm hdom hP hφ hε
  have hsplit : triForm P φ (refG' E h) =
      triForm (P.filter fun t => timeInt t ⊆ refExceptional (E (σ 0)) (E (σ 1))) φ (refG' E h) +
      triForm (P.filter fun t => ¬ timeInt t ⊆ refExceptional (E (σ 0)) (E (σ 1))) φ
        (refG' E h) := by
    unfold triForm
    rw [Finset.sum_filter_add_sum_filter_not]
  have hg : triForm P φ (refG' E h) ≤
      (insideConst + outsideConst N ε) * (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2 - ε) := by
    rw [hsplit, add_mul]
    exact add_le_add hin hout
  have hprod : (∏ k, (volume (E k)).toReal ^ ((1 : ℝ) / 2)) =
      (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2) * (volume (E (σ 1))).toReal ^ ((1 : ℝ) / 2) *
        (volume (E (σ 2))).toReal ^ ((1 : ℝ) / 2) := by
    rw [← Equiv.prod_comp σ (fun k => (volume (E k)).toReal ^ ((1 : ℝ) / 2)), Fin.prod_univ_three]
  rw [triForm_eq_prod_mul_triForm_refG' hpos, hprod]
  have ha := hpos (σ 0)
  have hc := hpos (σ 2)
  have hc1 : (volume (E (σ 2))).toReal ≤ 1 := hone
  have hK : 0 ≤ insideConst + outsideConst N ε :=
    add_nonneg insideConst_pos.le (outsideConst_nonneg N hε)
  have hadd : (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2) *
      (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2 - ε) = (volume (E (σ 0))).toReal ^ (1 - ε) := by
    rw [← Real.rpow_add ha]; ring_nf
  have hcle := rpow_half_le_rpow_neg_half_add hc hc1 hε1
  calc (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2) * (volume (E (σ 1))).toReal ^ ((1 : ℝ) / 2) *
        (volume (E (σ 2))).toReal ^ ((1 : ℝ) / 2) * triForm P φ (refG' E h)
      ≤ (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2) * (volume (E (σ 1))).toReal ^ ((1 : ℝ) / 2) *
        (volume (E (σ 2))).toReal ^ ((1 : ℝ) / 2) *
          ((insideConst + outsideConst N ε) * (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2 - ε)) :=
        mul_le_mul_of_nonneg_left hg (by positivity)
    _ = (insideConst + outsideConst N ε) *
          ((volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2) *
            (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2 - ε)) *
          (volume (E (σ 1))).toReal ^ ((1 : ℝ) / 2) *
          (volume (E (σ 2))).toReal ^ ((1 : ℝ) / 2) := by ring
    _ = (insideConst + outsideConst N ε) * (volume (E (σ 0))).toReal ^ (1 - ε) *
          (volume (E (σ 1))).toReal ^ ((1 : ℝ) / 2) *
          (volume (E (σ 2))).toReal ^ ((1 : ℝ) / 2) := by rw [hadd]
    _ ≤ (insideConst + outsideConst N ε) * (volume (E (σ 0))).toReal ^ (1 - ε) *
          (volume (E (σ 1))).toReal ^ ((1 : ℝ) / 2) *
          (volume (E (σ 2))).toReal ^ (-(1 : ℝ) / 2 + ε) := by
        have : 0 ≤ (insideConst + outsideConst N ε) * (volume (E (σ 0))).toReal ^ (1 - ε) *
            (volume (E (σ 1))).toReal ^ ((1 : ℝ) / 2) := by
          have := hpos (σ 1)
          positivity
        exact mul_le_mul_of_nonneg_left hcle this

/-- **M1(ε), existential form** (the body of the frozen `tri_restricted_eps ε`): for `0 < ε ≤ 1` there are
`N : ℕ` and `C > 0` with `M1Statement ε N C`. Here `N = ⌈1/(2ε)⌉ + 11`. -/
theorem exists_normM1 {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧ NormM1 ε N C :=
  ⟨⌈1 / (2 * ε)⌉₊ + 11, insideConst + outsideConst (⌈1 / (2 * ε)⌉₊ + 11) ε,
    add_pos_of_pos_of_nonneg insideConst_pos (outsideConst_nonneg _ hε), normM1_of_le hε hε1 le_rfl⟩

theorem exists_m1Statement {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧ M1Statement ε N C :=
  exists_m1Statement_of_exists_normM1 (exists_normM1 hε hε1)

end PrimeBHT.TimeFrequency.Tile
