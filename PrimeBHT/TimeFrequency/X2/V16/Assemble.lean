module

public import PrimeBHT.TimeFrequency.X2.V16.Hyps

/-!
# X2, node V16: the shared assembly of B10 and B11 (conversion of `main_estimate` to the region lemma)

Two pieces, both pure bookkeeping:

* `tsum_min_le_region` (analysis): the `ℝ≥0∞`-valued level sum of `main_estimate`, with bounds
  `Λb_v ≤ c_v A_v/A_τ` (`v ≠ τ`) and `Λb_τ ≤ c_τ ε`, is at most `∏ c_v · ε^θ · countConst R · ∏ A_v^{β_v}`
  (B9 + `tsum_levelTerm_le_region`; `θ = 0` is B10, `θ = η` is B11);
* `form_le_main` (tiles): the instance of `main_estimate` on a collection `Cs` of tiles: admissible collections are the
  residuals of `Cs`, the energies are `eng 𝔭.loc (slotExp u v) v (h v) · (qX R v)`, the step is V12 (hypothesis `hstep`),
  the tree bound is V15 (`TreeLemmaStatement`) on the removed maximal trees (good by `goodTree_maxTree`) and on one-tile trees.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.V16

/-! ### From `ℝ≥0∞` to `ℝ` -/

theorem ofReal_two_zpow (k : ℤ) : ENNReal.ofReal ((2 : ℝ) ^ k) = (2 : ℝ≥0∞) ^ k := by
  rw [← ENNReal.rpow_intCast, ← Real.rpow_intCast, ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp

/-- The summand of `main_estimate` as the `ofReal` of a real number. -/
theorem ofReal_summand (q Ar Λr : Fin 3 → ℝ) (hA : ∀ v, 0 < Ar v) (hΛ : ∀ v, 0 ≤ Λr v)
    (hq : ∀ v, 0 ≤ 1 / q v) (k : ℤ) :
    (2 : ℝ≥0∞) ^ k * ∏ v, min (ENNReal.ofReal (Λr v)) (((2 : ℝ≥0∞) ^ (-k) * ENNReal.ofReal (Ar v)) ^ (1 / q v)) =
      ENNReal.ofReal ((2 : ℝ) ^ k * ∏ v, min (Λr v) (((2 : ℝ) ^ (-k) * Ar v) ^ (1 / q v))) := by
  have hpos : ∀ v, 0 ≤ ((2 : ℝ) ^ (-k) * Ar v) ^ (1 / q v) := fun v =>
    Real.rpow_nonneg (mul_nonneg (zpow_nonneg (by norm_num) _) (hA v).le) _
  rw [ENNReal.ofReal_mul (zpow_nonneg (by norm_num) _), ofReal_two_zpow,
    ENNReal.ofReal_prod_of_nonneg (fun v _ => le_min (hΛ v) (hpos v))]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [ENNReal.ofReal_min]
  congr 1
  rw [← ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (zpow_nonneg (by norm_num) _) (hA v).le) (hq v),
    ENNReal.ofReal_mul (zpow_nonneg (by norm_num) _), ofReal_two_zpow]

/-! ### The real inequality, slot by slot (B9) -/

theorem slot_bound {R θ : ℝ} (hR : 4 ≤ R) (hθ0 : 0 ≤ θ) (hθ : θ ≤ etaR R) (τ v : Fin 3)
    (Ar : Fin 3 → ℝ) (hA : ∀ v, 0 < Ar v) (k : ℤ) (Λ c ε : ℝ) (hc : 1 ≤ c) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hΛ : Λ ≤ c * (if v = τ then ε else Ar v / Ar τ)) :
    min Λ (((2 : ℝ) ^ (-k) * Ar v) ^ (1 / qPlus R v)) ≤
      c * (if v = τ then ε ^ θ else 1) *
        min (Ar v / Ar τ) (((2 : ℝ) ^ (-k) * Ar v) ^ (1 / qTau R θ τ v)) := by
  have hR0 : 0 < R := by linarith
  have hX : 0 ≤ (2 : ℝ) ^ (-k) * Ar v := mul_nonneg (zpow_nonneg (by norm_num) _) (hA v).le
  have hthr : 0 ≤ ((2 : ℝ) ^ (-k) * Ar v) ^ (1 / qPlus R v) := Real.rpow_nonneg hX _
  have h1 : min Λ (((2 : ℝ) ^ (-k) * Ar v) ^ (1 / qPlus R v)) ≤
      min (c * (if v = τ then ε else Ar v / Ar τ)) (((2 : ℝ) ^ (-k) * Ar v) ^ (1 / qPlus R v)) :=
    min_le_min hΛ le_rfl
  refine h1.trans ?_
  have h2 := min_mul_le_mul_min (a := if v = τ then ε else Ar v / Ar τ) hc hthr
  refine h2.trans ?_
  by_cases hv : v = τ
  · subst hv
    simp only [ite_true, div_self (hA v).ne']
    have hθ1 : θ ≤ 1 := by
      have : etaR R ≤ 1 := by unfold etaR; rw [div_le_one (by positivity)]; linarith
      linarith
    have hq : qTau R θ v v = qPlus R v / (1 - θ) := by simp [qTau]
    have h3 := min_le_rpow_mul_min_one (x := ((2 : ℝ) ^ (-k) * Ar v) ^ (1 / qPlus R v)) hε0 hε1 hthr hθ0 hθ1
    have h4 : (((2 : ℝ) ^ (-k) * Ar v) ^ (1 / qPlus R v)) ^ (1 - θ) =
        ((2 : ℝ) ^ (-k) * Ar v) ^ (1 / qTau R θ v v) := by
      rw [← Real.rpow_mul hX, hq]
      congr 1
      have : 1 - θ ≠ 0 := by
        have : etaR R < 1 := by unfold etaR; rw [div_lt_one (by positivity)]; linarith
        linarith
      field_simp
    rw [h4] at h3
    calc c * min ε (((2 : ℝ) ^ (-k) * Ar v) ^ (1 / qPlus R v))
        ≤ c * (ε ^ θ * min 1 (((2 : ℝ) ^ (-k) * Ar v) ^ (1 / qTau R θ v v))) :=
          mul_le_mul_of_nonneg_left h3 (by linarith)
      _ = _ := by ring
  · simp only [hv, ite_false]
    have hq : qTau R θ τ v = qPlus R v := by simp [qTau, hv]
    rw [hq]
    simp only [mul_one, le_refl]


/-! ### The level sum -/

/-- **The level sum of `main_estimate` in the region** (B9 + B8).  With `0 < A_v ≤ A_τ`, `Λb_v ≤ c_v A_v/A_τ`
(`v ≠ τ`), `Λb_τ ≤ c_τ ε` (`0 ≤ ε ≤ 1`): the sum `∑_k 2^k ∏_v min (Λb_v) ((2^{-k} A_v)^{1/q⁺_v})` is at most
`(∏ c_v) ε^θ · countConst R · ∏ A_v^{β_v}`, for `β` in the corner region, `0 ≤ θ ≤ η`. -/
theorem tsum_min_le_region {R θ : ℝ} (hR : 4 ≤ R) (hθ0 : 0 ≤ θ) (hθ : θ ≤ etaR R) (τ : Fin 3)
    (Ar : Fin 3 → ℝ) (hA : ∀ v, 0 < Ar v) (hAτ : ∀ v, Ar v ≤ Ar τ)
    {β : Fin 3 → ℝ} (hβ : ∑ v, β v = 1) (h0 : |β 0 - 1 / 2| ≤ 1 / (8 * R))
    (h1 : |β 1 - 1 / 2| ≤ 1 / (8 * R)) (Λr c : Fin 3 → ℝ) (ε : ℝ) (hΛ0 : ∀ v, 0 ≤ Λr v)
    (hc : ∀ v, 1 ≤ c v) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hΛ : ∀ v, Λr v ≤ c v * (if v = τ then ε else Ar v / Ar τ)) :
    ∑' k : ℤ, (2 : ℝ≥0∞) ^ k * ∏ v, min (ENNReal.ofReal (Λr v))
        (((2 : ℝ≥0∞) ^ (-k) * ENNReal.ofReal (Ar v)) ^ (1 / qPlus R v)) ≤
      ENNReal.ofReal ((∏ v, c v) * ε ^ θ * (countConst R * ∏ v, Ar v ^ β v)) := by
  have hR0 : 0 < R := by linarith
  have hη : 0 < etaR R := by unfold etaR; positivity
  have hqp : ∀ v, 1 < qPlus R v := fun v => by
    have h := qX_lt_qPlus hR v
    have h2 := two_le_qX hR v
    linarith
  have hq0 : ∀ v, 0 ≤ 1 / qPlus R v := fun v => by have := hqp v; positivity
  have hAτpos : 0 < Ar τ := hA τ
  -- the real-valued summand
  have hterm : ∀ k : ℤ, (2 : ℝ) ^ k * ∏ v, min (Λr v) (((2 : ℝ) ^ (-k) * Ar v) ^ (1 / qPlus R v)) ≤
      ((∏ v, c v) * ε ^ θ) * levelTerm (qTau R θ τ) Ar τ k := by
    intro k
    have hfac := fun v => slot_bound hR hθ0 hθ τ v Ar hA k (Λr v) (c v) ε (hc v) hε0 hε1 (hΛ v)
    have hprod : ∏ v, min (Λr v) (((2 : ℝ) ^ (-k) * Ar v) ^ (1 / qPlus R v)) ≤
        ∏ v, (c v * (if v = τ then ε ^ θ else 1) *
          min (Ar v / Ar τ) (((2 : ℝ) ^ (-k) * Ar v) ^ (1 / qTau R θ τ v))) :=
      Finset.prod_le_prod₀
        (fun v _ => le_min (hΛ0 v) (Real.rpow_nonneg
          (mul_nonneg (zpow_nonneg (by norm_num) _) (hA v).le) _))
        (fun v _ => hfac v)
    have hite : ∏ v : Fin 3, (if v = τ then ε ^ θ else 1) = ε ^ θ := by
      simp
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hite] at hprod
    unfold levelTerm
    calc (2 : ℝ) ^ k * ∏ v, min (Λr v) (((2 : ℝ) ^ (-k) * Ar v) ^ (1 / qPlus R v))
        ≤ (2 : ℝ) ^ k * ((∏ v, c v) * ε ^ θ * ∏ v, min (Ar v / Ar τ)
            (((2 : ℝ) ^ (-k) * Ar v) ^ (1 / qTau R θ τ v))) :=
          mul_le_mul_of_nonneg_left hprod (zpow_nonneg (by norm_num) _)
      _ = _ := by ring
  have hCc : 0 ≤ (∏ v, c v) * ε ^ θ :=
    mul_nonneg (Finset.prod_nonneg fun v _ => by linarith [hc v]) (Real.rpow_nonneg hε0 _)
  have hsum := summable_levelTerm_region hR hθ0 hθ τ Ar hA hAτ hβ h0 h1
  have hlt0 : ∀ k : ℤ, 0 ≤ levelTerm (qTau R θ τ) Ar τ k := fun k => levelTerm_nonneg _ Ar τ hA k
  calc ∑' k : ℤ, (2 : ℝ≥0∞) ^ k * ∏ v, min (ENNReal.ofReal (Λr v))
        (((2 : ℝ≥0∞) ^ (-k) * ENNReal.ofReal (Ar v)) ^ (1 / qPlus R v))
      = ∑' k : ℤ, ENNReal.ofReal ((2 : ℝ) ^ k *
          ∏ v, min (Λr v) (((2 : ℝ) ^ (-k) * Ar v) ^ (1 / qPlus R v))) :=
        tsum_congr fun k => ofReal_summand (qPlus R) Ar Λr hA hΛ0 hq0 k
    _ ≤ ∑' k : ℤ, ENNReal.ofReal (((∏ v, c v) * ε ^ θ) * levelTerm (qTau R θ τ) Ar τ k) :=
        ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal (hterm k)
    _ = ENNReal.ofReal (∑' k : ℤ, ((∏ v, c v) * ε ^ θ) * levelTerm (qTau R θ τ) Ar τ k) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hCc (hlt0 k))
          (hsum.mul_left _)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left (tsum_levelTerm_le_region hR hθ0 hθ τ Ar hA hAτ hβ h0 h1) hCc


/-! ### The instance of `main_estimate` on a collection of tiles -/

/-- **B7 instantiated on a collection of tiles, generic in the energy family `e`.**  Under the tree bound `EnergyTreeA A`
(REV3: `A = True` is V15, `A = SingleScale` is V15s; `hA` says that every sub-collection of `Cs` satisfies `A`)
(V15) and monotonicity of `e`, the form on a collection `Cs` with `HasTC` is bounded by the level sum of
`main_estimate`, provided the energies of `Cs` are bounded by finite `Λb_v`, and the energy-halving step with count
`Ar_v` is available for every residual of `Cs` (V12). -/
theorem form_le_of_energy {u : ℝ} (hu : 1 < u) {𝔭 : Params} {e : EnergyFamily}
    {A : Finset TriTile → Prop} (hmono : EnergyMono e) (htree : EnergyTreeA A e u 𝔭) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (T : Form P) (CT : ℝ), FormBound u T CT →
      ∀ (Qs : Set Box), IsRankOne 𝔭.J Qs → ∀ (Cs : Finset TriTile), (∀ R ∈ Cs, R.box ∈ Qs) → HasTC Cs →
      (∀ S : Finset TriTile, S ⊆ Cs → A S) →
      ∀ (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ), IsModelData 𝔭 Cs χ m →
      ∀ (h : Fin 3 → ℝ → ZMod P → ℂ), (∀ i, Measurable (h i)) →
      (∀ v x, yNorm (slotExp u v) (h v x) ≤ 1) →
      ∀ (Λb : Fin 3 → ℝ≥0∞), (∀ v, Λb v < ⊤) → (∀ v, e P h v Cs ≤ Λb v) →
      ∀ (Ar : Fin 3 → ℝ), (∀ v, 0 < Ar v) →
      (∀ (v : Fin 3) (S : Finset TriTile), IsResidual Cs S → ∃ ts : List Top,
          e P h v (removeTrees S ts) ≤ e P h v S / 2 ∧
          topSum (removedTrees S ts) * e P h v S ^ qPlus (Rof u) v ≤ ENNReal.ofReal (Ar v)) →
        ‖modelForm T Cs χ m (h 0) (h 1) (h 2)‖ₑ ≤ ENNReal.ofReal (C * CT) *
          ∑' k : ℤ, (2 : ℝ≥0∞) ^ k * ∏ v, min (Λb v)
            (((2 : ℝ≥0∞) ^ (-k) * ENNReal.ofReal (Ar v)) ^ (1 / qPlus (Rof u) v)) := by
  have hR4 : 4 ≤ Rof u := four_le_Rof hu
  obtain ⟨Cm, hCm, hmain⟩ := main_estimate
  obtain ⟨Ct, hCt0, hCt⟩ := htree
  refine ⟨Cm.toReal * Ct, mul_nonneg ENNReal.toReal_nonneg hCt0, ?_⟩
  intro P _ T CT hT Qs hQ Cs hbox hTC hA χ m hmd h hmeas hbdd Λb hΛb hΛ Ar hAr hstep
  have hCT : 0 ≤ CT := not_lt.1 fun hneg => not_bound_of_neg T (by linarith) hneg hT
  -- the data of `main_estimate`
  set lam : TriTile → ℂ := fun P' =>
    if P' ∈ Cs then modelForm T {P'} χ m (h 0) (h 1) (h 2) else 0 with hlam
  have hsum_lam : ∀ S : Finset TriTile, S ⊆ Cs → ∑ P' ∈ S, lam P' = modelForm T S χ m (h 0) (h 1) (h 2) := by
    intro S hS
    have hl : ∀ P' ∈ S, lam P' = modelForm T {P'} χ m (h 0) (h 1) (h 2) :=
      fun P' hP' => by simp only [hlam, hS hP', ite_true]
    rw [Finset.sum_congr rfl hl]
    unfold modelForm
    simp only [Finset.sum_singleton]
  -- the tree bound (V15) on sub-collections of `Cs`
  have htree' : ∀ (Tr : Finset TriTile) (t : Top), IsGoodTree Tr t → Tr ⊆ Cs →
      ‖modelForm T Tr χ m (h 0) (h 1) (h 2)‖ₑ ≤ ENNReal.ofReal (Ct * CT) *
        ENNReal.ofReal ((2 : ℝ) ^ t.1.1) * ∏ w, e P h w Tr := by
    intro Tr t hg hsub
    exact hCt P T CT hT Qs hQ Tr t hg (hA Tr hsub) (fun R hR => hbox R (hsub hR)) χ m (hmd.mono hsub) h hmeas hbdd
  have hone : ∀ P' : TriTile, ‖lam P'‖ₑ ≤ ENNReal.ofReal (Ct * CT) *
      ENNReal.ofReal ((2 : ℝ) ^ P'.box.scale) * ∏ w, e P h w {P'} := by
    intro P'
    by_cases hP' : P' ∈ Cs
    · obtain ⟨t, ht1, hgood⟩ := isGoodTree_singleton P'
      have := htree' {P'} t hgood (Finset.singleton_subset_iff.2 hP')
      have e1 : t.1.1 = P'.box.scale := congrArg Prod.fst ht1
      rw [e1] at this
      simpa only [hlam, hP', ite_true] using this
    · simp [hlam, hP']
  have hstepmain : ∀ (v : Fin 3) (S : Finset TriTile), IsResidual Cs S →
      ∃ 𝒯 : List (Finset TriTile × ℝ≥0∞),
        (∀ T' ∈ 𝒯, T'.1 ⊆ S) ∧ 𝒯.Pairwise (fun T' T'' => Disjoint T'.1 T''.1) ∧
        IsResidual Cs (S \ (𝒯.map Prod.fst).foldr (· ∪ ·) ∅) ∧
        e P h v (S \ (𝒯.map Prod.fst).foldr (· ∪ ·) ∅) ≤ e P h v S / 2 ∧
        (𝒯.map Prod.snd).sum * e P h v S ^ qPlus (Rof u) v ≤ ENNReal.ofReal (Ar v) ∧
        ∀ T' ∈ 𝒯, ‖∑ P' ∈ T'.1, lam P'‖ₑ ≤
          ENNReal.ofReal (Ct * CT) * T'.2 * ∏ w, e P h w T'.1 := by
    intro v S hS
    obtain ⟨ts, hhalf, hcount⟩ := hstep v S hS
    have hmapfst : ((removedTrees S ts).map (fun T' => (T'.1, ENNReal.ofReal ((2 : ℝ) ^ T'.2.1.1)))).map
        Prod.fst = (removedTrees S ts).map Prod.fst := by
      simp [List.map_map, Function.comp_def]
    have hsdiff : S \ (((removedTrees S ts).map (fun T' => (T'.1, ENNReal.ofReal ((2 : ℝ) ^ T'.2.1.1)))).map
        Prod.fst).foldr (· ∪ ·) ∅ = removeTrees S ts := by
      rw [hmapfst, removeTrees_eq_sdiff]
    refine ⟨(removedTrees S ts).map (fun T' => (T'.1, ENNReal.ofReal ((2 : ℝ) ^ T'.2.1.1))), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro T' hT'
      obtain ⟨T'', hT'', rfl⟩ := List.mem_map.1 hT'
      exact removedTrees_subset S ts T'' hT''
    · exact (removedTrees_pairwise S ts).map _ (fun _ _ h => h)
    · rw [hsdiff]; exact hS.removeTrees ts
    · rw [hsdiff]; exact hhalf
    · have : (((removedTrees S ts).map (fun T' => (T'.1, ENNReal.ofReal ((2 : ℝ) ^ T'.2.1.1)))).map
          Prod.snd).sum = topSum (removedTrees S ts) := by
        simp [topSum, List.map_map, Function.comp_def]
      rw [this]; exact hcount
    · intro T' hT'
      obtain ⟨T'', hT'', rfl⟩ := List.mem_map.1 hT'
      obtain ⟨ts₀, hspec⟩ := removedTrees_spec S ts T'' hT''
      have hres := hS.removeTrees ts₀
      have hgood : IsGoodTree T''.1 T''.2 := by
        rw [hspec]; exact goodTree_maxTree hQ hbox hTC hres T''.2
      have hsub : T''.1 ⊆ Cs := (removedTrees_subset S ts T'' hT'').trans hS.subset
      simp only
      rw [hsum_lam _ hsub]
      exact htree' T''.1 T''.2 hgood hsub
  have hq1 : ∀ v, 1 ≤ qPlus (Rof u) v := fun v => by
    have := qX_lt_qPlus hR4 v
    have := two_le_qX hR4 v
    linarith
  have key := hmain (ι := TriTile) lam (fun P' => ENNReal.ofReal ((2 : ℝ) ^ P'.box.scale)) (IsResidual Cs)
    (e P h) (qPlus (Rof u)) (fun v => ENNReal.ofReal (Ar v)) Λb (ENNReal.ofReal (Ct * CT))
    hq1 (fun v => ENNReal.ofReal_pos.2 (hAr v)) (fun v => ENNReal.ofReal_lt_top) hΛb
    (fun P' => ENNReal.ofReal_lt_top) (fun v S S' hSS => hmono P h v hSS) hstepmain hone Cs
    (isResidual_refl Cs) hΛ
  rw [hsum_lam Cs Finset.Subset.rfl] at key
  calc ‖modelForm T Cs χ m (h 0) (h 1) (h 2)‖ₑ
      ≤ Cm * ENNReal.ofReal (Ct * CT) * ∑' k : ℤ, (2 : ℝ≥0∞) ^ k * ∏ v, min (Λb v)
          (((2 : ℝ≥0∞) ^ (-k) * ENNReal.ofReal (Ar v)) ^ (1 / qPlus (Rof u) v)) := key
    _ = ENNReal.ofReal (Cm.toReal * Ct * CT) * ∑' k : ℤ, (2 : ℝ≥0∞) ^ k * ∏ v, min (Λb v)
          (((2 : ℝ≥0∞) ^ (-k) * ENNReal.ofReal (Ar v)) ^ (1 / qPlus (Rof u) v)) := by
        rw [mul_assoc Cm.toReal Ct CT, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hCm.ne]

/-! ### Facts on the hull data -/

/-- The set dominating slot `v`: `E v` for `v ≠ τ`, the major subset `Ẽ` for `v = τ`. -/
def domSet (E : Fin 3 → Set ℝ) (τ v : Fin 3) : Set ℝ := if v = τ then exceptionalMajor 48 E τ else E v

theorem measurableSet_domSet {E : Fin 3 → Set ℝ} (hEm : ∀ i, MeasurableSet (E i)) (τ v : Fin 3) :
    MeasurableSet (domSet E τ v) := by
  unfold domSet; split_ifs
  · exact measurableSet_exceptionalMajor 48 τ (hEm τ) |> fun h => by assumption
  · exact hEm v

theorem domSet_subset (E : Fin 3 → Set ℝ) (τ v : Fin 3) : domSet E τ v ⊆ E v := by
  unfold domSet; split_ifs with hv
  · subst hv; exact exceptionalMajor_subset 48 E v
  · exact Set.Subset.rfl

theorem _root_.PrimeBHT.TimeFrequency.X2.IsHullData.dom {P : ℕ} [NeZero P] {u : ℝ} {E : Fin 3 → Set ℝ} {τ : Fin 3}
    {h : Fin 3 → ℝ → ZMod P → ℂ} (hH : IsHullData u E τ h) (v : Fin 3) :
    Interp.VDominatedBy (slotNorms u v) (domSet E τ v) (h v) := by
  obtain ⟨-, -, -, -, -, hdv, hdτ⟩ := hH
  unfold domSet
  by_cases hv : v = τ
  · subst hv; simpa using hdτ
  · simpa [hv] using hdv v hv

theorem _root_.PrimeBHT.TimeFrequency.X2.IsHullData.yNorm_le_one {P : ℕ} [NeZero P] {u : ℝ} {E : Fin 3 → Set ℝ} {τ : Fin 3}
    {h : Fin 3 → ℝ → ZMod P → ℂ} (hH : IsHullData u E τ h) (v : Fin 3) (x : ℝ) :
    yNorm (slotExp u v) (h v x) ≤ 1 := by
  have := hH.dom v x
  refine this.trans ?_
  by_cases hx : x ∈ domSet E τ v
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- `‖F‖_{L^q(ℝ; L^s(Y))}^q ≤ |S|` for `F` dominated by `1_S`. -/
theorem mixedPow_le_volume {P : ℕ} [NeZero P] {s q : ℝ} (hq : 0 < q) {S : Set ℝ}
    (hS : MeasurableSet S) {F : ℝ → ZMod P → ℂ}
    (hF : ∀ x, yNorm s (F x) ≤ S.indicator (fun _ => (1 : ℝ)) x) : mixedPow q s F ≤ volume S := by
  unfold mixedPow
  calc ∫⁻ x, ENNReal.ofReal (yNorm s (F x) ^ q) ≤ ∫⁻ x, S.indicator (1 : ℝ → ℝ≥0∞) x := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ S
        · have h1 : yNorm s (F x) ≤ 1 := by simpa [Set.indicator_of_mem hx] using hF x
          have h2 : yNorm s (F x) ^ q ≤ 1 := by
            calc yNorm s (F x) ^ q ≤ 1 ^ q := Real.rpow_le_rpow (yNorm_nonneg' _ _) h1 hq.le
              _ = 1 := Real.one_rpow q
          simpa [Set.indicator_of_mem hx] using ENNReal.ofReal_le_ofReal h2
        · have h1 : yNorm s (F x) ≤ 0 := by simpa [Set.indicator_of_notMem hx] using hF x
          have h0 : yNorm s (F x) = 0 := le_antisymm h1 (yNorm_nonneg' _ _)
          simp [Set.indicator_of_notMem hx, h0, Real.zero_rpow hq.ne']
    _ = volume S := lintegral_indicator_one hS

end PrimeBHT.TimeFrequency.X2.V16
