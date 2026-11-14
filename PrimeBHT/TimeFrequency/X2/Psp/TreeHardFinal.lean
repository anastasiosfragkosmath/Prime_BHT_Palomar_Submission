module

public import PrimeBHT.TimeFrequency.X2.Psp.TreeHardMain
public import PrimeBHT.TimeFrequency.X2.Psp.OverlapLean

/-!
# X2, V15 (assembly), step 12: the hard parts from `OverlapPspLean`, and `treeLemmaRev2_of_overlapPsp`

`OverlapPspLean 𝔭` is the part of `OverlapPsp` that the hard parts need: the overlapping slot is a HILBERT slot `k ≠ 2` with
`(s, q) = (2, 2)`, `K₀ = 2`; (O1) with boundedness; (O2); no (O3).

`hardPart_of_overlapPspLean`: `OverlapPspLean → HardPartStatement`;  `treeLemmaRev2_of_overlapPsp`: V15 from `OverlapPspLean` and
the second profile.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform Real ContDiff
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

theorem treePart_idem (Tr : Finset TriTile) (t : Top) (A : Finset (Fin 3)) :
    treePart (treePart Tr t A) t A = treePart Tr t A := by
  unfold treePart
  rw [Finset.filter_filter]
  simp only [and_self]

section Glue

variable {P : ℕ} [NeZero P] {𝔭 : Params} {η η' : ℝ → ℝ} {Tr TA : Finset TriTile} {t : Top} {χ : TriTile → ℝ → ℝ}
  {m : TriTile → Fin 3 → ℝ → ℂ}

/-- The constant of the conversion error in the `engV` form. -/
def convConst (𝔭 : Params) (R : ℝ) : ℝ :=
  24 * bLayerConst 𝔭 * ∏ k : Fin 3, (cutK 𝔭 ^ (1 / 6 : ℝ) * lacSConst 𝔭 (qv R k) ((𝔭.N : ℝ) / 6))

/-- **The conversion error in the `engV` form.** -/
theorem conv_bound (pd : PartData 𝔭 η η' Tr TA t χ m) {u R : ℝ} (hu : 1 < u) (hR : 2 < R) {T : Form P} {CT : ℝ}
    (hT : FormBound u T CT) {F : Fin 3 → ℝ → ZMod P → ℂ} (hF : ∀ k, Measurable (F k))
    (hFb : ∀ k, ∃ B, ∀ x, yNorm 2 (F k x) ≤ B) (R₀ : ℤ → TriTile)
    (hR₀ : ∀ σ ∈ treeScales TA, R₀ σ ∈ layer' TA σ) :
    ‖∑ σ ∈ treeScales TA, ∫ x, ((layerCut η TA σ x - layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
        T (tmult (m (R₀ σ) 0) (F 0) x) (tmult (m (R₀ σ) 1) (F 1) x) (tmult (m (R₀ σ) 2) (F 2) x)‖ₑ ≤
      ENNReal.ofReal (convConst 𝔭 R * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) *
        ∏ k : Fin 3, engV 𝔭 u R k (F k) Tr := by
  obtain ⟨hN, -, -, hC⟩ := pd.h𝔭.bounds
  have hCT : 0 ≤ CT := nonneg_of_formBound (by linarith) hT
  have hKp : 0 < cutK 𝔭 := cutK_pos (by linarith)
  have hbc := bLayerConst_nonneg pd.hη (by omega : 5 ≤ 𝔭.N)
  have h2 := conv_error pd hu hR hT hF hFb R₀ hR₀
  have hSk : ∀ k : Fin 3, 0 ≤ cutK 𝔭 ^ (1 / 6 : ℝ) * lacSConst 𝔭 (qv R k) ((𝔭.N : ℝ) / 6) := fun k =>
    mul_nonneg (Real.rpow_nonneg hKp.le _) (lacSConst_nonneg pd.h𝔭t (qv_gt_one hR k) _)
  have hprod : convProd 𝔭 u R F Tr = ENNReal.ofReal (∏ k : Fin 3, (cutK 𝔭 ^ (1 / 6 : ℝ) *
      lacSConst 𝔭 (qv R k) ((𝔭.N : ℝ) / 6))) * ∏ k : Fin 3, eng 𝔭.tree (slotExp u k) k (F k) Tr (qv R k) := by
    unfold convProd
    rw [ENNReal.ofReal_prod_of_nonneg fun k _ => hSk k, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hKp.le _)]
    ring
  refine h2.trans ?_
  rw [hprod]
  have hPi : 0 ≤ ∏ k : Fin 3, (cutK 𝔭 ^ (1 / 6 : ℝ) * lacSConst 𝔭 (qv R k) ((𝔭.N : ℝ) / 6)) :=
    Finset.prod_nonneg fun k _ => hSk k
  have e : ENNReal.ofReal (convConst 𝔭 R * CT) = ENNReal.ofReal (24 * bLayerConst 𝔭 * CT) *
      ENNReal.ofReal (∏ k : Fin 3, (cutK 𝔭 ^ (1 / 6 : ℝ) * lacSConst 𝔭 (qv R k) ((𝔭.N : ℝ) / 6))) := by
    unfold convConst
    rw [show 24 * bLayerConst 𝔭 * (∏ k : Fin 3, (cutK 𝔭 ^ (1 / 6 : ℝ) * lacSConst 𝔭 (qv R k) ((𝔭.N : ℝ) / 6))) * CT =
      (24 * bLayerConst 𝔭 * CT) * ∏ k : Fin 3, (cutK 𝔭 ^ (1 / 6 : ℝ) * lacSConst 𝔭 (qv R k) ((𝔭.N : ℝ) / 6)) by ring,
      ENNReal.ofReal_mul (by positivity)]
  rw [e]
  calc ENNReal.ofReal (24 * bLayerConst 𝔭 * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) *
        (ENNReal.ofReal (∏ k : Fin 3, (cutK 𝔭 ^ (1 / 6 : ℝ) * lacSConst 𝔭 (qv R k) ((𝔭.N : ℝ) / 6))) *
          ∏ k : Fin 3, eng 𝔭.tree (slotExp u k) k (F k) Tr (qv R k))
      ≤ ENNReal.ofReal (24 * bLayerConst 𝔭 * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) *
        (ENNReal.ofReal (∏ k : Fin 3, (cutK 𝔭 ^ (1 / 6 : ℝ) * lacSConst 𝔭 (qv R k) ((𝔭.N : ℝ) / 6))) *
          ∏ k : Fin 3, engV 𝔭 u R k (F k) Tr) := mul_le_mul' le_rfl (mul_le_mul' le_rfl (eng_prod_le_engV 𝔭 u R F Tr))
    _ = _ := by ring

theorem prod_fin3_eq (V : Fin 3 → ℝ≥0∞) {i j : Fin 3} (hi : i ≠ 2) (hj : j ≠ 2) (hij : i ≠ j) :
    ∏ k, V k = V i * (V j * V 2) := by
  fin_cases i <;> fin_cases j <;> simp at hi hj hij ⊢ <;> simp [Fin.prod_univ_three] <;> ring

theorem engV_ge_ne_two {P : ℕ} [NeZero P] (𝔭 : Params) (u R : ℝ) {k : Fin 3} (hk : k ≠ 2) (F : ℝ → ZMod P → ℂ)
    (Tr : Finset TriTile) :
    engTop 𝔭.tree 2 k F Tr 2 ≤ engV 𝔭 u R k F Tr ∧ eng 𝔭.tree 2 k F Tr 2 ≤ engV 𝔭 u R k F Tr := by
  have e1 : slotExp u k = 2 := by simp [slotExp, hk]
  have e2 : qv R k = 2 := by simp [qv, hk]
  unfold engV
  rw [e1, e2]
  exact ⟨le_max_right _ _, le_max_left _ _⟩

theorem engV_ge_two {P : ℕ} [NeZero P] (𝔭 : Params) (u R : ℝ) (F : ℝ → ZMod P → ℂ) (Tr : Finset TriTile) :
    eng 𝔭.tree u 2 F Tr R ≤ engV 𝔭 u R 2 F Tr := by
  have e1 : slotExp u 2 = u := by simp [slotExp]
  have e2 : qv R 2 = R := by simp [qv]
  unfold engV
  rw [e1, e2]
  exact le_max_left _ _

/-- **The hard parts, core**: `Λ_{TA} = P - ERR₂ + ERR₁ + CE`, each bounded.  The overlapping slot is `i`, the other Hilbert slot `j`,
`Tq` the form with the overlapping slot first (`hper`). -/
theorem hard_core (𝔭 : Params) (hO : OverlapPspLean 𝔭) (hND : 𝔭.N / 8 + 3 ≤ 𝔭.D) {u R : ℝ} (hu : 1 < u) (hR : 2 < R)
    (h𝔭 : 𝔭.Admissible) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (η η' : ℝ → ℝ) (Tr TA : Finset TriTile) (t : Top) (χ : TriTile → ℝ → ℝ)
      (m : TriTile → Fin 3 → ℝ → ℂ), PartData 𝔭 η η' Tr TA t χ m → ∀ (Qs : Set Box), IsRankOne 𝔭.J Qs →
      (∀ Q ∈ Tr, Q.box ∈ Qs) → ∀ (i j : Fin 3), i ≠ 2 → j ≠ 2 → (∀ R ∈ TA, IsOvSlot t i R.box) →
      (∀ R ∈ TA, ¬ IsOvSlot t j R.box) → (∀ R ∈ TA, ¬ IsOvSlot t 2 R.box) → IsLacunary j TA → IsLacunary 2 TA →
      i ≠ j → ∀ (T Tq : Form P) (CT : ℝ), FormBound u T CT → FormBound u Tq CT →
      (∀ a : Fin 3 → ZMod P → ℂ, T (a 0) (a 1) (a 2) = Tq (a i) (a j) (a 2)) →
      ∀ F : Fin 3 → ℝ → ZMod P → ℂ, (∀ k, Measurable (F k)) → (∀ k, ∃ B, ∀ x, yNorm 2 (F k x) ≤ B) →
        ‖modelForm T TA χ m (F 0) (F 1) (F 2)‖ₑ ≤ ENNReal.ofReal (C * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) *
          (engV 𝔭 u R i (F i) Tr * (engV 𝔭 u R j (F j) Tr * engV 𝔭 u R 2 (F 2) Tr)) := by
  obtain ⟨Cm, hCm0, hMain⟩ := main_term_exists h𝔭 hu hR
  obtain ⟨CO, hCO0, hO'⟩ := hO hND
  set Ca : ℝ := ((2 : ℝ) ^ (2 : ℝ) * jbConst 2) * ((24 / 99) * muConst) with hCa
  have hCa0 : 0 ≤ Ca := by
    have := jbConst_nonneg 2; have := muConst_pos
    positivity
  refine ⟨Cm * CO + |err2Const 𝔭 R| * CO + |err1Const 𝔭 CO Ca| + |convConst 𝔭 R|, by positivity, ?_⟩
  intro P _ η η' Tr TA t χ m pd Qs hQ hbox' i j hi hj hov hlacj hlac2 hILj hIL2 hij T Tq CT hT hTq hper F hF hFb
  have hCT : 0 ≤ CT := nonneg_of_formBound (by linarith) hT
  have hbox : ∀ R ∈ TA, R.box ∈ Qs := fun R hR => hbox' R (pd.sub hR)
  by_cases hne : TA.Nonempty
  swap
  · have : TA = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
    subst this; simp [modelForm]
  obtain ⟨R₂, hR₂⟩ := hne
  have hex : ∀ σ ∈ treeScales TA, ∃ R₁ : TriTile, R₁ ∈ layer' TA σ := fun σ hσ => by
    obtain ⟨R₁, hR₁, hs⟩ := mem_treeScales_iff.1 hσ
    exact ⟨R₁, mem_layer'_iff.2 ⟨hR₁, hs⟩⟩
  let R₀ : ℤ → TriTile := fun σ => if h : σ ∈ treeScales TA then (hex σ h).choose else R₂
  have hR₀ : ∀ σ ∈ treeScales TA, R₀ σ ∈ layer' TA σ := fun σ hσ => by
    simp only [R₀, dite_eq_left hσ]; exact (hex σ hσ).choose_spec
  have hFc : ∀ k, IsBddC (F k) := fun k => isBddC_of_hFb (hF k) (hFb k)
  obtain ⟨G, hGm, hGb, ⟨hO1, hGs⟩, hO2⟩ := hO' P Qs Tr TA t i η χ m hi h𝔭 pd.h𝔭t pd.hη ⟨η', pd.hη'⟩ hQ pd.sub hbox'
    pd.good hov (pd.lacData i) (F i) (hF i) (hFb i)
  set Eo := engTop 𝔭.tree 2 i (F i) Tr 2 with hEo
  set Eh := eng 𝔭.tree 2 j (F j) Tr 2 with hEh
  set Ew := eng 𝔭.tree u 2 (F 2) Tr R with hEw
  set MG : ℝ≥0∞ := ENNReal.ofReal CO * Eo with hMG
  have hGc : IsBddC G := isBddC_of_hFb hGm hGb
  rw [modelForm_eq_cubic_add_conv pd hFc R₀ hR₀]
  have hcub : (∑ σ ∈ treeScales TA, ∫ x, T ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) 0) (F 0) x)
          ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) 1) (F 1) x) ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) 2) (F 2) x)) =
      ∑ σ ∈ treeScales TA, ∫ x, Tq ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) i) (F i) x)
          ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) j) (F j) x) ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) 2) (F 2) x) := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact hper (fun k => (layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) k) (F k) x)
  rw [hcub, cubic_split pd (Tq := Tq) (hFc i) (hFc j) (hFc 2) hGc R₀ hR₀]
  -- the main term
  have hMGb : ∀ x, ENNReal.ofReal (yNorm 2 (G x)) ≤ MG := hO1
  have bP := hMain P η η' Tr TA t χ m pd Qs hQ hbox i j hi hj hov hlacj hlac2 hILj hIL2 Tq CT hTq (F j) (F 2) G (hF j)
    (hFb j) (hF 2) (hFb 2) hGm hGb hGs MG hMGb R₀ hR₀
  have bE2 := err2_bound pd hu hR hTq (i := i) (j := j) (hF j) (hFb j) (hF 2) (hFb 2) hGm hMGb R₀ hR₀
  -- the lattice window
  set s₀ : ℤ := R₂.box.scale with hs₀
  set lo : ℤ := -((TA.sup (fun R => R.box.scale.natAbs) : ℕ) : ℤ) - 1 with hlo
  set S : Finset ℤ := ovScales 𝔭.J s₀ lo t.1.1 with hS
  have hlat : ∀ σ ∈ treeScales TA, (𝔭.J : ℤ) ∣ σ - s₀ := by
    intro σ hσ
    obtain ⟨R', hR', hRs⟩ := mem_treeScales_iff.1 hσ
    have := hQ.1 R'.box (hbox R' hR') R₂.box (hbox R₂ hR₂)
    rw [← hRs]; exact this
  have hSlat : ∀ σ' ∈ S, (𝔭.J : ℤ) ∣ σ' - s₀ := fun σ' hσ' => (Finset.mem_filter.1 hσ').2
  have hTS : treeScales TA ⊆ S := by
    intro σ hσ
    obtain ⟨R', hR', hRs⟩ := mem_treeScales_iff.1 hσ
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨?_, ?_⟩, hlat σ hσ⟩
    · have h5 : (R'.box.scale.natAbs : ℕ) ≤ TA.sup (fun R => R.box.scale.natAbs) :=
        Finset.le_sup (f := fun R : TriTile => R.box.scale.natAbs) hR'
      have h6 : -R'.box.scale ≤ (R'.box.scale.natAbs : ℤ) := by omega
      have h7 : (R'.box.scale.natAbs : ℤ) ≤ ((TA.sup (fun R => R.box.scale.natAbs) : ℕ) : ℤ) := by exact_mod_cast h5
      omega
    · have := scale_le_of_dyadicInt_subset (pd.good.1 R' hR').1
      omega
  have hO2' : ∀ σ ∈ treeScales TA, ∀ v : ℤ, OvBound 2 2 CO (ovFactor 𝔭.J S (bdryEnds TA t.1) σ v) Eo σ v
      (fun x => (layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) i) (F i - G) x) := by
    intro σ hσ v
    refine hO2 σ (R₀ σ) (hR₀ σ hσ) v S (fun σ' hσ' => ?_) (fun σ' hσ' hne => ?_)
    · have := dvd_sub (hSlat σ' hσ') (hlat σ hσ)
      rwa [show σ' - s₀ - (σ - s₀) = σ' - σ by ring] at this
    · have h1 : (𝔭.J : ℤ) ∣ σ' - s₀ := by
        have := dvd_add hσ' (hlat σ hσ)
        rwa [show σ' - σ + (σ - s₀) = σ' - s₀ by ring] at this
      obtain ⟨hw1, hw2⟩ := bdryEnds_window hne
      exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hw1, hw2⟩, h1⟩
  have hsum := sum_a_le (by have := h𝔭.1; unfold jFloor at this; omega : 0 < 𝔭.J) hSlat (bdryEnds TA t.1) hTS TA t.1 rfl
  have bE1 := err1_bound pd hu hR hTq (i := i) (j := j) (hF i) (hF j) (hF 2) hGm R₀ hR₀ hCO0
    (fun σ v => ovFactor 𝔭.J S (bdryEnds TA t.1) σ v) (fun σ v => ovFactor_nonneg _ _ _ σ v) hO2' hCa0
    (by refine hsum.trans (le_of_eq ?_); rw [hCa]; congr 1; ring)
  have bCE := conv_bound pd hu hR hT hF hFb R₀ hR₀
  have key : ∀ (a b c d : ℂ) (X1 X2 X3 X4 : ℝ≥0∞), ‖a‖ₑ ≤ X1 → ‖b‖ₑ ≤ X2 → ‖c‖ₑ ≤ X3 → ‖d‖ₑ ≤ X4 →
      ‖(a - b + c) + d‖ₑ ≤ X1 + X2 + X3 + X4 := by
    intro a b c d X1 X2 X3 X4 h1 h2 h3 h4
    calc ‖(a - b + c) + d‖ₑ ≤ ‖a - b + c‖ₑ + ‖d‖ₑ := enorm_add_le _ _
      _ ≤ (‖a - b‖ₑ + ‖c‖ₑ) + ‖d‖ₑ := add_le_add (enorm_add_le _ _) le_rfl
      _ ≤ ((‖a‖ₑ + ‖b‖ₑ) + ‖c‖ₑ) + ‖d‖ₑ := add_le_add (add_le_add enorm_sub_le le_rfl) le_rfl
      _ ≤ X1 + X2 + X3 + X4 := add_le_add (add_le_add (add_le_add h1 h2) h3) h4
  -- comparison with the `engV` product
  obtain ⟨hVi, -⟩ := engV_ge_ne_two 𝔭 u R hi (F i) Tr
  obtain ⟨-, hVj⟩ := engV_ge_ne_two 𝔭 u R hj (F j) Tr
  have hVw := engV_ge_two 𝔭 u R (F 2) Tr
  set Vi := engV 𝔭 u R i (F i) Tr
  set Vj := engV 𝔭 u R j (F j) Tr
  set Vw := engV 𝔭 u R 2 (F 2) Tr
  have hprod := prod_fin3_eq (fun k => engV 𝔭 u R k (F k) Tr) hi hj hij
  have hW : Eo * (Eh * Ew) ≤ Vi * (Vj * Vw) := mul_le_mul' hVi (mul_le_mul' hVj hVw)
  set H : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ t.1.1) with hH
  have hMGW : MG * (Eh * Ew) ≤ ENNReal.ofReal CO * (Vi * (Vj * Vw)) := by
    rw [hMG, mul_assoc]; exact mul_le_mul' le_rfl hW
  have hCm := hCm0
  have e1 : ENNReal.ofReal (Cm * CT) * H * (MG * (Eh * Ew)) ≤
      ENNReal.ofReal (Cm * CO * CT) * H * (Vi * (Vj * Vw)) := by
    calc _ ≤ ENNReal.ofReal (Cm * CT) * H * (ENNReal.ofReal CO * (Vi * (Vj * Vw))) := mul_le_mul' le_rfl hMGW
      _ = _ := by
          rw [show Cm * CO * CT = (Cm * CT) * CO by ring, ENNReal.ofReal_mul (p := Cm * CT) (q := CO) (by positivity)]; ring
  have e2 : ENNReal.ofReal (err2Const 𝔭 R * CT) * H * (MG * (Eh * Ew)) ≤
      ENNReal.ofReal (|err2Const 𝔭 R| * CO * CT) * H * (Vi * (Vj * Vw)) := by
    calc _ ≤ ENNReal.ofReal (|err2Const 𝔭 R| * CT) * H * (ENNReal.ofReal CO * (Vi * (Vj * Vw))) :=
          mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) hCT)) le_rfl) hMGW
      _ = _ := by
          rw [show |err2Const 𝔭 R| * CO * CT = (|err2Const 𝔭 R| * CT) * CO by ring,
            ENNReal.ofReal_mul (p := |err2Const 𝔭 R| * CT) (q := CO) (by positivity)]; ring
  have e3 : ENNReal.ofReal (err1Const 𝔭 CO Ca * CT) * H * (Eo * (Eh * Ew)) ≤
      ENNReal.ofReal (|err1Const 𝔭 CO Ca| * CT) * H * (Vi * (Vj * Vw)) :=
    mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) hCT)) le_rfl) hW
  have e4 : ENNReal.ofReal (convConst 𝔭 R * CT) * H * ∏ k : Fin 3, engV 𝔭 u R k (F k) Tr ≤
      ENNReal.ofReal (|convConst 𝔭 R| * CT) * H * (Vi * (Vj * Vw)) := by
    rw [hprod]
    exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) hCT)) le_rfl) le_rfl
  have hn1 : 0 ≤ Cm * CO * CT := by positivity
  have hn2 : 0 ≤ |err2Const 𝔭 R| * CO * CT := by positivity
  have hn3 : 0 ≤ |err1Const 𝔭 CO Ca| * CT := by positivity
  have hn4 : 0 ≤ |convConst 𝔭 R| * CT := by positivity
  refine (key _ _ _ _ _ _ _ _ (bP.trans e1) (bE2.trans e2) (bE1.trans e3) (bCE.trans e4)).trans (le_of_eq ?_)
  rw [show (Cm * CO + |err2Const 𝔭 R| * CO + |err1Const 𝔭 CO Ca| + |convConst 𝔭 R|) * CT =
    Cm * CO * CT + |err2Const 𝔭 R| * CO * CT + |err1Const 𝔭 CO Ca| * CT + |convConst 𝔭 R| * CT by ring,
    ENNReal.ofReal_add (by positivity) hn4, ENNReal.ofReal_add (by positivity) hn3, ENNReal.ofReal_add hn1 hn2]
  ring

/-- One hard part from the core, with the overlapping slot `i ∉ A` and the lacunary slots `j, 2 ∈ A`. -/
theorem hard_from_core {𝔭 : Params} {u R C : ℝ} (_hu : 1 < u)
    (hC : ∀ (P : ℕ) [NeZero P] (η η' : ℝ → ℝ) (Tr TA : Finset TriTile) (t : Top) (χ : TriTile → ℝ → ℝ)
      (m : TriTile → Fin 3 → ℝ → ℂ), PartData 𝔭 η η' Tr TA t χ m → ∀ (Qs : Set Box), IsRankOne 𝔭.J Qs →
      (∀ Q ∈ Tr, Q.box ∈ Qs) → ∀ (i j : Fin 3), i ≠ 2 → j ≠ 2 → (∀ R ∈ TA, IsOvSlot t i R.box) →
      (∀ R ∈ TA, ¬ IsOvSlot t j R.box) → (∀ R ∈ TA, ¬ IsOvSlot t 2 R.box) → IsLacunary j TA → IsLacunary 2 TA →
      i ≠ j → ∀ (T Tq : Form P) (CT : ℝ), FormBound u T CT → FormBound u Tq CT →
      (∀ a : Fin 3 → ZMod P → ℂ, T (a 0) (a 1) (a 2) = Tq (a i) (a j) (a 2)) →
      ∀ F : Fin 3 → ℝ → ZMod P → ℂ, (∀ k, Measurable (F k)) → (∀ k, ∃ B, ∀ x, yNorm 2 (F k x) ≤ B) →
        ‖modelForm T TA χ m (F 0) (F 1) (F 2)‖ₑ ≤ ENNReal.ofReal (C * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) *
          (engV 𝔭 u R i (F i) Tr * (engV 𝔭 u R j (F j) Tr * engV 𝔭 u R 2 (F 2) Tr)))
    (h𝔭 : 𝔭.Admissible) {P : ℕ} [NeZero P] (T Tq : Form P) {CT : ℝ} (hT : FormBound u T CT) (hTq : FormBound u Tq CT)
    {Qs : Set Box} (hQ : IsRankOne 𝔭.J Qs) {Tr : Finset TriTile} {t : Top} {η η' : ℝ → ℝ} {χ : TriTile → ℝ → ℝ}
    {m : TriTile → Fin 3 → ℝ → ℂ} (A : Finset (Fin 3)) (i j : Fin 3) (hi : i ≠ 2) (hj : j ≠ 2) (hij : i ≠ j)
    (hiA : i ∉ A) (hjA : j ∈ A) (h2A : 2 ∈ A) (hbox' : ∀ Q ∈ Tr, Q.box ∈ Qs)
    (pd : PartData 𝔭 η η' Tr (treePart Tr t A) t χ m)
    (hper : ∀ a : Fin 3 → ZMod P → ℂ, T (a 0) (a 1) (a 2) = Tq (a i) (a j) (a 2))
    {F : Fin 3 → ℝ → ZMod P → ℂ} (hF : ∀ k, Measurable (F k)) (hFb : ∀ k, ∃ B, ∀ x, yNorm 2 (F k x) ≤ B) :
    ‖modelForm T (treePart Tr t A) χ m (F 0) (F 1) (F 2)‖ₑ ≤ ENNReal.ofReal (C * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) *
      (engV 𝔭 u R i (F i) Tr * (engV 𝔭 u R j (F j) Tr * engV 𝔭 u R 2 (F 2) Tr)) := by
  have hbT : ∀ R ∈ treePart Tr t A, R.box ∈ Qs := fun R hR => hbox' R (mem_treePart.1 hR).1
  have hov : ∀ R ∈ treePart Tr t A, IsOvSlot t i R.box := by
    intro R hR
    have := (mem_treePart.1 hR).2
    by_contra h
    have : i ∈ slotType t R.box := mem_slotType.2 h
    rw [(mem_treePart.1 hR).2] at this
    exact hiA this
  have hIL : ∀ k ∈ A, IsLacunary k (treePart Tr t A) := fun k hk => by
    have := isLacunary_treePart (J := 𝔭.J) h𝔭.1 hQ pd.good.1 hbT hk
    rwa [treePart_idem] at this
  exact hC P η η' Tr (treePart Tr t A) t χ m pd Qs hQ hbox' i j hi hj hov (fun R hR => not_isOvSlot_of_mem_treePart hjA hR)
    (fun R hR => not_isOvSlot_of_mem_treePart h2A hR) (hIL j hjA) (hIL 2 h2A) hij T Tq CT hT hTq hper F hF hFb

/-- **`HardPartStatement` from `OverlapPspLean`.** -/
theorem hardPart_of_overlapPspLean (hO : ∀ 𝔭 : Params, 𝔭.Admissible → 𝔭.tree.Admissible → OverlapPspLean 𝔭) :
    HardPartStatement := by
  intro 𝔭 h𝔭 h𝔭t hprof u R hu hR
  obtain ⟨C, hC0, hC⟩ := hard_core 𝔭 (hO 𝔭 h𝔭 h𝔭t) hprof.2 hu hR h𝔭
  refine ⟨C, hC0, ?_⟩
  intro P _ T CT hT Qs hQ Tr t η η' χ m A hA hbox' pd F hF hFb
  rcases hA with rfl | rfl
  · have h := hard_from_core hu hC h𝔭 T T hT hT hQ ({1, 2} : Finset (Fin 3)) 0 1 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hbox' pd (fun a => rfl) hF hFb
    refine h.trans (le_of_eq ?_)
    rw [Fin.prod_univ_three]; ring
  · have h := hard_from_core hu hC h𝔭 T T.swap12 hT hT.swap12 hQ ({0, 2} : Finset (Fin 3)) 1 0 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hbox' pd (fun a => rfl) hF hFb
    refine h.trans (le_of_eq ?_)
    rw [Fin.prod_univ_three]; ring

/-- **V15 from `OverlapPspLean`.** -/
theorem treeLemmaRev2_of_overlapPspLean
    (hO : ∀ 𝔭 : Params, 𝔭.Admissible → 𝔭.tree.Admissible → OverlapPspLean 𝔭) : TreeLemmaStatementRev2 :=
  treeLemmaRev2_of_hardParts (hardPart_of_overlapPspLean hO)

end Glue

end PrimeBHT.TimeFrequency.X2
