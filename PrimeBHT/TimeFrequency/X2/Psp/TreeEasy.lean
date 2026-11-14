module

public import PrimeBHT.TimeFrequency.X2.Psp.TreeMain

/-!
# X2, V15 (assembly), step 5: the parts with both Hilbert slots lacunary (`A ⊇ {0, 1}`)

(Route check §4 step 3, cases `B = ∅` and `B = {3}`; **no overlapping projection is needed here**: the single-scale sup bound
(L3) holds for a slot of ANY type, so the third slot is bounded by `sup_{σ,x} ‖χ̃_σ T_{m_σ 2} F₂‖_{L^u(Y)} ≤ C eng`, and the two
Hilbert slots are lacunary: Plancherel (L4) and the definition of the energy (L1).)

* `cubic_main_easy`: `‖Σ_σ ∫ Π(ℓ₀σ, ℓ₁σ, ℓ₂σ)‖ ≤ CT · C_{L3} E₂ · (|I_t|^{1/2} E₀)(|I_t|^{1/2} E₁)`;
* `part_easy`: with the conversion error (`conv_error`), `‖Λ_{TA}‖ ≤ C CT |I_t| ∏_k E_k`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

section Easy

variable {P : ℕ} [NeZero P] {𝔭 : Params} {η η' : ℝ → ℝ} {Tr TA : Finset TriTile} {t : Top} {χ : TriTile → ℝ → ℝ}
  {m : TriTile → Fin 3 → ℝ → ℂ}

theorem cubic_main_easy (pd : PartData 𝔭 η η' Tr TA t χ m) {Qs : Set Box} (hQ : IsRankOne 𝔭.J Qs)
    (hbox : ∀ R ∈ TA, R.box ∈ Qs) (hlac₀ : ∀ R ∈ TA, ¬ IsOvSlot t 0 R.box) (hlac₁ : ∀ R ∈ TA, ¬ IsOvSlot t 1 R.box)
    (hIL₀ : IsLacunary 0 TA) (hIL₁ : IsLacunary 1 TA) {u R : ℝ} (hu : 1 < u) (hR : 2 < R) {T : Form P} {CT : ℝ}
    (hT : FormBound u T CT) {F : Fin 3 → ℝ → ZMod P → ℂ} (hF : ∀ k, Measurable (F k))
    (hFb : ∀ k, ∃ B, ∀ x, yNorm 2 (F k x) ≤ B) (R₀ : ℤ → TriTile) (hR₀ : ∀ σ ∈ treeScales TA, R₀ σ ∈ layer' TA σ) :
    ‖∑ σ ∈ treeScales TA, ∫ x, T ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) 0) (F 0) x)
          ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) 1) (F 1) x) ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) 2) (F 2) x)‖ₑ ≤
      ENNReal.ofReal CT * (ENNReal.ofReal (lacL3Const 𝔭 R) * eng 𝔭.tree u 2 (F 2) Tr R) *
        ((ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (1 / 2 : ℝ)) * eng 𝔭.tree 2 0 (F 0) Tr 2) *
          (ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (1 / 2 : ℝ)) * eng 𝔭.tree 2 1 (F 1) Tr 2)) := by
  have hCT : 0 ≤ CT := nonneg_of_formBound (by linarith) hT
  set S := treeScales TA with hS
  set ℓ : Fin 3 → ℤ → ℝ → ZMod P → ℂ := fun k σ x => (layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) k) (F k) x with hℓ
  set u₀ : ℤ → ℝ → ℝ≥0∞ := fun σ x => ENNReal.ofReal (yNorm 2 (ℓ 0 σ x)) with hu₀
  set u₁ : ℤ → ℝ → ℝ≥0∞ := fun σ x => ENNReal.ofReal (yNorm 2 (ℓ 1 σ x)) with hu₁
  set v : ℤ → ℝ → ℝ≥0∞ := fun σ x => ENNReal.ofReal (yNorm u (ℓ 2 σ x)) with hv
  have hmeas : ∀ k : Fin 3, ∀ σ ∈ S, Measurable (ℓ k σ) := fun k σ hσ => measurable_layer_vec pd (hF k) (hR₀ σ hσ)
  have hm₀ : ∀ σ ∈ S, Measurable (u₀ σ) := fun σ hσ =>
    ENNReal.measurable_ofReal.comp ((measurable_yNorm_fun 2).comp (hmeas 0 σ hσ))
  have hm₁ : ∀ σ ∈ S, Measurable (u₁ σ) := fun σ hσ =>
    ENNReal.measurable_ofReal.comp ((measurable_yNorm_fun 2).comp (hmeas 1 σ hσ))
  have hm₂ : ∀ σ ∈ S, Measurable (v σ) := fun σ hσ =>
    ENNReal.measurable_ofReal.comp ((measurable_yNorm_fun u).comp (hmeas 2 σ hσ))
  -- the sup bound (L3) for slot 2
  have hvM : ∀ σ ∈ S, ∀ x, v σ x ≤ ENNReal.ofReal (lacL3Const 𝔭 R) * eng 𝔭.tree u 2 (F 2) Tr R := fun σ hσ x =>
    lacunary_L3 (by linarith) (by linarith) pd.h𝔭 pd.h𝔭t pd.hη' pd.hη pd.good pd.sub (pd.lacData 2) (hF 2) (hFb 2)
      (hR₀ σ hσ) x
  -- the `L²` bounds (L1 + L4) for slots 0, 1
  have hA₀ := lac_sq_bound pd hQ hbox hlac₀ hIL₀ (hF 0) (hFb 0) R₀ hR₀
  have hA₁ := lac_sq_bound pd hQ hbox hlac₁ hIL₁ (hF 1) (hFb 1) R₀ hR₀
  have hcs := cs_sum (S := S) (u₀ := u₀) (u₁ := u₁) (v := v) hm₀ hm₁ hvM hA₀ hA₁
  -- pointwise
  have hpt : ∀ σ x, ‖T (ℓ 0 σ x) (ℓ 1 σ x) (ℓ 2 σ x)‖ₑ ≤ ENNReal.ofReal CT * (u₀ σ x * u₁ σ x * v σ x) := by
    intro σ x
    rw [← ofReal_norm]
    have := hT (ℓ 0 σ x) (ℓ 1 σ x) (ℓ 2 σ x)
    refine (ENNReal.ofReal_le_ofReal this).trans (le_of_eq ?_)
    have h0 := yNorm_nonneg' 2 (ℓ 0 σ x)
    have h1 := yNorm_nonneg' 2 (ℓ 1 σ x)
    have h2 := yNorm_nonneg' u (ℓ 2 σ x)
    simp only [hu₀, hu₁, hv]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hCT]
    ring
  calc ‖∑ σ ∈ S, ∫ x, T (ℓ 0 σ x) (ℓ 1 σ x) (ℓ 2 σ x)‖ₑ
      ≤ ∑ σ ∈ S, ‖∫ x, T (ℓ 0 σ x) (ℓ 1 σ x) (ℓ 2 σ x)‖ₑ := enorm_sum_le _ _
    _ ≤ ∑ σ ∈ S, ∫⁻ x, ‖T (ℓ 0 σ x) (ℓ 1 σ x) (ℓ 2 σ x)‖ₑ :=
        Finset.sum_le_sum fun σ _ => enorm_integral_le_lintegral_enorm _
    _ ≤ ∑ σ ∈ S, ∫⁻ x, ENNReal.ofReal CT * (u₀ σ x * u₁ σ x * v σ x) :=
        Finset.sum_le_sum fun σ _ => lintegral_mono fun x => hpt σ x
    _ = ENNReal.ofReal CT * ∑ σ ∈ S, ∫⁻ x, u₀ σ x * u₁ σ x * v σ x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ hσ => ?_
        exact lintegral_const_mul (μ := volume) _ (((hm₀ σ hσ).mul (hm₁ σ hσ)).mul (hm₂ σ hσ))
    _ ≤ ENNReal.ofReal CT * (ENNReal.ofReal (lacL3Const 𝔭 R) * eng 𝔭.tree u 2 (F 2) Tr R *
          ((ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (1 / 2 : ℝ)) * eng 𝔭.tree 2 0 (F 0) Tr 2) *
            (ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (1 / 2 : ℝ)) * eng 𝔭.tree 2 1 (F 1) Tr 2))) :=
        mul_le_mul' le_rfl hcs
    _ = _ := by ring

theorem lacSConst_nonneg {𝔭 : Params} (h𝔭t : 𝔭.tree.Admissible) {q : ℝ} (hq : 1 < q) (Nw : ℝ) :
    0 ≤ lacSConst 𝔭 q Nw := by
  obtain ⟨hNt, hDt, hβt, hCt⟩ := h𝔭t.bounds
  have hδ := h𝔭t.2.2.2.1
  have hts := tileSupConst_nonneg 𝔭.tree hq (by linarith)
  have hjb := jbConst_nonneg (Nw - (𝔭.tree.N : ℝ))
  have hD : 0 < 𝔭.tree.C * ((3 : ℝ) / 2) ^ (2 * (𝔭.tree.N : ℝ)) := by
    have : (0 : ℝ) < 𝔭.tree.C := by linarith
    positivity
  unfold lacSConst
  have : 0 ≤ 𝔭.tree.C * ((3 : ℝ) / 2) ^ (2 * (𝔭.tree.N : ℝ)) * tileSupConst 𝔭.tree q *
      (2 ^ (Nw - (𝔭.tree.N : ℝ)) * jbConst (Nw - (𝔭.tree.N : ℝ))) := by positivity
  linarith

theorem lacL3Const_nonneg {𝔭 : Params} (h𝔭 : 𝔭.Admissible) (h𝔭t : 𝔭.tree.Admissible) {q : ℝ} (hq : 1 < q) :
    0 ≤ lacL3Const 𝔭 q := by
  obtain ⟨hN, hD, hβ, hC⟩ := h𝔭.bounds
  obtain ⟨hNt, hDt, hβt, hCt⟩ := h𝔭t.bounds
  have hδ := h𝔭t.2.2.2.1
  have hts := tileSupConst_nonneg 𝔭.tree hq (by linarith)
  have hjb := jbConst_nonneg ((𝔭.N : ℝ) / 2)
  have hK := cutK_pos (by linarith : 0 < 𝔭.C)
  have hD : 0 < 𝔭.tree.C * ((3 : ℝ) / 2) ^ (2 * (𝔭.tree.N : ℝ)) := by
    have : (0 : ℝ) < 𝔭.tree.C := by linarith
    positivity
  unfold lacL3Const
  have : 0 ≤ cutK 𝔭 * (𝔭.tree.C * ((3 : ℝ) / 2) ^ (2 * (𝔭.tree.N : ℝ))) * tileSupConst 𝔭.tree q *
      (2 ^ ((𝔭.N : ℝ) / 2) * jbConst ((𝔭.N : ℝ) / 2)) := by positivity
  linarith

/-- The constant of the parts with both Hilbert slots lacunary. -/
def easyConst (𝔭 : Params) (_u R : ℝ) : ℝ :=
  lacL3Const 𝔭 R + 24 * bLayerConst 𝔭 *
    ∏ k : Fin 3, (cutK 𝔭 ^ (1 / 6 : ℝ) * lacSConst 𝔭 (qv R k) ((𝔭.N : ℝ) / 6))

/-- **The parts with `A ⊇ {0, 1}`**: `‖Λ_{TA}‖ ≤ C CT |I_t| ∏_k eng_k`. -/
theorem part_easy (pd : PartData 𝔭 η η' Tr TA t χ m) {Qs : Set Box} (hQ : IsRankOne 𝔭.J Qs)
    (hbox : ∀ R ∈ TA, R.box ∈ Qs) (hlac₀ : ∀ R ∈ TA, ¬ IsOvSlot t 0 R.box) (hlac₁ : ∀ R ∈ TA, ¬ IsOvSlot t 1 R.box)
    (hIL₀ : IsLacunary 0 TA) (hIL₁ : IsLacunary 1 TA) {u R : ℝ} (hu : 1 < u) (hR : 2 < R) {T : Form P} {CT : ℝ}
    (hT : FormBound u T CT) {F : Fin 3 → ℝ → ZMod P → ℂ} (hF : ∀ k, Measurable (F k))
    (hFb : ∀ k, ∃ B, ∀ x, yNorm 2 (F k x) ≤ B) :
    ‖modelForm T TA χ m (F 0) (F 1) (F 2)‖ₑ ≤
      ENNReal.ofReal (easyConst 𝔭 u R * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) *
        ∏ k : Fin 3, eng 𝔭.tree (slotExp u k) k (F k) Tr (qv R k) := by
  have hCT : 0 ≤ CT := nonneg_of_formBound (by linarith) hT
  -- representatives of the layers
  have hex : ∀ σ ∈ treeScales TA, ∃ R₁ : TriTile, R₁ ∈ layer' TA σ := fun σ hσ => by
    obtain ⟨R₁, hR₁, hs⟩ := mem_treeScales_iff.1 hσ
    exact ⟨R₁, mem_layer'_iff.2 ⟨hR₁, hs⟩⟩
  by_cases hne : TA.Nonempty
  swap
  · have : TA = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
    subst this
    simp [modelForm]
  obtain ⟨R₂, hR₂⟩ := hne
  let R₀ : ℤ → TriTile := fun σ => if h : σ ∈ treeScales TA then (hex σ h).choose else R₂
  have hR₀ : ∀ σ ∈ treeScales TA, R₀ σ ∈ layer' TA σ := fun σ hσ => by
    simp only [R₀, dite_eq_left hσ]; exact (hex σ hσ).choose_spec
  have hFc : ∀ k, IsBddC (F k) := fun k => isBddC_of_hFb (hF k) (hFb k)
  rw [modelForm_eq_cubic_add_conv pd hFc R₀ hR₀]
  refine (enorm_add_le _ _).trans ?_
  have h1 := cubic_main_easy pd hQ hbox hlac₀ hlac₁ hIL₀ hIL₁ hu hR hT hF hFb R₀ hR₀
  have h2 := conv_error pd hu hR hT hF hFb R₀ hR₀
  have hL3 := lacL3Const_nonneg pd.h𝔭 pd.h𝔭t (by linarith : 1 < R)
  have hbc := bLayerConst_nonneg pd.hη (by obtain ⟨hN, -, -, -⟩ := pd.h𝔭.bounds; omega : 5 ≤ 𝔭.N)
  have hKp : 0 < cutK 𝔭 := cutK_pos (by obtain ⟨-, -, -, hC⟩ := pd.h𝔭.bounds; linarith)
  have hSk : ∀ k : Fin 3, 0 ≤ cutK 𝔭 ^ (1 / 6 : ℝ) * lacSConst 𝔭 (qv R k) ((𝔭.N : ℝ) / 6) := fun k =>
    mul_nonneg (Real.rpow_nonneg hKp.le _) (lacSConst_nonneg pd.h𝔭t (qv_gt_one hR k) _)
  have hPi : ENNReal.ofReal (∏ k : Fin 3, (cutK 𝔭 ^ (1 / 6 : ℝ) * lacSConst 𝔭 (qv R k) ((𝔭.N : ℝ) / 6))) =
      ∏ k : Fin 3, (ENNReal.ofReal (cutK 𝔭 ^ (1 / 6 : ℝ)) *
        ENNReal.ofReal (lacSConst 𝔭 (qv R k) ((𝔭.N : ℝ) / 6))) := by
    rw [ENNReal.ofReal_prod_of_nonneg fun k _ => hSk k]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hKp.le _)]
  have hc1 : ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (1 / 2 : ℝ)) * ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (1 / 2 : ℝ)) =
      ENNReal.ofReal ((2 : ℝ) ^ t.1.1) := by
    have hp := zpow_two_pos t.1.1
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hp.le _), ← Real.rpow_add hp]
    norm_num
  have e0 : slotExp u 0 = 2 := by simp [slotExp]
  have e1 : slotExp u 1 = 2 := by simp [slotExp]
  have e2 : slotExp u 2 = u := by simp [slotExp]
  have q0 : qv R 0 = 2 := by simp [qv]
  have q1 : qv R 1 = 2 := by simp [qv]
  have q2 : qv R 2 = R := by simp [qv]
  rw [Fin.prod_univ_three, e0, e1, e2, q0, q1, q2]
  rw [convProd, Fin.prod_univ_three, e0, e1, e2, q0, q1, q2] at h2
  set E₀ := eng 𝔭.tree 2 0 (F 0) Tr 2
  set E₁ := eng 𝔭.tree 2 1 (F 1) Tr 2
  set E₂ := eng 𝔭.tree u 2 (F 2) Tr R
  have hcubic : ‖∑ σ ∈ treeScales TA, ∫ x, T ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) 0) (F 0) x)
          ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) 1) (F 1) x) ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) 2) (F 2) x)‖ₑ ≤
      ENNReal.ofReal (lacL3Const 𝔭 R * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) * (E₀ * E₁ * E₂) := by
    refine h1.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hL3, ← hc1]
    ring
  have hconv := h2
  set PiR : ℝ := ∏ k : Fin 3, (cutK 𝔭 ^ (1 / 6 : ℝ) * lacSConst 𝔭 (qv R k) ((𝔭.N : ℝ) / 6)) with hPiR
  have hPi3 := hPi
  rw [Fin.prod_univ_three, q0, q1, q2] at hPi3
  have hPiR0 : 0 ≤ PiR := Finset.prod_nonneg fun k _ => hSk k
  have hconv' : ‖∑ σ ∈ treeScales TA, ∫ x, ((layerCut η TA σ x - layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
        T (tmult (m (R₀ σ) 0) (F 0) x) (tmult (m (R₀ σ) 1) (F 1) x) (tmult (m (R₀ σ) 2) (F 2) x)‖ₑ ≤
      ENNReal.ofReal (24 * bLayerConst 𝔭 * CT * PiR) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) * (E₀ * E₁ * E₂) := by
    refine hconv.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 24 * bLayerConst 𝔭 * CT), hPi3]
    ring
  have hfin : ENNReal.ofReal (easyConst 𝔭 u R * CT) = ENNReal.ofReal (lacL3Const 𝔭 R * CT) +
      ENNReal.ofReal (24 * bLayerConst 𝔭 * CT * PiR) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    unfold easyConst
    rw [← hPiR]
    ring
  calc _ ≤ _ := add_le_add hcubic hconv'
    _ = _ := by rw [hfin]; ring

end Easy

end PrimeBHT.TimeFrequency.X2
