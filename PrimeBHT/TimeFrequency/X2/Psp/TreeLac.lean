module

public import PrimeBHT.TimeFrequency.X2.Psp.TreeCS
import Mathlib.Algebra.Order.Chebyshev

/-!
# X2, V15 (assembly), step 3b: the lacunary slots

For a part `TA` of a tree and a lacunary slot `k`: the layer functions `ℓ_{kσ} = χ̃_σ T_{m_σ k} F_k` (= `T_{lacSym σ} G_k`, L2) satisfy

* `lac_sup_bound` (L3): `‖ℓ_{kσ}(x)‖_{L^s(Y)} ≤ C eng`;
* `lac_sq_bound` (L1 + L4, `s = q = 2`): `Σ_σ ∫ ‖ℓ_{kσ}‖² ≤ |I_t| eng²`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

section Basic

variable {P : ℕ} [NeZero P]

theorem isBddC_of_hFb {F : ℝ → ZMod P → ℂ} (hF : Measurable F) (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) : IsBddC F := by
  obtain ⟨B, hB⟩ := hFb
  refine isBddC_of_measurable hF (M := (P : ℝ) ^ (2 : ℝ)⁻¹ * B) fun x y => ?_
  exact (norm_apply_le_rpow_mul_yNorm (by norm_num) (F x) y).trans
    (mul_le_mul_of_nonneg_left (hB x) (by positivity))

omit [NeZero P] in
theorem Form_smul3 (T : Form P) (c : ℝ) (a b d : ZMod P → ℂ) :
    T ((c : ℂ) • a) ((c : ℂ) • b) ((c : ℂ) • d) = ((c ^ 3 : ℝ) : ℂ) * T a b d := by
  have h1 : T ((c : ℂ) • a) = (c : ℂ) • T a := T.map_smul _ _
  have h2 : (T a) ((c : ℂ) • b) = (c : ℂ) • (T a) b := (T a).map_smul _ _
  have h3 : (T a b) ((c : ℂ) • d) = (starRingEnd ℂ) (c : ℂ) • (T a b) d := (T a b).map_smulₛₗ _ _
  rw [h1, LinearMap.smul_apply, LinearMap.smul_apply, h2, LinearMap.smul_apply, h3]
  simp only [smul_eq_mul, Complex.conj_ofReal]
  push_cast; ring

omit [NeZero P] in
/-- The tile operators `T_{m_{R,k}} F_k` of a part are bounded (coordinatewise). -/
theorem exists_bound_tmult {𝔭 : Params} {η η' : ℝ → ℝ} {Tr TA : Finset TriTile} {t : Top} {χ : TriTile → ℝ → ℝ}
    {m : TriTile → Fin 3 → ℝ → ℂ} (pd : PartData 𝔭 η η' Tr TA t χ m) {k : Fin 3} {F : ℝ → ZMod P → ℂ}
    (hF : IsBddC F) {R : TriTile} (hR : R ∈ TA) : ∃ A : ℝ, 0 ≤ A ∧ ∀ x y, ‖tmult (m R k) F x y‖ ≤ A :=
  (IsBddC.tmult (pd.goodModel.kernel R hR k) hF).nonneg_bound

theorem yNorm_tmult_le_of_bound {s : ℝ} (hs : 0 < s) {m : ℝ → ℂ} {F : ℝ → ZMod P → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ x y, ‖tmult m F x y‖ ≤ A) (x : ℝ) : yNorm s (tmult m F x) ≤ A :=
  yNorm_le_of_forall_le hs hA (h x)

theorem integrable_layerCut {𝔭 : Params} {η η' : ℝ → ℝ} {Tr TA : Finset TriTile} {t : Top} {χ : TriTile → ℝ → ℝ}
    {m : TriTile → Fin 3 → ℝ → ℂ} (pd : PartData 𝔭 η η' Tr TA t χ m) (σ : ℤ) :
    Integrable (fun x => layerCut η TA σ x) := by
  have : (fun x => layerCut η TA σ x) = fun x => ∑ Q ∈ layer' TA σ, χ Q x := by
    funext x
    rw [← sum_layer'_cutoff_eq_layerCut pd.cut σ x]
  rw [this]
  refine integrable_finsetSum _ fun Q hQ => ?_
  have := (pd.goodModel.integrable Q (mem_layer'_iff.1 hQ).1).re
  simpa using this

theorem layerCut_nonneg' {𝔭 : Params} {η η' : ℝ → ℝ} {Tr TA : Finset TriTile} {t : Top} {χ : TriTile → ℝ → ℝ}
    {m : TriTile → Fin 3 → ℝ → ℂ} (pd : PartData 𝔭 η η' Tr TA t χ m) (σ : ℤ) (x : ℝ) :
    0 ≤ layerCut η TA σ x := layerCut_nonneg pd.hη TA σ x

theorem layerCut_le_one' {𝔭 : Params} {η η' : ℝ → ℝ} {Tr TA : Finset TriTile} {t : Top} {χ : TriTile → ℝ → ℝ}
    {m : TriTile → Fin 3 → ℝ → ℂ} (pd : PartData 𝔭 η η' Tr TA t χ m) (σ : ℤ) (x : ℝ) :
    layerCut η TA σ x ≤ 1 := by
  obtain ⟨hN, -, -, -⟩ := pd.h𝔭.bounds
  exact layerCut_le_one pd.hη (by omega) pd.good.2.1 σ x

end Basic

section LacSq

variable {P : ℕ} [NeZero P] {𝔭 : Params} {η η' : ℝ → ℝ} {Tr TA : Finset TriTile} {t : Top} {χ : TriTile → ℝ → ℝ}
  {m : TriTile → Fin 3 → ℝ → ℂ}

omit [NeZero P] in
/-- The layer of the tree operator is `χ̃_σ T_{m_σ k} F`. -/
theorem treeOp_layer_eq (pd : PartData 𝔭 η η' Tr TA t χ m) {k : Fin 3} (F : ℝ → ZMod P → ℂ) {σ : ℤ} {R₀ : TriTile}
    (hR₀ : R₀ ∈ layer' TA σ) (x : ℝ) :
    treeOp (layer' TA σ) (fun R x => (χ R x : ℂ)) (fun R => m R k) F x =
      (layerCut η TA σ x : ℂ) • tmult (m R₀ k) F x := by
  obtain ⟨hR₀T, hs₀⟩ := mem_layer'_iff.1 hR₀
  unfold treeOp
  have h1 : ∀ Q ∈ layer' TA σ, (χ Q x : ℂ) • tmult (m Q k) F x = (χ Q x : ℂ) • tmult (m R₀ k) F x := by
    intro Q hQ
    obtain ⟨hQT, hs⟩ := mem_layer'_iff.1 hQ
    rw [pd.cons Q hQT R₀ hR₀T (pd.good.2.1 Q hQT R₀ hR₀T (hs.trans hs₀.symm))]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_smul]
  congr 1
  have := sum_layer'_cutoff_eq_layerCut (η := η) (χ := χ) (Tr := TA) pd.cut σ x
  rw [← this]
  push_cast; rfl

omit [NeZero P] in
theorem treeOp_eq_sum_layers (TA : Finset TriTile) (ψ m' : TriTile → ℝ → ℂ) (F : ℝ → ZMod P → ℂ) (x : ℝ) :
    treeOp TA ψ m' F x = ∑ σ ∈ treeScales TA, treeOp (layer' TA σ) ψ m' F x := by
  unfold treeOp
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun Q : TriTile => Q.box.scale) (t := treeScales TA)
    (fun Q hQ => mem_treeScales_iff.2 ⟨Q, hQ, rfl⟩)]
  rfl

theorem measurable_layer_vec (pd : PartData 𝔭 η η' Tr TA t χ m) {k : Fin 3} {F : ℝ → ZMod P → ℂ}
    (hF : Measurable F) {σ : ℤ} {R₀ : TriTile} (hR₀ : R₀ ∈ layer' TA σ) :
    Measurable (fun x => (layerCut η TA σ x : ℂ) • tmult (m R₀ k) F x) := by
  obtain ⟨hR₀T, -⟩ := mem_layer'_iff.1 hR₀
  have hmeasT : Measurable (tmult (m R₀ k) F) := measurable_tmult_psp ((pd.cls R₀ hR₀T).2 k) hF
  have hc : Continuous (layerCut η TA σ) := by
    unfold layerCut
    exact continuous_finsetSum _ fun R _ => continuous_tileCutoff pd.hη σ R.pos
  exact (Complex.measurable_ofReal.comp hc.measurable).smul hmeasT

/-- Integrability of `‖ℓ_{kσ}‖²`, `ℓ_{kσ} = χ̃_σ T_{m_σ k} F`. -/
theorem integrable_yNorm_sq_layer (pd : PartData 𝔭 η η' Tr TA t χ m) {k : Fin 3} {F : ℝ → ZMod P → ℂ}
    (hF : Measurable F) (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) {σ : ℤ} {R₀ : TriTile} (hR₀ : R₀ ∈ layer' TA σ) :
    Integrable (fun x => yNorm 2 ((layerCut η TA σ x : ℂ) • tmult (m R₀ k) F x) ^ 2) := by
  obtain ⟨hR₀T, -⟩ := mem_layer'_iff.1 hR₀
  obtain ⟨A, hA0, hA⟩ := exists_bound_tmult pd (k := k) (isBddC_of_hFb hF hFb) hR₀T
  have hmeasT : Measurable (tmult (m R₀ k) F) := measurable_tmult_psp ((pd.cls R₀ hR₀T).2 k) hF
  have hc : Continuous (layerCut η TA σ) := by
    unfold layerCut
    exact continuous_finsetSum _ fun R _ => continuous_tileCutoff pd.hη σ R.pos
  have hmeas : Measurable (fun x => yNorm 2 ((layerCut η TA σ x : ℂ) • tmult (m R₀ k) F x) ^ 2) :=
    (((measurable_yNorm_fun 2).comp ((Complex.measurable_ofReal.comp hc.measurable).smul hmeasT))).pow_const 2
  refine ((integrable_layerCut pd σ).const_mul (A ^ 2)).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity), yNorm_csmul (by norm_num), Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (layerCut_nonneg' pd σ x)]
  have h1 := yNorm_tmult_le_of_bound (s := 2) (by norm_num) hA0 hA x
  have h2 := yNorm_nonneg' 2 (tmult (m R₀ k) F x)
  have h3 := layerCut_nonneg' pd σ x
  have h4 := layerCut_le_one' pd σ x
  calc (layerCut η TA σ x * yNorm 2 (tmult (m R₀ k) F x)) ^ 2
      = layerCut η TA σ x ^ 2 * yNorm 2 (tmult (m R₀ k) F x) ^ 2 := by ring
    _ ≤ layerCut η TA σ x * A ^ 2 := by
        have : yNorm 2 (tmult (m R₀ k) F x) ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ h2 h1 2
        nlinarith [mul_nonneg h3 (sub_nonneg.2 h4), sq_nonneg (yNorm 2 (tmult (m R₀ k) F x)), mul_nonneg h3 h3]
    _ = A ^ 2 * layerCut η TA σ x := by ring

/-- **(L1) + (L4) at `s = q = 2`**: `Σ_σ ∫ ‖ℓ_{kσ}‖² ≤ (|I_t|^{1/2} eng)²` for a lacunary slot `k` of the part `TA`. -/
theorem lac_sq_bound (pd : PartData 𝔭 η η' Tr TA t χ m) {Qs : Set Box} (hQ : IsRankOne 𝔭.J Qs)
    (hbox : ∀ R ∈ TA, R.box ∈ Qs) {k : Fin 3} (hlac : ∀ R ∈ TA, ¬ IsOvSlot t k R.box) (hIL : IsLacunary k TA)
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) (R₀ : ℤ → TriTile)
    (hR₀ : ∀ σ ∈ treeScales TA, R₀ σ ∈ layer' TA σ) :
    ∑ σ ∈ treeScales TA, ∫⁻ x, ENNReal.ofReal (yNorm 2 ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) k) F x)) ^ (2 : ℝ) ≤
      (ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (1 / 2 : ℝ)) * eng 𝔭.tree 2 k F Tr 2) ^ (2 : ℝ) := by
  set ψ : TriTile → ℝ → ℂ := fun R x => (χ R x : ℂ) with hψ
  set m' : TriTile → ℝ → ℂ := fun R => m R k with hm'
  set G : ℝ → ZMod P → ℂ := treeOp TA ψ m' F with hG
  have hL4 := lacunary_L4 (k := k) pd.h𝔭 pd.h𝔭.1 hQ hbox pd.good hlac (pd.lacData k) hF hFb
  have hv : ∀ σ ∈ treeScales TA, ∀ x, treeOp (layer' TA σ) ψ m' F x = (layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) k) F x :=
    fun σ hσ x => treeOp_layer_eq pd F (hR₀ σ hσ) x
  have hint : ∀ σ ∈ treeScales TA, Integrable (fun x => yNorm 2 (treeOp (layer' TA σ) ψ m' F x) ^ 2) := by
    intro σ hσ
    have := integrable_yNorm_sq_layer pd (k := k) hF hFb (hR₀ σ hσ)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hv σ hσ x]
  -- measurability and integrability of `‖G‖²`
  have hvm : ∀ σ ∈ treeScales TA, Measurable (fun x => treeOp (layer' TA σ) ψ m' F x) := by
    intro σ hσ
    have h1 := measurable_layer_vec pd (k := k) hF (hR₀ σ hσ)
    have h2 : (fun x => treeOp (layer' TA σ) ψ m' F x) = fun x => (layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) k) F x :=
      funext (hv σ hσ)
    rw [h2]; exact h1
  have hGm : Measurable G := by
    have : G = fun x => ∑ σ ∈ treeScales TA, treeOp (layer' TA σ) ψ m' F x := funext (treeOp_eq_sum_layers TA ψ m' F)
    rw [this]
    exact Finset.measurable_sum _ hvm
  have hGint : Integrable (fun x => yNorm 2 (G x) ^ 2) := by
    have hS : Integrable (fun x => ((treeScales TA).card : ℝ) *
        ∑ σ ∈ treeScales TA, yNorm 2 (treeOp (layer' TA σ) ψ m' F x) ^ 2) :=
      (integrable_finsetSum _ hint).const_mul _
    refine hS.mono' (((measurable_yNorm_fun 2).comp hGm).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 : yNorm 2 (G x) ≤ ∑ σ ∈ treeScales TA, yNorm 2 (treeOp (layer' TA σ) ψ m' F x) := by
      have : G x = ∑ σ ∈ treeScales TA, treeOp (layer' TA σ) ψ m' F x := treeOp_eq_sum_layers TA ψ m' F x
      rw [this]
      exact CZ.yNorm_sum_le (by norm_num) _ _
    calc yNorm 2 (G x) ^ 2 ≤ (∑ σ ∈ treeScales TA, yNorm 2 (treeOp (layer' TA σ) ψ m' F x)) ^ 2 :=
          pow_le_pow_left₀ (yNorm_nonneg' _ _) h1 2
      _ ≤ _ := sq_sum_le_card_mul_sum_sq
  -- the lintegral identity
  have hrp : ∀ a : ℝ, 0 ≤ a → ENNReal.ofReal a ^ (2 : ℝ) = ENNReal.ofReal (a ^ 2) := fun a ha => by
    rw [ENNReal.ofReal_rpow_of_nonneg ha (by norm_num), Real.rpow_two]
  have e1 : ∑ σ ∈ treeScales TA, ∫⁻ x, ENNReal.ofReal (yNorm 2 ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) k) F x)) ^ (2 : ℝ) =
      ∫⁻ x, ENNReal.ofReal (yNorm 2 (G x)) ^ (2 : ℝ) := by
    have h2 : ∀ σ ∈ treeScales TA, ∫⁻ x, ENNReal.ofReal (yNorm 2 ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) k) F x)) ^ (2 : ℝ) =
        ENNReal.ofReal (∫ x, yNorm 2 (treeOp (layer' TA σ) ψ m' F x) ^ 2) := by
      intro σ hσ
      rw [ofReal_integral_eq_lintegral_ofReal (hint σ hσ) (Filter.Eventually.of_forall fun x => sq_nonneg _)]
      refine lintegral_congr fun x => ?_
      rw [hv σ hσ x, hrp _ (yNorm_nonneg' _ _)]
    rw [Finset.sum_congr rfl h2, ← ENNReal.ofReal_sum_of_nonneg (fun σ _ => integral_nonneg fun x => sq_nonneg _),
      hL4, ofReal_integral_eq_lintegral_ofReal hGint (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    refine lintegral_congr fun x => ?_
    rw [hrp _ (yNorm_nonneg' _ _)]
  -- (L1)
  have hL1 := lacunary_L1 (s := 2) (q := 2) (F := F) (Cs := Tr) pd.sub pd.good.1 hIL (pd.lacData k).tree
  unfold treeOpNorm at hL1
  set E : ℝ≥0∞ := eng 𝔭.tree 2 k F Tr 2 with hE
  set c₁ : ℝ := ((2 : ℝ) ^ t.1.1) ^ (1 / 2 : ℝ) with hc₁
  have hp2 := zpow_two_pos t.1.1
  have hcc : ENNReal.ofReal c₁ * ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (-1 / (2 : ℝ))) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hp2.le _), ← Real.rpow_add hp2]
    have : (1 / 2 : ℝ) + -1 / 2 = 0 := by norm_num
    rw [this, Real.rpow_zero, ENNReal.ofReal_one]
  set eL : ℝ≥0∞ := eLpNorm (fun x => yNorm 2 (G x)) (ENNReal.ofReal 2) volume with heL
  have hL1' : eL ≤ ENNReal.ofReal c₁ * E := by
    calc eL = ENNReal.ofReal c₁ * (ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (-1 / (2 : ℝ))) * eL) := by
          rw [← mul_assoc, hcc, one_mul]
      _ ≤ ENNReal.ofReal c₁ * E := mul_le_mul' le_rfl hL1
  have hmeasA : Measurable (fun x => ENNReal.ofReal (yNorm 2 (G x))) :=
    ENNReal.measurable_ofReal.comp ((measurable_yNorm_fun 2).comp hGm)
  have heq : eL = (∫⁻ x, ENNReal.ofReal (yNorm 2 (G x)) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    have h0 : AEStronglyMeasurable (fun x => yNorm 2 (G x)) volume :=
      ((measurable_yNorm_fun 2).comp hGm).aestronglyMeasurable
    rw [heL, ← eLpNorm_enorm (fun x => yNorm 2 (G x)) h0]
    have : (fun x => ‖yNorm 2 (G x)‖ₑ) = fun x => ENNReal.ofReal (yNorm 2 (G x)) :=
      funext fun x => Real.enorm_eq_ofReal (yNorm_nonneg' _ _)
    rw [this]
    exact eLpNorm_ofReal_eq_lintegral (by norm_num) hmeasA
  rw [e1]
  have : (∫⁻ x, ENNReal.ofReal (yNorm 2 (G x)) ^ (2 : ℝ)) = eL ^ (2 : ℝ) := by
    rw [heq, ← ENNReal.rpow_mul]; norm_num
  rw [this]
  exact ENNReal.rpow_le_rpow hL1' (by norm_num)

end LacSq

end PrimeBHT.TimeFrequency.X2
