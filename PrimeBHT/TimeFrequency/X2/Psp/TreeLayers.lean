module

public import PrimeBHT.TimeFrequency.X2.Psp.OverlapStmt
public import PrimeBHT.TimeFrequency.X2.Psp.OverlapCoef
public import PrimeBHT.TimeFrequency.X2.ModelOp

/-!
# X2, V15 (assembly), step 1: the parts of a tree and the layer decomposition of the model form

`docs/audits/X2-V13-route-check.md` §4 step 1.

* `modelForm_eq_sum_treePart`: `Λ_Tr = Σ_A Λ_{T_A}` (`A` = the set of lacunary slots of the tile's box, `treePart`);
* `treePart_eq_empty_of_card_lt`: only the parts with `#A ≥ 2` are non-empty (S-1);
* `sum_layer_integrals`, `modelForm_eq_sum_layers`: for a good tree (one box per scale) with consistent multipliers,
  `Λ_{T_A} = Σ_σ ∫ χ̃_σ Π(T_{m_σ0}F₀, T_{m_σ1}F₁, T_{m_σ2}F₂)`, `χ̃_σ = layerCut`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

section Parts

variable {P : ℕ} [NeZero P]

omit [NeZero P] in
/-- `Λ_Tr = Σ_A Λ_{T_A}`. -/
theorem modelForm_eq_sum_treePart (T : Form P) (Tr : Finset TriTile) (t : Top) (χ : TriTile → ℝ → ℝ)
    (m : TriTile → Fin 3 → ℝ → ℂ) (F₀ F₁ F₂ : ℝ → ZMod P → ℂ) :
    modelForm T Tr χ m F₀ F₁ F₂ = ∑ A : Finset (Fin 3), modelForm T (treePart Tr t A) χ m F₀ F₁ F₂ := by
  unfold modelForm treePart
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun Q : TriTile => slotType t Q.box) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]

theorem treePart_eq_empty_of_card_lt {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {Tr : Finset TriTile}
    (hbox : ∀ R ∈ Tr, R.box ∈ Qs) (t : Top) {A : Finset (Fin 3)} (hA : A.card < 2) : treePart Tr t A = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun R hR => ?_
  obtain ⟨hRT, hRA⟩ := mem_treePart.1 hR
  have := two_le_card_slotType hQ (hbox R hRT) t
  rw [hRA] at this
  omega

/-- The model form is the sum over the parts with at least two lacunary slots. -/
theorem modelForm_eq_sum_big_parts {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {Tr : Finset TriTile}
    (hbox : ∀ R ∈ Tr, R.box ∈ Qs) (t : Top) (T : Form P) (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ)
    (F₀ F₁ F₂ : ℝ → ZMod P → ℂ) :
    modelForm T Tr χ m F₀ F₁ F₂ =
      ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin 3) => 2 ≤ A.card), modelForm T (treePart Tr t A) χ m F₀ F₁ F₂ := by
  rw [modelForm_eq_sum_treePart T Tr t χ m F₀ F₁ F₂, Finset.sum_filter]
  refine Finset.sum_congr rfl fun A _ => ?_
  by_cases h : 2 ≤ A.card
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, treePart_eq_empty_of_card_lt hQ hbox t (by omega)]
    simp [modelForm]

theorem card_bigParts : (Finset.univ.filter (fun A : Finset (Fin 3) => 2 ≤ A.card)).card = 4 := by decide

end Parts

section Layers

variable {P : ℕ} [NeZero P]

/-- One layer: `Σ_{Q ∈ layer σ} ∫ χ_Q Π(…) = ∫ χ̃_σ Π(T_{m_{R₀,0}}F₀, …)` for any `R₀` of the layer. -/
theorem sum_layer_integrals {TA : Finset TriTile} {t : Top} {T : Form P} {χ : TriTile → ℝ → ℝ}
    {m : TriTile → Fin 3 → ℝ → ℂ} {η : ℝ → ℝ} (hg : GoodModel TA χ m) (hT : IsGoodTree TA t)
    (hcons : ∀ Q ∈ TA, ∀ Q' ∈ TA, Q.box = Q'.box → m Q = m Q') (hcut : ∀ Q ∈ TA, χ Q = tileCutoff η Q.box.scale Q.pos)
    {F₀ F₁ F₂ : ℝ → ZMod P → ℂ} (h₀ : IsBddC F₀) (h₁ : IsBddC F₁) (h₂ : IsBddC F₂) {σ : ℤ} {R₀ : TriTile}
    (hR₀ : R₀ ∈ layer' TA σ) :
    ∑ Q ∈ layer' TA σ, ∫ x, (χ Q x : ℂ) * T (tmult (m Q 0) F₀ x) (tmult (m Q 1) F₁ x) (tmult (m Q 2) F₂ x) =
      ∫ x, (layerCut η TA σ x : ℂ) * T (tmult (m R₀ 0) F₀ x) (tmult (m R₀ 1) F₁ x) (tmult (m R₀ 2) F₂ x) := by
  obtain ⟨hR₀T, hs₀⟩ := mem_layer'_iff.1 hR₀
  have hmQ : ∀ Q ∈ layer' TA σ, m Q = m R₀ := by
    intro Q hQ
    obtain ⟨hQT, hs⟩ := mem_layer'_iff.1 hQ
    exact hcons Q hQT R₀ hR₀T (hT.2.1 Q hQT R₀ hR₀T (hs.trans hs₀.symm))
  have hint : ∀ Q ∈ layer' TA σ, Integrable (fun x => (χ Q x : ℂ) *
      T (tmult (m R₀ 0) F₀ x) (tmult (m R₀ 1) F₁ x) (tmult (m R₀ 2) F₂ x)) := by
    intro Q hQ
    have := integrable_modelIntegrand (T := T) hg (mem_layer'_iff.1 hQ).1 h₀ h₁ h₂
    rw [hmQ Q hQ] at this
    exact this
  have e1 : ∀ Q ∈ layer' TA σ, (fun x => (χ Q x : ℂ) * T (tmult (m Q 0) F₀ x) (tmult (m Q 1) F₁ x) (tmult (m Q 2) F₂ x)) =
      fun x => (χ Q x : ℂ) * T (tmult (m R₀ 0) F₀ x) (tmult (m R₀ 1) F₁ x) (tmult (m R₀ 2) F₂ x) := by
    intro Q hQ; rw [hmQ Q hQ]
  rw [Finset.sum_congr rfl fun Q hQ => by rw [e1 Q hQ], ← integral_finset_sum _ hint]
  congr 1
  funext x
  rw [← Finset.sum_mul]
  congr 1
  have := sum_layer'_cutoff_eq_layerCut (η := η) (χ := χ) (Tr := TA) hcut σ x
  rw [← this]
  push_cast
  rfl

/-- **Layer decomposition**: `Λ_{T_A} = Σ_σ ∫ χ̃_σ Π(T_{m_σ0}F₀, T_{m_σ1}F₁, T_{m_σ2}F₂)`. -/
theorem modelForm_eq_sum_layers {TA : Finset TriTile} {t : Top} {T : Form P} {χ : TriTile → ℝ → ℝ}
    {m : TriTile → Fin 3 → ℝ → ℂ} {η : ℝ → ℝ} (hg : GoodModel TA χ m) (hT : IsGoodTree TA t)
    (hcons : ∀ Q ∈ TA, ∀ Q' ∈ TA, Q.box = Q'.box → m Q = m Q') (hcut : ∀ Q ∈ TA, χ Q = tileCutoff η Q.box.scale Q.pos)
    {F₀ F₁ F₂ : ℝ → ZMod P → ℂ} (h₀ : IsBddC F₀) (h₁ : IsBddC F₁) (h₂ : IsBddC F₂)
    (R₀ : ℤ → TriTile) (hR₀ : ∀ σ ∈ treeScales TA, R₀ σ ∈ layer' TA σ) :
    modelForm T TA χ m F₀ F₁ F₂ = ∑ σ ∈ treeScales TA, ∫ x, (layerCut η TA σ x : ℂ) *
      T (tmult (m (R₀ σ) 0) F₀ x) (tmult (m (R₀ σ) 1) F₁ x) (tmult (m (R₀ σ) 2) F₂ x) := by
  unfold modelForm
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun Q : TriTile => Q.box.scale) (t := treeScales TA)
    (fun Q hQ => mem_treeScales_iff.2 ⟨Q, hQ, rfl⟩)]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have := sum_layer_integrals (T := T) hg hT hcons hcut h₀ h₁ h₂ (hR₀ σ hσ)
  rw [← this]
  rfl

end Layers

end PrimeBHT.TimeFrequency.X2
