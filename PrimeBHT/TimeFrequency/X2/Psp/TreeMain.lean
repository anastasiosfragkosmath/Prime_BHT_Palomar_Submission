module

public import PrimeBHT.TimeFrequency.X2.Psp.TreeLac

/-!
# X2, V15 (assembly), step 4: the cubic main term and the conversion

For a part `TA` (good tree, one box per scale) and bounded measurable `F_k`:
`Λ_{TA} = Σ_σ ∫ Π(ℓ_{0σ}, ℓ_{1σ}, ℓ_{2σ}) + Σ_σ ∫ (χ̃_σ - χ̃_σ³) Π(a_{0σ}, a_{1σ}, a_{2σ})`, `ℓ_{kσ} = χ̃_σ a_{kσ}`, `a_{kσ} = T_{m_σ k} F_k`
(`modelForm_eq_cubic_add_conv`), the first sum being the cubic form (each slot carries `χ̃_σ`) of MTT2's tree estimate.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

section Main

variable {P : ℕ} [NeZero P] {𝔭 : Params} {η η' : ℝ → ℝ} {Tr TA : Finset TriTile} {t : Top} {χ : TriTile → ℝ → ℝ}
  {m : TriTile → Fin 3 → ℝ → ℂ}

/-- `w · Π(a₀, a₁, a₂)` is integrable for a measurable `w` dominated by `χ̃_σ`. -/
theorem integrable_weight_T (pd : PartData 𝔭 η η' Tr TA t χ m) {T : Form P} {F : Fin 3 → ℝ → ZMod P → ℂ}
    (hF : ∀ k, IsBddC (F k)) {σ : ℤ} {R₀ : TriTile} (hR₀ : R₀ ∈ layer' TA σ) {w : ℝ → ℝ} (hw : Measurable w)
    (hwb : ∀ x, |w x| ≤ layerCut η TA σ x) :
    Integrable (fun x => (w x : ℂ) *
      T (tmult (m R₀ 0) (F 0) x) (tmult (m R₀ 1) (F 1) x) (tmult (m R₀ 2) (F 2) x)) := by
  obtain ⟨hR₀T, -⟩ := mem_layer'_iff.1 hR₀
  have ha := IsBddC.tmult (pd.goodModel.kernel R₀ hR₀T 0) (hF 0)
  have hb := IsBddC.tmult (pd.goodModel.kernel R₀ hR₀T 1) (hF 1)
  have hc := IsBddC.tmult (pd.goodModel.kernel R₀ hR₀T 2) (hF 2)
  obtain ⟨A, hA0, hA⟩ := ha.nonneg_bound
  obtain ⟨B, hB0, hB⟩ := hb.nonneg_bound
  obtain ⟨C, hC0, hC⟩ := hc.nonneg_bound
  have hTm := measurable_T T ha.1 hb.1 hc.1
  refine ((integrable_layerCut pd σ).const_mul (rieszBound T * (A * B) * C)).mono'
    ((Complex.measurable_ofReal.comp hw).mul hTm).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := norm_T_le T hA0 hB0 (hA x) (hB x) (hC x)
  have h2 := hwb x
  calc |w x| * ‖T (tmult (m R₀ 0) (F 0) x) (tmult (m R₀ 1) (F 1) x) (tmult (m R₀ 2) (F 2) x)‖
      ≤ layerCut η TA σ x * (rieszBound T * (A * B) * C) :=
        mul_le_mul h2 h1 (norm_nonneg _) (layerCut_nonneg' pd σ x)
    _ = _ := by ring

/-- **The cubic decomposition**: `Λ_{TA} = Σ_σ ∫ Π(χ̃a₀, χ̃a₁, χ̃a₂) + Σ_σ ∫ (χ̃ - χ̃³) Π(a₀, a₁, a₂)`. -/
theorem modelForm_eq_cubic_add_conv (pd : PartData 𝔭 η η' Tr TA t χ m) {T : Form P} {F : Fin 3 → ℝ → ZMod P → ℂ}
    (hF : ∀ k, IsBddC (F k)) (R₀ : ℤ → TriTile) (hR₀ : ∀ σ ∈ treeScales TA, R₀ σ ∈ layer' TA σ) :
    modelForm T TA χ m (F 0) (F 1) (F 2) =
      (∑ σ ∈ treeScales TA, ∫ x, T ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) 0) (F 0) x)
          ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) 1) (F 1) x) ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) 2) (F 2) x)) +
      ∑ σ ∈ treeScales TA, ∫ x, ((layerCut η TA σ x - layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
          T (tmult (m (R₀ σ) 0) (F 0) x) (tmult (m (R₀ σ) 1) (F 1) x) (tmult (m (R₀ σ) 2) (F 2) x) := by
  rw [modelForm_eq_sum_layers pd.goodModel pd.good pd.cons pd.cut (hF 0) (hF 1) (hF 2) R₀ hR₀, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have hc : Measurable (layerCut η TA σ) := by
    have : Continuous (layerCut η TA σ) := by
      unfold layerCut
      exact continuous_finsetSum _ fun R _ => continuous_tileCutoff pd.hη σ R.pos
    exact this.measurable
  have h3 := layerCut_nonneg' pd σ
  have h1 := layerCut_le_one' pd σ
  have hi3 := integrable_weight_T (T := T) pd hF (hR₀ σ hσ) (hc.pow_const 3) (fun x => by
    rw [abs_of_nonneg (pow_nonneg (h3 x) 3)]
    nlinarith [h3 x, h1 x, mul_nonneg (h3 x) (h3 x), mul_nonneg (mul_nonneg (h3 x) (h3 x)) (sub_nonneg.2 (h1 x))])
  have hid := integrable_weight_T (T := T) pd hF (hR₀ σ hσ) (w := fun x => layerCut η TA σ x - layerCut η TA σ x ^ 3)
    (hc.sub (hc.pow_const 3)) (fun x => by
    show |layerCut η TA σ x - layerCut η TA σ x ^ 3| ≤ layerCut η TA σ x
    have hh : 0 ≤ layerCut η TA σ x - layerCut η TA σ x ^ 3 := by
      nlinarith [h3 x, h1 x, mul_nonneg (h3 x) (h3 x), mul_nonneg (mul_nonneg (h3 x) (h3 x)) (sub_nonneg.2 (h1 x))]
    rw [abs_of_nonneg hh]
    nlinarith [pow_nonneg (h3 x) 3])
  have e : ∀ x, T ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) 0) (F 0) x)
        ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) 1) (F 1) x) ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) 2) (F 2) x) =
      ((layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
        T (tmult (m (R₀ σ) 0) (F 0) x) (tmult (m (R₀ σ) 1) (F 1) x) (tmult (m (R₀ σ) 2) (F 2) x) :=
    fun x => Form_smul3 T _ _ _ _
  simp_rw [e]
  rw [← integral_add hi3 hid]
  congr 1
  funext x
  push_cast
  ring

end Main

end PrimeBHT.TimeFrequency.X2
