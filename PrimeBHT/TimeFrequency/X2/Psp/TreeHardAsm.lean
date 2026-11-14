module

public import PrimeBHT.TimeFrequency.X2.Psp.TreeFinal

/-!
# X2, V15 (assembly), step 7: the hard parts (a Hilbert slot overlapping) — algebraic splitting

For a form `Tq` with the OVERLAPPING Hilbert slot in the first argument (`Tq = T` or `T.swap12`), the overlapping function
`G` (of `OverlapPsp`) and `a_o = T_{m_σ i} F_o = b + e`, `b = T_{m_σ i} G`, `e = T_{m_σ i}(F_o - G)`:

`Σ_σ ∫ Tq(χ̃a_o, χ̃a_h, χ̃a_w) = P - ERR₂ + ERR₁`,

* `P = Σ_σ ∫ χ̃² Tq(b, a_h, a_w) = Σ_σ ∫ Tq(b, ℓ_h, ℓ_w)` (the paraproduct term),
* `ERR₂ = Σ_σ ∫ (χ̃² - χ̃³) Tq(b, a_h, a_w)`,
* `ERR₁ = Σ_σ ∫ χ̃³ Tq(e, a_h, a_w)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

section Asm

variable {P : ℕ} [NeZero P] {𝔭 : Params} {η η' : ℝ → ℝ} {Tr TA : Finset TriTile} {t : Top} {χ : TriTile → ℝ → ℝ}
  {m : TriTile → Fin 3 → ℝ → ℂ}

omit [NeZero P] in
theorem isBddC_sub {F G : ℝ → ZMod P → ℂ} (hF : IsBddC F) (hG : IsBddC G) : IsBddC (F - G) := by
  have : F - G = F + (-1 : ℂ) • G := by funext x y; simp [sub_eq_add_neg]
  rw [this]; exact hF.add (hG.smul _)

/-- `w · Π(α, β, γ)` is integrable for bounded measurable `α, β, γ` and a measurable `w` dominated by `χ̃_σ`. -/
theorem integrable_weight_T' (pd : PartData 𝔭 η η' Tr TA t χ m) {Tq : Form P} {α β γ : ℝ → ZMod P → ℂ}
    (hα : IsBddC α) (hβ : IsBddC β) (hγ : IsBddC γ) {σ : ℤ} {w : ℝ → ℝ} (hw : Measurable w)
    (hwb : ∀ x, |w x| ≤ layerCut η TA σ x) : Integrable (fun x => (w x : ℂ) * Tq (α x) (β x) (γ x)) := by
  obtain ⟨A, hA0, hA⟩ := hα.nonneg_bound
  obtain ⟨B, hB0, hB⟩ := hβ.nonneg_bound
  obtain ⟨C, hC0, hC⟩ := hγ.nonneg_bound
  have hTm := measurable_T Tq hα.1 hβ.1 hγ.1
  refine ((integrable_layerCut pd σ).const_mul (rieszBound Tq * (A * B) * C)).mono'
    ((Complex.measurable_ofReal.comp hw).mul hTm).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := norm_T_le Tq hA0 hB0 (hA x) (hB x) (hC x)
  calc |w x| * ‖Tq (α x) (β x) (γ x)‖ ≤ layerCut η TA σ x * (rieszBound Tq * (A * B) * C) :=
        mul_le_mul (hwb x) h1 (norm_nonneg _) (layerCut_nonneg' pd σ x)
    _ = _ := by ring

omit [NeZero P] in
theorem Form_smul2 (T : Form P) (c : ℝ) (a b d : ZMod P → ℂ) :
    T a ((c : ℂ) • b) ((c : ℂ) • d) = ((c ^ 2 : ℝ) : ℂ) * T a b d := by
  have h2 : (T a) ((c : ℂ) • b) = (c : ℂ) • (T a) b := (T a).map_smul _ _
  have h3 : (T a b) ((c : ℂ) • d) = (starRingEnd ℂ) (c : ℂ) • (T a b) d := (T a b).map_smulₛₗ _ _
  rw [h2, LinearMap.smul_apply, h3]
  simp only [smul_eq_mul, Complex.conj_ofReal]
  push_cast; ring

/-- **The splitting** `Σ_σ ∫ Π(χ̃a_o, χ̃a_h, χ̃a_w) = P - ERR₂ + ERR₁`. -/
theorem cubic_split (pd : PartData 𝔭 η η' Tr TA t χ m) {Tq : Form P} {i j : Fin 3} {Fo Fh Fw G : ℝ → ZMod P → ℂ}
    (hFo : IsBddC Fo) (hFh : IsBddC Fh) (hFw : IsBddC Fw) (hG : IsBddC G) (R₀ : ℤ → TriTile)
    (hR₀ : ∀ σ ∈ treeScales TA, R₀ σ ∈ layer' TA σ) :
    ∑ σ ∈ treeScales TA, ∫ x, Tq ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) i) Fo x)
        ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) j) Fh x) ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) 2) Fw x) =
      (∑ σ ∈ treeScales TA, ∫ x, ((layerCut η TA σ x ^ 2 : ℝ) : ℂ) *
          Tq (tmult (m (R₀ σ) i) G x) (tmult (m (R₀ σ) j) Fh x) (tmult (m (R₀ σ) 2) Fw x)) -
        (∑ σ ∈ treeScales TA, ∫ x, ((layerCut η TA σ x ^ 2 - layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
          Tq (tmult (m (R₀ σ) i) G x) (tmult (m (R₀ σ) j) Fh x) (tmult (m (R₀ σ) 2) Fw x)) +
        ∑ σ ∈ treeScales TA, ∫ x, ((layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
          Tq (tmult (m (R₀ σ) i) (Fo - G) x) (tmult (m (R₀ σ) j) Fh x) (tmult (m (R₀ σ) 2) Fw x) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have hRσ := hR₀ σ hσ
  obtain ⟨hRT, -⟩ := mem_layer'_iff.1 hRσ
  have hgm := pd.goodModel
  have hbG := IsBddC.tmult (hgm.kernel (R₀ σ) hRT i) hG
  have heFG := IsBddC.tmult (hgm.kernel (R₀ σ) hRT i) (isBddC_sub hFo hG)
  have hah := IsBddC.tmult (hgm.kernel (R₀ σ) hRT j) hFh
  have haw := IsBddC.tmult (hgm.kernel (R₀ σ) hRT 2) hFw
  have hc : Measurable (layerCut η TA σ) := by
    have : Continuous (layerCut η TA σ) := by
      unfold layerCut
      exact continuous_finsetSum _ fun R _ => continuous_tileCutoff pd.hη σ R.pos
    exact this.measurable
  have h3 := layerCut_nonneg' pd σ
  have h1 := layerCut_le_one' pd σ
  have hw1 : ∀ x, |layerCut η TA σ x ^ 2| ≤ layerCut η TA σ x := fun x => by
    rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [h3 x, h1 x]
  have hw2 : ∀ x, |layerCut η TA σ x ^ 2 - layerCut η TA σ x ^ 3| ≤ layerCut η TA σ x := fun x => by
    have : 0 ≤ layerCut η TA σ x ^ 2 - layerCut η TA σ x ^ 3 := by
      nlinarith [mul_nonneg (h3 x) (h3 x), mul_nonneg (mul_nonneg (h3 x) (h3 x)) (sub_nonneg.2 (h1 x))]
    rw [abs_of_nonneg this]; nlinarith [h3 x, h1 x, pow_nonneg (h3 x) 3, mul_nonneg (h3 x) (h3 x)]
  have hw3 : ∀ x, |layerCut η TA σ x ^ 3| ≤ layerCut η TA σ x := fun x => by
    rw [abs_of_nonneg (pow_nonneg (h3 x) 3)]
    nlinarith [h3 x, h1 x, mul_nonneg (h3 x) (h3 x), mul_nonneg (mul_nonneg (h3 x) (h3 x)) (sub_nonneg.2 (h1 x))]
  have i1 := integrable_weight_T' (Tq := Tq) pd hbG hah haw (σ := σ) (hc.pow_const 2) hw1
  have i2 := integrable_weight_T' (Tq := Tq) pd hbG hah haw (σ := σ)
    (w := fun x => layerCut η TA σ x ^ 2 - layerCut η TA σ x ^ 3) ((hc.pow_const 2).sub (hc.pow_const 3)) hw2
  have i3 := integrable_weight_T' (Tq := Tq) pd heFG hah haw (σ := σ) (hc.pow_const 3) hw3
  have hsplit : tmult (m (R₀ σ) i) Fo = tmult (m (R₀ σ) i) G + tmult (m (R₀ σ) i) (Fo - G) := by
    rw [← tmult_add (hgm.kernel (R₀ σ) hRT i) hG (isBddC_sub hFo hG)]
    congr 1; funext x y; simp
  -- pointwise identity
  have e : ∀ x, Tq ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) i) Fo x)
        ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) j) Fh x) ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) 2) Fw x) =
      ((layerCut η TA σ x ^ 2 : ℝ) : ℂ) * Tq (tmult (m (R₀ σ) i) G x) (tmult (m (R₀ σ) j) Fh x) (tmult (m (R₀ σ) 2) Fw x) -
        ((layerCut η TA σ x ^ 2 - layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
          Tq (tmult (m (R₀ σ) i) G x) (tmult (m (R₀ σ) j) Fh x) (tmult (m (R₀ σ) 2) Fw x) +
        ((layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
          Tq (tmult (m (R₀ σ) i) (Fo - G) x) (tmult (m (R₀ σ) j) Fh x) (tmult (m (R₀ σ) 2) Fw x) := by
    intro x
    rw [Form_smul3, hsplit]
    simp only [Pi.add_apply, map_add, LinearMap.add_apply]
    push_cast; ring
  simp_rw [e]
  have key := integral_add (i1.sub i2) i3
  have key2 := integral_sub i1 i2
  simp only [Pi.sub_apply] at key key2
  rw [key, key2]

/-! ## Kernel sup bound -/

theorem lintegral_kern_eq (R x : ℝ) (hR : 0 < R) :
    ∫⁻ z, ENNReal.ofReal (R⁻¹ * (1 + |x - z| / R) ^ (-2 : ℤ)) = ENNReal.ofReal 2 := by
  have hI := integrable_one_add_abs_sub_div_rpow (p := 2) (by norm_num) x hR
  have e : ∀ z : ℝ, R⁻¹ * (1 + |x - z| / R) ^ (-2 : ℤ) = R⁻¹ * (1 + |z - x| / R) ^ (-(2 : ℝ)) := by
    intro z
    rw [abs_sub_comm, show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
  simp_rw [e]
  have hnn : ∀ z : ℝ, 0 ≤ R⁻¹ * (1 + |z - x| / R) ^ (-(2 : ℝ)) := fun z => by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal (hI.const_mul R⁻¹) (Filter.Eventually.of_forall hnn)]
  congr 1
  rw [integral_const_mul, integral_one_add_abs_sub_div_rpow (p := 2) (by norm_num) x hR]
  field_simp; norm_num

theorem ofReal_yNorm_tmult_sup_le {𝔭 : Params} (h𝔭 : 𝔭.Admissible) {s : ℝ} (hs : 1 ≤ s) {sc : ℤ} {c : ℝ} {m' : ℝ → ℂ}
    (hm : InMult 𝔭 sc c m') {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {M : ℝ≥0∞}
    (hM : ∀ z, ENNReal.ofReal (yNorm s (F z)) ≤ M) (x : ℝ) :
    ENNReal.ofReal (yNorm s (tmult m' F x)) ≤ ENNReal.ofReal (6 * 𝔭.β * 𝔭.C) * M := by
  have hR : (0 : ℝ) < (2 : ℝ) ^ sc := zpow_two_pos sc
  have h1 := ofReal_yNorm_tmult_le h𝔭 hs hm hF x
  refine h1.trans ?_
  have hcont : Continuous fun z : ℝ => ((2 : ℝ) ^ sc)⁻¹ * (1 + |x - z| / (2 : ℝ) ^ sc) ^ (-2 : ℤ) := by
    refine continuous_const.mul (Continuous.zpow₀ ?_ _ fun z => Or.inl ?_)
    · fun_prop
    · positivity
  have hmeas : Measurable fun z : ℝ => ENNReal.ofReal (((2 : ℝ) ^ sc)⁻¹ * (1 + |x - z| / (2 : ℝ) ^ sc) ^ (-2 : ℤ)) :=
    ENNReal.measurable_ofReal.comp hcont.measurable
  have hk : ∫⁻ z, ENNReal.ofReal (((2 : ℝ) ^ sc)⁻¹ * (1 + |x - z| / (2 : ℝ) ^ sc) ^ (-2 : ℤ)) *
        ENNReal.ofReal (yNorm s (F z)) ≤ ENNReal.ofReal 2 * M := by
    calc _ ≤ ∫⁻ z, ENNReal.ofReal (((2 : ℝ) ^ sc)⁻¹ * (1 + |x - z| / (2 : ℝ) ^ sc) ^ (-2 : ℤ)) * M :=
          lintegral_mono fun z => mul_le_mul' le_rfl (hM z)
      _ = ENNReal.ofReal 2 * M := by
          rw [lintegral_mul_const M hmeas, lintegral_kern_eq _ _ hR]
  obtain ⟨-, -, hβ, hC⟩ := h𝔭.bounds
  calc ENNReal.ofReal (3 * 𝔭.β * 𝔭.C) * ∫⁻ z, ENNReal.ofReal (((2 : ℝ) ^ sc)⁻¹ * (1 + |x - z| / (2 : ℝ) ^ sc) ^ (-2 : ℤ)) *
        ENNReal.ofReal (yNorm s (F z))
      ≤ ENNReal.ofReal (3 * 𝔭.β * 𝔭.C) * (ENNReal.ofReal 2 * M) := mul_le_mul' le_rfl hk
    _ = ENNReal.ofReal (6 * 𝔭.β * 𝔭.C) * M := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2; ring

/-! ## ERR₂ -/

theorem err2_real_ineq {c y₀ y₁ y₂ CT bL t : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hy₀ : 0 ≤ y₀) (hy₁ : 0 ≤ y₁)
    (hy₂ : 0 ≤ y₂) (hCT : 0 ≤ CT) (hbL : bL = c ^ (1 / 2 : ℝ) * (1 - c)) (ht : t ≤ CT * y₀ * y₁ * y₂) :
    (c ^ 2 - c ^ 3) * t ≤ CT * bL * y₀ * ((c ^ (1 / 6 : ℝ) * y₁) * (c ^ (1 / 6 : ℝ) * y₂)) := by
  set u : ℝ := c ^ (1 / 6 : ℝ) with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg hc0 _
  have hc : c = u ^ 6 := by rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hc0]; norm_num
  have hh : c ^ (1 / 2 : ℝ) = u ^ 3 := by rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hc0]; norm_num
  rw [hh] at hbL
  have hu1 : u ≤ 1 := by
    by_contra h; push Not at h
    have : 1 < u ^ 6 := one_lt_pow₀ h (by norm_num)
    linarith
  have h6 : u ^ 6 ≤ 1 := by rw [← hc]; exact hc1
  have hcc : 0 ≤ c ^ 2 - c ^ 3 := by
    nlinarith [mul_nonneg hc0 hc0, mul_nonneg (mul_nonneg hc0 hc0) (sub_nonneg.2 hc1)]
  have h3 : 0 ≤ CT * y₀ * y₁ * y₂ := by positivity
  have h2 : c ^ 2 - c ^ 3 ≤ u ^ 2 * (u ^ 3 * (1 - c)) := by
    rw [hc]
    have hp : 0 ≤ u := hu0
    have : 0 ≤ u ^ 5 := by positivity
    have h7 : u ^ 7 ≤ 1 := pow_le_one₀ hp hu1
    have h12 : (u ^ 6) ^ 2 - (u ^ 6) ^ 3 = u ^ 12 * (1 - u ^ 6) := by ring
    have h12' : u ^ 2 * (u ^ 3 * (1 - u ^ 6)) = u ^ 5 * (1 - u ^ 6) := by ring
    rw [h12, h12']
    have : u ^ 12 ≤ u ^ 5 := pow_le_pow_of_le_one hp hu1 (by norm_num)
    exact mul_le_mul_of_nonneg_right this (sub_nonneg.2 h6)
  calc (c ^ 2 - c ^ 3) * t ≤ (c ^ 2 - c ^ 3) * (CT * y₀ * y₁ * y₂) := mul_le_mul_of_nonneg_left ht hcc
    _ ≤ (u ^ 2 * (u ^ 3 * (1 - c))) * (CT * y₀ * y₁ * y₂) := mul_le_mul_of_nonneg_right h2 h3
    _ = _ := by rw [hbL]; ring

/-- The constant of ERR₂. -/
def err2Const (𝔭 : Params) (R : ℝ) : ℝ :=
  12 * bLayerConst 𝔭 * (6 * 𝔭.β * 𝔭.C) *
    ((cutK 𝔭 ^ (1 / 6 : ℝ) * lacSConst 𝔭 2 ((𝔭.N : ℝ) / 6)) * (cutK 𝔭 ^ (1 / 6 : ℝ) * lacSConst 𝔭 R ((𝔭.N : ℝ) / 6)))

/-- **ERR₂**: `‖Σ_σ ∫ (χ̃² - χ̃³) Π(T_{m_σ i}G, a_h, a_w)‖ ≤ C CT |I_t| M_G E_h E_w`, `M_G` a sup bound of `G`. -/
theorem err2_bound (pd : PartData 𝔭 η η' Tr TA t χ m) {Tq : Form P} {u R CT : ℝ} (hu : 1 < u) (hR : 2 < R)
    (hT : FormBound u Tq CT) {i j : Fin 3} {Fh Fw G : ℝ → ZMod P → ℂ} (hFh : Measurable Fh)
    (hFhb : ∃ B, ∀ x, yNorm 2 (Fh x) ≤ B) (hFw : Measurable Fw) (hFwb : ∃ B, ∀ x, yNorm 2 (Fw x) ≤ B)
    (hG : Measurable G) {MG : ℝ≥0∞} (hMG : ∀ x, ENNReal.ofReal (yNorm 2 (G x)) ≤ MG) (R₀ : ℤ → TriTile)
    (hR₀ : ∀ σ ∈ treeScales TA, R₀ σ ∈ layer' TA σ) :
    ‖∑ σ ∈ treeScales TA, ∫ x, ((layerCut η TA σ x ^ 2 - layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
        Tq (tmult (m (R₀ σ) i) G x) (tmult (m (R₀ σ) j) Fh x) (tmult (m (R₀ σ) 2) Fw x)‖ₑ ≤
      ENNReal.ofReal (err2Const 𝔭 R * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) *
        (MG * (eng 𝔭.tree 2 j Fh Tr 2 * eng 𝔭.tree u 2 Fw Tr R)) := by
  obtain ⟨hN, -, hβ, hC⟩ := pd.h𝔭.bounds
  have hb := pd.good.2.1
  have hCT : 0 ≤ CT := nonneg_of_formBound (by linarith) hT
  have hKp : 0 < cutK 𝔭 := cutK_pos (by linarith)
  set Eh := eng 𝔭.tree 2 j Fh Tr 2 with hEh
  set Ew := eng 𝔭.tree u 2 Fw Tr R with hEw
  set Kh : ℝ≥0∞ := ENNReal.ofReal (cutK 𝔭 ^ (1 / 6 : ℝ)) * ENNReal.ofReal (lacSConst 𝔭 2 ((𝔭.N : ℝ) / 6)) with hKh
  set Kw : ℝ≥0∞ := ENNReal.ofReal (cutK 𝔭 ^ (1 / 6 : ℝ)) * ENNReal.ofReal (lacSConst 𝔭 R ((𝔭.N : ℝ) / 6)) with hKw
  set Y : ℝ≥0∞ := (ENNReal.ofReal (6 * 𝔭.β * 𝔭.C) * MG) * ((Kh * Eh) * (Kw * Ew)) with hY
  have hpt : ∀ σ ∈ treeScales TA, ∀ x, ‖((layerCut η TA σ x ^ 2 - layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
        Tq (tmult (m (R₀ σ) i) G x) (tmult (m (R₀ σ) j) Fh x) (tmult (m (R₀ σ) 2) Fw x)‖ₑ ≤
      (ENNReal.ofReal CT * Y) * ENNReal.ofReal (bLayer η TA σ x) := by
    intro σ hσ x
    have hRσ := hR₀ σ hσ
    obtain ⟨hRT, -⟩ := mem_layer'_iff.1 hRσ
    have hc0 : 0 ≤ layerCut η TA σ x := layerCut_nonneg' pd σ x
    have hc1 : layerCut η TA σ x ≤ 1 := layerCut_le_one' pd σ x
    set c := layerCut η TA σ x with hc
    have hcc : 0 ≤ c ^ 2 - c ^ 3 := by
      nlinarith [mul_nonneg hc0 hc0, mul_nonneg (mul_nonneg hc0 hc0) (sub_nonneg.2 hc1)]
    have hbL0 : 0 ≤ bLayer η TA σ x := bLayer_nonneg pd.hη (by omega) hb σ x
    have hy₀ := yNorm_nonneg' 2 (tmult (m (R₀ σ) i) G x)
    have hy₁ := yNorm_nonneg' 2 (tmult (m (R₀ σ) j) Fh x)
    have hy₂ := yNorm_nonneg' u (tmult (m (R₀ σ) 2) Fw x)
    rw [← ofReal_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcc]
    have hTb := hT (tmult (m (R₀ σ) i) G x) (tmult (m (R₀ σ) j) Fh x) (tmult (m (R₀ σ) 2) Fw x)
    have hreal := err2_real_ineq (c := c) hc0 hc1 hy₀ hy₁ hy₂ hCT (bL := bLayer η TA σ x) rfl hTb
    refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
    have hbb : ENNReal.ofReal (yNorm 2 (tmult (m (R₀ σ) i) G x)) ≤ ENNReal.ofReal (6 * 𝔭.β * 𝔭.C) * MG :=
      ofReal_yNorm_tmult_sup_le pd.h𝔭 (by norm_num) ((pd.cls _ hRT).2 i) hG hMG x
    have hhh : ENNReal.ofReal (c ^ (1 / 6 : ℝ) * yNorm 2 (tmult (m (R₀ σ) j) Fh x)) ≤ Kh * Eh := by
      have := slot_weight_bound pd (s := 2) (q := 2) (k := j) (by norm_num) (by norm_num) hFh hFhb hRσ x
      rw [hKh]; rw [← mul_assoc] at this; exact this
    have hww : ENNReal.ofReal (c ^ (1 / 6 : ℝ) * yNorm u (tmult (m (R₀ σ) 2) Fw x)) ≤ Kw * Ew := by
      have := slot_weight_bound pd (s := u) (q := R) (k := 2) (by linarith) (by linarith) hFw hFwb hRσ x
      rw [hKw]; rw [← mul_assoc] at this; exact this
    have hc12 : 0 ≤ c ^ (1 / 6 : ℝ) := Real.rpow_nonneg hc0 _
    have hp₁ : 0 ≤ c ^ (1 / 6 : ℝ) * yNorm 2 (tmult (m (R₀ σ) j) Fh x) := mul_nonneg hc12 hy₁
    have hp₂ : 0 ≤ c ^ (1 / 6 : ℝ) * yNorm u (tmult (m (R₀ σ) 2) Fw x) := mul_nonneg hc12 hy₂
    calc ENNReal.ofReal (CT * bLayer η TA σ x * yNorm 2 (tmult (m (R₀ σ) i) G x) *
          ((c ^ (1 / 6 : ℝ) * yNorm 2 (tmult (m (R₀ σ) j) Fh x)) * (c ^ (1 / 6 : ℝ) * yNorm u (tmult (m (R₀ σ) 2) Fw x))))
        = ENNReal.ofReal CT * ENNReal.ofReal (bLayer η TA σ x) * ENNReal.ofReal (yNorm 2 (tmult (m (R₀ σ) i) G x)) *
          (ENNReal.ofReal (c ^ (1 / 6 : ℝ) * yNorm 2 (tmult (m (R₀ σ) j) Fh x)) *
            ENNReal.ofReal (c ^ (1 / 6 : ℝ) * yNorm u (tmult (m (R₀ σ) 2) Fw x))) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (mul_nonneg hCT hbL0),
            ENNReal.ofReal_mul hCT, ENNReal.ofReal_mul hp₁]
      _ ≤ ENNReal.ofReal CT * ENNReal.ofReal (bLayer η TA σ x) * (ENNReal.ofReal (6 * 𝔭.β * 𝔭.C) * MG) *
          ((Kh * Eh) * (Kw * Ew)) := mul_le_mul' (mul_le_mul' le_rfl hbb) (mul_le_mul' hhh hww)
      _ = (ENNReal.ofReal CT * Y) * ENNReal.ofReal (bLayer η TA σ x) := by rw [hY]; ring
  have hbc := bLayerConst_nonneg pd.hη (by omega : 5 ≤ 𝔭.N)
  have hSh := lacSConst_nonneg pd.h𝔭t (by norm_num : (1 : ℝ) < 2) ((𝔭.N : ℝ) / 6)
  have hSw := lacSConst_nonneg pd.h𝔭t (by linarith : (1 : ℝ) < R) ((𝔭.N : ℝ) / 6)
  have hcK6 : 0 ≤ cutK 𝔭 ^ (1 / 6 : ℝ) := Real.rpow_nonneg hKp.le _
  have hKb : 0 ≤ 6 * 𝔭.β * 𝔭.C := by positivity
  have hmeas : ∀ σ, Measurable (bLayer η TA σ) := fun σ => measurable_bLayer pd.hη TA σ
  calc ‖∑ σ ∈ treeScales TA, ∫ x, ((layerCut η TA σ x ^ 2 - layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
        Tq (tmult (m (R₀ σ) i) G x) (tmult (m (R₀ σ) j) Fh x) (tmult (m (R₀ σ) 2) Fw x)‖ₑ
      ≤ ∑ σ ∈ treeScales TA, ‖∫ x, ((layerCut η TA σ x ^ 2 - layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
        Tq (tmult (m (R₀ σ) i) G x) (tmult (m (R₀ σ) j) Fh x) (tmult (m (R₀ σ) 2) Fw x)‖ₑ := enorm_sum_le _ _
    _ ≤ ∑ σ ∈ treeScales TA, (ENNReal.ofReal CT * Y) * ∫⁻ x, ENNReal.ofReal (bLayer η TA σ x) := by
        refine Finset.sum_le_sum fun σ hσ => ?_
        refine (enorm_integral_le_lintegral_enorm _).trans ?_
        calc _ ≤ ∫⁻ x, (ENNReal.ofReal CT * Y) * ENNReal.ofReal (bLayer η TA σ x) := lintegral_mono fun x => hpt σ hσ x
          _ = _ := lintegral_const_mul _ (hmeas σ).ennreal_ofReal
    _ = (ENNReal.ofReal CT * Y) * ∑ σ ∈ treeScales TA, ∫⁻ x, ENNReal.ofReal (bLayer η TA σ x) := (Finset.mul_sum _ _ _).symm
    _ ≤ (ENNReal.ofReal CT * Y) * ENNReal.ofReal (12 * bLayerConst 𝔭 * (2 : ℝ) ^ t.1.1) :=
        mul_le_mul' le_rfl (sum_lintegral_bLayer_le pd.hη (by omega) pd.good)
    _ = ENNReal.ofReal (err2Const 𝔭 R * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) * (MG * (Eh * Ew)) := by
        have hp := zpow_two_pos t.1.1
        have e1 : ENNReal.ofReal (12 * bLayerConst 𝔭 * (2 : ℝ) ^ t.1.1) =
            ENNReal.ofReal (12 * bLayerConst 𝔭) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) :=
          ENNReal.ofReal_mul (by positivity)
        have e2 : ENNReal.ofReal (err2Const 𝔭 R * CT) = ENNReal.ofReal (12 * bLayerConst 𝔭) *
            ENNReal.ofReal (6 * 𝔭.β * 𝔭.C) * (Kh * Kw) * ENNReal.ofReal CT := by
          unfold err2Const
          have h12 : 0 ≤ 12 * bLayerConst 𝔭 := by positivity
          rw [show 12 * bLayerConst 𝔭 * (6 * 𝔭.β * 𝔭.C) *
              ((cutK 𝔭 ^ (1 / 6 : ℝ) * lacSConst 𝔭 2 ((𝔭.N : ℝ) / 6)) *
                (cutK 𝔭 ^ (1 / 6 : ℝ) * lacSConst 𝔭 R ((𝔭.N : ℝ) / 6))) * CT =
            (12 * bLayerConst 𝔭 * (6 * 𝔭.β * 𝔭.C) *
              ((cutK 𝔭 ^ (1 / 6 : ℝ) * lacSConst 𝔭 2 ((𝔭.N : ℝ) / 6)) *
                (cutK 𝔭 ^ (1 / 6 : ℝ) * lacSConst 𝔭 R ((𝔭.N : ℝ) / 6)))) * CT from rfl,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul h12, ENNReal.ofReal_mul (mul_nonneg hcK6 hSh), hKh, hKw,
            ENNReal.ofReal_mul hcK6, ENNReal.ofReal_mul hcK6]
        rw [e1, e2, hY]
        ring

/-! ## ERR₁: the local `L^q(I₀)` bound of the other slots -/

/-- `χ̃_σ T_{m_σ k} F` has the local `L^q(I₀)` bound of (S) (`I₀ = dyadicInt σ v`). -/
theorem slot_Lq_bound (pd : PartData 𝔭 η η' Tr TA t χ m) {s q : ℝ} (hs : 1 ≤ s) (hq : 1 ≤ q) {k : Fin 3}
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {σ : ℤ} {R₀ : TriTile} (hR₀ : R₀ ∈ layer' TA σ) (v : ℤ) :
    eLpNorm ((dyadicInt σ v).indicator (fun x => yNorm s ((layerCut η TA σ x : ℂ) • tmult (m R₀ k) F x)))
        (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (cutK 𝔭 ^ (1 / 6 : ℝ)) * (ENNReal.ofReal (lacSqConst 𝔭 ((𝔭.N : ℝ) / 6)) *
        ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (1 / q))) * eng 𝔭.tree s k F Tr q := by
  obtain ⟨hN, -, -, hC⟩ := pd.h𝔭.bounds
  have hCpos : 0 < 𝔭.C := by linarith
  have hS := lacunary_S_Lq (q := q) hs hq pd.h𝔭t pd.hη' (η := η) pd.good pd.sub (pd.lacData k) hF (tree_N_lt pd.h𝔭) hR₀ v
  have hKp : 0 ≤ cutK 𝔭 ^ (1 / 6 : ℝ) := Real.rpow_nonneg (cutK_pos hCpos).le _
  set g : ℝ → ℝ := (dyadicInt σ v).indicator (fun x => ∑ R ∈ layer' TA σ,
        jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-((𝔭.N : ℝ) / 6)) * yNorm s (tmult (m R₀ k) F x)) with hg
  have hmeasf : Measurable ((dyadicInt σ v).indicator (fun x => yNorm s ((layerCut η TA σ x : ℂ) • tmult (m R₀ k) F x))) :=
    (((measurable_yNorm_fun s).comp (measurable_layer_vec pd hF hR₀))).indicator (measurableSet_dyadicInt σ v)
  have hpt : ∀ x, ‖(dyadicInt σ v).indicator (fun x => yNorm s ((layerCut η TA σ x : ℂ) • tmult (m R₀ k) F x)) x‖ ≤
      ‖(cutK 𝔭 ^ (1 / 6 : ℝ)) • g x‖ := by
    intro x
    by_cases hx : x ∈ dyadicInt σ v
    · simp only [hg, Set.indicator_of_mem hx]
      have hy := yNorm_nonneg' s (tmult (m R₀ k) F x)
      have hc0 := layerCut_nonneg' pd σ x
      have hc1 := layerCut_le_one' pd σ x
      have hnn : 0 ≤ cutK 𝔭 ^ (1 / 6 : ℝ) * ∑ R ∈ layer' TA σ,
          jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-((𝔭.N : ℝ) / 6)) * yNorm s (tmult (m R₀ k) F x) :=
        mul_nonneg hKp (Finset.sum_nonneg fun R _ =>
          mul_nonneg (Real.rpow_nonneg (jb_pos _).le _) hy)
      rw [Real.norm_of_nonneg (yNorm_nonneg' _ _), yNorm_csmul (by linarith), Complex.norm_real,
        Real.norm_of_nonneg hc0, smul_eq_mul, Real.norm_of_nonneg hnn]
      have hw := layerCut_rpow_le pd.hη hCpos TA σ x (a := 1 / 6) (by norm_num) (by norm_num)
      have e : (𝔭.N : ℝ) * (1 / 6) = (𝔭.N : ℝ) / 6 := by ring
      rw [e] at hw
      have hcle : layerCut η TA σ x ≤ layerCut η TA σ x ^ (1 / 6 : ℝ) := by
        rcases hc0.eq_or_lt with h | h
        · rw [← h]; simp
        · calc layerCut η TA σ x = layerCut η TA σ x ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge h hc1 (by norm_num)
      calc layerCut η TA σ x * yNorm s (tmult (m R₀ k) F x) ≤ (cutK 𝔭 ^ (1 / 6 : ℝ) * ∑ R ∈ layer' TA σ,
            jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-((𝔭.N : ℝ) / 6))) * yNorm s (tmult (m R₀ k) F x) :=
          mul_le_mul_of_nonneg_right (hcle.trans hw) hy
        _ = _ := by rw [mul_assoc, Finset.sum_mul]
    · simp [hg, Set.indicator_of_notMem hx]
  have h1 : eLpNorm ((dyadicInt σ v).indicator (fun x => yNorm s ((layerCut η TA σ x : ℂ) • tmult (m R₀ k) F x)))
      (ENNReal.ofReal q) volume ≤ eLpNorm ((cutK 𝔭 ^ (1 / 6 : ℝ)) • g) (ENNReal.ofReal q) volume :=
    eLpNorm_mono hmeasf.aestronglyMeasurable (fun x => hpt x)
  rw [eLpNorm_const_smul] at h1
  refine h1.trans ?_
  rw [Real.enorm_eq_ofReal hKp, mul_assoc, mul_assoc]
  refine mul_le_mul' le_rfl ?_
  have := hS
  rw [mul_assoc] at this
  exact this

/-! ## Interpolation between `L²` and `L^∞` -/

theorem eLpNorm_interp_le {f : ℝ → ℝ≥0∞} (hf : Measurable f) {A E : ℝ≥0∞} {H : ℝ} (hH : 0 < H)
    (hS : ∀ x, f x ≤ A * E) (h2 : eLpNorm f (ENNReal.ofReal 2) volume ≤ A * ENNReal.ofReal (H ^ (1 / 2 : ℝ)) * E)
    {p : ℝ} (hp : 2 ≤ p) :
    eLpNorm f (ENNReal.ofReal p) volume ≤ A * ENNReal.ofReal (H ^ (1 / p)) * E := by
  have hp0 : 0 < p := by linarith
  have hf2 : eLpNorm f (ENNReal.ofReal 2) volume = (∫⁻ x, f x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
    eLpNorm_ofReal_eq_lintegral (by norm_num) hf
  have hI2 : ∫⁻ x, f x ^ (2 : ℝ) ≤ (A * ENNReal.ofReal (H ^ (1 / 2 : ℝ)) * E) ^ (2 : ℝ) := by
    have := ENNReal.rpow_le_rpow h2 (by norm_num : (0 : ℝ) ≤ 2)
    rw [hf2, ← ENNReal.rpow_mul] at this
    simpa using this
  rw [eLpNorm_ofReal_eq_lintegral hp0 hf]
  have hIp : ∫⁻ x, f x ^ p ≤ (A * E) ^ (p - 2) * ∫⁻ x, f x ^ (2 : ℝ) := by
    rw [← lintegral_const_mul _ (hf.pow_const _)]
    refine lintegral_mono fun x => ?_
    have : f x ^ p = f x ^ (p - 2) * f x ^ (2 : ℝ) := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by norm_num)]; congr 1; ring
    rw [this]
    exact mul_le_mul' (ENNReal.rpow_le_rpow (hS x) (by linarith)) le_rfl
  have h3 : (∫⁻ x, f x ^ p) ^ (1 / p) ≤ ((A * E) ^ (p - 2) * (A * ENNReal.ofReal (H ^ (1 / 2 : ℝ)) * E) ^ (2 : ℝ)) ^ (1 / p) :=
    ENNReal.rpow_le_rpow (hIp.trans (mul_le_mul' le_rfl hI2)) (by positivity)
  refine h3.trans (le_of_eq ?_)
  have hp1 : 0 ≤ 1 / p := by positivity
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp1, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  have e1 : (A * ENNReal.ofReal (H ^ (1 / 2 : ℝ)) * E) = (A * E) * ENNReal.ofReal (H ^ (1 / 2 : ℝ)) := by ring
  have hq0 : (0 : ℝ) ≤ 2 * (1 / p) := by positivity
  have hq1 : (0 : ℝ) ≤ (p - 2) * (1 / p) := mul_nonneg (by linarith) hp1
  rw [e1, ENNReal.mul_rpow_of_nonneg _ _ hq0, ← mul_assoc,
    ← ENNReal.rpow_add_of_nonneg _ _ hq1 hq0]
  have e2 : (p - 2) * (1 / p) + 2 * (1 / p) = 1 := by field_simp; ring
  rw [e2, ENNReal.rpow_one, ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hH.le _) hq0,
    ← Real.rpow_mul hH.le]
  have e3 : 1 / 2 * (2 * (1 / p)) = 1 / p := by ring
  rw [e3]; ring

theorem eLpNorm_ofReal_fun {f : ℝ → ℝ} (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (p : ℝ≥0∞) :
    eLpNorm (fun x => ENNReal.ofReal (f x)) p volume = eLpNorm f p volume := by
  rw [← eLpNorm_enorm f hf.aestronglyMeasurable]
  congr 1
  funext x
  exact (Real.enorm_eq_ofReal (h0 x)).symm

theorem ofReal_ind_eLp {f : ℝ → ZMod P → ℂ} (hf : Measurable f) {I : Set ℝ} (hI : MeasurableSet I) (s : ℝ)
    (p : ℝ≥0∞) :
    eLpNorm (fun x => ENNReal.ofReal (I.indicator (fun x => yNorm s (f x)) x)) p volume =
      eLpNorm (I.indicator (fun x => yNorm s (f x))) p volume := by
  refine eLpNorm_ofReal_fun (((measurable_yNorm_fun s).comp hf).indicator hI) (fun x => ?_) p
  by_cases hx : x ∈ I
  · rw [Set.indicator_of_mem hx]; exact yNorm_nonneg' _ _
  · rw [Set.indicator_of_notMem hx]

/-- The constant of ERR₁ (per slot). -/
def err1K (𝔭 : Params) : ℝ := cutK 𝔭 ^ (1 / 6 : ℝ) * lacSqConst 𝔭 ((𝔭.N : ℝ) / 6)

theorem err1K_nonneg {𝔭 : Params} (h𝔭 : 𝔭.Admissible) : 0 ≤ err1K 𝔭 := by
  obtain ⟨hN, -, -, hC⟩ := h𝔭.bounds
  have hK := cutK_pos (by linarith : 0 < 𝔭.C)
  unfold err1K lacSqConst
  have : 0 ≤ ((3 : ℝ) / 2) ^ ((𝔭.N : ℝ) / 6 - (𝔭.tree.N : ℝ)) * (𝔭.tree.C * ((3 : ℝ) / 2) ^ (2 * (𝔭.tree.N : ℝ))) *
      (2 ^ ((𝔭.N : ℝ) / 6 - (𝔭.tree.N : ℝ)) * jbConst ((𝔭.N : ℝ) / 6 - (𝔭.tree.N : ℝ))) := by
    have hjb := jbConst_nonneg ((𝔭.N : ℝ) / 6 - (𝔭.tree.N : ℝ))
    have hC' : (0 : ℝ) ≤ 𝔭.tree.C := by show (0 : ℝ) ≤ 𝔭.C; linarith
    positivity
  have := Real.rpow_nonneg hK.le (1 / 6 : ℝ)
  positivity

/-- **ERR₁, local**: on `I₀ = dyadicInt σ v`, Hölder `(p₀, 2, R)` with the `O2` bound for the overlapping slot. -/
theorem err1_local (pd : PartData 𝔭 η η' Tr TA t χ m) {Tq : Form P} {u R CT : ℝ} (hu : 1 < u) (hR : 2 < R)
    (hT : FormBound u Tq CT) {j : Fin 3} {Fh Fw : ℝ → ZMod P → ℂ} (hFh : Measurable Fh) (hFw : Measurable Fw)
    {U : ℝ → ZMod P → ℂ} (hU : Measurable U) {σ : ℤ} {R₀ : TriTile} (hR₀ : R₀ ∈ layer' TA σ) (v : ℤ) {C a : ℝ}
    (hC : 0 ≤ C) (ha : 0 ≤ a) {Eo : ℝ≥0∞} (hO : OvBound 2 2 C a Eo σ v U) :
    ∫⁻ x in dyadicInt σ v, ‖Tq (U x) ((layerCut η TA σ x : ℂ) • tmult (m R₀ j) Fh x)
        ((layerCut η TA σ x : ℂ) • tmult (m R₀ 2) Fw x)‖ₑ ≤
      ENNReal.ofReal CT * (ENNReal.ofReal (C * a) * ENNReal.ofReal ((2 : ℝ) ^ σ)) *
        (ENNReal.ofReal (err1K 𝔭) * ENNReal.ofReal (err1K 𝔭)) *
        (Eo * (eng 𝔭.tree 2 j Fh Tr 2 * eng 𝔭.tree u 2 Fw Tr R)) := by
  have hCT : 0 ≤ CT := nonneg_of_formBound (by linarith) hT
  have hp := zpow_two_pos σ
  set ℓh : ℝ → ZMod P → ℂ := fun x => (layerCut η TA σ x : ℂ) • tmult (m R₀ j) Fh x with hℓh
  set ℓw : ℝ → ZMod P → ℂ := fun x => (layerCut η TA σ x : ℂ) • tmult (m R₀ 2) Fw x with hℓw
  have hmh : Measurable ℓh := measurable_layer_vec pd hFh hR₀
  have hmw : Measurable ℓw := measurable_layer_vec pd hFw hR₀
  set I := dyadicInt σ v with hI
  have hIm : MeasurableSet I := measurableSet_dyadicInt σ v
  set a₀ : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (I.indicator (fun x => yNorm 2 (U x)) x) with ha₀
  set b₀ : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (I.indicator (fun x => yNorm 2 (ℓh x)) x) with hb₀
  set c₀ : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (I.indicator (fun x => yNorm u (ℓw x)) x) with hc₀
  have hma : Measurable a₀ := ENNReal.measurable_ofReal.comp (((measurable_yNorm_fun 2).comp hU).indicator hIm)
  have hmb : Measurable b₀ := ENNReal.measurable_ofReal.comp (((measurable_yNorm_fun 2).comp hmh).indicator hIm)
  have hmc : Measurable c₀ := ENNReal.measurable_ofReal.comp (((measurable_yNorm_fun u).comp hmw).indicator hIm)
  -- pointwise bound by `CT a₀ b₀ c₀`
  have hpt : ∀ x, I.indicator (fun x => ‖Tq (U x) (ℓh x) (ℓw x)‖ₑ) x ≤ ENNReal.ofReal CT * (a₀ x * b₀ x * c₀ x) := by
    intro x
    by_cases hx : x ∈ I
    · simp only [Set.indicator_of_mem hx, ha₀, hb₀, hc₀]
      rw [← ofReal_norm]
      refine (ENNReal.ofReal_le_ofReal (hT (U x) (ℓh x) (ℓw x))).trans (le_of_eq ?_)
      have h0 := yNorm_nonneg' 2 (U x)
      have h1 := yNorm_nonneg' 2 (ℓh x)
      have h2 := yNorm_nonneg' u (ℓw x)
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hCT]
      ring
    · simp [Set.indicator_of_notMem hx, ha₀, hb₀, hc₀]
  rw [← lintegral_indicator hIm]
  have hp₀ : 0 < 2 * R / (R - 2) := by apply div_pos <;> linarith
  have hp₀2 : 2 ≤ 2 * R / (R - 2) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hsum : 1 / (2 * R / (R - 2)) + 1 / 2 + 1 / R = 1 := by
    field_simp; ring
  have hH := lintegral_mul_three_le hp₀ (by norm_num : (0 : ℝ) < 2) (by linarith : 0 < R) hsum hma hmb hmc
  calc ∫⁻ x, I.indicator (fun x => ‖Tq (U x) (ℓh x) (ℓw x)‖ₑ) x
      ≤ ∫⁻ x, ENNReal.ofReal CT * (a₀ x * b₀ x * c₀ x) := lintegral_mono hpt
    _ = ENNReal.ofReal CT * ∫⁻ x, a₀ x * b₀ x * c₀ x := by
        exact lintegral_const_mul (ENNReal.ofReal CT) (f := fun x => a₀ x * b₀ x * c₀ x) ((hma.mul hmb).mul hmc)
    _ ≤ ENNReal.ofReal CT * (eLpNorm a₀ (ENNReal.ofReal (2 * R / (R - 2))) volume * eLpNorm b₀ (ENNReal.ofReal 2) volume *
          eLpNorm c₀ (ENNReal.ofReal R) volume) := mul_le_mul' le_rfl hH
    _ ≤ ENNReal.ofReal CT * ((ENNReal.ofReal (C * a) * ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (1 / (2 * R / (R - 2)))) * Eo) *
          (ENNReal.ofReal (cutK 𝔭 ^ (1 / 6 : ℝ)) * (ENNReal.ofReal (lacSqConst 𝔭 ((𝔭.N : ℝ) / 6)) *
            ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (1 / (2 : ℝ)))) * eng 𝔭.tree 2 j Fh Tr 2) *
          (ENNReal.ofReal (cutK 𝔭 ^ (1 / 6 : ℝ)) * (ENNReal.ofReal (lacSqConst 𝔭 ((𝔭.N : ℝ) / 6)) *
            ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (1 / R))) * eng 𝔭.tree u 2 Fw Tr R)) := by
        refine mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' ?_ ?_) ?_)
        · -- the overlapping slot: interpolation
          have hf0 : ∀ x, 0 ≤ I.indicator (fun x => yNorm 2 (U x)) x := fun x => by
            by_cases hx : x ∈ I
            · rw [Set.indicator_of_mem hx]; exact yNorm_nonneg' _ _
            · rw [Set.indicator_of_notMem hx]
          have hmf : Measurable (I.indicator (fun x => yNorm 2 (U x))) := ((measurable_yNorm_fun 2).comp hU).indicator hIm
          have hS : ∀ x, a₀ x ≤ ENNReal.ofReal (C * a) * Eo := by
            intro x
            by_cases hx : x ∈ I
            · simp only [ha₀, Set.indicator_of_mem hx]; exact hO.1 x hx
            · simp [ha₀, Set.indicator_of_notMem hx]
          have h2 : eLpNorm a₀ (ENNReal.ofReal 2) volume ≤
              ENNReal.ofReal (C * a) * ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (1 / (2 : ℝ))) * Eo := by
            have := hO.2
            rw [show a₀ = fun x => ENNReal.ofReal (I.indicator (fun x => yNorm 2 (U x)) x) from rfl,
              eLpNorm_ofReal_fun hmf hf0]
            refine this.trans (le_of_eq ?_)
            rw [ENNReal.ofReal_mul (mul_nonneg hC ha)]
          exact eLpNorm_interp_le hma hp (by simpa using hS) (by simpa using h2) hp₀2
        · have := slot_Lq_bound pd (s := 2) (q := 2) (k := j) (by norm_num) (by norm_num) hFh hR₀ v
          rw [show b₀ = fun x => ENNReal.ofReal (I.indicator (fun x => yNorm 2 (ℓh x)) x) from rfl,
            ofReal_ind_eLp hmh hIm 2 _]
          exact this
        · have := slot_Lq_bound pd (s := u) (q := R) (k := 2) (by linarith) (by linarith) hFw hR₀ v
          rw [show c₀ = fun x => ENNReal.ofReal (I.indicator (fun x => yNorm u (ℓw x)) x) from rfl,
            ofReal_ind_eLp hmw hIm u _]
          exact this
    _ = _ := by
        have hKp : 0 ≤ cutK 𝔭 ^ (1 / 6 : ℝ) := Real.rpow_nonneg (cutK_pos (by
          obtain ⟨-, -, -, hC1⟩ := pd.h𝔭.bounds; linarith : 0 < 𝔭.C)).le _
        have hH3 : ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (1 / (2 * R / (R - 2)))) * ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (1 / (2 : ℝ))) *
            ENNReal.ofReal (((2 : ℝ) ^ σ) ^ (1 / R)) = ENNReal.ofReal ((2 : ℝ) ^ σ) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hp.le _), ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hp.le _)
            (Real.rpow_nonneg hp.le _)), ← Real.rpow_add hp, ← Real.rpow_add hp, hsum, Real.rpow_one]
        have hK : ENNReal.ofReal (err1K 𝔭) = ENNReal.ofReal (cutK 𝔭 ^ (1 / 6 : ℝ)) * ENNReal.ofReal (lacSqConst 𝔭 ((𝔭.N : ℝ) / 6)) :=
          ENNReal.ofReal_mul hKp
        rw [hK, ← hH3]
        ring

/-- The constant of ERR₁. -/
def err1Const (𝔭 : Params) (C Ca : ℝ) : ℝ := C * Ca * err1K 𝔭 ^ 2

/-- **ERR₁**: `‖Σ_σ ∫ χ̃³ Π(T_{m_σ i}(F_o - G), a_h, a_w)‖ ≤ C CT |I_t| E_o E_h E_w`, from the `O2` bound of the overlapping slot on every
`σ`-interval, with `Σ_σ Σ_v 2^σ a_{σ,v} ≤ C_a |I_t|`. -/
theorem err1_bound (pd : PartData 𝔭 η η' Tr TA t χ m) {Tq : Form P} {u R CT : ℝ} (hu : 1 < u) (hR : 2 < R)
    (hT : FormBound u Tq CT) {i j : Fin 3} {Fo Fh Fw G : ℝ → ZMod P → ℂ} (hFo : Measurable Fo) (hFh : Measurable Fh)
    (hFw : Measurable Fw) (hG : Measurable G) (R₀ : ℤ → TriTile) (hR₀ : ∀ σ ∈ treeScales TA, R₀ σ ∈ layer' TA σ)
    {C : ℝ} (hC : 0 ≤ C) {Eo : ℝ≥0∞} (a : ℤ → ℤ → ℝ) (ha : ∀ σ v, 0 ≤ a σ v)
    (hO : ∀ σ ∈ treeScales TA, ∀ v : ℤ, OvBound 2 2 C (a σ v) Eo σ v
      (fun x => (layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) i) (Fo - G) x))
    {Ca : ℝ} (hCa : 0 ≤ Ca)
    (hsum : ∑ σ ∈ treeScales TA, ∑' v : ℤ, ENNReal.ofReal ((2 : ℝ) ^ σ * a σ v) ≤ ENNReal.ofReal (Ca * (2 : ℝ) ^ t.1.1)) :
    ‖∑ σ ∈ treeScales TA, ∫ x, ((layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
        Tq (tmult (m (R₀ σ) i) (Fo - G) x) (tmult (m (R₀ σ) j) Fh x) (tmult (m (R₀ σ) 2) Fw x)‖ₑ ≤
      ENNReal.ofReal (err1Const 𝔭 C Ca * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) *
        (Eo * (eng 𝔭.tree 2 j Fh Tr 2 * eng 𝔭.tree u 2 Fw Tr R)) := by
  have hCT : 0 ≤ CT := nonneg_of_formBound (by linarith) hT
  have hK0 := err1K_nonneg pd.h𝔭
  set E3 : ℝ≥0∞ := Eo * (eng 𝔭.tree 2 j Fh Tr 2 * eng 𝔭.tree u 2 Fw Tr R) with hE3
  set K2 : ℝ≥0∞ := ENNReal.ofReal (err1K 𝔭) * ENNReal.ofReal (err1K 𝔭) with hK2
  set M0 : ℝ≥0∞ := ENNReal.ofReal CT * K2 * E3 * ENNReal.ofReal C with hM0
  have hlocal : ∀ σ ∈ treeScales TA, ‖∫ x, ((layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
        Tq (tmult (m (R₀ σ) i) (Fo - G) x) (tmult (m (R₀ σ) j) Fh x) (tmult (m (R₀ σ) 2) Fw x)‖ₑ ≤
      M0 * ∑' v : ℤ, ENNReal.ofReal ((2 : ℝ) ^ σ * a σ v) := by
    intro σ hσ
    have hRσ := hR₀ σ hσ
    have hU : Measurable (fun x => (layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) i) (Fo - G) x) :=
      measurable_layer_vec pd (hFo.sub hG) hRσ
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have e : ∀ x, ‖((layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
        Tq (tmult (m (R₀ σ) i) (Fo - G) x) (tmult (m (R₀ σ) j) Fh x) (tmult (m (R₀ σ) 2) Fw x)‖ₑ =
        ‖Tq ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) i) (Fo - G) x) ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) j) Fh x)
          ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) 2) Fw x)‖ₑ := fun x => by rw [Form_smul3]
    simp_rw [e]
    have hU' : (⋃ v : ℤ, dyadicInt σ v) = Set.univ := by
      ext x; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      exact ⟨⌊x / (2 : ℝ) ^ σ⌋, mem_dyadicInt_floor σ x⟩
    have hdisj : Pairwise (Function.onFun Disjoint fun v : ℤ => dyadicInt σ v) := by
      intro v v' hne
      rcases dyadicInt_nested_or_disjoint σ v σ v' with h | h | h
      · exact absurd (index_eq_of_dyadicInt_subset rfl h) hne
      · exact absurd (index_eq_of_dyadicInt_subset rfl h).symm hne
      · exact h
    have hsplit := lintegral_iUnion (μ := volume) (fun v : ℤ => measurableSet_dyadicInt σ v) hdisj
      (fun x => ‖Tq ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) i) (Fo - G) x)
        ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) j) Fh x) ((layerCut η TA σ x : ℂ) • tmult (m (R₀ σ) 2) Fw x)‖ₑ)
    rw [hU', Measure.restrict_univ] at hsplit
    rw [hsplit, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun v => ?_
    refine (err1_local pd hu hR hT (j := j) hFh hFw hU hRσ v hC (ha σ v) (hO σ hσ v)).trans (le_of_eq ?_)
    have h2 : ENNReal.ofReal ((2 : ℝ) ^ σ * a σ v) = ENNReal.ofReal ((2 : ℝ) ^ σ) * ENNReal.ofReal (a σ v) :=
      ENNReal.ofReal_mul (zpow_two_pos σ).le
    rw [hM0, hK2, h2, ENNReal.ofReal_mul hC, hE3]
    ring
  calc ‖∑ σ ∈ treeScales TA, ∫ x, ((layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
        Tq (tmult (m (R₀ σ) i) (Fo - G) x) (tmult (m (R₀ σ) j) Fh x) (tmult (m (R₀ σ) 2) Fw x)‖ₑ
      ≤ ∑ σ ∈ treeScales TA, ‖∫ x, ((layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
        Tq (tmult (m (R₀ σ) i) (Fo - G) x) (tmult (m (R₀ σ) j) Fh x) (tmult (m (R₀ σ) 2) Fw x)‖ₑ := enorm_sum_le _ _
    _ ≤ ∑ σ ∈ treeScales TA, M0 * ∑' v : ℤ, ENNReal.ofReal ((2 : ℝ) ^ σ * a σ v) := Finset.sum_le_sum hlocal
    _ = M0 * ∑ σ ∈ treeScales TA, ∑' v : ℤ, ENNReal.ofReal ((2 : ℝ) ^ σ * a σ v) := (Finset.mul_sum _ _ _).symm
    _ ≤ M0 * ENNReal.ofReal (Ca * (2 : ℝ) ^ t.1.1) := mul_le_mul' le_rfl hsum
    _ = ENNReal.ofReal (err1Const 𝔭 C Ca * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) * E3 := by
        have hp := zpow_two_pos t.1.1
        have e1 : ENNReal.ofReal (Ca * (2 : ℝ) ^ t.1.1) = ENNReal.ofReal Ca * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) :=
          ENNReal.ofReal_mul hCa
        have e2 : ENNReal.ofReal (err1Const 𝔭 C Ca * CT) = ENNReal.ofReal C * ENNReal.ofReal Ca * K2 * ENNReal.ofReal CT := by
          unfold err1Const
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hC,
            show err1K 𝔭 ^ 2 = err1K 𝔭 * err1K 𝔭 by ring, ENNReal.ofReal_mul hK0, hK2]
        rw [e1, e2, hM0]
        ring

end Asm

end PrimeBHT.TimeFrequency.X2
