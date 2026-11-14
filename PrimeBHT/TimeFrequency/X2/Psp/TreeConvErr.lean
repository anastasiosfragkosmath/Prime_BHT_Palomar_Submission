module

public import PrimeBHT.TimeFrequency.X2.Psp.TreeConv
public import PrimeBHT.TimeFrequency.X2.V16.Hyps
public import PrimeBHT.TimeFrequency.X2.Paraproduct
public import PrimeBHT.TimeFrequency.X2.Psp.LacunaryLinf

/-!
# X2, V15 (assembly), step 2': the conversion error `Σ_σ ∫ (χ̃_σ - χ̃_σ³) Π(T_{m_σ0}F₀, T_{m_σ1}F₁, T_{m_σ2}F₂)`

(MTT2 Lemma 7.3; route check §4 step 2.)  With `bLayer = χ̃^{1/2}(1 - χ̃)`: `χ̃ - χ̃³ ≤ 2 bLayer (χ̃^{1/6})³`, the single-scale sup
bound (S) (`lacunary_S_sup`, `N_w = N/6`) in each slot, and `Σ_σ ∫ bLayer ≤ C |I_t|` (`sum_lintegral_bLayer_le`):
`‖Σ_σ ∫ (χ̃ - χ̃³) Π(…)‖ ≤ C CT |I_t| ∏_k eng_k`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-- The data of a part `TA` of a tree `Tr`: the model data restricted to `TA`, the two profiles `η` (class `𝔭`, of the cutoffs)
and `η'` (class `𝔭.tree`, for the domination arguments), `TA` a good tree. -/
structure PartData (𝔭 : Params) (η η' : ℝ → ℝ) (Tr TA : Finset TriTile) (t : Top) (χ : TriTile → ℝ → ℝ)
    (m : TriTile → Fin 3 → ℝ → ℂ) : Prop where
  h𝔭 : 𝔭.Admissible
  h𝔭t : 𝔭.tree.Admissible
  hη : IsEtaCut 𝔭 η
  hη' : IsEtaCut 𝔭.tree η'
  sub : TA ⊆ Tr
  good : IsGoodTree TA t
  cons : ∀ Q ∈ TA, ∀ Q' ∈ TA, Q.box = Q'.box → m Q = m Q'
  cut : ∀ Q ∈ TA, χ Q = tileCutoff η Q.box.scale Q.pos
  cls : ∀ Q ∈ TA, InX 𝔭 Q.box.scale Q.pos (χ Q) ∧ ∀ k, InMult 𝔭 Q.box.scale (Q.box.centre k) (m Q k)

theorem PartData.lacData {𝔭 : Params} {η η' : ℝ → ℝ} {Tr TA : Finset TriTile} {t : Top} {χ : TriTile → ℝ → ℝ}
    {m : TriTile → Fin 3 → ℝ → ℂ} (h : PartData 𝔭 η η' Tr TA t χ m) (k : Fin 3) : LacData 𝔭 TA k η χ m :=
  ⟨fun R hR => (h.cls R hR).1.1, fun R hR => (h.cls R hR).2 k, fun R hR R' hR' hb => by rw [h.cons R hR R' hR' hb],
    h.cut⟩

theorem PartData.goodModel {𝔭 : Params} {η η' : ℝ → ℝ} {Tr TA : Finset TriTile} {t : Top} {χ : TriTile → ℝ → ℝ}
    {m : TriTile → Fin 3 → ℝ → ℂ} (h : PartData 𝔭 η η' Tr TA t χ m) : GoodModel TA χ m :=
  goodModel_of_isModelData h.h𝔭 ⟨h.cls, h.cons, η, h.hη, h.cut⟩

theorem PartData.mono {𝔭 : Params} {η η' : ℝ → ℝ} {Tr TA TB : Finset TriTile} {t : Top} {χ : TriTile → ℝ → ℝ}
    {m : TriTile → Fin 3 → ℝ → ℂ} (h : PartData 𝔭 η η' Tr TA t χ m) (hB : TB ⊆ TA) (hg : IsGoodTree TB t) :
    PartData 𝔭 η η' Tr TB t χ m :=
  ⟨h.h𝔭, h.h𝔭t, h.hη, h.hη', hB.trans h.sub, hg, fun Q hQ Q' hQ' => h.cons Q (hB hQ) Q' (hB hQ'),
    fun Q hQ => h.cut Q (hB hQ), fun Q hQ => h.cls Q (hB hQ)⟩

/-! ## The weights: `χ̃^{1/6} ‖T_{m_σ}F‖` is bounded by the energy (S) -/

theorem tree_N_lt {𝔭 : Params} (h𝔭 : 𝔭.Admissible) : (𝔭.tree.N : ℝ) + 1 < (𝔭.N : ℝ) / 6 := by
  obtain ⟨hN, -, -, -⟩ := h𝔭.bounds
  have h1 : (400 : ℝ) ≤ 𝔭.N := by exact_mod_cast hN
  have h2 : ((𝔭.N / 8 : ℕ) : ℝ) ≤ (𝔭.N : ℝ) / 8 := Nat.cast_div_le
  rw [Params.tree_N]
  linarith

theorem slot_weight_bound {𝔭 : Params} {η η' : ℝ → ℝ} {Tr TA : Finset TriTile} {t : Top} {χ : TriTile → ℝ → ℝ}
    {m : TriTile → Fin 3 → ℝ → ℂ} (pd : PartData 𝔭 η η' Tr TA t χ m) {P : ℕ} [NeZero P] {s q : ℝ} (hs : 1 ≤ s)
    (hq : 1 < q) {k : Fin 3} {F : ℝ → ZMod P → ℂ} (hF : Measurable F) (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) {σ : ℤ}
    {R₀ : TriTile} (hR₀ : R₀ ∈ layer' TA σ) (x : ℝ) :
    ENNReal.ofReal (layerCut η TA σ x ^ (1 / 6 : ℝ) * yNorm s (tmult (m R₀ k) F x)) ≤
      ENNReal.ofReal (cutK 𝔭 ^ (1 / 6 : ℝ)) *
        (ENNReal.ofReal (lacSConst 𝔭 q ((𝔭.N : ℝ) / 6)) * eng 𝔭.tree s k F Tr q) := by
  obtain ⟨hN, -, -, hC⟩ := pd.h𝔭.bounds
  have hCpos : 0 < 𝔭.C := by linarith
  have hS := lacunary_S_sup (q := q) hs hq pd.h𝔭t pd.hη' (η := η) pd.good pd.sub (pd.lacData k) hF hFb
    (tree_N_lt pd.h𝔭) hR₀ x
  have hw := layerCut_rpow_le pd.hη hCpos TA σ x (a := 1 / 6) (by norm_num) (by norm_num)
  have e : (𝔭.N : ℝ) * (1 / 6) = (𝔭.N : ℝ) / 6 := by ring
  rw [e] at hw
  have hy := yNorm_nonneg' s (tmult (m R₀ k) F x)
  have hK := cutK_pos hCpos
  have hKp : 0 ≤ cutK 𝔭 ^ (1 / 6 : ℝ) := Real.rpow_nonneg hK.le _
  calc ENNReal.ofReal (layerCut η TA σ x ^ (1 / 6 : ℝ) * yNorm s (tmult (m R₀ k) F x))
      ≤ ENNReal.ofReal (cutK 𝔭 ^ (1 / 6 : ℝ) * ∑ R ∈ layer' TA σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^
          (-((𝔭.N : ℝ) / 6)) * yNorm s (tmult (m R₀ k) F x)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : ∑ R ∈ layer' TA σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-((𝔭.N : ℝ) / 6)) *
            yNorm s (tmult (m R₀ k) F x) = (∑ R ∈ layer' TA σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^
              (-((𝔭.N : ℝ) / 6))) * yNorm s (tmult (m R₀ k) F x) := by rw [Finset.sum_mul]
        rw [this, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hw hy
    _ = ENNReal.ofReal (cutK 𝔭 ^ (1 / 6 : ℝ)) * ENNReal.ofReal (∑ R ∈ layer' TA σ,
          jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-((𝔭.N : ℝ) / 6)) * yNorm s (tmult (m R₀ k) F x)) := by
        rw [← ENNReal.ofReal_mul hKp]
    _ ≤ _ := mul_le_mul' le_rfl hS

/-! ## The conversion error -/

theorem conv_real_ineq {c y₀ y₁ y₂ CT bL t : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hy₀ : 0 ≤ y₀) (hy₁ : 0 ≤ y₁)
    (hy₂ : 0 ≤ y₂) (hCT : 0 ≤ CT) (hbL : bL = c ^ (1 / 2 : ℝ) * (1 - c)) (ht : t ≤ CT * y₀ * y₁ * y₂) :
    (c - c ^ 3) * t ≤ 2 * CT * bL * ((c ^ (1 / 6 : ℝ) * y₀) * (c ^ (1 / 6 : ℝ) * y₁) * (c ^ (1 / 6 : ℝ) * y₂)) := by
  set u : ℝ := c ^ (1 / 6 : ℝ) with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg hc0 _
  have hc : c = u ^ 6 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hc0]; norm_num
  have hh : c ^ (1 / 2 : ℝ) = u ^ 3 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hc0]; norm_num
  rw [hh] at hbL
  have hu1 : u ≤ 1 := by
    by_contra h; push Not at h
    have : 1 < u ^ 6 := one_lt_pow₀ h (by norm_num)
    linarith
  have hcc3 : 0 ≤ c - c ^ 3 := by nlinarith [mul_nonneg hc0 (sub_nonneg.2 hc1), mul_nonneg hc0 hc0]
  have h1 : (c - c ^ 3) * t ≤ (c - c ^ 3) * (CT * y₀ * y₁ * y₂) := mul_le_mul_of_nonneg_left ht hcc3
  have h2 : c - c ^ 3 ≤ 2 * (u ^ 3 * (u ^ 3 * (1 - c))) := by
    rw [hc]
    have : 0 ≤ u ^ 6 := by positivity
    have h6 : u ^ 6 ≤ 1 := by rw [← hc]; exact hc1
    nlinarith [mul_nonneg this (sub_nonneg.2 h6), mul_nonneg (mul_nonneg this (sub_nonneg.2 h6)) this]
  have h3 : 0 ≤ CT * y₀ * y₁ * y₂ := by positivity
  calc (c - c ^ 3) * t ≤ (c - c ^ 3) * (CT * y₀ * y₁ * y₂) := h1
    _ ≤ (2 * (u ^ 3 * (u ^ 3 * (1 - c)))) * (CT * y₀ * y₁ * y₂) := mul_le_mul_of_nonneg_right h2 h3
    _ = _ := by rw [hbL]; ring

theorem slotExp_ge_one {u : ℝ} (hu : 1 < u) (k : Fin 3) : 1 ≤ slotExp u k := by
  unfold slotExp; split_ifs <;> linarith

theorem qv_gt_one {R : ℝ} (hR : 2 < R) (k : Fin 3) : 1 < qv R k := by
  unfold qv; split_ifs <;> linarith

/-- **The conversion error, pointwise** (MTT2 Lemma 7.3 integrand): `(χ̃ - χ̃³) Π(…) ≤ 2 CT β_σ ∏_k (χ̃^{1/6}‖T_{m_σ k}F_k‖)`,
with each factor `≤ C eng_k` by (S). -/
theorem conv_pointwise {𝔭 : Params} {η η' : ℝ → ℝ} {Tr TA : Finset TriTile} {t : Top} {χ : TriTile → ℝ → ℝ}
    {m : TriTile → Fin 3 → ℝ → ℂ} (pd : PartData 𝔭 η η' Tr TA t χ m) {P : ℕ} [NeZero P] {u R : ℝ} (hu : 1 < u)
    (hR : 2 < R) {T : Form P} {CT : ℝ} (hT : FormBound u T CT) {F : Fin 3 → ℝ → ZMod P → ℂ}
    (hF : ∀ k, Measurable (F k)) (hFb : ∀ k, ∃ B, ∀ x, yNorm 2 (F k x) ≤ B) {σ : ℤ} {R₀ : TriTile}
    (hR₀ : R₀ ∈ layer' TA σ) (x : ℝ) :
    ‖((layerCut η TA σ x - layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
        T (tmult (m R₀ 0) (F 0) x) (tmult (m R₀ 1) (F 1) x) (tmult (m R₀ 2) (F 2) x)‖ₑ ≤
      ENNReal.ofReal (2 * CT) * ENNReal.ofReal (bLayer η TA σ x) *
        ∏ k : Fin 3, (ENNReal.ofReal (cutK 𝔭 ^ (1 / 6 : ℝ)) *
          (ENNReal.ofReal (lacSConst 𝔭 (qv R k) ((𝔭.N : ℝ) / 6)) * eng 𝔭.tree (slotExp u k) k (F k) Tr (qv R k))) := by
  obtain ⟨hN, -, -, hC⟩ := pd.h𝔭.bounds
  have hb := pd.good.2.1
  have hc0 : 0 ≤ layerCut η TA σ x := by
    rw [layerCut_eq_integral pd.hη hb]
    exact setIntegral_nonneg (measurableSet_layerSet TA σ) fun y _ =>
      mul_nonneg (zpow_two_pos _).le (pd.hη.2.1 _)
  have hc1 := layerCut_le_one pd.hη (by omega) hb σ x
  have hCT : 0 ≤ CT := nonneg_of_formBound (by linarith) hT
  set c := layerCut η TA σ x with hc
  have hy : ∀ k : Fin 3, 0 ≤ yNorm (slotExp u k) (tmult (m R₀ k) (F k) x) := fun k => yNorm_nonneg' _ _
  have hTb := hT (tmult (m R₀ 0) (F 0) x) (tmult (m R₀ 1) (F 1) x) (tmult (m R₀ 2) (F 2) x)
  have e0 : slotExp u 0 = 2 := by simp [slotExp]
  have e1 : slotExp u 1 = 2 := by simp [slotExp]
  have e2 : slotExp u 2 = u := by simp [slotExp]
  rw [← ofReal_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by nlinarith [mul_nonneg hc0 (sub_nonneg.2 hc1), mul_nonneg hc0 hc0] : 0 ≤ c - c ^ 3)]
  have hreal := conv_real_ineq (c := c) (hy₀ := hy 0) (hy₁ := hy 1) (hy₂ := hy 2) hc0 hc1 hCT rfl
    (by rw [e0, e1, e2] at *; exact hTb :
      ‖T (tmult (m R₀ 0) (F 0) x) (tmult (m R₀ 1) (F 1) x) (tmult (m R₀ 2) (F 2) x)‖ ≤
        CT * yNorm (slotExp u 0) (tmult (m R₀ 0) (F 0) x) * yNorm (slotExp u 1) (tmult (m R₀ 1) (F 1) x) *
          yNorm (slotExp u 2) (tmult (m R₀ 2) (F 2) x))
  have hslot : ∀ k : Fin 3, ENNReal.ofReal (c ^ (1 / 6 : ℝ) * yNorm (slotExp u k) (tmult (m R₀ k) (F k) x)) ≤
      ENNReal.ofReal (cutK 𝔭 ^ (1 / 6 : ℝ)) *
        (ENNReal.ofReal (lacSConst 𝔭 (qv R k) ((𝔭.N : ℝ) / 6)) * eng 𝔭.tree (slotExp u k) k (F k) Tr (qv R k)) :=
    fun k => slot_weight_bound pd (slotExp_ge_one hu k) (qv_gt_one hR k) (hF k) (hFb k) hR₀ x
  have hc12 : 0 ≤ c ^ (1 / 6 : ℝ) := Real.rpow_nonneg hc0 _
  have hbL0 : 0 ≤ bLayer η TA σ x := bLayer_nonneg pd.hη (by omega) hb σ x
  refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
  set p₀ := c ^ (1 / 6 : ℝ) * yNorm (slotExp u 0) (tmult (m R₀ 0) (F 0) x) with hp₀
  set p₁ := c ^ (1 / 6 : ℝ) * yNorm (slotExp u 1) (tmult (m R₀ 1) (F 1) x) with hp₁
  set p₂ := c ^ (1 / 6 : ℝ) * yNorm (slotExp u 2) (tmult (m R₀ 2) (F 2) x) with hp₂
  have hp₀0 : 0 ≤ p₀ := mul_nonneg hc12 (hy 0)
  have hp₁0 : 0 ≤ p₁ := mul_nonneg hc12 (hy 1)
  have hp₂0 : 0 ≤ p₂ := mul_nonneg hc12 (hy 2)
  have hbL0' : 0 ≤ c ^ (1 / 2 : ℝ) * (1 - c) := hbL0
  calc ENNReal.ofReal (2 * CT * (c ^ (1 / 2 : ℝ) * (1 - c)) * (p₀ * p₁ * p₂))
      = ENNReal.ofReal (2 * CT) * ENNReal.ofReal (bLayer η TA σ x) *
          (ENNReal.ofReal p₀ * ENNReal.ofReal p₁ * ENNReal.ofReal p₂) := by
        have h2CT : (0 : ℝ) ≤ 2 * CT := by positivity
        rw [ENNReal.ofReal_mul (mul_nonneg h2CT hbL0'), ENNReal.ofReal_mul h2CT,
          ENNReal.ofReal_mul (mul_nonneg hp₀0 hp₁0), ENNReal.ofReal_mul hp₀0]
        rfl
    _ ≤ _ := by
        rw [Fin.prod_univ_three]
        gcongr
        · exact hslot 0
        · exact hslot 1
        · exact hslot 2

theorem measurable_bLayer {𝔭 : Params} {η : ℝ → ℝ} (hη : IsEtaCut 𝔭 η) (Tr : Finset TriTile) (σ : ℤ) :
    Measurable (bLayer η Tr σ) := by
  have hc : Continuous (layerCut η Tr σ) := by
    unfold layerCut
    exact continuous_finset_sum _ fun R _ => continuous_tileCutoff hη σ R.pos
  unfold bLayer
  exact ((hc.rpow_const (fun _ => Or.inr (by norm_num))).mul (continuous_const.sub hc)).measurable

/-- The product of the slot energies appearing in the conversion error. -/
def convProd (𝔭 : Params) (u R : ℝ) {P : ℕ} [NeZero P] (F : Fin 3 → ℝ → ZMod P → ℂ) (Tr : Finset TriTile) : ℝ≥0∞ :=
  ∏ k : Fin 3, (ENNReal.ofReal (cutK 𝔭 ^ (1 / 6 : ℝ)) *
    (ENNReal.ofReal (lacSConst 𝔭 (qv R k) ((𝔭.N : ℝ) / 6)) * eng 𝔭.tree (slotExp u k) k (F k) Tr (qv R k)))

/-- **The conversion error** (MTT2 Lemma 7.3): `‖Σ_σ ∫ (χ̃_σ - χ̃_σ³) Π(T_{m_σ0}F₀, T_{m_σ1}F₁, T_{m_σ2}F₂)‖ ≤ C CT |I_t| ∏_k eng_k`. -/
theorem conv_error {𝔭 : Params} {η η' : ℝ → ℝ} {Tr TA : Finset TriTile} {t : Top} {χ : TriTile → ℝ → ℝ}
    {m : TriTile → Fin 3 → ℝ → ℂ} (pd : PartData 𝔭 η η' Tr TA t χ m) {P : ℕ} [NeZero P] {u R : ℝ} (hu : 1 < u)
    (hR : 2 < R) {T : Form P} {CT : ℝ} (hT : FormBound u T CT) {F : Fin 3 → ℝ → ZMod P → ℂ}
    (hF : ∀ k, Measurable (F k)) (hFb : ∀ k, ∃ B, ∀ x, yNorm 2 (F k x) ≤ B) (R₀ : ℤ → TriTile)
    (hR₀ : ∀ σ ∈ treeScales TA, R₀ σ ∈ layer' TA σ) :
    ‖∑ σ ∈ treeScales TA, ∫ x, ((layerCut η TA σ x - layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
        T (tmult (m (R₀ σ) 0) (F 0) x) (tmult (m (R₀ σ) 1) (F 1) x) (tmult (m (R₀ σ) 2) (F 2) x)‖ₑ ≤
      ENNReal.ofReal (24 * bLayerConst 𝔭 * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) * convProd 𝔭 u R F Tr := by
  obtain ⟨hN, -, -, hC⟩ := pd.h𝔭.bounds
  set PP : ℝ≥0∞ := convProd 𝔭 u R F Tr with hPP
  calc ‖∑ σ ∈ treeScales TA, ∫ x, ((layerCut η TA σ x - layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
        T (tmult (m (R₀ σ) 0) (F 0) x) (tmult (m (R₀ σ) 1) (F 1) x) (tmult (m (R₀ σ) 2) (F 2) x)‖ₑ
      ≤ ∑ σ ∈ treeScales TA, ‖∫ x, ((layerCut η TA σ x - layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
        T (tmult (m (R₀ σ) 0) (F 0) x) (tmult (m (R₀ σ) 1) (F 1) x) (tmult (m (R₀ σ) 2) (F 2) x)‖ₑ :=
        enorm_sum_le _ _
    _ ≤ ∑ σ ∈ treeScales TA, (ENNReal.ofReal (2 * CT) * PP) * ∫⁻ x, ENNReal.ofReal (bLayer η TA σ x) := by
        refine Finset.sum_le_sum fun σ hσ => ?_
        refine (enorm_integral_le_lintegral_enorm _).trans ?_
        calc ∫⁻ x, ‖((layerCut η TA σ x - layerCut η TA σ x ^ 3 : ℝ) : ℂ) *
              T (tmult (m (R₀ σ) 0) (F 0) x) (tmult (m (R₀ σ) 1) (F 1) x) (tmult (m (R₀ σ) 2) (F 2) x)‖ₑ
            ≤ ∫⁻ x, (ENNReal.ofReal (2 * CT) * PP) * ENNReal.ofReal (bLayer η TA σ x) := by
              refine lintegral_mono fun x => ?_
              refine (conv_pointwise pd hu hR hT hF hFb (hR₀ σ hσ) x).trans (le_of_eq ?_)
              rw [hPP, convProd]; ring
          _ = _ := lintegral_const_mul _ (measurable_bLayer pd.hη TA σ).ennreal_ofReal
    _ = (ENNReal.ofReal (2 * CT) * PP) * ∑ σ ∈ treeScales TA, ∫⁻ x, ENNReal.ofReal (bLayer η TA σ x) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (ENNReal.ofReal (2 * CT) * PP) * ENNReal.ofReal (12 * bLayerConst 𝔭 * (2 : ℝ) ^ t.1.1) :=
        mul_le_mul' le_rfl (sum_lintegral_bLayer_le pd.hη (by omega) pd.good)
    _ = ENNReal.ofReal (24 * bLayerConst 𝔭 * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) * PP := by
        have hCT : 0 ≤ CT := nonneg_of_formBound (by linarith) hT
        have hb := bLayerConst_nonneg pd.hη (by omega : 5 ≤ 𝔭.N)
        rw [show ENNReal.ofReal (12 * bLayerConst 𝔭 * (2 : ℝ) ^ t.1.1) =
            ENNReal.ofReal (12 * bLayerConst 𝔭) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) from
              ENNReal.ofReal_mul (by positivity),
          show ENNReal.ofReal (24 * bLayerConst 𝔭 * CT) = ENNReal.ofReal (2 * CT) * ENNReal.ofReal (12 * bLayerConst 𝔭) from by
            rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring]
        ring

end PrimeBHT.TimeFrequency.X2
