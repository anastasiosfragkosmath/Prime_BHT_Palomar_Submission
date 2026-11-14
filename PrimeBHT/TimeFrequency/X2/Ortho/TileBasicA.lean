module

public import PrimeBHT.TimeFrequency.X2.Ortho.Closing
public import PrimeBHT.TimeFrequency.X2.Ortho.Gram
public import PrimeBHT.TimeFrequency.X2.Ortho.TailSum
public import PrimeBHT.TimeFrequency.X2.Ortho.Geometry
public import PrimeBHT.TimeFrequency.X2.Ortho.TreeScalar
public import PrimeBHT.TimeFrequency.X2.Ortho.Families

/-!
# X2, node V10: Layer A of `OrthoTileBasic` (TT* with dual vectors `z_R`)

Given dual vectors `z_R` with (Z1) `⟨z_R, F⟩ = a_R²`, (Z2) `yNorm 2 (z_R x) ≤ C₀ ĉ_R wt 6 c_R ℓ_R x`,
`ĉ_R = ℓ_R^{-1/2} a_R`, (Z3) `z_R ⊥ z_{R'}` unless `3ω_R ∩ 3ω_{R'} ≠ ∅`, the Gram sum satisfies
`‖∑ z_R‖² ≤ 8 C₀² Σ⁻¹ S + 32 C₀² μ √(S Θ)`, `S = ∑ a_R²`, `Θ = ∑ t_R`, `t_R = ∫_{ℝ∖I_{T(R)}} wt 3 c_R ℓ_R`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-- The time length `|I_R|`. -/
def tl (R : TriTile) : ℝ := (2 : ℝ) ^ R.box.scale

/-- The centre of `I_R`. -/
def tc (R : TriTile) : ℝ := dyCentre R.box.scale R.pos

theorem tl_pos (R : TriTile) : 0 < tl R := zpow_pos (by norm_num) _

theorem tc_eq (R : TriTile) : tc R = (2 : ℝ) ^ R.box.scale * R.pos + tl R / 2 := by
  unfold tc dyCentre tl; ring

theorem I_eq_Ico (R : TriTile) : R.I = Set.Ico ((2 : ℝ) ^ R.box.scale * R.pos) ((2 : ℝ) ^ R.box.scale * R.pos + tl R) := by
  unfold TriTile.I dyadicInt tl
  congr 1; ring

/-- The dual data (Z1)-(Z3). -/
structure TileDualData {P : ℕ} [NeZero P] (k : Fin 3) (F : ℝ → ZMod P → ℂ) (𝒮 : Finset TriTile)
    (C₀ : ℝ) (a : TriTile → ℝ) (z : TriTile → ℝ → ZMod P → ℂ) : Prop where
  nonneg : ∀ R ∈ 𝒮, 0 ≤ a R
  meas : ∀ R ∈ 𝒮, Measurable (z R)
  inner_F : ∀ R ∈ 𝒮, ∫ x, yInner (z R x) (F x) = ((a R ^ 2 : ℝ) : ℂ)
  bound : ∀ R ∈ 𝒮, ∀ x, yNorm 2 (z R x) ≤ C₀ * (tl R) ^ (-(1 : ℝ) / 2) * a R * wt 6 (tc R) (tl R) x
  orth : ∀ R ∈ 𝒮, ∀ R' ∈ 𝒮, ¬ FreqClose k R R' → ∫ x, yInner (z R x) (z R' x) = 0

theorem tl_mul_chat_sq (R : TriTile) (a : ℝ) : tl R * ((tl R) ^ (-(1 : ℝ) / 2) * a) ^ 2 = a ^ 2 := by
  have h := tl_pos R
  rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul h.le]
  have : tl R * (tl R ^ ((-(1 : ℝ) / 2) * ((2 : ℕ) : ℝ))) = 1 := by
    rw [show ((-(1 : ℝ) / 2) * ((2 : ℕ) : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
    field_simp
  calc tl R * (tl R ^ ((-(1 : ℝ) / 2) * ((2 : ℕ) : ℝ)) * a ^ 2) =
      (tl R * tl R ^ ((-(1 : ℝ) / 2) * ((2 : ℕ) : ℝ))) * a ^ 2 := by ring
    _ = a ^ 2 := by rw [this, one_mul]

section Gram

variable {P : ℕ} [NeZero P] {k : Fin 3} {F : ℝ → ZMod P → ℂ} {𝒮 : Finset TriTile} {C₀ : ℝ}
  {a : TriTile → ℝ} {z : TriTile → ℝ → ZMod P → ℂ}

/-- `ĉ_R = ℓ_R^{-1/2} a_R`. -/
def chat (a : TriTile → ℝ) (R : TriTile) : ℝ := (tl R) ^ (-(1 : ℝ) / 2) * a R

/-- `J(R, R') = ∫ w_R w_{R'}`. -/
def Jint (R R' : TriTile) : ℝ := ∫ x, wt 6 (tc R) (tl R) x * wt 6 (tc R') (tl R') x

theorem Jint_nonneg (R R' : TriTile) : 0 ≤ Jint R R' :=
  integral_nonneg fun _x => mul_nonneg (wt_pos _ _ _ _ (tl_pos R)).le (wt_pos _ _ _ _ (tl_pos R')).le

theorem integrable_wt_mul (R R' : TriTile) :
    Integrable (fun x => wt 6 (tc R) (tl R) x * wt 6 (tc R') (tl R') x) := by
  refine Integrable.mono' (integrable_wt (q := 6) (by norm_num) (tc R) (tl_pos R))
    ((continuous_wt 6 _ _ (tl_pos R)).mul (continuous_wt 6 _ _ (tl_pos R'))).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (wt_pos _ _ _ _ (tl_pos R)).le (wt_pos _ _ _ _ (tl_pos R')).le)]
  calc _ ≤ wt 6 (tc R) (tl R) x * 1 :=
        mul_le_mul_of_nonneg_left (wt_le_one (by norm_num) _ _ _ (tl_pos R')) (wt_pos _ _ _ _ (tl_pos R)).le
    _ = _ := mul_one _

theorem chat_nonneg (h : TileDualData k F 𝒮 C₀ a z) {R : TriTile} (hR : R ∈ 𝒮) : 0 ≤ chat a R :=
  mul_nonneg (Real.rpow_nonneg (tl_pos R).le _) (h.nonneg R hR)

/-- The pointwise product bound. -/
theorem yy_le (h : TileDualData k F 𝒮 C₀ a z) (hC₀ : 0 ≤ C₀) {R R' : TriTile} (hR : R ∈ 𝒮) (hR' : R' ∈ 𝒮)
    (x : ℝ) : yNorm 2 (z R x) * yNorm 2 (z R' x) ≤
      C₀ ^ 2 * (chat a R * chat a R') * (wt 6 (tc R) (tl R) x * wt 6 (tc R') (tl R') x) := by
  have h1 := h.bound R hR x
  have h2 := h.bound R' hR' x
  have hn : ∀ T : TriTile, 0 ≤ yNorm 2 (z T x) := fun T => by unfold yNorm; positivity
  calc yNorm 2 (z R x) * yNorm 2 (z R' x) ≤ (C₀ * tl R ^ (-(1 : ℝ) / 2) * a R * wt 6 (tc R) (tl R) x) *
        (C₀ * tl R' ^ (-(1 : ℝ) / 2) * a R' * wt 6 (tc R') (tl R') x) :=
      mul_le_mul h1 h2 (hn R') (mul_nonneg (mul_nonneg (mul_nonneg hC₀
        (Real.rpow_nonneg (tl_pos R).le _)) (h.nonneg R hR)) (wt_pos _ _ _ _ (tl_pos R)).le)
    _ = _ := by unfold chat; ring

theorem integrable_yy (h : TileDualData k F 𝒮 C₀ a z) (hC₀ : 0 ≤ C₀) {R R' : TriTile} (hR : R ∈ 𝒮)
    (hR' : R' ∈ 𝒮) : Integrable (fun x => yNorm 2 (z R x) * yNorm 2 (z R' x)) := by
  have hm : ∀ T ∈ 𝒮, Measurable fun x => yNorm 2 (z T x) := fun T hT =>
    (measurable_yNorm_fun 2).comp (h.meas T hT)
  refine ((integrable_wt_mul R R').const_mul (C₀ ^ 2 * (chat a R * chat a R'))).mono'
    ((hm R hR).mul (hm R' hR')).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hn : 0 ≤ yNorm 2 (z R x) * yNorm 2 (z R' x) := by unfold yNorm; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact yy_le h hC₀ hR hR' x

theorem integral_yy_le (h : TileDualData k F 𝒮 C₀ a z) (hC₀ : 0 ≤ C₀) {R R' : TriTile} (hR : R ∈ 𝒮)
    (hR' : R' ∈ 𝒮) : ∫ x, yNorm 2 (z R x) * yNorm 2 (z R' x) ≤
      C₀ ^ 2 * (chat a R * chat a R') * Jint R R' := by
  unfold Jint
  rw [← integral_const_mul]
  exact integral_mono (integrable_yy h hC₀ hR hR') ((integrable_wt_mul R R').const_mul _)
    fun x => yy_le h hC₀ hR hR' x

/-- The inner product is bounded by the product integral. -/
theorem norm_inner_le (h : TileDualData k F 𝒮 C₀ a z) (hC₀ : 0 ≤ C₀) {R R' : TriTile} (hR : R ∈ 𝒮)
    (hR' : R' ∈ 𝒮) : ‖∫ x, yInner (z R x) (z R' x)‖ ≤ ∫ x, yNorm 2 (z R x) * yNorm 2 (z R' x) := by
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) (integrable_yy h hC₀ hR hR')
    (Eventually.of_forall fun x => norm_yInner_le _ _)

/-- The tail of the weight of `R` outside the top of the tree `T`. -/
def tailT (T : Finset TriTile × Top) (R : TriTile) : ℝ :=
  ∫ x in (dyadicInt T.2.1.1 T.2.1.2)ᶜ, wt 3 (tc R) (tl R) x

theorem tailT_nonneg (T : Finset TriTile × Top) (R : TriTile) : 0 ≤ tailT T R :=
  setIntegral_nonneg (measurableSet_Ico.compl) fun _x _ => (wt_pos _ _ _ _ (tl_pos R)).le

theorem tailT_le (T : Finset TriTile × Top) (R : TriTile) : tailT T R ≤ tl R := by
  unfold tailT
  have h := integral_wt (q := 3) (by norm_num) (tc R) (tl_pos R)
  have h1 : ∫ x in (dyadicInt T.2.1.1 T.2.1.2)ᶜ, wt 3 (tc R) (tl R) x ≤ ∫ x, wt 3 (tc R) (tl R) x :=
    setIntegral_le_integral (integrable_wt (by norm_num) _ (tl_pos R))
      (Eventually.of_forall fun x => (wt_pos _ _ _ _ (tl_pos R)).le)
  rw [h] at h1
  have : 2 * tl R / (3 - 1) = tl R := by ring
  linarith

variable {J : ℕ} {Qs : Set Box} {𝒯 : List (Finset TriTile × Top)}

theorem integrable_yInner (h : TileDualData k F 𝒮 C₀ a z) (hC₀ : 0 ≤ C₀) {R R' : TriTile} (hR : R ∈ 𝒮)
    (hR' : R' ∈ 𝒮) : Integrable (fun x => yInner (z R x) (z R' x)) := by
  have h1 : ∀ y : ZMod P, Measurable fun x => z R x y := fun y => (measurable_pi_apply y).comp (h.meas R hR)
  have h2 : ∀ y : ZMod P, Measurable fun x => z R' x y := fun y => (measurable_pi_apply y).comp (h.meas R' hR')
  have hm : Measurable fun x => yInner (z R x) (z R' x) := by
    unfold yInner
    exact Measurable.const_mul (Finset.measurable_sum _ fun y _ =>
      (h1 y).mul (Complex.continuous_conj.measurable.comp (h2 y))) _
  exact (integrable_yy h hC₀ hR hR').mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun x => norm_yInner_le _ _)

theorem integral_sq_sum_le (h : TileDualData k F 𝒮 C₀ a z) (hC₀ : 0 ≤ C₀) :
    ∫ x, yNorm 2 (∑ R ∈ 𝒮, z R x) ^ 2 ≤ ∑ R ∈ 𝒮, ∑ R' ∈ 𝒮,
      (if FreqClose k R R' then ∫ x, yNorm 2 (z R x) * yNorm 2 (z R' x) else 0) := by
  have hint2 : Integrable (fun x => ∑ R ∈ 𝒮, ∑ R' ∈ 𝒮, yInner (z R x) (z R' x)) :=
    integrable_finsetSum _ fun R hR => integrable_finsetSum _ fun R' hR' => integrable_yInner h hC₀ hR hR'
  have key : ∀ x, yNorm 2 (∑ R ∈ 𝒮, z R x) ^ 2 = (∑ R ∈ 𝒮, ∑ R' ∈ 𝒮, yInner (z R x) (z R' x)).re := by
    intro x
    have h1 := yInner_self (∑ R ∈ 𝒮, z R x)
    rw [yInner_sum_left] at h1
    simp_rw [yInner_sum_right] at h1
    rw [h1, Complex.ofReal_re]
  have hre : ∫ x, (∑ R ∈ 𝒮, ∑ R' ∈ 𝒮, yInner (z R x) (z R' x)).re =
      (∫ x, ∑ R ∈ 𝒮, ∑ R' ∈ 𝒮, yInner (z R x) (z R' x)).re := by
    simpa using (Complex.reCLM.integral_comp_comm hint2)
  simp_rw [key]
  rw [hre, integral_finsetSum _ (fun R hR => integrable_finsetSum _ fun R' hR' => integrable_yInner h hC₀ hR hR')]
  have e : ∀ R ∈ 𝒮, ∫ x, ∑ R' ∈ 𝒮, yInner (z R x) (z R' x) = ∑ R' ∈ 𝒮, ∫ x, yInner (z R x) (z R' x) :=
    fun R hR => integral_finsetSum _ fun R' hR' => integrable_yInner h hC₀ hR hR'
  rw [Finset.sum_congr rfl e]
  refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun R hR => ?_))
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun R' hR' => ?_)
  by_cases hc : FreqClose k R R'
  · rw [ite_eq_left hc]; exact norm_inner_le h hC₀ hR hR'
  · rw [ite_eq_right hc, h.orth R hR R' hR' hc]; simp

/-- `Γ(R, R') = ∫ yNorm z_R yNorm z_{R'}`. -/
def Gy (z : TriTile → ℝ → ZMod P → ℂ) (R R' : TriTile) : ℝ :=
  ∫ x, yNorm 2 (z R x) * yNorm 2 (z R' x)

theorem Gy_nonneg (z : TriTile → ℝ → ZMod P → ℂ) (R R' : TriTile) : 0 ≤ Gy z R R' :=
  integral_nonneg fun x => by unfold yNorm; positivity

theorem Gy_comm (z : TriTile → ℝ → ZMod P → ℂ) (R R' : TriTile) : Gy z R R' = Gy z R' R := by
  unfold Gy; simp_rw [mul_comm]

theorem FreqClose.symm {k : Fin 3} {R R' : TriTile} (h : FreqClose k R R') : FreqClose k R' R := by
  unfold FreqClose at *; rwa [Set.inter_comm]

/-- The pair split: close pairs are same-box pairs or nested pairs (in one of the two orders). -/
theorem split_sum (𝒮 : Finset TriTile) :
    ∑ R ∈ 𝒮, ∑ R' ∈ 𝒮, (if FreqClose k R R' then Gy z R R' else 0) ≤
      ∑ R ∈ 𝒮, ∑ R' ∈ 𝒮, (if R.box = R'.box then Gy z R R' else 0) +
        2 * ∑ R ∈ 𝒮, ∑ R' ∈ 𝒮.filter (fun R' => R'.box.scale ≤ R.box.scale ∧ R'.box ≠ R.box ∧
          FreqClose k R' R), Gy z R R' := by
  set g₂ : TriTile → TriTile → ℝ := fun R R' =>
    if (R'.box.scale ≤ R.box.scale ∧ R'.box ≠ R.box ∧ FreqClose k R' R) then Gy z R R' else 0 with hg₂
  have hsumfilter : ∀ R, ∑ R' ∈ 𝒮.filter (fun R' => R'.box.scale ≤ R.box.scale ∧ R'.box ≠ R.box ∧
      FreqClose k R' R), Gy z R R' = ∑ R' ∈ 𝒮, g₂ R R' := fun R => by
    rw [Finset.sum_filter]
  have hpt : ∀ R R', (if FreqClose k R R' then Gy z R R' else 0) ≤
      (if R.box = R'.box then Gy z R R' else 0) + g₂ R R' + g₂ R' R := by
    intro R R'
    have h0 := Gy_nonneg z R R'
    have h0' := Gy_nonneg z R' R
    by_cases hc : FreqClose k R R'
    · rw [ite_eq_left hc]
      by_cases hb : R.box = R'.box
      · rw [ite_eq_left hb]
        have : 0 ≤ g₂ R R' := by simp only [hg₂]; split_ifs <;> [exact h0; exact le_rfl]
        have : 0 ≤ g₂ R' R := by simp only [hg₂]; split_ifs <;> [exact h0'; exact le_rfl]
        linarith
      · rw [ite_eq_right hb]
        rcases le_total R'.box.scale R.box.scale with hs | hs
        · have : g₂ R R' = Gy z R R' := by
            simp only [hg₂]; rw [ite_eq_left ⟨hs, fun h => hb h.symm, hc.symm⟩]
          have : 0 ≤ g₂ R' R := by simp only [hg₂]; split_ifs <;> [exact h0'; exact le_rfl]
          linarith
        · have : g₂ R' R = Gy z R R' := by
            simp only [hg₂]; rw [ite_eq_left ⟨hs, hb, hc⟩, Gy_comm]
          have : 0 ≤ g₂ R R' := by simp only [hg₂]; split_ifs <;> [exact h0; exact le_rfl]
          linarith
    · rw [ite_eq_right hc]
      have : 0 ≤ g₂ R R' := by simp only [hg₂]; split_ifs <;> [exact h0; exact le_rfl]
      have : 0 ≤ g₂ R' R := by simp only [hg₂]; split_ifs <;> [exact h0'; exact le_rfl]
      have : 0 ≤ (if R.box = R'.box then Gy z R R' else 0) := by split_ifs <;> [exact h0; exact le_rfl]
      linarith
  calc ∑ R ∈ 𝒮, ∑ R' ∈ 𝒮, (if FreqClose k R R' then Gy z R R' else 0)
      ≤ ∑ R ∈ 𝒮, ∑ R' ∈ 𝒮, ((if R.box = R'.box then Gy z R R' else 0) + g₂ R R' + g₂ R' R) :=
        Finset.sum_le_sum fun R _ => Finset.sum_le_sum fun R' _ => hpt R R'
    _ = ∑ R ∈ 𝒮, ∑ R' ∈ 𝒮, (if R.box = R'.box then Gy z R R' else 0) +
          ∑ R ∈ 𝒮, ∑ R' ∈ 𝒮, g₂ R R' + ∑ R ∈ 𝒮, ∑ R' ∈ 𝒮, g₂ R' R := by
        simp_rw [Finset.sum_add_distrib]
    _ = ∑ R ∈ 𝒮, ∑ R' ∈ 𝒮, (if R.box = R'.box then Gy z R R' else 0) +
          2 * ∑ R ∈ 𝒮, ∑ R' ∈ 𝒮, g₂ R R' := by
        rw [Finset.sum_comm (f := fun R R' => g₂ R' R)]; ring
    _ = _ := by simp_rw [hsumfilter]

/-- Translation weights of the same box. -/
def wpos (R R' : TriTile) : ℝ :=
  if R.box = R'.box then (1 + ((R'.pos : ℝ) - R.pos) ^ 2)⁻¹ else 0

theorem wpos_nonneg (R R' : TriTile) : 0 ≤ wpos R R' := by
  unfold wpos; split_ifs <;> positivity

theorem wpos_symm (R R' : TriTile) : wpos R R' = wpos R' R := by
  unfold wpos
  by_cases hb : R.box = R'.box
  · have hb' : R'.box = R.box := hb.symm
    rw [ite_eq_left hb, ite_eq_left hb']
    congr 2; ring
  · have hb' : ¬ R'.box = R.box := fun h => hb h.symm
    rw [ite_eq_right hb, ite_eq_right hb']

theorem wpos_row (𝒮 : Finset TriTile) (R : TriTile) : ∑ R' ∈ 𝒮, wpos R R' ≤ sInv :=
  row_sum_le 𝒮 R

theorem rpow_neg_three_le (n : ℝ) : (1 + |n|) ^ (-3 : ℝ) ≤ (1 + n ^ 2)⁻¹ := by
  have h1 : 0 < 1 + |n| := by positivity
  rw [Real.rpow_neg h1.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  apply inv_anti₀ (by positivity)
  nlinarith [abs_nonneg n, sq_abs n, mul_nonneg (abs_nonneg n) (abs_nonneg n)]

theorem tl_mul_chat_mul (a : TriTile → ℝ) {R R' : TriTile} (h : tl R = tl R') :
    tl R * (chat a R * chat a R') = a R * a R' := by
  unfold chat
  rw [← h]
  have hl := tl_pos R
  have e : tl R ^ (-(1 : ℝ) / 2) * tl R ^ (-(1 : ℝ) / 2) = (tl R)⁻¹ := by
    rw [← Real.rpow_add hl, show (-(1 : ℝ) / 2 + -(1 : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one]
  calc tl R * (tl R ^ (-(1 : ℝ) / 2) * a R * (tl R ^ (-(1 : ℝ) / 2) * a R')) =
      tl R * (tl R ^ (-(1 : ℝ) / 2) * tl R ^ (-(1 : ℝ) / 2)) * (a R * a R') := by ring
    _ = a R * a R' := by rw [e]; field_simp

/-- The same-box pair bound. -/
theorem same_box_pair (h : TileDualData k F 𝒮 C₀ a z) (hC₀ : 0 ≤ C₀) {R R' : TriTile} (hR : R ∈ 𝒮)
    (hR' : R' ∈ 𝒮) (hb : R.box = R'.box) :
    Gy z R R' ≤ 4 * C₀ ^ 2 * wpos R R' * (a R ^ 2 + a R' ^ 2) := by
  have hs : tl R' = tl R := by unfold tl; rw [hb]
  have h1 := integral_yy_le h hC₀ hR hR'
  have hJ : Jint R R' ≤ 8 * tl R * wpos R R' := by
    unfold Jint
    rw [hs]
    refine (J_same (tl_pos R)).trans ?_
    have hw : wt 3 (tc R) (tl R) (tc R') = (1 + |((R'.pos : ℝ) - R.pos)|) ^ (-3 : ℝ) := by
      unfold wt
      congr 2
      have hscale : R.box.scale = R'.box.scale := by rw [hb]
      rw [tc_eq, tc_eq]
      have : tl R' = tl R := hs
      rw [this, ← hscale]
      have hl := tl_pos R
      unfold tl
      rw [show (2 : ℝ) ^ R.box.scale * (R'.pos : ℝ) + (2 : ℝ) ^ R.box.scale / 2 -
        ((2 : ℝ) ^ R.box.scale * (R.pos : ℝ) + (2 : ℝ) ^ R.box.scale / 2) =
        (2 : ℝ) ^ R.box.scale * ((R'.pos : ℝ) - R.pos) by ring, abs_mul, abs_of_pos (zpow_pos (by norm_num) _)]
      field_simp
    rw [hw]
    unfold wpos
    rw [ite_eq_left hb]
    exact mul_le_mul_of_nonneg_left (rpow_neg_three_le _) (by have := tl_pos R; positivity)
  have hcc : 0 ≤ chat a R * chat a R' := mul_nonneg (chat_nonneg h hR) (chat_nonneg h hR')
  calc Gy z R R' ≤ C₀ ^ 2 * (chat a R * chat a R') * Jint R R' := h1
    _ ≤ C₀ ^ 2 * (chat a R * chat a R') * (8 * tl R * wpos R R') :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = 8 * C₀ ^ 2 * wpos R R' * (tl R * (chat a R * chat a R')) := by ring
    _ = 8 * C₀ ^ 2 * wpos R R' * (a R * a R') := by rw [tl_mul_chat_mul a hs.symm]
    _ ≤ 4 * C₀ ^ 2 * wpos R R' * (a R ^ 2 + a R' ^ 2) := by
        have := wpos_nonneg R R'
        nlinarith [sq_nonneg (a R - a R'), mul_nonneg (sq_nonneg C₀) this]

/-- The same-box block of the Gram sum. -/
theorem same_box_sum (h : TileDualData k F 𝒮 C₀ a z) (hC₀ : 0 ≤ C₀) :
    ∑ R ∈ 𝒮, ∑ R' ∈ 𝒮, (if R.box = R'.box then Gy z R R' else 0) ≤
      8 * C₀ ^ 2 * sInv * ∑ R ∈ 𝒮, a R ^ 2 := by
  have hpt : ∀ R ∈ 𝒮, ∀ R' ∈ 𝒮, (if R.box = R'.box then Gy z R R' else 0) ≤
      4 * C₀ ^ 2 * (wpos R R' * a R ^ 2 + wpos R R' * a R' ^ 2) := by
    intro R hR R' hR'
    by_cases hb : R.box = R'.box
    · rw [ite_eq_left hb]
      have := same_box_pair h hC₀ hR hR' hb
      nlinarith [this]
    · rw [ite_eq_right hb]
      have : wpos R R' = 0 := by unfold wpos; rw [ite_eq_right hb]
      rw [this]; simp
  have hA : ∑ R ∈ 𝒮, ∑ R' ∈ 𝒮, wpos R R' * a R ^ 2 ≤ sInv * ∑ R ∈ 𝒮, a R ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun R _ => ?_
    rw [← Finset.sum_mul]
    calc (∑ R' ∈ 𝒮, wpos R R') * a R ^ 2 ≤ sInv * a R ^ 2 :=
          mul_le_mul_of_nonneg_right (wpos_row 𝒮 R) (sq_nonneg _)
      _ = _ := rfl
  have hB : ∑ R ∈ 𝒮, ∑ R' ∈ 𝒮, wpos R R' * a R' ^ 2 ≤ sInv * ∑ R ∈ 𝒮, a R ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun R' _ => ?_
    rw [← Finset.sum_mul]
    have : ∑ R ∈ 𝒮, wpos R R' = ∑ R ∈ 𝒮, wpos R' R := Finset.sum_congr rfl fun R _ => wpos_symm R R'
    rw [this]
    exact mul_le_mul_of_nonneg_right (wpos_row 𝒮 R') (sq_nonneg _)
  calc _ ≤ ∑ R ∈ 𝒮, ∑ R' ∈ 𝒮, 4 * C₀ ^ 2 * (wpos R R' * a R ^ 2 + wpos R R' * a R' ^ 2) :=
        Finset.sum_le_sum fun R hR => Finset.sum_le_sum fun R' hR' => hpt R hR R' hR'
    _ = 4 * C₀ ^ 2 * (∑ R ∈ 𝒮, ∑ R' ∈ 𝒮, wpos R R' * a R ^ 2 +
          ∑ R ∈ 𝒮, ∑ R' ∈ 𝒮, wpos R R' * a R' ^ 2) := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 4 * C₀ ^ 2 * (sInv * ∑ R ∈ 𝒮, a R ^ 2 + sInv * ∑ R ∈ 𝒮, a R ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity)
    _ = 8 * C₀ ^ 2 * sInv * ∑ R ∈ 𝒮, a R ^ 2 := by ring

/-- Per-term Cauchy-Schwarz: `2 λ ĉ_R t ≤ λ² t + a_R²` for `0 ≤ t ≤ ℓ_R`. -/
theorem two_chat_t_le (a : TriTile → ℝ) (R : TriTile) {t l : ℝ} (_hl : 0 < l) (ht0 : 0 ≤ t) (ht : t ≤ tl R)
    (_hl0 : 0 < l) :
    2 * l * (chat a R * t) ≤ l ^ 2 * t + a R ^ 2 := by
  unfold chat
  set u := tl R ^ (-(1 : ℝ) / 2) with hu
  have hT := tl_pos R
  have hu2 : u * u * tl R = 1 := by
    have : u * u = (tl R)⁻¹ := by
      rw [hu, ← Real.rpow_add hT, show (-(1 : ℝ) / 2 + -(1 : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one]
    rw [this]; field_simp
  have hu0 : 0 ≤ u := Real.rpow_nonneg hT.le _
  have h1 : (l * t * u) ^ 2 ≤ l ^ 2 * t := by
    have : (l * t * u) ^ 2 = l ^ 2 * (t * t * (u * u)) := by ring
    rw [this]
    have h2 : t * t * (u * u) ≤ t := by
      calc t * t * (u * u) ≤ t * tl R * (u * u) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht ht0) (by positivity)
        _ = t * (u * u * tl R) := by ring
        _ = t := by rw [hu2]; ring
    exact mul_le_mul_of_nonneg_left h2 (sq_nonneg l)
  nlinarith [sq_nonneg (l * t * u - a R)]

theorem integrable_sq_sum (h : TileDualData k F 𝒮 C₀ a z) (hC₀ : 0 ≤ C₀) :
    Integrable (fun x => yNorm 2 (∑ R ∈ 𝒮, z R x) ^ 2) := by
  have hint2 : Integrable (fun x => ∑ R ∈ 𝒮, ∑ R' ∈ 𝒮, yInner (z R x) (z R' x)) :=
    integrable_finsetSum _ fun R hR => integrable_finsetSum _ fun R' hR' => integrable_yInner h hC₀ hR hR'
  refine hint2.re.congr (Eventually.of_forall fun x => ?_)
  have h1 := yInner_self (∑ R ∈ 𝒮, z R x)
  rw [yInner_sum_left] at h1
  simp_rw [yInner_sum_right] at h1
  simp only [RCLike.re_to_complex]
  rw [h1, Complex.ofReal_re]

/-- **TT\***: `S² ≤ ‖∑ z_R‖² ‖F‖²`. -/
theorem tt_star (h : TileDualData k F 𝒮 C₀ a z) (hC₀ : 0 ≤ C₀) (hF : Measurable F) {B : ℝ}
    (hFb : ∀ x, yNorm 2 (F x) ≤ B) (hFint : Integrable (fun x => yNorm 2 (F x) ^ 2)) :
    (∑ R ∈ 𝒮, a R ^ 2) ^ 2 ≤ (∫ x, yNorm 2 (∑ R ∈ 𝒮, z R x) ^ 2) * ∫ x, yNorm 2 (F x) ^ 2 := by
  have hS0 : 0 ≤ ∑ R ∈ 𝒮, a R ^ 2 := Finset.sum_nonneg fun R _ => sq_nonneg _
  have hB0 : 0 ≤ B := (by unfold yNorm; positivity : 0 ≤ yNorm 2 (F 0)).trans (hFb 0)
  have hFm : Measurable fun x => yNorm 2 (F x) := (measurable_yNorm_fun 2).comp hF
  have hZint := integrable_sq_sum h hC₀
  have hZm : Measurable fun x => yNorm 2 (∑ R ∈ 𝒮, z R x) :=
    (measurable_yNorm_fun 2).comp (Finset.measurable_sum _ fun R hR => h.meas R hR)
  -- integrability of `⟨z_R, F⟩`
  have hint : ∀ R ∈ 𝒮, Integrable (fun x => yInner (z R x) (F x)) := by
    intro R hR
    have h1 : ∀ y : ZMod P, Measurable fun x => z R x y := fun y => (measurable_pi_apply y).comp (h.meas R hR)
    have h2 : ∀ y : ZMod P, Measurable fun x => F x y := fun y => (measurable_pi_apply y).comp hF
    have hm : Measurable fun x => yInner (z R x) (F x) := by
      unfold yInner
      exact Measurable.const_mul (Finset.measurable_sum _ fun y _ =>
        (h1 y).mul (Complex.continuous_conj.measurable.comp (h2 y))) _
    have hb : Integrable (fun x => (C₀ * (tl R) ^ (-(1 : ℝ) / 2) * a R * B) * wt 6 (tc R) (tl R) x) :=
      (integrable_wt (q := 6) (by norm_num) (tc R) (tl_pos R)).const_mul _
    refine hb.mono' hm.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    refine (norm_yInner_le _ _).trans ?_
    have := h.bound R hR x
    have hn : 0 ≤ yNorm 2 (F x) := by unfold yNorm; positivity
    calc yNorm 2 (z R x) * yNorm 2 (F x) ≤ (C₀ * tl R ^ (-(1 : ℝ) / 2) * a R * wt 6 (tc R) (tl R) x) * B :=
          mul_le_mul this (hFb x) hn (mul_nonneg (mul_nonneg (mul_nonneg hC₀
            (Real.rpow_nonneg (tl_pos R).le _)) (h.nonneg R hR)) (wt_pos _ _ _ _ (tl_pos R)).le)
      _ = _ := by ring
  have hSc : (((∑ R ∈ 𝒮, a R ^ 2 : ℝ)) : ℂ) = ∫ x, yInner (∑ R ∈ 𝒮, z R x) (F x) := by
    rw [Complex.ofReal_sum]
    rw [Finset.sum_congr rfl (fun R hR => (h.inner_F R hR).symm)]
    rw [← integral_finsetSum _ hint]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [yInner_sum_left]
  have hint' : Integrable (fun x => yInner (∑ R ∈ 𝒮, z R x) (F x)) := by
    have := integrable_finsetSum 𝒮 hint
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [yInner_sum_left]
  have hfg : Integrable (fun x => yNorm 2 (∑ R ∈ 𝒮, z R x) * yNorm 2 (F x)) := by
    refine ((hZint.add hFint).const_mul 1).mono' (hZm.mul hFm).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have h0 : 0 ≤ yNorm 2 (∑ R ∈ 𝒮, z R x) * yNorm 2 (F x) := by unfold yNorm; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    simp only [Pi.add_apply, one_mul]
    nlinarith [sq_nonneg (yNorm 2 (∑ R ∈ 𝒮, z R x) - yNorm 2 (F x))]
  have hSle : ∑ R ∈ 𝒮, a R ^ 2 ≤ ∫ x, yNorm 2 (∑ R ∈ 𝒮, z R x) * yNorm 2 (F x) := by
    have h1 : ∑ R ∈ 𝒮, a R ^ 2 = ‖(((∑ R ∈ 𝒮, a R ^ 2 : ℝ)) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0]
    rw [h1, hSc]
    refine (norm_integral_le_integral_norm _).trans ?_
    exact integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) hfg
      (Eventually.of_forall fun x => norm_yInner_le _ _)
  refine sq_le_of_forall hS0 (integral_nonneg fun x => by positivity)
    (integral_nonneg fun x => by positivity) fun l hl => ?_
  have h2 : 2 * l * ∫ x, yNorm 2 (∑ R ∈ 𝒮, z R x) * yNorm 2 (F x) ≤
      ∫ x, (l ^ 2 * yNorm 2 (∑ R ∈ 𝒮, z R x) ^ 2 + yNorm 2 (F x) ^ 2) := by
    rw [← integral_const_mul]
    exact integral_mono (hfg.const_mul _) ((hZint.const_mul _).add hFint) fun x => by
      simp only
      nlinarith [sq_nonneg (l * yNorm 2 (∑ R ∈ 𝒮, z R x) - yNorm 2 (F x))]
  rw [integral_add (hZint.const_mul _) hFint, integral_const_mul] at h2
  have h3 : 2 * l * ∑ R ∈ 𝒮, a R ^ 2 ≤ 2 * l * ∫ x, yNorm 2 (∑ R ∈ 𝒮, z R x) * yNorm 2 (F x) :=
    mul_le_mul_of_nonneg_left hSle (by positivity)
  linarith

theorem theta_tile (𝒯 : List (Finset TriTile × Top)) :
    (𝒯.map fun T => ∑ R ∈ T.1, tailT T R).sum ≤ (𝒯.map fun T => ∑ R ∈ T.1, tl R).sum :=
  List.sum_le_sum fun T _ => Finset.sum_le_sum fun R _ => tailT_le T R

end Gram

end PrimeBHT.TimeFrequency.X2
