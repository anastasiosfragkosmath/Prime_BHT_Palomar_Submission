module

public import PrimeBHT.TimeFrequency.X2.Ortho
public import PrimeBHT.TimeFrequency.X2.Ortho.Nested
import PrimeBHT.TimeFrequency.X2.Ortho.Level

/-!
# X2, node V10: `pint` at `s = qX = 2` for the distinct-box `10`-close form of strong disjointness

The proof of `pint_two` (`Ortho.lean`) re-run for `IsStronglyDisjointO` (`Ortho/Nested.lean`): DPLMV's strong
disjointness restricted to pairs of tiles with DISTINCT boxes, tile sets pairwise disjoint as a separate conjunct.
Only the geometric inputs change (`disjoint_top`, `no_three_close`); the dual vectors, the Gram bound and the level
lemma are the built ones.  The same-box pairs of the built `IsStronglyDisjoint` are not needed by the proof (the
same-box block is the translation Schur sum).

* `pint_two_O`: `pint` for `IsStronglyDisjointO` (UNCONDITIONAL);
* `pint_two_nested_of_noShell`: `IsStronglyDisjointN` (the form produced by the V12 selection) + `NoShell`
  (no shell pairs between different trees) implies `IsStronglyDisjointO`;
* `pint_two_nested_singleScale`: UNCONDITIONAL for `IsStronglyDisjointN` families of tiles of ONE box scale.

`PintStatementFor HilbertExp` itself (`IsStronglyDisjointN` without `NoShell`) is FALSE (shell chains; see the report).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

section Gram

variable {P : ℕ} [NeZero P] {k : Fin 3} {F : ℝ → ZMod P → ℂ} {𝒮 : Finset TriTile} {C₀ : ℝ}
  {a : TriTile → ℝ} {z : TriTile → ℝ → ZMod P → ℂ}

variable {J : ℕ} {Qs : Set Box} {𝒯 : List (Finset TriTile × Top)}

/-- The nested block: `∑_{R' ∈ 𝒩(R)} ∫ yNorm z_R yNorm z_{R'} ≤ 16 C₀² μ ĉ_R t_R`. -/
theorem nested_bound_O (hQ : IsRankOne J Qs) (hSD : IsStronglyDisjointO k 𝒯)
    (hbox : ∀ T ∈ 𝒯, ∀ R ∈ T.1, R.box ∈ Qs) (h : TileDualData k F 𝒮 C₀ a z) (hC₀ : 0 ≤ C₀) {μ : ℝ}
    (hμ : ∀ R ∈ 𝒮, chat a R ≤ μ) (h𝒮 : 𝒮 = tilesOf 𝒯) {T : Finset TriTile × Top} (hT : T ∈ 𝒯)
    {R : TriTile} (hR : R ∈ T.1) :
    ∑ R' ∈ 𝒮.filter (fun R' => R'.box.scale ≤ R.box.scale ∧ R'.box ≠ R.box ∧ FreqClose k R' R),
      ∫ x, yNorm 2 (z R x) * yNorm 2 (z R' x) ≤ 16 * C₀ ^ 2 * μ * chat a R * tailT T R := by
  classical
  have hR𝒮 : R ∈ 𝒮 := by rw [h𝒮]; exact mem_tilesOf.2 ⟨T, hT, hR⟩
  set N := 𝒮.filter (fun R' => R'.box.scale ≤ R.box.scale ∧ R'.box ≠ R.box ∧ FreqClose k R' R) with hN
  have hmemN : ∀ R' ∈ N, R' ∈ 𝒮 ∧ R'.box.scale ≤ R.box.scale ∧ R'.box ≠ R.box ∧ FreqClose k R' R := by
    intro R' hR'
    rw [hN, Finset.mem_filter] at hR'
    exact ⟨hR'.1, hR'.2⟩
  have hwint : Integrable (wt 3 (tc R) (tl R)) := integrable_wt (by norm_num) _ (tl_pos R)
  -- the nested estimate for each term
  have hterm : ∀ R' ∈ N, ∫ x, yNorm 2 (z R x) * yNorm 2 (z R' x) ≤
      8 * C₀ ^ 2 * μ * chat a R * ∫ y in R'.I, wt 3 (tc R) (tl R) y := by
    intro R' hR'
    obtain ⟨hR'𝒮, hs, -, -⟩ := hmemN R' hR'
    have h1 := integral_yy_le h hC₀ hR𝒮 hR'𝒮
    have hle : tl R' ≤ tl R := by
      unfold tl; exact zpow_le_zpow_right₀ (by norm_num) hs
    have hJ : Jint R R' ≤ 8 * ∫ y in R'.I, wt 3 (tc R) (tl R) y := by
      unfold Jint
      rw [I_eq_Ico, tc_eq R']
      exact J_le_setIntegral (tl_pos R') hle
    have hcR := chat_nonneg h hR𝒮
    have hcR' := hμ R' hR'𝒮
    have hcR'0 := chat_nonneg h hR'𝒮
    calc _ ≤ C₀ ^ 2 * (chat a R * chat a R') * Jint R R' := h1
      _ ≤ C₀ ^ 2 * (chat a R * μ) * (8 * ∫ y in R'.I, wt 3 (tc R) (tl R) y) := by
          have hJ0 := Jint_nonneg R R'
          have hμ0 : 0 ≤ μ := hcR'0.trans hcR'
          have e1 : C₀ ^ 2 * (chat a R * chat a R') ≤ C₀ ^ 2 * (chat a R * μ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcR' hcR) (sq_nonneg C₀)
          exact mul_le_mul e1 hJ hJ0 (by positivity)
      _ = _ := by ring
  -- disjointness from the top of `T` and multiplicity
  have hdisj : ∀ R' ∈ N, Disjoint R'.I (dyadicInt T.2.1.1 T.2.1.2) := by
    intro R' hR'
    obtain ⟨hR'𝒮, hs, hb, hc⟩ := hmemN R' hR'
    obtain ⟨T', hT', hR'T'⟩ := mem_tilesOf.1 (h𝒮 ▸ hR'𝒮)
    have hne : T ≠ T' := by
      rintro rfl
      have hωne : R'.box.ω k ≠ R.box.ω k := fun hω =>
        hb (box_eq_of_omega_eq hQ (hbox T hT R' hR'T') (hbox T hT R hR) hω)
      have hdis := (hSD.1 T hT).2 R' hR'T' R hR hωne
      obtain ⟨x, hx1, hx2⟩ := hc
      exact Set.disjoint_left.1 hdis hx1 hx2
    exact hSD.disjoint_top hT hT' hne hR hR'T' hb hs hc.dilate_ten
  have hmult : ∀ x, ∀ b₁ ∈ N, ∀ b₂ ∈ N, ∀ b₃ ∈ N, b₁ ≠ b₂ → b₁ ≠ b₃ → b₂ ≠ b₃ → x ∈ b₁.I → x ∈ b₂.I →
      x ∈ b₃.I → False := by
    intro x b₁ h₁ b₂ h₂ b₃ h₃ n12 n13 n23 x1 x2 x3
    obtain ⟨m₁, s₁, -, c₁⟩ := hmemN b₁ h₁
    obtain ⟨m₂, s₂, -, c₂⟩ := hmemN b₂ h₂
    obtain ⟨m₃, s₃, -, c₃⟩ := hmemN b₃ h₃
    exact no_three_close_O hQ hSD hbox (R₀ := R) (h𝒮 ▸ m₁) (h𝒮 ▸ m₂) (h𝒮 ▸ m₃) s₁ s₂ s₃ c₁ c₂ c₃ n12 n13 n23 x1 x2 x3
  have hsum := sum_setIntegral_le N (fun R' => R'.I) (dyadicInt T.2.1.1 T.2.1.2) hwint
    (fun x => (wt_pos _ _ _ _ (tl_pos R)).le)
    (fun R' _ => by rw [I_eq_Ico]; exact measurableSet_Ico) measurableSet_Ico hdisj hmult
  calc ∑ R' ∈ N, ∫ x, yNorm 2 (z R x) * yNorm 2 (z R' x)
      ≤ ∑ R' ∈ N, 8 * C₀ ^ 2 * μ * chat a R * ∫ y in R'.I, wt 3 (tc R) (tl R) y :=
        Finset.sum_le_sum hterm
    _ = 8 * C₀ ^ 2 * μ * chat a R * ∑ R' ∈ N, ∫ y in R'.I, wt 3 (tc R) (tl R) y := by
        rw [Finset.mul_sum]
    _ ≤ 8 * C₀ ^ 2 * μ * chat a R * (2 * tailT T R) := by
        have hcR := chat_nonneg h hR𝒮
        have hμ0 : 0 ≤ μ := (chat_nonneg h hR𝒮).trans (hμ R hR𝒮)
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- The Gram bound for the dual vectors. -/
theorem gram_bound_O (hQ : IsRankOne J Qs) (hSD : IsStronglyDisjointO k 𝒯)
    (hbox : ∀ T ∈ 𝒯, ∀ R ∈ T.1, R.box ∈ Qs) (h : TileDualData k F 𝒮 C₀ a z) (hC₀ : 0 ≤ C₀) {μ : ℝ}
    (hμ0' : 0 ≤ μ) (hμ : ∀ R ∈ 𝒮, chat a R ≤ μ) (h𝒮 : 𝒮 = tilesOf 𝒯) :
    ∫ x, yNorm 2 (∑ R ∈ 𝒮, z R x) ^ 2 ≤ 8 * C₀ ^ 2 * sInv * ∑ R ∈ 𝒮, a R ^ 2 +
      32 * C₀ ^ 2 * μ * (Real.sqrt (∑ R ∈ 𝒮, a R ^ 2) *
        Real.sqrt ((𝒯.map fun T => ∑ R ∈ T.1, tailT T R).sum)) := by
  have hdisj := hSD.pairwise_disjoint
  have hS0 : 0 ≤ ∑ R ∈ 𝒮, a R ^ 2 := Finset.sum_nonneg fun R _ => sq_nonneg _
  set S := ∑ R ∈ 𝒮, a R ^ 2 with hS
  set Θ := (𝒯.map fun T => ∑ R ∈ T.1, tailT T R).sum with hΘ
  have hΘ0 : 0 ≤ Θ := List.sum_nonneg (fun x hx => by
    obtain ⟨T, _, rfl⟩ := List.mem_map.1 hx
    exact Finset.sum_nonneg fun R _ => tailT_nonneg T R)
  have hμ0 : ∀ R ∈ 𝒮, 0 ≤ μ := fun R hR => (chat_nonneg h hR).trans (hμ R hR)
  -- step 1
  have h1 := (integral_sq_sum_le h hC₀).trans (split_sum 𝒮)
  have h2 := same_box_sum h hC₀
  -- step 2/3: the nested sum
  set f : TriTile → ℝ := fun R => ∑ R' ∈ 𝒮.filter (fun R' => R'.box.scale ≤ R.box.scale ∧
    R'.box ≠ R.box ∧ FreqClose k R' R), Gy z R R' with hf
  set X := (𝒯.map fun T => ∑ R ∈ T.1, chat a R * tailT T R).sum with hX
  have hfX : ∑ R ∈ 𝒮, f R ≤ 16 * C₀ ^ 2 * μ * X := by
    have e : ∑ R ∈ 𝒮, f R = (𝒯.map fun T => ∑ R ∈ T.1, f R).sum := by
      rw [h𝒮, sum_family_eq hdisj]
    rw [e, hX, ← List.sum_map_mul_left]
    refine List.sum_le_sum fun T hT => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun R hR => ?_
    have := nested_bound_O hQ hSD hbox h hC₀ hμ h𝒮 hT hR
    calc f R ≤ 16 * C₀ ^ 2 * μ * chat a R * tailT T R := this
      _ = _ := by ring
  -- step 4: `X² ≤ S Θ`
  have hX0 : 0 ≤ X := List.sum_nonneg (fun x hx => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx
    refine Finset.sum_nonneg fun R hR => mul_nonneg ?_ (tailT_nonneg T R)
    exact chat_nonneg h (by rw [h𝒮]; exact mem_tilesOf.2 ⟨T, hT, hR⟩))
  have hXsq : X ^ 2 ≤ Θ * S := by
    refine sq_le_of_forall hX0 hΘ0 hS0 fun l hl => ?_
    have e1 : ∑ R ∈ 𝒮, a R ^ 2 = (𝒯.map fun T => ∑ R ∈ T.1, a R ^ 2).sum := by
      rw [h𝒮, sum_family_eq hdisj]
    have hterm : 2 * l * X ≤ (𝒯.map fun T => ∑ R ∈ T.1, (l ^ 2 * tailT T R + a R ^ 2)).sum := by
      rw [hX, ← List.sum_map_mul_left]
      refine List.sum_le_sum fun T hT => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun R hR => ?_
      have := two_chat_t_le a R hl (tailT_nonneg T R) (tailT_le T R) hl
      calc 2 * l * (chat a R * tailT T R) ≤ l ^ 2 * tailT T R + a R ^ 2 := this
        _ = _ := rfl
    have e2 : (𝒯.map fun T => ∑ R ∈ T.1, (l ^ 2 * tailT T R + a R ^ 2)).sum = l ^ 2 * Θ + S := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [List.sum_map_add, List.sum_map_mul_left, ← e1]
    rw [e2] at hterm
    linarith
  have hXle : X ≤ Real.sqrt (S * Θ) := by
    have := Real.abs_le_sqrt (x := X) (y := S * Θ) (by rw [mul_comm]; exact hXsq)
    exact (le_abs_self X).trans this
  rw [Real.sqrt_mul hS0] at hXle
  have h3 : ∑ R ∈ 𝒮, ∑ R' ∈ 𝒮.filter (fun R' => R'.box.scale ≤ R.box.scale ∧ R'.box ≠ R.box ∧
      FreqClose k R' R), Gy z R R' = ∑ R ∈ 𝒮, f R := rfl
  rw [h3] at h1
  have h4 : 32 * C₀ ^ 2 * μ * X ≤ 32 * C₀ ^ 2 * μ * (Real.sqrt S * Real.sqrt Θ) :=
    mul_le_mul_of_nonneg_left hXle (by positivity)
  calc ∫ x, yNorm 2 (∑ R ∈ 𝒮, z R x) ^ 2 ≤ _ := h1
    _ ≤ 8 * C₀ ^ 2 * sInv * S + 2 * (16 * C₀ ^ 2 * μ * X) := by linarith
    _ ≤ _ := by linarith

/-- The real-number basic estimate (Layer A, `Θ ≤ κ Λ'`). -/
theorem basic_real_O (hQ : IsRankOne J Qs) (hSD : IsStronglyDisjointO k 𝒯)
    (hbox : ∀ T ∈ 𝒯, ∀ R ∈ T.1, R.box ∈ Qs) (h : TileDualData k F 𝒮 C₀ a z) (hC₀ : 0 ≤ C₀)
    (hF : Measurable F) {B : ℝ} (hFb : ∀ x, yNorm 2 (F x) ≤ B)
    (hFint : Integrable (fun x => yNorm 2 (F x) ^ 2)) {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : ∀ R ∈ 𝒮, chat a R ≤ μ) (h𝒮 : 𝒮 = tilesOf 𝒯) {κ Λ' : ℝ} (_hκ : 0 ≤ κ) (_hΛ' : 0 ≤ Λ')
    (hΘ : (𝒯.map fun T => ∑ R ∈ T.1, tailT T R).sum ≤ κ * Λ') :
    ∑ R ∈ 𝒮, a R ^ 2 ≤ (2 * (8 * C₀ ^ 2 * sInv) + 4 * (32 * C₀ ^ 2) ^ 2 + 1) *
      ((∫ x, yNorm 2 (F x) ^ 2) + (μ ^ 2 * (κ * Λ')) ^ ((1 : ℝ) / 3) *
        (∫ x, yNorm 2 (F x) ^ 2) ^ ((2 : ℝ) / 3)) := by
  set S := ∑ R ∈ 𝒮, a R ^ 2 with hS
  set Θ := (𝒯.map fun T => ∑ R ∈ T.1, tailT T R).sum with hΘdef
  set f := ∫ x, yNorm 2 (F x) ^ 2 with hf
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun R _ => sq_nonneg _
  have hf0 : 0 ≤ f := integral_nonneg fun x => by positivity
  have hΘ0 : 0 ≤ Θ := List.sum_nonneg (fun x hx => by
    obtain ⟨T, _, rfl⟩ := List.mem_map.1 hx
    exact Finset.sum_nonneg fun R _ => tailT_nonneg T R)
  have hsInv := sInv_nonneg
  have H1 := tt_star h hC₀ hF hFb hFint
  have H2 := gram_bound_O hQ hSD hbox h hC₀ hμ0 hμ h𝒮
  have hZn0 : 0 ≤ ∫ x, yNorm 2 (∑ R ∈ 𝒮, z R x) ^ 2 := integral_nonneg fun x => by positivity
  have H3 : S ^ 2 ≤ f * (8 * C₀ ^ 2 * sInv * S + 32 * C₀ ^ 2 * (μ * Real.sqrt Θ) * Real.sqrt S) := by
    calc S ^ 2 ≤ (∫ x, yNorm 2 (∑ R ∈ 𝒮, z R x) ^ 2) * f := H1
      _ ≤ (8 * C₀ ^ 2 * sInv * S + 32 * C₀ ^ 2 * μ * (Real.sqrt S * Real.sqrt Θ)) * f :=
          mul_le_mul_of_nonneg_right H2 hf0
      _ = _ := by ring
  have H4 := basic_of_closing (C₁ := 8 * C₀ ^ 2 * sInv) (C₂ := 32 * C₀ ^ 2) hS0 hf0 (by positivity)
    (by positivity) hμ0 hΘ0 H3
  refine H4.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have : (μ ^ 2 * Θ) ^ ((1 : ℝ) / 3) ≤ (μ ^ 2 * (κ * Λ')) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hΘ (sq_nonneg μ)) (by norm_num)
  have h5 : 0 ≤ f ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hf0 _
  linarith [mul_le_mul_of_nonneg_right this h5]

theorem theta_top_O (hQ : IsRankOne J Qs) (hSD : IsStronglyDisjointO k 𝒯)
    (hbox : ∀ T ∈ 𝒯, ∀ R ∈ T.1, R.box ∈ Qs) :
    (𝒯.map fun T => ∑ R ∈ T.1, tailT T R).sum ≤
      4 * zetaTwo * (𝒯.map fun T => (2 : ℝ) ^ T.2.1.1).sum := by
  rw [← List.sum_map_mul_left]
  refine List.sum_le_sum fun T hT => ?_
  have htree := (hSD.1 T hT).1
  set φ : TriTile → ℤ × ℤ := fun R => (R.box.scale, R.pos) with hφ
  have hinj : Set.InjOn φ (T.1 : Set TriTile) := by
    intro R hR R' hR' hRR'
    have hs : R.box.scale = R'.box.scale := congrArg Prod.fst hRR'
    have hp : R.pos = R'.pos := congrArg Prod.snd hRR'
    have hb := IsTree.box_eq_of_scale_eq hQ htree (hbox T hT) R hR R' hR' hs
    cases R; cases R'; simp_all
  have e : ∑ R ∈ T.1, tailT T R = ∑ p ∈ T.1.image φ, ∫ x in (dyadicInt T.2.1.1 T.2.1.2)ᶜ,
      wt 3 (dyCentre p.1 p.2) ((2 : ℝ) ^ p.1) x := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun R _ => ?_
    unfold tailT tc tl; rfl
  rw [e, mul_comm]
  refine le_of_le_of_eq (tail_sum T.2.1.1 T.2.1.2 _ ?_) (by ring)
  intro p hp
  obtain ⟨R, hR, rfl⟩ := Finset.mem_image.1 hp
  exact (htree R hR).1

end Gram

/-- `OrthoTileBasic` for the distinct-box `10`-close form. -/
def OrthoTileBasicO (𝔭 : Params) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (P : ℕ) [NeZero P] (Qs : Set Box), IsRankOne 𝔭.J Qs →
    ∀ (k : Fin 3) (𝒯 : List (Finset TriTile × Top)), IsStronglyDisjointO k 𝒯 →
      (∀ T ∈ 𝒯, ∀ R ∈ T.1, R.box ∈ Qs) → ∀ (F : ℝ → ZMod P → ℂ) (B μ : ℝ), Measurable F →
        (∀ x, yNorm 2 (F x) ≤ B) → 0 ≤ μ →
          (∀ T ∈ 𝒯, ∀ R ∈ T.1, tileEng 𝔭 k F R ≤ ENNReal.ofReal μ) →
            ∀ Λ : ℝ≥0∞, (Λ = topSum 𝒯 ∨ Λ = tileSum 𝒯) →
              (𝒯.map (fun T => ∑ R ∈ T.1, ENNReal.ofReal ((2 : ℝ) ^ R.box.scale) *
                  tileEng 𝔭 k F R ^ (2 : ℝ))).sum ≤
                ENNReal.ofReal K * (mixedPow 2 2 F +
                  (ENNReal.ofReal (μ ^ 2) * Λ) ^ ((1 : ℝ) / 3) * mixedPow 2 2 F ^ ((2 : ℝ) / 3))

/-- **`OrthoTileBasicO` from the dual vectors.** -/
theorem tile_basic_of_duals_O (𝔭 : Params) (hD : TileDuals 𝔭) : OrthoTileBasicO 𝔭 := by
  obtain ⟨C₀, hC₀, hdual⟩ := hD
  have hsInv := sInv_nonneg
  have hZ := zetaTwo_nonneg
  set K₁ : ℝ := 2 * (8 * C₀ ^ 2 * sInv) + 4 * (32 * C₀ ^ 2) ^ 2 + 1 with hK₁
  have hK₁1 : 1 ≤ K₁ := by rw [hK₁]; nlinarith [sq_nonneg (32 * C₀ ^ 2), mul_nonneg (sq_nonneg C₀) hsInv]
  set κ : ℝ := max 1 (4 * zetaTwo) with hκ
  have hκ1 : 1 ≤ κ := le_max_left _ _
  set M : ℝ := max 1 (κ ^ ((1 : ℝ) / 3)) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  refine ⟨4 * K₁ * M, by positivity, ?_⟩
  intro P _ Qs hQ k 𝒯 hSD hbox F B μ hF hB hμ0 hμ Λ hΛ
  have hKpos : 0 < 4 * K₁ * M := by positivity
  by_cases hFtop : mixedPow 2 2 F = ⊤
  · rw [hFtop, top_add, ENNReal.mul_top (ENNReal.ofReal_pos.2 hKpos).ne']
    exact le_top
  have hFint := integrable_of_mixedPow_ne_top hF hFtop
  have hFe := mixedPow_eq_ofReal hFint
  set F2 := ∫ x, yNorm 2 (F x) ^ 2 with hF2
  have hF20 : 0 ≤ F2 := integral_nonneg fun x => by positivity
  have hdisj := hSD.pairwise_disjoint
  set 𝒮 := tilesOf 𝒯 with h𝒮
  have hbox𝒮 : ∀ R ∈ 𝒮, R.box ∈ Qs := by
    intro R hR
    obtain ⟨T, hT, hRT⟩ := mem_tilesOf.1 hR
    exact hbox T hT R hRT
  obtain ⟨a, z, hdata, hnear⟩ := hdual P Qs hQ k 𝒮 hbox𝒮 F B hF hB
  have hcμ : ∀ R ∈ 𝒮, chat a R ≤ μ := by
    intro R hR
    obtain ⟨T, hT, hRT⟩ := mem_tilesOf.1 hR
    have := (hnear R hR).2.trans (hμ T hT R hRT)
    exact (ENNReal.ofReal_le_ofReal_iff hμ0).1 this
  -- the left-hand side in terms of `a`
  have hLHS : (𝒯.map (fun T => ∑ R ∈ T.1, ENNReal.ofReal ((2 : ℝ) ^ R.box.scale) *
      tileEng 𝔭 k F R ^ (2 : ℝ))).sum ≤ 4 * ENNReal.ofReal (∑ R ∈ 𝒮, a R ^ 2) := by
    rw [sum_family_eq hdisj (fun R => ENNReal.ofReal ((2 : ℝ) ^ R.box.scale) * tileEng 𝔭 k F R ^ (2 : ℝ))]
    rw [ENNReal.ofReal_sum_of_nonneg (fun R _ => sq_nonneg _), Finset.mul_sum]
    refine Finset.sum_le_sum fun R hR => ?_
    have h1 : tileEng 𝔭 k F R ^ (2 : ℝ) ≤ (2 * ENNReal.ofReal (chat a R)) ^ (2 : ℝ) :=
      ENNReal.rpow_le_rpow (hnear R hR).1 (by norm_num)
    have hc0 := chat_nonneg hdata hR
    have h2 : (2 * ENNReal.ofReal (chat a R)) ^ (2 : ℝ) = 4 * ENNReal.ofReal (chat a R ^ 2) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_nonneg hc0 (by norm_num),
        Real.rpow_two]
      congr 1
      rw [show (2 : ℝ≥0∞) ^ (2 : ℝ) = 4 by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]; norm_num]
    calc ENNReal.ofReal ((2 : ℝ) ^ R.box.scale) * tileEng 𝔭 k F R ^ (2 : ℝ)
        ≤ ENNReal.ofReal (tl R) * (4 * ENNReal.ofReal (chat a R ^ 2)) := by
          rw [← h2]; exact mul_le_mul' le_rfl h1
      _ = 4 * ENNReal.ofReal (a R ^ 2) := by
          rw [mul_left_comm, ← ENNReal.ofReal_mul (tl_pos R).le]
          congr 2
          exact tl_mul_chat_sq R (a R)
  -- the real estimate
  have key : ∀ Λ' : ℝ, 0 ≤ Λ' → (𝒯.map fun T => ∑ R ∈ T.1, tailT T R).sum ≤ κ * Λ' →
      Λ = ENNReal.ofReal Λ' →
      (𝒯.map (fun T => ∑ R ∈ T.1, ENNReal.ofReal ((2 : ℝ) ^ R.box.scale) *
          tileEng 𝔭 k F R ^ (2 : ℝ))).sum ≤
        ENNReal.ofReal (4 * K₁ * M) * (mixedPow 2 2 F +
          (ENNReal.ofReal (μ ^ 2) * Λ) ^ ((1 : ℝ) / 3) * mixedPow 2 2 F ^ ((2 : ℝ) / 3)) := by
    intro Λ' hΛ' hΘ hΛeq
    have hreal := basic_real_O hQ hSD hbox hdata hC₀ hF hB hFint hμ0 hcμ h𝒮 (by positivity : 0 ≤ κ) hΛ' hΘ
    have hx0 : 0 ≤ μ ^ 2 * Λ' := by positivity
    have hcube : (μ ^ 2 * (κ * Λ')) ^ ((1 : ℝ) / 3) ≤ M * (μ ^ 2 * Λ') ^ ((1 : ℝ) / 3) := by
      have e : μ ^ 2 * (κ * Λ') = κ * (μ ^ 2 * Λ') := by ring
      rw [e, Real.mul_rpow (by positivity) hx0]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hx0 _)
    have h2 := Real.rpow_nonneg hF20 ((2 : ℝ) / 3)
    have hx1 := Real.rpow_nonneg hx0 ((1 : ℝ) / 3)
    have hSreal : ∑ R ∈ 𝒮, a R ^ 2 ≤ K₁ * M * (F2 + (μ ^ 2 * Λ') ^ ((1 : ℝ) / 3) * F2 ^ ((2 : ℝ) / 3)) := by
      refine hreal.trans ?_
      have h3 : F2 + (μ ^ 2 * (κ * Λ')) ^ ((1 : ℝ) / 3) * F2 ^ ((2 : ℝ) / 3) ≤
          M * (F2 + (μ ^ 2 * Λ') ^ ((1 : ℝ) / 3) * F2 ^ ((2 : ℝ) / 3)) := by
        have := mul_le_mul_of_nonneg_right hcube h2
        nlinarith [mul_nonneg hF20 (sub_nonneg.2 hM1), mul_nonneg hx1 h2]
      calc K₁ * (F2 + (μ ^ 2 * (κ * Λ')) ^ ((1 : ℝ) / 3) * F2 ^ ((2 : ℝ) / 3)) ≤
          K₁ * (M * (F2 + (μ ^ 2 * Λ') ^ ((1 : ℝ) / 3) * F2 ^ ((2 : ℝ) / 3))) :=
            mul_le_mul_of_nonneg_left h3 (by linarith)
        _ = _ := by ring
    have hRHS : ENNReal.ofReal (4 * K₁ * M) * (mixedPow 2 2 F +
        (ENNReal.ofReal (μ ^ 2) * Λ) ^ ((1 : ℝ) / 3) * mixedPow 2 2 F ^ ((2 : ℝ) / 3)) =
        ENNReal.ofReal (4 * K₁ * M * (F2 + (μ ^ 2 * Λ') ^ ((1 : ℝ) / 3) * F2 ^ ((2 : ℝ) / 3))) := by
      rw [hFe, hΛeq, ← ENNReal.ofReal_mul (sq_nonneg μ),
        ENNReal.ofReal_rpow_of_nonneg hx0 (by norm_num), ENNReal.ofReal_rpow_of_nonneg hF20 (by norm_num),
        ← ENNReal.ofReal_mul hx1, ← ENNReal.ofReal_add hF20 (by positivity),
        ← ENNReal.ofReal_mul hKpos.le]
    rw [hRHS]
    refine hLHS.trans ?_
    have : 4 * ENNReal.ofReal (∑ R ∈ 𝒮, a R ^ 2) = ENNReal.ofReal (4 * ∑ R ∈ 𝒮, a R ^ 2) := by
      rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
    rw [this]
    refine ENNReal.ofReal_le_ofReal ?_
    have : 4 * ∑ R ∈ 𝒮, a R ^ 2 ≤ 4 * (K₁ * M * (F2 + (μ ^ 2 * Λ') ^ ((1 : ℝ) / 3) * F2 ^ ((2 : ℝ) / 3))) :=
      mul_le_mul_of_nonneg_left hSreal (by norm_num)
    linarith
  rcases hΛ with rfl | rfl
  · -- `Λ = topSum 𝒯`
    have hfin : ∀ T ∈ 𝒯, ENNReal.ofReal ((2 : ℝ) ^ T.2.1.1) ≠ ⊤ := fun T _ => ENNReal.ofReal_ne_top
    have hne : topSum 𝒯 ≠ ⊤ := topSum_ne_top 𝒯
    have hL : (topSum 𝒯).toReal = (𝒯.map fun T => (2 : ℝ) ^ T.2.1.1).sum := by
      unfold topSum
      rw [toReal_list_sum 𝒯 _ hfin]
      congr 1
      refine List.map_congr_left fun T _ => ?_
      exact ENNReal.toReal_ofReal (zpow_pos (by norm_num) _).le
    have hL0 : 0 ≤ (𝒯.map fun T => (2 : ℝ) ^ T.2.1.1).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨T, _, rfl⟩ := List.mem_map.1 hx
        exact (zpow_pos (by norm_num) _).le
    refine key (𝒯.map fun T => (2 : ℝ) ^ T.2.1.1).sum hL0 ?_ ?_
    · refine (theta_top_O hQ hSD hbox).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hL0
    · rw [← hL, ENNReal.ofReal_toReal hne]
  · -- `Λ = tileSum 𝒯`
    have hfin : ∀ T ∈ 𝒯, (∑ R ∈ T.1, ENNReal.ofReal ((2 : ℝ) ^ R.box.scale)) ≠ ⊤ := fun T _ =>
      ENNReal.sum_ne_top.2 fun R _ => ENNReal.ofReal_ne_top
    have hne : tileSum 𝒯 ≠ ⊤ := list_sum_ne_top 𝒯 _ hfin
    have hL : (tileSum 𝒯).toReal = (𝒯.map fun T => ∑ R ∈ T.1, tl R).sum := by
      unfold tileSum
      rw [toReal_list_sum 𝒯 _ hfin]
      congr 1
      refine List.map_congr_left fun T _ => ?_
      rw [ENNReal.toReal_sum (fun R _ => ENNReal.ofReal_ne_top)]
      refine Finset.sum_congr rfl fun R _ => ?_
      exact ENNReal.toReal_ofReal (zpow_pos (by norm_num) _).le
    have hL0 : 0 ≤ (𝒯.map fun T => ∑ R ∈ T.1, tl R).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨T, _, rfl⟩ := List.mem_map.1 hx
        exact Finset.sum_nonneg fun R _ => (tl_pos R).le
    refine key (𝒯.map fun T => ∑ R ∈ T.1, tl R).sum hL0 ?_ ?_
    · refine (theta_tile 𝒯).trans ?_
      calc _ = 1 * (𝒯.map fun T => ∑ R ∈ T.1, tl R).sum := (one_mul _).symm
        _ ≤ κ * _ := mul_le_mul_of_nonneg_right hκ1 hL0
    · rw [← hL, ENNReal.ofReal_toReal hne]

/-- **`pint` at `s = qX = 2` for the distinct-box `10`-close form (conditional on the two analytic reductions).** -/
theorem pint_two_of_tileBasic_O (𝔭 : Params) (h𝔭 : (𝔭.decN 10).Admissible) (hβ : 𝔭.β + 2 * 𝔭.δ < 3)
    (hTB : OrthoTileBasicO (𝔭.decN 10)) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (Qs : Set Box), IsRankOne 𝔭.J Qs →
      ∀ (k : Fin 3) (𝒯 : List (Finset TriTile × Top)), IsStronglyDisjointO k 𝒯 →
        (∀ T ∈ 𝒯, ∀ R ∈ T.1, R.box ∈ Qs) → ∀ (F : ℝ → ZMod P → ℂ) (B : ℝ), Measurable F →
          (∀ x, yNorm 2 (F x) ≤ B) →
            (𝒯.map (fun T => ENNReal.ofReal ((2 : ℝ) ^ T.2.1.1) *
                topNorm 𝔭 2 k F T.1 T.2 2 ^ (2 : ℝ))).sum ≤
              ENNReal.ofReal C * (mixedPow 2 2 F +
                (ENNReal.ofReal (B ^ 2) * topSum 𝒯) ^ (1 - α) * mixedPow 2 2 F ^ α) := by
  classical
  have h𝔭0 : 𝔭.Admissible := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h𝔭
    exact ⟨h1, le_trans h2 (Nat.sub_le _ _), h3, h4, h5, h6, h7, h8⟩
  obtain ⟨K₁, hK₁, hT1⟩ := orthoTreeToTile_of_admissible h𝔭0 hβ
  obtain ⟨K₂, hK₂, hT2⟩ := hTB
  obtain ⟨C₃, hC₃, hE⟩ := tileEng_le (𝔭.decN 10) h𝔭
  set Kb : ℝ := max 1 K₂ with hKb
  have hKb1 : 1 ≤ Kb := le_max_left _ _
  have hε0 : 0 < 1 - α := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set Cα : ℝ := 6 * Kb ^ 2 * (3 + 1 / ((1 - α) * Real.log 2)) with hCα
  have hCα0 : 0 < Cα := by positivity
  set M₃ : ℝ := max 1 (C₃ ^ 2) with hM₃
  have hM₃1 : 1 ≤ M₃ := le_max_left _ _
  have hCpos : 0 < (K₁ + 1) * Cα * M₃ := by positivity
  refine ⟨(K₁ + 1) * Cα * M₃, hCpos.le, ?_⟩
  intro P _ Qs hQs k 𝒯 hSD hbox F B hF hB
  have hB0 : 0 ≤ B := le_trans (by unfold yNorm; positivity) (hB 0)
  have hdisj := hSD.pairwise_disjoint
  set 𝒮 := tilesOf 𝒯 with h𝒮
  set 𝔭' := 𝔭.decN 10 with h𝔭'
  -- step 0: from trees to tiles
  have hS : (𝒯.map (fun T => ENNReal.ofReal ((2 : ℝ) ^ T.2.1.1) *
        topNorm 𝔭 2 k F T.1 T.2 2 ^ (2 : ℝ))).sum ≤
      ENNReal.ofReal K₁ * ∑ R ∈ 𝒮, ENNReal.ofReal ((2 : ℝ) ^ R.box.scale) *
        tileEng 𝔭' k F R ^ (2 : ℝ) := by
    calc _ ≤ (𝒯.map (fun T => ENNReal.ofReal K₁ * ∑ R ∈ T.1, ENNReal.ofReal ((2 : ℝ) ^ R.box.scale) *
            tileEng 𝔭' k F R ^ (2 : ℝ))).sum :=
          List.sum_le_sum fun T hT =>
            hT1 P Qs hQs k T.1 T.2 (hSD.1 T hT).1 (hSD.1 T hT).2 (hbox T hT) F B hF hB
      _ = ENNReal.ofReal K₁ * (𝒯.map (fun T => ∑ R ∈ T.1, ENNReal.ofReal ((2 : ℝ) ^ R.box.scale) *
            tileEng 𝔭' k F R ^ (2 : ℝ))).sum := List.sum_map_mul_left _ _ _
      _ = _ := by rw [sum_family_eq hdisj]
  by_cases h𝒯 : 𝒯 = []
  · subst h𝒯; simp
  have hLpos : 0 < (topSum 𝒯).toReal :=
    ENNReal.toReal_pos (topSum_pos h𝒯).ne' (topSum_ne_top 𝒯)
  by_cases hF2top : mixedPow 2 2 F = ⊤
  · rw [hF2top, top_add, ENNReal.mul_top (ENNReal.ofReal_pos.2 hCpos).ne']
    exact le_top
  -- tile energies are finite and bounded by `C₃ B`
  have hfin : ∀ R, tileEng 𝔭' k F R ≠ ⊤ := fun R =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hE P k F B hF hB R)
  have hc_le : ∀ R, (tileEng 𝔭' k F R).toReal ≤ C₃ * B := fun R => by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hE P k F B hF hB R)
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hSeq : ∀ 𝒬 : Finset TriTile, ∑ R ∈ 𝒬, ENNReal.ofReal ((2 : ℝ) ^ R.box.scale) *
      tileEng 𝔭' k F R ^ (2 : ℝ) =
      ENNReal.ofReal (∑ R ∈ 𝒬, (2 : ℝ) ^ R.box.scale * (tileEng 𝔭' k F R).toReal ^ 2) := by
    intro 𝒬
    rw [ENNReal.ofReal_sum_of_nonneg (fun R _ => by positivity)]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [← ofReal_mul_ofReal_rpow_two (by positivity) ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hfin R)]
  by_cases hF20 : mixedPow 2 2 F = 0
  · have hbase := hT2 P Qs hQs k 𝒯 hSD hbox F B (C₃ * B) hF hB (by positivity)
      (fun T _ R _ => hE P k F B hF hB R) (topSum 𝒯) (Or.inl rfl)
    rw [hF20, ENNReal.zero_rpow_of_pos (by norm_num), mul_zero, add_zero, mul_zero,
      nonpos_iff_eq_zero, sum_family_eq hdisj] at hbase
    refine hS.trans ?_
    rw [hbase, mul_zero]
    exact zero_le
  -- the main case
  have hF2pos : 0 < (mixedPow 2 2 F).toReal := ENNReal.toReal_pos hF20 hF2top
  set F2 := (mixedPow 2 2 F).toReal with hF2
  set L := (topSum 𝒯).toReal with hL
  have hbasic : ∀ 𝒬 ⊆ 𝒮, ∀ μ : ℝ, 0 ≤ μ → (∀ i ∈ 𝒬, (tileEng 𝔭' k F i).toReal ≤ μ) →
      ∑ i ∈ 𝒬, (2 : ℝ) ^ i.box.scale * (tileEng 𝔭' k F i).toReal ^ 2 ≤
        Kb * (F2 + (μ ^ 2 * min L (∑ i ∈ 𝒬, (2 : ℝ) ^ i.box.scale)) ^ ((1 : ℝ) / 3) *
          F2 ^ ((2 : ℝ) / 3)) := by
    intro 𝒬 h𝒬 μ hμ hcμ
    have hSD' := hSD.restrictFamily 𝒬
    have hdisj' := hSD'.pairwise_disjoint
    have hbox' : ∀ T ∈ restrictFamily 𝒬 𝒯, ∀ R ∈ T.1, R.box ∈ Qs := by
      intro T hT R hR
      obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.1 hT
      exact hbox T₀ hT₀ R (Finset.mem_inter.1 hR).1
    have hen : ∀ T ∈ restrictFamily 𝒬 𝒯, ∀ R ∈ T.1, tileEng 𝔭' k F R ≤ ENNReal.ofReal μ := by
      intro T hT R hR
      obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.1 hT
      have hR𝒬 := (Finset.mem_inter.1 hR).2
      rw [← ENNReal.ofReal_toReal (hfin R)]
      exact ENNReal.ofReal_le_ofReal (hcμ R hR𝒬)
    have htiles : tilesOf (restrictFamily 𝒬 𝒯) = 𝒬 := by
      rw [tilesOf_restrictFamily]; exact Finset.inter_eq_right.2 h𝒬
    have hlhs : ((restrictFamily 𝒬 𝒯).map (fun T => ∑ R ∈ T.1,
        ENNReal.ofReal ((2 : ℝ) ^ R.box.scale) * tileEng 𝔭' k F R ^ (2 : ℝ))).sum =
        ENNReal.ofReal (∑ R ∈ 𝒬, (2 : ℝ) ^ R.box.scale * (tileEng 𝔭' k F R).toReal ^ 2) := by
      rw [sum_family_eq hdisj', htiles, hSeq]
    have hF2e : mixedPow 2 2 F ≠ ⊤ := hF2top
    have hmain := fun Λ hΛ => hT2 P Qs hQs k (restrictFamily 𝒬 𝒯) hSD' hbox' F B μ hF hB hμ hen Λ hΛ
    have hsumℓ : tileSum (restrictFamily 𝒬 𝒯) =
        ENNReal.ofReal (∑ R ∈ 𝒬, (2 : ℝ) ^ R.box.scale) := by
      rw [tileSum_eq hdisj', htiles, ENNReal.ofReal_sum_of_nonneg (fun R _ => by positivity)]
    have hnn : 0 ≤ ∑ R ∈ 𝒬, (2 : ℝ) ^ R.box.scale := Finset.sum_nonneg fun R _ => by positivity
    have hA := hmain (topSum (restrictFamily 𝒬 𝒯)) (Or.inl rfl)
    have hB' := hmain (tileSum (restrictFamily 𝒬 𝒯)) (Or.inr rfl)
    rw [hlhs, topSum_restrictFamily] at hA
    rw [hlhs, hsumℓ] at hB'
    have hA' := toReal_basic hK₂ hF2e (topSum_ne_top 𝒯) hA
    have hB'' := toReal_basic hK₂ hF2e ENNReal.ofReal_ne_top hB'
    have hlhsnn : 0 ≤ ∑ R ∈ 𝒬, (2 : ℝ) ^ R.box.scale * (tileEng 𝔭' k F R).toReal ^ 2 :=
      Finset.sum_nonneg fun R _ => by positivity
    rw [ENNReal.toReal_ofReal hlhsnn] at hA'
    rw [ENNReal.toReal_ofReal hlhsnn, ENNReal.toReal_ofReal hnn] at hB''
    have hmono : ∀ x : ℝ, 0 ≤ x → K₂ * x ≤ Kb * x := fun x hx =>
      mul_le_mul_of_nonneg_right (le_max_right _ _) hx
    have hnn2 : 0 ≤ F2 + (μ ^ 2 * L) ^ ((1 : ℝ) / 3) * F2 ^ ((2 : ℝ) / 3) := by positivity
    rcases le_total L (∑ R ∈ 𝒬, (2 : ℝ) ^ R.box.scale) with hle | hle
    · rw [min_eq_left hle]
      exact hA'.trans (hmono _ hnn2)
    · rw [min_eq_right hle]
      refine hB''.trans (hmono _ (by positivity))
  have hlev := level_lemma (𝒮 := 𝒮) (ℓ := fun R => (2 : ℝ) ^ R.box.scale)
    (c := fun R => (tileEng 𝔭' k F R).toReal) (K := Kb) (F2 := F2) (L := L) (μ₀ := C₃ * B)
    (α := α) hKb1 hF2pos hLpos (by positivity) hα hα1 (fun R _ => zpow_pos (by norm_num) _)
    (fun R _ => hc_le R) hbasic
  -- back to `ℝ≥0∞`
  have hF2e : mixedPow 2 2 F = ENNReal.ofReal F2 := (ENNReal.ofReal_toReal hF2top).symm
  have hLe : topSum 𝒯 = ENNReal.ofReal L := (ENNReal.ofReal_toReal (topSum_ne_top 𝒯)).symm
  set ε := 1 - α with hε
  have hrpow : (C₃ ^ 2) ^ ε ≤ M₃ := by
    rcases le_total (C₃ ^ 2) 1 with h1 | h1
    · exact (Real.rpow_le_one (sq_nonneg _) h1 hε0.le).trans hM₃1
    · calc (C₃ ^ 2) ^ ε ≤ (C₃ ^ 2) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
        _ = C₃ ^ 2 := Real.rpow_one _
        _ ≤ M₃ := le_max_right _ _
  have hreal : K₁ * (Cα * (F2 + ((C₃ * B) ^ 2 * L) ^ ε * F2 ^ α)) ≤
      (K₁ + 1) * Cα * M₃ * (F2 + (B ^ 2 * L) ^ ε * F2 ^ α) := by
    have h1 : ((C₃ * B) ^ 2 * L) ^ ε ≤ M₃ * (B ^ 2 * L) ^ ε := by
      rw [mul_pow, mul_assoc, Real.mul_rpow (sq_nonneg _) (by positivity)]
      exact mul_le_mul_of_nonneg_right hrpow (Real.rpow_nonneg (by positivity) _)
    have h2 : 0 ≤ (B ^ 2 * L) ^ ε * F2 ^ α := by positivity
    have h3 : F2 + ((C₃ * B) ^ 2 * L) ^ ε * F2 ^ α ≤ M₃ * (F2 + (B ^ 2 * L) ^ ε * F2 ^ α) := by
      have := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hF2pos.le α)
      nlinarith [hF2pos]
    have h4 : 0 ≤ K₁ * Cα := by positivity
    calc K₁ * (Cα * (F2 + ((C₃ * B) ^ 2 * L) ^ ε * F2 ^ α))
        = K₁ * Cα * (F2 + ((C₃ * B) ^ 2 * L) ^ ε * F2 ^ α) := by ring
      _ ≤ K₁ * Cα * (M₃ * (F2 + (B ^ 2 * L) ^ ε * F2 ^ α)) := mul_le_mul_of_nonneg_left h3 h4
      _ ≤ (K₁ + 1) * Cα * (M₃ * (F2 + (B ^ 2 * L) ^ ε * F2 ^ α)) := by
          gcongr; linarith
      _ = _ := by ring
  have hlev' : ENNReal.ofReal (∑ R ∈ 𝒮, (2 : ℝ) ^ R.box.scale * (tileEng 𝔭' k F R).toReal ^ 2) ≤
      ENNReal.ofReal (Cα * (F2 + ((C₃ * B) ^ 2 * L) ^ ε * F2 ^ α)) :=
    ENNReal.ofReal_le_ofReal hlev
  have hrhs : ENNReal.ofReal ((K₁ + 1) * Cα * M₃) * (mixedPow 2 2 F +
      (ENNReal.ofReal (B ^ 2) * topSum 𝒯) ^ ε * mixedPow 2 2 F ^ α) =
      ENNReal.ofReal ((K₁ + 1) * Cα * M₃ * (F2 + (B ^ 2 * L) ^ ε * F2 ^ α)) := by
    rw [hF2e, hLe, ← ENNReal.ofReal_mul (sq_nonneg B),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hε0.le,
      ENNReal.ofReal_rpow_of_nonneg hF2pos.le hα.le,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hF2pos.le (by positivity),
      ← ENNReal.ofReal_mul hCpos.le]
  rw [hrhs]
  refine hS.trans ?_
  rw [hSeq 𝒮, ← ENNReal.ofReal_mul hK₁]
  exact ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left hlev hK₁).trans hreal)

/-- **V10 for the distinct-box `10`-close form: `pint` at `s = qX = 2`, UNCONDITIONAL.**  For `k`-strongly disjoint
(`IsStronglyDisjointO`) families of `k`-lacunary trees of boxes of a rank-1 box set,
`∑_T |I_T| topNorm(F;T;2)² ≤ C (‖F‖₂² + (B² ∑_T|I_T|)^{1-α} ‖F‖₂^{2α})`. -/
theorem pint_two_O (𝔭 : Params) (h𝔭 : (𝔭.decN 10).Admissible) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (Qs : Set Box), IsRankOne 𝔭.J Qs →
      ∀ (k : Fin 3) (𝒯 : List (Finset TriTile × Top)), IsStronglyDisjointO k 𝒯 →
        (∀ T ∈ 𝒯, ∀ R ∈ T.1, R.box ∈ Qs) → ∀ (F : ℝ → ZMod P → ℂ) (B : ℝ), Measurable F →
          (∀ x, yNorm 2 (F x) ≤ B) →
            (𝒯.map (fun T => ENNReal.ofReal ((2 : ℝ) ^ T.2.1.1) *
                topNorm 𝔭 2 k F T.1 T.2 2 ^ (2 : ℝ))).sum ≤
              ENNReal.ofReal C * (mixedPow 2 2 F +
                (ENNReal.ofReal (B ^ 2) * topSum 𝒯) ^ (1 - α) * mixedPow 2 2 F ^ α) := by
  have h𝔭0 : 𝔭.Admissible := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h𝔭
    exact ⟨h1, le_trans h2 (Nat.sub_le _ _), h3, h4, h5, h6, h7, h8⟩
  exact pint_two_of_tileBasic_O 𝔭 h𝔭 h𝔭0.beta_delta
    (tile_basic_of_duals_O _ (tileDuals_of_admissible _ h𝔭)) hα hα1

/-- `PintStatementFor E` for the distinct-box `10`-close form. -/
def PintStatementOFor (E : ℝ → ℝ → Prop) : Prop :=
  ∀ (𝔭 : Params), (𝔭.decN 10).Admissible → ∀ {s qX α : ℝ}, E s qX → 0 < α → α < 1 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (Qs : Set Box), IsRankOne 𝔭.J Qs →
      ∀ (k : Fin 3) (𝒯 : List (Finset TriTile × Top)), IsStronglyDisjointO k 𝒯 →
        (∀ T ∈ 𝒯, ∀ R ∈ T.1, R.box ∈ Qs) → ∀ (F : ℝ → ZMod P → ℂ) (B : ℝ), Measurable F →
          (∀ x, yNorm s (F x) ≤ B) →
            (𝒯.map (fun T => ENNReal.ofReal ((2 : ℝ) ^ T.2.1.1) * topNorm 𝔭 s k F T.1 T.2 qX ^ qX)).sum ≤
              ENNReal.ofReal C * (mixedPow qX s F +
                (ENNReal.ofReal (B ^ qX) * topSum 𝒯) ^ (1 - α) * mixedPow qX s F ^ α)

/-- **`PintStatementOFor HilbertExp`** (class margin `(𝔭.decN 10).Admissible`), unconditional. -/
theorem pint_two_O_statement : PintStatementOFor HilbertExp := by
  intro 𝔭 h𝔭 s qX α hE hα hα1
  obtain ⟨rfl, rfl⟩ := hE
  obtain ⟨C, hC, h⟩ := pint_two_O 𝔭 h𝔭 hα hα1
  refine ⟨C, hC, ?_⟩
  intro P _ Qs hQ k 𝒯 hSD hbox F B hF hB
  have := h P Qs hQ k 𝒯 hSD hbox F B hF hB
  rwa [Real.rpow_two]

end PrimeBHT.TimeFrequency.X2
