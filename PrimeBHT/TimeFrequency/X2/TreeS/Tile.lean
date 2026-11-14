module

public import PrimeBHT.TimeFrequency.X2.TreeS.Slot

/-!
# X2, node V15s: the model form of ONE tile

`tile_form_le`: for one tile `R₀ ∈ Tr`, `‖∫ χ_{R₀} Π(T_{m₀}F₀, T_{m₁}F₁, T_{m₂}F₂)‖ₑ ≤ C CT |I_{R₀}| ∏_k eng 𝔭.tree (slotExp u k) k (F k) Tr (qv R k)`.

Hölder `(2, 2, ∞)` (`core_holder`), the `L^∞` bound of slot `2` by Bernstein (`slot_sup_exists`), and the domination of the weighted
tile norms by the energies (`slot_dom`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

section Tile

variable {𝔭 : Params}

theorem tile_form_le (h𝔭 : 𝔭.Admissible) {u R : ℝ} (hu : 1 < u) (hR : 2 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (T : Form P) (CT : ℝ), FormBound u T CT →
      ∀ (Tr : Finset TriTile) (R₀ : TriTile), R₀ ∈ Tr → ∀ (η : ℝ → ℝ), IsEtaCut 𝔭 η →
        ∀ (m : Fin 3 → ℝ → ℂ), (∀ k, InMult 𝔭 R₀.box.scale (R₀.box.centre k) (m k)) →
        ∀ F : Fin 3 → ℝ → ZMod P → ℂ, (∀ k, Measurable (F k)) → (∀ k, ∃ B, ∀ x, yNorm 2 (F k x) ≤ B) →
          ‖∫ x, ((tileCutoff η R₀.box.scale R₀.pos x : ℝ) : ℂ) *
              T (tmult (m 0) (F 0) x) (tmult (m 1) (F 1) x) (tmult (m 2) (F 2) x)‖ₑ ≤
            ENNReal.ofReal (C * CT) * ENNReal.ofReal ((2 : ℝ) ^ R₀.box.scale) *
              ∏ k, eng 𝔭.tree (slotExp u k) k (F k) Tr (qv R k) := by
  have hR1 : 1 < R := by linarith
  have hHC : R.HolderConjugate (Real.conjExponent R) := Real.HolderConjugate.conjExponent hR1
  obtain ⟨A, hA0, hA⟩ := slot_sup_exists h𝔭 hHC
  have h𝔭' := h𝔭
  obtain ⟨-, hNf, -, -, -, -, -, hC1⟩ := h𝔭'
  have hC : 0 < 𝔭.C := by linarith
  have hpl := psiLow_pos h𝔭
  have hCb := wsupConst_nonneg hA0 hHC.symm.lt
  set Cb : ℝ := wsupConst A (Real.conjExponent R) with hCbdef
  set pL : ℝ := psiLow 𝔭 (𝔭.tree.N : ℝ) with hpLdef
  refine ⟨cutK 𝔭 * Cb * (1 / pL) ^ 3, by have := cutK_pos hC; positivity, ?_⟩
  intro P _ T CT hT Tr R₀ hR₀ η hη m hm F hFm hFb
  have hu0 : 0 < u := by linarith
  have hN400 : 400 ≤ 𝔭.N := le_trans classFloor_ge hNf
  have hbN : 3 * ((𝔭.tree.N : ℕ) : ℝ) ≤ (𝔭.N : ℝ) := by
    rw [Params.tree_N]
    have : (𝔭.N / 8 : ℕ) * 8 ≤ 𝔭.N := Nat.div_mul_le_self _ _
    have h' : ((𝔭.N / 8 : ℕ) : ℝ) * 8 ≤ 𝔭.N := by exact_mod_cast this
    have h0 : (0 : ℝ) ≤ 𝔭.N := Nat.cast_nonneg _
    linarith
  have hb0 : (0 : ℝ) ≤ ((𝔭.tree.N : ℕ) : ℝ) := Nat.cast_nonneg _
  set ℓ : ℝ := (2 : ℝ) ^ R₀.box.scale with hℓdef
  have hℓ : 0 < ℓ := zpow_pos (by norm_num) _
  set c0 : ℝ := dyCentre R₀.box.scale R₀.pos with hc0
  set b : ℝ := ((𝔭.tree.N : ℕ) : ℝ) with hb
  set Nn : ℝ := (𝔭.N : ℝ) with hNn
  set W : ℝ → ℝ := fun z => jb ((z - c0) / ℓ) with hW
  have hWpos : ∀ z, 0 < W z := fun z => jb_pos _
  -- bounds on the coordinates
  have hcoord : ∀ k, ∃ B : ℝ, ∀ z y, ‖F k z y‖ ≤ B := by
    intro k
    obtain ⟨B, hB⟩ := hFb k
    refine ⟨(P : ℝ) ^ (2 : ℝ)⁻¹ * B, fun z y => ?_⟩
    refine (norm_apply_le_rpow_mul_yNorm (by norm_num : (0 : ℝ) < 2) (F k z) y).trans ?_
    exact mul_le_mul_of_nonneg_left (hB z) (by positivity)
  -- the functions `a_k`
  set a₀ : ℝ → ℝ := fun z => yNorm 2 (tmult (m 0) (F 0) z) with ha₀
  set a₁ : ℝ → ℝ := fun z => yNorm 2 (tmult (m 1) (F 1) z) with ha₁
  set a₂ : ℝ → ℝ := fun z => yNorm u (tmult (m 2) (F 2) z) with ha₂
  have ha₀m : Measurable a₀ := measurable_yNorm_tmult (hm 0) (hFm 0)
  have ha₁m : Measurable a₁ := measurable_yNorm_tmult (hm 1) (hFm 1)
  have ha₂m : Measurable a₂ := measurable_yNorm_tmult (hm 2) (hFm 2)
  have ha₀n : ∀ z, 0 ≤ a₀ z := fun z => CZ.yNorm_nonneg 2 _
  have ha₁n : ∀ z, 0 ≤ a₁ z := fun z => CZ.yNorm_nonneg 2 _
  have ha₂n : ∀ z, 0 ≤ a₂ z := fun z => CZ.yNorm_nonneg u _
  -- the energies
  set E₀ : ℝ≥0∞ := eng 𝔭.tree 2 0 (F 0) Tr 2 with hE₀
  set E₁ : ℝ≥0∞ := eng 𝔭.tree 2 1 (F 1) Tr 2 with hE₁
  set E₂ : ℝ≥0∞ := eng 𝔭.tree u 2 (F 2) Tr R with hE₂
  have hprod : ∏ k : Fin 3, eng 𝔭.tree (slotExp u k) k (F k) Tr (qv R k) = E₀ * E₁ * E₂ := by
    rw [Fin.prod_univ_three]
    simp [qv, hE₀, hE₁, hE₂]
  rw [hprod]
  by_cases hCT : CT < 0
  · -- the form vanishes
    have hz : ∀ a b c, T a b c = 0 := by
      intro a b c
      have h := hT a b c
      have h1 : CT * yNorm 2 a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hCT.le (CZ.yNorm_nonneg 2 a)
      have h2 : CT * yNorm 2 a * yNorm 2 b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 (CZ.yNorm_nonneg 2 b)
      have h3 : CT * yNorm 2 a * yNorm 2 b * yNorm u c ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h2 (CZ.yNorm_nonneg u c)
      exact norm_le_zero_iff.1 (h.trans h3)
    simp [hz]
  push Not at hCT
  have hcK := cutK_pos hC
  -- slot 2: Bernstein
  obtain ⟨B2, hB2⟩ := hcoord 2
  set ε₂ : ℝ≥0∞ := ENNReal.ofReal (ℓ ^ (-1 / R)) *
    Lq R (fun z => ENNReal.ofReal (W z ^ (-b) * a₂ z)) with hε₂
  have hε : ∀ x, ENNReal.ofReal (a₂ x) ≤ ENNReal.ofReal (Cb * jb ((x - c0) / ℓ) ^ b) * ε₂ := fun x =>
    hA P hu.le R₀.box.scale R₀.pos (R₀.box.centre 2) (hm 2) (hFm 2) hB2 x
  have hcore := core_holder (ℓ := ℓ) (c0 := c0) (b := b) (N := Nn) (Cb := Cb) hb0 hbN hCb ha₀m ha₁m ha₀n ha₁n
    ha₂n hε
  -- domination by the energies
  have d0 := slot_dom h𝔭 hη (s := 2) (q := 2) (by norm_num) (by norm_num) hR₀ (hm 0) (hFm 0)
  have d1 := slot_dom h𝔭 hη (s := 2) (q := 2) (by norm_num) (by norm_num) hR₀ (hm 1) (hFm 1)
  have d2 := slot_dom h𝔭 hη (s := u) (q := R) hu0 (by linarith) hR₀ (hm 2) (hFm 2)
  have hq2 : ENNReal.ofReal (ℓ ^ (1 / 2 : ℝ)) * ENNReal.ofReal (ℓ ^ (-1 / 2 : ℝ)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hℓ.le _), ← Real.rpow_add hℓ]
    norm_num
  have hL2 : ∀ (A : ℝ → ℝ≥0∞) (E : ℝ≥0∞),
      ENNReal.ofReal (ℓ ^ (-1 / 2 : ℝ)) * Lq 2 A ≤ ENNReal.ofReal (1 / pL) * E →
        Lq 2 A ≤ ENNReal.ofReal (ℓ ^ (1 / 2 : ℝ)) * (ENNReal.ofReal (1 / pL) * E) := by
    intro A E h
    calc Lq 2 A = ENNReal.ofReal (ℓ ^ (1 / 2 : ℝ)) * (ENNReal.ofReal (ℓ ^ (-1 / 2 : ℝ)) * Lq 2 A) := by
          rw [← mul_assoc, hq2, one_mul]
      _ ≤ _ := mul_le_mul' le_rfl h
  have hA₀ := hL2 _ _ d0
  have hA₁ := hL2 _ _ d1
  have hε₂le : ε₂ ≤ ENNReal.ofReal (1 / pL) * E₂ := d2
  -- the pointwise bound of the integrand
  have hpt : ∀ x, ‖((tileCutoff η R₀.box.scale R₀.pos x : ℝ) : ℂ) *
      T (tmult (m 0) (F 0) x) (tmult (m 1) (F 1) x) (tmult (m 2) (F 2) x)‖ₑ ≤
        ENNReal.ofReal (CT * cutK 𝔭) * ENNReal.ofReal (W x ^ (-Nn) * (a₀ x * a₁ x * a₂ x)) := by
    intro x
    have hχ0 := tileCutoff_nonneg hη R₀.box.scale R₀.pos x
    have hχ := tileCutoff_le hη R₀.box.scale R₀.pos x
    have hX0 : 0 ≤ W x ^ (-Nn) * (a₀ x * a₁ x * a₂ x) :=
      mul_nonneg (Real.rpow_nonneg (hWpos x).le _) (mul_nonneg (mul_nonneg (ha₀n x) (ha₁n x)) (ha₂n x))
    rw [← ENNReal.ofReal_mul (mul_nonneg hCT hcK.le), ← ofReal_norm, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hχ0]
    refine ENNReal.ofReal_le_ofReal ?_
    have hTb := hT (tmult (m 0) (F 0) x) (tmult (m 1) (F 1) x) (tmult (m 2) (F 2) x)
    calc tileCutoff η R₀.box.scale R₀.pos x * ‖T (tmult (m 0) (F 0) x) (tmult (m 1) (F 1) x) (tmult (m 2) (F 2) x)‖
        ≤ tileCutoff η R₀.box.scale R₀.pos x * (CT * a₀ x * a₁ x * a₂ x) :=
          mul_le_mul_of_nonneg_left hTb hχ0
      _ ≤ (cutK 𝔭 * W x ^ (-Nn)) * (CT * a₀ x * a₁ x * a₂ x) :=
          mul_le_mul_of_nonneg_right hχ (mul_nonneg (mul_nonneg (mul_nonneg hCT (ha₀n x)) (ha₁n x)) (ha₂n x))
      _ = CT * cutK 𝔭 * (W x ^ (-Nn) * (a₀ x * a₁ x * a₂ x)) := by ring
  -- the final computation
  have hoC : ENNReal.ofReal ℓ = ENNReal.ofReal (ℓ ^ (1 / 2 : ℝ)) * ENNReal.ofReal (ℓ ^ (1 / 2 : ℝ)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hℓ.le _), ← Real.rpow_add hℓ]
    norm_num
  have hkey : ENNReal.ofReal (cutK 𝔭 * Cb * (1 / pL) ^ 3 * CT) =
      ENNReal.ofReal (CT * cutK 𝔭) * ENNReal.ofReal Cb * ENNReal.ofReal (1 / pL) * ENNReal.ofReal (1 / pL) *
        ENNReal.ofReal (1 / pL) := by
    have h1 : 0 ≤ 1 / pL := by positivity
    rw [show cutK 𝔭 * Cb * (1 / pL) ^ 3 * CT = CT * cutK 𝔭 * Cb * (1 / pL) * (1 / pL) * (1 / pL) by ring,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity)]
  calc ‖∫ x, ((tileCutoff η R₀.box.scale R₀.pos x : ℝ) : ℂ) *
          T (tmult (m 0) (F 0) x) (tmult (m 1) (F 1) x) (tmult (m 2) (F 2) x)‖ₑ
      ≤ ∫⁻ x, ‖((tileCutoff η R₀.box.scale R₀.pos x : ℝ) : ℂ) *
          T (tmult (m 0) (F 0) x) (tmult (m 1) (F 1) x) (tmult (m 2) (F 2) x)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, ENNReal.ofReal (CT * cutK 𝔭) * ENNReal.ofReal (W x ^ (-Nn) * (a₀ x * a₁ x * a₂ x)) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (CT * cutK 𝔭) * ∫⁻ x, ENNReal.ofReal (W x ^ (-Nn) * (a₀ x * a₁ x * a₂ x)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (CT * cutK 𝔭) * (ENNReal.ofReal Cb * ε₂ *
          (Lq 2 (fun z => ENNReal.ofReal (W z ^ (-b) * a₀ z)) * Lq 2 (fun z => ENNReal.ofReal (W z ^ (-b) * a₁ z)))) :=
        mul_le_mul' le_rfl hcore
    _ ≤ ENNReal.ofReal (CT * cutK 𝔭) * (ENNReal.ofReal Cb * (ENNReal.ofReal (1 / pL) * E₂) *
          ((ENNReal.ofReal (ℓ ^ (1 / 2 : ℝ)) * (ENNReal.ofReal (1 / pL) * E₀)) *
            (ENNReal.ofReal (ℓ ^ (1 / 2 : ℝ)) * (ENNReal.ofReal (1 / pL) * E₁)))) :=
        mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' le_rfl hε₂le) (mul_le_mul' hA₀ hA₁))
    _ = ENNReal.ofReal (cutK 𝔭 * Cb * (1 / pL) ^ 3 * CT) * ENNReal.ofReal ℓ * (E₀ * E₁ * E₂) := by
        rw [hkey, hoC]; ring
    _ = _ := by rw [show cutK 𝔭 * Cb * (1 / pL) ^ 3 * CT = cutK 𝔭 * Cb * (1 / pL) ^ 3 * CT from rfl]

end Tile

end PrimeBHT.TimeFrequency.X2
