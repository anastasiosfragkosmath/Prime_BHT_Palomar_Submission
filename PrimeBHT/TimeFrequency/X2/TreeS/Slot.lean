module

public import PrimeBHT.TimeFrequency.X2.TreeS.Weighted
public import PrimeBHT.TimeFrequency.X2.TreeS.Bern

/-!
# X2, node V15s: single-slot bounds of one tile

* `slot_dom`: the weighted norm `ℓ^{-1/q} ‖⟨(· - c_I)/ℓ⟩^{-b} ‖T_m F‖_{L^s(Y)}‖_{L^q}` of one tile is at most
  `psiLow⁻¹ · eng 𝔭.tree s k F Tr q` (domination by the lower-bounded cutoff `ψ̃_I ∈ Ψ_I(𝔭.tree)` and `single_tile_le_eng`);
* `slot_sup`: Bernstein, the pointwise bound `‖T_m F (x)‖_{L^s(Y)} ≤ C ⟨(x - c_I)/ℓ⟩^b ℓ^{-1/R} ‖⟨⟩^{-b} ‖T_m F‖‖_{L^R}`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

section Slot

variable {𝔭 : Params} {P : ℕ} [NeZero P]

theorem continuous_fourierInv_inMult' {s : ℤ} {c : ℝ} {m : ℝ → ℂ} (hm : InMult 𝔭 s c m) : Continuous (𝓕⁻ m) :=
  continuous_fourierInv_of_integrable' (integrable_of_far hm.1.continuous hm.2.1)

theorem measurable_yNorm_tmult {s' : ℝ} {sc : ℤ} {c : ℝ} {m : ℝ → ℂ} (hm : InMult 𝔭 sc c m)
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) : Measurable fun z => yNorm s' (tmult m F z) :=
  CZ.measurable_yNorm s' fun y => (measurable_pi_iff.1 (measurable_tmult_of_cont (continuous_fourierInv_inMult' hm) hF)) y

theorem yNorm_smul_c {s : ℝ} (hs : 0 < s) (c : ℂ) (v : ZMod P → ℂ) : yNorm s (c • v) = ‖c‖ * yNorm s v :=
  yNorm_fun_const_mul hs c v

/-- `psiLow > 0`. -/
theorem psiLow_pos (h𝔭 : 𝔭.Admissible) : 0 < psiLow 𝔭 (𝔭.tree.N : ℝ) := by
  obtain ⟨-, hNf, -, -, -, -, -, hC1⟩ := h𝔭
  have hC : 0 < 𝔭.C := by linarith
  have hN400 : 400 ≤ 𝔭.N := le_trans classFloor_ge hNf
  have hbN : ((𝔭.tree.N : ℕ) : ℝ) ≤ 𝔭.N / 8 := by
    rw [Params.tree_N]
    have : (𝔭.N / 8 : ℕ) * 8 ≤ 𝔭.N := Nat.div_mul_le_self _ _
    have h' : ((𝔭.N / 8 : ℕ) : ℝ) * 8 ≤ 𝔭.N := by exact_mod_cast this
    linarith
  have hN4 : (400 : ℝ) ≤ 𝔭.N := by exact_mod_cast hN400
  have h0 : (0 : ℝ) ≤ ((𝔭.tree.N : ℕ) : ℝ) := Nat.cast_nonneg _
  have : (0 : ℝ) < (𝔭.N : ℝ) - ((𝔭.tree.N : ℕ) : ℝ) - 1 := by linarith
  have hK := cutK_pos hC
  unfold psiLow
  positivity

/-- **Domination of the weighted tile norm by the energy.** -/
theorem slot_dom (h𝔭 : 𝔭.Admissible) {η : ℝ → ℝ} (hη : IsEtaCut 𝔭 η) {s q : ℝ} (hs : 0 < s) (hq : 0 < q)
    {Tr : Finset TriTile} {R₀ : TriTile} (hR₀ : R₀ ∈ Tr) {k : Fin 3} {m : ℝ → ℂ}
    (hm : InMult 𝔭 R₀.box.scale (R₀.box.centre k) m) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) :
    ENNReal.ofReal (((2 : ℝ) ^ R₀.box.scale) ^ (-1 / q)) *
        Lq q (fun z => ENNReal.ofReal (jb ((z - dyCentre R₀.box.scale R₀.pos) / (2 : ℝ) ^ R₀.box.scale) ^
          (-(𝔭.tree.N : ℝ)) * yNorm s (tmult m F z))) ≤
      ENNReal.ofReal (1 / psiLow 𝔭 (𝔭.tree.N : ℝ)) * eng 𝔭.tree s k F Tr q := by
  obtain ⟨ψ, hψ, hψlow⟩ := exists_psiTilde h𝔭 hη R₀.box.scale R₀.pos
  have hpl := psiLow_pos h𝔭
  have hdom : ∀ x, ‖(((jb ((x - dyCentre R₀.box.scale R₀.pos) / (2 : ℝ) ^ R₀.box.scale) ^
      (-(𝔭.tree.N : ℝ)) : ℝ)) : ℂ)‖ ≤ (1 / psiLow 𝔭 (𝔭.tree.N : ℝ)) * ‖ψ x‖ := by
    intro x
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (jb_pos _).le _)]
    have := hψlow x
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpl]
    linarith
  have hmc := continuous_fourierInv_inMult' hm
  have hmeas : AEStronglyMeasurable (fun x => yNorm s ((((jb ((x - dyCentre R₀.box.scale R₀.pos) /
      (2 : ℝ) ^ R₀.box.scale) ^ (-(𝔭.tree.N : ℝ)) : ℝ)) : ℂ) • tmult m F x)) volume := by
    have : (fun x => yNorm s ((((jb ((x - dyCentre R₀.box.scale R₀.pos) / (2 : ℝ) ^ R₀.box.scale) ^
        (-(𝔭.tree.N : ℝ)) : ℝ)) : ℂ) • tmult m F x)) = fun x => jb ((x - dyCentre R₀.box.scale R₀.pos) /
          (2 : ℝ) ^ R₀.box.scale) ^ (-(𝔭.tree.N : ℝ)) * yNorm s (tmult m F x) := by
      funext x
      rw [yNorm_smul_c hs, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (jb_pos _).le _)]
    rw [this]
    exact ((Measurable.mul ((continuous_jb.comp ((continuous_id.sub continuous_const).div_const _)).measurable.pow_const _)
      (measurable_yNorm_tmult hm hF))).aestronglyMeasurable
  have h1 := eLpNorm_dominated hs m F (w := fun x => (((jb ((x - dyCentre R₀.box.scale R₀.pos) /
      (2 : ℝ) ^ R₀.box.scale) ^ (-(𝔭.tree.N : ℝ)) : ℝ)) : ℂ)) (θ := ψ)
    (div_nonneg zero_le_one hpl.le) hdom (ENNReal.ofReal q) hmeas
  have h2 := single_tile_le_eng (𝔭 := 𝔭.tree) (s := s) (q := q) (k := k) (F := F) hR₀
    (centre_div_mem_hull R₀.box k) hψ hm
  have hfun : (fun x => yNorm s ((((jb ((x - dyCentre R₀.box.scale R₀.pos) / (2 : ℝ) ^ R₀.box.scale) ^
      (-(𝔭.tree.N : ℝ)) : ℝ)) : ℂ) • tmult m F x)) = fun x => jb ((x - dyCentre R₀.box.scale R₀.pos) /
        (2 : ℝ) ^ R₀.box.scale) ^ (-(𝔭.tree.N : ℝ)) * yNorm s (tmult m F x) := by
    funext x
    rw [yNorm_smul_c hs, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (jb_pos _).le _)]
  have hnn : ∀ x, 0 ≤ jb ((x - dyCentre R₀.box.scale R₀.pos) / (2 : ℝ) ^ R₀.box.scale) ^ (-(𝔭.tree.N : ℝ)) *
      yNorm s (tmult m F x) := fun x => mul_nonneg (Real.rpow_nonneg (jb_pos _).le _) (CZ.yNorm_nonneg s _)
  have hm2 : Measurable fun x => jb ((x - dyCentre R₀.box.scale R₀.pos) / (2 : ℝ) ^ R₀.box.scale) ^
      (-(𝔭.tree.N : ℝ)) * yNorm s (tmult m F x) :=
    Measurable.mul ((continuous_jb.comp ((continuous_id.sub continuous_const).div_const _)).measurable.pow_const _)
      (measurable_yNorm_tmult hm hF)
  rw [hfun] at h1
  rw [← eLpNorm_eq_Lq hq hm2.aestronglyMeasurable hnn]
  calc ENNReal.ofReal (((2 : ℝ) ^ R₀.box.scale) ^ (-1 / q)) * eLpNorm (fun x => jb ((x - dyCentre R₀.box.scale R₀.pos) /
        (2 : ℝ) ^ R₀.box.scale) ^ (-(𝔭.tree.N : ℝ)) * yNorm s (tmult m F x)) (ENNReal.ofReal q) volume
      ≤ ENNReal.ofReal (((2 : ℝ) ^ R₀.box.scale) ^ (-1 / q)) *
          (ENNReal.ofReal (1 / psiLow 𝔭 (𝔭.tree.N : ℝ)) * eLpNorm (fun x => yNorm s (ψ x • tmult m F x))
            (ENNReal.ofReal q) volume) := mul_le_mul' le_rfl h1
    _ = ENNReal.ofReal (1 / psiLow 𝔭 (𝔭.tree.N : ℝ)) * (ENNReal.ofReal (((2 : ℝ) ^ R₀.box.scale) ^ (-1 / q)) *
          eLpNorm (fun x => yNorm s (ψ x • tmult m F x)) (ENNReal.ofReal q) volume) := by ring
    _ ≤ _ := mul_le_mul' le_rfl h2

/-- **Bernstein, weighted `L^R → L^∞` form for one tile**: there is `A ≥ 0` (depending only on the decay order `𝔭.tree.N`) with
`‖T_m F(x)‖_{L^{s'}(Y)} ≤ wsupConst A R' ⟨(x - c_I)/ℓ⟩^b ℓ^{-1/R} ‖⟨(· - c_I)/ℓ⟩^{-b} ‖T_m F‖‖_{L^R}`. -/
theorem slot_sup_exists (h𝔭 : 𝔭.Admissible) {R R' : ℝ} (hHC : R.HolderConjugate R') :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (P : ℕ) [NeZero P] {s' : ℝ}, 1 ≤ s' → ∀ (sc v : ℤ) (c : ℝ) {m : ℝ → ℂ},
      InMult 𝔭 sc c m → ∀ {F : ℝ → ZMod P → ℂ}, Measurable F → ∀ {B : ℝ}, (∀ z y, ‖F z y‖ ≤ B) → ∀ x : ℝ,
        ENNReal.ofReal (yNorm s' (tmult m F x)) ≤
          ENNReal.ofReal (wsupConst A R' * jb ((x - dyCentre sc v) / (2 : ℝ) ^ sc) ^ (𝔭.tree.N : ℝ)) *
            (ENNReal.ofReal (((2 : ℝ) ^ sc) ^ (-1 / R)) *
              Lq R (fun z => ENNReal.ofReal (jb ((z - dyCentre sc v) / (2 : ℝ) ^ sc) ^ (-(𝔭.tree.N : ℝ)) *
                yNorm s' (tmult m F z)))) := by
  obtain ⟨-, hNf, hDf, -, -, hβ1, hβ2, hC1⟩ := h𝔭
  have hD2 : 2 ≤ 𝔭.D := le_trans (by have := classFloor_ge; omega) hDf
  have hβ0 : 0 ≤ 𝔭.β := by linarith
  have hβ3 : 𝔭.β ≤ 3 := by linarith
  obtain ⟨A, hA0, hA⟩ := exists_norm_fourierInv_bernN_le (𝔭.tree.N + 2)
  refine ⟨A, hA0, fun P _ s' hs' sc v c m hm F hF B hB x => ?_⟩
  have hℓ : (0 : ℝ) < (2 : ℝ) ^ sc := zpow_pos (by norm_num) _
  have hL : (0 : ℝ) < (2 : ℝ) ^ sc / 3 := by positivity
  have hb0 : (0 : ℝ) ≤ (𝔭.tree.N : ℝ) := Nat.cast_nonneg _
  refine weighted_sup hHC hℓ hb0 hA0 (K := fun w => ‖𝓕⁻ (bernN c ((2 : ℝ) ^ sc / 3)) w‖)
    (g := fun z => yNorm s' (tmult m F z)) (fun w => norm_nonneg _)
    (continuous_fourierInv_bernN c _ hL).norm.measurable (fun w => ?_) (measurable_yNorm_tmult hm hF)
    (fun z => CZ.yNorm_nonneg s' _) (fun x' => yNorm_tmult_le_integral_bernstein hs' hD2 hβ0 hβ3 hm hF hB x') x
  have h1 := hA c ((2 : ℝ) ^ sc / 3) hL w
  have h2 : (1 + |w| / ((2 : ℝ) ^ sc)) ^ (-((𝔭.tree.N + 2 : ℕ) : ℝ)) ≥ 0 := by positivity
  calc ‖𝓕⁻ (bernN c ((2 : ℝ) ^ sc / 3)) w‖
      ≤ A * ((2 : ℝ) ^ sc / 3)⁻¹ * (1 + |w| / ((2 : ℝ) ^ sc / 3)) ^ (-((𝔭.tree.N + 2 : ℕ) : ℝ)) := h1
    _ ≤ A * (3 / (2 : ℝ) ^ sc) * (1 + |w| / (2 : ℝ) ^ sc) ^ (-((𝔭.tree.N : ℝ) + 2)) := by
        have e1 : ((2 : ℝ) ^ sc / 3)⁻¹ = 3 / (2 : ℝ) ^ sc := by field_simp
        have e2 : (-((𝔭.tree.N + 2 : ℕ) : ℝ)) = -((𝔭.tree.N : ℝ) + 2) := by push_cast; ring
        rw [e1, e2]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by have : (0 : ℝ) ≤ (𝔭.tree.N : ℝ) := Nat.cast_nonneg _; linarith)
        have : |w| / (2 : ℝ) ^ sc ≤ |w| / ((2 : ℝ) ^ sc / 3) := by
          rw [div_le_div_iff₀ hℓ hL]; nlinarith [abs_nonneg w]
        linarith

end Slot

end PrimeBHT.TimeFrequency.X2
