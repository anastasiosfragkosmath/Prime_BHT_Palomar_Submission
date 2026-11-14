module

public import PrimeBHT.TimeFrequency.X2.Ortho.TreeScalar
public import PrimeBHT.TimeFrequency.X2.Ortho.TileEng
import PrimeBHT.Lift

/-!
# X2, node V10: `OrthoTreeToTile` proved (DPLMV `l:ortho0`, operator form)

`ortho_tree_to_tile`: for a `k`-lacunary tree `T` of rank-1 boxes (any top `t`), `β + 2δ < 3`,

  `|I_t| · topNorm(F; T; 2)² ≤ K ∑_{R ∈ T} |I_R| · tileEng_{𝔭.decN 10}(R)²`.

The proof reduces the vector statement to the scalar `L²` bound `tree_scalar_bound` coordinatewise in `y`
(`yNorm 2 v ² = P⁻¹ ∑_y |v_y|²`), and the sup over tree data to the pointwise-in-data inequality.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform ComplexConjugate ContDiff Real
open PrimeBHT.TimeFrequency.Tile PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

section VecScalar

variable {P : ℕ} [NeZero P]

theorem yNorm_two_sq (G : ZMod P → ℂ) : yNorm 2 G ^ 2 = (P : ℝ)⁻¹ * ∑ y, ‖G y‖ ^ 2 := by
  have h2 : yNorm 2 G ^ (2 : ℝ) = (P : ℝ)⁻¹ * ∑ y, ‖G y‖ ^ (2 : ℝ) :=
    PrimeBHT.Lift.yNorm_rpow_self (by norm_num) G
  simpa only [Real.rpow_two] using h2

theorem integrable_sq_of_bdd {u : ℝ → ℂ} (hu : Integrable u) (hc : Continuous u) {M : ℝ}
    (hM : ∀ x, ‖u x‖ ≤ M) : Integrable (fun x => ‖u x‖ ^ 2) := by
  refine (hu.norm.const_mul M).mono' (hc.norm.pow 2).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have h2 : 0 ≤ ‖u x‖ := norm_nonneg _
  simp only [norm_pow, norm_norm]
  nlinarith [hM x]

theorem eLpNorm_sq_eq {S : ℝ → ZMod P → ℂ} (hm : AEStronglyMeasurable (fun x => yNorm 2 (S x)) volume)
    (hi : Integrable (fun x => yNorm 2 (S x) ^ 2) volume) :
    eLpNorm (fun x => yNorm 2 (S x)) (ENNReal.ofReal 2) volume ^ (2 : ℝ) =
      ENNReal.ofReal (∫ x, yNorm 2 (S x) ^ 2) := by
  rw [ENNReal.ofReal_ofNat, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hm]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_mul]
  have e : ∀ x : ℝ, ‖yNorm 2 (S x)‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (yNorm 2 (S x) ^ 2) := by
    intro x
    rw [Real.enorm_eq_ofReal (by unfold yNorm; positivity), ENNReal.ofReal_rpow_of_nonneg
      (by unfold yNorm; positivity) (by norm_num), Real.rpow_two]
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => by positivity)]
  norm_num

theorem ofReal_mul_treeOpNorm_sq (s : ℝ) (Tr : Finset TriTile) (t : Top) (ψ m : TriTile → ℝ → ℂ)
    (F : ℝ → ZMod P → ℂ) :
    ENNReal.ofReal ((2 : ℝ) ^ t.1.1) * treeOpNorm s 2 Tr t ψ m F ^ (2 : ℝ) =
      eLpNorm (fun x => yNorm s (treeOp Tr ψ m F x)) (ENNReal.ofReal 2) volume ^ (2 : ℝ) := by
  unfold treeOpNorm
  have ha : (0 : ℝ) < (2 : ℝ) ^ t.1.1 := zpow_pos (by norm_num) _
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_nonneg
    (Real.rpow_nonneg ha.le _) (by norm_num), ← mul_assoc, ← ENNReal.ofReal_mul ha.le]
  have : (2 : ℝ) ^ t.1.1 * (((2 : ℝ) ^ t.1.1) ^ (-1 / (2 : ℝ))) ^ (2 : ℝ) = 1 := by
    rw [← Real.rpow_mul ha.le]
    norm_num
    rw [Real.rpow_neg_one]; field_simp
  rw [this]; simp

/-- The vector-valued tree estimate: `∫ yNorm²(T_T F) ≤ 2 Σ⁻¹ ∑_R ∫ yNorm²(ψ̃_R T_{m_R} F)`. -/
theorem vec_tree_bound {𝔭 : Params} (hN : 14 ≤ 𝔭.N) (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β)
    (hβδ : 𝔭.β + 2 * 𝔭.δ ≤ 3) {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {k : Fin 3}
    {T : Finset TriTile} (hT : IsLacunary k T) (hbox : ∀ R ∈ T, R.box ∈ Qs) {ψ m : TriTile → ℝ → ℂ}
    (hdata : ∀ R ∈ T, InPsi 𝔭 R.box.scale R.pos (ψ R) ∧
      InMult 𝔭 R.box.scale (R.box.centre k) (m R))
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {B : ℝ} (hB : ∀ x, yNorm 2 (F x) ≤ B) :
    Integrable (fun x => yNorm 2 (treeOp T ψ m F x) ^ 2) ∧
      (∀ R ∈ T, Integrable (fun x => yNorm 2 (psiTilde R.box.scale R.pos (ψ R) x • tmult (m R) F x) ^ 2)) ∧
      ∫ x, yNorm 2 (treeOp T ψ m F x) ^ 2 ≤ 2 * sInv * ∑ R ∈ T,
        ∫ x, yNorm 2 (psiTilde R.box.scale R.pos (ψ R) x • tmult (m R) F x) ^ 2 := by
  classical
  have hN2 : 2 ≤ 𝔭.N := by omega
  have hN' : 2 ≤ (𝔭.decN 10).N := by simp only [Params.decN]; omega
  have hP : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
  set Bc : ℝ := (P : ℝ) ^ (2 : ℝ)⁻¹ * B with hBc
  have hBc' : ∀ y z, ‖F z y‖ ≤ Bc := fun y z =>
    (norm_apply_le_rpow_mul_yNorm (by norm_num) (F z) y).trans
      (mul_le_mul_of_nonneg_left (hB z) (by positivity))
  have hfy : ∀ y : ZMod P, Measurable fun z => F z y := fun y => (measurable_pi_apply y).comp hF
  have hψt : ∀ R ∈ T, InPsi (𝔭.decN 10) R.box.scale R.pos (psiTilde R.box.scale R.pos (ψ R)) :=
    fun R hR => inPsi_psiTilde hN (hdata R hR).1
  -- coordinates
  have hc1 : ∀ x y, treeOp T ψ m F x y = ∑ R ∈ T, gfun (ψ R) (m R) (fun z => F z y) x := by
    intro x y
    simp [treeOp, gfun, tm, tmult, Finset.sum_apply]
  have hc2 : ∀ R x y, (psiTilde R.box.scale R.pos (ψ R) x • tmult (m R) F x) y =
      gfun (psiTilde R.box.scale R.pos (ψ R)) (m R) (fun z => F z y) x := by
    intro R x y
    simp [gfun, tm, tmult]
  -- integrability of the coordinate squares
  have hI1 : ∀ y : ZMod P, Integrable (fun x => ‖∑ R ∈ T, gfun (ψ R) (m R) (fun z => F z y) x‖ ^ 2) := by
    intro y
    refine integrable_sq_of_bdd (u := fun x => ∑ R ∈ T, gfun (ψ R) (m R) (fun z => F z y) x)
      (integrable_finsetSum _ fun R hR => integrable_gfun hN2 hD hβ (hdata R hR).1 (hdata R hR).2
        (hfy y) (hBc' y))
      (continuous_finsetSum _ fun R hR => continuous_gfun hD hβ (hdata R hR).1 (hdata R hR).2
        (hfy y) (hBc' y))
      (M := ∑ R ∈ T, 𝔭.C * (Bc * ∫ w, ‖𝓕⁻ (m R) w‖)) fun x => ?_
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun R hR => ?_)
    exact norm_gfun_le hD hβ (hdata R hR).1 (hdata R hR).2 (hBc' y) x
  have hI2 : ∀ R ∈ T, ∀ y : ZMod P, Integrable (fun x => ‖gfun (psiTilde R.box.scale R.pos (ψ R)) (m R)
      (fun z => F z y) x‖ ^ 2) := fun R hR y =>
    integrable_sq_gfun (𝔭 := 𝔭.decN 10) hN' hD hβ (hψt R hR) (hdata R hR).2 (hfy y) (hBc' y)
  -- squares as sums over coordinates
  have hS1 : ∀ x, yNorm 2 (treeOp T ψ m F x) ^ 2 =
      (P : ℝ)⁻¹ * ∑ y, ‖∑ R ∈ T, gfun (ψ R) (m R) (fun z => F z y) x‖ ^ 2 := by
    intro x; rw [yNorm_two_sq]; simp_rw [hc1]
  have hS2 : ∀ R x, yNorm 2 (psiTilde R.box.scale R.pos (ψ R) x • tmult (m R) F x) ^ 2 =
      (P : ℝ)⁻¹ * ∑ y, ‖gfun (psiTilde R.box.scale R.pos (ψ R)) (m R) (fun z => F z y) x‖ ^ 2 := by
    intro R x; rw [yNorm_two_sq]; simp_rw [hc2]
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [hS1]
    exact (integrable_finsetSum _ fun y _ => hI1 y).const_mul _
  · intro R hR
    simp_rw [hS2]
    exact (integrable_finsetSum _ fun y _ => hI2 R hR y).const_mul _
  · simp_rw [hS1, hS2]
    rw [integral_const_mul, integral_finsetSum _ fun y _ => hI1 y]
    have hscal : ∀ y : ZMod P, ∫ x, ‖∑ R ∈ T, gfun (ψ R) (m R) (fun z => F z y) x‖ ^ 2 ≤
        2 * sInv * ∑ R ∈ T, ∫ x, ‖gfun (psiTilde R.box.scale R.pos (ψ R)) (m R) (fun z => F z y) x‖ ^ 2 :=
      fun y => tree_scalar_bound hN hD hβ hβδ hQ hT hbox hdata (hfy y) (hBc' y)
    calc (P : ℝ)⁻¹ * ∑ y, ∫ x, ‖∑ R ∈ T, gfun (ψ R) (m R) (fun z => F z y) x‖ ^ 2
        ≤ (P : ℝ)⁻¹ * ∑ y, 2 * sInv * ∑ R ∈ T, ∫ x, ‖gfun (psiTilde R.box.scale R.pos (ψ R)) (m R)
            (fun z => F z y) x‖ ^ 2 := by
          gcongr with y _
          exact hscal y
      _ = 2 * sInv * ∑ R ∈ T, (P : ℝ)⁻¹ * ∑ y, ∫ x, ‖gfun (psiTilde R.box.scale R.pos (ψ R)) (m R)
            (fun z => F z y) x‖ ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp_rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun y _ => by ring
      _ = _ := by
          congr 1
          refine Finset.sum_congr rfl fun R hR => ?_
          rw [integral_const_mul, integral_finsetSum _ fun y _ => hI2 R hR y]

end VecScalar

/-- **`OrthoTreeToTile` (DPLMV `l:ortho0`, operator form)**.  For `𝔭` admissible with `β + 2δ < 3`. -/
theorem ortho_tree_to_tile (𝔭 : Params) (h𝔭 : 𝔭.Admissible) (hβδ : 𝔭.β + 2 * 𝔭.δ < 3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (P : ℕ) [NeZero P] (Qs : Set Box), IsRankOne 𝔭.J Qs →
      ∀ (k : Fin 3) (T : Finset TriTile) (t : Top), IsTree T t → IsLacunary k T →
        (∀ R ∈ T, R.box ∈ Qs) → ∀ (F : ℝ → ZMod P → ℂ) (B : ℝ), Measurable F →
          (∀ x, yNorm 2 (F x) ≤ B) →
            ENNReal.ofReal ((2 : ℝ) ^ t.1.1) * topNorm 𝔭 2 k F T t 2 ^ (2 : ℝ) ≤
              ENNReal.ofReal K * ∑ R ∈ T, ENNReal.ofReal ((2 : ℝ) ^ R.box.scale) *
                tileEng (𝔭.decN 10) k F R ^ (2 : ℝ) := by
  classical
  obtain ⟨-, hNge, hDge, -, -, hβ1, -, -⟩ := h𝔭
  have hN14 : 14 ≤ 𝔭.N := by have : classFloor = 400 := rfl; omega
  have hD2 : 2 ≤ 𝔭.D := by have : classFloor = 400 := rfl; omega
  have hβ0 : 0 ≤ 𝔭.β := by linarith
  refine ⟨2 * sInv, by have := sInv_nonneg; positivity, ?_⟩
  intro P _ Qs hQ k T t _ hlac hbox F B hF hB
  set 𝔭' := 𝔭.decN 10 with h𝔭'
  set RHS : ℝ≥0∞ := ∑ R ∈ T, ENNReal.ofReal ((2 : ℝ) ^ R.box.scale) * tileEng 𝔭' k F R ^ (2 : ℝ) with hRHS
  have ha : 0 < ENNReal.ofReal ((2 : ℝ) ^ t.1.1) := ENNReal.ofReal_pos.2 (zpow_pos (by norm_num) _)
  have ha' : ENNReal.ofReal ((2 : ℝ) ^ t.1.1) ≠ ⊤ := ENNReal.ofReal_ne_top
  -- the inequality for each choice of data
  have hdat : ∀ ψ m : TriTile → ℝ → ℂ, IsTreeOpData 𝔭 k T ψ m →
      ENNReal.ofReal ((2 : ℝ) ^ t.1.1) * treeOpNorm 2 2 T t ψ m F ^ (2 : ℝ) ≤
        ENNReal.ofReal (2 * sInv) * RHS := by
    intro ψ m hψm
    have hdata := hψm.1
    obtain ⟨hi1, hi2, hle⟩ := vec_tree_bound hN14 hD2 hβ0 hβδ.le hQ hlac hbox hdata hF hB
    have hψt : ∀ R ∈ T, InPsi 𝔭' R.box.scale R.pos (psiTilde R.box.scale R.pos (ψ R)) :=
      fun R hR => inPsi_psiTilde hN14 (hdata R hR).1
    have hmeas : Measurable (treeOp T ψ m F) :=
      Finset.measurable_sum _ fun R hR => measurable_psi_smul_tmult (hdata R hR).1 (hdata R hR).2 hF
    have hmeasN : AEStronglyMeasurable (fun x => yNorm 2 (treeOp T ψ m F x)) volume :=
      ((measurable_yNorm_fun 2).comp hmeas).aestronglyMeasurable
    rw [ofReal_mul_treeOpNorm_sq, eLpNorm_sq_eq hmeasN hi1]
    refine (ENNReal.ofReal_le_ofReal hle).trans ?_
    rw [ENNReal.ofReal_mul (by have := sInv_nonneg; positivity),
      ENNReal.ofReal_sum_of_nonneg (fun R _ => integral_nonneg fun x => by positivity)]
    refine mul_le_mul' le_rfl (Finset.sum_le_sum fun R hR => ?_)
    -- single-tile comparison
    set V : ℝ → ZMod P → ℂ := fun x => psiTilde R.box.scale R.pos (ψ R) x • tmult (m R) F x with hV
    have hmV : Measurable V :=
      measurable_psi_smul_tmult (𝔭 := 𝔭') (hψt R hR) (hdata R hR).2 hF
    have hmVN : AEStronglyMeasurable (fun x => yNorm 2 (V x)) volume :=
      ((measurable_yNorm_fun 2).comp hmV).aestronglyMeasurable
    rw [← eLpNorm_sq_eq hmVN (hi2 R hR)]
    have hdR : IsTreeOpData 𝔭' k {R} (fun _ => psiTilde R.box.scale R.pos (ψ R)) (fun _ => m R) := by
      refine ⟨fun Q hQ => ?_, fun Q _ Q' _ _ => rfl⟩
      rw [Finset.mem_singleton] at hQ
      rw [hQ]
      exact ⟨hψt R hR, (hdata R hR).2⟩
    have h1 := le_topNorm (𝔭 := 𝔭') (s := 2) (F := F) (t := ((R.box.scale, R.pos), (0 : ℝ))) (q := 2) hdR
    have h2 := ofReal_mul_treeOpNorm_sq 2 {R} ((R.box.scale, R.pos), (0 : ℝ))
      (fun _ => psiTilde R.box.scale R.pos (ψ R)) (fun _ => m R) F
    have hsing : (fun x => yNorm 2 (treeOp {R} (fun _ => psiTilde R.box.scale R.pos (ψ R)) (fun _ => m R) F x)) =
        fun x => yNorm 2 (V x) := by
      funext x; simp [treeOp, hV]
    rw [hsing] at h2
    rw [← h2]
    unfold tileEng
    exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow h1 (by norm_num))
  -- take the supremum over the data
  set c : ℝ≥0∞ := (ENNReal.ofReal ((2 : ℝ) ^ t.1.1))⁻¹ * (ENNReal.ofReal (2 * sInv) * RHS) with hc
  have htop : topNorm 𝔭 2 k F T t 2 ≤ c ^ ((1 : ℝ) / 2) := by
    refine topNorm_le_of_forall fun ψ m hψm => ?_
    have h1 := hdat ψ m hψm
    have h2 : treeOpNorm 2 2 T t ψ m F ^ (2 : ℝ) ≤ c := by
      calc treeOpNorm 2 2 T t ψ m F ^ (2 : ℝ) =
            (ENNReal.ofReal ((2 : ℝ) ^ t.1.1))⁻¹ * (ENNReal.ofReal ((2 : ℝ) ^ t.1.1) *
              treeOpNorm 2 2 T t ψ m F ^ (2 : ℝ)) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel ha.ne' ha', one_mul]
        _ ≤ c := by rw [hc]; exact mul_le_mul' le_rfl h1
    calc treeOpNorm 2 2 T t ψ m F = (treeOpNorm 2 2 T t ψ m F ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
          rw [← ENNReal.rpow_mul]; norm_num
      _ ≤ _ := ENNReal.rpow_le_rpow h2 (by norm_num)
  have hsq : topNorm 𝔭 2 k F T t 2 ^ (2 : ℝ) ≤ c := by
    calc topNorm 𝔭 2 k F T t 2 ^ (2 : ℝ) ≤ (c ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow htop (by norm_num)
      _ = c := by rw [← ENNReal.rpow_mul]; norm_num
  calc ENNReal.ofReal ((2 : ℝ) ^ t.1.1) * topNorm 𝔭 2 k F T t 2 ^ (2 : ℝ) ≤
        ENNReal.ofReal ((2 : ℝ) ^ t.1.1) * c := mul_le_mul' le_rfl hsq
    _ = ENNReal.ofReal (2 * sInv) * RHS := by
        rw [hc, ← mul_assoc, ENNReal.mul_inv_cancel ha.ne' ha', one_mul]

end PrimeBHT.TimeFrequency.X2
