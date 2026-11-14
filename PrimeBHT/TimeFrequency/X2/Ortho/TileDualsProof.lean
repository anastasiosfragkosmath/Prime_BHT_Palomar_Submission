module

public import PrimeBHT.TimeFrequency.X2.Ortho.DualsVec
public import PrimeBHT.TimeFrequency.X2.Ortho.TileBasic
import PrimeBHT.Lift

/-!
# X2, node V10: `TileDuals` proved for admissible classes

Near-optimal data per tile (`near_opt`), the dual vectors `vz`, and the identification
`ofReal ĉ_R = treeOpNorm` of the one-tile tree.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform ComplexConjugate ContDiff Real
open PrimeBHT.TimeFrequency.Tile PrimeBHT.Statements

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

theorem isTreeOpData_zero (𝔭 : Params) (h𝔭 : 𝔭.Admissible) (k : Fin 3) (R : TriTile) :
    IsTreeOpData 𝔭 k {R} (fun _ _ => 0) (fun _ _ => 0) := by
  obtain ⟨-, -, -, -, -, -, -, hC⟩ := h𝔭
  have hC0 : 0 ≤ 𝔭.C := by linarith
  refine ⟨fun Q _ => ⟨⟨continuous_const, fun x => ?_, fun ξ _ => ?_⟩, ⟨contDiff_const, fun ξ _ => rfl, fun a _ ξ => ?_⟩⟩,
    fun Q _ Q' _ _ => rfl⟩
  · simp only [norm_zero]
    exact mul_nonneg hC0 (Real.rpow_nonneg (by have := one_le_jb ((x - dyCentre Q.box.scale Q.pos) / (2 : ℝ) ^ Q.box.scale); linarith) _)
  · simp [Real.fourier_real_eq]
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [hC0]
    · simp [hC0]

theorem integrable_piece_sq {P : ℕ} [NeZero P] {𝔭 : Params} {s v : ℤ} {c : ℝ} {ψ m : ℝ → ℂ}
    {F : ℝ → ZMod P → ℂ} (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ)
    (hm : InMult 𝔭 s c m) (hF : Measurable F) {B : ℝ} (hB : ∀ x, yNorm 2 (F x) ≤ B) :
    Integrable (fun x => yNorm 2 (ψ x • tmult m F x) ^ 2) := by
  have hc : ∀ x y, (ψ x • tmult m F x) y = gfun ψ m (fun z => F z y) x := by
    intro x y; simp [gfun, tm, tmult]
  have hI : ∀ y : ZMod P, Integrable (fun w => ‖gfun ψ m (fun z => F z y) w‖ ^ 2) := fun y =>
    integrable_sq_gfun (by omega) (by omega) hβ hψ hm (measurable_coord hF y) (coord_bound hF hB y)
  have : ∀ x, yNorm 2 (ψ x • tmult m F x) ^ 2 =
      (P : ℝ)⁻¹ * ∑ y : ZMod P, ‖gfun ψ m (fun z => F z y) x‖ ^ 2 := by
    intro x; rw [yNorm_two_sq]; simp_rw [hc]
  simp_rw [this]
  exact (integrable_finsetSum _ fun y _ => hI y).const_mul _

theorem near_opt {P : ℕ} [NeZero P] (𝔭 : Params) (h𝔭 : 𝔭.Admissible) (k : Fin 3)
    (F : ℝ → ZMod P → ℂ) (R : TriTile) (hfin : tileEng 𝔭 k F R ≠ ⊤) :
    ∃ ψ m : TriTile → ℝ → ℂ, IsTreeOpData 𝔭 k {R} ψ m ∧
      tileEng 𝔭 k F R ≤ 2 * treeOpNorm 2 2 {R} ((R.box.scale, R.pos), (0 : ℝ)) ψ m F := by
  by_cases h0 : tileEng 𝔭 k F R = 0
  · exact ⟨_, _, isTreeOpData_zero 𝔭 h𝔭 k R, by rw [h0]; exact zero_le⟩
  · have hlt : tileEng 𝔭 k F R / 2 < tileEng 𝔭 k F R := ENNReal.half_lt_self h0 hfin
    have hlt' : tileEng 𝔭 k F R / 2 < ⨆ (ψ : TriTile → ℝ → ℂ) (m : TriTile → ℝ → ℂ)
        (_ : IsTreeOpData 𝔭 k {R} ψ m), treeOpNorm 2 2 {R} ((R.box.scale, R.pos), (0 : ℝ)) ψ m F := hlt
    obtain ⟨ψ, hψ⟩ := lt_iSup_iff.1 hlt'
    obtain ⟨m, hm⟩ := lt_iSup_iff.1 hψ
    obtain ⟨hd, hv⟩ := lt_iSup_iff.1 hm
    refine ⟨ψ, m, hd, ?_⟩
    have := (ENNReal.div_le_iff (by norm_num) (by norm_num)).1 hv.le
    rw [mul_comm]; exact this

theorem ofReal_chat_eq {P : ℕ} [NeZero P] {𝔭 : Params} {F : ℝ → ZMod P → ℂ} {k : Fin 3} {R : TriTile}
    (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) {ψ m : TriTile → ℝ → ℂ}
    (hψ : InPsi 𝔭 R.box.scale R.pos (ψ R)) (hm : InMult 𝔭 R.box.scale (R.box.centre k) (m R))
    (hF : Measurable F) {B : ℝ} (hB : ∀ x, yNorm 2 (F x) ≤ B) :
    ENNReal.ofReal (chat (fun R' => va (ψ R') (m R') F) R) =
      treeOpNorm 2 2 {R} ((R.box.scale, R.pos), (0 : ℝ)) ψ m F := by
  have hsing : (fun x => yNorm 2 (treeOp {R} ψ m F x)) = fun x => yNorm 2 (ψ R x • tmult (m R) F x) := by
    funext x; simp [treeOp]
  have hmeas : Measurable fun x => ψ R x • tmult (m R) F x :=
    measurable_psi_smul_tmult hψ hm hF
  have hmN : AEStronglyMeasurable (fun x => yNorm 2 (ψ R x • tmult (m R) F x)) volume :=
    ((measurable_yNorm_fun 2).comp hmeas).aestronglyMeasurable
  have hint := integrable_piece_sq hN hD hβ hψ hm hF hB
  have he2 := eLpNorm_sq_eq hmN hint
  have hva := va_nonneg (ψ R) (m R) F
  have hsq : va (ψ R) (m R) F ^ 2 = ∫ x, yNorm 2 (ψ R x • tmult (m R) F x) ^ 2 :=
    Real.sq_sqrt (integral_nonneg fun x => by unfold yNorm; positivity)
  have he : eLpNorm (fun x => yNorm 2 (ψ R x • tmult (m R) F x)) (ENNReal.ofReal 2) volume =
      ENNReal.ofReal (va (ψ R) (m R) F) := by
    set e := eLpNorm (fun x => yNorm 2 (ψ R x • tmult (m R) F x)) (ENNReal.ofReal 2) volume
    have h1 : e = (e ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by rw [← ENNReal.rpow_mul]; norm_num
    rw [h1, he2, ← hsq, ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq hva]
  unfold treeOpNorm chat
  rw [hsing, he, ENNReal.ofReal_mul (Real.rpow_nonneg (tl_pos R).le _)]
  rfl

/-- **`TileDuals` for admissible classes.** -/
theorem tileDuals_of_admissible (𝔭 : Params) (h𝔭 : 𝔭.Admissible) : TileDuals 𝔭 := by
  have h𝔭' := h𝔭
  obtain ⟨-, hNge, hDge, -, -, hβ1, hβ3, hC1⟩ := h𝔭'
  have hN12 : 12 ≤ 𝔭.N := by have : classFloor = 400 := rfl; omega
  have hD12 : 12 ≤ 𝔭.D := by have : classFloor = 400 := rfl; omega
  have hβ0 : 0 ≤ 𝔭.β := by linarith
  have hC0 : 0 ≤ 𝔭.C := by linarith
  have hβ3' : 𝔭.β ≤ 3 := by linarith
  obtain ⟨C₃, hC₃, hE⟩ := tileEng_le 𝔭 h𝔭
  refine ⟨2 ^ 13 * 𝔭.β * 𝔭.C * 𝔭.C, by positivity, ?_⟩
  intro P _ Qs hQ k 𝒮 hbox F B hF hB
  have hfin : ∀ R, tileEng 𝔭 k F R ≠ ⊤ := fun R =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hE P k F B hF hB R)
  choose ψ m hdat hopt using fun R => near_opt 𝔭 h𝔭 k F R (hfin R)
  have hRd : ∀ R, InPsi 𝔭 R.box.scale R.pos (ψ R R) ∧
      InMult 𝔭 R.box.scale (R.box.centre k) (m R R) := fun R =>
    (hdat R).1 R (Finset.mem_singleton_self R)
  refine ⟨fun R => va (ψ R R) (m R R) F, fun R => vz (ψ R R) (m R R) F, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro R _; exact va_nonneg _ _ _
  · intro R _; exact measurable_vz (by omega) hβ0 (hRd R).1 (hRd R).2 hF hB
  · intro R _; exact vz_inner_F hN12 hD12 hβ0 (hRd R).1 (hRd R).2 hF hB
  · intro R _ x
    exact vz_bound hN12 hD12 hβ0 (hRd R).1 (hRd R).2 hF hB x
  · intro R _ R' _ hnc
    have hdis : Disjoint (dilate 3 (R.box.ω k)) (dilate 3 (R'.box.ω k)) :=
      Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hnc)
    rw [dilate_three_omega, dilate_three_omega] at hdis
    exact vz_orth hN12 hD12 hβ0 hβ3' (hRd R).1 (hRd R').1 (hRd R).2 (hRd R').2 hF hB hdis
  · intro R _
    -- State `hc` with `chat` unfolded: the kernel otherwise compares `chat a₁ R` with `chat a₂ R`
    -- argument-first (different functions `a₁ ≠ a₂`, equal only at `R`) and wastes seconds.
    have hc : ENNReal.ofReal ((tl R) ^ (-(1 : ℝ) / 2) * va (ψ R R) (m R R) F) =
        treeOpNorm 2 2 {R} ((R.box.scale, R.pos), (0 : ℝ)) (ψ R) (m R) F :=
      ofReal_chat_eq (𝔭 := 𝔭) (F := F) (k := k) (R := R) hN12 hD12 hβ0 (ψ := ψ R) (m := m R)
        (hRd R).1 (hRd R).2 hF hB
    refine ⟨?_, ?_⟩
    · exact (hopt R).trans (le_of_eq (congrArg (2 * ·) hc.symm))
    · exact hc.le.trans (le_topNorm (hdat R))

end PrimeBHT.TimeFrequency.X2
