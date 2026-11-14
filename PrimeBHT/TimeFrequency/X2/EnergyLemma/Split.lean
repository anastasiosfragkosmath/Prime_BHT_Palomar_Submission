module

public import PrimeBHT.TimeFrequency.X2.EnergyLemma.Defs
public import PrimeBHT.TimeFrequency.X2.Ortho.TileEng
import PrimeBHT.TimeFrequency.X2.CZ.Minkowski
import PrimeBHT.TimeFrequency.X2.ClassKernel
import PrimeBHT.Interface.X2Checks

/-!
# X2, node V12: splitting trees and the localization transfer for tree norms

* `topNorm_le_add_filter`: `topNorm` of a tree is at most the sum of the `topNorm` of the two parts of a partition
  of the tile set (same top): triangle inequality in `L^q(L^s)`, `s, q ≥ 1`;
* `topNorm_le_loc`: for a tree inside a window `W` and `F = p_W g`, `topNorm_𝔭 F ≤ K topNorm_{𝔭.loc} g`
  (from `treeOp_locPoly`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

theorem IsTreeOpData.mono {𝔭 : Params} {k : Fin 3} {Tr Tr' : Finset TriTile} {ψ m : TriTile → ℝ → ℂ}
    (h : IsTreeOpData 𝔭 k Tr ψ m) (hsub : Tr' ⊆ Tr) : IsTreeOpData 𝔭 k Tr' ψ m :=
  ⟨fun Q hQ => h.1 Q (hsub hQ), fun Q hQ Q' hQ' => h.2 Q (hsub hQ) Q' (hsub hQ')⟩

theorem measurable_treeOp {P : ℕ} {𝔭 : Params} {k : Fin 3} {Tr : Finset TriTile} {ψ m : TriTile → ℝ → ℂ}
    (h : IsTreeOpData 𝔭 k Tr ψ m) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) :
    Measurable (treeOp Tr ψ m F) := by
  unfold treeOp
  exact Finset.measurable_sum _ fun Q hQ =>
    measurable_psi_smul_tmult (h.1 Q hQ).1 (h.1 Q hQ).2 hF

theorem measurable_yNorm_treeOp {P : ℕ} [NeZero P] {𝔭 : Params} {k : Fin 3} {Tr : Finset TriTile}
    {ψ m : TriTile → ℝ → ℂ} (h : IsTreeOpData 𝔭 k Tr ψ m) {F : ℝ → ZMod P → ℂ} (hF : Measurable F)
    (s : ℝ) : Measurable (fun x => yNorm s (treeOp Tr ψ m F x)) :=
  (measurable_yNorm_fun s).comp (measurable_treeOp h hF)

/-! ## Localization transfer -/

theorem one_le_locPoly (W : ℤ × ℤ) (x : ℝ) : 1 ≤ locPoly W x := by
  unfold locPoly
  have : Even locLoss := ⟨50, by unfold locLoss; rfl⟩
  linarith [this.pow_nonneg ((x - dyCentre W.1 W.2) / (2 : ℝ) ^ W.1)]

theorem zero_lt_locPoly (W : ℤ × ℤ) (x : ℝ) : 0 < locPoly W x := lt_of_lt_of_le one_pos (one_le_locPoly W x)

theorem measurable_locPoly (W : ℤ × ℤ) : Measurable (locPoly W) := by
  unfold locPoly
  fun_prop

/-- `g = F / p_W`. -/
def locDiv {P : ℕ} (W : ℤ × ℤ) (F : ℝ → ZMod P → ℂ) : ℝ → ZMod P → ℂ :=
  fun x => ((locPoly W x)⁻¹ : ℂ) • F x

theorem locDiv_measurable {P : ℕ} (W : ℤ × ℤ) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) :
    Measurable (locDiv W F) := by
  unfold locDiv
  have hc : Measurable fun x => ((locPoly W x)⁻¹ : ℂ) :=
    (Complex.measurable_ofReal.comp (measurable_locPoly W)).inv
  refine measurable_pi_iff.2 fun y => ?_
  show Measurable fun x => ((locPoly W x)⁻¹ : ℂ) * F x y
  exact hc.mul ((measurable_pi_apply y).comp hF)

theorem locDiv_smul {P : ℕ} (W : ℤ × ℤ) (F : ℝ → ZMod P → ℂ) :
    (fun x => ((locPoly W x : ℝ) : ℂ) • locDiv W F x) = F := by
  funext x
  unfold locDiv
  have h : ((locPoly W x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_locPoly W x).ne'
  rw [smul_smul, mul_inv_cancel₀ h, one_smul]

theorem yNorm_locDiv_le {P : ℕ} [NeZero P] {s : ℝ} (hs : 0 < s) (W : ℤ × ℤ) (F : ℝ → ZMod P → ℂ)
    (x : ℝ) : yNorm s (locDiv W F x) ≤ yNorm s (F x) := by
  unfold locDiv
  rw [PrimeBHT.Interface.X2.yNorm_smul hs]
  have h1 : (1 : ℝ) ≤ locPoly W x := one_le_locPoly W x
  have h2 : ‖((locPoly W x)⁻¹ : ℂ)‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (zero_lt_locPoly W x).le]
    exact inv_le_one_of_one_le₀ h1
  calc ‖((locPoly W x)⁻¹ : ℂ)‖ * yNorm s (F x) ≤ 1 * yNorm s (F x) :=
        mul_le_mul_of_nonneg_right h2 (yNorm_nonneg' _ _)
    _ = _ := one_mul _

/-- A bound for `yNorm s` gives a bound for `yNorm 2` (finite `Y_P`). -/
theorem yNorm_two_le_rpow_mul {P : ℕ} [NeZero P] {s : ℝ} (hs : 0 < s) (G : ZMod P → ℂ) :
    yNorm 2 G ≤ (P : ℝ) ^ s⁻¹ * yNorm s G :=
  PrimeBHT.Interface.X2.yNorm_le (by norm_num) G fun y => norm_apply_le_rpow_mul_yNorm hs G y

/-- **Class transfer** (B6' of the V16 route check): a tree norm of `F = p_W g` in the class `𝔭` is bounded by a
constant times the tree norm of `g` in the class `𝔭.loc`, for trees inside the window `W`. -/
theorem topNorm_le_loc (𝔭 : Params) (h𝔭 : 𝔭.loc.Admissible) {s q : ℝ} (hs : 1 ≤ s) (hq : 1 ≤ q) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (P : ℕ) [NeZero P] (k : Fin 3) (W : ℤ × ℤ) (g : ℝ → ZMod P → ℂ), Measurable g →
      (∃ B, ∀ x, yNorm 2 (g x) ≤ B) → ∀ (Tr : Finset TriTile) (t : Top),
        (∀ Q ∈ Tr, Q.I ⊆ dyadicInt W.1 W.2) →
          topNorm 𝔭 s k (fun x => ((locPoly W x : ℝ) : ℂ) • g x) Tr t q ≤
            ENNReal.ofReal K * topNorm 𝔭.loc s k g Tr t q := by
  obtain ⟨K₀, hK₀, hloc⟩ := treeOp_locPoly 𝔭 h𝔭
  have hs0 : 0 < s := by linarith
  refine ⟨((locLoss : ℝ) + 1) * (K₀ + 1), ?_, ?_⟩
  · have : (1 : ℝ) ≤ (locLoss : ℝ) + 1 := by
      have : (0 : ℝ) ≤ locLoss := Nat.cast_nonneg _
      linarith
    nlinarith
  intro P _ k W g hg hB Tr t hW
  refine topNorm_le_of_forall fun ψ m hdata => ?_
  obtain ⟨ψ', m', hdata', hid⟩ := hloc P k Tr ψ m hdata W hW
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.2 hq
  set F : ℝ → ZMod P → ℂ := fun x => ((locPoly W x : ℝ) : ℂ) • g x with hFdef
  -- pointwise bound
  have hpt : ∀ x, ‖yNorm s (treeOp Tr ψ m F x)‖ ≤
      ‖(K₀ • ∑ b : Fin (locLoss + 1), fun x => yNorm s (treeOp Tr (ψ' b) (m' b) g x)) x‖ := by
    intro x
    rw [Real.norm_of_nonneg (yNorm_nonneg' _ _), hid g hg hB x]
    rw [PrimeBHT.Interface.X2.yNorm_smul hs0, Complex.norm_real, Real.norm_of_nonneg hK₀]
    have h1 := CZ.yNorm_sum_le hs (Finset.univ : Finset (Fin (locLoss + 1)))
      (fun b => treeOp Tr (ψ' b) (m' b) g x)
    have h2 : 0 ≤ ∑ b : Fin (locLoss + 1), yNorm s (treeOp Tr (ψ' b) (m' b) g x) :=
      Finset.sum_nonneg fun b _ => yNorm_nonneg' _ _
    rw [Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
      Real.norm_of_nonneg (mul_nonneg hK₀ h2)]
    exact mul_le_mul_of_nonneg_left h1 hK₀
  have hmeas : AEStronglyMeasurable (fun x => yNorm s (treeOp Tr ψ m F x)) volume :=
    (measurable_yNorm_treeOp hdata (by
      have : F = fun x => ((locPoly W x : ℝ) : ℂ) • g x := hFdef
      rw [this]
      refine measurable_pi_iff.2 fun y => ?_
      show Measurable fun x => ((locPoly W x : ℝ) : ℂ) * g x y
      exact (Complex.measurable_ofReal.comp (measurable_locPoly W)).mul
        ((measurable_pi_apply y).comp hg)) s).aestronglyMeasurable
  have hL := eLpNorm_mono hmeas hpt (p := ENNReal.ofReal q) (μ := volume)
  have hL2 := (eLpNorm_const_smul_le (c := K₀) (p := ENNReal.ofReal q) (μ := volume)
    (f := ∑ b : Fin (locLoss + 1), fun x => yNorm s (treeOp Tr (ψ' b) (m' b) g x)))
  have hL3 := eLpNorm_sum_le (p := ENNReal.ofReal q) (μ := volume) (s := (Finset.univ : Finset (Fin (locLoss + 1))))
    (f := fun b => fun x => yNorm s (treeOp Tr (ψ' b) (m' b) g x)) hq1
  -- assemble
  have hterm : ∀ b : Fin (locLoss + 1),
      ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (-1 / q)) *
        eLpNorm (fun x => yNorm s (treeOp Tr (ψ' b) (m' b) g x)) (ENNReal.ofReal q) volume ≤
        topNorm 𝔭.loc s k g Tr t q := fun b =>
    le_topNorm (hdata' b)
  have hsumle : ∑ b : Fin (locLoss + 1),
      ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (-1 / q)) *
        eLpNorm (fun x => yNorm s (treeOp Tr (ψ' b) (m' b) g x)) (ENNReal.ofReal q) volume ≤
      ((locLoss + 1 : ℕ) : ℝ≥0∞) * topNorm 𝔭.loc s k g Tr t q := by
    calc _ ≤ ∑ _b : Fin (locLoss + 1), topNorm 𝔭.loc s k g Tr t q := Finset.sum_le_sum fun b _ => hterm b
      _ = _ := by simp
  unfold treeOpNorm
  calc ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (-1 / q)) *
        eLpNorm (fun x => yNorm s (treeOp Tr ψ m F x)) (ENNReal.ofReal q) volume
      ≤ ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (-1 / q)) *
          (‖K₀‖ₑ * ∑ b : Fin (locLoss + 1),
            eLpNorm (fun x => yNorm s (treeOp Tr (ψ' b) (m' b) g x)) (ENNReal.ofReal q) volume) := by
        gcongr
        exact hL.trans (hL2.trans (by gcongr))
    _ = ‖K₀‖ₑ * ∑ b : Fin (locLoss + 1), ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (-1 / q)) *
          eLpNorm (fun x => yNorm s (treeOp Tr (ψ' b) (m' b) g x)) (ENNReal.ofReal q) volume := by
        rw [← Finset.mul_sum]; ring
    _ ≤ ‖K₀‖ₑ * (((locLoss + 1 : ℕ) : ℝ≥0∞) * topNorm 𝔭.loc s k g Tr t q) := by gcongr
    _ ≤ ENNReal.ofReal (((locLoss : ℝ) + 1) * (K₀ + 1)) * topNorm 𝔭.loc s k g Tr t q := by
        rw [Real.enorm_eq_ofReal hK₀, ← mul_assoc, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul hK₀]
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
        push_cast
        have : (0 : ℝ) ≤ locLoss := Nat.cast_nonneg _
        nlinarith

end PrimeBHT.TimeFrequency.X2
