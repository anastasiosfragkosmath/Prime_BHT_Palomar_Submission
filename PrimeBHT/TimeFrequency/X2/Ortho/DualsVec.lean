module

public import PrimeBHT.TimeFrequency.X2.Ortho.Duals
public import PrimeBHT.TimeFrequency.X2.Ortho.TreeToTile
public import PrimeBHT.TimeFrequency.X2.Ortho.TileBasicA
import PrimeBHT.Lift

/-!
# X2, node V10, Layer B: vector-valued duals and the fields (Z0)-(Z3) of `TileDualData`

For one tile with data `(ψ, m)` and `F : ℝ → ZMod P → ℂ`:
`vz ψ m F x y = dual ψ m (F · y) x`, `va ψ m F = ‖ψ T_m F‖_{L²(ℝ; L²(Y))}`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform ComplexConjugate ContDiff Real
open PrimeBHT.TimeFrequency.Tile PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

section Vec

variable {P : ℕ} [NeZero P]

/-- The vector dual. -/
def vz (ψ m : ℝ → ℂ) (F : ℝ → ZMod P → ℂ) (x : ℝ) : ZMod P → ℂ :=
  fun y => dual ψ m (fun z => F z y) x

/-- `‖ψ T_m F‖_{L²(ℝ; L²(Y))}`. -/
def va (ψ m : ℝ → ℂ) (F : ℝ → ZMod P → ℂ) : ℝ :=
  Real.sqrt (∫ x, yNorm 2 (ψ x • tmult m F x) ^ 2)

theorem va_nonneg (ψ m : ℝ → ℂ) (F : ℝ → ZMod P → ℂ) : 0 ≤ va ψ m F := Real.sqrt_nonneg _

variable {𝔭 : Params} {s v : ℤ} {c : ℝ} {ψ m : ℝ → ℂ} {F : ℝ → ZMod P → ℂ}

theorem coord_bound (_hF : Measurable F) {B : ℝ} (hB : ∀ x, yNorm 2 (F x) ≤ B) (y : ZMod P) :
    ∀ z, ‖F z y‖ ≤ (P : ℝ) ^ (2 : ℝ)⁻¹ * B := fun z =>
  (norm_apply_le_rpow_mul_yNorm (by norm_num) (F z) y).trans
    (mul_le_mul_of_nonneg_left (hB z) (by positivity))

omit [NeZero P] in
theorem measurable_coord (hF : Measurable F) (y : ZMod P) : Measurable fun z => F z y :=
  (measurable_pi_apply y).comp hF

theorem va_sq (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ) (hm : InMult 𝔭 s c m)
    (hF : Measurable F) {B : ℝ} (hB : ∀ x, yNorm 2 (F x) ≤ B) :
    va ψ m F ^ 2 = (P : ℝ)⁻¹ * ∑ y : ZMod P, ∫ w, ‖gfun ψ m (fun z => F z y) w‖ ^ 2 := by
  have hc : ∀ x y, (ψ x • tmult m F x) y = gfun ψ m (fun z => F z y) x := by
    intro x y; simp [gfun, tm, tmult]
  have hI : ∀ y : ZMod P, Integrable (fun w => ‖gfun ψ m (fun z => F z y) w‖ ^ 2) := fun y =>
    integrable_sq_gfun (by omega) (by omega) hβ hψ hm (measurable_coord hF y) (coord_bound hF hB y)
  unfold va
  rw [Real.sq_sqrt (integral_nonneg fun x => by positivity)]
  have : ∀ x, yNorm 2 (ψ x • tmult m F x) ^ 2 =
      (P : ℝ)⁻¹ * ∑ y : ZMod P, ‖gfun ψ m (fun z => F z y) x‖ ^ 2 := by
    intro x; rw [yNorm_two_sq]; simp_rw [hc]
  simp_rw [this]
  rw [integral_const_mul, integral_finsetSum _ fun y _ => hI y]

theorem dual_bdd (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ)
    (hm : InMult 𝔭 s c m) {f : ℝ → ℂ} (hf : Measurable f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) :
    ∃ M : ℝ, ∀ x, ‖dual ψ m f x‖ ≤ M := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  refine ⟨1 + (2 ^ 13 * 𝔭.β * 𝔭.C * 𝔭.C) ^ 2 * (2 / 11) * ((2 : ℝ) ^ s)⁻¹ * ∫ w, ‖gfun ψ m f w‖ ^ 2, fun x => ?_⟩
  have h1 := dual_norm_sq_le hN hD hβ hψ hm hf hB x
  have h2 := integral_kpsi_le hN hD hβ hψ hm x
  have hw := wt_le_one (q := 12) (by norm_num) (dyCentre s v) ((2 : ℝ) ^ s) x hL
  have hG : 0 ≤ ∫ w, ‖gfun ψ m f w‖ ^ 2 := integral_nonneg fun w => by positivity
  have hcoef : 0 ≤ (2 ^ 13 * 𝔭.β * 𝔭.C * 𝔭.C) ^ 2 * (2 / 11) * ((2 : ℝ) ^ s)⁻¹ := by
    have := inv_nonneg.2 hL.le; positivity
  have h3 : ∫ w, ‖𝓕⁻ m (w - x)‖ ^ 2 * ‖ψ w‖ ^ 2 ≤
      (2 ^ 13 * 𝔭.β * 𝔭.C * 𝔭.C) ^ 2 * (2 / 11) * ((2 : ℝ) ^ s)⁻¹ := by
    refine h2.trans ?_
    calc _ ≤ (2 ^ 13 * 𝔭.β * 𝔭.C * 𝔭.C) ^ 2 * (2 / 11) * ((2 : ℝ) ^ s)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hw hcoef
      _ = _ := mul_one _
  have h4 : ‖dual ψ m f x‖ ^ 2 ≤ (2 ^ 13 * 𝔭.β * 𝔭.C * 𝔭.C) ^ 2 * (2 / 11) * ((2 : ℝ) ^ s)⁻¹ *
      ∫ w, ‖gfun ψ m f w‖ ^ 2 := h1.trans (mul_le_mul_of_nonneg_right h3 hG)
  nlinarith [sq_nonneg (‖dual ψ m f x‖ - 1), norm_nonneg (dual ψ m f x)]

theorem measurable_vz (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ) (hm : InMult 𝔭 s c m)
    (hF : Measurable F) {B : ℝ} (hB : ∀ x, yNorm 2 (F x) ≤ B) : Measurable (vz ψ m F) :=
  measurable_pi_iff.2 fun y =>
    (continuous_dual hD hβ hψ hm (measurable_coord hF y) (coord_bound hF hB y)).measurable

/-- **(Z1)**. -/
theorem vz_inner_F (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ)
    (hm : InMult 𝔭 s c m) (hF : Measurable F) {B : ℝ} (hB : ∀ x, yNorm 2 (F x) ≤ B) :
    ∫ x, yInner (vz ψ m F x) (F x) = ((va ψ m F ^ 2 : ℝ) : ℂ) := by
  have hint : ∀ y : ZMod P, Integrable (fun x => dual ψ m (fun z => F z y) x *
      (starRingEnd ℂ) (F x y)) := by
    intro y
    have h1 := integrable_dual (by omega) (by omega) hβ hψ hm (measurable_coord hF y) (coord_bound hF hB y)
    have := h1.bdd_mul (f := fun x => (starRingEnd ℂ) (F x y)) (c := (P : ℝ) ^ (2 : ℝ)⁻¹ * B)
      (Complex.continuous_conj.measurable.comp (measurable_coord hF y)).aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Complex.norm_conj]; exact coord_bound hF hB y x)
    exact this.congr (Eventually.of_forall fun x => mul_comm _ _)
  have e1 : ∀ x, yInner (vz ψ m F x) (F x) =
      (P : ℂ)⁻¹ * ∑ y : ZMod P, dual ψ m (fun z => F z y) x * (starRingEnd ℂ) (F x y) := by
    intro x; rfl
  simp_rw [e1]
  rw [integral_const_mul, integral_finsetSum _ fun y _ => hint y]
  have e2 : ∀ y : ZMod P, ∫ x, dual ψ m (fun z => F z y) x * (starRingEnd ℂ) (F x y) =
      ((∫ w, ‖gfun ψ m (fun z => F z y) w‖ ^ 2 : ℝ) : ℂ) := by
    intro y
    rw [dual_inner_f (by omega) (by omega) hβ hψ hm (measurable_coord hF y) (coord_bound hF hB y),
      integral_complex_ofReal]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [gfun, norm_mul]
    unfold tm; ring
  simp_rw [e2]
  rw [va_sq hN hD hβ hψ hm hF hB]
  push_cast
  rfl

theorem wt_twelve_eq_sq (c L x : ℝ) (hL : 0 < L) : wt 12 c L x = wt 6 c L x * wt 6 c L x := by
  unfold wt
  have h : 0 < 1 + |x - c| / L := by positivity
  rw [← Real.rpow_add h]; norm_num

/-- **(Z2)**. -/
theorem vz_bound (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ)
    (hm : InMult 𝔭 s c m) (hF : Measurable F) {B : ℝ} (hB : ∀ x, yNorm 2 (F x) ≤ B) (x : ℝ) :
    yNorm 2 (vz ψ m F x) ≤ (2 ^ 13 * 𝔭.β * 𝔭.C * 𝔭.C) * ((2 : ℝ) ^ s) ^ (-(1 : ℝ) / 2) * va ψ m F *
      wt 6 (dyCentre s v) ((2 : ℝ) ^ s) x := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  have hC := nonneg_C_of_inPsi hψ
  set C₀ : ℝ := 2 ^ 13 * 𝔭.β * 𝔭.C * 𝔭.C with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  set L : ℝ := (2 : ℝ) ^ s with hLdef
  have hcoord : ∀ y : ZMod P, ‖vz ψ m F x y‖ ^ 2 ≤
      (∫ w, ‖𝓕⁻ m (w - x)‖ ^ 2 * ‖ψ w‖ ^ 2) * ∫ w, ‖gfun ψ m (fun z => F z y) w‖ ^ 2 := fun y =>
    dual_norm_sq_le hN hD hβ hψ hm (measurable_coord hF y) (coord_bound hF hB y) x
  have hsq : yNorm 2 (vz ψ m F x) ^ 2 ≤
      (∫ w, ‖𝓕⁻ m (w - x)‖ ^ 2 * ‖ψ w‖ ^ 2) * va ψ m F ^ 2 := by
    rw [yNorm_two_sq, va_sq hN hD hβ hψ hm hF hB, mul_left_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun y _ => hcoord y
  have hW := integral_kpsi_le hN hD hβ hψ hm x
  have h12 := wt_twelve_eq_sq (dyCentre s v) L x hL
  have hLhalf : L ^ (-(1 : ℝ) / 2) * L ^ (-(1 : ℝ) / 2) = L⁻¹ := by
    rw [← Real.rpow_add hL, show (-(1 : ℝ) / 2 + -(1 : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one]
  have hv0 := va_nonneg ψ m F
  have hw0 := (wt_pos 6 (dyCentre s v) L x hL).le
  have hrpow0 : 0 ≤ L ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hL.le _
  have hfinal : yNorm 2 (vz ψ m F x) ^ 2 ≤
      (C₀ * L ^ (-(1 : ℝ) / 2) * va ψ m F * wt 6 (dyCentre s v) L x) ^ 2 := by
    refine hsq.trans ?_
    calc (∫ w, ‖𝓕⁻ m (w - x)‖ ^ 2 * ‖ψ w‖ ^ 2) * va ψ m F ^ 2
        ≤ (C₀ ^ 2 * (2 / 11) * L⁻¹ * wt 12 (dyCentre s v) L x) * va ψ m F ^ 2 :=
          mul_le_mul_of_nonneg_right hW (sq_nonneg _)
      _ ≤ (C₀ ^ 2 * 1 * L⁻¹ * (wt 6 (dyCentre s v) L x * wt 6 (dyCentre s v) L x)) * va ψ m F ^ 2 := by
          rw [h12]
          have : 0 ≤ C₀ ^ 2 * L⁻¹ * (wt 6 (dyCentre s v) L x * wt 6 (dyCentre s v) L x) * va ψ m F ^ 2 := by
            have := inv_nonneg.2 hL.le; positivity
          nlinarith
      _ = _ := by rw [← hLhalf]; ring
  exact (pow_le_pow_iff_left₀ (by unfold yNorm; positivity) (by positivity) two_ne_zero).1 hfinal

/-- **(Z3)**. -/
theorem vz_orth {s' v' : ℤ} {c' : ℝ} {ψ' m' : ℝ → ℂ} (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β)
    (hβ3 : 𝔭.β ≤ 3) (hψ : InPsi 𝔭 s v ψ) (hψ' : InPsi 𝔭 s' v' ψ') (hm : InMult 𝔭 s c m)
    (hm' : InMult 𝔭 s' c' m') (hF : Measurable F) {B : ℝ} (hB : ∀ x, yNorm 2 (F x) ≤ B)
    (hdisj : Disjoint (Set.Ico (c - 3 * (2 : ℝ) ^ (-s) / 2) (c + 3 * (2 : ℝ) ^ (-s) / 2))
      (Set.Ico (c' - 3 * (2 : ℝ) ^ (-s') / 2) (c' + 3 * (2 : ℝ) ^ (-s') / 2))) :
    ∫ x, yInner (vz ψ m F x) (vz ψ' m' F x) = 0 := by
  have hint : ∀ y : ZMod P, Integrable (fun x => dual ψ m (fun z => F z y) x *
      (starRingEnd ℂ) (dual ψ' m' (fun z => F z y) x)) := by
    intro y
    have h1 := integrable_dual (by omega) (by omega) hβ hψ hm (measurable_coord hF y) (coord_bound hF hB y)
    obtain ⟨M, hM⟩ := dual_bdd hN hD hβ hψ' hm' (measurable_coord hF y) (coord_bound hF hB y)
    have hc' := continuous_dual (by omega) hβ hψ' hm' (measurable_coord hF y) (coord_bound hF hB y)
    have := h1.bdd_mul (f := fun x => (starRingEnd ℂ) (dual ψ' m' (fun z => F z y) x)) (c := M)
      (Complex.continuous_conj.measurable.comp hc'.measurable).aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Complex.norm_conj]; exact hM x)
    exact this.congr (Eventually.of_forall fun x => mul_comm _ _)
  have e1 : ∀ x, yInner (vz ψ m F x) (vz ψ' m' F x) =
      (P : ℂ)⁻¹ * ∑ y : ZMod P, dual ψ m (fun z => F z y) x *
        (starRingEnd ℂ) (dual ψ' m' (fun z => F z y) x) := by
    intro x; rfl
  simp_rw [e1]
  rw [integral_const_mul, integral_finsetSum _ fun y _ => hint y]
  have e2 : ∀ y : ZMod P, ∫ x, dual ψ m (fun z => F z y) x *
      (starRingEnd ℂ) (dual ψ' m' (fun z => F z y) x) = 0 := fun y =>
    dual_orthogonal (by omega) (by omega) hβ hβ3 hψ hψ' hm hm' (measurable_coord hF y)
      (measurable_coord hF y) (coord_bound hF hB y) (coord_bound hF hB y) hdisj
  simp_rw [e2]
  simp

end Vec

end PrimeBHT.TimeFrequency.X2
