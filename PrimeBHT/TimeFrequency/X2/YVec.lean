module

public import PrimeBHT.TimeFrequency.X2.Classes
public import PrimeBHT.TimeFrequency.X2.Interp.OperatorV
import PrimeBHT.TimeFrequency.X2.ClassKernel
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.MeanInequalities
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# X2, node V17 (instantiation data): the slot spaces `YVec P s` as normed types

`YVec P s` is a type synonym of `ZMod P → ℂ` carrying the norm `yNorm s` (`s ≥ 1`), so that the X1 theorem
R6c-I (`Interp.eLpNorm_le_of_restrictedStrong`, stated for general normed `F`, `E`) and the V17 chain
`X2/Interp/{FormV,OperatorV,StrongV}.lean` apply with `W := YVec P 2` (the Hilbert slots) and
`E := YVec P u'` (the output space `X_{u'}`).  This file supplies exactly the instantiation data left open by the
hand-back of `X2/Interp/StrongV.lean`:

* `NormedAddCommGroup`, `NormedSpace ℂ` (hence `NormedSpace ℝ`), `MeasurableSpace` (that of `ZMod P → ℂ`),
  `BorelSpace`, `SecondCountableTopology`, `SeparableSpace`; the topology and the measurable structure coincide
  with those of `ZMod P → ℂ` (`YVec.continuous_val`, `YVec.continuous_ofVal`);
* the injectivity obligation of the induced norm (inside the instance) and `YVec.norm_eq : ‖x‖ = yNorm s x`;
* `isSlotNorm_yNorm : IsSlotNorm (yNorm s)` (for `s > 0`);
* `yPair_le_yNorm_mul` (Hölder `‖⟨a, b⟩‖ ≤ yNorm u' a * yNorm u b`) and
  `isDualPairing_yPair : IsDualPairing (yNorm u) yPair` (`pr e v = yPair e v`; zero, Lipschitz field = Hölder,
  EXACT norming by the explicit map `e ↦ ‖e_y‖^{u'-1} e_y/‖e_y‖ / ‖e‖_{u'}^{u'-1}`).

## Deviations from the draft `80-V17-Interp`

* the scalar in `YVec.toPiLp` is the real number `(P : ℝ)^{-1/s}` cast to `ℂ` (the draft had a complex power);
* `Fact (1 ≤ ENNReal.ofReal 2)` is a global instance (`YVec.fact_two`); `YVec.fact_of_le` supplies the others;
* `YVec.norm_eq` keeps the draft's hypothesis `1 ≤ s` (it is also derivable from the `Fact`, `YVec.one_le_of_fact`);
* `YVec.val`/`YVec.mk` are reducible identities used to move between `YVec P s` and `ZMod P → ℂ`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- `ℂ^P` with the norm `yNorm s` (a type synonym; `s ≥ 1`). -/
def YVec (P : ℕ) (_s : ℝ) : Type := ZMod P → ℂ

instance (P : ℕ) (s : ℝ) : AddCommGroup (YVec P s) := inferInstanceAs (AddCommGroup (ZMod P → ℂ))
instance (P : ℕ) (s : ℝ) : Module ℂ (YVec P s) := inferInstanceAs (Module ℂ (ZMod P → ℂ))
instance (P : ℕ) (s : ℝ) : MeasurableSpace (YVec P s) :=
  inferInstanceAs (MeasurableSpace (ZMod P → ℂ))

/-- The underlying function of an element of `YVec P s` (the identity; reducible, so that it elaborates to
the carrier `ZMod P → ℂ`). -/
@[reducible] def YVec.val {P : ℕ} {s : ℝ} (x : YVec P s) : ZMod P → ℂ := x

/-- The element of `YVec P s` with the underlying function `x` (the identity). -/
@[reducible] def YVec.mk {P : ℕ} (s : ℝ) (x : ZMod P → ℂ) : YVec P s := x

theorem YVec.fact_of_le {s : ℝ} (hs : 1 ≤ s) : Fact (1 ≤ ENNReal.ofReal s) :=
  ⟨ENNReal.one_le_ofReal.2 hs⟩

instance YVec.fact_two : Fact (1 ≤ ENNReal.ofReal 2) := YVec.fact_of_le (by norm_num)

/-- The scaled embedding into `PiLp s`: `x ↦ P^{-1/s} • x`; its norm is `yNorm s x`. -/
def YVec.toPiLp (P : ℕ) (s : ℝ) :
    YVec P s →ₗ[ℂ] PiLp (ENNReal.ofReal s) (fun _ : ZMod P => ℂ) :=
  (((P : ℝ) ^ (-s⁻¹) : ℝ) : ℂ) •
    (WithLp.linearEquiv (ENNReal.ofReal s) ℂ (ZMod P → ℂ)).symm.toLinearMap

theorem YVec.toPiLp_apply {P : ℕ} (s : ℝ) (x : YVec P s) :
    YVec.toPiLp P s x =
      (((P : ℝ) ^ (-s⁻¹) : ℝ) : ℂ) • WithLp.toLp (ENNReal.ofReal s) x.val := rfl

theorem YVec.toPiLp_injective (P : ℕ) [NeZero P] (s : ℝ) : Function.Injective (YVec.toPiLp P s) := by
  intro x y h
  have hP : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
  have hc : (((P : ℝ) ^ (-s⁻¹) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hP _).ne'
  rw [YVec.toPiLp_apply, YVec.toPiLp_apply] at h
  have h2 := smul_right_injective _ hc h
  exact (WithLp.toLp_injective _) h2

instance (P : ℕ) [NeZero P] (s : ℝ) [Fact (1 ≤ ENNReal.ofReal s)] : NormedAddCommGroup (YVec P s) :=
  NormedAddCommGroup.induced (YVec P s) (PiLp (ENNReal.ofReal s) (fun _ : ZMod P => ℂ))
    (YVec.toPiLp P s).toAddMonoidHom (YVec.toPiLp_injective P s)

instance (P : ℕ) [NeZero P] (s : ℝ) [Fact (1 ≤ ENNReal.ofReal s)] : NormedSpace ℂ (YVec P s) :=
  NormedSpace.induced ℂ (YVec P s) (PiLp (ENNReal.ofReal s) (fun _ : ZMod P => ℂ)) (YVec.toPiLp P s)

/-- **The norm of `YVec P s` is `yNorm s`** (`s ≥ 1`). -/
theorem YVec.norm_eq {P : ℕ} [NeZero P] {s : ℝ} [Fact (1 ≤ ENNReal.ofReal s)] (hs : 1 ≤ s)
    (x : YVec P s) : ‖x‖ = yNorm s x.val := by
  have hP : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
  change ‖YVec.toPiLp P s x‖ = _
  rw [YVec.toPiLp_apply, norm_smul, yNorm_eq_norm_toLp hs, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg hP.le _)]

/-! ### Topology and measurable structure: the same as those of `ZMod P → ℂ` -/

section Topology

variable {P : ℕ} [NeZero P] {s : ℝ} [Fact (1 ≤ ENNReal.ofReal s)]

theorem YVec.one_le_of_fact {s : ℝ} [h : Fact (1 ≤ ENNReal.ofReal s)] : 1 ≤ s :=
  ENNReal.one_le_ofReal.1 h.out

/-- The coordinate functional of `YVec P s` is bounded by the norm: `|x y| ≤ P^{1/s} ‖x‖`. -/
theorem YVec.norm_apply_le (x : YVec P s) (y : ZMod P) :
    ‖x.val y‖ ≤ (P : ℝ) ^ s⁻¹ * ‖x‖ := by
  rw [YVec.norm_eq YVec.one_le_of_fact]
  exact norm_apply_le_rpow_mul_yNorm (by linarith [YVec.one_le_of_fact (s := s)]) x.val y

/-- The identity `YVec P s → (ZMod P → ℂ)` is continuous. -/
theorem YVec.continuous_val : Continuous (fun x : YVec P s => x.val) := by
  refine continuous_pi fun y => ?_
  let f : YVec P s →ₗ[ℂ] ℂ :=
    { toFun := fun x => x.val y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact AddMonoidHomClass.continuous_of_bound f ((P : ℝ) ^ s⁻¹) (fun x => YVec.norm_apply_le x y)

/-- The identity `(ZMod P → ℂ) → YVec P s` is continuous (finite dimension). -/
theorem YVec.continuous_mk : Continuous (fun x : ZMod P → ℂ => YVec.mk s x) := by
  let f : (ZMod P → ℂ) →ₗ[ℂ] YVec P s :=
    { toFun := fun x => YVec.mk s x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact f.continuous_of_finiteDimensional

theorem YVec.topology_eq :
    (inferInstance : TopologicalSpace (YVec P s)) =
      (inferInstance : TopologicalSpace (ZMod P → ℂ)) := by
  refine le_antisymm ?_ ?_
  · exact continuous_id_iff_le.1 YVec.continuous_val
  · exact continuous_id_iff_le.1 YVec.continuous_mk

instance YVec.borelSpace : BorelSpace (YVec P s) :=
  ⟨by
    have h : (borel (YVec P s)) = borel (ZMod P → ℂ) := by
      change @borel (ZMod P → ℂ) (inferInstance : TopologicalSpace (YVec P s)) = _
      rw [YVec.topology_eq]
    rw [h]
    exact @BorelSpace.measurable_eq (ZMod P → ℂ) _ _ _⟩

/-- The homeomorphism `YVec P s ≃ₜ (ZMod P → ℂ)` (the identity). -/
def YVec.homeo : YVec P s ≃ₜ (ZMod P → ℂ) where
  toFun := YVec.val
  invFun := YVec.mk s
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := YVec.continuous_val
  continuous_invFun := YVec.continuous_mk

instance YVec.secondCountableTopology : SecondCountableTopology (YVec P s) :=
  YVec.homeo.isEmbedding.secondCountableTopology

end Topology

/-! ### `yNorm` is a slot norm -/

section SlotNorm

variable {P : ℕ} [NeZero P]

theorem yNorm_rpow_eq {s : ℝ} (hs : 0 < s) (w : ZMod P → ℂ) :
    yNorm s w ^ s = (P : ℝ)⁻¹ * ∑ y, ‖w y‖ ^ s := by
  unfold yNorm
  exact Real.rpow_inv_rpow (by positivity) hs.ne'

theorem yNorm_zero_of_pos {s : ℝ} (hs : 0 < s) : yNorm s (0 : ZMod P → ℂ) = 0 := by
  unfold yNorm
  simp [Real.zero_rpow hs.ne', Real.zero_rpow (inv_ne_zero hs.ne')]

theorem yNorm_eq_zero_iff_of_pos {s : ℝ} (hs : 0 < s) (w : ZMod P → ℂ) : yNorm s w = 0 ↔ w = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ yNorm_zero_of_pos hs⟩
  have hP : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
  have h1 : (P : ℝ)⁻¹ * ∑ y, ‖w y‖ ^ s = 0 := by
    have := yNorm_rpow_eq hs w
    rw [h, Real.zero_rpow hs.ne'] at this
    exact this.symm
  have h2 : ∑ y, ‖w y‖ ^ s = 0 := by
    rcases mul_eq_zero.1 h1 with h3 | h3
    · exact absurd h3 (inv_pos.2 hP).ne'
    · exact h3
  funext y
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => Real.rpow_nonneg (norm_nonneg (w y)) s)).1
    h2 y (Finset.mem_univ y)
  have h4 : ‖w y‖ = 0 := by
    rcases (Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg (w y))).1 h3 with ⟨h5, -⟩
    exact h5
  simpa using h4

/-- `yNorm s` (`s > 0`) is a slot norm in the sense of the V17 chain: `yNorm s w ≤ 0 ↔ w = 0`. -/
theorem isSlotNorm_yNorm {s : ℝ} (hs : 0 < s) :
    Interp.IsSlotNorm (yNorm s : (ZMod P → ℂ) → ℝ) := fun w =>
  ⟨fun h => (yNorm_eq_zero_iff_of_pos hs w).1 (le_antisymm h (yNorm_nonneg' s w)),
    fun h => by rw [h]; exact (yNorm_zero_of_pos hs).le⟩

end SlotNorm

/-! ### The pairing `yPair`: Hölder, Lipschitz field, exact norming -/

section Pairing

variable {P : ℕ} [NeZero P]

theorem yPair_zero_left (v : ZMod P → ℂ) : yPair (0 : ZMod P → ℂ) v = 0 := by
  simp [yPair]

theorem yPair_zero_right (e : ZMod P → ℂ) : yPair e (0 : ZMod P → ℂ) = 0 := by
  simp [yPair]

theorem yPair_sub_left (e d v : ZMod P → ℂ) : yPair (e - d) v = yPair e v - yPair d v := by
  simp only [yPair, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]

/-- **Hölder's inequality for the normalized pairing**: `‖⟨a, b⟩‖ ≤ yNorm u' a * yNorm u b`. -/
theorem norm_yPair_le {u u' : ℝ} (h : u.HolderConjugate u') (a b : ZMod P → ℂ) :
    ‖yPair a b‖ ≤ yNorm u' a * yNorm u b := by
  have hP : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
  have hu : 0 < u := h.pos
  have hu' : 0 < u' := h.symm.pos
  have h1 : ‖yPair a b‖ ≤ (P : ℝ)⁻¹ * ∑ y, ‖a y‖ * ‖b y‖ := by
    unfold yPair
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hP.le)
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [norm_mul, Complex.norm_conj]
  have h2 : ∑ y, ‖a y‖ * ‖b y‖ ≤
      (∑ y, ‖a y‖ ^ u') ^ (1 / u') * (∑ y, ‖b y‖ ^ u) ^ (1 / u) := by
    have := Real.inner_le_Lp_mul_Lq (Finset.univ : Finset (ZMod P)) (fun y => ‖a y‖)
      (fun y => ‖b y‖) h.symm
    simpa only [abs_norm] using this
  have h3 : yNorm u' a * yNorm u b =
      (P : ℝ)⁻¹ * ((∑ y, ‖a y‖ ^ u') ^ (1 / u') * (∑ y, ‖b y‖ ^ u) ^ (1 / u)) := by
    unfold yNorm
    rw [Real.mul_rpow (by positivity) (Finset.sum_nonneg fun y _ => Real.rpow_nonneg (norm_nonneg _) _),
      Real.mul_rpow (by positivity) (Finset.sum_nonneg fun y _ => Real.rpow_nonneg (norm_nonneg _) _)]
    have h4 : ((P : ℝ)⁻¹) ^ u'⁻¹ * ((P : ℝ)⁻¹) ^ u⁻¹ = (P : ℝ)⁻¹ := by
      rw [← Real.rpow_add (inv_pos.2 hP), add_comm, h.inv_add_inv_eq_one, Real.rpow_one]
    simp only [one_div]
    calc _ = (((P : ℝ)⁻¹) ^ u'⁻¹ * ((P : ℝ)⁻¹) ^ u⁻¹) *
          ((∑ y, ‖a y‖ ^ u') ^ u'⁻¹ * (∑ y, ‖b y‖ ^ u) ^ u⁻¹) := by ring
      _ = _ := by rw [h4]
  rw [h3]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hP.le))

/-- The explicit norming vector of `e` (in the dual exponent `u'`, `N = yNorm u' e > 0`):
`v_y = (‖e_y‖^{u'-1} / N^{u'-1}) · e_y / ‖e_y‖` (and `v_y = 0` where `e_y = 0`). -/
def normingVec (u' : ℝ) (e : ZMod P → ℂ) : ZMod P → ℂ := fun y =>
  (((‖e y‖ ^ (u' - 1) / yNorm u' e ^ (u' - 1) : ℝ) : ℂ)) * (e y / (‖e y‖ : ℂ))

theorem pair_term_aux (z : ℂ) (r : ℝ) (hz : z ≠ 0) :
    z * conj (((r : ℝ) : ℂ) * (z / ((‖z‖ : ℝ) : ℂ))) = (((r * ‖z‖ : ℝ)) : ℂ) := by
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
  have h2 : z * conj z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [map_mul, Complex.conj_ofReal, map_div₀, Complex.conj_ofReal, Complex.ofReal_mul]
  calc z * (((r : ℝ) : ℂ) * (conj z / ((‖z‖ : ℝ) : ℂ)))
      = ((r : ℝ) : ℂ) * (z * conj z) / ((‖z‖ : ℝ) : ℂ) := by ring
    _ = _ := by rw [h2]; field_simp

theorem normingVec_pair_term {u' : ℝ} (hu' : 1 < u') (e : ZMod P → ℂ) (y : ZMod P) :
    e y * conj (normingVec u' e y) = ((‖e y‖ ^ u' / yNorm u' e ^ (u' - 1) : ℝ) : ℂ) := by
  by_cases hy : e y = 0
  · simp [normingVec, hy, Real.zero_rpow (by linarith : u' ≠ 0)]
  · have hn : (0 : ℝ) < ‖e y‖ := norm_pos_iff.2 hy
    have h1 : ‖e y‖ ^ u' = ‖e y‖ ^ (u' - 1) * ‖e y‖ := by
      rw [← Real.rpow_add_one hn.ne']; ring_nf
    unfold normingVec
    rw [pair_term_aux _ _ hy]
    congr 1
    rw [h1]; ring

theorem norm_normingVec {u' : ℝ} (hu' : 1 < u') (e : ZMod P → ℂ) (y : ZMod P) :
    ‖normingVec u' e y‖ = ‖e y‖ ^ (u' - 1) / yNorm u' e ^ (u' - 1) := by
  by_cases hy : e y = 0
  · simp [normingVec, hy, Real.zero_rpow (by linarith : u' - 1 ≠ 0)]
  · have hn : ‖e y‖ ≠ 0 := norm_ne_zero_iff.2 hy
    have hnn : (0 : ℝ) ≤ ‖e y‖ ^ (u' - 1) / yNorm u' e ^ (u' - 1) :=
      div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (yNorm_nonneg' _ _) _)
    unfold normingVec
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hnn, norm_div, Complex.norm_real,
      norm_norm, div_self hn, mul_one]

theorem holder_conj_sub_one_mul {u u' : ℝ} (h : u.HolderConjugate u') : (u' - 1) * u = u' := by
  have hu : 0 < u := h.pos
  have hu' : 0 < u' := h.symm.pos
  have h1 := h.inv_add_inv_eq_one
  field_simp at h1
  nlinarith

/-- **Exact norming** (Hölder's equality case): every `e` has `v` with `yNorm u v ≤ 1` and
`yNorm u' e ≤ Re ⟨e, v⟩` (in fact `= ` and `yNorm u v = 1` for `e ≠ 0`). -/
theorem exists_norming {u u' : ℝ} (h : u.HolderConjugate u') (e : ZMod P → ℂ) :
    ∃ v : ZMod P → ℂ, yNorm u v ≤ 1 ∧ yNorm u' e ≤ (yPair e v).re := by
  have hP : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
  have hu : 0 < u := h.pos
  have hu' : 1 < u' := h.symm.lt
  have hu'0 : 0 < u' := by linarith
  by_cases hN : yNorm u' e = 0
  · refine ⟨0, by rw [yNorm_zero_of_pos hu]; norm_num, ?_⟩
    rw [hN, yPair_zero_right]; simp
  have hNpos : 0 < yNorm u' e := lt_of_le_of_ne (yNorm_nonneg' _ _) (Ne.symm hN)
  refine ⟨normingVec u' e, ?_, ?_⟩
  · -- the norm of the norming vector is `1`
    have h1 : yNorm u (normingVec u' e) ^ u = 1 := by
      rw [yNorm_rpow_eq hu]
      have h2 : ∀ y, ‖normingVec u' e y‖ ^ u = ‖e y‖ ^ u' / yNorm u' e ^ u' := by
        intro y
        rw [norm_normingVec hu', Real.div_rpow (Real.rpow_nonneg (norm_nonneg _) _)
          (Real.rpow_nonneg hNpos.le _), ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_mul hNpos.le,
          holder_conj_sub_one_mul h]
      simp_rw [h2]
      rw [← Finset.sum_div, ← mul_div_assoc, ← yNorm_rpow_eq hu'0, div_self (Real.rpow_pos_of_pos hNpos _).ne']
    by_contra hgt
    push Not at hgt
    have := Real.one_lt_rpow hgt hu
    rw [h1] at this
    exact lt_irrefl _ this
  · have h3 : yPair e (normingVec u' e) = (((P : ℝ)⁻¹ * ∑ y, ‖e y‖ ^ u' / yNorm u' e ^ (u' - 1) : ℝ) : ℂ) := by
      unfold yPair
      simp_rw [normingVec_pair_term hu' e]
      push_cast
      rfl
    rw [h3, Complex.ofReal_re, ← Finset.sum_div, ← mul_div_assoc, ← yNorm_rpow_eq hu'0,
      ← Real.rpow_sub hNpos]
    simp

end Pairing

/-- **`IsDualPairing (yNorm u) yPair`** for `E = YVec P u'` (`u, u'` Hölder conjugate): `pr e v = yPair e v`.
Zero, the Lipschitz field (= Hölder, with `‖e - d‖ = yNorm u' (e - d)`) and exact norming. -/
theorem isDualPairing_yPair {P : ℕ} [NeZero P] {u u' : ℝ} (h : u.HolderConjugate u')
    [Fact (1 ≤ ENNReal.ofReal u')] :
    Interp.IsDualPairing (E := YVec P u') (W := ZMod P → ℂ) (yNorm u)
      (fun e v => yPair e.val v) where
  zero_left v := yPair_zero_left v
  lipschitz e d v := by
    have h1 : yPair e.val v - yPair d.val v = yPair (e - d).val v := (yPair_sub_left e.val d.val v).symm
    rw [h1, YVec.norm_eq (le_of_lt h.symm.lt)]
    exact norm_yPair_le h _ _
  norming e θ hθ := by
    obtain ⟨v, hv1, hv2⟩ := exists_norming h e.val
    refine ⟨v, hv1, ?_⟩
    rw [YVec.norm_eq (le_of_lt h.symm.lt)]
    have hN := yNorm_nonneg' u' e.val
    nlinarith


end PrimeBHT.TimeFrequency.X2
