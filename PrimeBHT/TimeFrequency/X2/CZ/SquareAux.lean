module

public import PrimeBHT.TimeFrequency.X2.CZ.Minkowski
public import PrimeBHT.TimeFrequency.X2.CZ.WeakAtoms
public import PrimeBHT.TimeFrequency.X2.CZ.WeakType

/-!
# V08(d): norm bookkeeping for the square-function bound

* `yNorm_avg_le` (Minkowski in `y`): if `Q(y) ≤ c (Σ_i w_i |V_i(y)|^p)^{1/p}` pointwise and `p ≤ s`, then
  `‖Q‖_{L^s(Y)} ≤ c (Σ_i w_i ‖V_i‖_{L^s(Y)}^p)^{1/p}`;
* `eLpNorm_avg_le` (Minkowski in `x`): if `D(x) ≤ c (Σ_i w_i a_i(x)^p)^{1/p}` and `p ≤ q`, then
  `‖D‖_{L^q} ≤ c (Σ_i w_i ‖a_i‖_{L^q}^p)^{1/p}` (Minkowski in `L^{q/p}`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology Real ComplexConjugate

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

open PrimeBHT.Statements

section YNorm

variable {P : ℕ} [NeZero P]

theorem yNorm_mono {s : ℝ} (hs : 0 < s) {u v : ZMod P → ℂ} (h : ∀ y, ‖u y‖ ≤ ‖v y‖) :
    yNorm s u ≤ yNorm s v := by
  have hP : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
  unfold yNorm
  refine Real.rpow_le_rpow (by positivity) ?_ (inv_nonneg.2 hs.le)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) (inv_nonneg.2 hP.le)
  exact Real.rpow_le_rpow (norm_nonneg _) (h y) hs.le

theorem yNorm_ratio {s q : ℝ} (hs : 0 < s) (hq : 0 < q) (u : ZMod P → ℂ) :
    yNorm (s / q) (fun y => ((‖u y‖ ^ q : ℝ) : ℂ)) = yNorm s u ^ q := by
  have hP : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
  unfold yNorm
  have e1 : ∀ y, ‖((‖u y‖ ^ q : ℝ) : ℂ)‖ ^ (s / q) = ‖u y‖ ^ s := by
    intro y
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      ← Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ _ hq.ne']
  simp_rw [e1]
  have hA : 0 ≤ (P : ℝ)⁻¹ * ∑ y, ‖u y‖ ^ s :=
    mul_nonneg (inv_nonneg.2 hP.le) (Finset.sum_nonneg fun y _ => Real.rpow_nonneg (norm_nonneg _) _)
  rw [← Real.rpow_mul hA]
  congr 1
  field_simp

/-- **Minkowski in `y` for a pointwise `p`-mean bound** (`0 < p ≤ s`, `s ≥ 1`). -/
theorem yNorm_avg_le {s p c : ℝ} (hs : 1 ≤ s) (hp : 0 < p) (hps : p ≤ s) (hc : 0 ≤ c)
    {ι : Type*} (S : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) (V : ι → ZMod P → ℂ)
    (Qx : ZMod P → ℝ) (hQ0 : ∀ y, 0 ≤ Qx y)
    (hQ : ∀ y, Qx y ≤ c * (∑ i ∈ S, w i * ‖V i y‖ ^ p) ^ p⁻¹) :
    yNorm s (fun y => (Qx y : ℂ)) ≤ c * (∑ i ∈ S, w i * yNorm s (V i) ^ p) ^ p⁻¹ := by
  have hs0 : 0 < s := by linarith
  have hr : 1 ≤ s / p := by rw [le_div_iff₀ hp]; linarith
  have hsum0 : ∀ y, 0 ≤ ∑ i ∈ S, w i * ‖V i y‖ ^ p := fun y =>
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (Real.rpow_nonneg (norm_nonneg _) _)
  -- pointwise `Q^p ≤ c^p Σ w |V|^p`
  have h1 : ∀ y, ‖((Qx y : ℝ) : ℂ)‖ ^ p ≤ ‖(((c ^ p * ∑ i ∈ S, w i * ‖V i y‖ ^ p : ℝ)) : ℂ)‖ := by
    intro y
    rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hQ0 y),
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hc _) (hsum0 y))]
    calc Qx y ^ p ≤ (c * (∑ i ∈ S, w i * ‖V i y‖ ^ p) ^ p⁻¹) ^ p :=
          Real.rpow_le_rpow (hQ0 y) (hQ y) hp.le
      _ = c ^ p * ∑ i ∈ S, w i * ‖V i y‖ ^ p := by
          rw [Real.mul_rpow hc (Real.rpow_nonneg (hsum0 y) _), ← Real.rpow_mul (hsum0 y),
            inv_mul_cancel₀ hp.ne', Real.rpow_one]
  have h2 : yNorm s (fun y => (Qx y : ℂ)) ^ p ≤ ∑ i ∈ S, (c ^ p * w i) * yNorm s (V i) ^ p := by
    rw [← yNorm_ratio hs0 hp]
    refine (yNorm_mono (by positivity) (u := fun y => ((‖((Qx y : ℝ) : ℂ)‖ ^ p : ℝ) : ℂ))
      (v := fun y => (((c ^ p * ∑ i ∈ S, w i * ‖V i y‖ ^ p : ℝ)) : ℂ)) ?_).trans ?_
    · intro y
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact h1 y
    · have e : (fun y => (((c ^ p * ∑ i ∈ S, w i * ‖V i y‖ ^ p : ℝ)) : ℂ)) =
          ∑ i ∈ S, (fun y => (((c ^ p * w i : ℝ)) : ℂ) * ((‖V i y‖ ^ p : ℝ) : ℂ)) := by
        ext y
        simp only [Finset.sum_apply]
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [e]
      refine (yNorm_sum_le hr S _).trans (Finset.sum_le_sum fun i hi => ?_)
      rw [yNorm_const_mul (by positivity), Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hc _) (hw i hi)), yNorm_ratio hs0 hp]
  have h3 : yNorm s (fun y => (Qx y : ℂ)) ^ p ≤ c ^ p * ∑ i ∈ S, w i * yNorm s (V i) ^ p := by
    refine h2.trans (le_of_eq ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hN0 : 0 ≤ yNorm s (fun y => (Qx y : ℂ)) := yNorm_nonneg s _
  have hsum1 : 0 ≤ ∑ i ∈ S, w i * yNorm s (V i) ^ p :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (Real.rpow_nonneg (yNorm_nonneg s _) _)
  calc yNorm s (fun y => (Qx y : ℂ)) = (yNorm s (fun y => (Qx y : ℂ)) ^ p) ^ p⁻¹ := by
        rw [← Real.rpow_mul hN0, mul_inv_cancel₀ hp.ne', Real.rpow_one]
    _ ≤ (c ^ p * ∑ i ∈ S, w i * yNorm s (V i) ^ p) ^ p⁻¹ :=
        Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) h3 (inv_nonneg.2 hp.le)
    _ = c * (∑ i ∈ S, w i * yNorm s (V i) ^ p) ^ p⁻¹ := by
        rw [Real.mul_rpow (Real.rpow_nonneg hc _) hsum1, ← Real.rpow_mul hc, mul_inv_cancel₀ hp.ne',
          Real.rpow_one]

end YNorm

section XNorm

/-- `‖D^p‖_{L^{q/p}} = ‖D‖_{L^q}^p` for `D ≥ 0` measurable. -/
theorem eLpNorm_rpow_eq {D : ℝ → ℝ} (hD0 : ∀ x, 0 ≤ D x) (hDm : Measurable D) {p q : ℝ} (hp : 0 < p)
    (hq : 0 < q) :
    eLpNorm (fun x => D x ^ p) (ENNReal.ofReal (q / p)) volume =
      eLpNorm D (ENNReal.ofReal q) volume ^ p := by
  have hr : 0 < q / p := div_pos hq hp
  have hm1 : AEStronglyMeasurable (fun x => D x ^ p) volume := (hDm.pow_const p).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hr).ne' ENNReal.ofReal_ne_top hm1,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq).ne' ENNReal.ofReal_ne_top
      hDm.aestronglyMeasurable, ENNReal.toReal_ofReal hr.le, ENNReal.toReal_ofReal hq.le,
    ← ENNReal.rpow_mul]
  have e : ∀ x, ‖D x ^ p‖ₑ ^ (q / p) = ‖D x‖ₑ ^ q := by
    intro x
    rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (hD0 x) _), Real.enorm_eq_ofReal (hD0 x),
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hD0 x) _) hr.le,
      ENNReal.ofReal_rpow_of_nonneg (hD0 x) hq.le, ← Real.rpow_mul (hD0 x), mul_div_cancel₀ _ hp.ne']
  simp_rw [e]
  congr 1
  field_simp

/-- **Minkowski in `x` for a pointwise `p`-mean bound** (`0 < p ≤ q`). -/
theorem eLpNorm_avg_le {ι : Type*} (S : Finset ι) {p q c : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hc : 0 ≤ c)
    (w : ι → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) (a : ι → ℝ → ℝ) (ha0 : ∀ i x, 0 ≤ a i x)
    (ham : ∀ i, Measurable (a i)) (D : ℝ → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hDm : Measurable D)
    (hD : ∀ x, D x ≤ c * (∑ i ∈ S, w i * a i x ^ p) ^ p⁻¹) :
    eLpNorm D (ENNReal.ofReal q) volume ≤ ENNReal.ofReal c *
      (∑ i ∈ S, ENNReal.ofReal (w i) * eLpNorm (a i) (ENNReal.ofReal q) volume ^ p) ^ p⁻¹ := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hr : 1 ≤ q / p := by rw [le_div_iff₀ hp]; linarith
  have hsum0 : ∀ x, 0 ≤ ∑ i ∈ S, w i * a i x ^ p := fun x =>
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (Real.rpow_nonneg (ha0 i x) _)
  have h1 : ∀ x, D x ^ p ≤ c ^ p * ∑ i ∈ S, w i * a i x ^ p := by
    intro x
    calc D x ^ p ≤ (c * (∑ i ∈ S, w i * a i x ^ p) ^ p⁻¹) ^ p :=
          Real.rpow_le_rpow (hD0 x) (hD x) hp.le
      _ = c ^ p * ∑ i ∈ S, w i * a i x ^ p := by
          rw [Real.mul_rpow hc (Real.rpow_nonneg (hsum0 x) _), ← Real.rpow_mul (hsum0 x),
            inv_mul_cancel₀ hp.ne', Real.rpow_one]
  have hor : 1 ≤ ENNReal.ofReal (q / p) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr
  have e1 : (fun x => c ^ p * ∑ i ∈ S, w i * a i x ^ p) =
      (c ^ p) • ∑ i ∈ S, (w i) • (fun x => a i x ^ p) := by
    ext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have h2 : eLpNorm (fun x => D x ^ p) (ENNReal.ofReal (q / p)) volume ≤
      ENNReal.ofReal (c ^ p) * ∑ i ∈ S, ENNReal.ofReal (w i) *
        eLpNorm (fun x => a i x ^ p) (ENNReal.ofReal (q / p)) volume := by
    calc eLpNorm (fun x => D x ^ p) (ENNReal.ofReal (q / p)) volume
        ≤ eLpNorm (fun x => c ^ p * ∑ i ∈ S, w i * a i x ^ p) (ENNReal.ofReal (q / p)) volume := by
          refine eLpNorm_mono (hDm.pow_const p).aestronglyMeasurable fun x => ?_
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hD0 x) _),
            abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hc _) (hsum0 x))]
          exact h1 x
      _ = ENNReal.ofReal (c ^ p) * eLpNorm (∑ i ∈ S, (w i) • (fun x => a i x ^ p))
            (ENNReal.ofReal (q / p)) volume := by
          rw [e1, eLpNorm_const_smul, Real.enorm_eq_ofReal (Real.rpow_nonneg hc _)]
      _ ≤ ENNReal.ofReal (c ^ p) * ∑ i ∈ S, eLpNorm ((w i) • (fun x => a i x ^ p))
            (ENNReal.ofReal (q / p)) volume := by
          exact mul_le_mul' le_rfl (eLpNorm_sum_le hor)
      _ = _ := by
          congr 1
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (hw i hi)]
  have h3 : ∀ i, eLpNorm (fun x => a i x ^ p) (ENNReal.ofReal (q / p)) volume =
      eLpNorm (a i) (ENNReal.ofReal q) volume ^ p := fun i =>
    eLpNorm_rpow_eq (ha0 i) (ham i) hp hq
  rw [eLpNorm_rpow_eq hD0 hDm hp hq] at h2
  simp_rw [h3] at h2
  calc eLpNorm D (ENNReal.ofReal q) volume
      = (eLpNorm D (ENNReal.ofReal q) volume ^ p) ^ p⁻¹ := by
        rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hp.ne', ENNReal.rpow_one]
    _ ≤ (ENNReal.ofReal (c ^ p) * ∑ i ∈ S, ENNReal.ofReal (w i) *
          eLpNorm (a i) (ENNReal.ofReal q) volume ^ p) ^ p⁻¹ :=
        ENNReal.rpow_le_rpow h2 (inv_nonneg.2 hp.le)
    _ = ENNReal.ofReal c * (∑ i ∈ S, ENNReal.ofReal (w i) *
          eLpNorm (a i) (ENNReal.ofReal q) volume ^ p) ^ p⁻¹ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hp.le),
          ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hc _) (inv_nonneg.2 hp.le),
          ← Real.rpow_mul hc, mul_inv_cancel₀ hp.ne', Real.rpow_one]

end XNorm

end PrimeBHT.TimeFrequency.X2.CZ
