module

public import PrimeBHT.TimeFrequency.X2.CZ.MixedNorm

/-!
# V08 phase 2: the norm `yNorm s` on `ℤ/P` is a norm (Minkowski), uniformly in `P`

`yNorm s` is a *function* `ZMod P → ℂ → ℝ`, not a `Norm` instance, so Mathlib's `norm_integral_le_integral_norm`
and `norm_tsum_le_tsum_norm` do not apply to `ℝ → ZMod P → ℂ`.  The facts the vector-valued
Calderón-Zygmund argument needs are therefore proved here, by hand, for every `s > 1` and every `P`:

* `yNorm_add_le`, `yNorm_sum_le`: the triangle inequality (`Real.Lp_add_le`);
* `yNorm_integral_le`: **Minkowski's integral inequality**
  `‖∫ V(a, ·) dμ‖_{L^s(Y)} ≤ ∫ ‖V(a, ·)‖_{L^s(Y)} dμ` (proved by testing against the Hölder extremiser
  `‖Z‖^{s-2} Z`, no Banach-space structure needed);
* `yNorm_tsum_le`: the triangle inequality for coordinatewise summable families.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology Real ComplexConjugate

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

open PrimeBHT.Statements

section Mink
variable {P : ℕ} [NeZero P]

/-- `w y = ‖Z y‖^{s-2} Z y`, the extremiser of the Hölder inequality for `Z`. -/
noncomputable def extremiser (s : ℝ) (Z : ZMod P → ℂ) (y : ZMod P) : ℂ :=
  ((‖Z y‖ ^ (s - 2) : ℝ) : ℂ) * Z y

omit [NeZero P] in
theorem norm_extremiser {s : ℝ} (hs : 1 < s) (Z : ZMod P → ℂ) (y : ZMod P) :
    ‖extremiser s Z y‖ = ‖Z y‖ ^ (s - 1) := by
  unfold extremiser
  by_cases h : Z y = 0
  · simp [h, Real.zero_rpow (by linarith : s - 1 ≠ 0)]
  · have hp : 0 < ‖Z y‖ := norm_pos_iff.2 h
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hp.le _)]
    rw [← Real.rpow_add_one hp.ne']
    congr 1; ring

omit [NeZero P] in
theorem mul_conj_extremiser {s : ℝ} (hs : 1 < s) (Z : ZMod P → ℂ) (y : ZMod P) :
    Z y * conj (extremiser s Z y) = ((‖Z y‖ ^ s : ℝ) : ℂ) := by
  unfold extremiser
  by_cases h : Z y = 0
  · simp [h, Real.zero_rpow (by linarith : s ≠ 0)]
  · have hp : 0 < ‖Z y‖ := norm_pos_iff.2 h
    rw [map_mul, Complex.conj_ofReal]
    have : Z y * conj (Z y) = ((‖Z y‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    calc Z y * (((‖Z y‖ ^ (s - 2) : ℝ) : ℂ) * conj (Z y))
        = ((‖Z y‖ ^ (s - 2) : ℝ) : ℂ) * (Z y * conj (Z y)) := by ring
      _ = ((‖Z y‖ ^ (s - 2) * ‖Z y‖ ^ 2 : ℝ) : ℂ) := by rw [this]; push_cast; ring
      _ = ((‖Z y‖ ^ s : ℝ) : ℂ) := by
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_add hp]
        norm_num


theorem yNorm_conj_exponent_extremiser {s : ℝ} (hs : 1 < s) (Z : ZMod P → ℂ) :
    yNorm (Real.conjExponent s) (extremiser s Z) = yNorm s Z ^ (s - 1) := by
  have hs' : (Real.conjExponent s) = s / (s - 1) := by
    rw [Real.conjExponent]
  have hs0 : (0 : ℝ) < s := by linarith
  have hs1 : (0 : ℝ) < s - 1 := by linarith
  have hnn : 0 ≤ (P : ℝ)⁻¹ * ∑ y, ‖Z y‖ ^ s := by positivity
  unfold yNorm
  have e1 : ∀ y, ‖extremiser s Z y‖ ^ (Real.conjExponent s) = ‖Z y‖ ^ s := by
    intro y
    rw [norm_extremiser hs, ← Real.rpow_mul (norm_nonneg _), hs']
    congr 1
    field_simp
  simp_rw [e1]
  rw [← Real.rpow_mul hnn, hs']
  congr 1
  field_simp


/-- **Minkowski's integral inequality** for the `L^s(Y_P)` norm (`s > 1`), uniform in `P`:
`‖∫ V(a, ·) dμ(a)‖_{L^s(Y)} ≤ ∫ ‖V(a, ·)‖_{L^s(Y)} dμ(a)`.  (The norm `yNorm s` is not a `Norm`
instance, so this is proved by testing against the Hölder extremiser.) -/
theorem yNorm_integral_le {s : ℝ} (hs : 1 < s) {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (V : α → ZMod P → ℂ) (hV : ∀ y, Integrable (fun a => V a y) μ)
    (hn : Integrable (fun a => yNorm s (V a)) μ) :
    yNorm s (fun y => ∫ a, V a y ∂μ) ≤ ∫ a, yNorm s (V a) ∂μ := by
  set Z : ZMod P → ℂ := fun y => ∫ a, V a y ∂μ with hZ
  set N := yNorm s Z with hNdef
  have hN0 : 0 ≤ N := yNorm_nonneg s Z
  by_cases hN : N = 0
  · rw [hN]; exact integral_nonneg fun a => yNorm_nonneg s _
  have hNpos : 0 < N := lt_of_le_of_ne hN0 (Ne.symm hN)
  have hs' := Real.HolderConjugate.conjExponent hs
  have hs1 : s ≠ 0 := by linarith
  have hP : (P : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne P
  -- the pairing of `Z` with its extremiser
  have hpair : pairingY Z (extremiser s Z) = ((N ^ s : ℝ) : ℂ) := by
    unfold pairingY
    simp_rw [mul_conj_extremiser hs]
    have h := yNorm_rpow_self (P := P) hs1 Z
    rw [← hNdef] at h
    rw [h]
    push_cast
    rfl
  -- linearity of the pairing in the first slot
  have hint : pairingY Z (extremiser s Z) = ∫ a, pairingY (V a) (extremiser s Z) ∂μ := by
    unfold pairingY
    have hi : ∀ y ∈ Finset.univ, Integrable (fun a => V a y * conj (extremiser s Z y)) μ :=
      fun y _ => (hV y).mul_const _
    rw [integral_const_mul, integral_finsetSum _ hi]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [integral_mul_const]
  have hbound : ∀ a, ‖pairingY (V a) (extremiser s Z)‖ ≤ yNorm s (V a) * N ^ (s - 1) := by
    intro a
    refine (norm_pairingY_le hs' (V a) (extremiser s Z)).trans ?_
    rw [yNorm_conj_exponent_extremiser hs]
  have hpi : Integrable (fun a => pairingY (V a) (extremiser s Z)) μ := by
    unfold pairingY
    exact (integrable_finsetSum _ fun y _ => (hV y).mul_const _).const_mul _
  have h1 : N ^ s ≤ (∫ a, yNorm s (V a) ∂μ) * N ^ (s - 1) := by
    have : ‖pairingY Z (extremiser s Z)‖ = N ^ s := by
      rw [hpair, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hN0 _)]
    rw [← this, hint]
    calc ‖∫ a, pairingY (V a) (extremiser s Z) ∂μ‖ ≤ ∫ a, ‖pairingY (V a) (extremiser s Z)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ a, yNorm s (V a) * N ^ (s - 1) ∂μ :=
          integral_mono hpi.norm (hn.mul_const _) hbound
      _ = (∫ a, yNorm s (V a) ∂μ) * N ^ (s - 1) := integral_mul_const _ _
  have h2 : N ^ s = N * N ^ (s - 1) := by
    rw [mul_comm, ← Real.rpow_add_one hNpos.ne']; congr 1; ring
  have hpos : 0 < N ^ (s - 1) := Real.rpow_pos_of_pos hNpos _
  rw [h2] at h1
  exact le_of_mul_le_mul_right h1 hpos

end Mink

section Tri
variable {P : ℕ} [NeZero P]

theorem yNorm_eq_mul {s : ℝ} (_hs : 0 < s) (u : ZMod P → ℂ) :
    yNorm s u = ((P : ℝ) ^ (-s⁻¹)) * (∑ y, ‖u y‖ ^ s) ^ s⁻¹ := by
  have hP : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
  unfold yNorm
  rw [Real.mul_rpow (by positivity) (Finset.sum_nonneg fun y _ => Real.rpow_nonneg (norm_nonneg _) _),
    Real.inv_rpow hP.le, Real.rpow_neg hP.le]

theorem yNorm_add_le {s : ℝ} (hs : 1 ≤ s) (u v : ZMod P → ℂ) :
    yNorm s (u + v) ≤ yNorm s u + yNorm s v := by
  have hs0 : 0 < s := by linarith
  have hP : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
  rw [yNorm_eq_mul hs0, yNorm_eq_mul hs0, yNorm_eq_mul hs0, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hP.le _)
  have h := Real.Lp_add_le (Finset.univ : Finset (ZMod P)) (fun y => ‖u y‖) (fun y => ‖v y‖) hs
  simp only [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), abs_norm, one_div] at h
  refine le_trans (Real.rpow_le_rpow (Finset.sum_nonneg fun y _ => Real.rpow_nonneg (norm_nonneg _) _)
    (Finset.sum_le_sum (g := fun y => (‖u y‖ + ‖v y‖) ^ s) fun y _ => ?_) (inv_nonneg.2 hs0.le)) h
  exact Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) hs0.le

/-- The triangle inequality for finite sums. -/
theorem yNorm_sum_le {s : ℝ} (hs : 1 ≤ s) {ι : Type*} (S : Finset ι) (u : ι → ZMod P → ℂ) :
    yNorm s (∑ i ∈ S, u i) ≤ ∑ i ∈ S, yNorm s (u i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have hs0 : 0 < s := by linarith
    simp [yNorm, Real.zero_rpow hs0.ne', Real.zero_rpow (inv_ne_zero hs0.ne')]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (yNorm_add_le hs _ _).trans (by linarith)

theorem continuous_yNorm {s : ℝ} (hs : 0 < s) : Continuous (fun u : ZMod P → ℂ => yNorm s u) := by
  unfold yNorm
  refine Continuous.rpow_const (continuous_const.mul (continuous_finsetSum _ fun y _ => ?_))
    (fun _ => Or.inr (inv_nonneg.2 hs.le))
  exact (Continuous.rpow_const (continuous_norm.comp (continuous_apply y))
    (fun _ => Or.inr hs.le))

/-- **Countable triangle inequality**: coordinatewise-summable families. -/
theorem yNorm_tsum_le {s : ℝ} (hs : 1 ≤ s) {ι : Type*} (u : ι → ZMod P → ℂ) (W : ZMod P → ℂ)
    (hW : ∀ y, HasSum (fun i => u i y) (W y)) (hu : Summable (fun i => yNorm s (u i))) :
    yNorm s W ≤ ∑' i, yNorm s (u i) := by
  have hs0 : 0 < s := by linarith
  have hlim : Tendsto (fun S : Finset ι => ∑ i ∈ S, u i) atTop (nhds W) := by
    rw [tendsto_pi_nhds]
    intro y
    simp only [Finset.sum_apply]
    exact hW y
  have h2 := ((continuous_yNorm (P := P) hs0).tendsto W).comp hlim
  refine le_of_tendsto h2 (Eventually.of_forall fun S => ?_)
  exact (yNorm_sum_le hs S u).trans (hu.sum_le_tsum S (fun i _ => yNorm_nonneg s _))

end Tri

end PrimeBHT.TimeFrequency.X2.CZ
