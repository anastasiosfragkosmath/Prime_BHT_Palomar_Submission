module

public import PrimeBHT.TimeFrequency.X2.FourierSupport

/-!
# X2, V13 part 2: the `L^q → L^∞` Bernstein inequality (FS-2, Hölder step)

`bernstein_Lq_Linf`: for a vector function `G` whose coordinates are band-limited with Fourier support in
`[c - 1/(2L), c + 1/(2L)]`, `‖G(x)‖_{L^s(Y)} ≤ C_q L^{-1/q} ‖G‖_{L^q(ℝ; L^s(Y))}` pointwise in `x` (`1 ≤ s`, `1 < q`),
with `C_q` depending only on `q`.  Proof: `yNorm_le_integral_bernstein` (reproducing formula + Minkowski), the kernel decay
`exists_norm_fourierInv_bernN_le` (order 2), and Hölder against `(1 + |x - z|/L)^{-2}`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

theorem exists_bern_decay_two :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c L : ℝ, 0 < L → ∀ w : ℝ,
      ‖𝓕⁻ (bernN c L) w‖ ≤ C * L⁻¹ * (1 + |w| / L) ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC, h⟩ := exists_norm_fourierInv_bernN_le 2
  exact ⟨C, hC, fun c L hL w => by simpa using h c L hL w⟩

/-- The constant of the order-2 kernel decay of the Bernstein multiplier, made positive. -/
def bernC2 : ℝ := Classical.choose exists_bern_decay_two + 1

theorem bernC2_pos : 0 < bernC2 := by
  unfold bernC2
  have := (Classical.choose_spec exists_bern_decay_two).1
  linarith

theorem norm_fourierInv_bernN_le_two (c L : ℝ) (hL : 0 < L) (w : ℝ) :
    ‖𝓕⁻ (bernN c L) w‖ ≤ bernC2 * L⁻¹ * (1 + |w| / L) ^ (-(2 : ℝ)) := by
  have h := (Classical.choose_spec exists_bern_decay_two).2 c L hL w
  have hp : 0 < (1 + |w| / L) ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  refine h.trans ?_
  unfold bernC2
  have hLi : 0 < L⁻¹ := inv_pos.2 hL
  nlinarith [mul_pos hLi hp]

/-- `ofReal ∫ h ≤ ∫⁻ ofReal h` for nonnegative `h` (the Bochner integral of a non-integrable function is `0`). -/
theorem ofReal_integral_le_lintegral {h : ℝ → ℝ} (hnn : ∀ z, 0 ≤ h z) :
    ENNReal.ofReal (∫ z, h z) ≤ ∫⁻ z, ENNReal.ofReal (h z) := by
  by_cases hi : Integrable h
  · exact (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnn)).le
  · rw [integral_undef hi]; simp

/-- **FS-2 (Hölder step)**: `‖G(x)‖_{L^s(Y)} ≤ C_q L^{-1/q} ‖G‖_{L^q(L^s(Y))}` for band-limited `G`
(coordinates with `𝓕 ⊆ [c - 1/(2L), c + 1/(2L)]`), `1 ≤ s`, `1 < q`; `C_q = bernC2 (2/(2q' - 1))^{1/q'}`, `q' = q/(q-1)`. -/
theorem bernstein_Lq_Linf {P : ℕ} [NeZero P] {s q : ℝ} (hs : 1 ≤ s) (hq : 1 < q) {G : ℝ → ZMod P → ℂ} {S : Set ℝ}
    (hG : ∀ y, IsBandLimited (fun x => G x y) S) {c L : ℝ} (hL : 0 < L)
    (hS : S ⊆ Icc (c - 1 / (2 * L)) (c + 1 / (2 * L))) (hmeas : Measurable fun z => yNorm s (G z)) (x : ℝ) :
    ENNReal.ofReal (yNorm s (G x)) ≤
      ENNReal.ofReal (bernC2 * (2 / (2 * Real.conjExponent q - 1)) ^ (1 / Real.conjExponent q) *
        L ^ (-(1 / q))) * eLpNorm (fun z => yNorm s (G z)) (ENNReal.ofReal q) volume := by
  set q' := Real.conjExponent q with hq'
  have hconj : Real.HolderConjugate q' q := (Real.HolderConjugate.conjExponent hq).symm
  have hq'1 : 1 < q' := hconj.lt
  have hq0 : 0 < q := by linarith
  have hq'0 : 0 < q' := by linarith
  set g : ℝ → ℝ := fun z => yNorm s (G z) with hg
  have hg0 : ∀ z, 0 ≤ g z := fun z => yNorm_nonneg' s _
  set A : ℝ := bernC2 * L⁻¹ with hA
  have hA0 : 0 < A := mul_pos bernC2_pos (inv_pos.2 hL)
  set f : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (A * (1 + |x - z| / L) ^ (-(2 : ℝ))) with hf
  have hfc : Continuous fun z : ℝ => A * (1 + |x - z| / L) ^ (-(2 : ℝ)) := by
    refine continuous_const.mul (Continuous.rpow_const (by fun_prop) fun z => Or.inl (by positivity))
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp hfc.measurable
  have hgm : Measurable fun z => ENNReal.ofReal (g z) := ENNReal.measurable_ofReal.comp hmeas
  -- step 1: pointwise kernel bound
  have h1 : ENNReal.ofReal (yNorm s (G x)) ≤ ∫⁻ z, f z * ENNReal.ofReal (g z) := by
    calc ENNReal.ofReal (yNorm s (G x))
        ≤ ENNReal.ofReal (∫ z, ‖𝓕⁻ (bernN c L) (x - z)‖ * yNorm s (G z)) :=
          ENNReal.ofReal_le_ofReal (yNorm_le_integral_bernstein hs hG hL hS x)
      _ ≤ ∫⁻ z, ENNReal.ofReal (‖𝓕⁻ (bernN c L) (x - z)‖ * yNorm s (G z)) :=
          ofReal_integral_le_lintegral (fun z => mul_nonneg (norm_nonneg _) (hg0 z))
      _ ≤ ∫⁻ z, f z * ENNReal.ofReal (g z) := by
          refine lintegral_mono fun z => ?_
          rw [ENNReal.ofReal_mul (norm_nonneg _)]
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal
            (norm_fourierInv_bernN_le_two c L hL (x - z))) le_rfl
  -- step 2: Hölder
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hconj hfm.aemeasurable hgm.aemeasurable
  -- step 3: the kernel norm
  have h3 : ∫⁻ z, f z ^ q' = ENNReal.ofReal (A ^ q' * (2 * L / (2 * q' - 1))) := by
    have hpt : ∀ z, f z ^ q' = ENNReal.ofReal (A ^ q' * (1 + |z - x| / L) ^ (-(2 * q'))) := by
      intro z
      simp only [hf]
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq'0.le, Real.mul_rpow hA0.le (by positivity),
        ← Real.rpow_mul (by positivity), abs_sub_comm x z]
      congr 3; ring
    simp_rw [hpt]
    have hint : Integrable (fun z : ℝ => A ^ q' * (1 + |z - x| / L) ^ (-(2 * q'))) :=
      (integrable_one_add_abs_sub_div_rpow (p := 2 * q') (by linarith) x hL).const_mul _
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun z => by positivity),
      integral_const_mul, integral_one_add_abs_sub_div_rpow (by linarith) x hL]
  -- step 4: the `L^{q'}` norm of the kernel
  have h4 : (∫⁻ z, f z ^ q') ^ (1 / q') =
      ENNReal.ofReal (A * (2 * L / (2 * q' - 1)) ^ (1 / q')) := by
    have hpos : 0 < 2 * q' - 1 := by linarith
    have hB : 0 ≤ 2 * L / (2 * q' - 1) := div_nonneg (by positivity) hpos.le
    have hAq : 0 ≤ A ^ q' := Real.rpow_nonneg hA0.le _
    rw [h3, ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hAq hB) (by positivity), Real.mul_rpow hAq hB,
      one_div, Real.rpow_rpow_inv hA0.le hq'0.ne']
  -- step 5: the `L^q` norm of `g`
  have h5 : (∫⁻ z, ENNReal.ofReal (g z) ^ q) ^ (1 / q) = eLpNorm g (ENNReal.ofReal q) volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq0) ENNReal.ofReal_ne_top hmeas.aestronglyMeasurable, ENNReal.toReal_ofReal hq0.le]
    simp_rw [Real.enorm_eq_ofReal (hg0 _)]
  -- step 6: constants
  have hconst : A * (2 * L / (2 * q' - 1)) ^ (1 / q') =
      bernC2 * (2 / (2 * q' - 1)) ^ (1 / q') * L ^ (-(1 / q)) := by
    have e1 : (2 * L / (2 * q' - 1)) = (2 / (2 * q' - 1)) * L := by ring
    have hpos : 0 < 2 * q' - 1 := by linarith
    rw [e1, Real.mul_rpow (by positivity) hL.le, hA]
    have e2 : L ^ (1 / q') * L⁻¹ = L ^ (-(1 / q)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hL]
      congr 1
      have := hconj.inv_add_inv_eq_one
      rw [one_div, one_div]; linarith
    calc bernC2 * L⁻¹ * ((2 / (2 * q' - 1)) ^ (1 / q') * L ^ (1 / q'))
        = bernC2 * (2 / (2 * q' - 1)) ^ (1 / q') * (L ^ (1 / q') * L⁻¹) := by ring
      _ = _ := by rw [e2]
  calc ENNReal.ofReal (yNorm s (G x)) ≤ ∫⁻ z, f z * ENNReal.ofReal (g z) := h1
    _ ≤ (∫⁻ z, f z ^ q') ^ (1 / q') * (∫⁻ z, ENNReal.ofReal (g z) ^ q) ^ (1 / q) := h2
    _ = _ := by rw [h4, h5, hconst]

end PrimeBHT.TimeFrequency.X2
