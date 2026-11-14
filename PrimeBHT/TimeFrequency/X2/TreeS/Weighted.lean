module

public import PrimeBHT.TimeFrequency.X2.EngTail.Tree
public import PrimeBHT.TimeFrequency.X2.Psp.Domination
public import PrimeBHT.TimeFrequency.X2.TreeS.Exotic

/-!
# X2, node V15s: the weighted `L^R → L^∞` inequality (Hölder against the Bernstein kernel)

`weighted_sup`: if `g ≥ 0` is measurable, `g(x) ≤ ∫ K(x - z) g(z) dz` for all `x` and `K(w) ≤ A (3/ℓ) (1 + |w|/ℓ)^{-(b+2)}` then
`g(x) ≤ C ⟨(x - c₀)/ℓ⟩^b ℓ^{-1/R} ‖⟨(· - c₀)/ℓ⟩^{-b} g‖_{L^R}` with `C = wsupConst A R'`
(an `ℝ≥0∞` inequality, `Lq` of `EngTail/Ops.lean`; `R'` the conjugate exponent of `R`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- The constant `3 A (2/(2R' - 1))^{1/R'}` of the weighted Bernstein inequality. -/
def wsupConst (A R' : ℝ) : ℝ := 3 * A * (2 / (2 * R' - 1)) ^ (1 / R')

theorem wsupConst_nonneg {A R' : ℝ} (hA : 0 ≤ A) (hR' : 1 < R') : 0 ≤ wsupConst A R' := by
  unfold wsupConst
  have : (0 : ℝ) < 2 * R' - 1 := by linarith
  positivity

theorem weighted_sup {R R' : ℝ} (hHC : R.HolderConjugate R') {ℓ c0 b A : ℝ} (hℓ : 0 < ℓ) (hb : 0 ≤ b)
    (hA : 0 ≤ A) {K g : ℝ → ℝ} (hK0 : ∀ w, 0 ≤ K w) (hKm : Measurable K)
    (hKb : ∀ w, K w ≤ A * (3 / ℓ) * (1 + |w| / ℓ) ^ (-(b + 2))) (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (hBern : ∀ x, g x ≤ ∫ z, K (x - z) * g z) (x : ℝ) :
    ENNReal.ofReal (g x) ≤ ENNReal.ofReal (wsupConst A R' * jb ((x - c0) / ℓ) ^ b) *
      (ENNReal.ofReal (ℓ ^ (-1 / R)) * Lq R (fun z => ENNReal.ofReal (jb ((z - c0) / ℓ) ^ (-b) * g z))) := by
  have hR : 1 < R := hHC.lt
  have hR' : 1 < R' := hHC.symm.lt
  have hR0 : 0 < R := hHC.pos
  have hR'0 : 0 < R' := hHC.symm.pos
  have hinv : R⁻¹ + R'⁻¹ = 1 := hHC.inv_add_inv_eq_one
  set W : ℝ → ℝ := fun z => jb ((z - c0) / ℓ) with hW
  have hWpos : ∀ z, 0 < W z := fun z => jb_pos _
  have hWm : Measurable W := (continuous_jb.comp ((continuous_id.sub continuous_const).div_const _)).measurable
  -- step 1
  have h1 : ENNReal.ofReal (g x) ≤ ∫⁻ z, ENNReal.ofReal (K (x - z) * g z) := by
    refine (ENNReal.ofReal_le_ofReal (hBern x)).trans ?_
    exact CZ.ofReal_integral_le_lintegral (fun z => mul_nonneg (hK0 _) (hg0 _))
  -- step 2
  set f₁ : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (K (x - z) * W z ^ b) with hf₁
  set h₁ : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (W z ^ (-b) * g z) with hh₁
  have h2 : ∀ z, ENNReal.ofReal (K (x - z) * g z) = f₁ z * h₁ z := by
    intro z
    simp only [hf₁, hh₁]
    rw [← ENNReal.ofReal_mul (mul_nonneg (hK0 _) (Real.rpow_nonneg (hWpos z).le _))]
    congr 1
    have : W z ^ b * W z ^ (-b) = 1 := by
      rw [← Real.rpow_add (hWpos z)]; simp
    calc K (x - z) * g z = K (x - z) * ((W z ^ b * W z ^ (-b)) * g z) := by rw [this, one_mul]
      _ = _ := by ring
  have hf₁m : Measurable f₁ :=
    ENNReal.measurable_ofReal.comp ((hKm.comp (measurable_const.sub measurable_id)).mul (hWm.pow_const _))
  have hh₁m : Measurable h₁ :=
    ENNReal.measurable_ofReal.comp ((hWm.pow_const _).mul hg)
  have h3 := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hHC.symm hf₁m.aemeasurable hh₁m.aemeasurable
  -- step 4: pointwise bound
  set Cx : ℝ := A * (3 / ℓ) * W x ^ b with hCx
  have hCx0 : 0 ≤ Cx := by rw [hCx]; have := hWpos x; positivity
  have h4 : ∀ z, f₁ z ≤ ENNReal.ofReal (Cx * (1 + |z - x| / ℓ) ^ (-(2 : ℝ))) := by
    intro z
    refine ENNReal.ofReal_le_ofReal ?_
    set e : ℝ := 1 + |z - x| / ℓ with he
    have he0 : 0 < e := by rw [he]; positivity
    have hWz : W z ≤ W x * e := by
      have := jb_add_le ((x - c0) / ℓ) ((z - x) / ℓ)
      have e1 : (x - c0) / ℓ + (z - x) / ℓ = (z - c0) / ℓ := by ring
      rw [e1] at this
      have e2 : jb ((z - x) / ℓ) = e := by
        rw [he]; unfold jb; rw [abs_div, abs_of_pos hℓ]
      rw [e2] at this
      exact this
    have hWb : W z ^ b ≤ W x ^ b * e ^ b := by
      calc W z ^ b ≤ (W x * e) ^ b := Real.rpow_le_rpow (hWpos z).le hWz hb
        _ = _ := Real.mul_rpow (hWpos x).le he0.le
    have hKz : K (x - z) ≤ A * (3 / ℓ) * e ^ (-(b + 2)) := by
      have := hKb (x - z)
      rwa [abs_sub_comm] at this
    have he2 : e ^ (-(b + 2)) * e ^ b = e ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add he0]; congr 1; ring
    calc K (x - z) * W z ^ b ≤ (A * (3 / ℓ) * e ^ (-(b + 2))) * (W x ^ b * e ^ b) :=
          mul_le_mul hKz hWb (Real.rpow_nonneg (hWpos z).le _) (by positivity)
      _ = A * (3 / ℓ) * W x ^ b * (e ^ (-(b + 2)) * e ^ b) := by ring
      _ = Cx * e ^ (-(2 : ℝ)) := by rw [he2]
  -- step 5: the `L^{R'}` norm of the kernel part
  have hp : 1 < 2 * R' := by linarith
  have hint := integrable_one_add_abs_sub_div_rpow hp x hℓ
  have hint2 := integral_one_add_abs_sub_div_rpow hp x hℓ
  have h5 : ∫⁻ z, f₁ z ^ R' ≤ ENNReal.ofReal (Cx ^ R' * (2 * ℓ / (2 * R' - 1))) := by
    calc ∫⁻ z, f₁ z ^ R' ≤ ∫⁻ z, ENNReal.ofReal (Cx ^ R') *
          ENNReal.ofReal ((1 + |z - x| / ℓ) ^ (-(2 * R'))) := by
          refine lintegral_mono fun z => ?_
          calc f₁ z ^ R' ≤ ENNReal.ofReal (Cx * (1 + |z - x| / ℓ) ^ (-(2 : ℝ))) ^ R' :=
                ENNReal.rpow_le_rpow (h4 z) hR'0.le
            _ = _ := by
                have hb0 : 0 ≤ (1 + |z - x| / ℓ) ^ (-(2 : ℝ)) := by positivity
                rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hCx0 hb0) hR'0.le,
                  ← ENNReal.ofReal_mul (Real.rpow_nonneg hCx0 _), Real.mul_rpow hCx0 hb0,
                  ← Real.rpow_mul (by positivity)]
                congr 3; ring
      _ = ENNReal.ofReal (Cx ^ R') * ∫⁻ z, ENNReal.ofReal ((1 + |z - x| / ℓ) ^ (-(2 * R'))) := by
          rw [lintegral_const_mul]
          exact ENNReal.measurable_ofReal.comp (((measurable_const.add
            ((continuous_abs.measurable.comp (measurable_id.sub_const x)).div_const ℓ)).pow_const _))
      _ = ENNReal.ofReal (Cx ^ R') * ENNReal.ofReal (2 * ℓ / (2 * R' - 1)) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun z => by positivity), hint2]
      _ = _ := by rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hCx0 _)]
  have h6 : (∫⁻ z, f₁ z ^ R') ^ (1 / R') ≤ ENNReal.ofReal (Cx * (2 * ℓ / (2 * R' - 1)) ^ (1 / R')) := by
    calc (∫⁻ z, f₁ z ^ R') ^ (1 / R') ≤ ENNReal.ofReal (Cx ^ R' * (2 * ℓ / (2 * R' - 1))) ^ (1 / R') :=
          ENNReal.rpow_le_rpow h5 (by positivity)
      _ = _ := by
          have hq0 : (0 : ℝ) < 2 * R' - 1 := by linarith
          have hq1 : 0 ≤ 2 * ℓ / (2 * R' - 1) := by positivity
          rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Real.rpow_nonneg hCx0 _) hq1) (by positivity),
            Real.mul_rpow (Real.rpow_nonneg hCx0 _) hq1, ← Real.rpow_mul hCx0, mul_one_div_cancel hR'0.ne',
            Real.rpow_one]
  -- step 6: the real identity
  have h7 : Cx * (2 * ℓ / (2 * R' - 1)) ^ (1 / R') = wsupConst A R' * W x ^ b * ℓ ^ (-1 / R) := by
    have hq0 : (0 : ℝ) < 2 * R' - 1 := by linarith
    have e1 : (2 * ℓ / (2 * R' - 1)) = (2 / (2 * R' - 1)) * ℓ := by ring
    have e2 : ℓ⁻¹ * ℓ ^ (1 / R') = ℓ ^ (-1 / R) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hℓ]
      congr 1
      have : 1 / R' = 1 - 1 / R := by
        have := hinv; simp only [one_div]; linarith
      rw [this]; ring
    rw [e1, Real.mul_rpow (by positivity) hℓ.le, hCx]
    unfold wsupConst
    calc A * (3 / ℓ) * W x ^ b * ((2 / (2 * R' - 1)) ^ (1 / R') * ℓ ^ (1 / R'))
        = 3 * A * (2 / (2 * R' - 1)) ^ (1 / R') * W x ^ b * (ℓ⁻¹ * ℓ ^ (1 / R')) := by
          field_simp
      _ = _ := by rw [e2]
  -- assembling
  have h8 : Lq R h₁ = (∫⁻ z, h₁ z ^ R) ^ (1 / R) := rfl
  calc ENNReal.ofReal (g x) ≤ ∫⁻ z, ENNReal.ofReal (K (x - z) * g z) := h1
    _ = ∫⁻ z, (f₁ * h₁) z := by simp only [Pi.mul_apply, h2]
    _ ≤ (∫⁻ z, f₁ z ^ R') ^ (1 / R') * (∫⁻ z, h₁ z ^ R) ^ (1 / R) := h3
    _ ≤ ENNReal.ofReal (Cx * (2 * ℓ / (2 * R' - 1)) ^ (1 / R')) * Lq R h₁ := by
        rw [h8]; exact mul_le_mul' h6 le_rfl
    _ = _ := by
        rw [h7, ENNReal.ofReal_mul (mul_nonneg (wsupConst_nonneg hA hR') (Real.rpow_nonneg (hWpos x).le _))]
        ring

/-- **Core Hölder step** `(2, 2, ∞)` of V15s. -/
theorem core_holder {ℓ c0 b N Cb : ℝ} (_hb : 0 ≤ b) (hNb : 3 * b ≤ N) (hCb : 0 ≤ Cb) {a₀ a₁ a₂ : ℝ → ℝ}
    (h₀ : Measurable a₀) (h₁ : Measurable a₁) (h₀' : ∀ z, 0 ≤ a₀ z) (h₁' : ∀ z, 0 ≤ a₁ z)
    (_h₂' : ∀ z, 0 ≤ a₂ z) {ε : ℝ≥0∞}
    (hε : ∀ x, ENNReal.ofReal (a₂ x) ≤ ENNReal.ofReal (Cb * jb ((x - c0) / ℓ) ^ b) * ε) :
    ∫⁻ x, ENNReal.ofReal (jb ((x - c0) / ℓ) ^ (-N) * (a₀ x * a₁ x * a₂ x)) ≤
      ENNReal.ofReal Cb * ε * (Lq 2 (fun z => ENNReal.ofReal (jb ((z - c0) / ℓ) ^ (-b) * a₀ z)) *
        Lq 2 (fun z => ENNReal.ofReal (jb ((z - c0) / ℓ) ^ (-b) * a₁ z))) := by
  set W : ℝ → ℝ := fun z => jb ((z - c0) / ℓ) with hW
  have hWpos : ∀ z, 0 < W z := fun z => jb_pos _
  have hW1 : ∀ z, 1 ≤ W z := fun z => one_le_jb _
  have hWm : Measurable W := (continuous_jb.comp ((continuous_id.sub continuous_const).div_const _)).measurable
  set A₀ : ℝ → ℝ := fun z => W z ^ (-b) * a₀ z with hA₀
  set A₁ : ℝ → ℝ := fun z => W z ^ (-b) * a₁ z with hA₁
  have hA₀m : Measurable A₀ := (hWm.pow_const _).mul h₀
  have hA₁m : Measurable A₁ := (hWm.pow_const _).mul h₁
  have hA₀0 : ∀ z, 0 ≤ A₀ z := fun z => mul_nonneg (Real.rpow_nonneg (hWpos z).le _) (h₀' z)
  have hA₁0 : ∀ z, 0 ≤ A₁ z := fun z => mul_nonneg (Real.rpow_nonneg (hWpos z).le _) (h₁' z)
  have hpt : ∀ x, ENNReal.ofReal (W x ^ (-N) * (a₀ x * a₁ x * a₂ x)) ≤
      ENNReal.ofReal Cb * ε * (ENNReal.ofReal (A₀ x) * ENNReal.ofReal (A₁ x)) := by
    intro x
    have hw1 : W x ^ b * W x ^ (-N) ≤ W x ^ (-b) * W x ^ (-b) := by
      rw [← Real.rpow_add (hWpos x), ← Real.rpow_add (hWpos x)]
      exact Real.rpow_le_rpow_of_exponent_le (hW1 x) (by linarith)
    have hx0 : 0 ≤ W x ^ (-N) * (a₀ x * a₁ x) := mul_nonneg (Real.rpow_nonneg (hWpos x).le _)
      (mul_nonneg (h₀' x) (h₁' x))
    calc ENNReal.ofReal (W x ^ (-N) * (a₀ x * a₁ x * a₂ x))
        = ENNReal.ofReal (W x ^ (-N) * (a₀ x * a₁ x)) * ENNReal.ofReal (a₂ x) := by
          rw [← ENNReal.ofReal_mul hx0]; congr 1; ring
      _ ≤ ENNReal.ofReal (W x ^ (-N) * (a₀ x * a₁ x)) * (ENNReal.ofReal (Cb * W x ^ b) * ε) :=
          mul_le_mul' le_rfl (hε x)
      _ = ENNReal.ofReal (Cb * (W x ^ b * W x ^ (-N)) * (a₀ x * a₁ x)) * ε := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hx0]; congr 2; ring
      _ ≤ ENNReal.ofReal (Cb * (W x ^ (-b) * W x ^ (-b)) * (a₀ x * a₁ x)) * ε := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          have := mul_nonneg (h₀' x) (h₁' x)
          gcongr
      _ = ENNReal.ofReal Cb * ε * (ENNReal.ofReal (A₀ x) * ENNReal.ofReal (A₁ x)) := by
          rw [← ENNReal.ofReal_mul (hA₀0 x)]
          have : Cb * (W x ^ (-b) * W x ^ (-b)) * (a₀ x * a₁ x) = Cb * (A₀ x * A₁ x) := by
            simp only [hA₀, hA₁]; ring
          rw [this, ENNReal.ofReal_mul hCb]
          ring
  calc ∫⁻ x, ENNReal.ofReal (W x ^ (-N) * (a₀ x * a₁ x * a₂ x))
      ≤ ∫⁻ x, ENNReal.ofReal Cb * ε * (ENNReal.ofReal (A₀ x) * ENNReal.ofReal (A₁ x)) := lintegral_mono hpt
    _ = ENNReal.ofReal Cb * ε * ∫⁻ x, ENNReal.ofReal (A₀ x) * ENNReal.ofReal (A₁ x) := by
        rw [lintegral_const_mul]
        exact (ENNReal.measurable_ofReal.comp hA₀m).mul (ENNReal.measurable_ofReal.comp hA₁m)
    _ ≤ ENNReal.ofReal Cb * ε * (Lq 2 (fun z => ENNReal.ofReal (A₀ z)) * Lq 2 (fun z => ENNReal.ofReal (A₁ z))) := by
        refine mul_le_mul' le_rfl ?_
        have := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
          (ENNReal.measurable_ofReal.comp hA₀m).aemeasurable (ENNReal.measurable_ofReal.comp hA₁m).aemeasurable
        simpa [Lq] using this

end PrimeBHT.TimeFrequency.X2
