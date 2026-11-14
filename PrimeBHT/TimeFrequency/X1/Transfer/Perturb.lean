module

public import PrimeBHT.TimeFrequency.X1.Transfer.Embed
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Part Z3 of `docs/x1-blueprint.md`: main term, error term, error operator

Let `K : ℝ → ℝ` be a kernel with `K(0) = 0`, differentiable, `|y| |K(y)| ≤ C` and `y² |K'(y)| ≤ C`
(Z2: `PrimeBHT.TimeFrequency.Transfer.exists_kernel_bounds`, uniform in `0 < λ ≤ μ`). With
`κ_m(u) = ∫ w_u(s) K(m + 1/2 + s) ds` (Z1) and `W(u) = ∫ w_u`:

* (a) `abs_kappaErr_le`: `κ_m(u) = W(u) K(m) + e_m(u)`, `|e_m(u)| ≤ 5 C · errW m` for all `u`
  (`errW m = 1 / max(1, |m|)^2`, the blueprint's `min(1, m^{-2})` with value `1` at `m = 0`).
* (b) `enorm_main_le`: for `|u| ≤ 1/12`, finitely supported `f, g`,
  `‖∑_m K(m) f(n - m) g(n + m)‖ₑ ≤ 6 (‖T_K(F, G)(n + u)‖ₑ + 5 C · 𝔈(f, g)(n))` where
  `𝔈(f, g)(n) = ∑_m errW m ‖f(n - m)‖ₑ ‖g(n + m)‖ₑ` (`errOp`, a positive bilinear operator
  independent of `u`, `L₁`, `L₂`).
* (c) `exists_errOp_bound`: for `0 < p, q`, `1/r = 1/p + 1/q`, `1/2 < r`, there is `A < ∞` with
  `∑_n 𝔈(f,g)(n)^r ≤ A (‖f‖_p ‖g‖_q)^r` (the `r`-triangle inequality for `r ≤ 1`, Hölder in the weights for
  `r > 1`, and Hölder with exponents `p/r, q/r` for each fixed `m`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Transfer

/-! ## The weight `errW` -/

/-- `errW m = 1 / max(1, |m|)²`. -/
def errW (m : ℤ) : ℝ := ((max 1 |(m : ℝ)|) ^ 2)⁻¹

theorem errW_pos (m : ℤ) : 0 < errW m := by
  unfold errW
  have : (0 : ℝ) < max 1 |(m : ℝ)| := lt_of_lt_of_le one_pos (le_max_left _ _)
  positivity

theorem errW_nonneg (m : ℤ) : 0 ≤ errW m := (errW_pos m).le

theorem errW_of_abs_le_one {m : ℤ} (h : |(m : ℝ)| ≤ 1) : errW m = 1 := by
  unfold errW
  rw [max_eq_left h]; norm_num

theorem errW_of_two_le {m : ℤ} (h : 2 ≤ |(m : ℝ)|) : errW m = ((m : ℝ) ^ 2)⁻¹ := by
  unfold errW
  rw [max_eq_right (by linarith), sq_abs]

/-! ## (a): the difference `K(y) - K(m)` -/

/-- For `y` with `|y - m - 1/2| < 1/3` (i.e. `y = m + 1/2 + s`, `|s| < 1/3`): `|K y - K m| ≤ 7 C errW m`. -/
theorem abs_sub_le_of_kernel {K : ℝ → ℝ} {C : ℝ} (hKd : Differentiable ℝ K) (hK0 : K 0 = 0)
    (h1 : ∀ y, |y| * |K y| ≤ C) (h2 : ∀ y, y ^ 2 * |deriv K y| ≤ C) (m : ℤ) {y : ℝ}
    (hy : |y - m - 1 / 2| < 1 / 3) : |K y - K m| ≤ 7 * C * errW m := by
  have hC : 0 ≤ C := (mul_nonneg (abs_nonneg _) (abs_nonneg _)).trans (h1 0)
  rw [abs_lt] at hy
  by_cases hm : 2 ≤ |(m : ℝ)|
  · have hm0 : (0 : ℝ) < (m : ℝ) ^ 2 := by
      have : (0 : ℝ) < |(m : ℝ)| := by linarith
      have h' : (m : ℝ) ≠ 0 := abs_pos.1 this
      positivity
    have hder : ∀ x ∈ Set.Icc ((m : ℝ) - 1) ((m : ℝ) + 1), ‖deriv K x‖ ≤ 4 * C / (m : ℝ) ^ 2 := by
      intro x hx
      have hxm : |(m : ℝ)| / 2 ≤ |x| := by
        have h3 := abs_sub_abs_le_abs_sub (m : ℝ) x
        have h4 : |(m : ℝ) - x| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
        linarith
      have hx2 : (m : ℝ) ^ 2 / 4 ≤ x ^ 2 := by
        have := pow_le_pow_left₀ (by positivity : 0 ≤ |(m : ℝ)| / 2) hxm 2
        rw [div_pow, sq_abs, sq_abs] at this
        linarith
      rw [Real.norm_eq_abs, le_div_iff₀ hm0]
      have h5 := mul_le_mul_of_nonneg_left hx2 (abs_nonneg (deriv K x))
      linarith [h2 x]
    have hmem : ∀ t : ℝ, |t - m| ≤ 1 → t ∈ Set.Icc ((m : ℝ) - 1) ((m : ℝ) + 1) := fun t ht => by
      rw [abs_le] at ht; exact ⟨by linarith, by linarith⟩
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => hKd x) hder
      (convex_Icc ((m : ℝ) - 1) ((m : ℝ) + 1)) (hmem m (by simp))
      (hmem y (by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]))
    have hym : ‖y - m‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hy.1, hy.2]
    rw [Real.norm_eq_abs] at hmv
    rw [errW_of_two_le hm]
    calc |K y - K m| ≤ 4 * C / (m : ℝ) ^ 2 * ‖y - m‖ := hmv
      _ ≤ 4 * C / (m : ℝ) ^ 2 * 1 := by gcongr
      _ ≤ 7 * C * ((m : ℝ) ^ 2)⁻¹ := by
          rw [mul_one, div_eq_mul_inv]
          have : 0 ≤ C * ((m : ℝ) ^ 2)⁻¹ := by positivity
          nlinarith
  · rw [not_le] at hm
    have hm1 : |(m : ℝ)| ≤ 1 := by
      have h' : |m| < 2 := by exact_mod_cast hm
      have h'' := abs_lt.1 h'
      have h3 : |m| ≤ 1 := abs_le.2 ⟨by omega, by omega⟩
      exact_mod_cast h3
    have hm' : (m : ℝ) = -1 ∨ (m : ℝ) = 0 ∨ (m : ℝ) = 1 := by
      have h' : |m| ≤ 1 := by exact_mod_cast hm1
      have h'' := abs_le.1 h'
      have : m = -1 ∨ m = 0 ∨ m = 1 := by omega
      rcases this with h | h | h <;> simp [h]
    have hy6 : 1 / 6 ≤ |y| := by
      rcases hm' with h | h | h <;> rw [h] at hy
      · exact le_abs.2 (Or.inr (by linarith [hy.1, hy.2]))
      · exact le_abs.2 (Or.inl (by linarith [hy.1, hy.2]))
      · exact le_abs.2 (Or.inl (by linarith [hy.1, hy.2]))
    have hKy : |K y| ≤ 6 * C := by
      have := mul_le_mul_of_nonneg_right hy6 (abs_nonneg (K y))
      linarith [h1 y]
    have hKm : |K m| ≤ C := by
      by_cases h0 : m = 0
      · rw [h0]; simp [hK0, hC]
      · have : (1 : ℝ) ≤ |(m : ℝ)| := by
          have : (1 : ℤ) ≤ |m| := Int.one_le_abs h0
          exact_mod_cast this
        have := mul_le_mul_of_nonneg_right this (abs_nonneg (K m))
        linarith [h1 m]
    rw [errW_of_abs_le_one hm1, mul_one]
    calc |K y - K m| ≤ |K y| + |K m| := abs_sub _ _
      _ ≤ 7 * C := by linarith

/-- The error of the main term. -/
def kappaErr (K : ℝ → ℝ) (m : ℤ) (u : ℝ) : ℝ := kappa K m u - winMass u * K m

/-- **Z3 (a).** `|κ_m(u) - W(u) K(m)| ≤ 5 C errW m`, for all `u`. -/
theorem abs_kappaErr_le {K : ℝ → ℝ} {C : ℝ} (hK : Continuous K) (hKd : Differentiable ℝ K)
    (hK0 : K 0 = 0) (h1 : ∀ y, |y| * |K y| ≤ C) (h2 : ∀ y, y ^ 2 * |deriv K y| ≤ C) (m : ℤ)
    (u : ℝ) : |kappaErr K m u| ≤ 5 * C * errW m := by
  have hC : 0 ≤ C := (mul_nonneg (abs_nonneg _) (abs_nonneg _)).trans (h1 0)
  set B : ℝ := 7 * C * errW m with hB
  have hB0 : 0 ≤ B := by rw [hB]; have := errW_nonneg m; positivity
  have hdiff : kappaErr K m u = ∫ s, winW u s * (K (m + 1 / 2 + s) - K m) := by
    unfold kappaErr kappa winMass
    simp_rw [mul_sub]
    rw [integral_sub (integrable_winW_mul hK u _) ((integrable_winW u).mul_const _),
      integral_mul_const]
  have hpt : ∀ s : ℝ, ‖winW u s * (K (m + 1 / 2 + s) - K m)‖ ≤ winW u s * B := by
    intro s
    by_cases h : winW u s = 0
    · simp [h]
    · have hs := abs_lt_of_winW_ne_zero h
      have hs3 : |(m : ℝ) + 1 / 2 + s - m - 1 / 2| < 1 / 3 := by
        rw [show (m : ℝ) + 1 / 2 + s - m - 1 / 2 = s by ring]
        linarith [abs_nonneg u]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (winW_nonneg u s)]
      exact mul_le_mul_of_nonneg_left (abs_sub_le_of_kernel hKd hK0 h1 h2 m hs3) (winW_nonneg u s)
  have hbound := norm_integral_le_of_norm_le ((integrable_winW u).mul_const B)
    (Eventually.of_forall hpt)
  rw [integral_mul_const, Real.norm_eq_abs] at hbound
  rw [hdiff]
  have hW : winMass u * B ≤ 2 / 3 * B := mul_le_mul_of_nonneg_right (winMass_le u) hB0
  calc |∫ s, winW u s * (K (m + 1 / 2 + s) - K m)| ≤ (∫ s, winW u s) * B := hbound
    _ = winMass u * B := rfl
    _ ≤ 2 / 3 * B := hW
    _ ≤ 5 * C * errW m := by
        rw [hB]; have := errW_nonneg m; nlinarith [mul_nonneg hC this]

/-! ## (b): the main term and the error operator -/

/-- The positive bilinear error operator `𝔈(f, g)(n) = ∑_m errW m ‖f(n - m)‖ₑ ‖g(n + m)‖ₑ`
(independent of `u`, `L₁`, `L₂`). -/
def errOp (f g : ℤ → ℂ) (n : ℤ) : ℝ≥0∞ :=
  ∑' m : ℤ, ENNReal.ofReal (errW m) * (‖f (n - m)‖ₑ * ‖g (n + m)‖ₑ)

/-- **Z3 (b).** For `|u| ≤ 1/12` and finitely supported `f, g`:
`‖∑_m K(m) f(n - m) g(n + m)‖ₑ ≤ 6 (‖∫ F(n + u - y) G(n + u + y) K(y) dy‖ₑ + 5 C 𝔈(f,g)(n))`,
`F = liftC (-1/2) f`, `G = liftC (1/2) g`. -/
theorem enorm_main_le {K : ℝ → ℝ} {C : ℝ} (hK : Continuous K) (hKd : Differentiable ℝ K)
    (hK0 : K 0 = 0) (hK1 : ∀ y, |y| * |K y| ≤ C) (hK2 : ∀ y, y ^ 2 * |deriv K y| ≤ C)
    {f g : ℤ → ℂ} (hf : (Function.support f).Finite) (hg : (Function.support g).Finite)
    (n : ℤ) {u : ℝ} (hu : |u| ≤ 1 / 12) :
    ‖∑' m : ℤ, (K m : ℂ) * f (n - m) * g (n + m)‖ₑ ≤
      6 * (‖∫ y, liftC (-1 / 2) f (n + u - y) * liftC (1 / 2) g (n + u + y) * (K y : ℂ)‖ₑ +
        ENNReal.ofReal (5 * C) * errOp f g n) := by
  classical
  have hC : 0 ≤ C := (mul_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hK1 0)
  set M : Finset ℤ := hf.toFinset.image (fun k => n - k) with hMdef
  have hM : ∀ m ∉ M, f (n - m) = 0 := by
    intro m hm
    by_contra h
    apply hm
    rw [hMdef, Finset.mem_image]
    exact ⟨n - m, by simpa using h, by ring⟩
  have hT : ∑' m : ℤ, f (n - m) * g (n + m) * (kappa K m u : ℂ) =
      ∑ m ∈ M, f (n - m) * g (n + m) * (kappa K m u : ℂ) :=
    tsum_eq_sum fun m hm => by simp [hM m hm]
  have hH : ∑' m : ℤ, (K m : ℂ) * f (n - m) * g (n + m) =
      ∑ m ∈ M, (K m : ℂ) * f (n - m) * g (n + m) :=
    tsum_eq_sum fun m hm => by simp [hM m hm]
  rw [integral_lift_eq hK hf hg n hu, hT, hH]
  have hTeq : ∑ m ∈ M, f (n - m) * g (n + m) * (kappa K m u : ℂ) =
      (winMass u : ℂ) * ∑ m ∈ M, (K m : ℂ) * f (n - m) * g (n + m) +
        ∑ m ∈ M, f (n - m) * g (n + m) * (kappaErr K m u : ℂ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold kappaErr
    push_cast
    ring
  have hE : ‖∑ m ∈ M, f (n - m) * g (n + m) * (kappaErr K m u : ℂ)‖ₑ ≤
      ENNReal.ofReal (5 * C) * errOp f g n := by
    calc ‖∑ m ∈ M, f (n - m) * g (n + m) * (kappaErr K m u : ℂ)‖ₑ
        ≤ ∑ m ∈ M, ‖f (n - m) * g (n + m) * (kappaErr K m u : ℂ)‖ₑ := enorm_sum_le _ _
      _ ≤ ∑ m ∈ M, ENNReal.ofReal (5 * C) *
            (ENNReal.ofReal (errW m) * (‖f (n - m)‖ₑ * ‖g (n + m)‖ₑ)) := by
          refine Finset.sum_le_sum fun m _ => ?_
          rw [enorm_mul, enorm_mul]
          have h1 : ‖((kappaErr K m u : ℝ) : ℂ)‖ₑ ≤
              ENNReal.ofReal (5 * C) * ENNReal.ofReal (errW m) := by
            rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
              ← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal (abs_kappaErr_le hK hKd hK0 hK1 hK2 m u)
          calc ‖f (n - m)‖ₑ * ‖g (n + m)‖ₑ * ‖((kappaErr K m u : ℝ) : ℂ)‖ₑ
              ≤ ‖f (n - m)‖ₑ * ‖g (n + m)‖ₑ * (ENNReal.ofReal (5 * C) * ENNReal.ofReal (errW m)) := by
                gcongr
            _ = ENNReal.ofReal (5 * C) * (ENNReal.ofReal (errW m) * (‖f (n - m)‖ₑ * ‖g (n + m)‖ₑ)) := by
                ring
      _ ≤ ENNReal.ofReal (5 * C) * errOp f g n := by
          rw [errOp, ← ENNReal.tsum_mul_left]
          exact ENNReal.sum_le_tsum M
  set H := ∑ m ∈ M, (K m : ℂ) * f (n - m) * g (n + m) with hHdef
  set E := ∑ m ∈ M, f (n - m) * g (n + m) * (kappaErr K m u : ℂ) with hEdef
  set T := ∑ m ∈ M, f (n - m) * g (n + m) * (kappa K m u : ℂ) with hTdef
  have hW : ENNReal.ofReal (1 / 6) ≤ ‖(winMass u : ℂ)‖ₑ := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (winMass_nonneg u)]
    exact ENNReal.ofReal_le_ofReal (le_winMass hu)
  have hWH : ‖(winMass u : ℂ) * H‖ₑ ≤ ‖T‖ₑ + ‖E‖ₑ := by
    have : (winMass u : ℂ) * H = T - E := by rw [hTeq]; ring
    rw [this]
    exact enorm_sub_le
  have h6 : ENNReal.ofReal (1 / 6) * ‖H‖ₑ ≤ ‖T‖ₑ + ‖E‖ₑ :=
    calc ENNReal.ofReal (1 / 6) * ‖H‖ₑ ≤ ‖(winMass u : ℂ)‖ₑ * ‖H‖ₑ := by gcongr
      _ = ‖(winMass u : ℂ) * H‖ₑ := (enorm_mul _ _).symm
      _ ≤ ‖T‖ₑ + ‖E‖ₑ := hWH
  have h66 : (6 : ℝ≥0∞) * ENNReal.ofReal (1 / 6) = 1 := by
    rw [← ENNReal.ofReal_ofNat 6, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  calc ‖H‖ₑ = 6 * (ENNReal.ofReal (1 / 6) * ‖H‖ₑ) := by rw [← mul_assoc, h66, one_mul]
    _ ≤ 6 * (‖T‖ₑ + ‖E‖ₑ) := by gcongr
    _ ≤ 6 * (‖T‖ₑ + ENNReal.ofReal (5 * C) * errOp f g n) := by gcongr

/-! ## (c): the `ℓ^p × ℓ^q → ℓ^r` bound for the error operator -/

/-- The `r`-triangle inequality for sums, `0 < r ≤ 1`. -/
theorem rpow_tsum_le_tsum_rpow {ι : Type*} (x : ι → ℝ≥0∞) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (∑' i, x i) ^ r ≤ ∑' i, x i ^ r := by
  classical
  have hfin : ∀ s : Finset ι, (∑ i ∈ s, x i) ^ r ≤ ∑ i ∈ s, x i ^ r := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [ENNReal.zero_rpow_of_pos hr0]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (ENNReal.rpow_add_le_add_rpow _ _ hr0.le hr1).trans (by gcongr)
  rw [← ENNReal.le_rpow_inv_iff hr0, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  rw [ENNReal.le_rpow_inv_iff hr0]
  exact (hfin s).trans (ENNReal.sum_le_tsum s)

/-- Hölder's inequality with weights on `ℤ`, `r ≥ 1`: `(∑ w x)^r ≤ (∑ w)^{r-1} ∑ w x^r`. -/
theorem rpow_tsum_mul_le (w x : ℤ → ℝ≥0∞) {r : ℝ} (hr : 1 ≤ r) :
    (∑' i, w i * x i) ^ r ≤ (∑' i, w i) ^ (r - 1) * ∑' i, w i * x i ^ r := by
  rcases hr.eq_or_lt with rfl | hr1
  · simp
  · set q := Real.conjExponent r with hq
    have hconj : r.HolderConjugate q := Real.HolderConjugate.conjExponent hr1
    have hr0 : 0 < r := by linarith
    have hq0 : 0 < q := hconj.right_pos
    have hinv : 1 / r + 1 / q = 1 := by
      have := hconj.inv_add_inv_eq_inv
      simpa [one_div] using this
    have key := ENNReal.lintegral_mul_le_Lp_mul_Lq Measure.count hconj
      (f := fun i : ℤ => w i ^ (1 / r) * x i) (g := fun i : ℤ => w i ^ (1 / q))
      (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable
    have e1 : ∀ i, (fun i : ℤ => w i ^ (1 / r) * x i) i * (fun i : ℤ => w i ^ (1 / q)) i = w i * x i := by
      intro i
      show w i ^ (1 / r) * x i * w i ^ (1 / q) = w i * x i
      rw [mul_right_comm, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hinv,
        ENNReal.rpow_one]
    have e2 : ∀ i, (w i ^ (1 / r) * x i) ^ r = w i * x i ^ r := by
      intro i
      rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hr0.ne',
        ENNReal.rpow_one]
    have e3 : ∀ i, (w i ^ (1 / q)) ^ q = w i := by
      intro i
      rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
    simp only [Pi.mul_apply, e1, e2, e3, lintegral_count] at key
    have key2 := ENNReal.rpow_le_rpow key hr0.le
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      one_div, inv_mul_cancel₀ hr0.ne', ENNReal.rpow_one] at key2
    have e4 : (1 / q) * r = r - 1 := by
      have : 1 / q = 1 - 1 / r := by linarith
      rw [this]; field_simp
    rw [e4, mul_comm] at key2
    exact key2

/-- Hölder for a fixed shift `m`: `∑_n (‖f(n - m)‖ₑ ‖g(n + m)‖ₑ)^r ≤ (‖f‖_p ‖g‖_q)^r`
for `1/r = 1/p + 1/q`, also for `r < 1`. -/
theorem tsum_enorm_mul_rpow_le {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 1 / r = 1 / p + 1 / q)
    (hr0 : 0 < r) (f g : ℤ → ℂ) (m : ℤ) :
    ∑' n : ℤ, (‖f (n - m)‖ₑ * ‖g (n + m)‖ₑ) ^ r ≤
      (eLpNorm f (ENNReal.ofReal p) Measure.count * eLpNorm g (ENNReal.ofReal q) Measure.count) ^ r := by
  have htriple : Real.HolderTriple p q r := ⟨by simpa [one_div] using hr.symm, hp, hq⟩
  have key := ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr htriple Measure.count
    (f := fun n : ℤ => ‖f (n - m)‖ₑ) (g := fun n : ℤ => ‖g (n + m)‖ₑ)
    (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable
  simp only [Pi.mul_apply, lintegral_count] at key
  have e1 : ∑' n : ℤ, ‖f (n - m)‖ₑ ^ p = ∑' k : ℤ, ‖f k‖ₑ ^ p :=
    (Equiv.subRight m).tsum_eq (fun k : ℤ => ‖f k‖ₑ ^ p)
  have e2 : ∑' n : ℤ, ‖g (n + m)‖ₑ ^ q = ∑' k : ℤ, ‖g k‖ₑ ^ q :=
    (Equiv.addRight m).tsum_eq (fun k : ℤ => ‖g k‖ₑ ^ q)
  rw [e1, e2, ← eLpNorm_count_eq f hp, ← eLpNorm_count_eq g hq] at key
  have key2 := ENNReal.rpow_le_rpow key hr0.le
  rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hr0.ne', ENNReal.rpow_one] at key2

theorem summable_errW_rpow {s : ℝ} (hs : 1 / 2 < s) : Summable fun m : ℤ => errW m ^ s := by
  have hb : 1 < 2 * s := by linarith
  have hsum := (Real.summable_abs_int_rpow hb).add (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  refine Summable.of_nonneg_of_le (fun m => Real.rpow_nonneg (errW_nonneg m) s) (fun m => ?_) hsum
  by_cases hm : m = 0
  · subst hm
    have : errW 0 = 1 := errW_of_abs_le_one (by simp)
    have h0 : (0 : ℝ) ≤ |((0 : ℤ) : ℝ)| ^ (-(2 * s)) := Real.rpow_nonneg (abs_nonneg _) _
    simp only [this, Real.one_rpow, ite_true]
    linarith
  · have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
      exact_mod_cast this
    have h2 : errW m ^ s = |(m : ℝ)| ^ (-(2 * s)) := by
      rw [errW, max_eq_right h1, Real.inv_rpow (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_mul (abs_nonneg _), Real.rpow_neg (abs_nonneg _)]
      norm_num
    simp only [h2, hm, ite_false, add_zero]
    exact le_rfl

theorem tsum_ofReal_errW_rpow_ne_top {s : ℝ} (hs : 1 / 2 < s) :
    ∑' m : ℤ, ENNReal.ofReal (errW m) ^ s ≠ ⊤ := by
  have : ∀ m : ℤ, ENNReal.ofReal (errW m) ^ s = ENNReal.ofReal (errW m ^ s) := fun m =>
    ENNReal.ofReal_rpow_of_nonneg (errW_nonneg m) (by linarith)
  simp_rw [this]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => Real.rpow_nonneg (errW_nonneg m) s)
    (summable_errW_rpow hs)]
  exact ENNReal.ofReal_ne_top

theorem tsum_ofReal_errW_ne_top : ∑' m : ℤ, ENNReal.ofReal (errW m) ≠ ⊤ := by
  have := tsum_ofReal_errW_rpow_ne_top (s := 1) (by norm_num)
  simpa only [ENNReal.rpow_one] using this

/-- **Z3 (c).** For `0 < p, q`, `1/r = 1/p + 1/q`, `1/2 < r` (so also `r < 1` is covered), there is
a finite constant `A` (`A = ∑_m errW(m)^r` for `r ≤ 1`, `A = (∑_m errW(m))^r` for `r > 1`) with
`∑_n 𝔈(f,g)(n)^r ≤ A (‖f‖_{ℓ^p} ‖g‖_{ℓ^q})^r` for all `f, g`. -/
theorem exists_errOp_bound {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 1 / r = 1 / p + 1 / q)
    (hr2 : 1 / 2 < r) :
    ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ f g : ℤ → ℂ,
      ∑' n : ℤ, errOp f g n ^ r ≤
        A * (eLpNorm f (ENNReal.ofReal p) Measure.count *
          eLpNorm g (ENNReal.ofReal q) Measure.count) ^ r := by
  have hr0 : 0 < r := by linarith
  by_cases hr1 : r ≤ 1
  · refine ⟨∑' m : ℤ, ENNReal.ofReal (errW m) ^ r, tsum_ofReal_errW_rpow_ne_top hr2, fun f g => ?_⟩
    calc ∑' n : ℤ, errOp f g n ^ r
        ≤ ∑' n : ℤ, ∑' m : ℤ, (ENNReal.ofReal (errW m) * (‖f (n - m)‖ₑ * ‖g (n + m)‖ₑ)) ^ r :=
          ENNReal.tsum_le_tsum fun n => rpow_tsum_le_tsum_rpow _ hr0 hr1
      _ = ∑' m : ℤ, ∑' n : ℤ, (ENNReal.ofReal (errW m) * (‖f (n - m)‖ₑ * ‖g (n + m)‖ₑ)) ^ r :=
          ENNReal.tsum_comm
      _ = ∑' m : ℤ, ENNReal.ofReal (errW m) ^ r * ∑' n : ℤ, (‖f (n - m)‖ₑ * ‖g (n + m)‖ₑ) ^ r := by
          refine tsum_congr fun m => ?_
          simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le]
          exact ENNReal.tsum_mul_left
      _ ≤ ∑' m : ℤ, ENNReal.ofReal (errW m) ^ r *
            (eLpNorm f (ENNReal.ofReal p) Measure.count *
              eLpNorm g (ENNReal.ofReal q) Measure.count) ^ r :=
          ENNReal.tsum_le_tsum fun m => by
            gcongr
            exact tsum_enorm_mul_rpow_le hp hq hr hr0 f g m
      _ = (∑' m : ℤ, ENNReal.ofReal (errW m) ^ r) *
            (eLpNorm f (ENNReal.ofReal p) Measure.count *
              eLpNorm g (ENNReal.ofReal q) Measure.count) ^ r := ENNReal.tsum_mul_right
  · rw [not_le] at hr1
    refine ⟨(∑' m : ℤ, ENNReal.ofReal (errW m)) ^ r,
      ENNReal.rpow_ne_top_of_nonneg hr0.le tsum_ofReal_errW_ne_top, fun f g => ?_⟩
    have hadd : (∑' m : ℤ, ENNReal.ofReal (errW m)) ^ r =
        (∑' m : ℤ, ENNReal.ofReal (errW m)) ^ (r - 1) * ∑' m : ℤ, ENNReal.ofReal (errW m) := by
      have := ENNReal.rpow_add_of_nonneg (x := ∑' m : ℤ, ENNReal.ofReal (errW m)) (r - 1) 1
        (by linarith) zero_le_one
      rwa [sub_add_cancel, ENNReal.rpow_one] at this
    calc ∑' n : ℤ, errOp f g n ^ r
        ≤ ∑' n : ℤ, (∑' m : ℤ, ENNReal.ofReal (errW m)) ^ (r - 1) *
            ∑' m : ℤ, ENNReal.ofReal (errW m) * (‖f (n - m)‖ₑ * ‖g (n + m)‖ₑ) ^ r :=
          ENNReal.tsum_le_tsum fun n =>
            rpow_tsum_mul_le (fun m => ENNReal.ofReal (errW m))
              (fun m => ‖f (n - m)‖ₑ * ‖g (n + m)‖ₑ) hr1.le
      _ = (∑' m : ℤ, ENNReal.ofReal (errW m)) ^ (r - 1) *
            ∑' n : ℤ, ∑' m : ℤ, ENNReal.ofReal (errW m) * (‖f (n - m)‖ₑ * ‖g (n + m)‖ₑ) ^ r :=
          ENNReal.tsum_mul_left
      _ = (∑' m : ℤ, ENNReal.ofReal (errW m)) ^ (r - 1) *
            ∑' m : ℤ, ENNReal.ofReal (errW m) * ∑' n : ℤ, (‖f (n - m)‖ₑ * ‖g (n + m)‖ₑ) ^ r := by
          rw [ENNReal.tsum_comm]
          congr 1
          exact tsum_congr fun m => ENNReal.tsum_mul_left
      _ ≤ (∑' m : ℤ, ENNReal.ofReal (errW m)) ^ (r - 1) *
            ∑' m : ℤ, ENNReal.ofReal (errW m) *
              (eLpNorm f (ENNReal.ofReal p) Measure.count *
                eLpNorm g (ENNReal.ofReal q) Measure.count) ^ r := by
          gcongr with m
          exact tsum_enorm_mul_rpow_le hp hq hr hr0 f g m
      _ = (∑' m : ℤ, ENNReal.ofReal (errW m)) ^ r *
            (eLpNorm f (ENNReal.ofReal p) Measure.count *
              eLpNorm g (ENNReal.ofReal q) Measure.count) ^ r := by
          rw [ENNReal.tsum_mul_right, hadd]
          ring

end PrimeBHT.TimeFrequency.Transfer

end
