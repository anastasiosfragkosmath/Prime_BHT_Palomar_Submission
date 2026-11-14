module

public import PrimeBHT.TimeFrequency.X2.Psp.O2Symbols

/-!
# X2, V13 O2 (c): the kernel of a layer multiplier and its increments (MTT2 `infty-kernel-bound`)

`Sym0 σ M C₀ m₀`: the multiplier `m₀` of a tree layer of scale `σ` in the frame centred at `0` (smooth, supported in
`|ξ| ≤ 3 · 2^{-σ}`, `(2^{-σ})^a |m₀^{(a)}| ≤ C₀` for `a ≤ M`).  Then for `K₀ = 𝓕⁻ m₀`:

* `Sym0.norm_ker_le`: `‖K₀(u)‖ ≤ C 2^{-σ} (1 + 2^{-σ}|u|)^{-M}`;
* `Sym0.norm_ker_diff_le`: for `|h| ≤ 2^σ`, `‖K₀(u + h) - K₀(u)‖ ≤ C 2^{-σ} (|h|/2^σ) (1 + 2^{-σ}|u|)^{-M}`
  (the kernel is the inverse transform of `m₀ (e(h ·) - 1)`, whose `M`-th derivative is `≲ (|h|/2^σ) 2^{σM}`, Leibniz).

`sym0_of_inMult`: a multiplier of the class `M_ω(𝔭)` of an overlapping slot, shifted by `θ`, is a `Sym0`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

theorem iteratedDeriv_cexp_real (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun ξ : ℝ => Complex.exp (c * (ξ : ℂ))) = fun ξ : ℝ => c ^ n * Complex.exp (c * (ξ : ℂ)) := by
  induction n with
  | zero => funext ξ; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext ξ
    have h1 : HasDerivAt (fun ξ : ℝ => Complex.exp (c * (ξ : ℂ))) (Complex.exp (c * (ξ : ℂ)) * (c * 1)) ξ := by
      have h0 : HasDerivAt (fun ξ : ℝ => c * (ξ : ℂ)) (c * 1) ξ :=
        (HasDerivAt.const_mul c (Complex.ofRealCLM.hasDerivAt (x := ξ)))
      exact h0.cexp
    have h2 := h1.const_mul (c ^ n)
    rw [h2.deriv]
    ring

/-- The multiplier of a tree layer of scale `σ` in the frame centred at `0`. -/
structure Sym0 (σ : ℤ) (M : ℕ) (C₀ : ℝ) (m₀ : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ m₀
  supp : ∀ ξ, 3 * (2 : ℝ) ^ (-σ) < |ξ| → m₀ ξ = 0
  deriv : ∀ a ≤ M, ∀ ξ, ((2 : ℝ) ^ (-σ)) ^ a * ‖iteratedDeriv a m₀ ξ‖ ≤ C₀

namespace Sym0

variable {σ : ℤ} {M : ℕ} {C₀ : ℝ} {m₀ : ℝ → ℂ}

theorem C_nonneg (h : Sym0 σ M C₀ m₀) : 0 ≤ C₀ := by
  have := h.deriv 0 (Nat.zero_le _) 0
  simp only [pow_zero, one_mul, iteratedDeriv_zero] at this
  exact (norm_nonneg _).trans this

theorem compact (h : Sym0 σ M C₀ m₀) : HasCompactSupport m₀ :=
  hasCompactSupport_of_far (c := 0) (r := 3 * (2 : ℝ) ^ (-σ)) (fun ξ hξ => h.supp ξ (by simpa using hξ))

theorem norm_le (h : Sym0 σ M C₀ m₀) (ξ : ℝ) : ‖m₀ ξ‖ ≤ C₀ := by
  have := h.deriv 0 (Nat.zero_le _) ξ
  simpa using this

theorem norm_iteratedDeriv_le (h : Sym0 σ M C₀ m₀) {a : ℕ} (ha : a ≤ M) (ξ : ℝ) :
    ‖iteratedDeriv a m₀ ξ‖ ≤ C₀ * ((2 : ℝ) ^ σ) ^ a := by
  have hp : (0 : ℝ) < ((2 : ℝ) ^ (-σ)) ^ a := pow_pos (zpow_two_pos _) _
  have h1 := h.deriv a ha ξ
  have e : C₀ * ((2 : ℝ) ^ σ) ^ a = C₀ / ((2 : ℝ) ^ (-σ)) ^ a := by
    rw [zpow_neg, inv_pow, div_inv_eq_mul, mul_comm]
  rw [e, le_div_iff₀ hp, mul_comm]
  exact h1

/-- **Kernel decay** of a layer multiplier. -/
theorem norm_ker_le (h : Sym0 σ M C₀ m₀) (u : ℝ) :
    ‖𝓕⁻ m₀ u‖ ≤ 2 ^ (M + 1) * (2 * (3 * (2 : ℝ) ^ (-σ))) * C₀ * ((1 + (2 : ℝ) ^ (-σ) * |u|)⁻¹) ^ M := by
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-σ) := zpow_two_pos _
  refine norm_fourierInv_le_pow (n := m₀) (c := 0) (r := 3 * (2 : ℝ) ^ (-σ)) (A := C₀) (l := (2 : ℝ) ^ (-σ)) M
    (by positivity) hl (h.smooth.of_le (by exact_mod_cast le_top)) (fun ξ hξ => h.supp ξ (by simpa using hξ))
    h.norm_le (fun ξ => ?_) u
  have h1 := h.deriv M le_rfl ξ
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hl _)]
  linarith

/-- the symbol `m₀ (e(h ·) - 1)` of the increment of the kernel -/
def incr (m₀ : ℝ → ℂ) (h : ℝ) (ξ : ℝ) : ℂ :=
  m₀ ξ * (Complex.exp (((2 * π * h : ℝ) * Complex.I : ℂ) * (ξ : ℂ)) - 1)

theorem fourierInv_incr (h : Sym0 σ M C₀ m₀) (hh u : ℝ) :
    𝓕⁻ (incr m₀ hh) u = 𝓕⁻ m₀ (u + hh) - 𝓕⁻ m₀ u := by
  have hi : ∀ a : ℝ, Integrable (fun ξ : ℝ => Complex.exp (↑(2 * π * ξ * a) * Complex.I) * m₀ ξ) := by
    intro a
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · have := h.smooth.continuous
      fun_prop
    · exact h.compact.mul_left
  rw [fourierInv_eq_integral_exp (incr m₀ hh) u, fourierInv_eq_integral_exp m₀ (u + hh),
    fourierInv_eq_integral_exp m₀ u, ← integral_sub (hi (u + hh)) (hi u)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  beta_reduce
  have : Complex.exp (↑(2 * π * ξ * (u + hh)) * Complex.I) =
      Complex.exp (↑(2 * π * ξ * u) * Complex.I) *
        Complex.exp (((2 * π * hh : ℝ) * Complex.I : ℂ) * (ξ : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  unfold incr
  rw [this]
  ring

theorem norm_incr_le (h : Sym0 σ M C₀ m₀) (hh : ℝ) (ξ : ℝ) :
    ‖incr m₀ hh ξ‖ ≤ C₀ * (6 * π * (|hh| / (2 : ℝ) ^ σ)) := by
  have hp := zpow_two_pos σ
  have hq := zpow_two_pos (-σ)
  have hpq : (2 : ℝ) ^ σ * (2 : ℝ) ^ (-σ) = 1 := by rw [← zpow_add₀ (by norm_num)]; simp
  by_cases hξ : 3 * (2 : ℝ) ^ (-σ) < |ξ|
  · unfold incr; rw [h.supp ξ hξ, zero_mul, norm_zero]
    have := h.C_nonneg
    positivity
  push Not at hξ
  unfold incr
  rw [norm_mul]
  have h1 : ‖Complex.exp (((2 * π * hh : ℝ) * Complex.I : ℂ) * (ξ : ℂ)) - 1‖ ≤ 6 * π * (|hh| / (2 : ℝ) ^ σ) := by
    have e : ((2 * π * hh : ℝ) * Complex.I : ℂ) * (ξ : ℂ) = Complex.I * ((2 * π * hh * ξ : ℝ) : ℂ) := by
      push_cast; ring
    rw [e]
    refine (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * π * hh * ξ)).trans ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]
    have : |ξ| ≤ 3 * (2 : ℝ) ^ (-σ) := hξ
    calc 2 * π * |hh| * |ξ| ≤ 2 * π * |hh| * (3 * (2 : ℝ) ^ (-σ)) := by gcongr
      _ = 6 * π * (|hh| / (2 : ℝ) ^ σ) := by
        rw [zpow_neg, div_eq_mul_inv]; ring
  exact mul_le_mul (h.norm_le ξ) h1 (norm_nonneg _) h.C_nonneg

/-- The `M`-th derivative of the increment symbol. -/
theorem norm_iteratedDeriv_incr_le (h : Sym0 σ M C₀ m₀) {hh : ℝ} (hh1 : |hh| ≤ (2 : ℝ) ^ σ) (ξ : ℝ) :
    ‖iteratedDeriv M (incr m₀ hh) ξ‖ ≤
      C₀ * (|hh| / (2 : ℝ) ^ σ) * (6 * π + (1 + 2 * π) ^ M) * ((2 : ℝ) ^ σ) ^ M := by
  have hp := zpow_two_pos σ
  have hq := zpow_two_pos (-σ)
  have hC := h.C_nonneg
  have hr : 0 ≤ |hh| / (2 : ℝ) ^ σ := by positivity
  have hr1 : |hh| / (2 : ℝ) ^ σ ≤ 1 := by rw [div_le_one hp]; exact hh1
  by_cases hξ : 3 * (2 : ℝ) ^ (-σ) < |ξ|
  · have := iteratedDeriv_eq_zero_of_far (n := incr m₀ hh) (c := 0) (r := 3 * (2 : ℝ) ^ (-σ))
      (fun ξ hξ => by unfold incr; rw [h.supp ξ (by simpa using hξ), zero_mul]) M (by simpa using hξ)
    rw [this, norm_zero]
    have : 0 ≤ (6 * π + (1 + 2 * π) ^ M) := by positivity
    positivity
  push Not at hξ
  set c : ℂ := ((2 * π * hh : ℝ) : ℂ) * Complex.I with hc
  have hcn : ‖c‖ = 2 * π * |hh| := by
    rw [hc, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]
  have hg : ContDiff ℝ ∞ (fun ξ : ℝ => Complex.exp (c * (ξ : ℂ)) - 1) :=
    (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)).sub contDiff_const
  have hexp : ContDiff ℝ ∞ (fun ξ : ℝ => Complex.exp (c * (ξ : ℂ))) :=
    Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
  -- Leibniz
  have hL : iteratedDeriv M (incr m₀ hh) ξ = ∑ i ∈ Finset.range (M + 1),
      (M.choose i : ℂ) * iteratedDeriv i m₀ ξ * iteratedDeriv (M - i) (fun ξ : ℝ => Complex.exp (c * (ξ : ℂ)) - 1) ξ := by
    have := iteratedDeriv_fun_mul (n := M) (x := ξ) (f := m₀) (g := fun ξ : ℝ => Complex.exp (c * (ξ : ℂ)) - 1)
      (h.smooth.contDiffAt.of_le (by exact_mod_cast le_top)) (hg.contDiffAt.of_le (by exact_mod_cast le_top))
    exact this
  -- derivatives of `exp(c ·) - 1`
  have hgd : ∀ j : ℕ, 1 ≤ j → ‖iteratedDeriv j (fun ξ : ℝ => Complex.exp (c * (ξ : ℂ)) - 1) ξ‖ ≤ ‖c‖ ^ j := by
    intro j hj
    have e1 : iteratedDeriv j (fun ξ : ℝ => Complex.exp (c * (ξ : ℂ)) - 1) ξ =
        iteratedDeriv j (fun ξ : ℝ => Complex.exp (c * (ξ : ℂ))) ξ -
          iteratedDeriv j (fun _ : ℝ => (1 : ℂ)) ξ :=
      iteratedDeriv_sub (hexp.contDiffAt.of_le (by exact_mod_cast le_top)) contDiffAt_const
    have e2 : iteratedDeriv j (fun _ : ℝ => (1 : ℂ)) ξ = 0 := by
      rw [iteratedDeriv_const]; simp; omega
    rw [e1, e2, sub_zero, iteratedDeriv_cexp_real c j]
    simp only [norm_mul, norm_pow, Complex.norm_exp]
    have : (c * (ξ : ℂ)).re = 0 := by
      rw [hc]; simp [Complex.mul_re]
    rw [this]; simp
  have hg0 : ‖iteratedDeriv 0 (fun ξ : ℝ => Complex.exp (c * (ξ : ℂ)) - 1) ξ‖ ≤ 6 * π * (|hh| / (2 : ℝ) ^ σ) := by
    simp only [iteratedDeriv_zero]
    have e : c * (ξ : ℂ) = Complex.I * ((2 * π * hh * ξ : ℝ) : ℂ) := by
      rw [hc]; push_cast; ring
    rw [e]
    refine (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * π * hh * ξ)).trans ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]
    calc 2 * π * |hh| * |ξ| ≤ 2 * π * |hh| * (3 * (2 : ℝ) ^ (-σ)) := by gcongr
      _ = 6 * π * (|hh| / (2 : ℝ) ^ σ) := by rw [zpow_neg, div_eq_mul_inv]; ring
  -- each term
  have hterm : ∀ i ∈ Finset.range (M + 1),
      ‖(M.choose i : ℂ) * iteratedDeriv i m₀ ξ * iteratedDeriv (M - i) (fun ξ : ℝ => Complex.exp (c * (ξ : ℂ)) - 1) ξ‖ ≤
        (M.choose i : ℝ) * (C₀ * (|hh| / (2 : ℝ) ^ σ) * (2 * π) ^ (M - i)) * ((2 : ℝ) ^ σ) ^ M +
          (if i = M then C₀ * (|hh| / (2 : ℝ) ^ σ) * (6 * π) * ((2 : ℝ) ^ σ) ^ M else 0) := by
    intro i hi
    have hiM : i ≤ M := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hm1 := h.norm_iteratedDeriv_le hiM ξ
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    by_cases hiM' : i = M
    · rw [hiM', ite_eq_left rfl]
      have hm1' : ‖iteratedDeriv M m₀ ξ‖ ≤ C₀ * ((2 : ℝ) ^ σ) ^ M := hiM' ▸ hm1
      have hg0' : ‖iteratedDeriv (M - M) (fun ξ : ℝ => Complex.exp (c * (ξ : ℂ)) - 1) ξ‖ ≤
          6 * π * (|hh| / (2 : ℝ) ^ σ) := by rw [Nat.sub_self]; exact hg0
      have h2 : ‖iteratedDeriv M m₀ ξ‖ *
          ‖iteratedDeriv (M - M) (fun ξ : ℝ => Complex.exp (c * (ξ : ℂ)) - 1) ξ‖ ≤
          (C₀ * ((2 : ℝ) ^ σ) ^ M) * (6 * π * (|hh| / (2 : ℝ) ^ σ)) :=
        mul_le_mul hm1' hg0' (norm_nonneg _) (by positivity)
      have h3 : 0 ≤ (M.choose M : ℝ) * (C₀ * (|hh| / (2 : ℝ) ^ σ) * (2 * π) ^ (M - M)) * ((2 : ℝ) ^ σ) ^ M := by
        positivity
      have h4 : (M.choose M : ℝ) = 1 := by simp
      rw [h4] at h3 ⊢
      nlinarith [h2, h3]
    · have hj : 1 ≤ M - i := by omega
      simp only [hiM', ite_false, add_zero]
      have h4 := hgd (M - i) hj
      rw [hcn] at h4
      have h5 : (2 * π * |hh|) ^ (M - i) ≤ (2 * π) ^ (M - i) * ((2 : ℝ) ^ σ) ^ (M - i) * (|hh| / (2 : ℝ) ^ σ) := by
        rw [mul_pow]
        have : |hh| ^ (M - i) ≤ ((2 : ℝ) ^ σ) ^ (M - i) * (|hh| / (2 : ℝ) ^ σ) := by
          have e : |hh| ^ (M - i) = ((2 : ℝ) ^ σ) ^ (M - i) * (|hh| / (2 : ℝ) ^ σ) ^ (M - i) := by
            rw [← mul_pow]; congr 1; field_simp
          rw [e]
          gcongr
          calc (|hh| / (2 : ℝ) ^ σ) ^ (M - i) ≤ (|hh| / (2 : ℝ) ^ σ) ^ 1 :=
                pow_le_pow_of_le_one hr hr1 hj
            _ = _ := pow_one _
        calc (2 * π) ^ (M - i) * |hh| ^ (M - i) ≤ (2 * π) ^ (M - i) * (((2 : ℝ) ^ σ) ^ (M - i) * (|hh| / (2 : ℝ) ^ σ)) := by
              gcongr
          _ = _ := by ring
      have hmM : ((2 : ℝ) ^ σ) ^ i * ((2 : ℝ) ^ σ) ^ (M - i) = ((2 : ℝ) ^ σ) ^ M := by
        rw [← pow_add]; congr 1; omega
      calc (M.choose i : ℝ) * ‖iteratedDeriv i m₀ ξ‖ * ‖iteratedDeriv (M - i) (fun ξ : ℝ => Complex.exp (c * (ξ : ℂ)) - 1) ξ‖
          ≤ (M.choose i : ℝ) * (C₀ * ((2 : ℝ) ^ σ) ^ i) * ((2 * π) ^ (M - i) * ((2 : ℝ) ^ σ) ^ (M - i) * (|hh| / (2 : ℝ) ^ σ)) := by
            gcongr
            exact le_trans h4 h5
        _ = (M.choose i : ℝ) * (C₀ * (|hh| / (2 : ℝ) ^ σ) * (2 * π) ^ (M - i)) * ((2 : ℝ) ^ σ) ^ M := by
            rw [← hmM]; ring
  rw [hL]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_add_distrib]
  have hbin : ∑ i ∈ Finset.range (M + 1), (M.choose i : ℝ) * (C₀ * (|hh| / (2 : ℝ) ^ σ) * (2 * π) ^ (M - i)) *
      ((2 : ℝ) ^ σ) ^ M = C₀ * (|hh| / (2 : ℝ) ^ σ) * (1 + 2 * π) ^ M * ((2 : ℝ) ^ σ) ^ M := by
    have := add_pow (1 : ℝ) (2 * π) M
    rw [this, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [one_pow, one_mul]
    ring
  have hif : ∑ i ∈ Finset.range (M + 1),
      (if i = M then C₀ * (|hh| / (2 : ℝ) ^ σ) * (6 * π) * ((2 : ℝ) ^ σ) ^ M else 0) =
      C₀ * (|hh| / (2 : ℝ) ^ σ) * (6 * π) * ((2 : ℝ) ^ σ) ^ M := by
    rw [Finset.sum_ite_eq' (Finset.range (M + 1)) M]
    simp
  rw [hbin, hif]
  apply le_of_eq
  ring

/-- **Kernel increments** of a layer multiplier: for `|h| ≤ 2^σ`,
`‖K₀(u + h) - K₀(u)‖ ≤ C 2^{-σ} (|h|/2^σ) (1 + 2^{-σ}|u|)^{-M}`. -/
theorem norm_ker_diff_le (h : Sym0 σ M C₀ m₀) (u hh : ℝ) (hh1 : |hh| ≤ (2 : ℝ) ^ σ) :
    ‖𝓕⁻ m₀ (u + hh) - 𝓕⁻ m₀ u‖ ≤
      2 ^ (M + 1) * (2 * (3 * (2 : ℝ) ^ (-σ))) *
        (C₀ * (|hh| / (2 : ℝ) ^ σ) * (6 * π + (1 + 2 * π) ^ M)) * ((1 + (2 : ℝ) ^ (-σ) * |u|)⁻¹) ^ M := by
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-σ) := zpow_two_pos _
  have hp := zpow_two_pos σ
  have hC := h.C_nonneg
  have hr : 0 ≤ |hh| / (2 : ℝ) ^ σ := by positivity
  have hAh : 0 ≤ C₀ * (|hh| / (2 : ℝ) ^ σ) * (6 * π + (1 + 2 * π) ^ M) := by positivity
  rw [← fourierInv_incr h hh u]
  have hinc : ContDiff ℝ M (incr m₀ hh) := by
    have : ContDiff ℝ ∞ (incr m₀ hh) := by
      unfold incr
      exact h.smooth.mul ((Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)).sub contDiff_const)
    exact this.of_le (by exact_mod_cast le_top)
  refine norm_fourierInv_le_pow (n := incr m₀ hh) (c := 0) (r := 3 * (2 : ℝ) ^ (-σ))
    (A := C₀ * (|hh| / (2 : ℝ) ^ σ) * (6 * π + (1 + 2 * π) ^ M)) (l := (2 : ℝ) ^ (-σ)) M (by positivity) hl hinc
    (fun ξ hξ => by unfold incr; rw [h.supp ξ (by simpa using hξ), zero_mul]) (fun ξ => ?_) (fun ξ => ?_) u
  · refine (norm_incr_le h hh ξ).trans ?_
    have : 6 * π ≤ 6 * π + (1 + 2 * π) ^ M := by
      have : 0 ≤ (1 + 2 * π) ^ M := by positivity
      linarith
    calc C₀ * (6 * π * (|hh| / (2 : ℝ) ^ σ)) = C₀ * (|hh| / (2 : ℝ) ^ σ) * (6 * π) := by ring
      _ ≤ _ := by gcongr
  · have := norm_iteratedDeriv_incr_le h hh1 ξ
    refine this.trans (le_of_eq ?_)
    rw [zpow_neg, inv_inv]

end Sym0

/-- A multiplier of the class `M_ω(𝔭)` of an overlapping slot, shifted by `θ`, is a `Sym0`. -/
theorem sym0_of_inMult {𝔭 : Params} {σ : ℤ} {c θ : ℝ} {m : ℝ → ℂ} (hm : InMult 𝔭 σ c m) (hβ : 𝔭.β ≤ 11 / 4)
    (hθ : |θ - c| ≤ 13 / 8 * (2 : ℝ) ^ (-σ)) : Sym0 σ 𝔭.D 𝔭.C (fun ξ => m (ξ + θ)) := by
  refine ⟨hm.1.comp (contDiff_id.add contDiff_const), fun ξ hξ => ?_, fun a ha ξ => ?_⟩
  · exact inMult_supp_theta hm hβ hθ (by simpa using hξ)
  · have := congrFun (iteratedDeriv_comp_add_const (n := a) (f := m) (s := θ)) ξ
    rw [this]
    exact hm.2.2 a ha (ξ + θ)

end PrimeBHT.TimeFrequency.X2
