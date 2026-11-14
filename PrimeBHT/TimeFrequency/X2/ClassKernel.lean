module

public import PrimeBHT.TimeFrequency.X2.Classes
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# X2, node V07: analytic toolbox for the adapted classes

Helper lemmas of `X2/ClassLemmas.lean` (`norm_singleTile_le`, `treeOp_locPoly`), none of which is a node
statement:

* `yNorm` is a norm for `s ≥ 1` in the form needed: homogeneity, coordinate bound, measurability and
  **Minkowski's integral inequality** `yNorm_integral_le_of_one_le` (through `PiLp`; also valid for `s = 1`);
* decay of the kernel `𝓕⁻ n` of a smooth compactly supported multiplier (`norm_fourierInv_le`:
  `‖𝓕⁻ n w‖ ≤ 3 (2r) A (1 + l|w|)⁻²`), continuity of `𝓕⁻ n`;
* integrability of `(x - a)^k f(x)` for `f` with decay `⟨(x - c)/L⟩^{-N}` (`integrable_pow_mul_jb`);
* Fourier support is preserved by multiplication with `(x - a)^k` (`fourier_pow_mul_eq_zero`).
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform ComplexConjugate ContDiff Real
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-! ### `yNorm` facts -/

section YNorm
variable {P : ℕ} [NeZero P]

theorem yNorm_nonneg' (s : ℝ) (G : ZMod P → ℂ) : 0 ≤ yNorm s G :=
  Real.rpow_nonneg (by positivity) _

theorem yNorm_eq_rpow_mul (s : ℝ) (G : ZMod P → ℂ) :
    yNorm s G = (P : ℝ) ^ (-s⁻¹) * (∑ y, ‖G y‖ ^ s) ^ s⁻¹ := by
  have hP : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
  unfold yNorm
  rw [Real.mul_rpow (by positivity) (Finset.sum_nonneg fun y _ => Real.rpow_nonneg (norm_nonneg _) _),
    Real.inv_rpow hP.le, Real.rpow_neg hP.le]

theorem yNorm_eq_norm_toLp {s : ℝ} (hs : 1 ≤ s) (G : ZMod P → ℂ) :
    yNorm s G = (P : ℝ) ^ (-s⁻¹) *
      ‖(WithLp.toLp (ENNReal.ofReal s) G : PiLp (ENNReal.ofReal s) (fun _ : ZMod P => ℂ))‖ := by
  have hs0 : 0 < s := by linarith
  rw [yNorm_eq_rpow_mul, PiLp.norm_eq_sum (by rw [ENNReal.toReal_ofReal hs0.le]; exact hs0)]
  simp [ENNReal.toReal_ofReal hs0.le]

theorem yNorm_fun_const_mul {s : ℝ} (hs : 0 < s) (c : ℂ) (G : ZMod P → ℂ) :
    yNorm s (fun y => c * G y) = ‖c‖ * yNorm s G := by
  unfold yNorm
  simp only [norm_mul]
  simp_rw [Real.mul_rpow (norm_nonneg c) (norm_nonneg _)]
  rw [← Finset.mul_sum, ← mul_assoc, mul_comm (P : ℝ)⁻¹, mul_assoc,
    Real.mul_rpow (Real.rpow_nonneg (norm_nonneg _) _) (by positivity),
    Real.rpow_rpow_inv (norm_nonneg _) hs.ne']

theorem norm_apply_le_rpow_mul_yNorm {s : ℝ} (hs : 0 < s) (G : ZMod P → ℂ) (y : ZMod P) :
    ‖G y‖ ≤ (P : ℝ) ^ s⁻¹ * yNorm s G := by
  have hP : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
  have h1 : ‖G y‖ ^ s ≤ ∑ y', ‖G y'‖ ^ s :=
    Finset.single_le_sum (f := fun y' => ‖G y'‖ ^ s) (fun y' _ => Real.rpow_nonneg (norm_nonneg _) _)
      (Finset.mem_univ y)
  have h2 : ‖G y‖ ≤ (∑ y', ‖G y'‖ ^ s) ^ s⁻¹ := by
    calc ‖G y‖ = (‖G y‖ ^ s) ^ s⁻¹ := (Real.rpow_rpow_inv (norm_nonneg _) hs.ne').symm
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) h1 (inv_nonneg.2 hs.le)
  have h3 : (P : ℝ) ^ s⁻¹ * yNorm s G = (∑ y', ‖G y'‖ ^ s) ^ s⁻¹ := by
    rw [yNorm_eq_rpow_mul, ← mul_assoc, ← Real.rpow_add hP]
    simp
  rw [h3]; exact h2

theorem measurable_yNorm_fun (s : ℝ) : Measurable (fun G : ZMod P → ℂ => yNorm s G) := by
  unfold yNorm
  refine Measurable.pow_const (Measurable.const_mul (Finset.measurable_sum _ fun y _ => ?_) _) _
  exact (measurable_pi_apply y).norm.pow_const s

/-- **Minkowski's integral inequality** for the normalized `ℓ^s` norm of `Y_P` (`s ≥ 1`). -/
theorem yNorm_integral_le_of_one_le {s : ℝ} (hs : 1 ≤ s) (V : ℝ → ZMod P → ℂ)
    (hV : ∀ y, Integrable (fun a => V a y)) :
    yNorm s (fun y => ∫ a, V a y) ≤ ∫ a, yNorm s (V a) := by
  have : Fact (1 ≤ ENNReal.ofReal s) := ⟨by simpa using ENNReal.ofReal_le_ofReal hs⟩
  set p := ENNReal.ofReal s with hp
  set U : ℝ → PiLp p (fun _ : ZMod P => ℂ) := fun a => WithLp.toLp p (V a) with hU
  have hUy : ∀ y, Integrable (fun a => U a y) := fun y => hV y
  have hUi : Integrable U := integrable_piLp_iff.2 hUy
  have hcoord : (WithLp.toLp p (fun y => ∫ a, V a y) : PiLp p (fun _ : ZMod P => ℂ)) = ∫ a, U a := by
    ext y
    rw [eval_integral_piLp hUy y]
  have hc : 0 ≤ (P : ℝ) ^ (-s⁻¹) := by positivity
  rw [yNorm_eq_norm_toLp hs, hcoord]
  calc (P : ℝ) ^ (-s⁻¹) * ‖∫ a, U a‖ ≤ (P : ℝ) ^ (-s⁻¹) * ∫ a, ‖U a‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hc
    _ = ∫ a, (P : ℝ) ^ (-s⁻¹) * ‖U a‖ := (integral_const_mul _ _).symm
    _ = ∫ a, yNorm s (V a) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        simp only [hU]
        rw [yNorm_eq_norm_toLp hs]

end YNorm

/-! ### Kernels of smooth compactly supported multipliers -/


theorem iteratedDeriv_eq_zero_of_far {n : ℝ → ℂ} {c r : ℝ}
    (hn : ∀ ξ, r < |ξ - c| → n ξ = 0) (k : ℕ) {ξ : ℝ} (hξ : r < |ξ - c|) :
    iteratedDeriv k n ξ = 0 := by
  have h : n =ᶠ[𝓝 ξ] (0 : ℝ → ℂ) := by
    have hopen : IsOpen {ξ' : ℝ | r < |ξ' - c|} := isOpen_lt continuous_const (by fun_prop)
    filter_upwards [hopen.mem_nhds hξ] with ξ' hξ' using hn ξ' hξ'
  rw [h.iteratedDeriv_eq k]
  simp

theorem hasCompactSupport_of_far {f : ℝ → ℂ} {c r : ℝ} (hf : ∀ ξ, r < |ξ - c| → f ξ = 0) :
    HasCompactSupport f := by
  refine HasCompactSupport.intro (isCompact_Icc (a := c - r) (b := c + r)) fun ξ hξ => hf ξ ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at hξ
  rw [lt_abs]
  rcases hξ with h | h
  · right; linarith
  · left; linarith

theorem integrable_of_far {f : ℝ → ℂ} {c r : ℝ} (hc : Continuous f)
    (hf : ∀ ξ, r < |ξ - c| → f ξ = 0) : Integrable f :=
  hc.integrable_of_hasCompactSupport (hasCompactSupport_of_far hf)

theorem integral_norm_le_of_far {f : ℝ → ℂ} {c r A : ℝ} (hr : 0 ≤ r)
    (hf : ∀ ξ, r < |ξ - c| → f ξ = 0) (hA : ∀ ξ, ‖f ξ‖ ≤ A) :
    ∫ ξ, ‖f ξ‖ ≤ 2 * r * A := by
  have h1 : ∫ ξ, ‖f ξ‖ = ∫ ξ in Set.Icc (c - r) (c + r), ‖f ξ‖ := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun ξ hξ => ?_).symm
    have : ‖f ξ‖ = 0 := by
      rw [hf ξ ?_, norm_zero]
      simp only [Set.mem_Icc, not_and_or, not_le] at hξ
      rw [lt_abs]
      rcases hξ with h | h
      · right; linarith
      · left; linarith
    exact this
  rw [h1]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (c - r) (c + r))
    (f := fun ξ => ‖f ξ‖) (C := A) (by simp) (fun ξ _ => by simpa using hA ξ)
  have h2 : volume.real (Set.Icc (c - r) (c + r)) = 2 * r := by
    rw [Real.volume_real_Icc_of_le (by linarith : c - r ≤ c + r)]; ring
  rw [h2, Real.norm_eq_abs] at this
  calc _ ≤ |∫ ξ in Set.Icc (c - r) (c + r), ‖f ξ‖| := le_abs_self _
    _ ≤ A * (2 * r) := this
    _ = 2 * r * A := by ring

/-- Decay of the kernel `𝓕⁻ n` of a smooth compactly supported multiplier `n` (support in `|ξ - c| ≤ r`,
`‖n‖ ≤ A`, `‖n''‖ ≤ A l⁻²`): `‖𝓕⁻ n w‖ ≤ 3 (2r) A (1 + l |w|)⁻²`. -/
theorem norm_fourierInv_le {n : ℝ → ℂ} {c r A l : ℝ} (hr : 0 ≤ r) (hl : 0 < l)
    (hn : ContDiff ℝ 2 n) (hsupp : ∀ ξ, r < |ξ - c| → n ξ = 0)
    (h0 : ∀ ξ, ‖n ξ‖ ≤ A) (h2 : ∀ ξ, ‖iteratedDeriv 2 n ξ‖ ≤ A * (l⁻¹) ^ 2) (w : ℝ) :
    ‖𝓕⁻ n w‖ ≤ 3 * (2 * r) * A * ((1 + l * |w|)⁻¹) ^ 2 := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (h0 0)
  have hint : ∀ k : ℕ, k ≤ 2 → Integrable (iteratedDeriv k n) := fun k hk =>
    integrable_of_far (hn.continuous_iteratedDeriv k (by exact_mod_cast hk))
      (fun ξ hξ => iteratedDeriv_eq_zero_of_far hsupp k hξ)
  have hK0 : ‖𝓕⁻ n w‖ ≤ 2 * r * A := by
    rw [Real.fourierInv_eq_fourier_neg]
    exact (Real.norm_fourier_le_integral_norm n (-w)).trans
      (integral_norm_le_of_far hr hsupp h0)
  have hF2 : 𝓕 (iteratedDeriv 2 n) = fun x : ℝ => (2 * π * Complex.I * x) ^ 2 • 𝓕 n x :=
    Real.fourier_iteratedDeriv (N := 2) hn (fun k hk => hint k (by exact_mod_cast hk)) (by norm_num)
  have hnorm : ∀ x : ℝ, ‖(2 * π * Complex.I * x : ℂ) ^ 2‖ = (2 * π * |x|) ^ 2 := by
    intro x
    rw [norm_pow]
    congr 1
    simp only [Complex.norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_one,
      Complex.norm_ofNat, abs_of_pos Real.pi_pos]
  have hK2 : (2 * π * w) ^ 2 * ‖𝓕⁻ n w‖ ≤ 2 * r * (A * (l⁻¹) ^ 2) := by
    have h1 := Real.norm_fourier_le_integral_norm (iteratedDeriv 2 n) (-w)
    rw [hF2] at h1
    simp only [norm_smul, hnorm] at h1
    have h3 : (2 * π * |-w|) ^ 2 * ‖𝓕 n (-w)‖ ≤ 2 * r * (A * (l⁻¹) ^ 2) :=
      h1.trans (integral_norm_le_of_far hr (fun ξ hξ => iteratedDeriv_eq_zero_of_far hsupp 2 hξ) h2)
    rw [Real.fourierInv_eq_fourier_neg]
    rw [abs_neg] at h3
    calc (2 * π * w) ^ 2 * ‖𝓕 n (-w)‖ = (2 * π * |w|) ^ 2 * ‖𝓕 n (-w)‖ := by rw [mul_pow (2 * π), mul_pow (2 * π), sq_abs]
      _ ≤ _ := h3
  set K := ‖𝓕⁻ n w‖ with hK
  have hK_nn : 0 ≤ K := norm_nonneg _
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  have hlw : 0 < 1 + l * |w| := by positivity
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hl2 : l ^ 2 * (l⁻¹) ^ 2 = 1 := by field_simp
  have e1 : (2 * π * w) ^ 2 * K * l ^ 2 ≤ 2 * r * A := by
    have := mul_le_mul_of_nonneg_right hK2 (sq_nonneg l)
    calc (2 * π * w) ^ 2 * K * l ^ 2 ≤ 2 * r * (A * (l⁻¹) ^ 2) * l ^ 2 := this
      _ = 2 * r * A * (l ^ 2 * (l⁻¹) ^ 2) := by ring
      _ = 2 * r * A := by rw [hl2]; ring
  have e2 : (l * |w|) ^ 2 * K ≤ 2 * r * A / 4 := by
    have h4 : (2 * π * w) ^ 2 * K * l ^ 2 = 4 * π ^ 2 * ((l * |w|) ^ 2 * K) := by
      rw [show (2 * π * w) ^ 2 = 4 * π ^ 2 * |w| ^ 2 by rw [mul_pow, sq_abs]; ring]; ring
    rw [h4] at e1
    have hX : 0 ≤ (l * |w|) ^ 2 * K := mul_nonneg (sq_nonneg _) hK_nn
    have hpi2 : 1 ≤ π ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 hpi2) hX]
  have : K * (1 + l * |w|) ^ 2 ≤ 2 * K + 2 * ((l * |w|) ^ 2 * K) := by
    nlinarith [sq_nonneg (1 - l * |w|)]
  nlinarith





theorem continuous_fourierInv_of_integrable' {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕⁻ f) := by
  have : (𝓕⁻ f : ℝ → ℂ) = VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ) f := by
    ext w
    rfl
  rw [this]
  refine VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar ?_ hf
  fun_prop



/-! ### Weights and Fourier support -/


theorem integrable_jb_rpow {L c : ℝ} (hL : 0 < L) {r : ℝ} (hr : 1 < r) :
    Integrable (fun x : ℝ => jb ((x - c) / L) ^ (-r)) := by
  have h0 : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-r)) :=
    integrable_one_add_norm (by simpa using hr)
  have h1 := (integrable_comp_mul_left_iff (fun x : ℝ => (1 + ‖x‖) ^ (-r)) (inv_ne_zero hL.ne')).2 h0
  have h2 := h1.comp_sub_right c
  refine h2.congr (Eventually.of_forall fun x => ?_)
  simp [jb, div_eq_inv_mul]

theorem integrable_pow_mul_jb {L c a : ℝ} (hL : 0 < L) {N : ℝ} (k : ℕ) (hN : (k : ℝ) + 1 < N)
    {C : ℝ} {f : ℝ → ℂ} (hf : Continuous f) (hfb : ∀ x, ‖f x‖ ≤ C * jb ((x - c) / L) ^ (-N)) :
    Integrable (fun x : ℝ => (((x - a) ^ k : ℝ) : ℂ) * f x) := by
  have hint := (integrable_jb_rpow (c := c) hL (r := N - k) (by linarith)).const_mul
    (|C| * (L + |c - a|) ^ k)
  refine hint.mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
  set t := (x - c) / L with ht
  have hjb := one_le_jb t
  have hxa : |x - a| ≤ (L + |c - a|) * jb t := by
    have h1 : |x - a| ≤ |x - c| + |c - a| := by
      have := abs_sub_le x c a; linarith
    have h2 : |x - c| = L * |t| := by
      rw [ht, abs_div, abs_of_pos hL]; field_simp
    unfold jb
    nlinarith [abs_nonneg t, abs_nonneg (c - a)]
  have hpw : |x - a| ^ k ≤ ((L + |c - a|) * jb t) ^ k :=
    pow_le_pow_left₀ (abs_nonneg _) hxa k
  have hjbpos : 0 < jb t := jb_pos t
  have e1 : jb t ^ k * jb t ^ (-N) = jb t ^ (-(N - k)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hjbpos]; congr 1; ring
  calc ‖(((x - a) ^ k : ℝ) : ℂ) * f x‖ = |x - a| ^ k * ‖f x‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow]
    _ ≤ ((L + |c - a|) * jb t) ^ k * (C * jb t ^ (-N)) :=
        mul_le_mul hpw (hfb x) (norm_nonneg _) (by positivity)
    _ ≤ ((L + |c - a|) * jb t) ^ k * (|C| * jb t ^ (-N)) := by
        gcongr; exact le_abs_self C
    _ = |C| * (L + |c - a|) ^ k * (jb t ^ k * jb t ^ (-N)) := by rw [mul_pow]; ring
    _ = _ := by rw [e1]

theorem fourier_const_mul' (c : ℂ) (f : ℝ → ℂ) (w : ℝ) :
    𝓕 (fun x => c * f x) w = c * 𝓕 f w := by
  simp only [Real.fourier_eq]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [Circle.smul_def]
  ring

theorem fourier_add' {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (w : ℝ) :
    𝓕 (fun x => f x + g x) w = 𝓕 f w + 𝓕 g w := by
  simp only [Real.fourier_eq, smul_add]
  exact integral_add ((Real.fourierIntegral_convergent_iff w).2 hf)
    ((Real.fourierIntegral_convergent_iff w).2 hg)

theorem fourier_sub_mul_eq_zero {f : ℝ → ℂ} (hf : Integrable f)
    (hxf : Integrable (fun x : ℝ => (x : ℂ) * f x)) (a ρ : ℝ)
    (h : ∀ ξ, ρ < |ξ| → 𝓕 f ξ = 0) :
    ∀ ξ, ρ < |ξ| → 𝓕 (fun x : ℝ => ((x - a : ℝ) : ℂ) * f x) ξ = 0 := by
  intro ξ hξ
  have hxf' : Integrable (fun x : ℝ => x • f x) := by
    simpa [Complex.real_smul] using hxf
  have hder := Real.deriv_fourier hf hxf'
  have h1 : (fun x : ℝ => ((x - a : ℝ) : ℂ) * f x) =
      fun x : ℝ => (x : ℂ) * f x + (-(a : ℂ)) * f x := by
    ext x; push_cast; ring
  rw [h1, fourier_add' hxf (hf.const_mul _), fourier_const_mul', h ξ hξ, mul_zero, add_zero]
  have hd : deriv (𝓕 f) ξ = 0 := by
    have hopen : IsOpen {ξ' : ℝ | ρ < |ξ'|} := isOpen_lt continuous_const (by fun_prop)
    have heq : 𝓕 f =ᶠ[𝓝 ξ] (fun _ => (0 : ℂ)) := by
      filter_upwards [hopen.mem_nhds hξ] with ξ' hξ' using h ξ' hξ'
    rw [heq.deriv_eq]; simp
  have h2 : deriv (𝓕 f) ξ = (-2 * π * Complex.I) * 𝓕 (fun x : ℝ => (x : ℂ) * f x) ξ := by
    rw [hder, ← fourier_const_mul']
    have : (fun x : ℝ => (-2 * π * Complex.I * x) • f x) =
        fun x : ℝ => (-2 * π * Complex.I) * ((x : ℂ) * f x) := by
      ext x; simp only [smul_eq_mul]; ring
    rw [this]
  rw [hd] at h2
  have hne : (-2 * (π : ℂ) * Complex.I) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    simp [this]
  exact (mul_eq_zero.1 h2.symm).resolve_left hne

theorem fourier_pow_mul_eq_zero {L c C N : ℝ} (hL : 0 < L) {ψ : ℝ → ℂ} (hψc : Continuous ψ)
    (hψ : ∀ x, ‖ψ x‖ ≤ C * jb ((x - c) / L) ^ (-N)) {ρ : ℝ}
    (h : ∀ ξ, ρ < |ξ| → 𝓕 ψ ξ = 0) (a : ℝ) :
    ∀ k : ℕ, (k : ℝ) + 1 < N → ∀ ξ, ρ < |ξ| →
      𝓕 (fun x : ℝ => (((x - a) ^ k : ℝ) : ℂ) * ψ x) ξ = 0 := by
  intro k
  induction k with
  | zero => intro _; simpa using h
  | succ k ih =>
    intro hk
    have hk' : (k : ℝ) + 1 < N := by push_cast at hk; linarith
    have hf : Integrable (fun x : ℝ => (((x - a) ^ k : ℝ) : ℂ) * ψ x) :=
      integrable_pow_mul_jb (c := c) (a := a) hL k hk' hψc hψ
    have hf1 : Integrable (fun x : ℝ => (((x - a) ^ (k + 1) : ℝ) : ℂ) * ψ x) :=
      integrable_pow_mul_jb (c := c) (a := a) hL (k + 1) hk hψc hψ
    have hxf : Integrable (fun x : ℝ => (x : ℂ) * ((((x - a) ^ k : ℝ) : ℂ) * ψ x)) := by
      have := hf1.add (hf.const_mul (a : ℂ))
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply]
      push_cast; ring
    have key := fourier_sub_mul_eq_zero hf hxf a ρ (ih hk')
    have e : (fun x : ℝ => (((x - a) ^ (k + 1) : ℝ) : ℂ) * ψ x) =
        fun x : ℝ => ((x - a : ℝ) : ℂ) * ((((x - a) ^ k : ℝ) : ℂ) * ψ x) := by
      ext x; push_cast; ring
    rw [e]
    exact key



end PrimeBHT.TimeFrequency.X2
