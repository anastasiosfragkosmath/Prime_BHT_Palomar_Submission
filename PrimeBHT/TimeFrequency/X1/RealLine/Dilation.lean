module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import PrimeBHT.Frozen.IsCutoff
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Real-line dilation covariance (blueprint node R1, `docs/x1-blueprint.md` section 4)

Notation: `D_s f := fun x => f (s * x)`, `B_t(φ, f, g)(x) = ∫ f(x - y) g(x + y) t⁻¹ φ(y / t) dy`
(`dilAvg φ t f g x`), and `K_{λ,μ}(y) = (χ(λ y) - χ(μ y)) / y` (`bhtKernelR`), `T_K = bhtOpR`.

* (a) `dilAvg_dilate`: `B_t(φ, D_s f, D_s g)(x) = B_{t s}(φ, f, g)(s x)` for `s, t > 0`.
* (b) `bhtOpR_dilate`: `T_{K_{λ,μ}}(D_s f, D_s g)(x) = T_{K_{λ/s, μ/s}}(f, g)(s x)`, through the kernel identity
  `bhtKernelR_dilate`: `K_{λ,μ}(y / s) / s = K_{λ/s, μ/s}(y)`. Integrability is NOT assumed: both sides are the
  same Bochner integral after the change of variables (`integral_dilate`).
* (c) `eLpNorm_comp_mul_left`: `‖h(s ·)‖_{L^r} = s^{-1/r} ‖h‖_{L^r}` for every function `h` and every exponent
  (no measurability needed), and `bhtOpR_bound_dilate_iff`: the `L^p × L^q → L^r` bound for all Schwartz
  `f, g` at `(λ, μ)` is equivalent to the one at `(λ/s, μ/s)` with the same constant, when `1/r = 1/p + 1/q`.

The definitions `bhtKernelR` and `bhtOpR` mirror `drafts/M2Statement.lean.txt`, which is under independent
audit and not frozen; they are to be identified with the frozen definitions once M2 is approved.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PrimeBHT.TimeFrequency.RealLine

/-! ## Definitions -/

/-- mirror of drafts/M2Statement.lean.txt; to be identified with the frozen definition once M2 is approved.
The real-line smooth-truncation kernel `K_{λ,μ}(y) = (χ(λy) - χ(μy)) / y`. -/
def bhtKernelR (χ : ℝ → ℝ) (lam mu : ℝ) (y : ℝ) : ℝ := (χ (lam * y) - χ (mu * y)) / y

/-- mirror of drafts/M2Statement.lean.txt; to be identified with the frozen definition once M2 is approved.
The real-line bilinear operator `∫ f(x - y) g(x + y) K_{λ,μ}(y) dy` (Bochner integral). -/
def bhtOpR (χ : ℝ → ℝ) (lam mu : ℝ) (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, f (x - y) * g (x + y) * (bhtKernelR χ lam mu y : ℂ)

/-- The dilated average `B_t(φ, f, g)(x) = ∫ f(x - y) g(x + y) t⁻¹ φ(y / t) dy` of the blueprint (BD26 L136),
for a real profile `φ : ℝ → ℝ` and a scale `t` (meant to be `t > 0`). It is the Bochner integral. -/
def dilAvg (φ : ℝ → ℝ) (t : ℝ) (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, f (x - y) * g (x + y) * ((t⁻¹ * φ (y / t) : ℝ) : ℂ)

/-! ## The change of variables -/

/-- **Change of variables** (no integrability hypothesis; for `s > 0`):
`∫ f(s(x-y)) g(s(x+y)) k(y) dy = ∫ f(sx - u) g(sx + u) s⁻¹ k(u/s) du`. -/
theorem integral_dilate {s : ℝ} (hs : 0 < s) (f g k : ℝ → ℂ) (x : ℝ) :
    ∫ y, f (s * (x - y)) * g (s * (x + y)) * k y =
      ∫ u, f (s * x - u) * g (s * x + u) * ((s⁻¹ : ℝ) * k (u / s)) := by
  have hs0 : s ≠ 0 := hs.ne'
  have h1 : ∀ y : ℝ, f (s * (x - y)) * g (s * (x + y)) * k y =
      (fun u : ℝ => f (s * x - u) * g (s * x + u) * k (u / s)) (s * y) := by
    intro y
    simp only [mul_sub, mul_add, mul_div_cancel_left₀ _ hs0]
  simp_rw [h1]
  rw [Measure.integral_comp_mul_left (fun u : ℝ => f (s * x - u) * g (s * x + u) * k (u / s)) s,
    abs_of_pos (inv_pos.2 hs), ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [Complex.real_smul]
  ring

/-! ## R1 (a): dilated averages -/

/-! ## R1 (b): the truncated kernel and operator -/

/-- The kernel is real-line dilation covariant: `K_{λ,μ}(y / s) / s = K_{λ/s, μ/s}(y)` for `s ≠ 0`
(that is, `K^{(s)}_{λ,μ} = K_{λ/s, μ/s}` with `K^{(s)}(y) := K(y / s) / s`). -/
theorem bhtKernelR_dilate (χ : ℝ → ℝ) (lam mu : ℝ) {s : ℝ} (hs : s ≠ 0) (y : ℝ) :
    bhtKernelR χ lam mu (y / s) / s = bhtKernelR χ (lam / s) (mu / s) y := by
  have h1 : lam * (y / s) = lam / s * y := by ring
  have h2 : mu * (y / s) = mu / s * y := by ring
  simp only [bhtKernelR, h1, h2]
  rw [div_div, div_mul_cancel₀ y hs]

/-- **R1 (b).** `T_{K_{λ,μ}}(D_s f, D_s g)(x) = T_{K_{λ/s, μ/s}}(f, g)(s x)` for `s > 0`, with no
integrability hypothesis (when the integrand is not integrable both sides are `0`). -/
theorem bhtOpR_dilate (χ : ℝ → ℝ) (lam mu : ℝ) {s : ℝ} (hs : 0 < s) (f g : ℝ → ℂ) (x : ℝ) :
    bhtOpR χ lam mu (fun u => f (s * u)) (fun u => g (s * u)) x =
      bhtOpR χ (lam / s) (mu / s) f g (s * x) := by
  unfold bhtOpR
  rw [integral_dilate hs f g (fun y => (bhtKernelR χ lam mu y : ℂ)) x]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [← bhtKernelR_dilate χ lam mu hs.ne' u, Complex.ofReal_div, div_eq_inv_mul]
  push_cast
  ring

/-! ## R1 (c): scaling of the `L^r` norm -/

/-- **R1 (c), scaling of `eLpNorm`.** For `s > 0`, every function `h` and every exponent `r`
(no measurability assumption: both sides are `⊤` together for non a.e. strongly measurable `h`),
`‖h(s ·)‖_{L^r} = s^{-1/r} ‖h‖_{L^r}`. -/
theorem eLpNorm_comp_mul_left {E : Type*} [NormedAddCommGroup E] (h : ℝ → E) {s : ℝ} (hs : 0 < s)
    (r : ℝ≥0∞) :
    eLpNorm (fun x => h (s * x)) r volume =
      ENNReal.ofReal s⁻¹ ^ (1 / r).toReal * eLpNorm h r volume := by
  have hme : MeasurableEmbedding (fun x : ℝ => s * x) := measurableEmbedding_mulLeft₀ hs.ne'
  have h1 := hme.eLpNorm_map_measure (g := h) (p := r) (μ := volume)
  rw [Real.map_volume_mul_left hs.ne', abs_of_pos (inv_pos.2 hs),
    eLpNorm_smul_measure_of_ne_zero (by simp [hs]) h r volume] at h1
  exact h1.symm

/-- **R1 (c), real exponents.** `‖h(s ·)‖_{L^r} = s^{-1/r} ‖h‖_{L^r}` for real `r > 0`, `s > 0`, written
with `ENNReal.ofReal r`. -/
theorem eLpNorm_comp_mul_left_ofReal {E : Type*} [NormedAddCommGroup E] (h : ℝ → E) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) :
    eLpNorm (fun x => h (s * x)) (ENNReal.ofReal r) volume =
      ENNReal.ofReal (s ^ (-(1 / r))) * eLpNorm h (ENNReal.ofReal r) volume := by
  rw [eLpNorm_comp_mul_left h hs, one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hr.le,
    ENNReal.ofReal_rpow_of_nonneg (inv_pos.2 hs).le (inv_nonneg.2 hr.le), Real.inv_rpow hs.le,
    Real.rpow_neg hs.le, one_div]

/-- The dilate `u ↦ f(s u)` of a Schwartz function is Schwartz (`s > 0`). -/
theorem exists_schwartz_dilate (f : SchwartzMap ℝ ℂ) {s : ℝ} (hs : 0 < s) :
    ∃ f' : SchwartzMap ℝ ℂ, ∀ u, f' u = f (s * u) :=
  ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 s hs.ne')) f, fun _ => rfl⟩

/-- **R1 (c), one direction.** If the bound `‖T_{K_{λ,μ}}(f, g)‖_r ≤ C ‖f‖_p ‖g‖_q` holds for all Schwartz
`f, g` at `(λ, μ)`, it holds at `(λ/s, μ/s)` with the same `C` (`s > 0`, `1/r = 1/p + 1/q`): the scaling
factor is `s^{-1/r}` on the left and `s^{-1/p - 1/q} = s^{-1/r}` on the right. No hypothesis on `χ` or on
`λ, μ` is needed. -/
theorem bhtOpR_bound_dilate (χ : ℝ → ℝ) (lam mu : ℝ) {s : ℝ} (hs : 0 < s) {p q r C : ℝ} (hp : 0 < p)
    (hq : 0 < q) (hr : 0 < r) (hpqr : 1 / r = 1 / p + 1 / q)
    (h : ∀ f g : SchwartzMap ℝ ℂ,
      eLpNorm (bhtOpR χ lam mu f g) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume *
          eLpNorm g (ENNReal.ofReal q) volume) :
    ∀ f g : SchwartzMap ℝ ℂ,
      eLpNorm (bhtOpR χ (lam / s) (mu / s) f g) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume *
          eLpNorm g (ENNReal.ofReal q) volume := by
  intro f g
  obtain ⟨f', hf'⟩ := exists_schwartz_dilate f hs
  obtain ⟨g', hg'⟩ := exists_schwartz_dilate g hs
  have hf'' : (⇑f' : ℝ → ℂ) = fun u => f (s * u) := funext hf'
  have hg'' : (⇑g' : ℝ → ℂ) = fun u => g (s * u) := funext hg'
  have hFt : (fun u => bhtOpR χ (lam / s) (mu / s) f g (s * u)) = bhtOpR χ lam mu f' g' := by
    funext u
    rw [← bhtOpR_dilate χ lam mu hs f g u, hf'', hg'']
  have h1 := h f' g'
  rw [← hFt, eLpNorm_comp_mul_left_ofReal _ hs hr, hf'', hg'',
    eLpNorm_comp_mul_left_ofReal _ hs hp, eLpNorm_comp_mul_left_ofReal _ hs hq] at h1
  have hA : ENNReal.ofReal (s ^ (-(1 / r))) =
      ENNReal.ofReal (s ^ (-(1 / p))) * ENNReal.ofReal (s ^ (-(1 / q))) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hs, hpqr, neg_add]
  rw [hA] at h1
  have h0 : ENNReal.ofReal (s ^ (-(1 / p))) * ENNReal.ofReal (s ^ (-(1 / q))) ≠ 0 := by
    apply mul_ne_zero <;> (rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity)
  have htop : ENNReal.ofReal (s ^ (-(1 / p))) * ENNReal.ofReal (s ^ (-(1 / q))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  refine (ENNReal.mul_le_mul_iff_right h0 htop).1 ?_
  refine h1.trans (le_of_eq ?_)
  ring

/-- **R1 (c).** The bound `‖T_{K_{λ,μ}}(f, g)‖_r ≤ C ‖f‖_p ‖g‖_q` for all Schwartz `f, g` is equivalent at
`(λ, μ)` and at `(λ/s, μ/s)` (`s > 0`) with the same `C`, when `1/r = 1/p + 1/q`. -/
theorem bhtOpR_bound_dilate_iff (χ : ℝ → ℝ) (lam mu : ℝ) {s : ℝ} (hs : 0 < s) {p q r C : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hpqr : 1 / r = 1 / p + 1 / q) :
    (∀ f g : SchwartzMap ℝ ℂ,
      eLpNorm (bhtOpR χ lam mu f g) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume *
          eLpNorm g (ENNReal.ofReal q) volume) ↔
    (∀ f g : SchwartzMap ℝ ℂ,
      eLpNorm (bhtOpR χ (lam / s) (mu / s) f g) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume *
          eLpNorm g (ENNReal.ofReal q) volume) := by
  refine ⟨bhtOpR_bound_dilate χ lam mu hs hp hq hr hpqr, fun h => ?_⟩
  have h' := bhtOpR_bound_dilate χ (lam / s) (mu / s) (inv_pos.2 hs) hp hq hr hpqr h
  have e1 : lam / s / s⁻¹ = lam := by field_simp
  have e2 : mu / s / s⁻¹ = mu := by field_simp
  rwa [e1, e2] at h'

end PrimeBHT.TimeFrequency.RealLine

end
