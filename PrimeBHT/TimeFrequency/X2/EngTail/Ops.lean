module

public import PrimeBHT.TimeFrequency.X2.EngTail.TreeStrong
public import PrimeBHT.TimeFrequency.X2.EngTail.Decomp
public import PrimeBHT.TimeFrequency.X2.EngTail.Cover

/-!
# X2, node B5: operator-level tools for the induction

* `integrable_tileKernel_mul`: `z ↦ K_S(x, z) g(z)` is integrable for bounded measurable `g`;
* `yNorm_kernelOp_le`: `‖∫ K(x, z) G(z) dz‖_X ≤ ∫ w` if `‖K(x, z)‖ ‖G(z)‖_X ≤ w(z)` (Minkowski);
* `Lq`: the `L^q` norm of an `ℝ≥0∞`-valued function, with its triangle inequality and the `famPhi` bounds.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

section Integrability

variable {ι : Type*}

/-- `z ↦ K_S(x, z) g(z)` is integrable for bounded measurable `g`. -/
theorem integrable_tileKernel_mul {N M Cφ Cκ : ℝ} (hM : 1 < M) (S : Finset ι) (j v : ι → ℤ) (φ κ : ι → ℝ → ℂ)
    (hb : ∀ i ∈ S, TileBound N M Cφ Cκ (j i) (v i) (φ i) (κ i)) {g : ℝ → ℂ} (hg : Measurable g) {B : ℝ}
    (hgb : ∀ z, ‖g z‖ ≤ B) (x : ℝ) : Integrable (fun z => tileKernel S φ κ x z * g z) := by
  unfold tileKernel
  simp_rw [Finset.sum_mul]
  refine integrable_finsetSum _ fun i hi => ?_
  have hL : (0 : ℝ) < (2 : ℝ) ^ (j i) := zpow_pos (by norm_num) _
  have := integrable_kernel_mul (κ := κ i) (hb i hi).κ_diff.continuous hM hL (hb i hi).κ_le hg hgb x
  exact (this.const_mul (φ i x)).congr (Eventually.of_forall fun z => by simp only [mul_assoc])

end Integrability

section Minkowski

variable {P : ℕ} [NeZero P]

/-- `‖∫ K(x, z) G(z) dz‖_X ≤ ∫ w` if `‖K(x, z)‖ ‖G(z)‖_X ≤ w(z)`. -/
theorem yNorm_kernelOp_le {s : ℝ} (hs : 1 < s) {K : ℝ → ℝ → ℂ} (hKm : Measurable (Function.uncurry K))
    {G : ℝ → ZMod P → ℂ} (hGm : ∀ y, Measurable fun z => G z y) {w : ℝ → ℝ} (hw : Integrable w) (x : ℝ)
    (hle : ∀ z, ‖K x z‖ * yNorm s (G z) ≤ w z) :
    yNorm s (fun y => ∫ z, K x z * G z y) ≤ ∫ z, w z := by
  have hs0 : 0 < s := by linarith
  have hKx : Measurable fun z => K x z := hKm.comp (measurable_const.prodMk measurable_id)
  have hVm : ∀ y, Measurable fun z => K x z * G z y := fun y => hKx.mul (hGm y)
  have hVn : ∀ z, yNorm s (fun y => K x z * G z y) = ‖K x z‖ * yNorm s (G z) := fun z =>
    yNorm_fun_const_mul hs0 (K x z) (G z)
  have hP0 : (0 : ℝ) ≤ (P : ℝ) ^ s⁻¹ := by positivity
  have hV : ∀ y, Integrable (fun z => K x z * G z y) := by
    intro y
    refine Integrable.mono' (hw.const_mul ((P : ℝ) ^ s⁻¹)) (hVm y).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    calc ‖K x z‖ * ‖G z y‖ ≤ ‖K x z‖ * ((P : ℝ) ^ s⁻¹ * yNorm s (G z)) :=
          mul_le_mul_of_nonneg_left (norm_apply_le_rpow_mul_yNorm hs0 (G z) y) (norm_nonneg _)
      _ = (P : ℝ) ^ s⁻¹ * (‖K x z‖ * yNorm s (G z)) := by ring
      _ ≤ (P : ℝ) ^ s⁻¹ * w z := mul_le_mul_of_nonneg_left (hle z) hP0
  have hnm : Measurable fun z => yNorm s (fun y => K x z * G z y) := CZ.measurable_yNorm s hVm
  have hn : Integrable (fun z => yNorm s (fun y => K x z * G z y)) := by
    refine Integrable.mono' hw hnm.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (CZ.yNorm_nonneg s _), hVn z]
    exact hle z
  have h1 := CZ.yNorm_integral_le hs (fun z y => K x z * G z y) hV hn
  refine h1.trans ?_
  refine integral_mono hn hw fun z => ?_
  rw [hVn z]; exact hle z

end Minkowski

section Lq

/-- The `L^q` norm of an `ℝ≥0∞`-valued function: `(∫⁻ f^q)^{1/q}`. -/
def Lq (q : ℝ) (f : ℝ → ℝ≥0∞) : ℝ≥0∞ := (∫⁻ x, f x ^ q) ^ (1 / q)

theorem Lq_mono {q : ℝ} (hq : 0 < q) {f g : ℝ → ℝ≥0∞} (h : ∀ x, f x ≤ g x) : Lq q f ≤ Lq q g := by
  unfold Lq
  exact ENNReal.rpow_le_rpow (lintegral_mono fun x => ENNReal.rpow_le_rpow (h x) hq.le)
    (by positivity)

theorem Lq_add_le {q : ℝ} (hq : 1 ≤ q) {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    Lq q (fun x => f x + g x) ≤ Lq q f + Lq q g :=
  ENNReal.lintegral_Lp_add_le hf.aemeasurable hg.aemeasurable hq

theorem Lq_zero {q : ℝ} (hq : 0 < q) : Lq q (fun _ => 0) = 0 := by
  unfold Lq
  simp [ENNReal.zero_rpow_of_pos hq, hq]

/-- `Lq` of a function bounded by a constant multiple of `famPhi`. -/
theorem Lq_famPhi_le {ι : Type*} {q : ℝ} (hq : 1 < q) (F : Finset ι) (c ℓ : ι → ℝ) {α : ℝ} (hα : 0 ≤ α)
    (hℓ : ∀ i, 0 < ℓ i)
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      Disjoint (Ico (c i - ℓ i / 2) (c i + ℓ i / 2)) (Ico (c j - ℓ j / 2) (c j + ℓ j / 2))) :
    Lq q (famPhi c ℓ (fun _ => α) F) ≤
      famConst q * ENNReal.ofReal α * ENNReal.ofReal (∑ i ∈ F, ℓ i) ^ (1 / q) := by
  have hq0 : 0 < q := by linarith
  have h := famPhi_norm_le (c := c) (ℓ := ℓ) (a := fun _ => α) hq hℓ (fun _ => hα) F hdisj
  unfold Lq
  refine h.trans (le_of_eq ?_)
  have e : ∑ i ∈ F, ENNReal.ofReal α ^ q * ENNReal.ofReal (ℓ i) =
      ENNReal.ofReal α ^ q * ENNReal.ofReal (∑ i ∈ F, ℓ i) := by
    rw [← Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun i _ => (hℓ i).le)]
  rw [e, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne',
    ENNReal.rpow_one, mul_assoc]

end Lq

end PrimeBHT.TimeFrequency.X2
