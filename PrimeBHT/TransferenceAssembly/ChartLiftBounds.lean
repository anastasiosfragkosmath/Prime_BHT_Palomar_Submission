module

public import PrimeBHT.TransferenceAssembly.ChartLift
public import PrimeBHT.Lift

/-!
# S27: uniform bounds for the chart kernel, and X2 / lift norm conversion

(a) `∃ C, ∀ t, ∑' j, ‖chartKernel χ (t - j)‖ ≤ C`.
(b) `eLpNorm (x ↦ yNorm s (F x)) 2 = ofReal (mixedNormR 2 s F)`, and the `p = ⊤` bound.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff ENNReal

namespace PrimeBHT.TransferenceAssembly

open PrimeBHT.Lift

/-- Schwartz decay `‖K x‖ (1 + |x|)^2 ≤ M`. -/
theorem schwartz_decay_two (K : 𝓢(ℝ, ℂ)) : ∃ M : ℝ, ∀ x : ℝ, ‖K x‖ * (1 + |x|) ^ 2 ≤ M := by
  refine ⟨2 ^ (2 : ℕ × ℕ).1 * (Finset.Iic ((2 : ℕ), (0 : ℕ))).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) K, fun x => ?_⟩
  have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((2 : ℕ), (0 : ℕ)))
    (k := 2) (n := 0) le_rfl le_rfl K x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  simpa [mul_comm] using this

theorem summable_one_div_one_add_abs_sq :
    Summable fun i : ℤ => 1 / (1 + |(i : ℝ)|) ^ 2 := by
  have h1 : Summable fun n : ℕ => 1 / (1 + |(n : ℝ)|) ^ 2 := by
    have := (Real.summable_one_div_nat_add_rpow 1 2).2 one_lt_two
    refine this.congr fun n => ?_
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), add_comm]
    norm_cast
  refine Summable.of_nat_of_neg h1 ?_
  simpa using h1

theorem one_add_abs_sub_ge (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (i : ℤ) :
    (1 + |(i : ℝ)|) / 2 ≤ 1 + |s - i| := by
  have h1 : |(i : ℝ)| ≤ |s - i| + 1 := by
    have : |(i : ℝ)| ≤ |s - i| + |s| := by
      calc |(i : ℝ)| = |-(s - i) + s| := by congr 1; ring
        _ ≤ |-(s - i)| + |s| := abs_add_le _ _
        _ = |s - i| + |s| := by rw [abs_neg]
    rw [abs_of_nonneg hs0] at this
    linarith
  have := abs_nonneg (s - i)
  linarith

theorem tsum_chartKernel_sub_le_aux (K : ℝ → ℂ) (M : ℝ) (hK : ∀ x : ℝ, ‖K x‖ * (1 + |x|) ^ 2 ≤ M)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Summable (fun i : ℤ => ‖K (s - i)‖) ∧
      ∑' i : ℤ, ‖K (s - i)‖ ≤ 4 * M * ∑' i : ℤ, 1 / (1 + |(i : ℝ)|) ^ 2 := by
  have hbd : ∀ i : ℤ, ‖K (s - i)‖ ≤ 4 * M * (1 / (1 + |(i : ℝ)|) ^ 2) := by
    intro i
    have hp : 0 < (1 + |s - i|) := by positivity
    have hq : 0 < (1 + |(i : ℝ)|) := by positivity
    have h2 := one_add_abs_sub_ge s hs0 hs1 i
    have h3 := hK (s - i)
    have hM : 0 ≤ M := le_trans (by positivity) h3
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    have h4 : (1 + |(i : ℝ)|) ^ 2 ≤ 4 * (1 + |s - i|) ^ 2 := by nlinarith
    calc ‖K (s - i)‖ * (1 + |(i : ℝ)|) ^ 2 ≤ ‖K (s - i)‖ * (4 * (1 + |s - i|) ^ 2) :=
          mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
      _ = 4 * (‖K (s - i)‖ * (1 + |s - i|) ^ 2) := by ring
      _ ≤ 4 * M := by linarith
  have hsum := (summable_one_div_one_add_abs_sq.mul_left (4 * M))
  have hs : Summable (fun i : ℤ => ‖K (s - i)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbd hsum
  refine ⟨hs, ?_⟩
  calc ∑' i : ℤ, ‖K (s - i)‖ ≤ ∑' i : ℤ, 4 * M * (1 / (1 + |(i : ℝ)|) ^ 2) :=
        hs.tsum_le_tsum hbd hsum
    _ = 4 * M * ∑' i : ℤ, 1 / (1 + |(i : ℝ)|) ^ 2 := tsum_mul_left

/-- **(a)** Uniform bound of the chart kernel: `sup_t ∑_j ‖κ(t - j)‖ < ∞`. -/
theorem exists_tsum_chartKernel_sub_le {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) : ∃ C : ℝ, ∀ t : ℝ, ∑' j : ℤ, ‖chartKernel χ (t - j)‖ ≤ C := by
  obtain ⟨M, hM⟩ := schwartz_decay_two (chartKernelSchwartz hχ hχc)
  have hK : ∀ x : ℝ, ‖chartKernel χ x‖ * (1 + |x|) ^ 2 ≤ M := by
    intro x; rw [chartKernel_eq hχ hχc]; exact hM x
  refine ⟨4 * M * ∑' i : ℤ, 1 / (1 + |(i : ℝ)|) ^ 2, fun t => ?_⟩
  set j₀ : ℤ := ⌊t⌋ with hj₀
  have hs0 : 0 ≤ t - j₀ := sub_nonneg.2 (Int.floor_le t)
  have hs1 : t - j₀ ≤ 1 := by have := Int.lt_floor_add_one t; rw [hj₀]; linarith
  rw [← (Equiv.addLeft j₀).tsum_eq]
  have : ∀ i : ℤ, ‖chartKernel χ (t - ((Equiv.addLeft j₀ i : ℤ) : ℝ))‖ =
      ‖chartKernel χ ((t - j₀) - i)‖ := by
    intro i; simp only [Equiv.coe_addLeft]; push_cast; congr 2; ring
  simp_rw [this]
  exact (tsum_chartKernel_sub_le_aux _ M hK _ hs0 hs1).2


/-! ## (a-discrete) the Riemann-sum bound -/

/-! ## (b) conversion between `eLpNorm` and the mixed norm -/

variable {P : ℕ} [NeZero P]

/-- **(b), `p = 2`**: the `eLpNorm` of the fibre norm equals the real mixed norm. -/
theorem eLpNorm_yNorm_two_eq (s : ℝ) (F : ℝ → ZMod P → ℂ)
    (hm : AEStronglyMeasurable (fun x => yNorm s (F x)) volume)
    (hi : Integrable (fun x => yNorm s (F x) ^ (2 : ℝ)) volume) :
    eLpNorm (fun x => yNorm s (F x)) 2 volume = ENNReal.ofReal (mixedNormR 2 s F) := by
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm, h2, mixedNormR]
  have hnn : ∀ x, 0 ≤ yNorm s (F x) := fun x => yNorm_nonneg s (F x)
  have hpt : ∀ x, ‖yNorm s (F x)‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (yNorm s (F x) ^ (2 : ℝ)) := by
    intro x
    rw [Real.enorm_eq_ofReal (hnn x), ENNReal.ofReal_rpow_of_nonneg (hnn x) (by norm_num)]
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hnn x) _),
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun x => Real.rpow_nonneg (hnn x) _)
      (by norm_num)]
  norm_num

/-- **(b), `p = ⊤`**: a uniform bound on the fibre norms bounds the `L^∞` norm. -/
theorem eLpNorm_yNorm_top_le (s : ℝ) (F : ℝ → ZMod P → ℂ) {M : ℝ}
    (hm : AEStronglyMeasurable (fun x => yNorm s (F x)) volume)
    (hM : ∀ x, yNorm s (F x) ≤ M) :
    eLpNorm (fun x => yNorm s (F x)) ⊤ volume ≤ ENNReal.ofReal M := by
  rw [eLpNorm_exponent_top hm]
  refine eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (yNorm_nonneg s _)]
  exact hM x

end PrimeBHT.TransferenceAssembly
