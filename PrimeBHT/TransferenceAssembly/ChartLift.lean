module

public import PrimeBHT.TransferenceAssembly.X2
public import PrimeBHT.Lift

/-!
# N41(b): the chart tensor is the lift (partial)

`chartPiece_eq_sum`: `h_A(x) = ∑_n h(n) e(-n A/N) N⁻¹ κ((x-n)/N)`, `κ(u) = ∫ χ(β) e(uβ) dβ`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate ContDiff

namespace PrimeBHT.TransferenceAssembly

open PrimeCarleson

variable {N : ℕ} [NeZero N] {χ : ℝ → ℂ}

/-- `κ(u) = ∫ χ(β) e(uβ) dβ`. -/
def chartKernel (χ : ℝ → ℂ) (u : ℝ) : ℂ := ∫ β, χ β * e (u * β)

theorem chartPiece_eq_sum (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (h : ℤ →₀ ℂ)
    (A : ZMod N) (x : ℝ) :
    chartPiece hχ hχc h A x = ∑ n ∈ h.support, h n * e (-(n * (A.val : ℝ) / N)) *
      ((N : ℂ)⁻¹ * chartKernel χ ((x - n) / N)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [chartPiece_apply]
  have hint : ∀ n ∈ h.support, Integrable fun α : ℝ =>
      h n * e (-(n * (A.val : ℝ) / N)) * (χ (N * α) * e ((x - n) * α)) := by
    intro n _
    refine Integrable.const_mul ?_ _
    have hc : Continuous fun α : ℝ => χ (N * α) * e ((x - n) * α) :=
      (hχ.continuous.comp (by fun_prop)).mul (contDiff_e.continuous.comp (by fun_prop))
    refine hc.integrable_of_hasCompactSupport ?_
    have : HasCompactSupport fun α : ℝ => χ (N * α) := by
      simpa [smul_eq_mul] using hχc.comp_smul hN.ne'
    exact this.mul_right
  have hpt : (fun α : ℝ => chartCoeffHat χ N h A α * e (x * α)) = fun α =>
      ∑ n ∈ h.support, h n * e (-(n * (A.val : ℝ) / N)) * (χ (N * α) * e ((x - n) * α)) := by
    funext α
    simp only [chartCoeffHat, seqFourier, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have h1 : e (-((n : ℝ) * (α + A.val / N))) * e (x * α) =
        e (-(n * (A.val : ℝ) / N)) * e ((x - n) * α) := by
      rw [← e_add, ← e_add]; congr 1; ring
    linear_combination (χ (N * α) * h n) * h1
  rw [hpt, integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul]
  congr 1
  unfold chartKernel
  have := Measure.integral_comp_mul_left (fun β : ℝ => χ β * e ((x - n) / N * β)) (N : ℝ)
  rw [show (fun α : ℝ => χ (N * α) * e ((x - n) * α)) =
      fun α : ℝ => χ (N * α) * e ((x - n) / N * (N * α)) from funext fun α => by
        congr 2; field_simp]
  rw [this, abs_of_pos (inv_pos.2 hN), Complex.real_smul]
  push_cast; ring

theorem e_neg_mul_val (n : ℤ) (A : ZMod N) :
    e (-(n * (A.val : ℝ) / N)) = ZMod.stdAddChar (A * (-(n : ZMod N))) := by
  have : A * (-(n : ZMod N)) = ((-(n * (A.val : ℤ)) : ℤ) : ZMod N) := by
    push_cast; simp; ring
  rw [this, ZMod.stdAddChar_coe]
  unfold e
  congr 1
  push_cast
  ring

/-- **N41(b)**: the chart tensor `∑_A h_A(x) e(Ay/N)` is the lift `∑_{n ≡ y} h(n) κ((x-n)/N)`. -/
theorem tensorFun_chartPiece_eq_lift (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (h : ℤ →₀ ℂ) (x : ℝ) (y : ZMod N) :
    tensorFun (chartPiece hχ hχc h) x y = Lift.lift (chartKernel χ) N h x y := by
  classical
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  unfold tensorFun Lift.lift
  simp_rw [chartPiece_eq_sum, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  have horth : ∑ A : ZMod N, (ZMod.stdAddChar (A * (y - (n : ZMod N))) : ℂ) =
      if (n : ZMod N) = y then (N : ℂ) else 0 := by
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N), ZMod.card]
    by_cases hy : (n : ZMod N) = y
    · rw [ite_eq_left hy, ite_eq_left (by rw [hy, sub_self])]
    · rw [ite_eq_right hy, ite_eq_right (fun h0 => hy (sub_eq_zero.1 h0).symm)]; simp
  have hterm : ∀ A : ZMod N, h n * e (-(n * (A.val : ℝ) / N)) *
      ((N : ℂ)⁻¹ * chartKernel χ ((x - n) / N)) * ZMod.stdAddChar (A * y) =
      (h n * ((N : ℂ)⁻¹ * chartKernel χ ((x - n) / N))) * ZMod.stdAddChar (A * (y - (n : ZMod N))) := by
    intro A
    have hA : A * (y - (n : ZMod N)) = A * y + A * (-(n : ZMod N)) := by ring
    rw [e_neg_mul_val, hA, AddChar.map_add_eq_mul]
    ring
  simp_rw [hterm, ← Finset.mul_sum, horth]
  split_ifs
  · field_simp
  · simp

/-- `κ = 𝓕⁻ χ` as a Schwartz function. -/
def chartKernelSchwartz (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) : 𝓢(ℝ, ℂ) :=
  𝓕⁻ (hχc.toSchwartzMap hχ)

theorem chartKernelSchwartz_apply (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (u : ℝ) :
    chartKernelSchwartz hχ hχc u = chartKernel χ u := by
  rw [chartKernelSchwartz, SchwartzMap.fourierInv_coe, Real.fourierInv_eq', chartKernel]
  refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
  simp only [smul_eq_mul, e, RCLike.inner_apply, conj_trivial]
  rw [mul_comm]
  change χ β * _ = _
  congr 2
  push_cast
  ring

theorem chartKernel_eq (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    chartKernel χ = ⇑(chartKernelSchwartz hχ hχc) :=
  funext fun u => (chartKernelSchwartz_apply hχ hχc u).symm

theorem measurable_chartKernel (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    Measurable (chartKernel χ) := by
  rw [chartKernel_eq hχ hχc]; exact (chartKernelSchwartz hχ hχc).continuous.measurable

theorem integrable_chartKernel (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    Integrable (chartKernel χ) := by
  rw [chartKernel_eq hχ hχc]; exact (chartKernelSchwartz hχ hχc).integrable

theorem summable_chartKernel_sub (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (t : ℝ) :
    Summable fun j : ℤ => ‖chartKernel χ (t - j)‖ := by
  let g : 𝓢(ℝ, ℂ) := SchwartzMap.compSubConstCLM ℂ t
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv
      (chartKernelSchwartz hχ hχc))
  have hg : ∀ x : ℝ, g x = chartKernel χ (t - x) := by
    intro x
    simp only [g, SchwartzMap.compSubConstCLM_apply]
    rw [← chartKernelSchwartz_apply hχ hχc]
    change chartKernelSchwartz hχ hχc (-(x - t)) = _
    congr 1; ring
  have := Transference.summable_norm_schwartz_int g
  simpa only [hg] using this

end PrimeBHT.TransferenceAssembly
