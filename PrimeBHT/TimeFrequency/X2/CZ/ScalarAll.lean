module

public import PrimeBHT.TimeFrequency.X2.CZ.AdjointMult

/-!
# V08 phase 3: the scalar bound `TruncScalarStrong s A` for every `s > 1`

For `1 < s ≤ 2` this is `exists_truncScalarStrong_le_two`.  For `s > 2` the adjoint of the normalized truncated
kernel of `σ` is the normalized truncated kernel of `conj σ` (again Mikhlin, same `B`), the strong
`(s', s')` bound, `s' = s/(s-1) < 2`, holds for it, and duality (`kStrong_of_adjoint`) transfers it back.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology Real ComplexConjugate

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

open PrimeBHT.Statements

/-- The scalar bound (`P = 1`) in `eLpNorm` form from `KStrong 1`. -/
theorem eLpNorm_kop_le_of_kStrong_one {K : ℝ → ℝ → ℂ} {s A : ℝ} (hs : 0 < s) (_hA : 0 ≤ A)
    (hK : KStrong 1 K s s A) {h : ℝ → ℂ} (hm : Measurable h) (hi : Integrable h volume)
    (hb : ∃ C, ∀ u, ‖h u‖ ≤ C) (hKm : Measurable (Function.uncurry K)) :
    eLpNorm (kop K h) (ENNReal.ofReal s) volume ≤ ENNReal.ofReal A * eLpNorm h (ENNReal.ofReal s) volume := by
  have h1 := hK (fun u _ => h u) ⟨fun _ => hm, fun _ => hi, fun _ => hb⟩
  simp only [yNorm_zmod_one hs, ofReal_norm] at h1
  have hm1 : AEStronglyMeasurable (kop K h) volume := (measurable_kop hKm hm).aestronglyMeasurable
  rw [lintegral_enorm_rpow_eq hs hm1, lintegral_enorm_rpow_eq hs hm.aestronglyMeasurable,
    ← ENNReal.mul_rpow_of_nonneg _ _ hs.le] at h1
  exact (ENNReal.rpow_le_rpow_iff hs).1 h1

/-- The `TruncScalarStrong` hypothesis from `KStrong 1` of the normalized truncated kernels. -/
theorem truncScalarStrong_of_kStrong_one {s A : ℝ} (hs : 0 < s) (hA : 0 ≤ A)
    (hK : ∀ (B : ℝ) (σ : ℝ → ℂ), IsMikhlin 3 B σ → 0 < B → ∀ N : ℕ, KStrong 1 (normKernel σ B N) s s A) :
    TruncScalarStrong s A := by
  intro B σ hσ N h hm hi hb
  have hB0 := hσ.nonneg
  rcases hB0.eq_or_lt with hB | hB
  · subst hB
    have : kconv (kernelTrunc σ N) h = fun _ => 0 := by
      ext x; simp [kconv, kop, kernelTrunc_eq_zero_of_B_zero hσ N]
    rw [this]; simp
  · have hK_eLp := eLpNorm_kop_le_of_kStrong_one hs hA (hK B σ hσ hB N) hm hi hb (measurable_normKernel hσ N)
    have hkc : kconv (kernelTrunc σ N) h = (B : ℂ) • kop (normKernel σ B N) h := by
      ext x
      rw [Pi.smul_apply, kop_normKernel hB]
      have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
      simp [smul_eq_mul, hBc]
    rw [hkc, eLpNorm_const_smul]
    have : ‖(B : ℂ)‖ₑ = ENNReal.ofReal B := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
    rw [this]
    calc ENNReal.ofReal B * eLpNorm (kop (normKernel σ B N) h) (ENNReal.ofReal s) volume
        ≤ ENNReal.ofReal B * (ENNReal.ofReal A * eLpNorm h (ENNReal.ofReal s) volume) :=
          mul_le_mul' le_rfl hK_eLp
      _ = ENNReal.ofReal (A * B) * eLpNorm h (ENNReal.ofReal s) volume := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hB.le, mul_comm B]

theorem conjExponent_mem_Ioo {s : ℝ} (hs : 2 < s) :
    1 < Real.conjExponent s ∧ Real.conjExponent s < 2 := by
  have h1 : 0 < s - 1 := by linarith
  unfold Real.conjExponent
  constructor
  · rw [lt_div_iff₀ h1]; linarith
  · rw [div_lt_iff₀ h1]; linarith

/-- The `KStrong 1` bound of the normalized truncated kernels at an exponent `1 < s < 2`. -/
theorem kStrong_one_normKernel_lt_two {s : ℝ} (hs : 1 < s) (hs2 : s < 2) (P : ℕ) [NeZero P] {B : ℝ}
    {σ : ℝ → ℂ} (hσ : IsMikhlin 3 B σ) (hB : 0 < B) (N : ℕ) :
    KStrong P (normKernel σ B N) s s (marcConst s ^ s⁻¹) :=
  fun g hg => hGood_of_scalar (K := normKernel σ B N) hs (measurable_normKernel hσ N)
    (norm_normKernel_le hσ hB N) (hScalar_normKernel (truncScalarStrong_lt_two hs hs2) hσ hB N)
    g hg.1 hg.2.1 hg.2.2

/-- **`TruncScalarStrong` for `s > 2`**, by duality. -/
theorem exists_truncScalarStrong_gt_two {s : ℝ} (hs : 2 < s) :
    ∃ A : ℝ, 0 ≤ A ∧ TruncScalarStrong s A := by
  obtain ⟨h1, h2⟩ := conjExponent_mem_Ioo hs
  refine ⟨marcConst (Real.conjExponent s) ^ (Real.conjExponent s)⁻¹,
    Real.rpow_nonneg (marcConst_nonneg h1 h2) _, ?_⟩
  refine truncScalarStrong_of_kStrong_one (by linarith)
    (Real.rpow_nonneg (marcConst_nonneg h1 h2) _) ?_
  intro B σ hσ hB N
  refine kStrong_of_adjoint (measurable_normKernel hσ N) (norm_normKernel_le hσ hB N) (by linarith)
    (by linarith) (Real.rpow_nonneg (marcConst_nonneg h1 h2) _) ?_
  rw [adjKernel_normKernel]
  exact kStrong_one_normKernel_lt_two h1 h2 1 hσ.conj hB N

/-- **`TruncScalarStrong` for every `s > 1`**, unconditional. -/
theorem exists_truncScalarStrong {s : ℝ} (hs : 1 < s) : ∃ A : ℝ, 0 ≤ A ∧ TruncScalarStrong s A := by
  rcases le_or_gt s 2 with h | h
  · exact exists_truncScalarStrong_le_two hs h
  · exact exists_truncScalarStrong_gt_two h

end PrimeBHT.TimeFrequency.X2.CZ
