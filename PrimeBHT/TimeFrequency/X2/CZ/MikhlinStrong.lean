module

public import PrimeBHT.TimeFrequency.X2.CZ.WeakMikhlin
public import PrimeBHT.TimeFrequency.X2.CZ.MarcinkiewiczKernel

/-!
# V08 phase 3: strong type for Mikhlin multipliers, `1 < q ≤ s ≤ 2`

* `normKernel σ B N = B⁻¹ K^N(x - u)`: the normalized truncated kernel (bounded measurable, Hörmander with the
  absolute constant `cH`, `L²` bound `2`).
* `truncScalarStrong_lt_two`: the scalar bound `TruncScalarStrong q A_q` for `1 < q < 2`, uniform in `N` and
  linear in `B` after normalization: **Marcinkiewicz** between weak `(1,1)` (`weak11_of_kernel` at `P = 1`)
  and `L²` (Plancherel), through `marcinkiewicz_kernel`.
* `scalarMikhlinStrong_of_trunc`: `TruncScalarStrong → ScalarMikhlinStrong` (Fatou in `N`).
* consequences: `vectorMikhlinWeak_le_two` (weak `(1,1)` into `L^{1,∞}(ℝ; L^s(Y_P))` for all `1 < s ≤ 2`,
  **unconditional**) and `vectorMikhlinStrong_diag_le_two` (`q = s ≤ 2`, unconditional).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology Real FourierTransform SchwartzMap

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

open PrimeBHT.Statements

/-- **Fatou along a pointwise limit** (for `lintegral`s of measurable functions). -/
theorem lintegral_le_of_tendsto_of_le {f : ℕ → ℝ → ℝ≥0∞} {g : ℝ → ℝ≥0∞} {c : ℝ≥0∞}
    (hf : ∀ N, Measurable (f N)) (hlim : ∀ x, Tendsto (fun N => f N x) atTop (nhds (g x)))
    (h : ∀ N, ∫⁻ x, f N x ≤ c) : ∫⁻ x, g x ≤ c := by
  calc ∫⁻ x, g x = ∫⁻ x, liminf (fun N => f N x) atTop :=
        lintegral_congr fun x => ((hlim x).liminf_eq).symm
    _ ≤ liminf (fun N => ∫⁻ x, f N x) atTop := lintegral_liminf_le hf
    _ ≤ c := liminf_le_of_frequently_le' (Frequently.of_forall h)

section NormKernel

variable {σ : ℝ → ℂ} {B : ℝ}

/-- The normalized truncated kernel `B⁻¹ K^N(x - u)`. -/
def normKernel (σ : ℝ → ℂ) (B : ℝ) (N : ℕ) : ℝ → ℝ → ℂ := fun x u => (B : ℂ)⁻¹ * kernelTrunc σ N (x - u)

theorem measurable_normKernel (hσ : IsMikhlin 3 B σ) (N : ℕ) :
    Measurable (Function.uncurry (normKernel σ B N)) := by
  have hc : Continuous (kernelTrunc σ N) := continuous_kernelTrunc hσ N
  exact (continuous_const.mul (hc.comp (continuous_fst.sub continuous_snd))).measurable

theorem norm_normKernel_le (hσ : IsMikhlin 3 B σ) (hB : 0 < B) (N : ℕ) (x z : ℝ) :
    ‖normKernel σ B N x z‖ ≤ B⁻¹ * ∫ ξ, ‖symbolTrunc σ N ξ‖ := by
  unfold normKernel
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
  exact mul_le_mul_of_nonneg_left (norm_kernelTrunc_le_integral hσ N _) (by positivity)

theorem kop_normKernel (_hB : 0 < B) (N : ℕ) (h : ℝ → ℂ) (x : ℝ) :
    kop (normKernel σ B N) h x = (B : ℂ)⁻¹ * kconv (kernelTrunc σ N) h x := by
  simp only [kop, kconv, normKernel]
  rw [← integral_const_mul]
  congr 1; ext u; ring

/-- Hörmander for the normalized kernel, with the absolute constant `cH`. -/
theorem hH_normKernel (hσ : IsMikhlin 3 B σ) (hB : 0 < B) (N : ℕ) (c u ℓ : ℝ)
    (hu : |u - c| ≤ ℓ / 2) :
    ∫⁻ x in {x : ℝ | ℓ < |x - c|}, ‖normKernel σ B N x u - normKernel σ B N x c‖ₑ ≤
      ENNReal.ofReal cH := by
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  refine hH_of_centered (Kf := fun z => (B : ℂ)⁻¹ * kernelTrunc σ N z) (c0 := cH) (fun y => ?_) c u ℓ hu
  have hy := lintegral_kernelTrunc_sub_le hσ hB N y
  have e : ∀ x, ‖(B : ℂ)⁻¹ * kernelTrunc σ N (x - y) - (B : ℂ)⁻¹ * kernelTrunc σ N x‖ₑ =
      ENNReal.ofReal B⁻¹ * ‖kernelTrunc σ N (x - y) - kernelTrunc σ N x‖ₑ := by
    intro x
    rw [← mul_sub, enorm_mul, enorm_inv_ofReal hB]
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal B⁻¹ * ∫⁻ x in {x : ℝ | 2 * |y| < |x|}, ‖kernelTrunc σ N (x - y) - kernelTrunc σ N x‖ₑ
      ≤ ENNReal.ofReal B⁻¹ * ENNReal.ofReal (cH * B) := mul_le_mul' le_rfl hy
    _ = ENNReal.ofReal cH := by
        have hcH : 0 ≤ cH := by unfold cH; positivity
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp

/-- The scalar hypothesis of `hGood_of_scalar` for the normalized kernel. -/
theorem hScalar_normKernel {s A : ℝ} (hT : TruncScalarStrong s A) (hσ : IsMikhlin 3 B σ) (hB : 0 < B)
    (N : ℕ) (h : ℝ → ℂ) (hm : Measurable h) (hi : Integrable h volume) (hb : ∃ C, ∀ u, ‖h u‖ ≤ C) :
    eLpNorm (kop (normKernel σ B N) h) (ENNReal.ofReal s) volume ≤
      ENNReal.ofReal A * eLpNorm h (ENNReal.ofReal s) volume := by
  have e : kop (normKernel σ B N) h = (B : ℂ)⁻¹ • kconv (kernelTrunc σ N) h := by
    ext x; rw [kop_normKernel hB]; simp [smul_eq_mul]
  rw [e, eLpNorm_const_smul, enorm_inv_ofReal hB]
  calc ENNReal.ofReal B⁻¹ * eLpNorm (kconv (kernelTrunc σ N) h) (ENNReal.ofReal s) volume
      ≤ ENNReal.ofReal B⁻¹ * (ENNReal.ofReal (A * B) * eLpNorm h (ENNReal.ofReal s) volume) :=
        mul_le_mul' le_rfl (hT B σ hσ N h hm hi hb)
    _ = ENNReal.ofReal A * eLpNorm h (ENNReal.ofReal s) volume := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2; field_simp

end NormKernel

theorem yNorm_zmod_one {s : ℝ} (hs : 0 < s) (v : ZMod 1 → ℂ) : yNorm s v = ‖v 0‖ := by
  unfold yNorm
  have : (∑ y : ZMod 1, ‖v y‖ ^ s) = ‖v 0‖ ^ s := by
    rw [Fintype.sum_unique]; rfl
  rw [this]
  simp only [Nat.cast_one, inv_one, one_mul]
  rw [← Real.rpow_mul (norm_nonneg _), mul_inv_cancel₀ hs.ne', Real.rpow_one]

section ScalarStrong

variable {σ : ℝ → ℂ} {B : ℝ}

theorem kernelTrunc_eq_zero_of_B_zero (hσ : IsMikhlin 3 0 σ) (N : ℕ) (x : ℝ) :
    kernelTrunc σ N x = 0 := by
  have hb := isBoundedSymbol_symbolTrunc hσ N
  unfold kernelTrunc
  rw [Real.fourierInv_eq_fourier_neg]
  have hae : symbolTrunc σ N =ᵐ[volume] fun _ => (0 : ℂ) := by
    filter_upwards [hb.ae_norm_le] with ξ hξ
    exact norm_le_zero_iff.1 (by simpa using hξ)
  rw [Real.fourier_congr_ae hae]
  simp [Real.fourier_eq]

/-- The explicit constant of the Marcinkiewicz step for the multipliers. -/
def marcConst (q : ℝ) : ℝ :=
  q * 2 ^ q * ((2 + 2 ^ (2 * (2 : ℝ) - 1) * 2 ^ (2 : ℝ) + 4 * cH) / (q - 1) + 2 ^ (2 : ℝ) / (2 - q))

theorem marcConst_nonneg {q : ℝ} (hq : 1 < q) (hq2 : q < 2) : 0 ≤ marcConst q := by
  have hcH : 0 ≤ cH := by unfold cH; positivity
  unfold marcConst
  have h1 : 0 < q - 1 := by linarith
  have h2 : 0 < 2 - q := by linarith
  positivity

/-- **Scalar `L^q` bound of the truncated multipliers, `1 < q < 2`** (Marcinkiewicz between weak `(1,1)` and
Plancherel; uniform in `N`, linear in `B`): `A_q = marcConst(q)^{1/q}`. -/
theorem truncScalarStrong_lt_two {q : ℝ} (hq : 1 < q) (hq2 : q < 2) :
    TruncScalarStrong q (marcConst q ^ q⁻¹) := by
  intro B σ hσ N h hm hi hb
  have hq0 : 0 < q := by linarith
  have hB0 := hσ.nonneg
  rcases hB0.eq_or_lt with hB | hB
  · subst hB
    have : kconv (kernelTrunc σ N) h = fun _ => 0 := by
      ext x; simp [kconv, kop, kernelTrunc_eq_zero_of_B_zero hσ N]
    rw [this]; simp
  · have hcH : 0 ≤ cH := by unfold cH; positivity
    have hs2 : (1 : ℝ) < 2 := by norm_num
    -- hypotheses for the normalized kernel at `s = 2`, `A = 2`
    have hKm := measurable_normKernel hσ N
    have hKb := norm_normKernel_le hσ hB N
    have hH := hH_normKernel hσ hB N
    have hGood : ∀ g : ℝ → ZMod 1 → ℂ, (∀ y, Measurable fun u => g u y) →
        (∀ y, Integrable fun u => g u y) → (∀ y, ∃ C, ∀ u, ‖g u y‖ ≤ C) →
        ∫⁻ x, ENNReal.ofReal (yNorm 2 (fun y => kop (normKernel σ B N) (fun u => g u y) x)) ^ (2 : ℝ) ≤
          ENNReal.ofReal 2 ^ (2 : ℝ) * ∫⁻ u, ENNReal.ofReal (yNorm 2 (g u)) ^ (2 : ℝ) :=
      fun g hgm hgi hgb => hGood_of_scalar (K := normKernel σ B N) hs2 hKm hKb
        (hScalar_normKernel truncScalarStrong_two hσ hB N) g hgm hgi hgb
    have hmain := marcinkiewicz_kernel (P := 1) (s := 2) hs2 hKm hKb (by norm_num : (0 : ℝ) ≤ 2) hcH hH hGood
      hq hq2 (fun u _ => h u) (fun _ => hm) (fun _ => hi) (fun _ => hb)
    simp only [yNorm_zmod_one (by norm_num : (0 : ℝ) < 2)] at hmain
    have hmeas1 : AEStronglyMeasurable (kop (normKernel σ B N) h) volume :=
      (measurable_kop hKm hm).aestronglyMeasurable
    have hne0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.2 hq0).ne'
    have hint : ∫⁻ x, ‖kop (normKernel σ B N) h x‖ₑ ^ q ≤
        ENNReal.ofReal (marcConst q) * ∫⁻ x, ‖h x‖ₑ ^ q := by
      simp only [ofReal_norm] at hmain
      exact hmain
    have hMq : 0 ≤ marcConst q := marcConst_nonneg hq hq2
    have hK_eLp : eLpNorm (kop (normKernel σ B N) h) (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal (marcConst q ^ q⁻¹) * eLpNorm h (ENNReal.ofReal q) volume := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 ENNReal.ofReal_ne_top hmeas1,
        eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 ENNReal.ofReal_ne_top hm.aestronglyMeasurable,
        ENNReal.toReal_ofReal hq0.le, one_div]
      calc (∫⁻ x, ‖kop (normKernel σ B N) h x‖ₑ ^ q) ^ q⁻¹
          ≤ (ENNReal.ofReal (marcConst q) * ∫⁻ x, ‖h x‖ₑ ^ q) ^ q⁻¹ :=
            ENNReal.rpow_le_rpow hint (inv_nonneg.2 hq0.le)
        _ = ENNReal.ofReal (marcConst q) ^ q⁻¹ * (∫⁻ x, ‖h x‖ₑ ^ q) ^ q⁻¹ :=
            ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hq0.le)
        _ = ENNReal.ofReal (marcConst q ^ q⁻¹) * (∫⁻ x, ‖h x‖ₑ ^ q) ^ q⁻¹ := by
            rw [ENNReal.ofReal_rpow_of_nonneg hMq (inv_nonneg.2 hq0.le)]
    have hkc : kconv (kernelTrunc σ N) h = (B : ℂ) • kop (normKernel σ B N) h := by
      ext x
      rw [Pi.smul_apply, kop_normKernel hB]
      have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
      simp [smul_eq_mul, hBc]
    rw [hkc, eLpNorm_const_smul]
    have : ‖(B : ℂ)‖ₑ = ENNReal.ofReal B := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
    rw [this]
    calc ENNReal.ofReal B * eLpNorm (kop (normKernel σ B N) h) (ENNReal.ofReal q) volume
        ≤ ENNReal.ofReal B * (ENNReal.ofReal (marcConst q ^ q⁻¹) * eLpNorm h (ENNReal.ofReal q) volume) :=
          mul_le_mul' le_rfl hK_eLp
      _ = ENNReal.ofReal (marcConst q ^ q⁻¹ * B) * eLpNorm h (ENNReal.ofReal q) volume := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hB.le, mul_comm B]

end ScalarStrong

theorem lintegral_enorm_rpow_eq {q : ℝ} (hq : 0 < q) {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume) :
    ∫⁻ x, ‖f x‖ₑ ^ q = eLpNorm f (ENNReal.ofReal q) volume ^ q := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq).ne' ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hq.le, one_div, ← ENNReal.rpow_mul, inv_mul_cancel₀ hq.ne', ENNReal.rpow_one]

/-- `TruncScalarStrong` for every exponent in `(1, 2]`, unconditionally. -/
theorem exists_truncScalarStrong_le_two {s : ℝ} (hs : 1 < s) (hs2 : s ≤ 2) :
    ∃ A : ℝ, 0 ≤ A ∧ TruncScalarStrong s A := by
  rcases hs2.eq_or_lt with h | h
  · subst h
    exact ⟨2, by norm_num, truncScalarStrong_two⟩
  · exact ⟨_, Real.rpow_nonneg (marcConst_nonneg hs h) _, truncScalarStrong_lt_two hs h⟩

section Mixed

variable {P : ℕ} [NeZero P] {σ : ℝ → ℂ} {B s : ℝ}

theorem tendsto_yNorm_tensorMultTrunc {s : ℝ} (hs : 0 < s) (hσ : IsMikhlin 3 B σ)
    (f : ZMod P → 𝓢(ℝ, ℂ)) (x : ℝ) :
    Tendsto (fun N : ℕ => yNorm s (fun y => multOp (symbolTrunc σ N) (⇑(fibreSchwartz f y)) x))
      atTop (nhds (yNorm s (tensorMult σ f x))) := by
  have e : tensorMult σ f x = fun y => multOp σ (⇑(fibreSchwartz f y)) x := by
    ext y; exact tensorMult_eq_multOp_fibreSchwartz hσ.isBoundedSymbol f x y
  rw [e]
  exact ((continuous_yNorm hs).tendsto _).comp
    (tendsto_pi_nhds.2 fun y => tendsto_multOp_symbolTrunc hσ (fibreSchwartz f y) x)

theorem yNorm_multOp_trunc_eq (hs : 0 < s) (hσ : IsMikhlin 3 B σ) (hB : 0 < B) (N : ℕ)
    (f : ZMod P → 𝓢(ℝ, ℂ)) (x : ℝ) :
    yNorm s (fun y => multOp (symbolTrunc σ N) (⇑(fibreSchwartz f y)) x) =
      B * yNorm s (fun y => kop (normKernel σ B N) (fun u => tensorFun f u y) x) := by
  have h1 : (fun y => multOp (symbolTrunc σ N) (⇑(fibreSchwartz f y)) x) =
      fun y => (B : ℂ) * kop (normKernel σ B N) (fun u => tensorFun f u y) x := by
    ext y
    have hi : Integrable (⇑(fibreSchwartz f y)) volume := (fibreSchwartz f y).integrable
    have e : (fun u => tensorFun f u y) = ⇑(fibreSchwartz f y) := by
      ext u; exact (fibreSchwartz_apply f y u).symm
    rw [← kconv_kernelTrunc_eq hσ N hi x, e, kop_normKernel hB]
    have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
    field_simp
  rw [h1, yNorm_const_mul (P := P) hs, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]

end Mixed

end PrimeBHT.TimeFrequency.X2.CZ
