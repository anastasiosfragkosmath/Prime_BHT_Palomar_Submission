module

public import PrimeBHT.Interface.X1Statement
public import PrimeBHT.Frozen.BhtOpR
public import PrimeBHT.Frozen.BhtTrunc
public import PrimeBHT.Frozen.IsCutoff
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import PrimeBHT.TimeFrequency.X1.Transfer.Embed
import PrimeBHT.TimeFrequency.X1.Transfer.Kernel
import PrimeBHT.TimeFrequency.X1.Transfer.Perturb
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Part Z4 of `docs/x1-blueprint.md`: M2 implies X1

* `M2Prop`: the statement of the real-line theorem M2, written over the frozen
  `PrimeBHT.Statements.bhtOpR` and `PrimeBHT.Statements.IsCutoff`, literally the type of the frozen
  `PrimeBHT.Statements.bht_real_smooth` (text of `scripts/data/approved/M2-approved.lean.txt`).
* `x1_of_m2 : M2Prop → X1Statement`: **conditional** on M2 (the only hypothesis). Proof: Z1 lifts finitely
  supported `f, g` to the Schwartz functions `F, G`; Z2/Z3 give, for `|u| ≤ 1/12`,
  `‖H(n)‖ₑ ≤ 6 (‖T(F,G)(n + u)‖ₑ + 5 C 𝔈(n))` with `H = bhtTrunc χ L₁ L₂ f g`; the averaging argument
  (`tsum_enorm_rpow_le_of_pointwise`, in `ℝ≥0∞`) integrates this over `u ∈ [-1/12, 1/12]`, uses the disjoint
  windows `[n - 1/12, n + 1/12]`, the `L^r` bound of M2 and the `ℓ^p × ℓ^q → ℓ^r` bound of `𝔈` (Z3 (c)).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Transfer

/-- **M2** (the real-line theorem), as a `Prop`: exactly the type of the frozen
`PrimeBHT.Statements.bht_real_smooth`. -/
def M2Prop : Prop :=
  ∀ χ : ℝ → ℝ, PrimeBHT.Statements.IsCutoff χ →
    ∀ p q r : ℝ, 1 < p → 1 < q → 1 / r = 1 / p + 1 / q → 2 / 3 < r →
      ∃ C : ℝ, ∀ lam mu : ℝ, 0 < lam → lam < mu → ∀ f g : SchwartzMap ℝ ℂ,
        eLpNorm (PrimeBHT.Statements.bhtOpR χ lam mu f g) (ENNReal.ofReal r) volume ≤
          ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume *
            eLpNorm g (ENNReal.ofReal q) volume

open PrimeBHT.Statements

/-! ## Preliminaries on `bhtOpR` and `bhtTrunc` -/

/-- The operator is continuous in `x` (for continuous `f, g`, a cutoff and `0 < λ ≤ μ`). -/
theorem continuous_bhtOpR {χ : ℝ → ℝ} (hχ : IsCutoff χ) {lam mu : ℝ} (hlam : 0 < lam)
    (hlm : lam ≤ mu) {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (bhtOpR χ lam mu f g) := by
  have hK := continuous_bhtKernelR hχ hlam hlm
  have hcont : Continuous
      (Function.uncurry fun x y : ℝ => f (x - y) * g (x + y) * (bhtKernelR χ lam mu y : ℂ)) :=
    ((hf.comp (continuous_fst.sub continuous_snd)).mul
      (hg.comp (continuous_fst.add continuous_snd))).mul
      (Complex.continuous_ofReal.comp (hK.comp continuous_snd))
  have h := continuous_parametric_integral_of_continuous (μ := volume) hcont
    (isCompact_Icc (a := -(1 / lam)) (b := 1 / lam))
  refine h.congr fun x => ?_
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
    simp [bhtKernelR_eq_zero_of_notMem_Icc hχ hlam hlm hy]

/-- The kernel of `bhtTrunc χ L₁ L₂` at `m ∈ ℤ` is `K_{λ,μ}(m)` with `λ = 1/L₂`, `μ = 1/L₁`. -/
theorem bhtTrunc_eq_tsum_bhtKernelR (χ : ℝ → ℝ) (L₁ L₂ : ℝ) (f g : ℤ → ℂ) (x : ℤ) :
    bhtTrunc χ L₁ L₂ f g x =
      ∑' m : ℤ, (bhtKernelR χ L₂⁻¹ L₁⁻¹ (m : ℝ) : ℂ) * f (x - m) * g (x + m) := by
  unfold bhtTrunc
  refine tsum_congr fun m => ?_
  by_cases hm : m = 0
  · subst hm; simp [bhtKernelR_zero]
  · simp only [hm, ↓reduceIte, bhtKernelR, div_eq_inv_mul]

/-! ## Averaging in `ℝ≥0∞` -/

/-- The windows `[n - 1/12, n + 1/12]` are pairwise disjoint. -/
theorem pairwise_disjoint_windows :
    Pairwise (Function.onFun Disjoint fun n : ℤ => Set.Icc ((n : ℝ) - 1 / 12) ((n : ℝ) + 1 / 12)) := by
  intro n m hnm
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hy
  apply hnm
  have h1 : ((n - m : ℤ) : ℝ) < 1 := by push_cast; linarith [hx.1, hx.2, hy.1, hy.2]
  have h2 : (-1 : ℝ) < ((n - m : ℤ) : ℝ) := by push_cast; linarith [hx.1, hx.2, hy.1, hy.2]
  have h1' : n - m < 1 := by exact_mod_cast h1
  have h2' : -1 < n - m := by exact_mod_cast h2
  omega

theorem exists_rpow_add_le {r : ℝ} (hr : 0 < r) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ a b : ℝ≥0∞, (a + b) ^ r ≤ c * (a ^ r + b ^ r) := by
  by_cases hr1 : r ≤ 1
  · exact ⟨1, ENNReal.one_ne_top, fun a b => by
      rw [one_mul]; exact ENNReal.rpow_add_le_add_rpow a b hr.le hr1⟩
  · exact ⟨2 ^ (r - 1), ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top,
      fun a b => ENNReal.rpow_add_le_mul_rpow_add_rpow a b (by linarith)⟩

/-- **The averaging step.** If `‖H n‖ₑ ≤ 6 (‖T(n + u)‖ₑ + E n)` for all `n ∈ ℤ` and `|u| ≤ 1/12`, then
`∑_n ‖H n‖ₑ^r ≤ 6^r c (6 ∫ ‖T‖ₑ^r + ∑_n (E n)^r)`, where `(a + b)^r ≤ c (a^r + b^r)`. -/
theorem tsum_enorm_rpow_le_of_pointwise {T : ℝ → ℂ} (hT : Continuous T) {H : ℤ → ℂ}
    {E : ℤ → ℝ≥0∞} {r : ℝ} (hr : 0 < r) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hcb : ∀ a b : ℝ≥0∞, (a + b) ^ r ≤ c * (a ^ r + b ^ r))
    (hpt : ∀ (n : ℤ) (u : ℝ), |u| ≤ 1 / 12 → ‖H n‖ₑ ≤ 6 * (‖T (n + u)‖ₑ + E n)) :
    ∑' n : ℤ, ‖H n‖ₑ ^ r ≤
      6 ^ r * c * (6 * (∫⁻ x, ‖T x‖ₑ ^ r) + ∑' n : ℤ, E n ^ r) := by
  have h6r : (6 : ℝ≥0∞) ^ r ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hr.le ENNReal.ofNat_ne_top
  have hν : (6 : ℝ≥0∞) * ENNReal.ofReal (1 / 6) = 1 := by
    rw [← ENNReal.ofReal_ofNat 6, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hmeas : Measurable fun x : ℝ => ‖T x‖ₑ ^ r := (hT.measurable.enorm).pow_const r
  have hvol : ∀ n : ℤ, volume (Set.Icc ((n : ℝ) - 1 / 12) ((n : ℝ) + 1 / 12)) =
      ENNReal.ofReal (1 / 6) := by
    intro n
    rw [Real.volume_Icc]
    congr 1
    ring
  have hn : ∀ n : ℤ, ‖H n‖ₑ ^ r ≤
      6 ^ r * c * (6 * (∫⁻ x in Set.Icc ((n : ℝ) - 1 / 12) ((n : ℝ) + 1 / 12), ‖T x‖ₑ ^ r) +
        E n ^ r) := by
    intro n
    have h1 : ‖H n‖ₑ ^ r * ENNReal.ofReal (1 / 6) ≤
        6 ^ r * c * ((∫⁻ x in Set.Icc ((n : ℝ) - 1 / 12) ((n : ℝ) + 1 / 12), ‖T x‖ₑ ^ r) +
          E n ^ r * ENNReal.ofReal (1 / 6)) := by
      calc ‖H n‖ₑ ^ r * ENNReal.ofReal (1 / 6)
          = ∫⁻ x in Set.Icc ((n : ℝ) - 1 / 12) ((n : ℝ) + 1 / 12), ‖H n‖ₑ ^ r := by
            rw [setLIntegral_const, hvol]
        _ ≤ ∫⁻ x in Set.Icc ((n : ℝ) - 1 / 12) ((n : ℝ) + 1 / 12),
              6 ^ r * c * (‖T x‖ₑ ^ r + E n ^ r) := by
            refine setLIntegral_mono' measurableSet_Icc fun x hx => ?_
            have hu : |x - n| ≤ 1 / 12 := by
              rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
            have h2 := hpt n (x - n) hu
            rw [show (n : ℝ) + (x - n) = x by ring] at h2
            calc ‖H n‖ₑ ^ r ≤ (6 * (‖T x‖ₑ + E n)) ^ r := ENNReal.rpow_le_rpow h2 hr.le
              _ = 6 ^ r * (‖T x‖ₑ + E n) ^ r := ENNReal.mul_rpow_of_nonneg _ _ hr.le
              _ ≤ 6 ^ r * (c * (‖T x‖ₑ ^ r + E n ^ r)) := by gcongr; exact hcb _ _
              _ = 6 ^ r * c * (‖T x‖ₑ ^ r + E n ^ r) := by ring
        _ = 6 ^ r * c * ((∫⁻ x in Set.Icc ((n : ℝ) - 1 / 12) ((n : ℝ) + 1 / 12), ‖T x‖ₑ ^ r) +
              E n ^ r * ENNReal.ofReal (1 / 6)) := by
            rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top h6r hc),
              lintegral_add_right _ measurable_const, setLIntegral_const, hvol]
    calc ‖H n‖ₑ ^ r = 6 * (‖H n‖ₑ ^ r * ENNReal.ofReal (1 / 6)) := by
          rw [mul_comm (‖H n‖ₑ ^ r), ← mul_assoc, hν, one_mul]
      _ ≤ 6 * (6 ^ r * c * ((∫⁻ x in Set.Icc ((n : ℝ) - 1 / 12) ((n : ℝ) + 1 / 12), ‖T x‖ₑ ^ r) +
            E n ^ r * ENNReal.ofReal (1 / 6))) := by gcongr
      _ = 6 ^ r * c * (6 * (∫⁻ x in Set.Icc ((n : ℝ) - 1 / 12) ((n : ℝ) + 1 / 12), ‖T x‖ₑ ^ r) +
            E n ^ r) := by
          have : (6 : ℝ≥0∞) * (E n ^ r * ENNReal.ofReal (1 / 6)) = E n ^ r := by
            rw [mul_comm (E n ^ r), ← mul_assoc, hν, one_mul]
          rw [mul_left_comm, mul_add, this]
  have hsum : ∑' n : ℤ, ∫⁻ x in Set.Icc ((n : ℝ) - 1 / 12) ((n : ℝ) + 1 / 12), ‖T x‖ₑ ^ r ≤
      ∫⁻ x, ‖T x‖ₑ ^ r := by
    rw [← lintegral_iUnion (fun n => measurableSet_Icc) pairwise_disjoint_windows]
    exact setLIntegral_le_lintegral _ _
  calc ∑' n : ℤ, ‖H n‖ₑ ^ r
      ≤ ∑' n : ℤ, 6 ^ r * c * (6 * (∫⁻ x in Set.Icc ((n : ℝ) - 1 / 12) ((n : ℝ) + 1 / 12),
          ‖T x‖ₑ ^ r) + E n ^ r) := ENNReal.tsum_le_tsum hn
    _ = 6 ^ r * c * (6 * (∑' n : ℤ, ∫⁻ x in Set.Icc ((n : ℝ) - 1 / 12) ((n : ℝ) + 1 / 12),
          ‖T x‖ₑ ^ r) + ∑' n : ℤ, E n ^ r) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ ≤ 6 ^ r * c * (6 * (∫⁻ x, ‖T x‖ₑ ^ r) + ∑' n : ℤ, E n ^ r) := by gcongr

/-! ## The assembly -/

/-- **M2 ⇒ X1** (conditional on `M2Prop`, i.e. on the frozen `bht_real_smooth`; no other hypothesis). -/
theorem x1_of_m2 : M2Prop → PrimeBHT.Interface.X1Statement.X1Statement := by
  intro hM2 χ hχ p q r hp hq hpqr hr
  obtain ⟨C₂, hC₂⟩ := hM2 χ hχ p q r hp hq hpqr hr
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hr0 : 0 < r := by linarith
  obtain ⟨Ck, hCk0, hCk⟩ := exists_kernel_bounds hχ
  obtain ⟨A, hA, hAb⟩ := exists_errOp_bound hp0 hq0 hpqr (by linarith : (1 : ℝ) / 2 < r)
  obtain ⟨c, hc, hcb⟩ := exists_rpow_add_le hr0
  set Aconst : ℝ≥0∞ := 6 ^ r * c * (6 * ENNReal.ofReal C₂ ^ r + ENNReal.ofReal (5 * Ck) ^ r * A)
    with hAconst
  have hAfin : Aconst ≠ ⊤ := by
    have h6 : (6 : ℝ≥0∞) ^ r ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hr0.le ENNReal.ofNat_ne_top
    have h1 : ENNReal.ofReal C₂ ^ r ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hr0.le ENNReal.ofReal_ne_top
    have h2 : ENNReal.ofReal (5 * Ck) ^ r ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg hr0.le ENNReal.ofReal_ne_top
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top h6 hc)
      (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top h1, ENNReal.mul_ne_top h2 hA⟩)
  refine ⟨(Aconst ^ (1 / r)).toReal, ?_⟩
  intro L₁ L₂ hL₁ hL₁₂ f g hf hg
  have hL₂ : 0 < L₂ := hL₁.trans hL₁₂
  have hlam : 0 < L₂⁻¹ := inv_pos.2 hL₂
  have hlm : L₂⁻¹ < L₁⁻¹ := inv_strictAnti₀ hL₁ hL₁₂
  obtain ⟨hKs, hK1, hK2⟩ := hCk L₂⁻¹ L₁⁻¹ hlam hlm.le
  set K : ℝ → ℝ := bhtKernelR χ L₂⁻¹ L₁⁻¹ with hKdef
  have hKc : Continuous K := continuous_bhtKernelR hχ hlam hlm.le
  have hKd : Differentiable ℝ K := hKs.differentiable (by simp)
  have hK0 : K 0 = 0 := bhtKernelR_zero _ _ _
  obtain ⟨F, hF⟩ := exists_schwartz_liftC (-1 / 2) hf
  obtain ⟨G, hG⟩ := exists_schwartz_liftC (1 / 2) hg
  have hF' : (⇑F : ℝ → ℂ) = liftC (-1 / 2) f := funext hF
  have hG' : (⇑G : ℝ → ℂ) = liftC (1 / 2) g := funext hG
  set T : ℝ → ℂ := bhtOpR χ L₂⁻¹ L₁⁻¹ F G with hTdef
  have hTc : Continuous T := continuous_bhtOpR hχ hlam hlm.le F.continuous G.continuous
  set P : ℝ≥0∞ := eLpNorm f (ENNReal.ofReal p) Measure.count *
    eLpNorm g (ENNReal.ofReal q) Measure.count with hPdef
  -- the pointwise bound
  have hpt : ∀ (n : ℤ) (u : ℝ), |u| ≤ 1 / 12 → ‖bhtTrunc χ L₁ L₂ f g n‖ₑ ≤
      6 * (‖T (n + u)‖ₑ + ENNReal.ofReal (5 * Ck) * errOp f g n) := by
    intro n u hu
    have := enorm_main_le hKc hKd hK0 hK1 hK2 hf hg n hu
    rw [bhtTrunc_eq_tsum_bhtKernelR]
    convert this using 4
    simp only [hTdef, bhtOpR, hF', hG', hKdef]
  have havg := tsum_enorm_rpow_le_of_pointwise hTc hr0 hc hcb hpt
  -- bound the pieces
  have hTnorm : ∫⁻ x, ‖T x‖ₑ ^ r ≤ (ENNReal.ofReal C₂ * P) ^ r := by
    have h1 := hC₂ L₂⁻¹ L₁⁻¹ hlam hlm F G
    have h2 : eLpNorm T (ENNReal.ofReal r) volume = (∫⁻ x, ‖T x‖ₑ ^ r) ^ (1 / r) :=
      eLpNorm_volume_eq hTc.aestronglyMeasurable hr0
    have h3 : eLpNorm F (ENNReal.ofReal p) volume ≤ eLpNorm f (ENNReal.ofReal p) Measure.count := by
      rw [hF']; exact eLpNorm_liftC_le _ hf hp0
    have h4 : eLpNorm G (ENNReal.ofReal q) volume ≤ eLpNorm g (ENNReal.ofReal q) Measure.count := by
      rw [hG']; exact eLpNorm_liftC_le _ hg hq0
    have h5 : eLpNorm T (ENNReal.ofReal r) volume ≤ ENNReal.ofReal C₂ * P := by
      calc eLpNorm T (ENNReal.ofReal r) volume
          ≤ ENNReal.ofReal C₂ * eLpNorm F (ENNReal.ofReal p) volume *
              eLpNorm G (ENNReal.ofReal q) volume := h1
        _ ≤ ENNReal.ofReal C₂ * eLpNorm f (ENNReal.ofReal p) Measure.count *
              eLpNorm g (ENNReal.ofReal q) Measure.count := by gcongr
        _ = ENNReal.ofReal C₂ * P := by rw [hPdef, mul_assoc]
    have h6 := ENNReal.rpow_le_rpow h5 hr0.le
    rw [h2, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hr0.ne', ENNReal.rpow_one] at h6
    exact h6
  have hE : ∑' n : ℤ, (ENNReal.ofReal (5 * Ck) * errOp f g n) ^ r ≤
      ENNReal.ofReal (5 * Ck) ^ r * A * P ^ r := by
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le]
    rw [ENNReal.tsum_mul_left, mul_assoc]
    gcongr
    exact hAb f g
  have hsum : ∑' n : ℤ, ‖bhtTrunc χ L₁ L₂ f g n‖ₑ ^ r ≤ Aconst * P ^ r := by
    refine havg.trans ?_
    calc 6 ^ r * c * (6 * (∫⁻ x, ‖T x‖ₑ ^ r) + ∑' n : ℤ, (ENNReal.ofReal (5 * Ck) * errOp f g n) ^ r)
        ≤ 6 ^ r * c * (6 * (ENNReal.ofReal C₂ * P) ^ r + ENNReal.ofReal (5 * Ck) ^ r * A * P ^ r) := by
          gcongr
      _ = Aconst * P ^ r := by
          rw [hAconst, ENNReal.mul_rpow_of_nonneg _ _ hr0.le]
          ring
  -- conclude
  rw [eLpNorm_count_eq _ hr0, ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg
    (by positivity) hAfin)]
  calc (∑' n : ℤ, ‖bhtTrunc χ L₁ L₂ f g n‖ₑ ^ r) ^ (1 / r)
      ≤ (Aconst * P ^ r) ^ (1 / r) := ENNReal.rpow_le_rpow hsum (by positivity)
    _ = Aconst ^ (1 / r) * P := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, one_div,
          mul_inv_cancel₀ hr0.ne', ENNReal.rpow_one]
    _ = Aconst ^ (1 / r) * eLpNorm f (ENNReal.ofReal p) Measure.count *
          eLpNorm g (ENNReal.ofReal q) Measure.count := by rw [hPdef, mul_assoc]

end PrimeBHT.TimeFrequency.Transfer

end
