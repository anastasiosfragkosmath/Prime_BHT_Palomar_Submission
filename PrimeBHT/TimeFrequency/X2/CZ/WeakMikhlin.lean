module

public import PrimeBHT.TimeFrequency.X2.CZ.Truncated
public import PrimeBHT.TimeFrequency.X2.CZ.WeakType

/-!
# V08 phase 2: weak type `(1,1)` of `T_σ ⊗ Id` into `L^{1,∞}(ℝ; L^s(Y_P))`

`VectorMikhlinWeak` (`Statements.lean`) for Mikhlin symbols with constants **independent of `P`** and
**linear in `B`**:

* `vectorMikhlinWeak_two`: **unconditional** for `s = 2` (`X = H`): the scalar bound is Plancherel
  (`‖σ^N‖_∞ ≤ 2B`), `A = 2`, `C = 2 + 2^3 · 2^2 + 4 cH = 34 + 4 cH`;
* `weak11_tensorMult_of_trunc`, `vectorMikhlinWeak_of_trunc` (`…_of_trunc`, **conditional**): for every
  `1 < s < ∞`, assuming the scalar `L^s(ℝ)` bound of the truncated multipliers `K^N *` uniformly in `N`
  (`TruncScalarStrong s A`; this is the base case `q = s` of V08(a), which for `s ≠ 2` needs the scalar
  Marcinkiewicz interpolation and duality, not yet done); `C = 2 + 2^{2s-1} A^s + 4 cH`.

Route: truncate `σ ↦ σ^N` (`Truncated.lean`: `T_{σ^N} h = K^N * h`, `K^N ∈ L¹` bounded continuous, uniform
Hörmander and `L²` bounds), apply the abstract weak type theorem `weak11_of_kernel` (`WeakType.lean`) to the
normalized kernel `K̃ = K^N / B`, then let `N → ∞` on Schwartz data (`tendsto_multOp_symbolTrunc`, continuity
of `yNorm`, continuity from below of the measure).  The weak-type argument is *quadratic* in the `L²` constant
(good part by Chebyshev in `L^s`), so the normalization `K / B` is what makes the final constant linear in `B`.

## Corrections to the blueprint (V08 steps 2-5), proved here
1. *Truncated kernels instead of an `L²` extension.*  The blueprint's `T` on `L¹ + L^s` and "Marcinkiewicz
   applies" are not literally available: `T_σ ⊗ Id` is defined on Schwartz tensors only, and the Carleson
   clone's `exists_hasStrongType_real_interpolation` needs an operator defined on all of `L^{p₀} + L^{p₁}`
   (`AESubadditiveOn`) between normed spaces.  The truncations `T_N = K^N *` are defined on every `L¹`
   function, uniformly bounded, and converge to `T_σ` on Schwartz functions, so they are the right object:
   weak `(1,1)` and the later Marcinkiewicz step are applied to `T_N`, then `N → ∞`.
2. *The Bochner integral in `X` does not exist as printed*: `(ZMod P → ℂ, yNorm s)` is not a normed space
   instance.  The inequality used for the vector means and the bad atoms, `‖∫ φ v‖_X ≤ ∫ |φ| ‖v‖_X`, is
   proved coordinatewise by testing against the Hölder extremiser (`Minkowski.lean`, `s > 1`, uniform in `P`).
3. *Constants.*  The weak-type constant of the printed argument is quadratic in the `L²` (resp. `L^s`)
   bound; linearity in `B` holds only after normalizing the symbol (`σ ↦ σ / B`), as done here.
4. *Dilation.*  With half-open dyadic `Q_i` of length `ℓ_i` the excluded set is `|x - c_i| ≤ ℓ_i` (twice the
   interval), not `3Q_i`: `|x - c_i| > ℓ_i ≥ 2 |u - c_i|` is exactly the Hörmander hypothesis
   (`∫_{|x| > 2|y|} |K(x - y) - K(x)| dx ≤ cH`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology Real FourierTransform SchwartzMap

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

open PrimeBHT.Statements

section Kernel

variable {σ : ℝ → ℂ} {B : ℝ}

theorem kconv_kernelTrunc_eq (hσ : IsMikhlin 3 B σ) (N : ℕ) {h : ℝ → ℂ}
    (hh : Integrable h volume) (x : ℝ) :
    kconv (kernelTrunc σ N) h x = multOp (symbolTrunc σ N) h x :=
  (multOp_eq_integral_fourierInv (integrable_symbolTrunc hσ N) hh x).symm

theorem continuous_kernelTrunc (hσ : IsMikhlin 3 B σ) (N : ℕ) : Continuous (kernelTrunc σ N) :=
  continuous_fourierInv_of_integrable _ (integrable_symbolTrunc hσ N)

theorem norm_kernelTrunc_le_integral (_hσ : IsMikhlin 3 B σ) (N : ℕ) (x : ℝ) :
    ‖kernelTrunc σ N x‖ ≤ ∫ ξ, ‖symbolTrunc σ N ξ‖ := by
  unfold kernelTrunc
  rw [Real.fourierInv_eq_fourier_neg]
  exact Real.norm_fourier_le_integral_norm _ _

/-- Translation of the Hörmander condition: from the centered form `c = 0` to arbitrary centres. -/
theorem hH_of_centered {Kf : ℝ → ℂ} {c0 : ℝ}
    (h : ∀ y : ℝ, ∫⁻ x in {x : ℝ | 2 * |y| < |x|}, ‖Kf (x - y) - Kf x‖ₑ ≤ ENNReal.ofReal c0)
    (c u ℓ : ℝ) (hu : |u - c| ≤ ℓ / 2) :
    ∫⁻ x in {x : ℝ | ℓ < |x - c|}, ‖Kf (x - u) - Kf (x - c)‖ₑ ≤ ENNReal.ofReal c0 := by
  set y := u - c with hy
  have hS0 : MeasurableSet {z : ℝ | ℓ < |z|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hSc : MeasurableSet {x : ℝ | ℓ < |x - c|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (measurable_id.sub_const _))
  set hh : ℝ → ℝ≥0∞ := fun z => ‖Kf (z - y) - Kf z‖ₑ with hhdef
  have e : ∀ x, Set.indicator {x : ℝ | ℓ < |x - c|} (fun x => ‖Kf (x - u) - Kf (x - c)‖ₑ) x =
      Set.indicator {z : ℝ | ℓ < |z|} hh (x - c) := by
    intro x
    by_cases hx : ℓ < |x - c|
    · rw [indicator_of_mem (show x ∈ {x : ℝ | ℓ < |x - c|} from hx),
        indicator_of_mem (show x - c ∈ {z : ℝ | ℓ < |z|} from hx)]
      simp only [hhdef, hy]
      congr 3; ring
    · rw [indicator_of_notMem (show x ∉ {x : ℝ | ℓ < |x - c|} from hx),
        indicator_of_notMem (show x - c ∉ {z : ℝ | ℓ < |z|} from hx)]
  calc ∫⁻ x in {x : ℝ | ℓ < |x - c|}, ‖Kf (x - u) - Kf (x - c)‖ₑ
      = ∫⁻ x, Set.indicator {x : ℝ | ℓ < |x - c|} (fun x => ‖Kf (x - u) - Kf (x - c)‖ₑ) x :=
        (lintegral_indicator hSc _).symm
    _ = ∫⁻ x, Set.indicator {z : ℝ | ℓ < |z|} hh (x - c) := lintegral_congr e
    _ = ∫⁻ z, Set.indicator {z : ℝ | ℓ < |z|} hh z :=
        lintegral_sub_right_eq_self (fun z => Set.indicator {z : ℝ | ℓ < |z|} hh z) c
    _ = ∫⁻ z in {z : ℝ | ℓ < |z|}, hh z := lintegral_indicator hS0 _
    _ ≤ ∫⁻ z in {z : ℝ | 2 * |y| < |z|}, hh z := by
        refine lintegral_mono_set ?_
        intro z hz
        simp only [mem_ofPred_eq] at hz ⊢
        have : 2 * |y| ≤ ℓ := by linarith
        linarith
    _ ≤ ENNReal.ofReal c0 := h y

end Kernel

section Scalar

/-- The scalar `L^s(ℝ)` bound of the truncated multipliers `K^N * ·` on bounded integrable functions,
uniformly in `N` (the hypothesis of the conditional statements for `s ≠ 2`). -/
def TruncScalarStrong (s A : ℝ) : Prop :=
  ∀ (B : ℝ) (σ : ℝ → ℂ), IsMikhlin 3 B σ → ∀ N : ℕ, ∀ h : ℝ → ℂ, Measurable h →
    Integrable h volume → (∃ C, ∀ u, ‖h u‖ ≤ C) →
    eLpNorm (kconv (kernelTrunc σ N) h) (ENNReal.ofReal s) volume ≤
      ENNReal.ofReal (A * B) * eLpNorm h (ENNReal.ofReal s) volume

theorem memLp_two_of_bdd_integrable {h : ℝ → ℂ} (hm : Measurable h) (hi : Integrable h volume)
    (hb : ∃ C, ∀ u, ‖h u‖ ≤ C) : MemLp h 2 volume := by
  obtain ⟨C, hC⟩ := hb
  rw [memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable]
  refine Integrable.mono' (g := fun u => C * ‖h u‖) (hi.norm.const_mul C)
    (hm.norm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
  exact mul_le_mul_of_nonneg_right (hC u) (norm_nonneg _)

/-- **The `L²` case is Plancherel**: `TruncScalarStrong 2 2`, unconditional. -/
theorem truncScalarStrong_two : TruncScalarStrong 2 2 := by
  intro B σ hσ N h hm hi hb
  have hq : ENNReal.ofReal 2 = 2 := by simp
  rw [hq, eLpNorm_congr_ae ?_]
  · have := eLpNorm_multOp_two_le_of_integrable (isBoundedSymbol_symbolTrunc hσ N)
      (integrable_symbolTrunc hσ N) hi (memLp_two_of_bdd_integrable hm hi hb)
    simpa [mul_comm] using this
  · exact Eventually.of_forall fun x => kconv_kernelTrunc_eq hσ N hi x

end Scalar

section Trunc

variable {P : ℕ} [NeZero P] {σ : ℝ → ℂ} {B : ℝ}

theorem enorm_inv_ofReal {B : ℝ} (hB : 0 < B) : ‖((B : ℂ))⁻¹‖ₑ = ENNReal.ofReal B⁻¹ := by
  rw [← ofReal_norm, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]

theorem schwartz_bounded (S : 𝓢(ℝ, ℂ)) : ∃ C, ∀ u, ‖S u‖ ≤ C :=
  ⟨‖S.toBoundedContinuousFunction‖, fun u => S.toBoundedContinuousFunction.norm_coe_le_norm u⟩

/-- The fibres of a tensor Schwartz function. -/
theorem tensorFun_fibre_facts (f : ZMod P → 𝓢(ℝ, ℂ)) :
    (∀ y, Measurable fun u => tensorFun f u y) ∧ (∀ y, Integrable fun u => tensorFun f u y) ∧
      (∀ y, ∃ C, ∀ u, ‖tensorFun f u y‖ ≤ C) := by
  have e : ∀ y, (fun u => tensorFun f u y) = ⇑(fibreSchwartz f y) := fun y => by
    ext u; exact (fibreSchwartz_apply f y u).symm
  refine ⟨fun y => ?_, fun y => ?_, fun y => ?_⟩
  · rw [e y]; exact (fibreSchwartz f y).continuous.measurable
  · rw [e y]; exact (fibreSchwartz f y).integrable
  · obtain ⟨C, hC⟩ := schwartz_bounded (fibreSchwartz f y)
    exact ⟨C, fun u => by rw [← fibreSchwartz_apply f y u]; exact hC u⟩

/-- **Uniform weak type `(1,1)` of the truncated operators** (`σ^N`, any `N`), conditional on the scalar
bound `hT`.  `C = (2 + 2^{2s-1} A^s + 4 cH) B`. -/
theorem weak11_tensorMultTrunc_of_trunc {s A : ℝ} (hs : 1 < s) (hA : 0 ≤ A)
    (hT : TruncScalarStrong s A) (hσ : IsMikhlin 3 B σ) (hB : 0 < B) (N : ℕ)
    (f : ZMod P → 𝓢(ℝ, ℂ)) {t : ℝ} (ht : 0 < t) :
    volume {x : ℝ | t < yNorm s (fun y => multOp (symbolTrunc σ N) (⇑(fibreSchwartz f y)) x)} ≤
      ENNReal.ofReal ((2 + 2 ^ (2 * s - 1) * A ^ s + 4 * cH) * B / t) *
        ∫⁻ u, ENNReal.ofReal (yNorm s (tensorFun f u)) := by
  have hs0 : 0 < s := by linarith
  obtain ⟨hFm, hFi, hFb⟩ := tensorFun_fibre_facts f
  have hcH : 0 ≤ cH := by unfold cH; positivity
  set K : ℝ → ℂ := kernelTrunc σ N with hK
  set K' : ℝ → ℂ := fun x => (B : ℂ)⁻¹ * K x with hK'
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have hKc : Continuous K := continuous_kernelTrunc hσ N
  have hKc' : Continuous K' := continuous_const.mul hKc
  have hKm' : Measurable (Function.uncurry fun x u : ℝ => K' (x - u)) :=
    (hKc'.comp (continuous_fst.sub continuous_snd)).measurable
  have hKb0 : ∀ x, ‖K' x‖ ≤ B⁻¹ * ∫ ξ, ‖symbolTrunc σ N ξ‖ := fun x => by
    simp only [hK']
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
    exact mul_le_mul_of_nonneg_left (norm_kernelTrunc_le_integral hσ N x) (by positivity)
  have hKb' : ∀ x z : ℝ, ‖K' (x - z)‖ ≤ B⁻¹ * ∫ ξ, ‖symbolTrunc σ N ξ‖ := fun x z => hKb0 _
  -- Hörmander for `K'`
  have hH : ∀ c u ℓ : ℝ, |u - c| ≤ ℓ / 2 →
      ∫⁻ x in {x : ℝ | ℓ < |x - c|}, ‖K' (x - u) - K' (x - c)‖ₑ ≤ ENNReal.ofReal cH := by
    refine hH_of_centered (c0 := cH) (fun y => ?_)
    have hy := lintegral_kernelTrunc_sub_le hσ hB N y
    have e : ∀ x, ‖K' (x - y) - K' x‖ₑ = ENNReal.ofReal B⁻¹ * ‖K (x - y) - K x‖ₑ := by
      intro x
      simp only [hK']
      rw [← mul_sub, enorm_mul, enorm_inv_ofReal hB]
    simp_rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal B⁻¹ * ∫⁻ x in {x : ℝ | 2 * |y| < |x|}, ‖K (x - y) - K x‖ₑ
        ≤ ENNReal.ofReal B⁻¹ * ENNReal.ofReal (cH * B) := mul_le_mul' le_rfl hy
      _ = ENNReal.ofReal cH := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; field_simp
  -- scalar bound for `K'`
  have hScalar : ∀ h : ℝ → ℂ, Measurable h → Integrable h volume → (∃ C, ∀ u, ‖h u‖ ≤ C) →
      eLpNorm (kconv K' h) (ENNReal.ofReal s) volume ≤
        ENNReal.ofReal A * eLpNorm h (ENNReal.ofReal s) volume := by
    intro h hm hi hb
    have e : kconv K' h = (B : ℂ)⁻¹ • kconv K h := by
      ext x; simp only [kconv, kop, hK', Pi.smul_apply, smul_eq_mul]
      rw [← integral_const_mul]; congr 1; ext u; ring
    rw [e, eLpNorm_const_smul, enorm_inv_ofReal hB]
    calc ENNReal.ofReal B⁻¹ * eLpNorm (kconv K h) (ENNReal.ofReal s) volume
        ≤ ENNReal.ofReal B⁻¹ * (ENNReal.ofReal (A * B) * eLpNorm h (ENNReal.ofReal s) volume) :=
          mul_le_mul' le_rfl (hT B σ hσ N h hm hi hb)
      _ = ENNReal.ofReal A * eLpNorm h (ENNReal.ofReal s) volume := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2; field_simp
  have hGood : ∀ g : ℝ → ZMod P → ℂ, (∀ y, Measurable fun u => g u y) →
      (∀ y, Integrable fun u => g u y) → (∀ y, ∃ C, ∀ u, ‖g u y‖ ≤ C) →
      ∫⁻ x, ENNReal.ofReal (yNorm s (fun y => kconv K' (fun u => g u y) x)) ^ s ≤
        ENNReal.ofReal A ^ s * ∫⁻ u, ENNReal.ofReal (yNorm s (g u)) ^ s :=
    fun g hgm hgi hgb => hGood_of_scalar (K := fun x u => K' (x - u)) hs hKm' hKb' (A := A) hScalar g hgm hgi hgb
  have hw := weak11_of_kernel (K := fun x u => K' (x - u)) hs hKm' hKb' hA hcH hH hGood (tensorFun f) hFm hFi hFb
    (t := t / B) (by positivity)
  -- identify the sets
  have hrel : ∀ x, yNorm s (fun y => multOp (symbolTrunc σ N) (⇑(fibreSchwartz f y)) x) =
      B * yNorm s (fun y => kconv K' (fun u => tensorFun f u y) x) := by
    intro x
    have h1 : (fun y => multOp (symbolTrunc σ N) (⇑(fibreSchwartz f y)) x) =
        fun y => (B : ℂ) * kconv K' (fun u => tensorFun f u y) x := by
      ext y
      have hi : Integrable (⇑(fibreSchwartz f y)) volume := (fibreSchwartz f y).integrable
      rw [← kconv_kernelTrunc_eq hσ N hi x]
      have e : (fun u => tensorFun f u y) = ⇑(fibreSchwartz f y) := by
        ext u; exact (fibreSchwartz_apply f y u).symm
      rw [e]
      simp only [kconv, kop, hK']
      rw [← integral_const_mul]
      congr 1; ext u; field_simp; simp only [hK]; ring
    rw [h1, yNorm_const_mul (P := P) hs0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
  have hset : {x : ℝ | t < yNorm s (fun y => multOp (symbolTrunc σ N) (⇑(fibreSchwartz f y)) x)} =
      {x : ℝ | t / B < yNorm s (fun y => kconv K' (fun u => tensorFun f u y) x)} := by
    ext x
    simp only [mem_ofPred_eq, hrel x]
    rw [div_lt_iff₀ hB, mul_comm]
  rw [hset]
  refine hw.trans (le_of_eq ?_)
  congr 2
  field_simp

end Trunc

section Limit

variable {P : ℕ} [NeZero P] {σ : ℝ → ℂ} {B : ℝ}

/-- **Weak type `(1,1)` of `T_σ ⊗ Id` on tensor Schwartz functions, `B > 0`** (limit `N → ∞` of the
truncations; conditional on the scalar bound `hT`).  `C = 2 + 2^{2s-1} A^s + 4 cH`. -/
theorem weak11_tensorMult_of_trunc {s A : ℝ} (hs : 1 < s) (hA : 0 ≤ A)
    (hT : TruncScalarStrong s A) (hσ : IsMikhlin 3 B σ) (hB : 0 < B)
    (f : ZMod P → 𝓢(ℝ, ℂ)) {t : ℝ} (ht : 0 < t) :
    volume {x : ℝ | t < yNorm s (tensorMult σ f x)} ≤
      ENNReal.ofReal ((2 + 2 ^ (2 * s - 1) * A ^ s + 4 * cH) * B / t) *
        ∫⁻ u, ENNReal.ofReal (yNorm s (tensorFun f u)) := by
  have hs0 : 0 < s := by linarith
  set An : ℕ → Set ℝ := fun N => {x : ℝ | t <
    yNorm s (fun y => multOp (symbolTrunc σ N) (⇑(fibreSchwartz f y)) x)} with hAn
  have hbound : ∀ N, volume (An N) ≤ ENNReal.ofReal ((2 + 2 ^ (2 * s - 1) * A ^ s + 4 * cH) * B / t) *
      ∫⁻ u, ENNReal.ofReal (yNorm s (tensorFun f u)) := fun N =>
    weak11_tensorMultTrunc_of_trunc hs hA hT hσ hB N f ht
  have hlim : ∀ x, Tendsto (fun N : ℕ => yNorm s (fun y => multOp (symbolTrunc σ N)
      (⇑(fibreSchwartz f y)) x)) atTop (nhds (yNorm s (tensorMult σ f x))) := by
    intro x
    have e : tensorMult σ f x = fun y => multOp σ (⇑(fibreSchwartz f y)) x := by
      ext y; exact tensorMult_eq_multOp_fibreSchwartz hσ.isBoundedSymbol f x y
    rw [e]
    exact ((continuous_yNorm hs0).tendsto _).comp
      (tendsto_pi_nhds.2 fun y => tendsto_multOp_symbolTrunc hσ (fibreSchwartz f y) x)
  set Bn : ℕ → Set ℝ := fun n => ⋂ m, ⋂ (_ : n ≤ m), An m with hBn
  have hmono : Monotone Bn := by
    intro n n' hnn' x hx
    simp only [hBn, mem_iInter] at hx ⊢
    exact fun m hm => hx m (hnn'.trans hm)
  have hsub : {x : ℝ | t < yNorm s (tensorMult σ f x)} ⊆ ⋃ n, Bn n := by
    intro x hx
    have hev := (hlim x).eventually (lt_mem_nhds (show t < yNorm s (tensorMult σ f x) from hx))
    obtain ⟨n, hn⟩ := eventually_atTop.1 hev
    exact mem_iUnion.2 ⟨n, by simp only [hBn, mem_iInter]; exact fun m hm => hn m hm⟩
  calc volume {x : ℝ | t < yNorm s (tensorMult σ f x)} ≤ volume (⋃ n, Bn n) := measure_mono hsub
    _ = ⨆ n, volume (Bn n) := hmono.measure_iUnion
    _ ≤ _ := iSup_le fun n =>
        (measure_mono (fun x hx => by simp only [hBn, mem_iInter] at hx; exact hx n le_rfl)).trans
          (hbound n)

/-- If `B = 0` the multiplier vanishes a.e. and `T_σ ⊗ Id = 0`. -/
theorem tensorMult_eq_zero_of_B_zero (hσ : IsMikhlin 3 0 σ) (f : ZMod P → 𝓢(ℝ, ℂ)) (x : ℝ)
    (y : ZMod P) : tensorMult σ f x y = 0 := by
  have hb := hσ.isBoundedSymbol
  rw [tensorMult_eq_multOp_fibreSchwartz hb]
  unfold multOp
  rw [Real.fourierInv_eq_fourier_neg]
  have hae : (fun ξ => σ ξ * 𝓕 (⇑(fibreSchwartz f y)) ξ) =ᵐ[volume] fun _ => (0 : ℂ) := by
    filter_upwards [hb.ae_norm_le] with ξ hξ
    have : σ ξ = 0 := norm_le_zero_iff.1 hξ
    simp [this]
  rw [Real.fourier_congr_ae hae]
  simp [Real.fourier_eq]

theorem vectorMikhlinWeak_of_trunc {s A : ℝ} (hs : 1 < s) (hA : 0 ≤ A) (hT : TruncScalarStrong s A) :
    VectorMikhlinWeak 3 s (2 + 2 ^ (2 * s - 1) * A ^ s + 4 * cH) := by
  intro P _ B σ hσ f t ht
  have hs0 : 0 < s := by linarith
  have hcH : 0 ≤ cH := by unfold cH; positivity
  have hC : 0 ≤ 2 + 2 ^ (2 * s - 1) * A ^ s + 4 * cH := by positivity
  have hI : mixedENorm 1 s (tensorFun f) = ∫⁻ u, ENNReal.ofReal (yNorm s (tensorFun f u)) := by
    unfold mixedENorm
    have hm : AEStronglyMeasurable (fun x => yNorm s (tensorFun f x)) volume :=
      (measurable_yNorm s (tensorFun_fibre_facts f).1).aestronglyMeasurable
    rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm hm]
    refine lintegral_congr fun u => ?_
    rw [Real.enorm_eq_ofReal (yNorm_nonneg s _)]
  rw [hI]
  have hB0 := hσ.nonneg
  rcases hB0.eq_or_lt with hB | hB
  · -- `B = 0`
    subst hB
    have hz : {x : ℝ | t < yNorm s (tensorMult σ f x)} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      have : tensorMult σ f x = 0 := by
        ext y; exact tensorMult_eq_zero_of_B_zero hσ f x y
      rw [this, yNorm_zero' hs0]; exact ht.le
    rw [hz]; simp
  · have h := weak11_tensorMult_of_trunc hs hA hT hσ hB f ht
    calc ENNReal.ofReal t * volume {x : ℝ | t < yNorm s (tensorMult σ f x)}
        ≤ ENNReal.ofReal t * (ENNReal.ofReal ((2 + 2 ^ (2 * s - 1) * A ^ s + 4 * cH) * B / t) *
            ∫⁻ u, ENNReal.ofReal (yNorm s (tensorFun f u))) := mul_le_mul' le_rfl h
      _ = ENNReal.ofReal ((2 + 2 ^ (2 * s - 1) * A ^ s + 4 * cH) * B) *
            ∫⁻ u, ENNReal.ofReal (yNorm s (tensorFun f u)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul ht.le]
          congr 2; field_simp

end Limit

end PrimeBHT.TimeFrequency.X2.CZ
