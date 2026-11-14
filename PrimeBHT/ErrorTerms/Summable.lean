module

public import PrimeBHT.ErrorTerms.L2
public import PrimeBHT.ErrorTerms.Rough
public import PrimeBHT.FinalAssembly

/-!
# N20 (c), `e:error-summable`, conditional on X3

For `1 < p, q`, `1/r = 1/p + 1/q` and every `A' ≥ 0` (in particular `A' = 100`):
`‖S_k^err(f,g)‖_{ℓ^r} ≤ C k^{-A'} ‖f‖_p ‖g‖_q` for all `k ≥ 1` and finitely supported `f, g`.

Proof (blueprint N20 (c)).  The reciprocal tuple `(a,b) = (1/p, 1/q)` lies in `(0,1)^2`; with
`c = (1/4,1/4)` there is `λ > 1` with `P₁ = c + λ((a,b) - c) ∈ (0,1)^2`
(`exists_aux_tuple`, openness).  Put `θ = 1/λ`, `(1/p₁, 1/q₁) = P₁`, `1/r₁ = 1/p₁ + 1/q₁`; then
`(a,b) = (1-θ) c + θ P₁` and `1/r = (1-θ)/2 + θ/r₁`.  N60 (`FinalAssembly.interp_power`) between
`(4,4,2)` with constant `C_A k^{-A}` (`eLpNorm_Serr_le_of_X3`) and `(p₁,q₁,r₁)` with constant
`C₁ k^{B₁}` (`eLpNorm_Serr_rough`, unconditional) gives `k^{-A(1-θ) + B₁θ}`; `A` is chosen after `B₁`.
-/

@[expose] public section

open MeasureTheory Finset Filter Topology
open scoped ENNReal

namespace PrimeBHT.ErrorTerms

open PrimeBHT.Kernel PrimeBHT.Decomposition PrimeBHT.SingleScaleL1 PrimeBHT.FinalAssembly
  PrimeCarleson

/-! ### `S_k^err` as a bilinear map -/

/-- `S_k^err` as a bilinear map on finitely supported sequences. -/
noncomputable def errOp (χ : ℝ → ℝ) (k : ℕ) :
    (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ) :=
  bilinOp (Finset.Icc (-((2 ^ k : ℕ) : ℤ)) ((2 ^ k : ℕ) : ℤ))
    (fun n => ((psiK χ k n : ℝ) : ℂ) * E k n)

lemma errOp_apply {χ : ℝ → ℝ} (hχ : IsCutoff χ) (k : ℕ) (f g : ℤ →₀ ℂ) :
    errOp χ k f g = Serr χ k ⇑f ⇑g := by
  refine (bilinOp_eq_bilin (fun n hn => ?_) f g).trans (Serr_eq_bilin k _ _).symm
  rw [psiK_eq_zero_of_notMem_Icc hχ k hn]
  simp

/-! ### The auxiliary tuple -/

/-- Every `(a, b) ∈ (0,1)²` is an interior point seen from `(1/4, 1/4)`: there are `θ ∈ (0,1)` and
`(a₁, b₁) ∈ (0,1)²` with `(a, b) = (1-θ)(1/4,1/4) + θ (a₁, b₁)`. -/
lemma exists_aux_tuple {a b : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ θ a₁ b₁ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 ∧ a₁ ∈ Set.Ioo (0 : ℝ) 1 ∧ b₁ ∈ Set.Ioo (0 : ℝ) 1 ∧
      a = (1 - θ) / 4 + θ * a₁ ∧ b = (1 - θ) / 4 + θ * b₁ := by
  have hev : ∀ d : ℝ, 1 / 4 + d ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ᶠ y : ℝ in 𝓝 1, 1 / 4 + y * d ∈ Set.Ioo (0 : ℝ) 1 := by
    intro d hd
    have hc : Continuous fun y : ℝ => 1 / 4 + y * d := by fun_prop
    refine hc.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds ?_)
    simpa using hd
  have hda : 1 / 4 + (a - 1 / 4) ∈ Set.Ioo (0 : ℝ) 1 := by simpa using ha
  have hdb : 1 / 4 + (b - 1 / 4) ∈ Set.Ioo (0 : ℝ) 1 := by simpa using hb
  have h1 : ∀ᶠ y : ℝ in 𝓝[>] 1, (1 / 4 + y * (a - 1 / 4) ∈ Set.Ioo (0 : ℝ) 1 ∧
      1 / 4 + y * (b - 1 / 4) ∈ Set.Ioo (0 : ℝ) 1) ∧ y ∈ Set.Ioi (1 : ℝ) :=
    (((hev _ hda).and (hev _ hdb)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨y, ⟨hya, hyb⟩, hy1⟩ := h1.exists
  have hy : (1 : ℝ) < y := hy1
  have hy0 : 0 < y := by linarith
  refine ⟨1 / y, 1 / 4 + y * (a - 1 / 4), 1 / 4 + y * (b - 1 / 4), ⟨by positivity, ?_⟩, hya, hyb,
    ?_, ?_⟩
  · rw [div_lt_one hy0]; exact hy
  · field_simp
    ring
  · field_simp
    ring

/-! ### The main estimate -/

/-- **N20 (c), `e:error-summable`, conditional on X3**: for `1 < p, q`, `1/r = 1/p + 1/q` and every
`A'` there is `C` with `‖S_k^err(f,g)‖_{ℓ^r} ≤ C k^{-A'} ‖f‖_p ‖g‖_q` for all `k ≥ 1` and finitely
supported `f, g`. -/
theorem eLpNorm_Serr_le_k_rpow_of_X3 (hX3 : X3Statement) {χ : ℝ → ℝ} (hχ : IsCutoff χ)
    {p q r : ℝ} (hp : 1 < p) (hq : 1 < q) (hr : 1 / r = 1 / p + 1 / q) (A' : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (Serr χ k ⇑f ⇑g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * (k : ℝ) ^ (-A')) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count *
          eLpNorm (⇑g) (ENNReal.ofReal q) Measure.count := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have ha : 1 / p ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_lt_one hp0]; exact hp⟩
  have hb : 1 / q ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_lt_one hq0]; exact hq⟩
  obtain ⟨θ, a₁, b₁, hθ, ha₁, hb₁, hpa, hqb⟩ := exists_aux_tuple ha hb
  obtain ⟨hθ0, hθ1⟩ := hθ
  -- the auxiliary tuple
  set p₁ : ℝ := 1 / a₁ with hp₁
  set q₁ : ℝ := 1 / b₁ with hq₁
  set r₁ : ℝ := 1 / (a₁ + b₁) with hr₁
  have hp₁1 : 1 < p₁ := by rw [hp₁, lt_div_iff₀ ha₁.1]; linarith [ha₁.2]
  have hq₁1 : 1 < q₁ := by rw [hq₁, lt_div_iff₀ hb₁.1]; linarith [hb₁.2]
  have hr₁eq : 1 / r₁ = 1 / p₁ + 1 / q₁ := by
    rw [hr₁, hp₁, hq₁, one_div_one_div, one_div_one_div, one_div_one_div]
  have hr₁pos : 0 < r₁ := by rw [hr₁]; have := ha₁.1; have := hb₁.1; positivity
  -- the rough bound at the auxiliary tuple
  obtain ⟨B₁, C₁, hB₁, hC₁, hrough⟩ := eLpNorm_Serr_rough hχ hp₁1 hq₁1 hr₁eq
  -- choose the decay exponent after `B₁`
  set A : ℝ := max 1 ((A' + θ * B₁) / (1 - θ)) with hA
  have hA1 : 1 ≤ A := le_max_left _ _
  have h1θ : 0 < 1 - θ := by linarith
  have hAθ : A' + θ * B₁ ≤ (1 - θ) * A := by
    have : (A' + θ * B₁) / (1 - θ) ≤ A := le_max_right _ _
    rw [div_le_iff₀ h1θ] at this
    linarith
  obtain ⟨C₀, hC₀, hL2⟩ := eLpNorm_Serr_le_of_X3 hX3 hχ hA1
  refine ⟨(C₀ + 1) ^ (1 - θ) * (C₁ + 1) ^ θ, by positivity, fun k hk f g => ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  rw [← errOp_apply hχ k f g]
  have hmain := interp_power (errOp χ k) hk0 (p₀ := 4) (p₁ := p₁) (q₀ := 4) (q₁ := q₁)
    (r₀ := 2) (r₁ := r₁) (C₀ := C₀ + 1) (C₁ := C₁ + 1) (α₀ := -A) (α₁ := B₁) (θ := θ)
    (p := p) (q := q) (r := r) (by norm_num) hp₁1.le (by norm_num) hq₁1.le (by norm_num) hr₁eq
    (by linarith) (by linarith) ?_ ?_ ⟨hθ0, hθ1⟩ ?_ ?_ hr f g
  · refine hmain.trans ?_
    have hexp : (k : ℝ) ^ ((1 - θ) * (-A) + θ * B₁) ≤ (k : ℝ) ^ (-A') :=
      Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
    have hnn : 0 ≤ (C₀ + 1) ^ (1 - θ) * (C₁ + 1) ^ θ := by positivity
    have : (C₀ + 1) ^ (1 - θ) * (C₁ + 1) ^ θ * (k : ℝ) ^ ((1 - θ) * (-A) + θ * B₁) ≤
        (C₀ + 1) ^ (1 - θ) * (C₁ + 1) ^ θ * (k : ℝ) ^ (-A') :=
      mul_le_mul_of_nonneg_left hexp hnn
    gcongr
  · intro f g
    rw [errOp_apply hχ k f g]
    simp only [ENNReal.ofReal_ofNat] at hL2 ⊢
    refine (hL2 k hk f g).trans ?_
    have hk' : (0 : ℝ) ≤ (k : ℝ) ^ (-A) := Real.rpow_nonneg hk0.le _
    have : C₀ * (k : ℝ) ^ (-A) ≤ (C₀ + 1) * (k : ℝ) ^ (-A) :=
      mul_le_mul_of_nonneg_right (by linarith) hk'
    gcongr
  · intro f g
    rw [errOp_apply hχ k f g]
    refine (hrough k hk f g).trans ?_
    have hk' : (0 : ℝ) ≤ (k : ℝ) ^ B₁ := Real.rpow_nonneg hk0.le _
    have : C₁ * (k : ℝ) ^ B₁ ≤ (C₁ + 1) * (k : ℝ) ^ B₁ :=
      mul_le_mul_of_nonneg_right (by linarith) hk'
    gcongr
  · rw [hpa, hp₁, div_div_eq_mul_div, div_one]
  · rw [hqb, hq₁, div_div_eq_mul_div, div_one]

/-- **N20 (c), `e:error-summable`, conditional on X3**: the decay `k^{-100}`. -/
theorem eLpNorm_Serr_le_k_pow_of_X3 (hX3 : X3Statement) {χ : ℝ → ℝ} (hχ : IsCutoff χ)
    {p q r : ℝ} (hp : 1 < p) (hq : 1 < q) (hr : 1 / r = 1 / p + 1 / q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (Serr χ k ⇑f ⇑g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * (k : ℝ) ^ (-(100 : ℝ))) * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count *
          eLpNorm (⇑g) (ENNReal.ofReal q) Measure.count :=
  eLpNorm_Serr_le_k_rpow_of_X3 hX3 hχ hp hq hr 100

end PrimeBHT.ErrorTerms
