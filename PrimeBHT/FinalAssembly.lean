module

public import PrimeBHT.Interpolation
public import PrimeBHT.Exponents

/-!
# S14: power-saving interpolation and the case `r ≥ 1` of the final assembly (N51)

* `interp_power`: bilinear interpolation (N60, `interp_bilinear_holder`) for bounds of the form
  `‖T f g‖_{rᵢ} ≤ Cᵢ Q^{αᵢ} ‖f‖_{pᵢ} ‖g‖_{qᵢ}`; the output is
  `C₀^{1-θ} C₁^θ Q^{(1-θ)α₀ + θα₁}`.
* `exists_power_saving_of_estimates`: the case `r ≥ 1` (blueprint N51), conditional on the
  `(2,2,1)` estimate with exponent `-1/20` and the progression estimate at every Banach tuple.
-/

public section

namespace PrimeBHT.FinalAssembly

open MeasureTheory
open scoped ENNReal

/-- The constant in `interp_power` after the exponents of `Q` have been collected. -/
theorem power_const_eq {Q C₀ C₁ α₀ α₁ θ : ℝ} (hQ : 0 < Q) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) :
    (C₀ * Q ^ α₀) ^ (1 - θ) * (C₁ * Q ^ α₁) ^ θ =
      C₀ ^ (1 - θ) * C₁ ^ θ * Q ^ ((1 - θ) * α₀ + θ * α₁) := by
  rw [Real.mul_rpow hC₀.le (Real.rpow_nonneg hQ.le _),
    Real.mul_rpow hC₁.le (Real.rpow_nonneg hQ.le _), ← Real.rpow_mul hQ.le,
    ← Real.rpow_mul hQ.le, Real.rpow_add hQ]
  rw [mul_comm α₀, mul_comm α₁]
  ring

/-- **Power-saving interpolation.** If `‖T f g‖_{rᵢ} ≤ Cᵢ Q^{αᵢ} ‖f‖_{pᵢ} ‖g‖_{qᵢ}` for `i = 0, 1`
(`Q > 0`, `Cᵢ > 0`, `1 ≤ pᵢ, qᵢ`, `1/rᵢ = 1/pᵢ + 1/qᵢ`), then at the interpolated exponents
`‖T f g‖_{r} ≤ C₀^{1-θ} C₁^θ Q^{(1-θ)α₀ + θα₁} ‖f‖_p ‖g‖_q`. -/
theorem interp_power
    (T : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ))
    {Q : ℝ} (hQ : 0 < Q)
    {p₀ p₁ q₀ q₁ r₀ r₁ C₀ C₁ α₀ α₁ θ p q r : ℝ}
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁)
    (hr₀ : 1 / r₀ = 1 / p₀ + 1 / q₀) (hr₁ : 1 / r₁ = 1 / p₁ + 1 / q₁)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (h₀ : ∀ f g : ℤ →₀ ℂ, eLpNorm (T f g) (ENNReal.ofReal r₀) Measure.count ≤
      ENNReal.ofReal (C₀ * Q ^ α₀) * eLpNorm f (ENNReal.ofReal p₀) Measure.count *
        eLpNorm g (ENNReal.ofReal q₀) Measure.count)
    (h₁ : ∀ f g : ℤ →₀ ℂ, eLpNorm (T f g) (ENNReal.ofReal r₁) Measure.count ≤
      ENNReal.ofReal (C₁ * Q ^ α₁) * eLpNorm f (ENNReal.ofReal p₁) Measure.count *
        eLpNorm g (ENNReal.ofReal q₁) Measure.count)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (hp : 1 / p = (1 - θ) / p₀ + θ / p₁)
    (hq : 1 / q = (1 - θ) / q₀ + θ / q₁) (hr : 1 / r = 1 / p + 1 / q) (f g : ℤ →₀ ℂ) :
    eLpNorm (T f g) (ENNReal.ofReal r) Measure.count ≤
      ENNReal.ofReal (C₀ ^ (1 - θ) * C₁ ^ θ * Q ^ ((1 - θ) * α₀ + θ * α₁)) *
        eLpNorm f (ENNReal.ofReal p) Measure.count *
        eLpNorm g (ENNReal.ofReal q) Measure.count := by
  have h := PrimeBHT.Interpolation.interp_bilinear_holder T hp₀ hp₁ hq₀ hq₁ hr₀ hr₁
    (mul_pos hC₀ (Real.rpow_pos_of_pos hQ _)) (mul_pos hC₁ (Real.rpow_pos_of_pos hQ _))
    h₀ h₁ hθ hp hq hr f g
  rwa [power_const_eq hQ hC₀ hC₁] at h

/-! ## The case `r ≥ 1` (blueprint N51) -/

open PrimeBHT.Exponents in
/-- **N51, the case `r ≥ 1`, conditional on (A) and (B).**

The family `T i` (`i` ranges over an arbitrary index type `ι`, e.g. pairs `(Q, J)` with `Q` dyadic,
so that constants are uniform in all other parameters) is indexed by the real parameter `Q i`.
Hypotheses:
* (A) the `(2,2,1)` estimate `‖T i f g‖_{ℓ¹} ≤ C_A (Q i)^{-1/20} ‖f‖₂ ‖g‖₂` for `Q i ≥ Q₀`
  (N51 steps 1-2: the moderate part from N12(b) summed over `≤ Q^{1/6}` scales, plus N26 at
  `τ = 1/6`; `-1/12 + 1/30 = -1/20`);
* (B) the progression estimate (N24) at every Banach tuple `(p₁, q₁, r₁)`
  (`1 < p₁, q₁`, `1/p₁ + 1/q₁ ≤ 1`, `1/r₁ = 1/p₁ + 1/q₁`) with loss `Q^ε` for every `ε > 0`
  (exponent `max{1/r₁ - 1, 0} = 0`).

Conclusion: for `(p, q, r) ∈ R` with `r ≥ 1` there are `σ > 0`, `C > 0`, `Q₁` with
`‖T i f g‖_{ℓ^r} ≤ C (Q i)^{-σ} ‖f‖_p ‖g‖_q` whenever `Q i ≥ Q₁`. -/
theorem exists_power_saving_of_estimates
    {ι : Type*} (T : ι → (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) (Q : ι → ℝ)
    {p q r : ℝ} (hR : InR p q r) (hr : 1 ≤ r)
    {C_A Q₀ : ℝ} (hCA : 0 < C_A)
    (hA : ∀ i, Q₀ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (T i f g) (ENNReal.ofReal 1) Measure.count ≤
        ENNReal.ofReal (C_A * Q i ^ (-(1 / 20 : ℝ))) *
          eLpNorm f (ENNReal.ofReal 2) Measure.count * eLpNorm g (ENNReal.ofReal 2) Measure.count)
    (hB : ∀ p₁ q₁ r₁ : ℝ, 1 < p₁ → 1 < q₁ → 1 / p₁ + 1 / q₁ ≤ 1 → 1 / r₁ = 1 / p₁ + 1 / q₁ →
      ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
        eLpNorm (T i f g) (ENNReal.ofReal r₁) Measure.count ≤
          ENNReal.ofReal (C * Q i ^ ε) *
            eLpNorm f (ENNReal.ofReal p₁) Measure.count *
              eLpNorm g (ENNReal.ofReal q₁) Measure.count) :
    ∃ σ C Q₁ : ℝ, 0 < σ ∧ 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (T i f g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ (-σ)) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count := by
  have hpq : 1 / p + 1 / q ≤ 1 := by
    rw [← hR.inv_r]
    exact (div_le_one hR.pos_r).2 hr
  obtain ⟨θ₁, p₁, q₁, r₁, hθ0, hθ1, hp₁, hq₁, hr₁, hr₁eq, e1, e2, -⟩ :=
    exists_banach_partner hR.one_lt_p hR.one_lt_q hpq
  have hr₁pos : 0 < r₁ := lt_of_lt_of_le zero_lt_one hr₁
  have hsum : 1 / p₁ + 1 / q₁ ≤ 1 := by
    rw [← hr₁eq]
    exact (div_le_one hr₁pos).2 hr₁
  obtain ⟨hε, hσ, hexp⟩ := power_saving hθ0 hθ1
  obtain ⟨C₁, Q₁, hC₁, hB'⟩ := hB p₁ q₁ r₁ hp₁ hq₁ hsum hr₁eq _ hε
  refine ⟨(1 - θ₁) / 40, C_A ^ (1 - θ₁) * C₁ ^ θ₁, max (max Q₀ Q₁) 1, hσ,
    mul_pos (Real.rpow_pos_of_pos hCA _) (Real.rpow_pos_of_pos hC₁ _), ?_⟩
  intro i hi f g
  have hQ : 0 < Q i := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hi)
  have hQ₀ : Q₀ ≤ Q i := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hi
  have hQ₁ : Q₁ ≤ Q i := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hi
  have h := interp_power (T i) hQ (p₀ := 2) (p₁ := p₁) (q₀ := 2) (q₁ := q₁) (r₀ := 1) (r₁ := r₁)
    (C₀ := C_A) (C₁ := C₁) (α₀ := -(1 / 20 : ℝ)) (α₁ := (1 - θ₁) / (40 * θ₁)) (θ := θ₁)
    (p := p) (q := q) (r := r) (by norm_num) hp₁.le (by norm_num) hq₁.le (by norm_num) hr₁eq
    hCA hC₁ (hA i hQ₀) (hB' i hQ₁) ⟨hθ0, hθ1⟩ (by rw [e1]; ring) (by rw [e2]; ring) hR.inv_r f g
  have hex : (1 - θ₁) * (-(1 / 20 : ℝ)) + θ₁ * ((1 - θ₁) / (40 * θ₁)) = -((1 - θ₁) / 40) := by
    linear_combination hexp
  rwa [hex] at h

/-! ## The auxiliary tuple of N50 and the first interpolation of the case `r < 1` (N52 (A), (B)) -/

section ExponentData

open PrimeBHT.Exponents

variable {p q r : ℝ}

/-- The interpolation weight `θ` of `ExponentData` lies in `(0,1)`. -/
theorem exponentData_theta_mem (D : ExponentData p q r) : D.θ ∈ Set.Ioo (0 : ℝ) 1 := by
  have h1 := D.θ_gt
  have h2 := D.θ_lt
  have ht := D.t_pos
  have h3 : D.θ < 1 - 2 * D.t := lt_of_lt_of_le h2 (min_le_right _ _)
  constructor <;> linarith

/-- `1/r = 1/p + 1/q` for the target of an `ExponentData` (it is the interpolation of
`1/p₀ + 1/q₀ = 1/r₀` and `1/2 + 1/2 = 1`). -/
theorem exponentData_inv_r (D : ExponentData p q r) : 1 / r = 1 / p + 1 / q := by
  have h1 := D.interp_p
  have h2 := D.interp_q
  have h3 := D.interp_r
  have h4 := D.inv_p₀_add_inv_q₀
  have h5 := D.t_eq
  linear_combination h1 + h2 - (1 - D.θ) * h4 - h3 - h5

/-- `(1 - θ) (1/r₀ - 1) = t` (P3). -/
theorem exponentData_one_sub_theta_mul (D : ExponentData p q r) :
    (1 - D.θ) * (1 / D.r₀ - 1) = D.t := by
  have h1 : 1 - D.θ ≠ 0 := (sub_pos.2 (exponentData_theta_mem D).2).ne'
  have h2 := D.inv_r₀_eq
  rw [h2]
  field_simp
  ring

/-- Power-saving interpolation between the auxiliary tuple `(p₀, q₀, r₀)` (weight `1 - θ`) and
`(2, 2, 1)` (weight `θ`) of `ExponentData`, for a single operator at a single `Q > 0`
(N52 (A), (B)). -/
theorem interp_power_exponentData (D : ExponentData p q r)
    (T : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) {Q C₀ C₁ α₀ α₁ : ℝ} (hQ : 0 < Q)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (h₀ : ∀ f g : ℤ →₀ ℂ, eLpNorm (T f g) (ENNReal.ofReal D.r₀) Measure.count ≤
      ENNReal.ofReal (C₀ * Q ^ α₀) * eLpNorm f (ENNReal.ofReal D.p₀) Measure.count *
        eLpNorm g (ENNReal.ofReal D.q₀) Measure.count)
    (h₁ : ∀ f g : ℤ →₀ ℂ, eLpNorm (T f g) (ENNReal.ofReal 1) Measure.count ≤
      ENNReal.ofReal (C₁ * Q ^ α₁) * eLpNorm f (ENNReal.ofReal 2) Measure.count *
        eLpNorm g (ENNReal.ofReal 2) Measure.count)
    (f g : ℤ →₀ ℂ) :
    eLpNorm (T f g) (ENNReal.ofReal r) Measure.count ≤
      ENNReal.ofReal (C₀ ^ (1 - D.θ) * C₁ ^ D.θ * Q ^ ((1 - D.θ) * α₀ + D.θ * α₁)) *
        eLpNorm f (ENNReal.ofReal p) Measure.count *
          eLpNorm g (ENNReal.ofReal q) Measure.count :=
  interp_power T hQ D.one_lt_p₀.le (by norm_num) D.one_lt_q₀.le (by norm_num)
    D.inv_p₀_add_inv_q₀.symm (by norm_num) hC₀ hC₁ h₀ h₁ (exponentData_theta_mem D)
    (by rw [← D.interp_p]; ring) (by rw [← D.interp_q]; ring) (exponentData_inv_r D) f g

/-- Interpolation of two estimates with `ε`-losses, at the pair `(p₀, q₀, r₀)` of `ExponentData`
with exponent `α₀ + ε` and at `(2, 2, 1)` with exponent `α₁ + ε`: the interpolated estimate at
`(p, q, r)` has exponent `(1 - θ) α₀ + θ α₁ + ε`. -/
theorem interp_epsilon_of_estimates {ι : Type*}
    (T : ι → (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) (Q : ι → ℝ)
    (D : ExponentData p q r) (α₀ α₁ : ℝ)
    (h₀ : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (T i f g) (ENNReal.ofReal D.r₀) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ (α₀ + ε)) * eLpNorm f (ENNReal.ofReal D.p₀) Measure.count *
          eLpNorm g (ENNReal.ofReal D.q₀) Measure.count)
    (h₁ : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (T i f g) (ENNReal.ofReal 1) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ (α₁ + ε)) * eLpNorm f (ENNReal.ofReal 2) Measure.count *
          eLpNorm g (ENNReal.ofReal 2) Measure.count) :
    ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (T i f g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ ((1 - D.θ) * α₀ + D.θ * α₁ + ε)) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count := by
  intro ε hε
  obtain ⟨C₀, Qa, hC₀, ha⟩ := h₀ ε hε
  obtain ⟨C₁, Qb, hC₁, hb⟩ := h₁ ε hε
  have hθ := exponentData_theta_mem D
  refine ⟨C₀ ^ (1 - D.θ) * C₁ ^ D.θ, max (max Qa Qb) 1,
    mul_pos (Real.rpow_pos_of_pos hC₀ _) (Real.rpow_pos_of_pos hC₁ _), ?_⟩
  intro i hi f g
  have hQ : 0 < Q i := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hi)
  have hQa : Qa ≤ Q i := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hi
  have hQb : Qb ≤ Q i := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hi
  have h := interp_power_exponentData D (T i) hQ hC₀ hC₁ (ha i hQa) (hb i hQb) f g
  have hex : (1 - D.θ) * (α₀ + ε) + D.θ * (α₁ + ε) = (1 - D.θ) * α₀ + D.θ * α₁ + ε := by ring
  rwa [hex] at h

/-- **N52 (A), `eq:singlecomplexitylongquasibanach`, conditional on its two inputs.**
From `‖U_Q‖_{2,2→1} ≲ Q^{-3/8+ε}` (N26 at `τ = 3/4`) and `‖U_Q‖_{p₀,q₀→r₀} ≲ Q^{1/r₀-1+ε}`
(N24 at the auxiliary tuple, `r₀ ∈ (2/3, 1)`), for every `ε > 0`, one gets
`‖U_Q‖_{p,q→r} ≲ Q^{t - 3θ/8 + ε}`, where `t - 3θ/8 < 0` is `D.E_U_neg`. -/
theorem power_decay_quasiBanach_of_estimates {ι : Type*}
    (T : ι → (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) (Q : ι → ℝ)
    (D : ExponentData p q r)
    (hU : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (T i f g) (ENNReal.ofReal 1) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ (-(3 / 8 : ℝ) + ε)) * eLpNorm f (ENNReal.ofReal 2) Measure.count *
          eLpNorm g (ENNReal.ofReal 2) Measure.count)
    (hP : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (T i f g) (ENNReal.ofReal D.r₀) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ (1 / D.r₀ - 1 + ε)) *
          eLpNorm f (ENNReal.ofReal D.p₀) Measure.count *
            eLpNorm g (ENNReal.ofReal D.q₀) Measure.count) :
    ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (T i f g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ (D.t - 3 * D.θ / 8 + ε)) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count := by
  intro ε hε
  obtain ⟨C, Q₁, hC, h⟩ := interp_epsilon_of_estimates T Q D (1 / D.r₀ - 1) (-(3 / 8 : ℝ)) hP hU ε hε
  have hex : (1 - D.θ) * (1 / D.r₀ - 1) + D.θ * (-(3 / 8 : ℝ)) + ε = D.t - 3 * D.θ / 8 + ε := by
    have := exponentData_one_sub_theta_mul D
    linear_combination this
  rw [hex] at h
  exact ⟨C, Q₁, hC, h⟩

/-- **N52 (B), the initial group, conditional on its two inputs.** From N12(a) at `(p₀, q₀, r₀)`
(exponent `ε`) and N12(b) at `(2, 2, 1)` (exponent `-1/4 + ε`) one gets
`‖T_k^Q‖_{p,q→r} ≲ Q^{-θ/4 + ε}`. -/
theorem single_scale_power_decay_of_estimates {ι : Type*}
    (T : ι → (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) (Q : ι → ℝ)
    (D : ExponentData p q r)
    (hL : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (T i f g) (ENNReal.ofReal 1) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ (-(1 / 4 : ℝ) + ε)) * eLpNorm f (ENNReal.ofReal 2) Measure.count *
          eLpNorm g (ENNReal.ofReal 2) Measure.count)
    (hP : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (T i f g) (ENNReal.ofReal D.r₀) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ ε) *
          eLpNorm f (ENNReal.ofReal D.p₀) Measure.count *
            eLpNorm g (ENNReal.ofReal D.q₀) Measure.count) :
    ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (T i f g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ (-(D.θ / 4) + ε)) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count := by
  intro ε hε
  have hP' : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (T i f g) (ENNReal.ofReal D.r₀) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ ((0 : ℝ) + ε)) *
          eLpNorm f (ENNReal.ofReal D.p₀) Measure.count *
            eLpNorm g (ENNReal.ofReal D.q₀) Measure.count := by
    intro ε hε
    simpa only [zero_add] using hP ε hε
  obtain ⟨C, Q₁, hC, h⟩ := interp_epsilon_of_estimates T Q D 0 (-(1 / 4 : ℝ)) hP' hL ε hε
  have hex : (1 - D.θ) * 0 + D.θ * (-(1 / 4 : ℝ)) + ε = -(D.θ / 4) + ε := by ring
  rw [hex] at h
  exact ⟨C, Q₁, hC, h⟩

end ExponentData

end PrimeBHT.FinalAssembly
