module

public import PrimeBHT.Kernel
public import PrimeBHT.SingleScale
public import PrimeBHT.Interpolation

/-!
# N12 (b), `e:single-L1`: packaging and interpolation (stage (b))

* `PrimeBHT.SingleScaleL1.weight χ Q k n = ψ_k(n) w_Q(n)` (the coefficient of `T_k^Q`).
* `PrimeBHT.SingleScaleL1.bilinOp S a`: the bilinear operator `(f, g) ↦ ∑_{n ∈ S} a n f(x-n) g(x+n)`
  as a bilinear `LinearMap` on `ℤ →₀ ℂ`; it agrees with `bilin a` when `a` vanishes off `S`.
* `interp_442`: N60 at the endpoints `(4,4,2)` and `(u,u,u/2)` landing at `(2,2,1)`,
  `θ_u = u/(4-u)`.
* `eLpNorm_single_L1_of_442`: from the `(4,4,2)` estimate with `M₀ = C Q^{δ-3/8}` (hypothesis `h442`)
  and the rough bound at `(u,u,u/2)`, the `ℓ²×ℓ² → ℓ¹` bound `C_ε Q^{-1/4+ε}`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace PrimeBHT.SingleScaleL1

open PrimeBHT.Kernel PrimeBHT.SingleScale PrimeBHT.Interpolation PrimeCarleson

/-- The coefficient `n ↦ ψ_k(n) w_Q(n)` of the single-scale operator `T_k^Q`. -/
noncomputable abbrev weight (χ : ℝ → ℝ) (Q k : ℕ) : ℤ → ℂ :=
  fun n => ((psiK χ k n : ℝ) : ℂ) * blockWeight (Finset.Ioc (Q / 2) Q) n

/-- The bilinear operator `(f, g) ↦ (x ↦ ∑_{n ∈ S} a n f(x-n) g(x+n))` on finitely supported
sequences, as a bilinear map. -/
noncomputable def bilinOp (S : Finset ℤ) (a : ℤ → ℂ) :
    (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ) :=
  LinearMap.mk₂ ℂ (fun f g x => ∑ n ∈ S, a n * f (x - n) * g (x + n))
    (fun f₁ f₂ g => by
      funext x
      simp only [Finsupp.coe_add, Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring)
    (fun c f g => by
      funext x
      simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring)
    (fun f g₁ g₂ => by
      funext x
      simp only [Finsupp.coe_add, Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring)
    (fun c f g => by
      funext x
      simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring)

lemma bilinOp_apply (S : Finset ℤ) (a : ℤ → ℂ) (f g : ℤ →₀ ℂ) (x : ℤ) :
    bilinOp S a f g x = ∑ n ∈ S, a n * f (x - n) * g (x + n) := rfl

lemma bilinOp_eq_bilin {S : Finset ℤ} {a : ℤ → ℂ} (ha : ∀ n ∉ S, a n = 0) (f g : ℤ →₀ ℂ) :
    bilinOp S a f g = bilin a ⇑f ⇑g := by
  funext x
  rw [bilinOp_apply]
  unfold bilin
  exact (tsum_eq_sum (fun n hn => by rw [ha n hn]; simp)).symm

/-- `ψ_k(n) w_Q(n)` vanishes for `|n| ≥ 2^k`. -/
lemma weight_eq_zero {χ : ℝ → ℝ} (hχ : IsCutoff χ) (Q k : ℕ) {n : ℤ}
    (hn : n ∉ Finset.Icc (-((2 ^ k : ℕ) : ℤ)) ((2 ^ k : ℕ) : ℤ)) : weight χ Q k n = 0 := by
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
  have hLeq : (((2 ^ k : ℕ) : ℤ) : ℝ) = 2 ^ k := by push_cast; rfl
  have hle : (2 : ℝ) ^ k ≤ |(n : ℝ)| := by
    rw [← hLeq]
    rcases hn with h | h
    · have : ((n : ℤ) : ℝ) < -(((2 ^ k : ℕ) : ℤ) : ℝ) := by exact_mod_cast h
      have hp : (0 : ℝ) < (((2 ^ k : ℕ) : ℤ) : ℝ) := by rw [hLeq]; positivity
      rw [abs_of_neg (by linarith)]; linarith
    · have : (((2 ^ k : ℕ) : ℤ) : ℝ) < (n : ℝ) := by exact_mod_cast h
      have hp : (0 : ℝ) < (((2 ^ k : ℕ) : ℤ) : ℝ) := by rw [hLeq]; positivity
      rw [abs_of_pos (by linarith)]; linarith
  show ((psiK χ k n : ℝ) : ℂ) * blockWeight (Finset.Ioc (Q / 2) Q) n = 0
  rw [hχ.psiK_eq_zero_of_le_abs k hle]
  simp

/-- The operator `T_k^Q` as a bilinear map. -/
noncomputable def single (χ : ℝ → ℝ) (Q k : ℕ) : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ) :=
  bilinOp (Finset.Icc (-((2 ^ k : ℕ) : ℤ)) ((2 ^ k : ℕ) : ℤ)) (weight χ Q k)

lemma single_apply {χ : ℝ → ℝ} (hχ : IsCutoff χ) (Q k : ℕ) (f g : ℤ →₀ ℂ) :
    single χ Q k f g = bilin (weight χ Q k) ⇑f ⇑g :=
  bilinOp_eq_bilin (fun _ hn => weight_eq_zero hχ Q k hn) f g

/-! ### The interpolation step -/

/-- N60 at `(4,4,2)` and `(u,u,u/2)` with weight `θ_u = u/(4-u)` on the second endpoint, landing at
`(2,2,1)`. -/
theorem interp_442 (T : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) {u M₀ M₁ : ℝ} (hu1 : 1 < u)
    (hu2 : u < 2) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₀ : ∀ f g : ℤ →₀ ℂ, eLpNorm (T f g) (ENNReal.ofReal 2) Measure.count ≤
      ENNReal.ofReal M₀ * eLpNorm f (ENNReal.ofReal 4) Measure.count *
        eLpNorm g (ENNReal.ofReal 4) Measure.count)
    (h₁ : ∀ f g : ℤ →₀ ℂ, eLpNorm (T f g) (ENNReal.ofReal (u / 2)) Measure.count ≤
      ENNReal.ofReal M₁ * eLpNorm f (ENNReal.ofReal u) Measure.count *
        eLpNorm g (ENNReal.ofReal u) Measure.count) (f g : ℤ →₀ ℂ) :
    eLpNorm (T f g) (ENNReal.ofReal 1) Measure.count ≤
      ENNReal.ofReal (M₀ ^ (1 - u / (4 - u)) * M₁ ^ (u / (4 - u))) *
        eLpNorm f (ENNReal.ofReal 2) Measure.count * eLpNorm g (ENNReal.ofReal 2) Measure.count := by
  have h4u : 0 < 4 - u := by linarith
  have hθ : u / (4 - u) ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨div_pos (by linarith) h4u, ?_⟩
    rw [div_lt_one h4u]; linarith
  have hpq : 1 / (2 : ℝ) = (1 - u / (4 - u)) / 4 + u / (4 - u) / u := by
    field_simp
    ring
  have hr : 1 / (1 : ℝ) = (1 - u / (4 - u)) / 2 + u / (4 - u) / (u / 2) := by
    field_simp
    ring
  exact interp_bilinear T (by norm_num) (by linarith) (by norm_num) (by linarith) (by norm_num)
    (by positivity) hM₀ hM₁ h₀ h₁ hθ hpq hpq hr f g

/-! ### Real arithmetic of the exponents -/

/-- The choice of the interpolation parameter: `u = 1 + min(1/2, ε)`, so `1 < u < 2`,
`u - 1 ≤ ε`. -/
lemma exponent_aux {u ε : ℝ} (hε : 0 < ε) (hu : u = 1 + min (1 / 2) ε) :
    1 < u ∧ u < 2 ∧ u - 1 ≤ ε := by
  have h1 : min (1 / 2 : ℝ) ε ≤ 1 / 2 := min_le_left _ _
  have h2 : min (1 / 2 : ℝ) ε ≤ ε := min_le_right _ _
  have h3 : 0 < min (1 / 2 : ℝ) ε := lt_min (by norm_num) hε
  refine ⟨by linarith, by linarith, by linarith⟩

/-- `1 - θ_u = 2(2-u)/(4-u) ≥ (2/3)(2-u)`, and `≤ 1`. -/
lemma one_sub_theta {u : ℝ} (hu1 : 1 < u) (hu2 : u < 2) :
    1 - u / (4 - u) = 2 * (2 - u) / (4 - u) ∧ 2 / 3 * (2 - u) ≤ 2 * (2 - u) / (4 - u) ∧
      2 * (2 - u) / (4 - u) ≤ 1 := by
  have h4u : 0 < 4 - u := by linarith
  refine ⟨by field_simp; ring, ?_, ?_⟩
  · rw [le_div_iff₀ h4u]
    nlinarith
  · rw [div_le_one h4u]; linarith

/-- The exponent bound: `(ε/4 - 3/8) κ + ε/4 ≤ -1/4 + ε`, for `κ = 2(2-u)/(4-u)`, `u - 1 ≤ ε`. -/
lemma exponent_le {u ε κ : ℝ} (hε : 0 < ε) (hu1 : 1 < u) (hu2 : u < 2) (hu : u - 1 ≤ ε)
    (hκ1 : 2 / 3 * (2 - u) ≤ κ) (hκ2 : κ ≤ 1) :
    (ε / 4 - 3 / 8) * κ + ε / 4 ≤ -1 / 4 + ε := by
  have hκ0 : 0 ≤ κ := le_trans (by nlinarith) hκ1
  nlinarith

/-! ### From the `(4,4,2)` estimate to the `ℓ¹` estimate -/

/-- **N12 (b), conditional on the `(4,4,2)` estimate** `h442`: the `(4,4,2)` estimate of the form
`M₀ = C Q^{δ-3/8}` for `Q ≥ 1` with `Q^{20} ≤ 2^k` (this is `l:U3maxmod` (c) combined with the
`U³` bound for `w_Q`) implies, via N60 and the rough bound at `(u,u,u/2)`, the bound
`‖T_k^Q(f,g)‖_{ℓ¹} ≤ C_ε Q^{-1/4+ε} ‖f‖_{ℓ²} ‖g‖_{ℓ²}`. -/
theorem eLpNorm_single_L1_of_442 {χ : ℝ → ℝ} (hχ : IsCutoff χ)
    (h442 : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q k : ℕ), 1 ≤ Q → (Q : ℝ) ^ 20 ≤ 2 ^ k →
      ∀ f g : ℤ →₀ ℂ, eLpNorm (bilin (weight χ Q k) ⇑f ⇑g) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal (C * (Q : ℝ) ^ (δ - 3 / 8)) *
          eLpNorm f (ENNReal.ofReal 4) Measure.count * eLpNorm g (ENNReal.ofReal 4) Measure.count)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q k : ℕ), 1 ≤ Q → (Q : ℝ) ^ 20 ≤ 2 ^ k → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (bilin (weight χ Q k) ⇑f ⇑g) (ENNReal.ofReal 1) Measure.count ≤
        ENNReal.ofReal (C * (Q : ℝ) ^ (-1 / 4 + ε)) *
          eLpNorm f (ENNReal.ofReal 2) Measure.count * eLpNorm g (ENNReal.ofReal 2) Measure.count := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 + min (1 / 2) ε := ⟨_, rfl⟩
  obtain ⟨hu1, hu2, huε⟩ := exponent_aux hε hu
  have h4u : 0 < 4 - u := by linarith
  have hδ : 0 < ε / 4 := by positivity
  obtain ⟨C₀, hC₀, h₀⟩ := h442 (ε / 4) hδ
  have hrough : 1 / (u / 2) = 1 / u + 1 / u := by field_simp; ring
  obtain ⟨b, C₁, hb, hC₁, h₁⟩ := eLpNorm_bilin_psiK_blockWeight_le hχ hu1 hu1 hrough
  set θ : ℝ := u / (4 - u) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) h4u.le
  obtain ⟨hκeq, hκ1, hκ2⟩ := one_sub_theta hu1 hu2
  set κ : ℝ := 2 * (2 - u) / (4 - u) with hκ
  have hκ0 : 0 ≤ κ := div_nonneg (by linarith) h4u.le
  obtain ⟨C', hC', hlog⟩ := one_add_log_rpow_le (b := b * θ) (ε := ε / 4) (by positivity) hδ
  refine ⟨C₀ ^ κ * C₁ ^ θ * C', by positivity, fun Q k hQ hQk f g => ?_⟩
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hl0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hL0 : 0 < 1 + Real.log Q := by linarith
  set M₀ : ℝ := C₀ * (Q : ℝ) ^ (ε / 4 - 3 / 8) with hM₀
  set M₁ : ℝ := C₁ * (1 + Real.log Q) ^ b with hM₁
  have hM₀0 : 0 ≤ M₀ := by positivity
  have hM₁0 : 0 ≤ M₁ := by positivity
  have hmain := interp_442 (single χ Q k) hu1 hu2 hM₀0 hM₁0
    (fun f g => by rw [single_apply hχ]; exact h₀ Q k hQ hQk f g)
    (fun f g => by rw [single_apply hχ]; exact h₁ Q k hQ f g) f g
  rw [single_apply hχ] at hmain
  refine hmain.trans ?_
  have hreal : M₀ ^ (1 - u / (4 - u)) * M₁ ^ (u / (4 - u)) ≤
      (C₀ ^ κ * C₁ ^ θ * C') * (Q : ℝ) ^ (-1 / 4 + ε) := by
    rw [hκeq]
    have e1 : M₀ ^ κ = C₀ ^ κ * (Q : ℝ) ^ ((ε / 4 - 3 / 8) * κ) := by
      rw [hM₀, Real.mul_rpow hC₀ (Real.rpow_nonneg hQ0.le _), ← Real.rpow_mul hQ0.le]
    have e2 : M₁ ^ θ = C₁ ^ θ * (1 + Real.log Q) ^ (b * θ) := by
      rw [hM₁, Real.mul_rpow hC₁ (Real.rpow_nonneg hL0.le _), ← Real.rpow_mul hL0.le]
    have h3 := hlog Q hQ1
    have hexp := exponent_le hε hu1 hu2 huε hκ1 hκ2
    have h4 : (Q : ℝ) ^ ((ε / 4 - 3 / 8) * κ + ε / 4) ≤ (Q : ℝ) ^ (-1 / 4 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hQ1 hexp
    calc M₀ ^ κ * M₁ ^ θ
        = C₀ ^ κ * (Q : ℝ) ^ ((ε / 4 - 3 / 8) * κ) * (C₁ ^ θ * (1 + Real.log Q) ^ (b * θ)) := by
          rw [e1, e2]
      _ ≤ C₀ ^ κ * (Q : ℝ) ^ ((ε / 4 - 3 / 8) * κ) * (C₁ ^ θ * (C' * (Q : ℝ) ^ (ε / 4))) := by
          gcongr
      _ = (C₀ ^ κ * C₁ ^ θ * C') * (Q : ℝ) ^ ((ε / 4 - 3 / 8) * κ + ε / 4) := by
          rw [Real.rpow_add hQ0]; ring
      _ ≤ _ := by gcongr
  exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl) le_rfl

end PrimeBHT.SingleScaleL1
