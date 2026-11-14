module

public import PrimeBHT.SingleScaleL1.Interp
public import PrimeBHT.SingleScaleL1.FourFourTwo

/-!
# Node N12 (b), `e:single-L1`: the `ℓ² × ℓ² → ℓ¹` bound for a single scale

For `T_k^Q(f,g)(x) = ∑ₙ ψ_k(n) w_Q(n) f(x-n) g(x+n)` (`w_Q = blockWeight (Ioc (Q/2) Q)`,
`bilin` of `PrimeBHT.Kernel`) we prove: for every `ε > 0` there is `C_ε` with
`‖T_k^Q(f,g)‖_{ℓ¹} ≤ C_ε Q^{-1/4+ε} ‖f‖_{ℓ²} ‖g‖_{ℓ²}`
for all `Q ≥ 1` and `k` with `Q < 8` or `Q^{20} ≤ 2^k` (the hypothesis `k ≥ b_Q` of the blueprint gives
`Q^{20} ≤ 2^k` for `Q ≥ 8`, blueprint N00 item 4), and all finitely supported `f, g`.

Stages (see the submodules):
* (a) `PrimeBHT.SingleScaleL1.eLpNorm_single_442` (`FourFourTwo`): the `(4,4,2)` estimate
  `M₀ = C Q^{δ-3/8}` for `Q^{20} ≤ 2^k`, by the reflection `n ↦ -n`, `l:U3maxmod` (b) and the
  vendored [F+, Prop 2.1];
* (b) `PrimeBHT.SingleScaleL1.eLpNorm_single_L1_of_442` (`Interp`): N60 between `(4,4,2)` and
  `(u,u,u/2)` with `θ_u = u/(4-u)`, landing at `(2,2,1)`, with `u = u(ε)`;
* (c) `PrimeBHT.SingleScaleL1.eLpNorm_single_L1`: the final statement; for `Q < 8` the rough bound
  `eLpNorm_bilin_psiK_blockWeight_le` at `(2,2,1)`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace PrimeBHT.SingleScaleL1

open PrimeBHT.Kernel PrimeBHT.SingleScale PrimeCarleson

/-- The small-`Q` case: for `1 ≤ Q < 8` the rough bound at `(2,2,1)` already gives `C Q^{-1/4+ε}`. -/
lemma eLpNorm_single_L1_small {χ : ℝ → ℝ} (hχ : IsCutoff χ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q k : ℕ), 1 ≤ Q → Q < 8 → ∀ f g : ℤ → ℂ,
      eLpNorm (bilin (weight χ Q k) f g) (ENNReal.ofReal 1) Measure.count ≤
        ENNReal.ofReal (C * (Q : ℝ) ^ (-1 / 4 + ε)) *
          eLpNorm f (ENNReal.ofReal 2) Measure.count * eLpNorm g (ENNReal.ofReal 2) Measure.count := by
  obtain ⟨b, C₀, hb, hC₀, hrough⟩ := eLpNorm_bilin_psiK_blockWeight_le hχ (p := 2) (q := 2)
    (r := 1) (by norm_num) (by norm_num) (by norm_num)
  set c₀ : ℝ := (8 : ℝ) ^ (1 / 4 : ℝ) with hc₀
  have hc₀0 : 0 ≤ c₀ := Real.rpow_nonneg (by norm_num) _
  refine ⟨C₀ * (1 + Real.log 8) ^ b * c₀, by positivity, fun Q k hQ hQ8 f g => ?_⟩
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hQ8' : (Q : ℝ) ≤ 8 := by exact_mod_cast hQ8.le
  refine (hrough Q k hQ f g).trans ?_
  have hlog : 1 + Real.log Q ≤ 1 + Real.log 8 :=
    by linarith [Real.log_le_log hQ0 hQ8']
  have hl0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hpow : (1 + Real.log Q) ^ b ≤ (1 + Real.log 8) ^ b :=
    Real.rpow_le_rpow (by linarith) hlog hb
  have h1 : (Q : ℝ) ^ (1 / 4 : ℝ) ≤ c₀ := Real.rpow_le_rpow hQ0.le hQ8' (by norm_num)
  have h2 : (Q : ℝ) ^ (-1 / 4 : ℝ) * (Q : ℝ) ^ (1 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add hQ0]; norm_num
  have h3 : (Q : ℝ) ^ (-1 / 4 : ℝ) ≤ (Q : ℝ) ^ (-1 / 4 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have h4 : 1 ≤ c₀ * (Q : ℝ) ^ (-1 / 4 + ε) := by
    calc (1 : ℝ) = (Q : ℝ) ^ (-1 / 4 : ℝ) * (Q : ℝ) ^ (1 / 4 : ℝ) := h2.symm
      _ ≤ (Q : ℝ) ^ (-1 / 4 + ε) * c₀ := by
          gcongr
      _ = _ := by ring
  have h5 : C₀ * (1 + Real.log Q) ^ b ≤
      C₀ * (1 + Real.log 8) ^ b * c₀ * (Q : ℝ) ^ (-1 / 4 + ε) := by
    calc C₀ * (1 + Real.log Q) ^ b ≤ C₀ * (1 + Real.log 8) ^ b := by gcongr
      _ = C₀ * (1 + Real.log 8) ^ b * 1 := by ring
      _ ≤ C₀ * (1 + Real.log 8) ^ b * (c₀ * (Q : ℝ) ^ (-1 / 4 + ε)) := by gcongr
      _ = _ := by ring
  gcongr

/-- **N12 (b), `e:single-L1`** (final statement). For every `ε > 0` there is `C ≥ 0` such that for all
natural `Q ≥ 1` and all `k` with `Q < 8` or `Q^{20} ≤ 2^k`, and all finitely supported `f, g`,
`‖x ↦ ∑ₙ ψ_k(n) w_Q(n) f(x-n) g(x+n)‖_{ℓ¹} ≤ C Q^{-1/4+ε} ‖f‖_{ℓ²} ‖g‖_{ℓ²}`,
with `w_Q = blockWeight (Finset.Ioc (Q / 2) Q)`. -/
theorem eLpNorm_single_L1 {χ : ℝ → ℝ} (hχ : IsCutoff χ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q k : ℕ), 1 ≤ Q → (Q < 8 ∨ (Q : ℝ) ^ 20 ≤ 2 ^ k) → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (bilin (fun n => ((psiK χ k n : ℝ) : ℂ) * blockWeight (Finset.Ioc (Q / 2) Q) n)
          ⇑f ⇑g) 1 Measure.count ≤
        ENNReal.ofReal (C * (Q : ℝ) ^ (-1 / 4 + ε)) * eLpNorm f 2 Measure.count *
          eLpNorm g 2 Measure.count := by
  obtain ⟨C₁, hC₁, h₁⟩ := eLpNorm_single_L1_small hχ hε
  obtain ⟨C₂, hC₂, h₂⟩ := eLpNorm_single_L1_of_442 hχ (fun δ hδ => eLpNorm_single_442 hχ hδ) hε
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun Q k hQ hcase f g => ?_⟩
  have hQ0 : (0 : ℝ) ≤ (Q : ℝ) ^ (-1 / 4 + ε) := Real.rpow_nonneg (Nat.cast_nonneg Q) _
  simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at h₁ h₂
  rcases hcase with h | h
  · refine (h₁ Q k hQ h f g).trans ?_
    gcongr
    exact le_max_left _ _
  · refine (h₂ Q k hQ h f g).trans ?_
    gcongr
    exact le_max_right _ _

end PrimeBHT.SingleScaleL1
