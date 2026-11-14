module

public import PrimeBHT.MainBanach.Ops
public import PrimeBHT.MainBanach.Estimates

/-!
# S24 (gate G1): the case `r ≥ 1` of the main theorem, assembled end to end (conditional)

`main_banach_of_inputs`: for a cutoff `χ` and `(p, q, r) ∈ R` with `r ≥ 1`, and the explicit inputs

* (a) `X3Statement` (the sealed `[F+, Prop 3.1]`; blueprint X3),
* (b) the time-frequency anchor X1 in the form `∀ p' q' r', 1 < p' → 1 < q' → 1/r' = 1/p' + 1/q' →
  1 ≤ r' → ∃ C', BHTSmooth χ p' q' r' C'` (all Banach tuples; the proof uses it at the target `(p,q,r)`
  for the finitely many small `Q` and at the auxiliary Banach partner `(p₁, q₁, r₁)` of N51 produced
  by `exists_banach_partner` inside `exists_power_saving_of_estimates`),
* (c) `Key0Prop χ` (the corrected `p:key0`, N26),

there is `C ≥ 0` with `‖H_P(f, g)‖_{ℓ^r} ≤ C ‖f‖_p ‖g‖_q` for all `f, g : ℤ →₀ ℂ`, where `H_P` is
`FinalSum.hP` (`= primeBHT`, see `FinalSum.hP_coe_eq`).

Chain: `hE` (`eLpNorm_Serr_le_k_pow_of_X3`), `hProg` (`blk_progression_of_bhtSmooth` for `[b_Q, J]`),
`hH` (`exists_hH_of_key0`, N51 via `exists_power_saving_of_estimates`), assembly
(`FinalSum.exists_const_hP_of_estimates`, `τ = 1/6`).
-/

@[expose] public noncomputable section

open MeasureTheory PrimeBHT.Kernel PrimeBHT.Decomposition PrimeBHT.Exponents
open scoped ENNReal

namespace PrimeBHT.MainBanach

open PrimeBHT.Progression (BHTSmooth)

/-- The finite sum of the `T_k^Q`, `b_Q ≤ k ≤ J`, as the block `blk`. -/
theorem sum_Tk_eq_blk {χ : ℝ → ℝ} (hχ : IsCutoff χ) (j a b : ℕ) (f g : ℤ →₀ ℂ) :
    ∑ k ∈ Finset.Icc a b, Tk χ j k ⇑f ⇑g = blk χ j (Finset.Icc a b) f g := by
  funext x
  rw [blk_apply hχ, Finset.sum_apply]

/-- **`main_banach_of_inputs`** (gate G1, conditional): the case `r ≥ 1` of the main theorem. -/
theorem main_banach_of_inputs {χ : ℝ → ℝ} (hχ : IsCutoff χ) {p q r : ℝ} (hR : InR p q r)
    (hr : 1 ≤ r) (hX3 : PrimeBHT.ErrorTerms.X3Statement)
    (hX1 : ∀ p' q' r' : ℝ, 1 < p' → 1 < q' → 1 / r' = 1 / p' + 1 / q' → 1 ≤ r' →
      ∃ C' : ℝ, BHTSmooth χ p' q' r' C')
    (hK : Key0Prop χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : ℤ →₀ ℂ,
      eLpNorm (PrimeBHT.FinalSum.hP ⇑f ⇑g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count *
          eLpNorm (⇑g) (ENNReal.ofReal q) Measure.count := by
  have hp1 := hR.one_lt_p
  have hq1 := hR.one_lt_q
  -- (1) the error terms
  obtain ⟨C_E, hCE, hE⟩ :=
    PrimeBHT.ErrorTerms.eLpNorm_Serr_le_k_pow_of_X3 hX3 hχ hp1 hq1 hR.inv_r
  -- (3) the decay of the moderate part and the tail (N51)
  obtain ⟨σ, C_H, hσ, hCH, j₁, hH⟩ := exists_hH_of_key0 hK hχ hX1 hR hr
  -- (2) the progression estimate at the target tuple
  obtain ⟨C₀, hX₀⟩ := hX1 p q r hp1 hq1 hR.inv_r hr
  obtain ⟨C', hC', hP⟩ := blk_progression_of_bhtSmooth hχ hR.pos_p hR.pos_q hR.pos_r hR.inv_r hX₀
    (ε := 1) one_pos
  refine PrimeBHT.FinalSum.exists_const_hP_of_estimates hχ (τ := 1 / 6) (σ := σ) (by norm_num)
    hR.pos_r (PrimeBHT.FinalSum.one_lt_hundred_mul_min_of_half_lt (by linarith)) hσ hCE hCH.le
    (Cp := fun j => C' * ((2 : ℝ) ^ j) ^ (max (1 / r - 1) 0 + 1)) (fun j => by positivity) j₁
    (fun f g k hk => hE k hk f g) ?_ hH
  intro f g j J
  rw [sum_Tk_eq_blk hχ]
  exact hP j (bQ ((2 : ℝ) ^ j)) J (one_le_bQ_two_pow j) f g

end PrimeBHT.MainBanach

end
