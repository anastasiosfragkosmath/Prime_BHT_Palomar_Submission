module

public import PrimeBHT.FinalGlue
public import PrimeBHT.FinalSum
public import PrimeBHT.ErrorTerms
public import PrimeBHT.Progression
public import PrimeBHT.Exponents
public import PrimeBHT.Decomposition
public import PrimeBHT.Kernel

/-!
# S25 (gate G2): the case `r < 1` of the main theorem (blueprint N52, N53), conditional provider

`main_quasiBanach_of_inputs`: for a cutoff `χ` and `(p, q, r) ∈ R` with `r < 1`, there is `C ≥ 0` with
`‖H_P(f,g)‖_{ℓ^r} ≤ C ‖f‖_p ‖g‖_q` for all `f, g : ℤ →₀ ℂ` (`H_P = FinalSum.hP`, the formula of the
frozen `primeBHT`, by `FinalSum.hP_coe_eq`), assuming exactly

* `X3Statement` (the sealed `[F+, Prop 3.1]`; used through `ErrorTerms.eLpNorm_Serr_le_k_pow_of_X3`),
* `Key0Statement χ` (the corrected `p:key0`; used inside `FinalGlue.complexity_decay_add_of_key0_of_bhtSmooth`),
* `BHTSmooth χ p' q' r' C'` (the anchor X1) at exactly three tuples (for `p ≤ q`, `D` the exponent
  data of `(p, q, r)`): the target `(p, q, r)` (for the finitely many small dyadic `Q`: `hProg`),
  `(D.p₀, D.q₀, D.r₀)` and `(1/(1 - D.δ), 1/D.δ, 1)` (inside `FinalGlue`).  For `p > q` the same
  holds with `(q, p, r)` in place of `(p, q, r)`.

Structure of the proof:

1. `hE` (`e:error-summable`) from `ErrorTerms.eLpNorm_Serr_le_k_pow_of_X3`;
2. `hProg` (`e:progression` for `I = [b_Q, J]`) from `Progression.progression_of_bhtSmooth` at the
   target tuple with `ε = 1` (`exists_hProg_of_bhtSmooth`);
3. `hH` (`e:complexity-decay` at `τ = 3/4`) from `FinalGlue.complexity_decay_add_of_key0_of_bhtSmooth`;
4. assembly by `FinalSum.exists_const_hP_of_estimates` (`main_quasiBanach_of_data`);
5. the swap `p > q` via `hP g f = - hP f g` (`hP_swap`).
-/

@[expose] public section

open MeasureTheory PrimeBHT.Kernel PrimeBHT.Decomposition PrimeBHT.Exponents
open scoped ENNReal

namespace PrimeBHT.MainQuasiBanach

open PrimeBHT.Progression (BHTSmooth)
open PrimeBHT.FinalSum (hP)

/-! ### Step 5 (lemma): `H_P` is antisymmetric (Lemma 1.2) -/

/-- **Lemma 1.2.** `H_P(g, f) = - H_P(f, g)`: the substitution `n ↦ -n` in the defining series. -/
theorem hP_swap (f g : ℤ → ℂ) (x : ℤ) : hP g f x = -hP f g x := by
  unfold hP
  rw [← tsum_neg]
  let F : ℤ → ℂ := fun n => if n = 0 then 0 else
    ((ArithmeticFunction.vonMangoldt n.natAbs : ℝ) : ℂ) / (n : ℂ) * g (x - n) * f (x + n)
  have h1 : ∑' n : ℤ, F n = ∑' n : ℤ, F (-n) := ((Equiv.neg ℤ).tsum_eq F).symm
  refine h1.trans (tsum_congr fun n => ?_)
  by_cases hn : n = 0
  · simp [F, hn]
  · have hn' : -n ≠ 0 := neg_ne_zero.2 hn
    simp only [F, hn, hn', ite_false, Int.natAbs_neg, Int.cast_neg, sub_neg_eq_add]
    rw [← sub_eq_add_neg]
    ring

/-- `H_P(g, f) = - H_P(f, g)` as an identity of functions. -/
theorem hP_swap_eq (f g : ℤ → ℂ) : hP g f = -hP f g := by
  funext x
  exact hP_swap f g x

/-- The `ℓ^r` quasi-norm of `H_P(g, f)` equals that of `H_P(f, g)`. -/
theorem eLpNorm_hP_swap (f g : ℤ → ℂ) (s : ℝ≥0∞) :
    eLpNorm (hP g f) s Measure.count = eLpNorm (hP f g) s Measure.count := by
  rw [hP_swap_eq, eLpNorm_neg]

/-! ### Step 2: `hProg` -/

/-- **`hProg` of `FinalSum`, from `BHTSmooth` at the target tuple** (N53 step 4).  For every dyadic
`Q = 2^j` and every `J`, `‖∑_{k = b_Q}^{J} T_k^Q(f,g)‖_{ℓ^r} ≤ Cp(j) ‖f‖_p ‖g‖_q`, where the sum over
`k ∈ [b_Q, J]` is `T_I^Q` (`FinalGlue.blk_Icc_eq_opIQ`) and `Cp j = C' Q^{max(1/r - 1, 0) + 1}`
(`progression_of_bhtSmooth` with `ε = 1`). -/
theorem exists_hProg_of_bhtSmooth {χ : ℝ → ℝ} (hχ : IsCutoff χ) {p q r C : ℝ} (hp : 0 < p)
    (hq : 0 < q) (hr : 0 < r) (hpqr : 1 / r = 1 / p + 1 / q) (hX : BHTSmooth χ p q r C) :
    ∃ Cp : ℕ → ℝ, (∀ j, 0 ≤ Cp j) ∧ ∀ f g : ℤ →₀ ℂ, ∀ j J : ℕ,
      eLpNorm (∑ k ∈ Finset.Icc (bQ ((2 : ℝ) ^ j)) J, Tk χ j k ⇑f ⇑g)
          (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (Cp j) * eLpNorm ⇑f (ENNReal.ofReal p) Measure.count *
          eLpNorm ⇑g (ENNReal.ofReal q) Measure.count := by
  obtain ⟨C', hC', h⟩ := PrimeBHT.Progression.progression_of_bhtSmooth hp hq hr hpqr hX
    (ε := 1) one_pos
  refine ⟨fun j => C' * (((2 ^ j : ℕ) : ℝ)) ^ (max (1 / r - 1) 0 + 1), fun j => by positivity,
    fun f g j J => ?_⟩
  have e : ∑ k ∈ Finset.Icc (bQ ((2 : ℝ) ^ j)) J, Tk χ j k ⇑f ⇑g =
      PrimeBHT.FinalGlue.blk χ j (Finset.Icc (bQ ((2 : ℝ) ^ j)) J) f g := by
    funext x
    rw [PrimeBHT.FinalGlue.blk_apply hχ, Finset.sum_apply]
  rw [e, PrimeBHT.FinalGlue.blk_Icc_eq_opIQ hχ]
  exact h (2 ^ j) (Nat.one_le_two_pow) (bQ ((2 : ℝ) ^ j)) J (one_le_bQ_two_pow j) ⇑f ⇑g
    (PrimeBHT.FinalGlue.finite_support_coe f) (PrimeBHT.FinalGlue.finite_support_coe g)

/-! ### Steps 1, 3, 4: the assembly for `p ≤ q` with the exponent data in hand -/

/-- `5/6 < r` from the exponent data (`t = 1/r - 1 < 1/5`). -/
theorem five_sixth_lt_of_data {p q r : ℝ} (hr0 : 0 < r) (D : ExponentData p q r) : 5 / 6 < r := by
  have h : 1 / r < 6 / 5 := by linarith [D.t_eq, D.t_lt_fifth]
  rw [div_lt_iff₀ hr0] at h
  linarith

/-- **N52 + N53 (`r < 1`, `p ≤ q`), the assembly with the exponent data `D` given.**  The anchors used
are exactly `X3Statement`, `Key0Statement χ` and `BHTSmooth` at the three tuples `(p, q, r)`
(`hT`, the finitely many small `Q`), `(D.p₀, D.q₀, D.r₀)` (`hX₀`) and `(1/(1-D.δ), 1/D.δ, 1)` (`hX₁`). -/
theorem main_quasiBanach_of_data {χ : ℝ → ℝ} (hχ : IsCutoff χ)
    (hX3 : PrimeBHT.ErrorTerms.X3Statement) (hK : PrimeBHT.FinalGlue.Key0Statement χ)
    {p q r : ℝ} (hp : 1 < p) (hq : 1 < q) (hr0 : 0 < r) (hr : 1 / r = 1 / p + 1 / q)
    (D : ExponentData p q r) {C_T C₀ C₁ : ℝ} (hT : BHTSmooth χ p q r C_T)
    (hX₀ : BHTSmooth χ D.p₀ D.q₀ D.r₀ C₀)
    (hX₁ : BHTSmooth χ (1 / (1 - D.δ)) (1 / D.δ) 1 C₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : ℤ →₀ ℂ,
      eLpNorm (hP ⇑f ⇑g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal C * eLpNorm ⇑f (ENNReal.ofReal p) Measure.count *
          eLpNorm ⇑g (ENNReal.ofReal q) Measure.count := by
  have h56 := five_sixth_lt_of_data hr0 D
  -- step 1: `hE`
  obtain ⟨C_E, hCE, hE⟩ :=
    PrimeBHT.ErrorTerms.eLpNorm_Serr_le_k_pow_of_X3 hX3 hχ hp hq hr
  -- step 2: `hProg`
  obtain ⟨Cp, hCp, hProg⟩ := exists_hProg_of_bhtSmooth hχ (lt_trans zero_lt_one hp)
    (lt_trans zero_lt_one hq) hr0 hr hT
  -- step 3: `hH`
  obtain ⟨σ, C_H, j₁, hσ, hCH, hH⟩ :=
    PrimeBHT.FinalGlue.complexity_decay_add_of_key0_of_bhtSmooth hχ hK D hX₀ hX₁
  -- step 4: assembly
  exact PrimeBHT.FinalSum.exists_const_hP_of_estimates hχ (τ := 3 / 4) (by norm_num) hr0
    (PrimeBHT.FinalSum.one_lt_hundred_mul_min_of_half_lt (by linarith)) hσ hCE hCH.le hCp j₁
    (fun f g k hk => hE k hk f g) hProg (fun f g j J hj => hH j J hj f g)

/-! ### The theorem for `p ≤ q`, from the universal form of the anchor X1 -/

/-- **N52 + N53, `r < 1`, `p ≤ q`** (conditional provider).  The hypothesis `hX` is the anchor X1 in
its universal form on the open range `1 < p'`, `1 < q'`, `1/r' = 1/p' + 1/q'`, `2/3 < r'`; the proof
uses it only at the three tuples `(p, q, r)`, `(D.p₀, D.q₀, D.r₀)` and `(1/(1-D.δ), 1/D.δ, 1)`, where
`D` is the `ExponentData` of `InR.exists_exponentData` (see `main_quasiBanach_of_data`). -/
theorem main_quasiBanach_of_inputs_le {χ : ℝ → ℝ} (hχ : IsCutoff χ)
    (hX3 : PrimeBHT.ErrorTerms.X3Statement) (hK : PrimeBHT.FinalGlue.Key0Statement χ)
    (hX : ∀ p' q' r' : ℝ, 1 < p' → 1 < q' → 1 / r' = 1 / p' + 1 / q' → 2 / 3 < r' →
      ∃ C' : ℝ, BHTSmooth χ p' q' r' C')
    {p q r : ℝ} (h : InR p q r) (hr : r < 1) (hpq : p ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : ℤ →₀ ℂ,
      eLpNorm (hP ⇑f ⇑g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal C * eLpNorm ⇑f (ENNReal.ofReal p) Measure.count *
          eLpNorm ⇑g (ENNReal.ofReal q) Measure.count := by
  obtain ⟨D⟩ := h.exists_exponentData hr hpq
  have h56 : 5 / 6 < r := five_sixth_lt_of_data h.pos_r D
  have hδ0 : 0 < D.δ := D.δ_pos
  have hδhalf : D.δ < 1 / 2 := lt_of_lt_of_le D.δ_lt (min_le_left _ _)
  have h1δ : 0 < 1 - D.δ := by linarith
  obtain ⟨C_T, hT⟩ := hX p q r h.one_lt_p h.one_lt_q h.inv_r (by linarith)
  obtain ⟨C₀, hX₀⟩ := hX D.p₀ D.q₀ D.r₀ D.one_lt_p₀ D.one_lt_q₀ D.inv_p₀_add_inv_q₀.symm
    D.two_thirds_lt_r₀
  obtain ⟨C₁, hX₁⟩ := hX (1 / (1 - D.δ)) (1 / D.δ) 1 (one_lt_one_div h1δ (by linarith))
    (one_lt_one_div hδ0 (by linarith)) (by rw [one_div_one_div, one_div_one_div]; ring)
    (by norm_num)
  exact main_quasiBanach_of_data hχ hX3 hK h.one_lt_p h.one_lt_q h.pos_r h.inv_r D hT hX₀ hX₁

/-! ### Step 5: the theorem for all `(p, q, r) ∈ R` with `r < 1` -/

/-- **`main_quasiBanach_of_inputs` (N52 + N53, the case `r < 1`; gate G2).**  For a cutoff `χ` and
`(p, q, r) ∈ R` with `r < 1`, there is `C ≥ 0` with `‖H_P(f,g)‖_{ℓ^r} ≤ C ‖f‖_p ‖g‖_q` for all
`f, g : ℤ →₀ ℂ`, where `H_P = FinalSum.hP` (definitionally the frozen `primeBHT`, `FinalSum.hP_coe_eq`),
under `X3Statement`, `Key0Statement χ` and the anchor X1 `hX` (used only at the tuples listed in
`main_quasiBanach_of_inputs_le`, for the target `(p, q, r)` if `p ≤ q`, and `(q, p, r)` if `p > q`). -/
theorem main_quasiBanach_of_inputs {χ : ℝ → ℝ} (hχ : IsCutoff χ)
    (hX3 : PrimeBHT.ErrorTerms.X3Statement) (hK : PrimeBHT.FinalGlue.Key0Statement χ)
    (hX : ∀ p' q' r' : ℝ, 1 < p' → 1 < q' → 1 / r' = 1 / p' + 1 / q' → 2 / 3 < r' →
      ∃ C' : ℝ, BHTSmooth χ p' q' r' C')
    {p q r : ℝ} (h : InR p q r) (hr : r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : ℤ →₀ ℂ,
      eLpNorm (hP ⇑f ⇑g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal C * eLpNorm ⇑f (ENNReal.ofReal p) Measure.count *
          eLpNorm ⇑g (ENNReal.ofReal q) Measure.count := by
  rcases le_total p q with hpq | hqp
  · exact main_quasiBanach_of_inputs_le hχ hX3 hK hX h hr hpq
  · obtain ⟨C, hC, hCb⟩ := main_quasiBanach_of_inputs_le hχ hX3 hK hX h.symm hr hqp
    refine ⟨C, hC, fun f g => ?_⟩
    rw [← eLpNorm_hP_swap ⇑f ⇑g, mul_right_comm]
    exact hCb g f

end PrimeBHT.MainQuasiBanach
