module

public import PrimeBHT.FinalGlue.Ops

/-!
# S21: the raw estimates of N52 derived from the base nodes

All statements are for the blocks `blk χ j F`, uniformly in the scale window `F` and `J`.

* `blk_tail_decay_of_key0` (E2, `e:secondinterp`): from `Key0Statement χ`.
* `blk_progression_of_bhtSmooth` (E3, `e:thirdinterp`, and the `U` bound at `(p₀,q₀,r₀)`): from
  `progression_of_bhtSmooth`, i.e. from `BHTSmooth χ p q r C` at the tuple used.
* `blk_rough_decay` (E4, `e:fourthinterp`): unconditional (`eLpNorm_single_rough_rpow` and the
  `r`-quasi-triangle inequality).
* `blk_initial_decay` (N52 (B), `e:negpower`): unconditional (`eLpNorm_single_L1`, `eLpNorm_single_rough`,
  `single_scale_power_decay_of_estimates`, quasi-triangle).
-/

@[expose] public noncomputable section

open MeasureTheory PrimeBHT.Kernel PrimeBHT.Decomposition PrimeBHT.Exponents PrimeBHT.FinalAssembly
open scoped ENNReal

namespace PrimeBHT.FinalGlue

open PrimeBHT.SingleScaleL1 (single single_apply)
open PrimeBHT.Progression (BHTSmooth)

theorem pow_cast_two (j : ℕ) : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; rfl

theorem one_le_two_pow_real (j : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)

/-! ## E2: from `Key0Statement` -/

/-- **(E2) `e:secondinterp`, conditional on `Key0Statement χ`.**  For `τ ∈ (0,1)`: the block
`[⌈Q^τ⌉, J]` (any `J`) is bounded `ℓ² × ℓ² → ℓ¹` by `C Q^{-τ/2+ε}`. -/
theorem blk_tail_decay_of_key0 {χ : ℝ → ℝ} (hK : Key0Statement χ) (hχ : IsCutoff χ) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C Q₁ : ℝ, 0 < C ∧ ∀ j J : ℕ, Q₁ ≤ (2 : ℝ) ^ j → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (blk χ j (Finset.Icc ⌈((2 : ℝ) ^ j) ^ τ⌉₊ J) f g) (ENNReal.ofReal 1) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-(τ / 2) + ε)) *
          eLpNorm f (ENNReal.ofReal 2) Measure.count *
            eLpNorm g (ENNReal.ofReal 2) Measure.count := by
  obtain ⟨Q₀, C, hC, h⟩ := hK hχ τ hτ0 hτ1 ε hε
  refine ⟨C + 1, (Q₀ : ℝ), by linarith, fun j J hQ f g => ?_⟩
  have hQ' : Q₀ ≤ 2 ^ j := by exact_mod_cast hQ
  have h1 := h (2 ^ j) ⟨j, rfl⟩ hQ' J f g
  rw [blk_Icc_eq_uOp hχ]
  simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  refine h1.trans ?_
  rw [pow_cast_two, neg_div]
  exact mul_le_mul' (mul_le_mul' (PrimeBHT.GroupDecay.ofReal_mul_rpow_le (one_le_two_pow_real j)
    hC (by linarith) le_rfl) le_rfl) le_rfl

/-! ## E3 and the `U` bound at `(p₀, q₀, r₀)`: from `BHTSmooth` -/

/-- **(E3) `e:progression` for a block, conditional on `BHTSmooth χ p q r C`** at the tuple used. -/
theorem blk_progression_of_bhtSmooth {χ : ℝ → ℝ} (hχ : IsCutoff χ) {p q r C : ℝ} (hp : 0 < p)
    (hq : 0 < q) (hr : 0 < r) (hpqr : 1 / r = 1 / p + 1 / q) (hX : BHTSmooth χ p q r C) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ j a b : ℕ, 1 ≤ a → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (blk χ j (Finset.Icc a b) f g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C' * ((2 : ℝ) ^ j) ^ (max (1 / r - 1) 0 + ε)) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count := by
  obtain ⟨C', hC', h⟩ := PrimeBHT.Progression.progression_of_bhtSmooth hp hq hr hpqr hX hε
  refine ⟨C' + 1, by linarith, fun j a b ha f g => ?_⟩
  rw [blk_Icc_eq_opIQ hχ]
  have h1 := h (2 ^ j) Nat.one_le_two_pow a b ha f g (finite_support_coe f) (finite_support_coe g)
  rw [pow_cast_two] at h1
  refine h1.trans ?_
  exact mul_le_mul' (mul_le_mul' (PrimeBHT.GroupDecay.ofReal_mul_rpow_le (one_le_two_pow_real j)
    hC' (by linarith) le_rfl) le_rfl) le_rfl

/-! ## E4: the rough bound summed over the scales -/

/-- **(E4) `e:fourthinterp`**: for `1 < p, q`, `1/r = 1/p + 1/q`, `r ≤ 1`, a block `F` with at most
`Q^c` scales satisfies `‖blk‖_r ≤ C Q^{c/r + ε} ‖f‖_p ‖g‖_q`.  Unconditional. -/
theorem blk_rough_decay {χ : ℝ → ℝ} (hχ : IsCutoff χ) {p q r c : ℝ} (hp : 1 < p) (hq : 1 < q)
    (hr : 1 / r = 1 / p + 1 / q) (hr1 : r ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (F : Finset ℕ), (F.card : ℝ) ≤ ((2 : ℝ) ^ j) ^ c →
      ∀ f g : ℤ →₀ ℂ,
      eLpNorm (blk χ j F f g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (c * (1 / r) + ε)) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count := by
  have hr0 : 0 < r := by
    have h1 := one_div_pos.2 (lt_trans one_pos hp)
    have h2 := one_div_pos.2 (lt_trans one_pos hq)
    exact one_div_pos.1 (by rw [hr]; linarith)
  obtain ⟨C, hC, h⟩ := PrimeBHT.SingleScale.eLpNorm_single_rough_rpow hχ hp hq hr hε
  refine ⟨C + 1, by linarith, fun j F hF f g => ?_⟩
  have hk : ∀ k ∈ F, eLpNorm (single χ (2 ^ j) k f g) (ENNReal.ofReal r) Measure.count ≤
      ENNReal.ofReal ((C + 1) * ((2 : ℝ) ^ j) ^ ε) *
        (eLpNorm f (ENNReal.ofReal p) Measure.count * eLpNorm g (ENNReal.ofReal q) Measure.count) := by
    intro k _
    rw [single_apply hχ]
    have h1 := h (2 ^ j) k ⟨j, rfl⟩ ⇑f ⇑g
    rw [pow_cast_two] at h1
    refine h1.trans ?_
    rw [mul_assoc]
    exact mul_le_mul' (PrimeBHT.GroupDecay.ofReal_mul_rpow_le (one_le_two_pow_real j) hC
      (by linarith) le_rfl) le_rfl
  have h2 := eLpNorm_blk_le χ j F f g hr0 hr1 hk
  rw [mul_assoc]
  exact h2.trans (card_rpow_mul_le (one_le_two_pow_real j) hr0 (by linarith) hF _)

theorem card_Icc_le_rpow {a b : ℕ} {x : ℝ} (hx : 0 < x) (ha : 1 ≤ a) (hb : b ≤ ⌈x⌉₊ - 1) :
    ((Finset.Icc a b).card : ℝ) ≤ x :=
  card_le_of_mem hx fun k hk => by
    have hk' := Finset.mem_Icc.1 hk
    have h1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.2 hx
    exact ⟨le_trans ha hk'.1, Nat.lt_ceil.1 (by omega)⟩

/-! ## The initial group -/

/-- For `Q = 2^j` and `k ≥ b_Q`: `Q < 8` or `Q^{20} ≤ 2^k` (blueprint N00 item 4). -/
theorem q_lt_eight_or {j k : ℕ} (hk : bQ ((2 : ℝ) ^ j) ≤ k) :
    2 ^ j < 8 ∨ ((2 ^ j : ℕ) : ℝ) ^ 20 ≤ 2 ^ k := by
  by_cases h8 : 2 ^ j < 8
  · exact Or.inl h8
  right
  have hj3 : 3 ≤ j := by
    by_contra hj
    have h2 : j ≤ 2 := by omega
    have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
    omega
  have hk1 : 1 ≤ k := (one_le_bQ_two_pow j).trans hk
  have hM := (two_pow_le_Mk_iff hk1).2 hk
  rw [le_Mk_iff (one_le_two_pow_real j), Real.log_pow] at hM
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hjR : (3 : ℝ) ≤ j := by exact_mod_cast hj3
  have ha2 : 2 ≤ (j : ℝ) * Real.log 2 := by
    have := mul_le_mul_of_nonneg_right hjR hl2.le
    linarith
  have hform : ((j : ℝ) * Real.log 2) ^ 10 / Real.log 2 = j * ((j : ℝ) * Real.log 2) ^ 9 := by
    field_simp
  rw [hform] at hM
  have h9 : (20 : ℝ) ≤ ((j : ℝ) * Real.log 2) ^ 9 :=
    calc (20 : ℝ) ≤ 2 ^ 9 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) ha2 9
  have h20 : (20 : ℝ) * j ≤ k := by
    have := mul_le_mul_of_nonneg_left h9 (by positivity : (0 : ℝ) ≤ j)
    linarith
  have h20' : 20 * j ≤ k := by exact_mod_cast h20
  rw [pow_cast_two, ← pow_mul]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- The single-scale bound `‖T_k^Q‖_{p,q→r} ≲ Q^{-θ/4+ε}` uniformly in `k ≥ b_Q` (N52 (B), first half;
unconditional). -/
theorem single_scale_decay_of_bQ {χ : ℝ → ℝ} (hχ : IsCutoff χ) {p q r : ℝ} (D : ExponentData p q r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C Q₁ : ℝ, 0 < C ∧ ∀ j k : ℕ, bQ ((2 : ℝ) ^ j) ≤ k → Q₁ ≤ (2 : ℝ) ^ j →
      ∀ f g : ℤ →₀ ℂ,
      eLpNorm (single χ (2 ^ j) k f g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-(D.θ / 4) + ε)) *
          eLpNorm f (ENNReal.ofReal p) Measure.count * eLpNorm g (ENNReal.ofReal q) Measure.count := by
  have hL : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧
      ∀ x : {x : ℕ × ℕ // bQ ((2 : ℝ) ^ x.1) ≤ x.2}, Q₁ ≤ (2 : ℝ) ^ x.1.1 → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (single χ (2 ^ x.1.1) x.1.2 f g) (ENNReal.ofReal 1) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ x.1.1) ^ (-(1 / 4 : ℝ) + ε)) *
          eLpNorm f (ENNReal.ofReal 2) Measure.count *
            eLpNorm g (ENNReal.ofReal 2) Measure.count := by
    intro ε hε
    obtain ⟨C, hC, h⟩ := PrimeBHT.SingleScaleL1.eLpNorm_single_L1 hχ hε
    refine ⟨C + 1, 1, by linarith, fun x _ f g => ?_⟩
    rw [single_apply hχ]
    have h1 := h (2 ^ x.1.1) x.1.2 Nat.one_le_two_pow (q_lt_eight_or x.2) f g
    rw [pow_cast_two] at h1
    simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
    refine h1.trans ?_
    rw [show (-1 / 4 : ℝ) = -(1 / 4) by ring]
    exact mul_le_mul' (mul_le_mul' (PrimeBHT.GroupDecay.ofReal_mul_rpow_le
      (one_le_two_pow_real _) hC (by linarith) le_rfl) le_rfl) le_rfl
  have hP : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧
      ∀ x : {x : ℕ × ℕ // bQ ((2 : ℝ) ^ x.1) ≤ x.2}, Q₁ ≤ (2 : ℝ) ^ x.1.1 → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (single χ (2 ^ x.1.1) x.1.2 f g) (ENNReal.ofReal D.r₀) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ x.1.1) ^ ε) *
          eLpNorm f (ENNReal.ofReal D.p₀) Measure.count *
            eLpNorm g (ENNReal.ofReal D.q₀) Measure.count := by
    intro ε hε
    obtain ⟨C, hC, h⟩ := PrimeBHT.SingleScale.eLpNorm_single_rough_rpow hχ D.one_lt_p₀
      D.one_lt_q₀ D.inv_p₀_add_inv_q₀.symm hε
    refine ⟨C + 1, 1, by linarith, fun x _ f g => ?_⟩
    rw [single_apply hχ]
    have h1 := h (2 ^ x.1.1) x.1.2 ⟨x.1.1, rfl⟩ ⇑f ⇑g
    rw [pow_cast_two] at h1
    refine h1.trans ?_
    exact mul_le_mul' (mul_le_mul' (PrimeBHT.GroupDecay.ofReal_mul_rpow_le
      (one_le_two_pow_real _) hC (by linarith) le_rfl) le_rfl) le_rfl
  obtain ⟨C, Q₁, hC, h⟩ := single_scale_power_decay_of_estimates
    (fun x : {x : ℕ × ℕ // bQ ((2 : ℝ) ^ x.1) ≤ x.2} => single χ (2 ^ x.1.1) x.1.2)
    (fun x => (2 : ℝ) ^ x.1.1) D hL hP ε hε
  exact ⟨C, Q₁, hC, fun j k hk hQ f g => h ⟨(j, k), hk⟩ hQ f g⟩

/-- **N52 (B), `e:negpower`: the initial group.**  `H₀ = ∑_{b_Q ≤ k ≤ J, k < Q^{τ₀}} T_k^Q` satisfies
`‖H₀‖_r ≲ Q^{τ₀/r - θ/4 + ε} ‖f‖_p ‖g‖_q`, uniformly in `J`.  Unconditional. -/
theorem blk_initial_decay {χ : ℝ → ℝ} (hχ : IsCutoff χ) {p q r : ℝ} (D : ExponentData p q r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C Q₁ : ℝ, 0 < C ∧ ∀ j J : ℕ, Q₁ ≤ (2 : ℝ) ^ j → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (blk χ j ((Finset.Icc (bQ ((2 : ℝ) ^ j)) J).filter
          (fun k : ℕ => (k : ℝ) < ((2 : ℝ) ^ j) ^ D.τ 0)) f g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (D.τ 0 / r - D.θ / 4 + ε)) *
          eLpNorm f (ENNReal.ofReal p) Measure.count * eLpNorm g (ENNReal.ofReal q) Measure.count := by
  obtain ⟨C, Q₁, hC, h⟩ := single_scale_decay_of_bQ hχ D hε
  obtain ⟨hr0, hr1⟩ := PrimeBHT.GroupDecay.exponentData_r_mem D
  refine ⟨C, Q₁, hC, fun j J hQ f g => ?_⟩
  have hQ1 := one_le_two_pow_real j
  have hk : ∀ k ∈ (Finset.Icc (bQ ((2 : ℝ) ^ j)) J).filter
        (fun k : ℕ => (k : ℝ) < ((2 : ℝ) ^ j) ^ D.τ 0),
      eLpNorm (single χ (2 ^ j) k f g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-(D.θ / 4) + ε)) *
          (eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count) := by
    intro k hk
    have hk' := Finset.mem_filter.1 hk
    rw [← mul_assoc]
    exact h j k (Finset.mem_Icc.1 hk'.1).1 hQ f g
  have hcard : ((((Finset.Icc (bQ ((2 : ℝ) ^ j)) J).filter
        (fun k : ℕ => (k : ℝ) < ((2 : ℝ) ^ j) ^ D.τ 0))).card : ℝ) ≤ ((2 : ℝ) ^ j) ^ D.τ 0 := by
    refine card_le_of_mem (Real.rpow_pos_of_pos (by positivity) _) fun k hk => ?_
    have hk' := Finset.mem_filter.1 hk
    exact ⟨(one_le_bQ_two_pow j).trans (Finset.mem_Icc.1 hk'.1).1, hk'.2⟩
  have h2 := eLpNorm_blk_le χ j _ f g hr0 hr1.le hk
  have h3 := card_rpow_mul_le (c := D.τ 0) (β := -(D.θ / 4) + ε) hQ1 hr0 hC.le hcard
    (eLpNorm f (ENNReal.ofReal p) Measure.count * eLpNorm g (ENNReal.ofReal q) Measure.count)
  have e : D.τ 0 * (1 / r) + (-(D.θ / 4) + ε) = D.τ 0 / r - D.θ / 4 + ε := by ring
  rw [e] at h3
  rw [mul_assoc]
  exact h2.trans h3

end PrimeBHT.FinalGlue
