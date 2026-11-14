module

public import PrimeBHT.MainBanach.Ops
public import PrimeBHT.ErrorTerms
public import PrimeBHT.FinalSum
public import PrimeBHT.FinalAssembly

/-!
# S24 (gate G1): the component estimates for the case `r ≥ 1`

All statements are uniform in the truncation `J` (the index of the family is the pair `(j, J)`,
`Q = 2^j`).  Inputs: the anchors `Key0Prop χ` (N26) and `BHTSmooth χ p' q' r' C'` (X1) at Banach
tuples; everything else is proved from the built modules.

* `Tfam χ τ (j, J) = H^J_{Q,mod;τ} + U^J_{Q;τ}` as a bilinear map (`Tfam_apply`).
* (A) `family_L1_decay`: `‖Tfam‖_{2,2→1} ≤ C Q^{-1/20}` (`τ = 1/6`): moderate part from
  `eLpNorm_single_L1`, tail from `Key0Prop`.
* (B) `family_progression_decay`: `‖Tfam‖_{p₁,q₁→r₁} ≤ C Q^ε` at every Banach tuple.
* `exists_hH`: the decay `C_H Q^{-σ}` at the target `(p, q, r)`, `r ≥ 1` (N51), via
  `FinalAssembly.exists_power_saving_of_estimates`.
-/

@[expose] public noncomputable section

open MeasureTheory PrimeBHT.Kernel PrimeBHT.Decomposition PrimeBHT.Exponents PrimeBHT.FinalAssembly
open scoped ENNReal

namespace PrimeBHT.MainBanach

open PrimeBHT.SingleScaleL1 (single single_apply)
open PrimeBHT.Progression (BHTSmooth)

/-! ## Counting -/

/-- `(#F)^{1/r} (C Q^β N) ≤ C Q^{c/r+β} N` for `#F ≤ Q^c`. -/
theorem card_rpow_mul_le {n : ℕ} {Q c r β C : ℝ} (hQ : 1 ≤ Q) (hr : 0 < r) (hC : 0 ≤ C)
    (hn : (n : ℝ) ≤ Q ^ c) (N : ℝ≥0∞) :
    (n : ℝ≥0∞) ^ (1 / r) * (ENNReal.ofReal (C * Q ^ β) * N) ≤
      ENNReal.ofReal (C * Q ^ (c * (1 / r) + β)) * N := by
  have hQ0 : 0 < Q := by linarith
  have h1 : ((n : ℝ) ^ (1 / r)) ≤ Q ^ (c * (1 / r)) := by
    rw [Real.rpow_mul hQ0.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg n) hn (by positivity)
  calc (n : ℝ≥0∞) ^ (1 / r) * (ENNReal.ofReal (C * Q ^ β) * N)
      = ENNReal.ofReal ((n : ℝ) ^ (1 / r) * (C * Q ^ β)) * N := by
        rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg n)
          (by positivity), ← mul_assoc,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    _ ≤ ENNReal.ofReal (C * Q ^ (c * (1 / r) + β)) * N := by
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) N
        rw [Real.rpow_add hQ0]
        calc (n : ℝ) ^ (1 / r) * (C * Q ^ β) ≤ Q ^ (c * (1 / r)) * (C * Q ^ β) := by gcongr
          _ = C * (Q ^ (c * (1 / r)) * Q ^ β) := by ring

theorem ofReal_add_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (N M : ℝ≥0∞) :
    ENNReal.ofReal a * N * M + ENNReal.ofReal b * N * M = ENNReal.ofReal (a + b) * N * M := by
  rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add ha hb]

/-! ## The family `Tfam` -/

/-- The scales `b_Q ≤ k ≤ J`, `k < Q^τ` of the moderate part. -/
def Hset (τ : ℝ) (j J : ℕ) : Finset ℕ :=
  (Finset.Icc (bQ ((2 : ℝ) ^ j)) J).filter (fun k : ℕ => (k : ℝ) < ((2 : ℝ) ^ j) ^ τ)

/-- The scales `⌈Q^τ⌉ ≤ k ≤ J` of the tail. -/
def Uset (τ : ℝ) (j J : ℕ) : Finset ℕ := Finset.Icc ⌈((2 : ℝ) ^ j) ^ τ⌉₊ J

/-- `H^J_{Q,mod;τ} + U^J_{Q;τ}` for `i = (j, J)`, `Q = 2^j`, as a bilinear map. -/
def Tfam (χ : ℝ → ℝ) (τ : ℝ) (i : ℕ × ℕ) : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ) :=
  blk χ i.1 (Hset τ i.1 i.2) + blk χ i.1 (Uset τ i.1 i.2)

theorem Tfam_apply_add (χ : ℝ → ℝ) (τ : ℝ) (i : ℕ × ℕ) (f g : ℤ →₀ ℂ) :
    Tfam χ τ i f g = blk χ i.1 (Hset τ i.1 i.2) f g + blk χ i.1 (Uset τ i.1 i.2) f g := rfl

theorem Tfam_apply {χ : ℝ → ℝ} (hχ : IsCutoff χ) (τ : ℝ) (i : ℕ × ℕ) (f g : ℤ →₀ ℂ) :
    Tfam χ τ i f g = Hmod χ τ i.2 i.1 ⇑f ⇑g + Utail χ τ i.2 i.1 ⇑f ⇑g := by
  rw [Tfam_apply_add, Hmod_eq_blk hχ, Utail_eq_blk hχ]
  rfl

theorem Hset_eq_Icc (τ : ℝ) (j J : ℕ) :
    Hset τ j J = Finset.Icc (bQ ((2 : ℝ) ^ j)) (min J (⌈((2 : ℝ) ^ j) ^ τ⌉₊ - 1)) := by
  have h1 : 1 ≤ ⌈((2 : ℝ) ^ j) ^ τ⌉₊ :=
    Nat.one_le_ceil_iff.2 (Real.rpow_pos_of_pos (by positivity) _)
  have hb := one_le_bQ_two_pow j
  ext k
  simp only [Hset, Finset.mem_filter, Finset.mem_Icc, ← Nat.lt_ceil]
  omega

theorem one_le_ceil_two_pow {τ : ℝ} (j : ℕ) : 1 ≤ ⌈((2 : ℝ) ^ j) ^ τ⌉₊ :=
  Nat.one_le_ceil_iff.2 (Real.rpow_pos_of_pos (by positivity) _)

/-! ## (A) the `(2,2,1)` estimate -/

/-- The tail `[⌈Q^τ⌉, J]`, from `Key0Prop χ`. -/
theorem blk_tail_decay_of_key0 {χ : ℝ → ℝ} (hK : Key0Prop χ) (hχ : IsCutoff χ) {τ : ℝ}
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

/-- The moderate part `∑_{b_Q ≤ k < Q^τ} T_k^Q`: at most `Q^τ` scales, each `≲ Q^{-1/4+ε}`
(`eLpNorm_single_L1`, `k ≥ b_Q`), summed in `ℓ¹`. -/
theorem blk_moderate_decay {χ : ℝ → ℝ} (hχ : IsCutoff χ) {τ ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ j J : ℕ, ∀ f g : ℤ →₀ ℂ,
      eLpNorm (blk χ j (Hset τ j J) f g) (ENNReal.ofReal 1) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (τ + (-1 / 4 + ε))) *
          eLpNorm f (ENNReal.ofReal 2) Measure.count *
            eLpNorm g (ENNReal.ofReal 2) Measure.count := by
  obtain ⟨C, hC, h⟩ := PrimeBHT.SingleScaleL1.eLpNorm_single_L1 hχ hε
  refine ⟨C + 1, by linarith, fun j J f g => ?_⟩
  have hQ1 := one_le_two_pow_real j
  have hk : ∀ k ∈ Hset τ j J,
      eLpNorm (single χ (2 ^ j) k f g) (ENNReal.ofReal 1) Measure.count ≤
        ENNReal.ofReal ((C + 1) * ((2 : ℝ) ^ j) ^ (-1 / 4 + ε)) *
          (eLpNorm f (ENNReal.ofReal 2) Measure.count *
            eLpNorm g (ENNReal.ofReal 2) Measure.count) := by
    intro k hk
    have hk' := Finset.mem_filter.1 hk
    rw [single_apply hχ]
    have h1 := h (2 ^ j) k Nat.one_le_two_pow (q_lt_eight_or (Finset.mem_Icc.1 hk'.1).1) f g
    rw [pow_cast_two] at h1
    simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
    refine h1.trans ?_
    rw [mul_assoc]
    exact mul_le_mul' (PrimeBHT.GroupDecay.ofReal_mul_rpow_le hQ1 hC (by linarith) le_rfl) le_rfl
  have hcard : ((Hset τ j J).card : ℝ) ≤ ((2 : ℝ) ^ j) ^ τ := by
    refine card_le_of_mem (Real.rpow_pos_of_pos (by positivity) _) fun k hk => ?_
    have hk' := Finset.mem_filter.1 hk
    exact ⟨(one_le_bQ_two_pow j).trans (Finset.mem_Icc.1 hk'.1).1, hk'.2⟩
  have h2 := eLpNorm_blk_le χ j _ f g one_pos le_rfl hk
  have h3 := card_rpow_mul_le (c := τ) (r := 1) (β := -1 / 4 + ε) (C := C + 1) hQ1 one_pos (by linarith) hcard
    (eLpNorm f (ENNReal.ofReal 2) Measure.count * eLpNorm g (ENNReal.ofReal 2) Measure.count)
  have e : τ * (1 / 1) + (-1 / 4 + ε) = τ + (-1 / 4 + ε) := by ring
  rw [e] at h3
  rw [mul_assoc]
  exact h2.trans h3

/-- **(A)**: `‖H_{mod;1/6} + U_{;1/6}‖_{2,2→1} ≤ C Q^{-1/20}`, uniformly in `J`. -/
theorem family_L1_decay {χ : ℝ → ℝ} (hK : Key0Prop χ) (hχ : IsCutoff χ) :
    ∃ C_A Q₀ : ℝ, 0 < C_A ∧ ∀ i : ℕ × ℕ, Q₀ ≤ (2 : ℝ) ^ i.1 → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (Tfam χ (1 / 6) i f g) (ENNReal.ofReal 1) Measure.count ≤
        ENNReal.ofReal (C_A * ((2 : ℝ) ^ i.1) ^ (-(1 / 20 : ℝ))) *
          eLpNorm f (ENNReal.ofReal 2) Measure.count * eLpNorm g (ENNReal.ofReal 2) Measure.count := by
  obtain ⟨C₁, Q₁, hC₁, h₁⟩ := blk_tail_decay_of_key0 hK hχ (τ := 1 / 6) (by norm_num) (by norm_num)
    (ε := 1 / 30) (by norm_num)
  obtain ⟨C₂, hC₂, h₂⟩ := blk_moderate_decay hχ (τ := 1 / 6) (ε := 1 / 30) (by norm_num)
  refine ⟨C₁ + C₂, Q₁, by linarith, fun i hi f g => ?_⟩
  have e1 : -((1 / 6 : ℝ) / 2) + 1 / 30 = -(1 / 20) := by norm_num
  have e2 : ((1 / 6 : ℝ) + (-1 / 4 + 1 / 30)) = -(1 / 20) := by norm_num
  have hH := h₂ i.1 i.2 f g
  have hU := h₁ i.1 i.2 hi f g
  rw [e2] at hH
  rw [e1] at hU
  rw [Tfam_apply_add]
  refine (eLpNorm_add_le (ENNReal.one_le_ofReal.2 le_rfl)).trans ?_
  refine (add_le_add hH hU).trans (le_of_eq ?_)
  have hX : 0 ≤ ((2 : ℝ) ^ i.1) ^ (-(1 / 20 : ℝ)) := Real.rpow_nonneg (by positivity) _
  rw [ofReal_add_mul (mul_nonneg hC₂.le hX) (mul_nonneg hC₁.le hX), ← add_mul, add_comm C₂ C₁]

/-! ## (B) the progression estimate for the family at Banach tuples -/

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

/-- **(B)**: at every Banach tuple `(p₁, q₁, r₁)` (`1 < p₁, q₁`, `1/p₁ + 1/q₁ ≤ 1`,
`1/r₁ = 1/p₁ + 1/q₁`) the family satisfies `‖Tfam‖_{p₁,q₁→r₁} ≤ C Q^ε`, uniformly in `J`.
Conditional on `BHTSmooth χ p₁ q₁ r₁ C₁` at the Banach tuples (hypothesis `hX`). -/
theorem family_progression_decay {χ : ℝ → ℝ} (hχ : IsCutoff χ)
    (hX : ∀ p' q' r' : ℝ, 1 < p' → 1 < q' → 1 / r' = 1 / p' + 1 / q' → 1 ≤ r' →
      ∃ C' : ℝ, BHTSmooth χ p' q' r' C') :
    ∀ p₁ q₁ r₁ : ℝ, 1 < p₁ → 1 < q₁ → 1 / p₁ + 1 / q₁ ≤ 1 → 1 / r₁ = 1 / p₁ + 1 / q₁ →
      ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i : ℕ × ℕ, Q₁ ≤ (2 : ℝ) ^ i.1 → ∀ f g : ℤ →₀ ℂ,
        eLpNorm (Tfam χ (1 / 6) i f g) (ENNReal.ofReal r₁) Measure.count ≤
          ENNReal.ofReal (C * ((2 : ℝ) ^ i.1) ^ ε) *
            eLpNorm f (ENNReal.ofReal p₁) Measure.count *
              eLpNorm g (ENNReal.ofReal q₁) Measure.count := by
  intro p₁ q₁ r₁ hp hq hsum hr₁ ε hε
  have hr₀ : 0 < r₁ := by
    have h1 := one_div_pos.2 (lt_trans one_pos hp)
    have h2 := one_div_pos.2 (lt_trans one_pos hq)
    exact one_div_pos.1 (by rw [hr₁]; linarith)
  have hr1' : 1 / r₁ ≤ 1 := by rw [hr₁]; exact hsum
  have hr1 : 1 ≤ r₁ := by
    rw [div_le_one hr₀] at hr1'
    exact hr1'
  obtain ⟨C₀, hX₀⟩ := hX p₁ q₁ r₁ hp hq hr₁ hr1
  obtain ⟨C', hC', h⟩ := blk_progression_of_bhtSmooth hχ (lt_trans one_pos hp)
    (lt_trans one_pos hq) hr₀ hr₁ hX₀ hε
  have hmax : max (1 / r₁ - 1) 0 = 0 := max_eq_right (by linarith)
  refine ⟨C' + C', 1, by linarith, fun i _ f g => ?_⟩
  rw [Tfam_apply_add]
  refine (eLpNorm_add_le (ENNReal.one_le_ofReal.2 hr1)).trans ?_
  have hH := h i.1 (bQ ((2 : ℝ) ^ i.1)) (min i.2 (⌈((2 : ℝ) ^ i.1) ^ (1 / 6 : ℝ)⌉₊ - 1))
    (one_le_bQ_two_pow _) f g
  have hU := h i.1 ⌈((2 : ℝ) ^ i.1) ^ (1 / 6 : ℝ)⌉₊ i.2 (one_le_ceil_two_pow _) f g
  rw [hmax, zero_add] at hH hU
  rw [Hset_eq_Icc]
  refine (add_le_add hH hU).trans (le_of_eq ?_)
  have hX' : 0 ≤ ((2 : ℝ) ^ i.1) ^ ε := Real.rpow_nonneg (by positivity) _
  rw [ofReal_add_mul (mul_nonneg hC'.le hX') (mul_nonneg hC'.le hX'), ← add_mul]

/-! ## The decay at the target tuple (N51) -/

/-- **N51 (the case `r ≥ 1`), conditional on `Key0Prop χ` and `BHTSmooth` at the Banach tuples**:
for `(p, q, r) ∈ R`, `r ≥ 1` there are `σ, C_H > 0` and `j₁` with
`‖H^J_{Q,mod;1/6} + U^J_{Q;1/6}‖_{ℓ^r} ≤ C_H Q^{-σ} ‖f‖_p ‖g‖_q` for every `Q = 2^j`, `j > j₁`
and every `J`. -/
theorem exists_hH_of_key0 {χ : ℝ → ℝ} (hK : Key0Prop χ) (hχ : IsCutoff χ)
    (hX : ∀ p' q' r' : ℝ, 1 < p' → 1 < q' → 1 / r' = 1 / p' + 1 / q' → 1 ≤ r' →
      ∃ C' : ℝ, BHTSmooth χ p' q' r' C')
    {p q r : ℝ} (hR : InR p q r) (hr : 1 ≤ r) :
    ∃ σ C_H : ℝ, 0 < σ ∧ 0 < C_H ∧ ∃ j₁ : ℕ, ∀ f g : ℤ →₀ ℂ, ∀ j J : ℕ, j₁ < j →
      eLpNorm (Hmod χ (1 / 6) J j ⇑f ⇑g + Utail χ (1 / 6) J j ⇑f ⇑g) (ENNReal.ofReal r)
          Measure.count ≤
        ENNReal.ofReal (C_H * ((2 : ℝ) ^ j) ^ (-σ)) *
          eLpNorm ⇑f (ENNReal.ofReal p) Measure.count *
            eLpNorm ⇑g (ENNReal.ofReal q) Measure.count := by
  obtain ⟨C_A, Q₀, hCA, hA⟩ := family_L1_decay hK hχ
  have hB := family_progression_decay hχ hX
  obtain ⟨σ, C, Q₁, hσ, hC, h⟩ := exists_power_saving_of_estimates (Tfam χ (1 / 6))
    (fun i : ℕ × ℕ => (2 : ℝ) ^ i.1) hR hr hCA hA hB
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt Q₁ (one_lt_two : (1 : ℝ) < 2)
  refine ⟨σ, C, hσ, hC, n, fun f g j J hj => ?_⟩
  have h1 := h (j, J) (le_trans hn.le (pow_le_pow_right₀ (by norm_num) hj.le)) f g
  rw [Tfam_apply hχ] at h1
  exact h1

end PrimeBHT.MainBanach

end
