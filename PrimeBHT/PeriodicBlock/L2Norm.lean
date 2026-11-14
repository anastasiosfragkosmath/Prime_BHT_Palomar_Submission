module

public import PrimeBHT.PeriodicBlock.Basic
public import PrimeCarleson.Proof.Paper.P5.Periodic
public import PrimeCarleson.Proof.Goal0.Exponents

/-!
# The `p = 2` case (blueprint N30): `‖Λ_B‖²_{L²(Y_N)} = ∑_{q ∈ B} 1/φ(q)`

`lam_intCast` identifies `lam B N` with the audited `blockWeight B` on representatives;
`l2_lam_sq` computes the `L²(Y_N)` norm (orthogonality of the characters of the distinct reduced
fractions, via the vendored `avg_blockWeight_mul_e_neg`), `sum_inv_totient_le` is the explicit-`ε`
bound `1/φ(q) ≤ C Q^{ε-1}` summed over `B`, and `l2_bilinAvg_lam_le` is the final
`d_B(2) ≤ C |B|^{1/2} Q^{-1/2+ε/2}` statement.
-/

@[expose] public section

namespace PrimeBHT.PeriodicBlock

open Finset PrimeCarleson PrimeCarleson.Proof.Paper PrimeCarleson.Proof.Goal0
open scoped BigOperators ComplexConjugate

theorem blockWeight_add_mul_of_dvd {B : Finset ℕ} {N : ℕ} (hBN : ∀ q ∈ B, q ∣ N) (n k : ℤ) :
    blockWeight B (n + N * k) = blockWeight B n := by
  unfold blockWeight
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨m, hm⟩ := hBN q hq
  rw [hm]
  have : n + ((q * m : ℕ) : ℤ) * k = n + q * (m * k) := by push_cast; ring
  rw [this, ramanujanSum_add_mul]

/-- `Λ_B` on `Y_N` is the periodic function `blockWeight B`: `Λ_B(n mod N) = w_{Q,B}(n)`. -/
theorem lam_intCast {B : Finset ℕ} {N : ℕ} [NeZero N] (hBN : ∀ q ∈ B, q ∣ N) (n : ℤ) :
    lam B N (n : ZMod N) = blockWeight B n := by
  unfold lam
  have h : (((n : ZMod N).val : ℕ) : ℤ) = n % N := ZMod.val_intCast n
  rw [h]
  have h2 : n % N + N * (n / N) = n := Int.emod_add_mul_ediv n N
  conv_rhs => rw [← h2]
  exact (blockWeight_add_mul_of_dvd hBN _ _).symm

theorem sum_zmod_val {M : Type*} [AddCommMonoid M] (N : ℕ) [NeZero N] (f : ℕ → M) :
    ∑ r : ZMod N, f r.val = ∑ l ∈ range N, f l := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  exact Fin.sum_univ_eq_sum_range f (k + 1)

theorem card_filter_coprime_range (q : ℕ) :
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
  rw [Nat.totient_eq_card_coprime]
  congr 1
  exact Finset.filter_congr fun a _ => Nat.coprime_comm

/-- Orthonormality of the characters of the distinct reduced fractions, in the form
`∑_{ρ ∈ Γ_B} |μ(ρ.den)/φ(ρ.den)|² = ∑_{q ∈ B} 1/φ(q)` (`μ² = 1` for squarefree `q`). -/
theorem sum_norm_sq_coefFrac {B : Finset ℕ} (hB : ∀ q ∈ B, Squarefree q) :
    ∑ r ∈ reducedFractions B, ‖coefFrac r‖ ^ 2 = ∑ q ∈ B, ((q.totient : ℝ))⁻¹ := by
  rw [sum_reducedFractions]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq0 : 0 < q := Nat.pos_of_ne_zero (hB q hq).ne_zero
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq0
  have hμ : (((ArithmeticFunction.moebius q : ℤ) : ℝ)) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hB q hq)
  have key : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ‖coefFrac ((a : ℚ) / q)‖ ^ 2 = ((q.totient : ℝ))⁻¹ ^ 2 := by
    intro a ha
    rw [Finset.mem_filter] at ha
    unfold coefFrac
    rw [den_natCast_div hq0 ha.2, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, div_pow, hμ, one_div, inv_pow]
  rw [Finset.sum_congr rfl key, Finset.sum_const, card_filter_coprime_range, nsmul_eq_mul]
  field_simp

/-- **N30, the norm of `Λ_B`**: for `N = 𝒬_B = lcm B` and `B` squarefree,
`‖Λ_B‖²_{L²(Y_N)} = ∑_{q ∈ B} 1/φ(q)`. -/
theorem expect_norm_sq_lam {B : Finset ℕ} (hB : ∀ q ∈ B, Squarefree q) {N : ℕ} [NeZero N]
    (hN : lcmQ B = N) :
    𝔼 r : ZMod N, ‖lam B N r‖ ^ 2 = ∑ q ∈ B, ((q.totient : ℝ))⁻¹ := by
  subst hN
  have hpos : ∀ q ∈ B, 0 < q := fun q hq => Nat.pos_of_ne_zero (hB q hq).ne_zero
  have hNC : ((lcmQ B : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (lcmQ_pos hpos).ne'
  have hconj : ∀ l : ℕ, conj (blockWeight B (l : ℤ)) =
      ∑ r ∈ reducedFractions B, conj (coefFrac r) * e (-((l : ℝ) * (r : ℝ))) := by
    intro l
    rw [blockWeight_eq_sum_reducedFractions, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_mul, e_neg, Int.cast_natCast]
    rfl
  have h1 : ∀ l : ℕ, blockWeight B (l : ℤ) * conj (blockWeight B (l : ℤ)) =
      ∑ r ∈ reducedFractions B,
        conj (coefFrac r) * (blockWeight B (l : ℤ) * e (-((l : ℝ) * (r : ℝ)))) := by
    intro l
    rw [hconj, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  have h2 : ∑ l ∈ range (lcmQ B), blockWeight B (l : ℤ) * conj (blockWeight B (l : ℤ)) =
      (lcmQ B : ℂ) * ∑ r ∈ reducedFractions B, conj (coefFrac r) * coefFrac r := by
    simp_rw [h1]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [← Finset.mul_sum]
    have := avg_blockWeight_mul_e_neg hpos hr
    rw [inv_mul_eq_iff_eq_mul₀ hNC] at this
    rw [this]
    ring
  have h3 : (((𝔼 r : ZMod (lcmQ B), ‖lam B (lcmQ B) r‖ ^ 2 : ℝ)) : ℂ) =
      (((∑ q ∈ B, ((q.totient : ℝ))⁻¹ : ℝ)) : ℂ) := by
    rw [show (((𝔼 r : ZMod (lcmQ B), ‖lam B (lcmQ B) r‖ ^ 2 : ℝ)) : ℂ) =
        𝔼 r : ZMod (lcmQ B), ((‖lam B (lcmQ B) r‖ ^ 2 : ℝ) : ℂ) from
      RCLike.ofReal_expect (K := ℂ) _ _, Fintype.expect_eq_sum_div_card, ZMod.card]
    have h4 : ∀ r : ZMod (lcmQ B), ((‖lam B (lcmQ B) r‖ ^ 2 : ℝ) : ℂ) =
        blockWeight B (r.val : ℤ) * conj (blockWeight B (r.val : ℤ)) := by
      intro r
      rw [Complex.ofReal_pow, ← Complex.mul_conj']
      rfl
    simp_rw [h4]
    rw [sum_zmod_val (lcmQ B) (fun l => blockWeight B (l : ℤ) * conj (blockWeight B (l : ℤ))),
      h2, ← sum_norm_sq_coefFrac hB]
    push_cast
    field_simp
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_comm, Complex.mul_conj']
  exact_mod_cast h3

/-- **N30**: `‖Λ_B‖²_{L²(Y_N)} = ∑_{q ∈ B} 1/φ(q)`, with the `L²` norm `l2`. -/
theorem l2_lam_sq {B : Finset ℕ} (hB : ∀ q ∈ B, Squarefree q) {N : ℕ} [NeZero N]
    (hN : lcmQ B = N) : l2 (lam B N) ^ 2 = ∑ q ∈ B, ((q.totient : ℝ))⁻¹ := by
  rw [l2_sq]
  exact expect_norm_sq_lam hB hN

/-- **(A2), explicit `ε`-form**: `∑_{q ∈ B} 1/φ(q) ≤ C_ε |B| Q^{ε-1}` for `B ⊆ (Q/2, Q]`, `Q ≥ 1`. -/
theorem exists_sum_inv_totient_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ) (B : Finset ℕ), 1 ≤ Q → (∀ q ∈ B, Q / 2 < (q : ℝ) ∧ (q : ℝ) ≤ Q) →
      ∑ q ∈ B, ((q.totient : ℝ))⁻¹ ≤ C * B.card * Q ^ (ε - 1) := by
  obtain ⟨C, hC1, hC⟩ := exists_card_divisors_le_rpow hε
  refine ⟨2 * C, by linarith, fun Q B hQ hB => ?_⟩
  calc ∑ q ∈ B, ((q.totient : ℝ))⁻¹ ≤ ∑ _q ∈ B, 2 * C * Q ^ (ε - 1) := by
        refine Finset.sum_le_sum fun q hq => ?_
        obtain ⟨h1, h2⟩ := hB q hq
        have hq0 : 0 < q := by
          have : (0 : ℝ) < q := by linarith
          exact_mod_cast this
        exact inv_totient_le hε hε1 hC hq0 h1.le hQ
    _ = 2 * C * B.card * Q ^ (ε - 1) := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **N30 (explicit form)**: for `N = 𝒬_B` and `B ⊆ (Q/2, Q]` squarefree,
`‖Λ_B‖_{L²(Y_N)} ≤ (C_ε |B|)^{1/2} Q^{-(1-ε)/2}`. -/
theorem exists_l2_lam_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ) (B : Finset ℕ), 1 ≤ Q → (∀ q ∈ B, Q / 2 < (q : ℝ) ∧ (q : ℝ) ≤ Q) →
      (∀ q ∈ B, Squarefree q) → ∀ (N : ℕ) [NeZero N], lcmQ B = N →
        l2 (lam B N) ≤ √(C * B.card) * Q ^ ((ε - 1) / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_sum_inv_totient_le hε hε1
  refine ⟨C, hC0, fun Q B hQ hBQ hsq N _ hN => ?_⟩
  have hQ0 : 0 < Q := by linarith
  have h1 := l2_lam_sq hsq hN
  have h2 := hC Q B hQ hBQ
  have h3 : l2 (lam B N) ≤ √(∑ q ∈ B, ((q.totient : ℝ))⁻¹) := by
    rw [← h1, Real.sqrt_sq (l2_nonneg _)]
  refine h3.trans ?_
  calc √(∑ q ∈ B, ((q.totient : ℝ))⁻¹) ≤ √(C * B.card * Q ^ (ε - 1)) := Real.sqrt_le_sqrt h2
    _ = √(C * B.card) * Q ^ ((ε - 1) / 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow (Q ^ (ε - 1)),
          ← Real.rpow_mul hQ0.le]
        congr 2
        ring

/-- **N30, `d_B(2) ≲ |B|^{1/2} Q^{-1/2+o(1)}`** in explicit-`ε` form: with `C = C_ε` of
`exists_l2_lam_le`, `‖A_B(F,G)‖_{L²} ≤ (C |B|)^{1/2} Q^{-(1-ε)/2} ‖F‖_{L²} ‖G‖_{L²}`. -/
theorem exists_l2_bilinAvg_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ) (B : Finset ℕ), 1 ≤ Q → (∀ q ∈ B, Q / 2 < (q : ℝ) ∧ (q : ℝ) ≤ Q) →
      (∀ q ∈ B, Squarefree q) → ∀ (N : ℕ) [NeZero N], lcmQ B = N → ∀ F G : ZMod N → ℂ,
        l2 (bilinAvg (lam B N) F G) ≤ √(C * B.card) * Q ^ ((ε - 1) / 2) * l2 F * l2 G := by
  obtain ⟨C, hC0, hC⟩ := exists_l2_lam_le hε hε1
  refine ⟨C, hC0, fun Q B hQ hBQ hsq N _ hN F G => ?_⟩
  have h1 := l2_bilinAvg_le (lam B N) F G
  have h2 := hC Q B hQ hBQ hsq N hN
  refine h1.trans ?_
  have := l2_nonneg F; have := l2_nonneg G
  gcongr

end PrimeBHT.PeriodicBlock
