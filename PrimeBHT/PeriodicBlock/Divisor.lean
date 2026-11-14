module

public import PrimeBHT.PeriodicBlock.L2Norm
public import PrimeCarleson.Proof.Goal0.Divisors

/-!
# The divisor-sum decomposition (blueprint N31, identities (a) and (d))

* `lam_eq_sum_divisors` (N31(a)): `Λ_B(r) = ∑_{d | N} d μ(d) β_d 1_{d | r}` on `Y_N`, with
  `β_d = ∑_{q ∈ B, d | q} 1/φ(q)` (`beta`); it uses `μ(q) μ(q/d) = μ(d)` for squarefree `q`, `d ∣ q`
  (`moebius_mul_moebius_div_of_squarefree`) and the audited identity
  `ramanujanSum_eq_sum_divisors`.
* `sum_beta_eq` (N31(d)): `a_B = ∑_{d | N} β_d = ∑_{q ∈ B} d_div(q)/φ(q)`, and
  `exists_sum_beta_le`: `a_B ≤ C_ε |B| Q^{ε-1}`.
-/

@[expose] public section

namespace PrimeBHT.PeriodicBlock

open Finset PrimeCarleson PrimeCarleson.Proof.Paper PrimeCarleson.Proof.Goal0
open scoped BigOperators ComplexConjugate

/-- `β_d = ∑_{q ∈ B, d ∣ q} 1/φ(q)`. -/
noncomputable def beta (B : Finset ℕ) (d : ℕ) : ℝ :=
  ∑ q ∈ B with d ∣ q, ((q.totient : ℝ))⁻¹

/-- For squarefree `q` and `f ∣ q`: `μ(q) μ(q/f) = μ(f)`. -/
theorem moebius_mul_moebius_div_of_squarefree {q f : ℕ} (hq : Squarefree q) (hf : f ∣ q) :
    ArithmeticFunction.moebius q * ArithmeticFunction.moebius (q / f) =
      ArithmeticFunction.moebius f := by
  have hcop : f.Coprime (q / f) := coprime_div_of_squarefree hq hf
  have h1 : ArithmeticFunction.moebius q =
      ArithmeticFunction.moebius f * ArithmeticFunction.moebius (q / f) := by
    conv_lhs => rw [← Nat.mul_div_cancel' hf]
    exact ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  have h2 : ArithmeticFunction.moebius (q / f) ^ 2 = 1 :=
    ArithmeticFunction.moebius_sq_eq_one_of_squarefree
      (hq.squarefree_of_dvd (Nat.div_dvd_of_dvd hf))
  rw [h1, mul_assoc, ← sq, h2, mul_one]

/-- **N31(a), integer form.** For squarefree `q ∈ B`,
`Λ_B(n) = ∑_{d | N} d μ(d) β_d 1_{d ∣ n}` for every `n : ℕ`. -/
theorem blockWeight_eq_sum_divisors {B : Finset ℕ} {N : ℕ} (hN : N ≠ 0)
    (hsq : ∀ q ∈ B, Squarefree q) (hBN : ∀ q ∈ B, q ∣ N) (n : ℕ) :
    blockWeight B (n : ℤ) = ∑ d ∈ N.divisors,
      (d : ℂ) * ((ArithmeticFunction.moebius d : ℤ) : ℂ) * (beta B d : ℂ) *
        (if d ∣ n then 1 else 0) := by
  unfold blockWeight
  have step1 : ∀ q ∈ B,
      (((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ) : ℂ) * ramanujanSum q n =
        ∑ f ∈ q.divisors with f ∣ n, (f : ℂ) * ((ArithmeticFunction.moebius f : ℤ) : ℂ) *
          (((q.totient : ℝ))⁻¹ : ℝ) := by
    intro q hq
    rw [ramanujanSum_eq_sum_divisors, Finset.mul_sum]
    refine Finset.sum_congr (by ext f; simp [Int.natCast_dvd_natCast]) fun f hf => ?_
    rw [Finset.mem_filter, Nat.mem_divisors] at hf
    have h := moebius_mul_moebius_div_of_squarefree (hsq q hq) hf.1.1
    have hc : ((ArithmeticFunction.moebius q : ℤ) : ℂ) *
        ((ArithmeticFunction.moebius (q / f) : ℤ) : ℂ) =
        ((ArithmeticFunction.moebius f : ℤ) : ℂ) := by exact_mod_cast h
    push_cast
    rw [div_eq_mul_inv]
    linear_combination ((f : ℂ) * ((Nat.totient q : ℂ))⁻¹) * hc
  rw [Finset.sum_congr rfl step1]
  rw [Finset.sum_comm' (t' := N.divisors.filter (fun d => d ∣ n))
    (s' := fun f => B.filter (fun q => f ∣ q))]
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    unfold beta
    push_cast
    rw [← Finset.mul_sum]
    split_ifs
    · ring
    · simp
  · intro q f
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨hq, ⟨⟨hfq, hq0⟩, hfn⟩⟩
      exact ⟨⟨hq, hfq⟩, ⟨⟨hfq.trans (hBN q hq), hN⟩, hfn⟩⟩
    · rintro ⟨⟨hq, hfq⟩, ⟨_, hfn⟩⟩
      exact ⟨hq, ⟨⟨hfq, (hsq q hq).ne_zero⟩, hfn⟩⟩

/-- **N31(a)** on `Y_N`: `Λ_B(r) = ∑_{d | N} d μ(d) β_d 1_{d | r}` for `r ∈ Y_N`
(`d ∣ r` meaning `d ∣ r.val`, equivalent to `(d : ZMod N) ∣ r` for `d ∣ N`, see
`natCast_dvd_iff_dvd_val`). -/
theorem lam_eq_sum_divisors {B : Finset ℕ} {N : ℕ} [NeZero N]
    (hsq : ∀ q ∈ B, Squarefree q) (hBN : ∀ q ∈ B, q ∣ N) (r : ZMod N) :
    lam B N r = ∑ d ∈ N.divisors,
      (d : ℂ) * ((ArithmeticFunction.moebius d : ℤ) : ℂ) * (beta B d : ℂ) *
        (if d ∣ r.val then 1 else 0) :=
  blockWeight_eq_sum_divisors (NeZero.ne N) hsq hBN r.val

/-- **N31(d), first identity**: `a_B = ∑_{d | N} β_d = ∑_{q ∈ B} d_div(q)/φ(q)`. -/
theorem sum_beta_eq {B : Finset ℕ} {N : ℕ} (hN : N ≠ 0) (hBN : ∀ q ∈ B, q ∣ N)
    (hq0 : ∀ q ∈ B, q ≠ 0) :
    ∑ d ∈ N.divisors, beta B d = ∑ q ∈ B, (q.divisors.card : ℝ) / (q.totient : ℝ) := by
  unfold beta
  rw [Finset.sum_comm' (t' := B) (s' := fun q => N.divisors.filter (fun d => d ∣ q))]
  · refine Finset.sum_congr rfl fun q hq => ?_
    rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    congr 2
    have : N.divisors.filter (fun d => d ∣ q) = q.divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨_, h⟩
        exact ⟨h, hq0 q hq⟩
      · rintro ⟨h, _⟩
        exact ⟨⟨h.trans (hBN q hq), hN⟩, h⟩
    rw [this]
  · intro d q
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨hd, hq, hdq⟩
      exact ⟨⟨hd, hdq⟩, hq⟩
    · rintro ⟨⟨hd, hdq⟩, hq⟩
      exact ⟨hd, hq, hdq⟩

/-- **N31(d), explicit bound**: `a_B = ∑_{d | N} β_d ≤ C_ε |B| Q^{ε-1}` for `B ⊆ (Q/2, Q]`. -/
theorem exists_sum_beta_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ) (B : Finset ℕ) (N : ℕ), N ≠ 0 → 1 ≤ Q → (∀ q ∈ B, q ∣ N) →
      (∀ q ∈ B, Q / 2 < (q : ℝ) ∧ (q : ℝ) ≤ Q) →
        ∑ d ∈ N.divisors, beta B d ≤ C * B.card * Q ^ (ε - 1) := by
  have hδ : 0 < ε / 2 := by linarith
  obtain ⟨C, hC1, hC⟩ := exists_card_divisors_le_rpow hδ
  refine ⟨2 * C * C, by positivity, fun Q B N hN hQ hBN hBQ => ?_⟩
  have hQ0 : 0 < Q := by linarith
  have hq0 : ∀ q ∈ B, 0 < q := fun q hq => by
    have : (0 : ℝ) < q := by linarith [(hBQ q hq).1]
    exact_mod_cast this
  rw [sum_beta_eq hN hBN fun q hq => (hq0 q hq).ne']
  calc ∑ q ∈ B, (q.divisors.card : ℝ) / (q.totient : ℝ)
      ≤ ∑ _q ∈ B, (C * Q ^ (ε / 2)) * (2 * C * Q ^ (ε / 2 - 1)) := by
        refine Finset.sum_le_sum fun q hq => ?_
        obtain ⟨h1, h2⟩ := hBQ q hq
        have hqR : (0 : ℝ) < q := by exact_mod_cast hq0 q hq
        have hτ : (q.divisors.card : ℝ) ≤ C * Q ^ (ε / 2) :=
          (hC q (hq0 q hq)).trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hqR.le h2 hδ.le) (by linarith))
        have hφ := inv_totient_le (C := C) (ε := ε / 2) hδ (by linarith) hC (hq0 q hq) h1.le hQ
        rw [div_eq_mul_inv]
        exact mul_le_mul hτ hφ (inv_nonneg.2 (Nat.cast_nonneg _)) (by positivity)
    _ = 2 * C * C * B.card * Q ^ (ε - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have : Q ^ (ε / 2) * Q ^ (ε / 2 - 1) = Q ^ (ε - 1) := by
          rw [← Real.rpow_add hQ0]; congr 1; ring
        calc (B.card : ℝ) * (C * Q ^ (ε / 2) * (2 * C * Q ^ (ε / 2 - 1)))
            = 2 * C * C * B.card * (Q ^ (ε / 2) * Q ^ (ε / 2 - 1)) := by ring
          _ = _ := by rw [this]

/-- **N31(b)**: for `N = d D`, `𝔼_{r ∈ Y_N} 1_{d | r} U(r) = d⁻¹ 𝔼_{l ∈ Y_D} U(d l)`
(`d l` denotes the class of `d · l.val` in `Y_N`). -/
theorem expect_ite_dvd_val {N d D : ℕ} [NeZero N] [NeZero D] (hND : d * D = N) (hd : 0 < d)
    (U : ZMod N → ℂ) :
    𝔼 r : ZMod N, (if d ∣ r.val then U r else 0) =
      (d : ℂ)⁻¹ * 𝔼 l : ZMod D, U (((d * l.val : ℕ)) : ZMod N) := by
  have hdN : d ∣ N := ⟨D, hND.symm⟩
  have hDd : N / d = D := by rw [← hND]; exact Nat.mul_div_cancel_left D hd
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have h := inv_mul_sum_ite_dvd (N := N) (d := d) hd hdN (fun r => (d : ℂ)⁻¹ * U (r : ZMod N))
  rw [hDd] at h
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, ZMod.card, ZMod.card]
  have e1 : ∑ r : ZMod N, (if d ∣ r.val then U r else 0) =
      ∑ r ∈ Finset.range N, (if d ∣ r then (d : ℂ) * ((d : ℂ)⁻¹ * U (r : ZMod N)) else 0) := by
    rw [← sum_zmod_val N (fun r => if d ∣ r then (d : ℂ) * ((d : ℂ)⁻¹ * U (r : ZMod N)) else 0)]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs
    · rw [← mul_assoc, mul_inv_cancel₀ hdC, one_mul, ZMod.natCast_zmod_val]
    · rfl
  have e2 : ∑ l : ZMod D, U (((d * l.val : ℕ)) : ZMod N) =
      d * ∑ l ∈ Finset.range D, ((d : ℂ)⁻¹ * U (((l * d : ℕ)) : ZMod N)) := by
    rw [← sum_zmod_val D (fun l => ((d : ℂ)⁻¹ * U (((l * d : ℕ)) : ZMod N))), Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc, mul_inv_cancel₀ hdC, one_mul, mul_comm d]
  rw [e1, e2, div_eq_inv_mul, h]
  have hDC : (D : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne D)
  field_simp

end PrimeBHT.PeriodicBlock
