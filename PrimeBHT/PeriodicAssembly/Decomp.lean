module

public import PrimeBHT.Periodic
public import PrimeBHT.PeriodicBlock

/-!
# The divisor-sum decomposition of `A_B` (blueprint N31(c))

For `B` a finite set of squarefree naturals, `N` squarefree with `q ∣ N` for all `q ∈ B`:
`A_B(F,G) = ∑_{d | N} μ(d) β_d A_d(F,G)` as functions on `Y_N = ZMod N`, where
`A_B = bilinAvg (lam B N)` and `A_d = Split.A (Split.ofDvd _ _)`.

`Ad` is the total version of `A_d` (it is `0` for `d ∤ N`), so the sum can be indexed by
`N.divisors`.  Also here: the bridge `PeriodicBlock.l2 = Periodic.l2`.
-/

@[expose] public section

namespace PrimeBHT.PeriodicAssembly

open Finset PrimeBHT.Periodic
open scoped BigOperators ComplexConjugate

/-- `A_d` for `d ∣ N` (`N` squarefree), extended by `0` for `d ∤ N`. -/
noncomputable def Ad {N : ℕ} [NeZero N] (hN : Squarefree N) (d : ℕ) (F G : ZMod N → ℂ) :
    ZMod N → ℂ :=
  if h : d ∣ N then (Split.ofDvd hN h).A F G else 0

theorem Ad_of_dvd {N : ℕ} [NeZero N] (hN : Squarefree N) {d : ℕ} (hd : d ∣ N)
    (F G : ZMod N → ℂ) : Ad hN d F G = (Split.ofDvd hN hd).A F G := by
  unfold Ad
  simp [hd]

theorem emb_ofDvd {N : ℕ} [NeZero N] (hN : Squarefree N) {d : ℕ} (hd : d ∣ N) (l : ZMod (N / d)) :
    (Split.ofDvd hN hd).emb l = (((d * l.val : ℕ)) : ZMod N) := by
  unfold Split.emb
  push_cast
  rfl

/-- **N31(c).** `A_B(F,G)(y) = ∑_{d | N} μ(d) β_d A_d(F,G)(y)`. -/
theorem bilinAvg_lam_eq_sum_divisors {B : Finset ℕ} {N : ℕ} [NeZero N]
    (hsq : ∀ q ∈ B, Squarefree q) (hBN : ∀ q ∈ B, q ∣ N) (hN : Squarefree N)
    (F G : ZMod N → ℂ) (y : ZMod N) :
    PrimeBHT.PeriodicBlock.bilinAvg (PrimeBHT.PeriodicBlock.lam B N) F G y =
      ∑ d ∈ N.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (PrimeBHT.PeriodicBlock.beta B d : ℂ) * Ad hN d F G y := by
  unfold PrimeBHT.PeriodicBlock.bilinAvg
  simp_rw [PrimeBHT.PeriodicBlock.lam_eq_sum_divisors hsq hBN, Finset.sum_mul]
  rw [Finset.expect_sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdN : d ∣ N := Nat.dvd_of_mem_divisors hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdN (Nat.pos_of_ne_zero (NeZero.ne N))
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
  rw [Ad_of_dvd hN hdN]
  have : NeZero (N / d) := (Split.ofDvd hN hdN).neZero_D
  have h1 : ∀ r : ZMod N,
      (d : ℂ) * ((ArithmeticFunction.moebius d : ℤ) : ℂ) * (PrimeBHT.PeriodicBlock.beta B d : ℂ) *
        (if d ∣ r.val then (1 : ℂ) else 0) * F (y - r) * G (y + r) =
      ((d : ℂ) * ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (PrimeBHT.PeriodicBlock.beta B d : ℂ)) *
        (if d ∣ r.val then F (y - r) * G (y + r) else 0) := by
    intro r
    split_ifs <;> ring
  simp_rw [h1]
  rw [← Finset.mul_expect]
  have h2 := PrimeBHT.PeriodicBlock.expect_ite_dvd_val (N := N) (d := d) (D := N / d)
    (Nat.mul_div_cancel' hdN) hdpos (fun r => F (y - r) * G (y + r))
  rw [h2]
  unfold Split.A
  have h3 : ∀ l : ZMod (N / d),
      F (y - (Split.ofDvd hN hdN).emb l) * G (y + (Split.ofDvd hN hdN).emb l) =
      F (y - (((d * l.val : ℕ)) : ZMod N)) * G (y + (((d * l.val : ℕ)) : ZMod N)) := by
    intro l
    rw [emb_ofDvd hN hdN l]
  simp_rw [Split.ofDvd_D]
  simp_rw [h3]
  rw [← mul_assoc]
  congr 1
  field_simp

/-- **N31(c)** as an identity of functions on `Y_N`. -/
theorem bilinAvg_lam_eq_sum_divisors_fun {B : Finset ℕ} {N : ℕ} [NeZero N]
    (hsq : ∀ q ∈ B, Squarefree q) (hBN : ∀ q ∈ B, q ∣ N) (hN : Squarefree N)
    (F G : ZMod N → ℂ) :
    PrimeBHT.PeriodicBlock.bilinAvg (PrimeBHT.PeriodicBlock.lam B N) F G =
      ∑ d ∈ N.divisors, (((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (PrimeBHT.PeriodicBlock.beta B d : ℂ)) • Ad hN d F G := by
  funext y
  rw [bilinAvg_lam_eq_sum_divisors hsq hBN hN F G y, Finset.sum_apply]
  rfl

end PrimeBHT.PeriodicAssembly
