module

public import PrimeBHT.Decomposition
public import PrimeBHT.Progression
import Mathlib.Analysis.PSeries

/-!
# S18: sum over `Q` and `k` and passage to the theorem (blueprint node N53, Lemma 1.4)

Everything here is *conditional on the component estimates* (named `…_of_estimates`), which the
consumer supplies.

**Part A: the abstract assembly (N53 steps 2, 3, 4, 5, 6).**  Fix `r > 0`, `s = min r 1`, `τ > 0`.
By `Decomposition.exactred` (with a threshold `j₂` such that `b_Q ≤ Q^τ` for dyadic `Q = 2^j`,
`j > j₂`), for finitely supported `f`
`H^J(f,g) = ∑_{k ≤ J} S_k^err + ∑_{j ≤ j₂} ∑_{k=b_Q}^J T_k^Q + ∑_{j > j₂} (H_{Q,mod} + U_Q)`
(`Q = 2^j`, `j ∈ jset J`).  Given

* `hE`  : `‖S_k^err‖_{ℓ^r} ≤ C_E k^{-100} ‖f‖_p ‖g‖_q` (`k ≥ 1`),
* `hProg` : `‖∑_{k=b_Q}^J T_k^Q‖_{ℓ^r} ≤ Cp(j) ‖f‖_p ‖g‖_q` (every `j`, every `J`; `e:progression`
  for the interval `I = [b_Q, J]`; the constant may depend on `Q = 2^j`),
* `hH`  : `‖H_{Q,mod} + U_Q‖_{ℓ^r} ≤ C_H Q^{-σ} ‖f‖_p ‖g‖_q` (`j > j₁`, every `J`),

the `s`-triangle inequality (`Progression.eLpNorm_sum_rpow_le`) gives
`‖H^J(f,g)‖_{ℓ^r} ≤ C ‖f‖_p ‖g‖_q` for all `J`, with
`C = assemblyConst r σ C_E C_H Cp j₂` (`exists_const_HJ_of_estimates`).

**Part B: Lemma 1.4.**  `hP f g x = ∑_{n ≠ 0} Λ(|n|)/n · f(x-n) g(x+n)` (literally the `primeBHT` of
`drafts/T0Statement.lean`); for finitely supported `f, g` there is `J₀` with `H^J = H_P` for all
`J ≥ J₀` (`exists_HJ_eq_hP`), and the uniform bound passes to `H_P` (`eLpNorm_hP_le_of_HJ`).
`exists_const_hP_of_estimates` chains Parts A and B.
-/

@[expose] public section

open MeasureTheory PrimeBHT.Kernel PrimeBHT.Decomposition
open scoped ENNReal

namespace PrimeBHT.FinalSum

/-! ### Part A: the `s`-triangle assembly -/

section Core

variable {r : ℝ}

/-- Raising a bound `x ≤ c N` to the power `s > 0`. -/
theorem rpow_bound_of_le {x N : ℝ≥0∞} {c s : ℝ} (hc : 0 ≤ c) (hs : 0 < s)
    (h : x ≤ ENNReal.ofReal c * N) : x ^ s ≤ ENNReal.ofReal (c ^ s) * N ^ s := by
  calc x ^ s ≤ (ENNReal.ofReal c * N) ^ s := ENNReal.rpow_le_rpow h hs.le
    _ = ENNReal.ofReal (c ^ s) * N ^ s := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hs.le, ENNReal.ofReal_rpow_of_nonneg hc hs.le]

/-- The `s`-triangle inequality for a finite sum of functions, each bounded by `a i · N`:
`‖∑ F i‖_r^s ≤ (∑ a_i^s) N^s`, `s = min r 1`. -/
theorem eLpNorm_finsetSum_rpow_le {ι : Type*} (t : Finset ι) (F : ι → ℤ → ℂ) (a : ι → ℝ)
    (ha : ∀ i ∈ t, 0 ≤ a i) (N : ℝ≥0∞) (hr : 0 < r)
    (h : ∀ i ∈ t, eLpNorm (F i) (ENNReal.ofReal r) Measure.count ≤ ENNReal.ofReal (a i) * N) :
    eLpNorm (∑ i ∈ t, F i) (ENNReal.ofReal r) Measure.count ^ min r 1 ≤
      ENNReal.ofReal (∑ i ∈ t, a i ^ min r 1) * N ^ min r 1 := by
  have hs : 0 < min r 1 := lt_min hr one_pos
  refine (PrimeBHT.Progression.eLpNorm_sum_rpow_le t F hr).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => Real.rpow_nonneg (ha i hi) _), Finset.sum_mul]
  exact Finset.sum_le_sum fun i hi => rpow_bound_of_le (ha i hi) hs (h i hi)

/-- The `s`-triangle inequality for three summands. -/
theorem eLpNorm_add_add_rpow_le (X Y Z : ℤ → ℂ) (hr : 0 < r) :
    eLpNorm (X + Y + Z) (ENNReal.ofReal r) Measure.count ^ min r 1 ≤
      eLpNorm X (ENNReal.ofReal r) Measure.count ^ min r 1 +
        eLpNorm Y (ENNReal.ofReal r) Measure.count ^ min r 1 +
          eLpNorm Z (ENNReal.ofReal r) Measure.count ^ min r 1 := by
  have h := PrimeBHT.Progression.eLpNorm_sum_rpow_le (Finset.univ : Finset (Fin 3)) ![X, Y, Z] hr
  simpa only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] using h

/-- Taking the `1/s`-th power of `x^s ≤ A N^s`. -/
theorem le_of_rpow_le {x N : ℝ≥0∞} {A s : ℝ} (hA : 0 ≤ A) (hs : 0 < s)
    (h : x ^ s ≤ ENNReal.ofReal A * N ^ s) : x ≤ ENNReal.ofReal (A ^ s⁻¹) * N := by
  have h2 := ENNReal.rpow_le_rpow h (inv_nonneg.2 hs.le)
  rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hs.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hs.le), ← ENNReal.rpow_mul,
    mul_inv_cancel₀ hs.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hA (inv_nonneg.2 hs.le)] at h2
  exact h2

/-- Three groups of terms, each with `‖·‖^s ≤ A_i N^s`, give `‖X+Y+Z‖ ≤ (A₁+A₂+A₃)^{1/s} N`. -/
theorem eLpNorm_add_add_le {X Y Z : ℤ → ℂ} (hr : 0 < r) {N : ℝ≥0∞} {A₁ A₂ A₃ : ℝ}
    (h₁ : 0 ≤ A₁) (h₂ : 0 ≤ A₂) (h₃ : 0 ≤ A₃)
    (hX : eLpNorm X (ENNReal.ofReal r) Measure.count ^ min r 1 ≤ ENNReal.ofReal A₁ * N ^ min r 1)
    (hY : eLpNorm Y (ENNReal.ofReal r) Measure.count ^ min r 1 ≤ ENNReal.ofReal A₂ * N ^ min r 1)
    (hZ : eLpNorm Z (ENNReal.ofReal r) Measure.count ^ min r 1 ≤ ENNReal.ofReal A₃ * N ^ min r 1) :
    eLpNorm (X + Y + Z) (ENNReal.ofReal r) Measure.count ≤
      ENNReal.ofReal ((A₁ + A₂ + A₃) ^ (min r 1)⁻¹) * N := by
  have hs : 0 < min r 1 := lt_min hr one_pos
  refine le_of_rpow_le (by linarith) hs ?_
  refine (eLpNorm_add_add_rpow_le X Y Z hr).trans ?_
  rw [ENNReal.ofReal_add (add_nonneg h₁ h₂) h₃, ENNReal.ofReal_add h₁ h₂, add_mul, add_mul]
  gcongr

end Core

/-! #### The three real series -/

section Series

/-- `∑_{k ≤ J} (C k^{-100})^s ≤ C^s ∑_k k^{-100 s}` (finite since `100 s > 1`). -/
theorem sum_error_le {s C : ℝ} (hs : 1 < 100 * s) (hC : 0 ≤ C) (J : ℕ) :
    ∑ k ∈ Finset.Icc 1 J, (C * (k : ℝ) ^ (-(100 : ℝ))) ^ s ≤
      C ^ s * ∑' k : ℕ, (k : ℝ) ^ (-(100 * s)) := by
  have hsum : Summable fun k : ℕ => (k : ℝ) ^ (-(100 * s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hterm : ∀ k ∈ Finset.Icc 1 J, (C * (k : ℝ) ^ (-(100 : ℝ))) ^ s =
      C ^ s * (k : ℝ) ^ (-(100 * s)) := by
    intro k _
    rw [Real.mul_rpow hC (Real.rpow_nonneg (Nat.cast_nonneg k) _),
      ← Real.rpow_mul (Nat.cast_nonneg k)]
    congr 2
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hC _)
  exact hsum.sum_le_tsum _ (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg k) _)

/-- `(C (2^j)^{-σ})^s = C^s (2^{-σ s})^j`. -/
theorem decay_term {C σ s : ℝ} (hC : 0 ≤ C) (j : ℕ) :
    (C * ((2 : ℝ) ^ j) ^ (-σ)) ^ s = C ^ s * ((2 : ℝ) ^ (-(σ * s))) ^ j := by
  rw [Real.mul_rpow hC (Real.rpow_nonneg (by positivity) _), ← Real.rpow_natCast (2 : ℝ) j,
    ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
    ← Real.rpow_natCast ((2 : ℝ) ^ (-(σ * s))) j, ← Real.rpow_mul (by norm_num)]
  congr 2
  ring

/-- `∑_{j} (C (2^j)^{-σ})^s ≤ C^s ∑_j (2^{-σ s})^j` (a geometric series, `σ s > 0`). -/
theorem sum_decay_le {s σ C : ℝ} (hs : 0 < s) (hσ : 0 < σ) (hC : 0 ≤ C) (t : Finset ℕ) :
    ∑ j ∈ t, (C * ((2 : ℝ) ^ j) ^ (-σ)) ^ s ≤ C ^ s * ∑' j : ℕ, ((2 : ℝ) ^ (-(σ * s))) ^ j := by
  have hρ0 : 0 ≤ (2 : ℝ) ^ (-(σ * s)) := Real.rpow_nonneg (by norm_num) _
  have hρ1 : (2 : ℝ) ^ (-(σ * s)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos (mul_pos hσ hs))
  have hsum := summable_geometric_of_lt_one hρ0 hρ1
  rw [Finset.sum_congr rfl (fun j _ => decay_term hC j), ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hC _)
  exact hsum.sum_le_tsum _ (fun j _ => pow_nonneg hρ0 j)

end Series

/-! #### The exact identity with an arbitrary threshold -/

/-- `Decomposition.exactred` for any threshold `j₂` with `b_Q ≤ Q^τ` for dyadic `Q = 2^j`, `j > j₂`
(the dyadic `Q ≤ C` of `exactred` are `j ≤ j₂`). -/
theorem exactred_of_threshold (χ : ℝ → ℝ) {τ : ℝ} {j₂ : ℕ}
    (hj₂ : ∀ j : ℕ, j₂ < j → (bQ ((2 : ℝ) ^ j) : ℝ) ≤ ((2 : ℝ) ^ j) ^ τ) (J : ℕ)
    {f g : ℤ → ℂ} (hf : f.support.Finite) (x : ℤ) :
    HJ χ J f g x =
      ∑ k ∈ Finset.Icc 1 J, Serr χ k f g x
        + ∑ j ∈ (jset J).filter (fun j => j ≤ j₂),
            ∑ k ∈ Finset.Icc (bQ ((2 : ℝ) ^ j)) J, Tk χ j k f g x
        + ∑ j ∈ (jset J).filter (fun j => j₂ < j),
            (Hmod χ τ J j f g x + Utail χ τ J j f g x) := by
  have hC : ∀ j : ℕ, (2 : ℝ) ^ j₂ < (2 : ℝ) ^ j → (bQ ((2 : ℝ) ^ j) : ℝ) ≤ ((2 : ℝ) ^ j) ^ τ :=
    fun j hj => hj₂ j ((pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hj)
  rw [exactred (χ := χ) J τ ((2 : ℝ) ^ j₂) hC hf x]
  have hle : ∀ j : ℕ, (2 : ℝ) ^ j ≤ (2 : ℝ) ^ j₂ ↔ j ≤ j₂ :=
    fun j => pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)
  simp only [hle, not_le]

/-- The identity of `exactred_of_threshold` as an identity of functions `ℤ → ℂ`. -/
theorem HJ_eq_sum_groups (χ : ℝ → ℝ) {τ : ℝ} {j₂ : ℕ}
    (hj₂ : ∀ j : ℕ, j₂ < j → (bQ ((2 : ℝ) ^ j) : ℝ) ≤ ((2 : ℝ) ^ j) ^ τ) (J : ℕ)
    {f g : ℤ → ℂ} (hf : f.support.Finite) :
    HJ χ J f g =
      (∑ k ∈ Finset.Icc 1 J, Serr χ k f g)
        + (∑ j ∈ (jset J).filter (fun j => j ≤ j₂),
            ∑ k ∈ Finset.Icc (bQ ((2 : ℝ) ^ j)) J, Tk χ j k f g)
        + ∑ j ∈ (jset J).filter (fun j => j₂ < j),
            (Hmod χ τ J j f g + Utail χ τ J j f g) := by
  funext x
  rw [exactred_of_threshold χ hj₂ J hf x]
  simp only [Pi.add_apply, Finset.sum_apply]

/-! #### The constant and the assembly theorem -/

/-- The constant of the final assembly, `s = min r 1`:
`(C_E^s ∑_k k^{-100 s} + ∑_{j ≤ j₂} Cp(j)^s + C_H^s ∑_j 2^{-j σ s})^{1/s}`.
It depends only on `r, σ, C_E, C_H, Cp|_{[0,j₂]}, j₂` (not on `J, f, g, p, q`). -/
noncomputable def assemblyConst (r σ C_E C_H : ℝ) (Cp : ℕ → ℝ) (j₂ : ℕ) : ℝ :=
  (C_E ^ min r 1 * ∑' k : ℕ, (k : ℝ) ^ (-(100 * min r 1)) +
      ∑ j ∈ Finset.range (j₂ + 1), Cp j ^ min r 1 +
      C_H ^ min r 1 * ∑' j : ℕ, ((2 : ℝ) ^ (-(σ * min r 1))) ^ j) ^ (min r 1)⁻¹

theorem assemblyConst_nonneg {r σ C_E C_H : ℝ} {Cp : ℕ → ℝ} (j₂ : ℕ) (hCE : 0 ≤ C_E)
    (hCH : 0 ≤ C_H) (hCp : ∀ j, 0 ≤ Cp j) :
    0 ≤ assemblyConst r σ C_E C_H Cp j₂ := by
  unfold assemblyConst
  refine Real.rpow_nonneg ?_ _
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · exact mul_nonneg (Real.rpow_nonneg hCE _) (tsum_nonneg fun k => Real.rpow_nonneg (Nat.cast_nonneg k) _)
  · exact Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hCp j) _
  · exact mul_nonneg (Real.rpow_nonneg hCH _)
      (tsum_nonneg fun j => pow_nonneg (Real.rpow_nonneg (by norm_num) _) j)

/-- **The assembly (N53 steps 2-6) for fixed `f, g` and fixed `J`, with the explicit constant.**
`N` stands for `‖f‖_p ‖g‖_q`.  The threshold `j₂` serves both as the threshold of `e:exactred`
(`hj₂`) and as the range beyond which the decay estimate `hH` holds. -/
theorem eLpNorm_HJ_le_of_estimates (χ : ℝ → ℝ) {τ : ℝ} {j₂ : ℕ}
    (hj₂ : ∀ j : ℕ, j₂ < j → (bQ ((2 : ℝ) ^ j) : ℝ) ≤ ((2 : ℝ) ^ j) ^ τ)
    {r σ C_E C_H : ℝ} {Cp : ℕ → ℝ} (hr : 0 < r) (hs : 1 < 100 * min r 1) (hσ : 0 < σ)
    (hCE : 0 ≤ C_E) (hCH : 0 ≤ C_H) (hCp : ∀ j, 0 ≤ Cp j)
    {f g : ℤ → ℂ} (hf : f.support.Finite) {N : ℝ≥0∞}
    (hE : ∀ k : ℕ, 1 ≤ k →
      eLpNorm (Serr χ k f g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C_E * (k : ℝ) ^ (-(100 : ℝ))) * N)
    (hProg : ∀ j J : ℕ,
      eLpNorm (∑ k ∈ Finset.Icc (bQ ((2 : ℝ) ^ j)) J, Tk χ j k f g)
        (ENNReal.ofReal r) Measure.count ≤ ENNReal.ofReal (Cp j) * N)
    (hH : ∀ j J : ℕ, j₂ < j →
      eLpNorm (Hmod χ τ J j f g + Utail χ τ J j f g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C_H * ((2 : ℝ) ^ j) ^ (-σ)) * N)
    (J : ℕ) :
    eLpNorm (HJ χ J f g) (ENNReal.ofReal r) Measure.count ≤
      ENNReal.ofReal (assemblyConst r σ C_E C_H Cp j₂) * N := by
  classical
  have hs0 : 0 < min r 1 := lt_min hr one_pos
  rw [HJ_eq_sum_groups χ hj₂ J hf]
  -- the three groups
  have hXr := eLpNorm_finsetSum_rpow_le (r := r) (Finset.Icc 1 J) (fun k => Serr χ k f g)
    (fun k => C_E * (k : ℝ) ^ (-(100 : ℝ)))
    (fun k _ => mul_nonneg hCE (Real.rpow_nonneg (Nat.cast_nonneg k) _)) N hr
    (fun k hk => hE k (Finset.mem_Icc.1 hk).1)
  have hYr := eLpNorm_finsetSum_rpow_le (r := r) ((jset J).filter (fun j => j ≤ j₂))
    (fun j => ∑ k ∈ Finset.Icc (bQ ((2 : ℝ) ^ j)) J, Tk χ j k f g) Cp (fun j _ => hCp j) N hr
    (fun j _ => hProg j J)
  have hZr := eLpNorm_finsetSum_rpow_le (r := r) ((jset J).filter (fun j => j₂ < j))
    (fun j => Hmod χ τ J j f g + Utail χ τ J j f g) (fun j => C_H * ((2 : ℝ) ^ j) ^ (-σ))
    (fun j _ => mul_nonneg hCH (Real.rpow_nonneg (by positivity) _)) N hr
    (fun j hj => hH j J (Finset.mem_filter.1 hj).2)
  have hEsum := sum_error_le (s := min r 1) hs hCE J
  have hPsum : ∑ j ∈ (jset J).filter (fun j => j ≤ j₂), Cp j ^ min r 1 ≤
      ∑ j ∈ Finset.range (j₂ + 1), Cp j ^ min r 1 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => Real.rpow_nonneg (hCp j) _)
    intro j hj
    rw [Finset.mem_range]
    have := (Finset.mem_filter.1 hj).2
    omega
  have hHsum := sum_decay_le (s := min r 1) hs0 hσ hCH ((jset J).filter (fun j => j₂ < j))
  have hA₁ : 0 ≤ C_E ^ min r 1 * ∑' k : ℕ, (k : ℝ) ^ (-(100 * min r 1)) :=
    mul_nonneg (Real.rpow_nonneg hCE _)
      (tsum_nonneg fun k => Real.rpow_nonneg (Nat.cast_nonneg k) _)
  have hA₂ : 0 ≤ ∑ j ∈ Finset.range (j₂ + 1), Cp j ^ min r 1 :=
    Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hCp j) _
  have hA₃ : 0 ≤ C_H ^ min r 1 * ∑' j : ℕ, ((2 : ℝ) ^ (-(σ * min r 1))) ^ j :=
    mul_nonneg (Real.rpow_nonneg hCH _)
      (tsum_nonneg fun j => pow_nonneg (Real.rpow_nonneg (by norm_num) _) j)
  have hmain := eLpNorm_add_add_le (N := N) hr hA₁ hA₂ hA₃
    (hXr.trans (by gcongr))
    (hYr.trans (by gcongr))
    (hZr.trans (by gcongr))
  exact hmain

/-- The coercion of a finitely supported function `ℤ →₀ ℂ` has finite support (as a `Set`). -/
theorem finite_support_coe (f : ℤ →₀ ℂ) : (Function.support ⇑f).Finite := by
  rw [Finsupp.fun_support_eq]
  exact f.support.finite_toSet

/-- **N53 steps 2-6 for finitely supported `f, g : ℤ →₀ ℂ`, uniform in `J`.**
There is a threshold `j₂ ≥ j₁` (depending only on `τ` and `j₁`) such that for all `J` and all
finitely supported `f, g`, `‖H^J(f,g)‖_{ℓ^r} ≤ C ‖f‖_p ‖g‖_q` with the explicit constant
`C = assemblyConst r σ C_E C_H Cp j₂`, which depends only on `(C_E, Cp, C_H, σ, j₂, r)`.

Hypotheses (supplied by the consumer, with constants independent of `f, g, J`):
`hE` is `e:error-summable` (`k ≥ 1`), `hProg` is `e:progression` for the interval `[b_Q, J]`
(constant `Cp j` for `Q = 2^j`), `hH` is the decay estimate `e:complexity-decay` for `Q = 2^j`,
`j > j₁`. -/
theorem eLpNorm_HJ_le_assemblyConst_of_estimates (χ : ℝ → ℝ) {p q r τ σ : ℝ} (hτ : 0 < τ)
    (hr : 0 < r) (hs : 1 < 100 * min r 1) (hσ : 0 < σ) {C_E C_H : ℝ} (hCE : 0 ≤ C_E)
    (hCH : 0 ≤ C_H) {Cp : ℕ → ℝ} (hCp : ∀ j, 0 ≤ Cp j) (j₁ : ℕ)
    (hE : ∀ f g : ℤ →₀ ℂ, ∀ k : ℕ, 1 ≤ k →
      eLpNorm (Serr χ k ⇑f ⇑g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C_E * (k : ℝ) ^ (-(100 : ℝ))) *
          eLpNorm ⇑f (ENNReal.ofReal p) Measure.count *
            eLpNorm ⇑g (ENNReal.ofReal q) Measure.count)
    (hProg : ∀ f g : ℤ →₀ ℂ, ∀ j J : ℕ,
      eLpNorm (∑ k ∈ Finset.Icc (bQ ((2 : ℝ) ^ j)) J, Tk χ j k ⇑f ⇑g)
          (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (Cp j) * eLpNorm ⇑f (ENNReal.ofReal p) Measure.count *
          eLpNorm ⇑g (ENNReal.ofReal q) Measure.count)
    (hH : ∀ f g : ℤ →₀ ℂ, ∀ j J : ℕ, j₁ < j →
      eLpNorm (Hmod χ τ J j ⇑f ⇑g + Utail χ τ J j ⇑f ⇑g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C_H * ((2 : ℝ) ^ j) ^ (-σ)) *
          eLpNorm ⇑f (ENNReal.ofReal p) Measure.count *
            eLpNorm ⇑g (ENNReal.ofReal q) Measure.count) :
    ∃ j₂ : ℕ, j₁ ≤ j₂ ∧ ∀ (f g : ℤ →₀ ℂ) (J : ℕ),
      eLpNorm (HJ χ J ⇑f ⇑g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (assemblyConst r σ C_E C_H Cp j₂) *
          eLpNorm ⇑f (ENNReal.ofReal p) Measure.count *
            eLpNorm ⇑g (ENNReal.ofReal q) Measure.count := by
  obtain ⟨j₀, hj₀⟩ := exists_bQ_le_rpow hτ
  refine ⟨max j₀ j₁, le_max_right _ _, fun f g J => ?_⟩
  have hj₂ : ∀ j : ℕ, max j₀ j₁ < j → (bQ ((2 : ℝ) ^ j) : ℝ) ≤ ((2 : ℝ) ^ j) ^ τ :=
    fun j hj => hj₀ j (lt_of_le_of_lt (le_max_left _ _) hj)
  rw [mul_assoc]
  refine eLpNorm_HJ_le_of_estimates χ hj₂ hr hs hσ hCE hCH hCp (finite_support_coe f)
    (N := eLpNorm ⇑f (ENNReal.ofReal p) Measure.count * eLpNorm ⇑g (ENNReal.ofReal q) Measure.count)
    (fun k hk => ?_) (fun j J => ?_) (fun j J hj => ?_) J
  · simpa only [mul_assoc] using hE f g k hk
  · simpa only [mul_assoc] using hProg f g j J
  · simpa only [mul_assoc] using hH f g j J (lt_of_le_of_lt (le_max_right _ _) hj)

/-- The same, with an existentially quantified constant: for finitely supported `f, g : ℤ →₀ ℂ`
and all `J`, `‖H^J(f,g)‖_{ℓ^r} ≤ C ‖f‖_p ‖g‖_q`. -/
theorem exists_const_HJ_of_estimates (χ : ℝ → ℝ) {p q r τ σ : ℝ} (hτ : 0 < τ)
    (hr : 0 < r) (hs : 1 < 100 * min r 1) (hσ : 0 < σ) {C_E C_H : ℝ} (hCE : 0 ≤ C_E)
    (hCH : 0 ≤ C_H) {Cp : ℕ → ℝ} (hCp : ∀ j, 0 ≤ Cp j) (j₁ : ℕ)
    (hE : ∀ f g : ℤ →₀ ℂ, ∀ k : ℕ, 1 ≤ k →
      eLpNorm (Serr χ k ⇑f ⇑g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C_E * (k : ℝ) ^ (-(100 : ℝ))) *
          eLpNorm ⇑f (ENNReal.ofReal p) Measure.count *
            eLpNorm ⇑g (ENNReal.ofReal q) Measure.count)
    (hProg : ∀ f g : ℤ →₀ ℂ, ∀ j J : ℕ,
      eLpNorm (∑ k ∈ Finset.Icc (bQ ((2 : ℝ) ^ j)) J, Tk χ j k ⇑f ⇑g)
          (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (Cp j) * eLpNorm ⇑f (ENNReal.ofReal p) Measure.count *
          eLpNorm ⇑g (ENNReal.ofReal q) Measure.count)
    (hH : ∀ f g : ℤ →₀ ℂ, ∀ j J : ℕ, j₁ < j →
      eLpNorm (Hmod χ τ J j ⇑f ⇑g + Utail χ τ J j ⇑f ⇑g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C_H * ((2 : ℝ) ^ j) ^ (-σ)) *
          eLpNorm ⇑f (ENNReal.ofReal p) Measure.count *
            eLpNorm ⇑g (ENNReal.ofReal q) Measure.count) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : ℤ →₀ ℂ) (J : ℕ),
      eLpNorm (HJ χ J ⇑f ⇑g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal C * eLpNorm ⇑f (ENNReal.ofReal p) Measure.count *
          eLpNorm ⇑g (ENNReal.ofReal q) Measure.count := by
  obtain ⟨j₂, -, h⟩ := eLpNorm_HJ_le_assemblyConst_of_estimates χ hτ hr hs hσ hCE hCH hCp j₁
    hE hProg hH
  exact ⟨_, assemblyConst_nonneg j₂ hCE hCH hCp, h⟩

/-! ### Part B: Lemma 1.4 and the passage to `H_P` -/

/-- The prime bilinear Hilbert transform `H_P(f,g)(x) = ∑_{n ≠ 0} Λ(|n|)/n · f(x-n) g(x+n)`,
literally the formula of `primeBHT` in `drafts/T0Statement.lean` (for `f g : ℤ →₀ ℂ`, see
`hP_coe_eq`), written for arbitrary functions `ℤ → ℂ`. -/
noncomputable def hP (f g : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑' n : ℤ, if n = 0 then 0 else
    ((ArithmeticFunction.vonMangoldt n.natAbs : ℝ) : ℂ) / (n : ℂ) * f (x - n) * g (x + n)

/-- The `n`-th term of `H^J`: once `2|n| ≤ 2^J` on the support of the summand, the telescoping
identity `∑_{k=1}^J ψ_k(n) = 1/n` turns it into the term of `H_P`. -/
theorem sum_term_eq {χ : ℝ → ℝ} (hχ : IsCutoff χ) (J : ℕ) (f g : ℤ → ℂ) (x n : ℤ)
    (h : n ≠ 0 → f (x - n) ≠ 0 → g (x + n) ≠ 0 → 2 * |(n : ℝ)| ≤ 2 ^ J) :
    ∑ k ∈ Finset.Icc 1 J, (psiK χ k n : ℂ) * w n * f (x - n) * g (x + n) =
      if n = 0 then 0 else
        ((ArithmeticFunction.vonMangoldt n.natAbs : ℝ) : ℂ) / (n : ℂ) * f (x - n) * g (x + n) := by
  by_cases hn : n = 0
  · subst hn
    simp [psiK_zero]
  simp only [hn, ↓reduceIte]
  by_cases hf0 : f (x - n) = 0
  · simp [hf0]
  by_cases hg0 : g (x + n) = 0
  · simp [hg0]
  have hsum := hχ.sum_psiK_int hn (h hn hf0 hg0)
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← Complex.ofReal_sum, hsum]
  simp only [w]
  push_cast
  ring

/-- **Lemma 1.4.** For finitely supported `f, g` there is `J₀` with `H^J(f,g)(x) = H_P(f,g)(x)` for
all `J ≥ J₀` and all `x`. -/
theorem exists_HJ_eq_hP {χ : ℝ → ℝ} (hχ : IsCutoff χ) {f g : ℤ → ℂ} (hf : f.support.Finite)
    (hg : g.support.Finite) :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∀ x : ℤ, HJ χ J f g x = hP f g x := by
  obtain ⟨Rf, hRf⟩ : ∃ R : ℕ, ∀ s : ℤ, f s ≠ 0 → s.natAbs ≤ R := by
    obtain ⟨R, hR⟩ := (hf.image Int.natAbs).bddAbove
    exact ⟨R, fun s hs => hR ⟨s, hs, rfl⟩⟩
  obtain ⟨Rg, hRg⟩ : ∃ R : ℕ, ∀ s : ℤ, g s ≠ 0 → s.natAbs ≤ R := by
    obtain ⟨R, hR⟩ := (hg.image Int.natAbs).bddAbove
    exact ⟨R, fun s hs => hR ⟨s, hs, rfl⟩⟩
  refine ⟨2 * (Rf + Rg), fun J hJ x => ?_⟩
  have hterm : ∀ n : ℤ, ∑ k ∈ Finset.Icc 1 J, (psiK χ k n : ℂ) * w n * f (x - n) * g (x + n) =
      if n = 0 then 0 else
        ((ArithmeticFunction.vonMangoldt n.natAbs : ℝ) : ℂ) / (n : ℂ) * f (x - n) * g (x + n) := by
    intro n
    refine sum_term_eq hχ J f g x n ?_
    intro _ hf0 hg0
    have h1 := hRf _ hf0
    have h2 := hRg _ hg0
    have h4 : 2 * n.natAbs ≤ 2 ^ J := by
      calc 2 * n.natAbs ≤ 2 * (Rf + Rg) := by omega
        _ ≤ 2 ^ (2 * (Rf + Rg)) := (Nat.lt_two_pow_self).le
        _ ≤ 2 ^ J := Nat.pow_le_pow_right two_pos hJ
    have h5 : |(n : ℝ)| = (n.natAbs : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      simp
    rw [h5]
    exact_mod_cast h4
  have hswap := Summable.tsum_finsetSum (s := Finset.Icc 1 J)
    (f := fun (k : ℕ) (n : ℤ) => (psiK χ k n : ℂ) * w n * f (x - n) * g (x + n))
    (fun k _ => summable_summand hf (fun n => (psiK χ k n : ℂ) * w n) g x)
  unfold HJ hP
  rw [← hswap]
  exact tsum_congr hterm

/-- **The passage from `H^J` to `H_P`.** If `‖H^J(f,g)‖_{ℓ^r} ≤ B` for all `J` (finitely supported
`f, g`), then `‖H_P(f,g)‖_{ℓ^r} ≤ B`. -/
theorem eLpNorm_hP_le_of_HJ {χ : ℝ → ℝ} (hχ : IsCutoff χ) {r : ℝ} {B : ℝ≥0∞} {f g : ℤ → ℂ}
    (hf : f.support.Finite) (hg : g.support.Finite)
    (h : ∀ J : ℕ, eLpNorm (HJ χ J f g) (ENNReal.ofReal r) Measure.count ≤ B) :
    eLpNorm (hP f g) (ENNReal.ofReal r) Measure.count ≤ B := by
  obtain ⟨J₀, hJ₀⟩ := exists_HJ_eq_hP hχ hf hg
  have hfun : HJ χ J₀ f g = hP f g := funext (hJ₀ J₀ le_rfl)
  rw [← hfun]
  exact h J₀

/-- If `‖H^J(f,g)‖_{ℓ^r} ≤ C ‖f‖_p ‖g‖_q` for all `J` and all finitely supported `f, g`, then
`‖H_P(f,g)‖_{ℓ^r} ≤ C ‖f‖_p ‖g‖_q` for all `f, g : ℤ →₀ ℂ` (the shape of `t_maintheorem`). -/
theorem eLpNorm_hP_le_of_uniform {χ : ℝ → ℝ} (hχ : IsCutoff χ) {p q r C : ℝ}
    (h : ∀ (f g : ℤ →₀ ℂ) (J : ℕ),
      eLpNorm (HJ χ J ⇑f ⇑g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal C * eLpNorm ⇑f (ENNReal.ofReal p) Measure.count *
          eLpNorm ⇑g (ENNReal.ofReal q) Measure.count)
    (f g : ℤ →₀ ℂ) :
    eLpNorm (hP ⇑f ⇑g) (ENNReal.ofReal r) Measure.count ≤
      ENNReal.ofReal C * eLpNorm ⇑f (ENNReal.ofReal p) Measure.count *
        eLpNorm ⇑g (ENNReal.ofReal q) Measure.count :=
  eLpNorm_hP_le_of_HJ hχ (finite_support_coe f) (finite_support_coe g) (h f g)

/-- **N53, the whole assembly, conditional on the component estimates.**  Under `hE`, `hProg`, `hH`
(see `eLpNorm_HJ_le_assemblyConst_of_estimates`) there is `C ≥ 0` with
`‖H_P(f,g)‖_{ℓ^r} ≤ C ‖f‖_p ‖g‖_q` for all `f, g : ℤ →₀ ℂ`, where `H_P` is `hP`
(the formula of `primeBHT`).  Here `hs : 1 < 100 * min r 1` holds for `r > 1/2`
(`one_lt_hundred_mul_min_of_half_lt`; `Exponents.one_lt_hundred_mul_min` gives it for `r > 2/3`). -/
theorem exists_const_hP_of_estimates {χ : ℝ → ℝ} (hχ : IsCutoff χ) {p q r τ σ : ℝ} (hτ : 0 < τ)
    (hr : 0 < r) (hs : 1 < 100 * min r 1) (hσ : 0 < σ) {C_E C_H : ℝ} (hCE : 0 ≤ C_E)
    (hCH : 0 ≤ C_H) {Cp : ℕ → ℝ} (hCp : ∀ j, 0 ≤ Cp j) (j₁ : ℕ)
    (hE : ∀ f g : ℤ →₀ ℂ, ∀ k : ℕ, 1 ≤ k →
      eLpNorm (Serr χ k ⇑f ⇑g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C_E * (k : ℝ) ^ (-(100 : ℝ))) *
          eLpNorm ⇑f (ENNReal.ofReal p) Measure.count *
            eLpNorm ⇑g (ENNReal.ofReal q) Measure.count)
    (hProg : ∀ f g : ℤ →₀ ℂ, ∀ j J : ℕ,
      eLpNorm (∑ k ∈ Finset.Icc (bQ ((2 : ℝ) ^ j)) J, Tk χ j k ⇑f ⇑g)
          (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (Cp j) * eLpNorm ⇑f (ENNReal.ofReal p) Measure.count *
          eLpNorm ⇑g (ENNReal.ofReal q) Measure.count)
    (hH : ∀ f g : ℤ →₀ ℂ, ∀ j J : ℕ, j₁ < j →
      eLpNorm (Hmod χ τ J j ⇑f ⇑g + Utail χ τ J j ⇑f ⇑g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C_H * ((2 : ℝ) ^ j) ^ (-σ)) *
          eLpNorm ⇑f (ENNReal.ofReal p) Measure.count *
            eLpNorm ⇑g (ENNReal.ofReal q) Measure.count) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : ℤ →₀ ℂ,
      eLpNorm (hP ⇑f ⇑g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal C * eLpNorm ⇑f (ENNReal.ofReal p) Measure.count *
          eLpNorm ⇑g (ENNReal.ofReal q) Measure.count := by
  obtain ⟨C, hC, h⟩ := exists_const_HJ_of_estimates χ hτ hr hs hσ hCE hCH hCp j₁ hE hProg hH
  exact ⟨C, hC, eLpNorm_hP_le_of_uniform hχ h⟩

/-- `1 < 100 min(r,1)` for `r > 1/2` (in particular for `r > 2/3`, the range of the theorem). -/
theorem one_lt_hundred_mul_min_of_half_lt {r : ℝ} (hr : 1 / 2 < r) : 1 < 100 * min r 1 := by
  have : 1 / 2 < min r 1 := lt_min hr (by norm_num)
  linarith

end PrimeBHT.FinalSum
