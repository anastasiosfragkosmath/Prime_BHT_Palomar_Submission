module

public import PrimeCarleson.Proof.Common.FourierR

/-!
# N42 (42c): the sampled multiplier

For an `N`-periodic weight `w : ℤ → ℂ` and a Schwartz kernel `K`,
`∑_n K(n) w(n) e(-nθ) = ∑_{ℓ ∈ ZMod N} (F_N w)(ℓ) ∑_{j ∈ ℤ} K̂(θ - ℓ/N - j)`,
where `F_N w (ℓ) = E_{r ∈ ZMod N} w(r) e(-ℓ r / N)` is the normalized Fourier transform on `ZMod N`
(blueprint N42 step 3, `e:sampled-multiplier`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform Real SchwartzMap

namespace PrimeBHT.Transference

open PrimeCarleson PrimeCarleson.Proof.Goal0 PrimeCarleson.Proof.Common

/-- The normalized Fourier transform on `ZMod N` of an `N`-periodic weight `w : ℤ → ℂ`:
`F_N w (ℓ) = N⁻¹ ∑_{r ∈ ZMod N} w(r) e(-ℓ r / N)` (representatives `0, …, N-1`). -/
def finFourier (N : ℕ) [NeZero N] (w : ℤ → ℂ) (ℓ : ZMod N) : ℂ :=
  (N : ℂ)⁻¹ * ∑ r : ZMod N, w (r.val : ℤ) * e (-((ℓ.val : ℝ) * r.val / N))

theorem e_natCast_mul (k : ℕ) (t : ℝ) : e (k * t) = e t ^ k := by
  unfold e
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem e_eq_one_iff (t : ℝ) : e t = 1 ↔ ∃ n : ℤ, t = n := by
  unfold e
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : (t : ℂ) = n := by
      apply mul_left_cancel₀ h2
      rw [hn]; ring
    exact_mod_cast this
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

/-- Sum over `ZMod N` of a function of the representative, as a sum over `range N`. -/
theorem sum_zmod_val_eq_sum_range (N : ℕ) [NeZero N] (f : ℕ → ℂ) :
    ∑ ℓ : ZMod N, f ℓ.val = ∑ k ∈ Finset.range N, f k := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  exact Fin.sum_univ_eq_sum_range f (k + 1)

/-- Orthogonality: `∑_{ℓ ∈ ZMod N} e(ℓ m / N) = N 1_{m ≡ 0 (N)}`. -/
theorem sum_e_mul_div (N : ℕ) [NeZero N] (m : ℤ) :
    ∑ ℓ : ZMod N, e ((ℓ.val : ℝ) * m / N) = if (m : ZMod N) = 0 then (N : ℂ) else 0 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  rw [sum_zmod_val_eq_sum_range N (fun k => e ((k : ℝ) * m / N))]
  have hpow : ∀ k : ℕ, e ((k : ℝ) * m / N) = e ((m : ℝ) / N) ^ k := fun k => by
    rw [← e_natCast_mul]; ring_nf
  simp_rw [hpow]
  split_ifs with hm
  · obtain ⟨q, hq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd m N).1 hm
    have : e ((m : ℝ) / N) = 1 := by
      rw [hq]; push_cast
      rw [mul_div_cancel_left₀ _ hN, e_intCast]
    simp [this]
  · have hz : e ((m : ℝ) / N) ≠ 1 := by
      intro h1
      obtain ⟨n, hn⟩ := (e_eq_one_iff _).1 h1
      apply hm
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      refine ⟨n, ?_⟩
      have : (m : ℝ) = N * n := by rw [← hn]; field_simp
      exact_mod_cast this
    rw [geom_sum_eq hz, ← e_natCast_mul, mul_div_cancel₀ _ hN, e_intCast, sub_self, zero_div]

/-- An `N`-periodic weight is determined by its residue class. -/
theorem periodic_apply_val {N : ℕ} [NeZero N] {w : ℤ → ℂ} (hw : Function.Periodic w (N : ℤ))
    (n : ℤ) : w ((n : ZMod N).val : ℤ) = w n := by
  rw [ZMod.val_intCast]
  rw [Int.emod_def, mul_comm]
  have h := hw.int_mul (n / N) (n - n / N * N)
  simp only [Int.cast_id, sub_add_cancel] at h
  exact h.symm

/-- **Finite Fourier inversion** on `ZMod N`: `w(n) = ∑_ℓ (F_N w)(ℓ) e(ℓ n / N)`. -/
theorem finFourier_inversion {N : ℕ} [NeZero N] {w : ℤ → ℂ} (hw : Function.Periodic w (N : ℤ))
    (n : ℤ) : w n = ∑ ℓ : ZMod N, finFourier N w ℓ * e ((ℓ.val : ℝ) * n / N) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  unfold finFourier
  simp_rw [mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have key : ∀ r : ZMod N, ∑ ℓ : ZMod N, w (r.val : ℤ) * e (-((ℓ.val : ℝ) * r.val / N)) *
      e ((ℓ.val : ℝ) * n / N) = w (r.val : ℤ) * if ((n - r.val : ℤ) : ZMod N) = 0 then (N : ℂ)
        else 0 := fun r => by
    rw [← sum_e_mul_div N (n - r.val), Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [mul_assoc, ← e_add]
    congr 2
    push_cast
    ring
  simp_rw [key, mul_ite, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hfilter : (Finset.univ.filter fun r : ZMod N => ((n - r.val : ℤ) : ZMod N) = 0) =
      {(n : ZMod N)} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    push_cast
    rw [ZMod.natCast_zmod_val, sub_eq_zero, eq_comm]
  rw [hfilter, Finset.sum_singleton, periodic_apply_val hw]
  field_simp

/-- **Sampled multiplier** (N42 (42c), `e:sampled-multiplier`): for an `N`-periodic weight `w`
and a Schwartz kernel `K`,
`∑_n K(n) w(n) e(-nθ) = ∑_{ℓ ∈ ZMod N} (F_N w)(ℓ) ∑_{j ∈ ℤ} K̂(θ - ℓ/N - j)`. -/
theorem tsum_kernel_mul_weight_mul_e_eq {N : ℕ} [NeZero N] {w : ℤ → ℂ}
    (hw : Function.Periodic w (N : ℤ)) (K : 𝓢(ℝ, ℂ)) (θ : ℝ) :
    ∑' n : ℤ, K n * w n * e (-((n : ℝ) * θ)) =
      ∑ ℓ : ZMod N, finFourier N w ℓ *
        ∑' j : ℤ, 𝓕 (K : ℝ → ℂ) (θ - (ℓ.val : ℝ) / N - j) := by
  have hterm : ∀ n : ℤ, K n * w n * e (-((n : ℝ) * θ)) = ∑ ℓ : ZMod N, finFourier N w ℓ *
      (K n * e (-((n : ℝ) * (θ - (ℓ.val : ℝ) / N)))) := fun n => by
    rw [finFourier_inversion hw n, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    have : -((n : ℝ) * (θ - (ℓ.val : ℝ) / N)) = (ℓ.val : ℝ) * n / N + -((n : ℝ) * θ) := by ring
    rw [this, e_add]
    ring
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum fun ℓ _ =>
    (summable_mul_e_int_schwartz K _).mul_left (finFourier N w ℓ)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [tsum_mul_left, tsum_mul_e_eq_tsum_fourier_add_schwartz, ← (Equiv.neg ℤ).tsum_eq]
  congr 2
  ext j
  simp only [Equiv.neg_apply, Int.cast_neg]
  ring_nf

end PrimeBHT.Transference
