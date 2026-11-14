module

public import PrimeBHT.U3MaxMod.Gowers

/-!
# `l:U3maxmod`, part 4: the plain-average bound (real-sum form)

`‖x ↦ N⁻¹ ∑_{n ∈ [N]} W(n) f(x-n) g(x+n)‖_{ℓ²} ≤ 2 ‖W‖_{U³([N])} ‖f‖_{ℓ⁴} ‖g‖_{ℓ⁴}`
with `‖·‖_{ℓ^p}` written as `(∑' x, ‖·‖^p)^{1/p}`.
-/

@[expose] public noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace PrimeBHT.U3MaxMod

open PrimeCarleson PrimeCarleson.Proof.Common PrimeCarleson.Proof.Paper

/-- The final real arithmetic (powers of `N` and the constant `2`). -/
lemma final_alg {N d L0 u v Ff Fg A n Wn c : ℝ} (hN : 0 < N) (hd0 : 0 ≤ d) (hd : d ≤ 2 * N)
    (hc0 : 0 ≤ c) (hc : 128 ≤ c ^ 8)
    (hL0 : 0 ≤ L0) (hFf : 0 ≤ Ff) (hFg : 0 ≤ Fg) (hn8 : n ^ 8 ≤ 8 * N ^ 4)
    (hA : A = Wn * n) (hWn : 0 ≤ Wn) (hu : u = Ff ^ 4) (hv : v = Fg ^ 4)
    (h : L0 ^ 4 ≤ d ^ 4 * u ^ 2 * v ^ 2 * A ^ 8) :
    Real.sqrt (L0 / N ^ 2) ≤ c * Wn * Ff * Fg := by
  set X : ℝ := c * Wn * Ff * Fg with hX
  have hX0 : 0 ≤ X := by positivity
  have hP : 0 ≤ (Ff * Fg * Wn) ^ 8 := by positivity
  have h1 : L0 ^ 4 ≤ N ^ 8 * X ^ 8 := by
    calc L0 ^ 4 ≤ d ^ 4 * u ^ 2 * v ^ 2 * A ^ 8 := h
      _ ≤ (2 * N) ^ 4 * (Ff ^ 4) ^ 2 * (Fg ^ 4) ^ 2 * (Wn ^ 8 * (8 * N ^ 4)) := by
          rw [hu, hv, hA, mul_pow]
          gcongr
      _ = 128 * N ^ 8 * (Ff * Fg * Wn) ^ 8 := by ring
      _ ≤ N ^ 8 * X ^ 8 := by
          have : X ^ 8 = c ^ 8 * (Ff * Fg * Wn) ^ 8 := by rw [hX]; ring
          rw [this]
          calc 128 * N ^ 8 * (Ff * Fg * Wn) ^ 8 = N ^ 8 * (128 * (Ff * Fg * Wn) ^ 8) := by ring
            _ ≤ N ^ 8 * (c ^ 8 * (Ff * Fg * Wn) ^ 8) := by gcongr
  have h2 : (Real.sqrt (L0 / N ^ 2)) ^ 8 ≤ X ^ 8 := by
    have e : (Real.sqrt (L0 / N ^ 2)) ^ 8 = (L0 / N ^ 2) ^ 4 := by
      rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, Real.sq_sqrt (by positivity)]
    rw [e, div_pow, div_le_iff₀ (by positivity)]
    calc L0 ^ 4 ≤ N ^ 8 * X ^ 8 := h1
      _ = X ^ 8 * (N ^ 2) ^ 4 := by ring
  exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) hX0 (by norm_num)).1 h2

lemma rpow_quarter_pow {u : ℝ} (hu : 0 ≤ u) : (u ^ (1 / 4 : ℝ)) ^ 4 = u := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu]; norm_num

/-- **`l:U3maxmod` (a), real-sum form**: for `N ≥ 1`, any `W : ℤ → ℂ` (only its values on `[N]`
matter, exactly as for the norm `‖W‖_{U³([N])}`) and finitely supported `f, g`,
`‖N⁻¹ ∑_{n ∈ [N]} W(n) f(x-n) g(x+n)‖_{ℓ²_x} ≤ 2 ‖W‖_{U³([N])} ‖f‖_4 ‖g‖_4`. -/
theorem l2_bilinAvg_le_gen (N : ℕ+) (W f g : ℤ → ℂ) (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) {c : ℝ} (hc0 : 0 ≤ c) (hc8 : 128 ≤ c ^ 8) :
    Real.sqrt (∑' x, ‖((N : ℕ) : ℂ)⁻¹ * ∑ n ∈ Finset.Icc (1 : ℤ) N, W n * f (x - n) * g (x + n)‖ ^ 2)
      ≤ c * gowersNormInterval 3 N W * (∑' x, ‖f x‖ ^ 4) ^ (1 / 4 : ℝ) *
        (∑' x, ‖g x‖ ^ 4) ^ (1 / 4 : ℝ) := by
  set I : Finset ℤ := Finset.Icc (1 : ℤ) N with hI
  set D : Finset ℤ := Finset.Icc (1 - (N : ℤ)) (N - 1) with hD
  set F : ℤ →₀ ℂ := restrictInterval N W with hF
  have hFn : ∀ n, n ∈ I → F n = W n := fun n hn => by
    simp [hF, restrictInterval, Finsupp.indicator_apply, show n ∈ Finset.Icc (1 : ℤ) N from hn]
  have hc : ∀ n, n ∉ I → (⇑F) n = 0 := fun n hn => by
    simp [hF, restrictInterval, Finsupp.indicator_apply, show n ∉ Finset.Icc (1 : ℤ) N from hn]
  have hIs : ∀ x, F x ≠ 0 → x ∈ I := fun x hx => by
    by_contra hxI
    exact hx (hc x hxI)
  have hDs : ∀ n ∈ I, ∀ n' ∈ I, n' - n ∈ D := fun x hx y hy => by
    simp only [hI, hD, Finset.mem_Icc] at hx hy ⊢
    omega
  have hS : ∀ x, ∑ n ∈ I, W n * f (x - n) * g (x + n) = sF I (⇑F) f g x := by
    intro x
    unfold sF
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hFn n hn, mul_assoc]
  have h4 := fourth_power_le I D hDs (⇑F) hc f g hf hg
  rw [sum_sq_AF_eq F I D hIs hDs] at h4
  set L0 : ℝ := ∑' x, ‖sF I (⇑F) f g x‖ ^ 2 with hL0
  have hNpos : (0 : ℝ) < (N : ℕ) := by exact_mod_cast N.pos
  have hL : ∑' x, ‖((N : ℕ) : ℂ)⁻¹ * ∑ n ∈ I, W n * f (x - n) * g (x + n)‖ ^ 2 =
      L0 / ((N : ℕ) : ℝ) ^ 2 := by
    simp_rw [hS, norm_mul, mul_pow]
    rw [tsum_mul_left]
    simp [norm_inv, div_eq_inv_mul]
    rfl
  rw [hL]
  have hone : (1 : ℝ) ≤ gowersNorm 3 (restrictInterval N 1) :=
    one_le_gowersNorm_restrictFinset_one 3 ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by have := N.pos; omega⟩⟩
  have hn8 := gowersNorm_one_pow_eight_le N
  have hu0 : 0 ≤ ∑' x, ‖f x‖ ^ 4 := tsum_nonneg fun x => by positivity
  have hv0 : 0 ≤ ∑' x, ‖g x‖ ^ 4 := tsum_nonneg fun x => by positivity
  have hD2 : (D.card : ℝ) ≤ 2 * ((N : ℕ) : ℝ) := by
    have h2 : D.card ≤ 2 * (N : ℕ) := by
      simp only [hD, Int.card_Icc]
      omega
    exact_mod_cast h2
  have hWn : gowersNormInterval 3 N W = gowersNorm 3 F / gowersNorm 3 (restrictInterval N 1) := rfl
  rw [hWn]
  refine final_alg hNpos (Nat.cast_nonneg _) hD2 hc0 hc8 (tsum_nonneg fun x => by positivity)
    (Real.rpow_nonneg hu0 _) (Real.rpow_nonneg hv0 _) hn8 ?_
    (div_nonneg (gowersNorm_nonneg _ _) (by linarith)) (rpow_quarter_pow hu0).symm
    (rpow_quarter_pow hv0).symm h4
  field_simp


/-- **`l:U3maxmod` (a), real-sum form**, constant `2`. -/
theorem l2_bilinAvg_le (N : ℕ+) (W f g : ℤ → ℂ) (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) :
    Real.sqrt (∑' x, ‖((N : ℕ) : ℂ)⁻¹ * ∑ n ∈ Finset.Icc (1 : ℤ) N, W n * f (x - n) * g (x + n)‖ ^ 2)
      ≤ 2 * gowersNormInterval 3 N W * (∑' x, ‖f x‖ ^ 4) ^ (1 / 4 : ℝ) *
        (∑' x, ‖g x‖ ^ 4) ^ (1 / 4 : ℝ) :=
  l2_bilinAvg_le_gen N W f g hf hg (by norm_num) (by norm_num)

end PrimeBHT.U3MaxMod
