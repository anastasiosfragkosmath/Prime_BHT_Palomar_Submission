module

public import PrimeBHT.SingleScale
public import PrimeBHT.ErrorTerms.Moment

/-!
# N20 (b), `e:errrough`: the rough bound `‖S_k^err(f,g)‖_{ℓ^r} ≤ C k^B ‖f‖_p ‖g‖_q` (unconditional)

The argument of `PrimeBHT.SingleScale.eLpNorm_bilin_psiK_blockWeight_le` (N12 (a), steps 1-5), run for
an arbitrary even weight `W` with a prescribed `m`-th moment `∑_{0<|n|≤2^k} |W(n)|^m ≤ 2 · 2^k · M`:

* `norm_bilin_psiK_le`: pointwise Hölder in `n` bound `|∑_n ψ_k(n) W(n) f(x-n) g(x+n)|
  ≤ c 3^{1/s} (2M)^{1/m} B_{2^k}(|f|^s,|g|^s)(x)^{1/s}`;
* `eLpNorm_bilin_psiK_le_of_moment`: the `ℓ^r` bound (N11 at `|f|^s, |g|^s`) with constant
  `c₀ M^{1/m}`;
* `eLpNorm_Serr_rough`: for `W = E_k` the moment bound `sum_E_pow_le` (polylogarithmic in `k`, the
  KMTT moment of the cumulative Heath-Brown model plus `Λ(n) ≤ k` on the support of `ψ_k`) gives
  `C k^B`.  No `X3` is needed.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace PrimeBHT.ErrorTerms

open PrimeBHT.Kernel PrimeBHT.FixedAverage PrimeBHT.SingleScale PrimeBHT.Decomposition PrimeCarleson

/-- `S_k^err(f,g) = bilin (ψ_k E_k) f g`. -/
theorem Serr_eq_bilin {χ : ℝ → ℝ} (k : ℕ) (f g : ℤ → ℂ) :
    Serr χ k f g = bilin (fun n => ((psiK χ k n : ℝ) : ℂ) * E k n) f g := rfl

/-- Pointwise Hölder bound `|T_W(f,g)(x)| ≤ c 3^{1/s} (2M)^{1/m} (B_{2^k}(|f|^s,|g|^s)(x))^{1/s}`
for the weight `ψ_k W` with `∑_{0<|n|≤2^k} |W(n)|^m ≤ 2 · 2^k · M`. -/
lemma norm_bilin_psiK_le {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : ∀ t, |psi χ t| ≤ c)
    {m : ℕ} {s : ℝ} (hm : 2 ≤ m) (hms : (m : ℝ)⁻¹ + s⁻¹ = 1) (W : ℤ → ℂ) (k : ℕ) {M : ℝ}
    (hM : 0 ≤ M)
    (hMom : ∑ n ∈ (Finset.Icc (-((2 ^ k : ℕ) : ℤ)) ((2 ^ k : ℕ) : ℤ)).erase 0, ‖W n‖ ^ m ≤
      2 * ((2 ^ k : ℕ) : ℝ) * M)
    (f g : ℤ → ℂ) (x : ℤ) :
    ‖bilin (fun n => ((psiK χ k n : ℝ) : ℂ) * W n) f g x‖ ≤
      c * 3 ^ (1 / s) * (2 * M) ^ (1 / (m : ℝ)) *
        (B (2 ^ k) (fun y => ((‖f y‖ ^ s : ℝ) : ℂ)) (fun y => ((‖g y‖ ^ s : ℝ) : ℂ)) x) ^
          (1 / s) := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  have hs0 : 0 < s := by
    have : 0 < s⁻¹ := by
      have h : (m : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hm1
      linarith
    exact inv_pos.1 this
  set L : ℕ := 2 ^ k with hL
  have hL1 : 1 ≤ L := Nat.one_le_two_pow
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hLpos : (0 : ℝ) < L := by linarith
  have hLeq : (L : ℝ) = 2 ^ k := by rw [hL]; push_cast; rfl
  set S : Finset ℤ := (Finset.Icc (-(L : ℤ)) L).erase 0 with hS
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0)
  -- the weight vanishes off `S`
  have hsupp : ∀ n ∉ S, ((psiK χ k n : ℝ) : ℂ) * W n = 0 := by
    intro n hn
    by_cases h0 : n = 0
    · subst h0; simp [psiK_zero]
    · have hnI : n ∉ Finset.Icc (-(L : ℤ)) L := fun h => hn (Finset.mem_erase.2 ⟨h0, h⟩)
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hnI
      have hle : (2 : ℝ) ^ k ≤ |(n : ℝ)| := by
        rw [← hLeq]
        rcases hnI with h | h
        · have : ((n : ℤ) : ℝ) < -(L : ℝ) := by exact_mod_cast h
          rw [abs_of_neg (by linarith)]; linarith
        · have : (L : ℝ) < (n : ℝ) := by exact_mod_cast h
          rw [abs_of_pos (by linarith)]; linarith
      rw [hχ.psiK_eq_zero_of_le_abs k hle]
      simp
  have hbil : bilin (fun n => ((psiK χ k n : ℝ) : ℂ) * W n) f g x
      = ∑ n ∈ S, ((psiK χ k n : ℝ) : ℂ) * W n * f (x - n) * g (x + n) := by
    unfold bilin
    exact tsum_eq_sum (fun n hn => by beta_reduce; rw [hsupp n hn]; simp)
  rw [hbil]
  -- termwise bound
  have hterm : ∀ n ∈ S, ‖((psiK χ k n : ℝ) : ℂ) * W n * f (x - n) * g (x + n)‖ ≤
      c / L * (‖W n‖ * (‖f (x - n)‖ * ‖g (x + n)‖)) := by
    intro n _
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := abs_psiK_le hc k n
    rw [← hLeq] at h1
    have h2 : |psiK χ k n| * ‖W n‖ ≤ c / L * ‖W n‖ :=
      mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    calc |psiK χ k n| * ‖W n‖ * ‖f (x - n)‖ * ‖g (x + n)‖
        = (|psiK χ k n| * ‖W n‖) * (‖f (x - n)‖ * ‖g (x + n)‖) := by ring
      _ ≤ (c / L * ‖W n‖) * (‖f (x - n)‖ * ‖g (x + n)‖) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = _ := by ring
  have h1 : ‖∑ n ∈ S, ((psiK χ k n : ℝ) : ℂ) * W n * f (x - n) * g (x + n)‖ ≤
      c / L * ∑ n ∈ S, ‖W n‖ * (‖f (x - n)‖ * ‖g (x + n)‖) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  -- Hölder in `n`
  have h2 := holder_nat hm hms S (fun n => ‖W n‖)
    (fun n => ‖f (x - n)‖ * ‖g (x + n)‖) (fun n => norm_nonneg _)
    (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  -- the second factor is dominated by `(2L+1) B_L(F,G)(x)`
  set Bx := B L (fun y => ((‖f y‖ ^ s : ℝ) : ℂ)) (fun y => ((‖g y‖ ^ s : ℝ) : ℂ)) x with hBx
  have hBx0 : 0 ≤ Bx := B_nonneg _ _ _ _
  have hY : ∑ n ∈ S, (‖f (x - n)‖ * ‖g (x + n)‖) ^ s ≤ 3 * L * Bx := by
    have e1 : ∀ n, (‖f (x - n)‖ * ‖g (x + n)‖) ^ s =
        ‖(((‖f (x - n)‖ ^ s : ℝ)) : ℂ)‖ * ‖(((‖g (x + n)‖ ^ s : ℝ)) : ℂ)‖ := fun n => by
      rw [norm_ofReal_rpow, norm_ofReal_rpow, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    simp_rw [e1]
    have e2 : ∑ n ∈ Finset.Icc (-(L : ℤ)) L,
        ‖(((‖f (x - n)‖ ^ s : ℝ)) : ℂ)‖ * ‖(((‖g (x + n)‖ ^ s : ℝ)) : ℂ)‖ =
        (2 * (L : ℝ) + 1) * Bx := by
      rw [hBx, B, ← mul_assoc, mul_one_div_cancel (by positivity), one_mul]
    calc ∑ n ∈ S, ‖(((‖f (x - n)‖ ^ s : ℝ)) : ℂ)‖ * ‖(((‖g (x + n)‖ ^ s : ℝ)) : ℂ)‖
        ≤ ∑ n ∈ Finset.Icc (-(L : ℤ)) L,
          ‖(((‖f (x - n)‖ ^ s : ℝ)) : ℂ)‖ * ‖(((‖g (x + n)‖ ^ s : ℝ)) : ℂ)‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun n _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (2 * (L : ℝ) + 1) * Bx := e2
      _ ≤ 3 * L * Bx := by gcongr; linarith
  have hX0 : 0 ≤ ∑ n ∈ S, ‖W n‖ ^ m :=
    Finset.sum_nonneg fun n _ => by positivity
  have hY0 : 0 ≤ ∑ n ∈ S, (‖f (x - n)‖ * ‖g (x + n)‖) ^ s :=
    Finset.sum_nonneg fun n _ => Real.rpow_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _
  have hXb : (∑ n ∈ S, ‖W n‖ ^ m) ^ (1 / (m : ℝ)) ≤ (2 * L * M) ^ (1 / (m : ℝ)) :=
    Real.rpow_le_rpow hX0 hMom (by positivity)
  have hYb : (∑ n ∈ S, (‖f (x - n)‖ * ‖g (x + n)‖) ^ s) ^ (1 / s) ≤ (3 * L * Bx) ^ (1 / s) :=
    Real.rpow_le_rpow hY0 hY (by positivity)
  calc _ ≤ c / L * ∑ n ∈ S, ‖W n‖ * (‖f (x - n)‖ * ‖g (x + n)‖) := h1
    _ ≤ c / L * ((2 * L * M) ^ (1 / (m : ℝ)) * (3 * L * Bx) ^ (1 / s)) := by
        refine mul_le_mul_of_nonneg_left (h2.trans ?_) (by positivity)
        exact mul_le_mul hXb hYb (by positivity) (by positivity)
    _ = _ := rpow_combine hLpos hM hBx0 hms

/-- **The `ℓ^r` bound for a weight with a controlled `m`-th moment** (N12 (a) steps 1-5, for a general
even-support weight `W`): for `1 < p, q`, `1/r = 1/p + 1/q` there are an integer `m ≥ 2` and `c₀ ≥ 0`
(depending on `χ, p, q`) such that whenever `∑_{0<|n|≤2^k} |W(n)|^m ≤ 2 · 2^k · M`,
`‖∑_n ψ_k(n) W(n) f(x-n) g(x+n)‖_{ℓ^r} ≤ c₀ M^{1/m} ‖f‖_p ‖g‖_q`. -/
theorem eLpNorm_bilin_psiK_le_of_moment {χ : ℝ → ℝ} (hχ : IsCutoff χ) {p q r : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 / r = 1 / p + 1 / q) :
    ∃ (m : ℕ) (c₀ : ℝ), 2 ≤ m ∧ 0 ≤ c₀ ∧ ∀ (W : ℤ → ℂ) (k : ℕ) (M : ℝ), 0 ≤ M →
      ∑ n ∈ (Finset.Icc (-((2 ^ k : ℕ) : ℤ)) ((2 ^ k : ℕ) : ℤ)).erase 0, ‖W n‖ ^ m ≤
        2 * ((2 ^ k : ℕ) : ℝ) * M →
      ∀ f g : ℤ → ℂ,
        eLpNorm (bilin (fun n => ((psiK χ k n : ℝ) : ℂ) * W n) f g) (ENNReal.ofReal r)
            Measure.count ≤
          ENNReal.ofReal (c₀ * M ^ (1 / (m : ℝ))) *
            eLpNorm f (ENNReal.ofReal p) Measure.count *
              eLpNorm g (ENNReal.ofReal q) Measure.count := by
  obtain ⟨m, s, hm, hs1, hsp, hsq, hms⟩ := exists_nat_conj hp hq
  obtain ⟨c, hc0, hc⟩ := hχ.exists_bound_psi
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < s := by linarith
  have hr0 : 0 < r := by
    have : 0 < 1 / r := by rw [hr]; positivity
    exact one_div_pos.1 this
  refine ⟨m, c * 3 ^ (1 / s) * 2 ^ (1 / (m : ℝ)) * 9 ^ (1 / s), hm, by positivity, ?_⟩
  intro W k M hM hMom f g
  have hpt := fun x => norm_bilin_psiK_le hχ hc hm hms W k hM hMom f g x
  set F : ℤ → ℂ := fun y => ((‖f y‖ ^ s : ℝ) : ℂ) with hF
  set G : ℤ → ℂ := fun y => ((‖g y‖ ^ s : ℝ) : ℂ) with hG
  set K : ℝ := c * 3 ^ (1 / s) * (2 * M) ^ (1 / (m : ℝ)) with hK
  have hK0 : 0 ≤ K := by positivity
  have h1 := eLpNorm_le_of_pointwise (T := bilin (fun n => ((psiK χ k n : ℝ) : ℂ) * W n) f g)
    (Bf := B (2 ^ k) F G) hK0 hr0 hs0 (fun x => B_nonneg _ _ _ _) hpt
  -- N11 at `F = |f|^s`, `G = |g|^s`
  have hu : (1 : ℝ) ≤ p / s := by rw [le_div_iff₀ hs0]; linarith
  have hv : (1 : ℝ) ≤ q / s := by rw [le_div_iff₀ hs0]; linarith
  have huvt : 1 / (r / s) = 1 / (p / s) + 1 / (q / s) := by
    have : 1 / (r / s) = s * (1 / r) := by field_simp
    rw [this, hr]
    field_simp
  have h2 := eLpNorm_B_le_real (2 ^ k) F G hu hv huvt
  rw [hF, hG, eLpNorm_norm_rpow_count f hp0 hs0, eLpNorm_norm_rpow_count g hq0 hs0] at h2
  have h3 : eLpNorm (B (2 ^ k) F G) (ENNReal.ofReal (r / s)) Measure.count ^ (1 / s) ≤
      (9 : ℝ≥0∞) ^ (1 / s) * eLpNorm f (ENNReal.ofReal p) Measure.count *
        eLpNorm g (ENNReal.ofReal q) Measure.count := by
    calc _ ≤ (9 * eLpNorm f (ENNReal.ofReal p) Measure.count ^ s *
            eLpNorm g (ENNReal.ofReal q) Measure.count ^ s) ^ (1 / s) :=
          ENNReal.rpow_le_rpow h2 (by positivity)
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
            ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            ← ENNReal.rpow_mul, mul_one_div_cancel hs0.ne', ENNReal.rpow_one, ENNReal.rpow_one]
  have e9 : ENNReal.ofReal ((9 : ℝ) ^ (1 / s)) = (9 : ℝ≥0∞) ^ (1 / s) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by positivity), ENNReal.ofReal_ofNat]
  have hconst : K * 9 ^ (1 / s) =
      c * 3 ^ (1 / s) * 2 ^ (1 / (m : ℝ)) * 9 ^ (1 / s) * M ^ (1 / (m : ℝ)) := by
    rw [hK, Real.mul_rpow (by norm_num) hM]
    ring
  calc _ ≤ ENNReal.ofReal K * eLpNorm (B (2 ^ k) F G) (ENNReal.ofReal (r / s)) Measure.count ^
        (1 / s) := h1
    _ ≤ ENNReal.ofReal K * ((9 : ℝ≥0∞) ^ (1 / s) * eLpNorm f (ENNReal.ofReal p) Measure.count *
        eLpNorm g (ENNReal.ofReal q) Measure.count) := by gcongr
    _ = ENNReal.ofReal (K * 9 ^ (1 / s)) * eLpNorm f (ENNReal.ofReal p) Measure.count *
        eLpNorm g (ENNReal.ofReal q) Measure.count := by
        rw [ENNReal.ofReal_mul hK0, e9]
        ring
    _ = _ := by rw [hconst]

/-- **N20 (b), `e:errrough`** (unconditional): for `1 < p, q`, `1/r = 1/p + 1/q` there are `b, C ≥ 0`
(depending on `χ, p, q`) such that for all `k ≥ 1` and all `f, g`,
`‖x ↦ ∑_n ψ_k(n) E_k(n) f(x-n) g(x+n)‖_{ℓ^r} ≤ C k^b ‖f‖_p ‖g‖_q`. -/
theorem eLpNorm_Serr_rough {χ : ℝ → ℝ} (hχ : IsCutoff χ) {p q r : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 / r = 1 / p + 1 / q) :
    ∃ b C : ℝ, 0 ≤ b ∧ 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ f g : ℤ → ℂ,
      eLpNorm (Serr χ k f g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * (k : ℝ) ^ b) * eLpNorm f (ENNReal.ofReal p) Measure.count *
          eLpNorm g (ENNReal.ofReal q) Measure.count := by
  obtain ⟨m, c₀, hm, hc₀, H⟩ := eLpNorm_bilin_psiK_le_of_moment hχ hp hq hr
  obtain ⟨Cm, hCm0, hCm⟩ := sum_E_pow_le m (by omega)
  have hm0 : (0 : ℝ) < m := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  set e : ℝ := (m : ℝ) + ((2 : ℝ) ^ m + m) / 10 with he
  refine ⟨e * (1 / (m : ℝ)), c₀ * Cm ^ (1 / (m : ℝ)), by positivity, by positivity, ?_⟩
  intro k hk f g
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hM0 : 0 ≤ Cm * (k : ℝ) ^ e := by positivity
  have h := H (E k) k (Cm * (k : ℝ) ^ e) hM0 (hCm k hk) f g
  rw [Serr_eq_bilin]
  refine h.trans ?_
  have hM : (Cm * (k : ℝ) ^ e) ^ (1 / (m : ℝ)) = Cm ^ (1 / (m : ℝ)) * (k : ℝ) ^ (e * (1 / (m : ℝ))) := by
    rw [Real.mul_rpow hCm0 (Real.rpow_nonneg hk0 _), ← Real.rpow_mul hk0]
  rw [hM, ← mul_assoc]

end PrimeBHT.ErrorTerms
