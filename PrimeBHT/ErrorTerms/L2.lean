module

public import PrimeBHT.SingleScaleL1.FourFourTwo
public import PrimeBHT.ErrorTerms.Rough
public import PrimeCarleson.Frozen.HeathBrownModel
public import PrimeCarleson.Frozen.GowersNormInterval
public import PrimeCarleson.Frozen.RestrictInterval

/-!
# N20 (a), `e:errL2`, conditional on the sealed `[F+, Prop 3.1]` (X3)

`X3Statement` is the frozen theorem `PrimeCarleson.vonMangoldt_sub_heathBrown_U3` (not importable here:
its proof closure is not vendored) written as a `Prop`, character for character:
for every `A ≥ 1` there is `C` with, for all `N : ℕ+`, `2 ≤ N`,
`‖Λ - Λ_{≤ exp ((log N)^{1/10})}‖_{U³[N]} ≤ C (log N)^{-A}`.

Every theorem that uses it is named `…_of_X3`.

* `psiK_eq_phiPos_of_pos`, `bilin_psiK_mul_eq`: the reflection `n ↦ -n` for an *even* weight `W`
  (`T_W(f,g) = S₊(f,g) - S₊(g,f)`, the argument of `PrimeBHT.SingleScaleL1.bilin_weight_eq` for
  a general `W`);
* `eLpNorm_bilin_psiK_le_gowers`: `‖T_W(f,g)‖_{ℓ²} ≤ 16 M ‖W‖_{U³([2^k])} ‖f‖_{ℓ⁴} ‖g‖_{ℓ⁴}`
  (`l:U3maxmod` (b));
* `gowersNormInterval_E_le_of_X3`: `‖E_k‖_{U³([2^k])} ≤ C_A k^{-A}`, `N = 2^k`, `Mk_eq_pnat`,
  `E_eq_of_pos` (`gowersNormInterval` only sees `[1,N]`);
* `eLpNorm_Serr_le_of_X3`: **`e:errL2`**.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace PrimeBHT.ErrorTerms

open PrimeBHT.Kernel PrimeBHT.Decomposition PrimeBHT.SingleScaleL1 PrimeCarleson

/-- **The sealed `[F+, Prop 3.1]` (X3)**, exactly as the frozen theorem
`PrimeCarleson.vonMangoldt_sub_heathBrown_U3` reads. -/
def X3Statement : Prop :=
  ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, ∀ N : ℕ+, 2 ≤ N →
      gowersNormInterval 3 N
          (fun n => ((ArithmeticFunction.vonMangoldt n.toNat : ℝ) : ℂ) -
            heathBrownModel (Real.exp (Real.log N ^ ((1 : ℝ) / 10))) n) ≤
        C * Real.log N ^ (-A)

/-! ### The reflection for an even weight -/

lemma psiK_eq_phiPos_of_pos (χ : ℝ → ℝ) (k : ℕ) {n : ℤ} (hn : 0 < n) :
    ((psiK χ k n : ℝ) : ℂ) = (((pow2 k : ℕ+) : ℕ) : ℂ)⁻¹ *
      ((phiPos χ ((n : ℝ) / (((pow2 k : ℕ+) : ℕ) : ℝ)) : ℝ) : ℂ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (((pow2 k : ℕ+) : ℕ) : ℝ) = 2 ^ k := by simp [pow2]
  rw [hpow, phiPos_of_pos (by positivity)]
  simp only [psiK, pow2_coe]
  push_cast
  ring

lemma psiK_eq_zero_of_notMem_Icc {χ : ℝ → ℝ} (hχ : IsCutoff χ) (k : ℕ) {n : ℤ}
    (hn : n ∉ Finset.Icc (-((2 ^ k : ℕ) : ℤ)) ((2 ^ k : ℕ) : ℤ)) : psiK χ k n = 0 := by
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
  have hLeq : (((2 ^ k : ℕ) : ℤ) : ℝ) = 2 ^ k := by push_cast; rfl
  have hle : (2 : ℝ) ^ k ≤ |(n : ℝ)| := by
    rw [← hLeq]
    have hp : (0 : ℝ) < (((2 ^ k : ℕ) : ℤ) : ℝ) := by rw [hLeq]; positivity
    rcases hn with h | h
    · have : ((n : ℤ) : ℝ) < -(((2 ^ k : ℕ) : ℤ) : ℝ) := by exact_mod_cast h
      rw [abs_of_neg (by linarith)]; linarith
    · have : (((2 ^ k : ℕ) : ℤ) : ℝ) < (n : ℝ) := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]; linarith
  exact hχ.psiK_eq_zero_of_le_abs k hle

/-- The reflection identity for an even weight `W`: `T_W(f,g) = S₊(f,g) - S₊(g,f)`, where
`T_W(f,g)(x) = ∑_n ψ_k(n) W(n) f(x-n) g(x+n)`. -/
lemma bilin_psiK_mul_eq {χ : ℝ → ℝ} (hχ : IsCutoff χ) (k : ℕ) (W : ℤ → ℂ)
    (hW : ∀ n, W (-n) = W n) (f g : ℤ → ℂ) (x : ℤ) :
    bilin (fun n => ((psiK χ k n : ℝ) : ℂ) * W n) f g x =
      Splus (phiPos χ) (pow2 k) W f g x - Splus (phiPos χ) (pow2 k) W g f x := by
  set N0 : ℤ := ((2 ^ k : ℕ) : ℤ) with hN0
  set F : ℤ → ℂ := fun n => ((psiK χ k n : ℝ) : ℂ) * W n * f (x - n) * g (x + n) with hF
  have h1 : bilin (fun n => ((psiK χ k n : ℝ) : ℂ) * W n) f g x =
      ∑ n ∈ Finset.Icc (-N0) N0, F n := by
    unfold bilin
    exact tsum_eq_sum (fun n hn => by
      show ((psiK χ k n : ℝ) : ℂ) * W n * f (x - n) * g (x + n) = 0
      rw [psiK_eq_zero_of_notMem_Icc hχ k hn]
      simp)
  have hsplit : ∑ n ∈ Finset.Icc (-N0) N0, F n =
      ∑ n ∈ Finset.Icc (1 : ℤ) N0, F n + ∑ m ∈ Finset.Icc (1 : ℤ) N0, F (-m) := by
    have hdisj : Disjoint (Finset.Icc (1 : ℤ) N0) ((Finset.Icc (1 : ℤ) N0).image Neg.neg) := by
      rw [Finset.disjoint_left]
      intro n hn hn'
      simp only [Finset.mem_Icc, Finset.mem_image] at hn hn'
      obtain ⟨m, hm, rfl⟩ := hn'
      omega
    have himg : ∑ m ∈ Finset.Icc (1 : ℤ) N0, F (-m) =
        ∑ n ∈ (Finset.Icc (1 : ℤ) N0).image Neg.neg, F n :=
      (Finset.sum_image (f := F) (fun a _ b _ h => neg_injective h)).symm
    rw [himg, ← Finset.sum_union hdisj]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro n hn
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_image] at hn ⊢
      rcases hn with hn | ⟨m, hm, rfl⟩ <;> omega
    · intro n hn hn'
      have h0 : n = 0 := by
        simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_image, not_or, not_exists,
          not_and] at hn hn'
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact hn'.2 (-n) (by omega) (by omega)
        · exact hn'.1 (by omega) (by omega)
      subst h0
      simp only [hF]
      show ((psiK χ k ((0 : ℤ) : ℝ) : ℝ) : ℂ) * _ * _ * _ = 0
      simp [psiK_zero]
  rw [h1, hsplit]
  have hpos : ∑ n ∈ Finset.Icc (1 : ℤ) N0, F n =
      Splus (phiPos χ) (pow2 k) W f g x := by
    unfold Splus
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    simp only [hF]
    rw [psiK_eq_phiPos_of_pos χ k (by omega)]
  have hneg : ∑ m ∈ Finset.Icc (1 : ℤ) N0, F (-m) =
      -Splus (phiPos χ) (pow2 k) W g f x := by
    unfold Splus
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    simp only [hF]
    have hpk : ((psiK χ k ((-n : ℤ) : ℝ) : ℝ) : ℂ) = -((psiK χ k n : ℝ) : ℂ) := by
      rw [Int.cast_neg, hχ.psiK_neg]
      push_cast
      ring
    rw [hpk, hW, psiK_eq_phiPos_of_pos χ k (by omega)]
    simp only [sub_neg_eq_add, ← sub_eq_add_neg]
    ring
  rw [hpos, hneg]
  ring

/-! ### The `ℓ²` bound in terms of the `U³` norm of an even weight -/

/-- `‖T_W(f,g)‖_{ℓ²} ≤ 16 M ‖W‖_{U³([2^k])} ‖f‖_{ℓ⁴} ‖g‖_{ℓ⁴}` for every even `W : ℤ → ℂ`
(`M = M(χ)` the sup-norm constant of `φ = ψ 1_{(0,∞)}` and `φ''`). -/
theorem eLpNorm_bilin_psiK_le_gowers {χ : ℝ → ℝ} (hχ : IsCutoff χ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (k : ℕ) (W : ℤ → ℂ), (∀ n, W (-n) = W n) → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (bilin (fun n => ((psiK χ k n : ℝ) : ℂ) * W n) ⇑f ⇑g) 2 Measure.count ≤
        ENNReal.ofReal (16 * M * gowersNormInterval 3 (pow2 k) W) *
          eLpNorm (⇑f) 4 Measure.count * eLpNorm (⇑g) 4 Measure.count := by
  obtain ⟨M, hM0, h0, h2⟩ := exists_bounds_phiPos hχ
  have hφ : ContDiff ℝ 2 (phiPos χ) := (contDiff_phiPos hχ).of_le (by simp)
  refine ⟨M, hM0, fun k W hW f g => ?_⟩
  have hS : ∀ f g : ℤ →₀ ℂ, eLpNorm (Splus (phiPos χ) (pow2 k) W ⇑f ⇑g) 2 Measure.count ≤
      ENNReal.ofReal (8 * M * gowersNormInterval 3 (pow2 k) W) * eLpNorm (⇑f) 4 Measure.count *
        eLpNorm (⇑g) 4 Measure.count := fun f g =>
    PrimeBHT.U3MaxMod.eLpNorm_smooth_le_real (pow2 k) W f g hφ (support_phiPos_subset hχ) h0 h2
  have heq : bilin (fun n => ((psiK χ k n : ℝ) : ℂ) * W n) ⇑f ⇑g =
      Splus (phiPos χ) (pow2 k) W ⇑f ⇑g - Splus (phiPos χ) (pow2 k) W ⇑g ⇑f := by
    funext x
    exact bilin_psiK_mul_eq hχ k W hW _ _ x
  have hU0 : 0 ≤ gowersNormInterval 3 (pow2 k) W :=
    div_nonneg (PrimeCarleson.Proof.Paper.gowersNorm_nonneg _ _)
      (PrimeCarleson.Proof.Paper.gowersNorm_nonneg _ _)
  rw [heq]
  refine (eLpNorm_sub_le (by norm_num)).trans ?_
  have h16 : ENNReal.ofReal (16 * M * gowersNormInterval 3 (pow2 k) W) =
      2 * ENNReal.ofReal (8 * M * gowersNormInterval 3 (pow2 k) W) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  rw [h16]
  calc _ ≤ ENNReal.ofReal (8 * M * gowersNormInterval 3 (pow2 k) W) * eLpNorm (⇑f) 4 Measure.count *
        eLpNorm (⇑g) 4 Measure.count +
      ENNReal.ofReal (8 * M * gowersNormInterval 3 (pow2 k) W) * eLpNorm (⇑g) 4 Measure.count *
        eLpNorm (⇑f) 4 Measure.count := add_le_add (hS f g) (hS g f)
    _ = _ := by ring

/-! ### X3 at `N = 2^k` -/

/-- `‖W‖_{U³([N])}` depends on `W` only through its values on `[1, N]`. -/
lemma gowersNormInterval_congr {s N : ℕ+} {g g' : ℤ → ℂ}
    (h : ∀ n ∈ Finset.Icc (1 : ℤ) N, g n = g' n) :
    gowersNormInterval s N g = gowersNormInterval s N g' := by
  have : restrictInterval N g = restrictInterval N g' := by
    ext n
    simp only [restrictInterval, Finsupp.indicator_apply]
    split_ifs with hn
    · exact h n hn
    · rfl
  simp only [gowersNormInterval, this]

/-- X3 at `N = 2^k`: `‖E_k‖_{U³([2^k])} ≤ C_A k^{-A}` for all `k ≥ 1`. -/
theorem gowersNormInterval_E_le_of_X3 (hX3 : X3Statement) {A : ℝ} (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      gowersNormInterval 3 (pow2 k) (E k) ≤ C * (k : ℝ) ^ (-A) := by
  obtain ⟨C, hC⟩ := hX3 A hA
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨max C 0 * Real.log 2 ^ (-A), by positivity, fun k hk => ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hN2 : (2 : ℕ+) ≤ pow2 k := by
    rw [← PNat.coe_le_coe, pow2_coe]
    show 2 ≤ 2 ^ k
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hNR : (((pow2 k : ℕ+) : ℕ) : ℝ) = 2 ^ k := by simp [pow2]
  have hcut : Real.exp (Real.log (((pow2 k : ℕ+) : ℕ) : ℝ) ^ ((1 : ℝ) / 10)) = Mk k := by
    rw [hNR]; rfl
  have hX := hC (pow2 k) hN2
  rw [hcut] at hX
  have hcongr : gowersNormInterval 3 (pow2 k) (E k) =
      gowersNormInterval 3 (pow2 k)
        (fun n => ((ArithmeticFunction.vonMangoldt n.toNat : ℝ) : ℂ) -
          heathBrownModel (Mk k) n) := by
    refine gowersNormInterval_congr fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    exact E_eq_of_pos k (by omega)
  rw [hcongr]
  refine hX.trans ?_
  have hlogN : Real.log (((pow2 k : ℕ+) : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
    rw [hNR, Real.log_pow]
  rw [hlogN, Real.mul_rpow hk0 hl2.le]
  have hpos : 0 ≤ (k : ℝ) ^ (-A) * Real.log 2 ^ (-A) := by positivity
  calc C * ((k : ℝ) ^ (-A) * Real.log 2 ^ (-A))
      ≤ max C 0 * ((k : ℝ) ^ (-A) * Real.log 2 ^ (-A)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
    _ = _ := by ring

/-- **N20 (a), `e:errL2`, conditional on X3.** For every `A ≥ 1` there is `C_A` with
`‖x ↦ ∑_n ψ_k(n) E_k(n) f(x-n) g(x+n)‖_{ℓ²} ≤ C_A k^{-A} ‖f‖_{ℓ⁴} ‖g‖_{ℓ⁴}` for all `k ≥ 1` and all
finitely supported `f, g`. -/
theorem eLpNorm_Serr_le_of_X3 (hX3 : X3Statement) {χ : ℝ → ℝ} (hχ : IsCutoff χ) {A : ℝ}
    (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (Serr χ k ⇑f ⇑g) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal (C * (k : ℝ) ^ (-A)) * eLpNorm (⇑f) (ENNReal.ofReal 4) Measure.count *
          eLpNorm (⇑g) (ENNReal.ofReal 4) Measure.count := by
  obtain ⟨M, hM0, hM⟩ := eLpNorm_bilin_psiK_le_gowers hχ
  obtain ⟨C₁, hC₁0, hC₁⟩ := gowersNormInterval_E_le_of_X3 hX3 hA
  refine ⟨16 * M * C₁, by positivity, fun k hk f g => ?_⟩
  have h := hM k (E k) (fun n => E_neg k n) f g
  rw [Serr_eq_bilin]
  simp only [ENNReal.ofReal_ofNat] at h ⊢
  refine h.trans ?_
  have hk0 : (0 : ℝ) ≤ (k : ℝ) ^ (-A) := Real.rpow_nonneg (Nat.cast_nonneg k) _
  have : 16 * M * gowersNormInterval 3 (pow2 k) (E k) ≤ 16 * M * C₁ * (k : ℝ) ^ (-A) := by
    rw [mul_assoc (16 * M)]
    exact mul_le_mul_of_nonneg_left (hC₁ k hk) (by positivity)
  gcongr

end PrimeBHT.ErrorTerms
