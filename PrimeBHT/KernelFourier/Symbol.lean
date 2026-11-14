module

public import PrimeBHT.KernelFourier.Dyadic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.Basic

/-!
# Abstract symbol bound: `|t|^j |∂^j (Φ(N ·) ∑_{k=a}^b Ψ(2^k ·))(t)| ≤ A_j`, uniformly in `N, a, b`

`Φ` has `sup_u |u|^i |Φ^{(i)}(u)| ≤ B_i` and `Ψ` satisfies the "dyadic" bound
`|u|^i |Ψ^{(i)}(u)| ≤ C_i min(|u|, |u|⁻¹)`. This is the (purely algebraic) core of the uniform bound
`e:kernel-BV` of N25 (b); the hypotheses on `Ψ = ψ̂` come from `ψ̂(0) = 0` and Schwartz decay.
-/

@[expose] public section

open scoped ContDiff

namespace PrimeBHT.KernelFourier

theorem scale_eq {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (c : ℝ) (i : ℕ) (t : ℝ) :
    |t| ^ i * ‖iteratedDeriv i (fun z => Φ (c * z)) t‖ = |c * t| ^ i * ‖iteratedDeriv i Φ (c * t)‖ := by
  have h := iteratedDeriv_comp_const_smul (hΦ.of_le (by exact_mod_cast le_top) : ContDiff ℝ i Φ) c
  rw [h]
  simp only [norm_smul, norm_pow, Real.norm_eq_abs]
  rw [abs_mul, mul_pow]
  ring

theorem scale_bound {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (B : ℕ → ℝ)
    (hB : ∀ i u, |u| ^ i * ‖iteratedDeriv i Φ u‖ ≤ B i) (c : ℝ) (i : ℕ) (t : ℝ) :
    |t| ^ i * ‖iteratedDeriv i (fun z => Φ (c * z)) t‖ ≤ B i := by
  rw [scale_eq hΦ]
  exact hB i _

theorem sum_scale_bound {Ψ : ℝ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) (C : ℕ → ℝ) (hC0 : ∀ i, 0 ≤ C i)
    (hC : ∀ i u, u ≠ 0 → |u| ^ i * ‖iteratedDeriv i Ψ u‖ ≤ C i * min |u| |u|⁻¹)
    (a b i : ℕ) {t : ℝ} (ht : t ≠ 0) :
    |t| ^ i * ‖iteratedDeriv i (fun z => ∑ k ∈ Finset.Icc a b, Ψ (2 ^ k * z)) t‖ ≤ 6 * C i := by
  have hk : ∀ k : ℕ, ContDiff ℝ ∞ (fun z : ℝ => Ψ (2 ^ k * z)) := fun k =>
    hΨ.comp (contDiff_const.mul contDiff_id)
  rw [iteratedDeriv_fun_sum (fun k _ => (hk k).contDiffAt.of_le (by exact_mod_cast le_top))]
  have hts : 0 < |t| := abs_pos.2 ht
  calc |t| ^ i * ‖∑ k ∈ Finset.Icc a b, iteratedDeriv i (fun z => Ψ (2 ^ k * z)) t‖
      ≤ |t| ^ i * ∑ k ∈ Finset.Icc a b, ‖iteratedDeriv i (fun z => Ψ (2 ^ k * z)) t‖ := by
        gcongr; exact norm_sum_le _ _
    _ = ∑ k ∈ Finset.Icc a b, |t| ^ i * ‖iteratedDeriv i (fun z => Ψ (2 ^ k * z)) t‖ := by
        rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.Icc a b, C i * min (2 ^ k * |t|) (2 ^ k * |t|)⁻¹ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [scale_eq hΨ]
        have h2 : (2 : ℝ) ^ k ≠ 0 := by positivity
        have := hC i (2 ^ k * t) (mul_ne_zero h2 ht)
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ k)] at this ⊢
        exact this
    _ = C i * ∑ k ∈ Finset.Icc a b, min (2 ^ k * |t|) (2 ^ k * |t|)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ C i * 6 := mul_le_mul_of_nonneg_left (sum_min_dyadic_le hts a b) (hC0 i)
    _ = 6 * C i := by ring

theorem symbol_core {Φ Ψ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΨ : ContDiff ℝ ∞ Ψ) (B C : ℕ → ℝ)
    (hB : ∀ i u, |u| ^ i * ‖iteratedDeriv i Φ u‖ ≤ B i) (hC0 : ∀ i, 0 ≤ C i)
    (hC : ∀ i u, u ≠ 0 → |u| ^ i * ‖iteratedDeriv i Ψ u‖ ≤ C i * min |u| |u|⁻¹)
    (N : ℝ) (a b j : ℕ) {t : ℝ} (ht : t ≠ 0) :
    |t| ^ j * ‖iteratedDeriv j (fun z => Φ (N * z) * ∑ k ∈ Finset.Icc a b, Ψ (2 ^ k * z)) t‖ ≤
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i * (6 * C (j - i)) := by
  have hf : ContDiff ℝ ∞ (fun z : ℝ => Φ (N * z)) := hΦ.comp (contDiff_const.mul contDiff_id)
  have hg : ContDiff ℝ ∞ (fun z : ℝ => ∑ k ∈ Finset.Icc a b, Ψ (2 ^ k * z)) :=
    ContDiff.sum fun k _ => hΨ.comp (contDiff_const.mul contDiff_id)
  have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hf hg t (n := j) (by exact_mod_cast le_top)
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hL
  calc |t| ^ j * ‖iteratedDeriv j (fun z => Φ (N * z) * ∑ k ∈ Finset.Icc a b, Ψ (2 ^ k * z)) t‖
      ≤ |t| ^ j * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedDeriv i (fun z => Φ (N * z)) t‖ *
          ‖iteratedDeriv (j - i) (fun z => ∑ k ∈ Finset.Icc a b, Ψ (2 ^ k * z)) t‖ := by
        gcongr
    _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (|t| ^ i * ‖iteratedDeriv i (fun z => Φ (N * z)) t‖) *
          (|t| ^ (j - i) *
            ‖iteratedDeriv (j - i) (fun z => ∑ k ∈ Finset.Icc a b, Ψ (2 ^ k * z)) t‖) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hij : i ≤ j := by have := Finset.mem_range.1 hi; omega
        have : |t| ^ j = |t| ^ i * |t| ^ (j - i) := by rw [← pow_add]; congr 1; omega
        rw [this]; ring
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i * (6 * C (j - i)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := scale_bound hΦ B hB N i t
        have h2 := sum_scale_bound hΨ C hC0 hC a b (j - i) ht
        have h3 : 0 ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
        have hBi : 0 ≤ B i := le_trans (by positivity) (hB i 0)
        have h4 : 0 ≤ |t| ^ i * ‖iteratedDeriv i (fun z => Φ (N * z)) t‖ := by positivity
        have h5 : 0 ≤ |t| ^ (j - i) *
            ‖iteratedDeriv (j - i) (fun z => ∑ k ∈ Finset.Icc a b, Ψ (2 ^ k * z)) t‖ := by positivity
        calc (j.choose i : ℝ) * (|t| ^ i * ‖iteratedDeriv i (fun z => Φ (N * z)) t‖) *
              (|t| ^ (j - i) *
                ‖iteratedDeriv (j - i) (fun z => ∑ k ∈ Finset.Icc a b, Ψ (2 ^ k * z)) t‖)
            ≤ (j.choose i : ℝ) * B i * (6 * C (j - i)) := by gcongr
            _ = _ := rfl

end PrimeBHT.KernelFourier
