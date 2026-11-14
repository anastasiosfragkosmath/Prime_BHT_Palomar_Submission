module

public import PrimeBHT.TimeFrequency.X2.Classes
public import PrimeBHT.TimeFrequency.X2.ClassKernel
public import PrimeBHT.TimeFrequency.X2.ClassLemmas
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# X2, node V10: kernel decay of every order `M ≤ D` of the multipliers of the class `M_ω(𝔭)`

`ClassKernel.norm_fourierInv_le` gives the decay `(1 + l|w|)^{-2}` (two derivatives).  The Gram estimates of
V10 (translates `R^{+n}` of a tile, nested tiles with `Peetre` factors `⟨n |I'|/|I|⟩^{M}`) need decay of a higher
order; the class controls `D ≥ 400` derivatives, so
`‖𝓕⁻ m w‖ ≤ 2^M β C 2^{-s} (1 + |w|/2^s)^{-M}` for every `M ≤ D` (`norm_fourierInv_inMult_le_pow`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform ContDiff Real

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- Decay of order `M` of the kernel `𝓕⁻ n` of a smooth compactly supported multiplier
(support in `|ξ - c| ≤ r`, `‖n‖ ≤ A`, `‖n^{(M)}‖ ≤ A l^{-M}`): `‖𝓕⁻ n w‖ ≤ 2^{M+1} (2r) A (1 + l|w|)^{-M}`. -/
theorem norm_fourierInv_le_pow {n : ℝ → ℂ} {c r A l : ℝ} (M : ℕ) (hr : 0 ≤ r) (hl : 0 < l)
    (hn : ContDiff ℝ M n) (hsupp : ∀ ξ, r < |ξ - c| → n ξ = 0)
    (h0 : ∀ ξ, ‖n ξ‖ ≤ A) (hM : ∀ ξ, ‖iteratedDeriv M n ξ‖ ≤ A * (l⁻¹) ^ M) (w : ℝ) :
    ‖𝓕⁻ n w‖ ≤ 2 ^ (M + 1) * (2 * r) * A * ((1 + l * |w|)⁻¹) ^ M := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (h0 0)
  have hint : ∀ k : ℕ, k ≤ M → Integrable (iteratedDeriv k n) := fun k hk =>
    integrable_of_far (hn.continuous_iteratedDeriv k (by exact_mod_cast hk))
      (fun ξ hξ => iteratedDeriv_eq_zero_of_far hsupp k hξ)
  have hK0 : ‖𝓕⁻ n w‖ ≤ 2 * r * A := by
    rw [Real.fourierInv_eq_fourier_neg]
    exact (Real.norm_fourier_le_integral_norm n (-w)).trans
      (integral_norm_le_of_far hr hsupp h0)
  have hFM : 𝓕 (iteratedDeriv M n) = fun x : ℝ => (2 * π * Complex.I * x) ^ M • 𝓕 n x :=
    Real.fourier_iteratedDeriv (N := (M : ℕ∞)) hn
      (fun k hk => hint k (by exact_mod_cast hk)) (by exact_mod_cast le_rfl)
  have hnorm : ∀ x : ℝ, ‖(2 * π * Complex.I * x : ℂ) ^ M‖ = (2 * π * |x|) ^ M := by
    intro x
    rw [norm_pow]
    congr 1
    simp only [Complex.norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_one,
      Complex.norm_ofNat, abs_of_pos Real.pi_pos]
  have hKM : (2 * π * |w|) ^ M * ‖𝓕⁻ n w‖ ≤ 2 * r * (A * (l⁻¹) ^ M) := by
    have h1 := Real.norm_fourier_le_integral_norm (iteratedDeriv M n) (-w)
    rw [hFM] at h1
    simp only [norm_smul, hnorm] at h1
    have h3 : (2 * π * |-w|) ^ M * ‖𝓕 n (-w)‖ ≤ 2 * r * (A * (l⁻¹) ^ M) :=
      h1.trans (integral_norm_le_of_far hr (fun ξ hξ => iteratedDeriv_eq_zero_of_far hsupp M hξ) hM)
    rw [Real.fourierInv_eq_fourier_neg]
    rwa [abs_neg] at h3
  set K := ‖𝓕⁻ n w‖ with hK
  have hK_nn : 0 ≤ K := norm_nonneg _
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  have hlw : 0 < 1 + l * |w| := by positivity
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hlM : l ^ M * (l⁻¹) ^ M = 1 := by rw [← mul_pow, mul_inv_cancel₀ hl.ne']; simp
  have e1 : (2 * π * |w|) ^ M * K * l ^ M ≤ 2 * r * A := by
    have := mul_le_mul_of_nonneg_right hKM (pow_nonneg hl.le M)
    calc (2 * π * |w|) ^ M * K * l ^ M ≤ 2 * r * (A * (l⁻¹) ^ M) * l ^ M := this
      _ = 2 * r * A * (l ^ M * (l⁻¹) ^ M) := by ring
      _ = 2 * r * A := by rw [hlM]; ring
  have e2 : (l * |w|) ^ M * K ≤ 2 * r * A := by
    have h4 : (2 * π * |w|) ^ M * K * l ^ M = (2 * π) ^ M * ((l * |w|) ^ M * K) := by
      rw [mul_pow, mul_pow]; ring
    rw [h4] at e1
    have hX : 0 ≤ (l * |w|) ^ M * K := mul_nonneg (pow_nonneg (by positivity) _) hK_nn
    have hpi2 : 1 ≤ (2 * π) ^ M := one_le_pow₀ (by linarith)
    nlinarith [mul_nonneg (sub_nonneg.2 hpi2) hX]
  -- `(1 + t)^M ≤ 2^{M-1}(1 + t^M)` for `M ≥ 1`, trivial for `M = 0`
  have h5 : (1 + l * |w|) ^ M ≤ 2 ^ M * (1 + (l * |w|) ^ M) := by
    have ht : 0 ≤ l * |w| := by positivity
    rcases le_total (l * |w|) 1 with h | h
    · calc (1 + l * |w|) ^ M ≤ 2 ^ M := pow_le_pow_left₀ (by positivity) (by linarith) M
        _ ≤ 2 ^ M * (1 + (l * |w|) ^ M) := by
          nlinarith [pow_nonneg ht M, pow_pos (by norm_num : (0 : ℝ) < 2) M]
    · calc (1 + l * |w|) ^ M ≤ (2 * (l * |w|)) ^ M := pow_le_pow_left₀ (by positivity) (by linarith) M
        _ = 2 ^ M * (l * |w|) ^ M := by rw [mul_pow]
        _ ≤ 2 ^ M * (1 + (l * |w|) ^ M) := by
          nlinarith [pow_nonneg ht M, pow_pos (by norm_num : (0 : ℝ) < 2) M]
  calc K * (1 + l * |w|) ^ M ≤ K * (2 ^ M * (1 + (l * |w|) ^ M)) := mul_le_mul_of_nonneg_left h5 hK_nn
    _ = 2 ^ M * (K + (l * |w|) ^ M * K) := by ring
    _ ≤ 2 ^ M * (2 * r * A + 2 * r * A) := by gcongr
    _ = 2 ^ (M + 1) * (2 * r) * A := by ring

/-- **Kernel decay of order `M ≤ D` in the class `M_ω(𝔭)`** (`ω` of length `l = 2^{-s}`):
`‖𝓕⁻ m w‖ ≤ 2^{M+1} β C l (1 + l|w|)^{-M}`. -/
theorem norm_fourierInv_inMult_le_pow {𝔭 : Params} {M : ℕ} (hM : M ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) {s : ℤ}
    {c : ℝ} {m : ℝ → ℂ} (hm : InMult 𝔭 s c m) (w : ℝ) :
    ‖𝓕⁻ m w‖ ≤ 2 ^ (M + 1) * 𝔭.β * 𝔭.C * (2 ^ (-s) * ((1 + 2 ^ (-s) * |w|)⁻¹) ^ M : ℝ) := by
  obtain ⟨hsm, hsupp, hder⟩ := hm
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-s) := zpow_pos (by norm_num) _
  have hC : 0 ≤ 𝔭.C := by
    have := hder 0 (Nat.zero_le _) 0
    simp only [pow_zero, one_mul, iteratedDeriv_zero] at this
    exact (norm_nonneg _).trans this
  have hk := norm_fourierInv_le_pow (n := m) (c := c) (r := 𝔭.β * (2 : ℝ) ^ (-s) / 2) (A := 𝔭.C)
    (l := (2 : ℝ) ^ (-s)) M (by positivity) hl (hsm.of_le (by exact_mod_cast le_top)) hsupp
    (fun ξ => by simpa using hder 0 (Nat.zero_le _) ξ)
    (fun ξ => by
      have h := hder M hM ξ
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      linarith) w
  refine hk.trans (le_of_eq ?_)
  ring

end PrimeBHT.TimeFrequency.X2
