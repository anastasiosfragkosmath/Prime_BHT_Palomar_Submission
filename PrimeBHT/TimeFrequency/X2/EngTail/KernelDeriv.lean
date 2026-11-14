module

public import PrimeBHT.TimeFrequency.X2.Ortho.Kernel
public import PrimeBHT.TimeFrequency.X2.EngTail.CZKernel
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# X2, node B5: derivative of the kernel of a class multiplier

For `n ∈ M_ω(𝔭)` (`InMult 𝔭 s c n`, length `l = 2^{-s}`, centre `c`) with `|c| ≤ C₀ l`:
`𝓕⁻ n` is differentiable, `(𝓕⁻ n)' = 𝓕⁻(2πi η n)` and
`‖(𝓕⁻ n)'(w)‖ ≤ 2^{M+1} (β l) (2π C l (C₀ + β/2 + M)) (1 + l|w|)^{-M}` for `M + 1 ≤ D`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform ContDiff Real

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- Leibniz for `(η - a) · n(η)`: `D^{k+1}[(η - a) n] = (η - a) D^{k+1} n + (k+1) D^k n`. -/
theorem iteratedDeriv_sub_mul {n : ℝ → ℂ} (hn : ContDiff ℝ ∞ n) (a : ℝ) (k : ℕ) :
    iteratedDeriv (k + 1) (fun η : ℝ => ((η - a : ℝ) : ℂ) * n η) =
      fun η => ((η - a : ℝ) : ℂ) * iteratedDeriv (k + 1) n η + ((k + 1 : ℕ) : ℂ) * iteratedDeriv k n η := by
  have hdiff : ∀ j : ℕ, Differentiable ℝ (iteratedDeriv j n) := fun j =>
    hn.differentiable_iteratedDeriv j (by exact_mod_cast WithTop.coe_lt_top _)
  induction k with
  | zero =>
    ext η
    have h1 : HasDerivAt (fun η : ℝ => ((η - a : ℝ) : ℂ)) 1 η := by
      have := ((hasDerivAt_id η).sub_const a).ofReal_comp
      simpa using this
    have h2 : HasDerivAt (fun η : ℝ => ((η - a : ℝ) : ℂ) * iteratedDeriv 0 n η)
        (1 * iteratedDeriv 0 n η + ((η - a : ℝ) : ℂ) * deriv (iteratedDeriv 0 n) η) η :=
      h1.mul ((hdiff 0).differentiableAt (x := η)).hasDerivAt
    rw [iteratedDeriv_one]
    simp only [iteratedDeriv_zero] at h2
    rw [h2.deriv]
    simp [iteratedDeriv_one]
    ring
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    ext η
    have h1 : HasDerivAt (fun η : ℝ => ((η - a : ℝ) : ℂ)) 1 η := by
      have := ((hasDerivAt_id η).sub_const a).ofReal_comp
      simpa using this
    have h2 : HasDerivAt (fun η : ℝ => ((η - a : ℝ) : ℂ) * iteratedDeriv (k + 1) n η +
        ((k + 1 : ℕ) : ℂ) * iteratedDeriv k n η)
        (1 * iteratedDeriv (k + 1) n η + ((η - a : ℝ) : ℂ) * deriv (iteratedDeriv (k + 1) n) η +
          ((k + 1 : ℕ) : ℂ) * deriv (iteratedDeriv k n) η) η :=
      (h1.mul ((hdiff (k + 1)).differentiableAt (x := η)).hasDerivAt).add
        (((hdiff k).differentiableAt (x := η)).hasDerivAt.const_mul (((k + 1 : ℕ) : ℂ)))
    rw [h2.deriv]
    have e1 : deriv (iteratedDeriv k n) η = iteratedDeriv (k + 1) n η := by rw [iteratedDeriv_succ]
    have e2 : deriv (iteratedDeriv (k + 1) n) η = iteratedDeriv (k + 1 + 1) n η := by
      rw [iteratedDeriv_succ (n := k + 1)]
    rw [e1, e2]
    push_cast
    ring

/-- The derivative of `𝓕⁻ n` for a continuous compactly supported `n`. -/
theorem hasDerivAt_fourierInv_cs {n : ℝ → ℂ} (hn : Continuous n) {c r : ℝ}
    (hsupp : ∀ ξ, r < |ξ - c| → n ξ = 0) (w : ℝ) :
    HasDerivAt (𝓕⁻ n) (𝓕⁻ (fun η : ℝ => (2 * π * Complex.I * η) * n η) w) w := by
  have hint : Integrable n := integrable_of_far hn hsupp
  have hint' : Integrable (fun x : ℝ => x • n x) := by
    have : Continuous fun x : ℝ => x • n x := continuous_id.smul hn
    refine this.integrable_of_hasCompactSupport ?_
    exact hasCompactSupport_of_far (c := c) (r := r) (fun ξ hξ => by simp [hsupp ξ hξ])
  have h1 := Real.hasDerivAt_fourier hint hint' (-w)
  have h2 := h1.scomp w (hasDerivAt_neg w)
  have e : 𝓕⁻ n = (𝓕 n) ∘ Neg.neg := by
    funext w'; exact Real.fourierInv_eq_fourier_neg n w'
  rw [e]
  convert h2 using 1
  rw [Real.fourierInv_eq_fourier_neg]
  have : (fun x : ℝ => (-2 * (π : ℂ) * Complex.I * x) • n x) =
      fun x => (-1 : ℂ) * ((2 * π * Complex.I * x) * n x) := by
    funext x; simp [smul_eq_mul]
  rw [this, fourier_const_mul']
  simp


/-- Decay of the derivative of the kernel of a class multiplier with centre `|c| ≤ C₀ l`. -/
theorem norm_fourierInv_deriv_inMult_le {𝔭 : Params} {M : ℕ} (hM1 : 1 ≤ M) (hM : M ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β)
    {s : ℤ} {c C₀ : ℝ} {n : ℝ → ℂ} (hn : InMult 𝔭 s c n) (hC₀ : 0 ≤ C₀) (hc : |c| ≤ C₀ * (2 : ℝ) ^ (-s))
    (w : ℝ) :
    ‖𝓕⁻ (fun η : ℝ => (2 * π * Complex.I * η) * n η) w‖ ≤
      2 ^ (M + 1) * (2 * (𝔭.β * (2 : ℝ) ^ (-s) / 2)) *
        (2 * π * 𝔭.C * (2 : ℝ) ^ (-s) * (C₀ + 𝔭.β / 2 + M)) * ((1 + (2 : ℝ) ^ (-s) * |w|)⁻¹) ^ M := by
  obtain ⟨hsm, hsupp, hder⟩ := hn
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-s) := zpow_pos (by norm_num) _
  set l : ℝ := (2 : ℝ) ^ (-s) with hldef
  have hC : 0 ≤ 𝔭.C := by
    have := hder 0 (Nat.zero_le _) 0
    simp only [pow_zero, one_mul, iteratedDeriv_zero] at this
    exact (norm_nonneg _).trans this
  have hr : 0 ≤ 𝔭.β * l / 2 := by positivity
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℂ, c₂ = 2 * π * Complex.I := ⟨_, rfl⟩
  have hc₂n : ‖c₂‖ = 2 * π := by
    simp [hc₂, abs_of_pos Real.pi_pos]
  set P : ℝ → ℂ := fun η => (2 * π * Complex.I * η) * n η with hP
  have hPeq : P = fun η => c₂ * (((η - 0 : ℝ) : ℂ) * n η) := by
    funext η; simp only [hP, hc₂]; push_cast; ring
  have hQsm : ContDiff ℝ ∞ (fun η : ℝ => ((η - 0 : ℝ) : ℂ) * n η) :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_id.sub contDiff_const)).mul hsm
  have hPsm : ContDiff ℝ M P := by
    rw [hPeq]
    exact (contDiff_const.mul hQsm).of_le (by exact_mod_cast le_top)
  have hPsupp : ∀ ξ, 𝔭.β * l / 2 < |ξ - c| → P ξ = 0 := fun ξ hξ => by simp only [hP, hsupp ξ hξ, mul_zero]
  have hη : ∀ ξ, |ξ - c| ≤ 𝔭.β * l / 2 → |ξ| ≤ (C₀ + 𝔭.β / 2) * l := by
    intro ξ hξ
    have h1 : |ξ| ≤ |ξ - c| + |c| := by
      calc |ξ| = |(ξ - c) + c| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    nlinarith
  set A : ℝ := 2 * π * 𝔭.C * l * (C₀ + 𝔭.β / 2 + M) with hA
  have hApos : 0 ≤ A := by positivity
  have h0 : ∀ ξ, ‖P ξ‖ ≤ A := by
    intro ξ
    by_cases hξ : |ξ - c| ≤ 𝔭.β * l / 2
    · have h1 := hη ξ hξ
      have h2 : ‖n ξ‖ ≤ 𝔭.C := by
        have := hder 0 (Nat.zero_le _) ξ
        simpa using this
      rw [hPeq]
      show ‖c₂ * (((ξ - 0 : ℝ) : ℂ) * n ξ)‖ ≤ A
      rw [norm_mul, norm_mul, hc₂n, Complex.norm_real, Real.norm_eq_abs, sub_zero]
      calc 2 * π * (|ξ| * ‖n ξ‖) ≤ 2 * π * (((C₀ + 𝔭.β / 2) * l) * 𝔭.C) := by gcongr
        _ ≤ A := by
          simp only [hA]
          have : 0 ≤ 2 * π * 𝔭.C * l := by positivity
          nlinarith [mul_nonneg this (Nat.cast_nonneg (α := ℝ) M)]
    · push Not at hξ
      rw [hPsupp ξ hξ, norm_zero]; exact hApos
  have hMd : ∀ ξ, ‖iteratedDeriv M P ξ‖ ≤ A * (l⁻¹) ^ M := by
    intro ξ
    obtain ⟨k, hk⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    rw [hk]
    have hPd : iteratedDeriv (k + 1) P ξ = c₂ *
        (((ξ - 0 : ℝ) : ℂ) * iteratedDeriv (k + 1) n ξ + ((k + 1 : ℕ) : ℂ) * iteratedDeriv k n ξ) := by
      rw [hPeq]
      have h3 : iteratedDeriv (k + 1) (fun η : ℝ => c₂ * (((η - 0 : ℝ) : ℂ) * n η)) ξ =
          c₂ * iteratedDeriv (k + 1) (fun η : ℝ => ((η - 0 : ℝ) : ℂ) * n η) ξ :=
        iteratedDeriv_const_mul_field c₂ (fun η : ℝ => ((η - 0 : ℝ) : ℂ) * n η)
      rw [h3, iteratedDeriv_sub_mul hsm 0 k]
    rw [hPd]
    by_cases hξ : |ξ - c| ≤ 𝔭.β * l / 2
    · have h1 := hη ξ hξ
      have hdk1 := hder (k + 1) (by omega) ξ
      have hdk := hder k (by omega) ξ
      have e1 : ‖iteratedDeriv (k + 1) n ξ‖ ≤ 𝔭.C * (l⁻¹) ^ (k + 1) := by
        rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]; linarith
      have e2 : ‖iteratedDeriv k n ξ‖ ≤ 𝔭.C * (l⁻¹) ^ k := by
        rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]; linarith
      rw [norm_mul, hc₂n]
      have hsum : ‖((ξ - 0 : ℝ) : ℂ) * iteratedDeriv (k + 1) n ξ + ((k + 1 : ℕ) : ℂ) * iteratedDeriv k n ξ‖ ≤
          ((C₀ + 𝔭.β / 2) * l) * (𝔭.C * (l⁻¹) ^ (k + 1)) + ((k + 1 : ℕ) : ℝ) * (𝔭.C * (l⁻¹) ^ k) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, sub_zero]
          gcongr
        · rw [norm_mul, Complex.norm_natCast]
          gcongr
      have hl1 : l * l⁻¹ = 1 := mul_inv_cancel₀ hl.ne'
      calc 2 * π * ‖((ξ - 0 : ℝ) : ℂ) * iteratedDeriv (k + 1) n ξ + ((k + 1 : ℕ) : ℂ) * iteratedDeriv k n ξ‖
          ≤ 2 * π * (((C₀ + 𝔭.β / 2) * l) * (𝔭.C * (l⁻¹) ^ (k + 1)) + ((k + 1 : ℕ) : ℝ) * (𝔭.C * (l⁻¹) ^ k)) := by
            gcongr
        _ = A * (l⁻¹) ^ (k + 1) := by
            have hMk : (M : ℝ) = k + 1 := by rw [hk]; push_cast; ring
            simp only [hA, hMk]
            push_cast
            have : (l⁻¹) ^ (k + 1) = (l⁻¹) ^ k * l⁻¹ := pow_succ _ _
            rw [this]
            field_simp
    · push Not at hξ
      have h1 : iteratedDeriv (k + 1) n ξ = 0 := iteratedDeriv_eq_zero_of_far hsupp (k + 1) hξ
      have h2 : iteratedDeriv k n ξ = 0 := iteratedDeriv_eq_zero_of_far hsupp k hξ
      rw [h1, h2]
      simp only [mul_zero, add_zero, norm_zero]
      positivity
  have hk := norm_fourierInv_le_pow (n := P) (c := c) (r := 𝔭.β * l / 2) (A := A) (l := l) M hr hl hPsm hPsupp h0 hMd w
  refine hk.trans (le_of_eq ?_)
  ring

end PrimeBHT.TimeFrequency.X2
