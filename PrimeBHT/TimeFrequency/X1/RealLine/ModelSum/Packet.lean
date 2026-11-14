module

public import PrimeBHT.TimeFrequency.X1.RealLine.Coefficients
public import PrimeBHT.Frozen.IsAdapted
public import PrimeBHT.Frozen.TimeInt
public import PrimeBHT.Frozen.FreqInt
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Scaled wave packets and their adaptedness (blueprint node R4 (d), packets)

`scaledPacket ρ s v ℓ (x) = 2^{-s/2} ψ_{v,ℓ}(2^{-s} x)` is the scale-`s` wave packet `ψ^{(s)}_{v,ℓ}`.

* `fourier_scaledPacket`: `𝓕 ψ^{(s)}_{v,ℓ}(ξ) = 2^{s/2} e(-v 2^s ξ) ρ̂(2^s ξ - ℓ/3)`, hence it vanishes
  outside `2^{-s}[ℓ/3 + 1/10, ℓ/3 + 9/10] ⊆ 2^{-s}[ℓ/3, ℓ/3 + 1)`.
* `exists_isAdapted_scaledPacket`: there is `C = C(ρ, N) > 0` such that every `κ • ψ^{(s)}_{v+m,n}` with
  `‖κ‖ ≤ C⁻¹ (1+|m|)^{-N}` is adapted, in the *frozen* sense `PrimeBHT.Statements.IsAdapted N I ω` (exponent
  `N`, constant exactly `1`), to `I = 2^s [v, v+1)` and `ω = 2^{-s} [n/3, n/3 + 1)`. The proof: the demodulated
  function `e^{-2πi c(ω) x} κ ψ^{(s)}_{v+m,n}(x)` is a unimodular constant times
  `κ 2^{-s/2} e^{-πi 2^{-s} x} ρ(2^{-s}x - v - m)` (`c(ω) = 2^{-s}(n/3 + 1/2)`), and Peetre's inequality
  `1 + |a| ≤ (1 + |a - b|)(1 + |b|)` moves the centre `v + m` to the centre `v + 1/2` of `I` at the price
  `(3/2)^N (1+|m|)^N`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform Real SchwartzMap ContDiff

namespace PrimeBHT.TimeFrequency.RealLine

/-- The `L²`-normalised dilation `G^{(σ)}(x) = σ^{-1/2} G(x/σ)`. -/
def dilPacket (σ : ℝ) (G : ℝ → ℂ) (x : ℝ) : ℂ := ((σ ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * G (σ⁻¹ * x)

/-- The scale-`s` wave packet `ψ^{(s)}_{v,ℓ}(x) = 2^{-s/2} ψ_{v,ℓ}(2^{-s} x)`. -/
def scaledPacket (ρ : ℝ → ℂ) (s v ℓ : ℤ) : ℝ → ℂ :=
  dilPacket ((2 : ℝ) ^ s) (wavePacket ρ v ℓ)

theorem scaledPacket_apply (ρ : ℝ → ℂ) (s v ℓ : ℤ) (x : ℝ) :
    scaledPacket ρ s v ℓ x =
      ((((2 : ℝ) ^ s) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * wavePacket ρ v ℓ (((2 : ℝ) ^ s)⁻¹ * x) := rfl

/-! ## Fourier transform of a dilation -/

theorem fourier_const_mul' (a : ℂ) (g : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun y => a * g y) ξ = a * 𝓕 g ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]; ring

theorem fourier_comp_mul_left (G : ℝ → ℂ) {a : ℝ} (ha : a ≠ 0) (ξ : ℝ) :
    𝓕 (fun x => G (a * x)) ξ = ((|a⁻¹| : ℝ) : ℂ) * 𝓕 G (a⁻¹ * ξ) := by
  rw [fourier_eq_integral_ePhase, fourier_eq_integral_ePhase]
  have h : ∀ x : ℝ, ePhase (-(x * ξ)) * G (a * x) =
      (fun y : ℝ => ePhase (-(y * (a⁻¹ * ξ))) * G y) (a * x) := by
    intro x
    simp only
    congr 3
    field_simp
  simp_rw [h]
  rw [Measure.integral_comp_mul_left (fun y : ℝ => ePhase (-(y * (a⁻¹ * ξ))) * G y) a,
    Complex.real_smul]

theorem fourier_dilPacket (σ : ℝ) (hσ : 0 < σ) (G : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (dilPacket σ G) ξ = ((σ ^ (-(1 : ℝ) / 2) * σ : ℝ) : ℂ) * 𝓕 G (σ * ξ) := by
  unfold dilPacket
  rw [fourier_const_mul', fourier_comp_mul_left G (inv_ne_zero hσ.ne') ξ, inv_inv,
    abs_of_pos hσ]
  push_cast
  ring

theorem fourier_scaledPacket (ρ : ℝ → ℂ) (s v ℓ : ℤ) (ξ : ℝ) :
    𝓕 (scaledPacket ρ s v ℓ) ξ =
      ((((2 : ℝ) ^ s) ^ (-(1 : ℝ) / 2) * (2 : ℝ) ^ s : ℝ) : ℂ) *
        (ePhase (-((v : ℝ) * ((2 : ℝ) ^ s * ξ))) * 𝓕 ρ ((2 : ℝ) ^ s * ξ - (ℓ : ℝ) / 3)) := by
  rw [scaledPacket, fourier_dilPacket _ (zpow_pos (by norm_num) s), fourier_wavePacket]

theorem fourier_scaledPacket_eq_zero {ρ : 𝓢(ℝ, ℂ)} (hρ : IsFrameWindow ρ) (s v ℓ : ℤ) {ξ : ℝ}
    (h : ξ ∉ Set.Ico ((2 : ℝ) ^ (-s) * ((ℓ : ℝ) / 3)) ((2 : ℝ) ^ (-s) * ((ℓ : ℝ) / 3 + 1))) :
    𝓕 (scaledPacket ρ s v ℓ) ξ = 0 := by
  rw [fourier_scaledPacket]
  have hσ : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) s
  have hm : (2 : ℝ) ^ s * ξ - (ℓ : ℝ) / 3 ∉ Set.Icc (1 / 10 : ℝ) (9 / 10) := by
    intro hI
    apply h
    obtain ⟨h1, h2⟩ := hI
    have e : (2 : ℝ) ^ (-s) = ((2 : ℝ) ^ s)⁻¹ := zpow_neg 2 s
    rw [e]
    have hi : 0 < ((2 : ℝ) ^ s)⁻¹ := inv_pos.2 hσ
    have hξ : ξ = ((2 : ℝ) ^ s)⁻¹ * ((2 : ℝ) ^ s * ξ) := by field_simp
    constructor
    · rw [hξ]
      exact mul_le_mul_of_nonneg_left (by linarith) hi.le
    · rw [hξ]
      exact mul_lt_mul_of_pos_left (by linarith) hi
  rw [hρ.1 _ hm]
  simp

/-! ## Regularity and integrability of scaled packets -/

theorem contDiff_ePhase : ContDiff ℝ ∞ ePhase := by
  unfold ePhase
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

theorem contDiff_scaledPacket (ρ : 𝓢(ℝ, ℂ)) (s v ℓ : ℤ) : ContDiff ℝ ∞ (scaledPacket ρ s v ℓ) := by
  have h1 : ContDiff ℝ ∞ (fun x : ℝ => ((2 : ℝ) ^ s)⁻¹ * x - (v : ℝ)) := by fun_prop
  have h2 : ContDiff ℝ ∞ (fun x : ℝ => ePhase ((ℓ : ℝ) * (((2 : ℝ) ^ s)⁻¹ * x - v) / 3)) :=
    contDiff_ePhase.comp (by fun_prop)
  have h3 : ContDiff ℝ ∞ (fun x : ℝ => ρ (((2 : ℝ) ^ s)⁻¹ * x - v)) := ρ.smooth ⊤ |>.comp h1
  have := h2.mul h3
  unfold scaledPacket dilPacket wavePacket
  simp only [sub_eq_add_neg] at *
  fun_prop

theorem integrable_scaledPacket (ρ : 𝓢(ℝ, ℂ)) (s v ℓ : ℤ) : Integrable (scaledPacket ρ s v ℓ) := by
  have hσ : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) s
  have h : Integrable (fun x : ℝ => wavePacket ρ v ℓ (((2 : ℝ) ^ s)⁻¹ * x)) :=
    (integrable_wavePacket ρ v ℓ).comp_mul_left' (inv_ne_zero hσ.ne')
  exact h.const_mul _

/-! ## Peetre's inequality and the decay bookkeeping -/

/-- Peetre's inequality `1 + |a| ≤ (1 + |a - b|)(1 + |b|)`. -/
theorem one_add_abs_le_mul (a b : ℝ) : 1 + |a| ≤ (1 + |a - b|) * (1 + |b|) := by
  have h : |a| ≤ |a - b| + |b| := by
    calc |a| = |(a - b) + b| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  nlinarith [abs_nonneg (a - b), abs_nonneg b, mul_nonneg (abs_nonneg (a - b)) (abs_nonneg b)]

/-- Moving the centre `v + m` of a packet to the centre `v + 1/2` of `[v, v+1)`: with `z = y - (v+m)`
and `a = y - (v + 1/2) = z + m - 1/2`, `1 + |a| ≤ (3/2)(1 + |m|)(1 + |z|)`. -/
theorem one_add_abs_le_shift (z m : ℝ) :
    1 + |z + m - 1 / 2| ≤ (3 / 2) * (1 + |m|) * (1 + |z|) := by
  have h1 := one_add_abs_le_mul (z + m - 1 / 2) (m - 1 / 2)
  have h2 : z + m - 1 / 2 - (m - 1 / 2) = z := by ring
  rw [h2] at h1
  have h3 : 1 + |m - 1 / 2| ≤ (3 / 2) * (1 + |m|) := by
    have : |m - 1 / 2| ≤ |m| + 1 / 2 := by
      calc |m - 1 / 2| ≤ |m| + |(1 / 2 : ℝ)| := abs_sub _ _
        _ = |m| + 1 / 2 := by norm_num
    nlinarith [abs_nonneg m]
  calc 1 + |z + m - 1 / 2| ≤ (1 + |z|) * (1 + |m - 1 / 2|) := h1
    _ ≤ (1 + |z|) * ((3 / 2) * (1 + |m|)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (3 / 2) * (1 + |m|) * (1 + |z|) := by ring

theorem rpow_neg_nat_le {N : ℕ} {X Y c : ℝ} (hX : 0 < X) (hY : 0 < Y) (hc : 0 < c) (h : Y ≤ c * X) :
    X ^ (-(N : ℝ)) ≤ c ^ N * Y ^ (-(N : ℝ)) := by
  have h1 := rpow_neg_anti (s := (N : ℝ)) hY h (Nat.cast_nonneg N)
  rw [Real.mul_rpow hc.le hX.le] at h1
  calc X ^ (-(N : ℝ)) = c ^ (N : ℝ) * (c ^ (-(N : ℝ)) * X ^ (-(N : ℝ))) := by
        rw [← mul_assoc, ← Real.rpow_add hc]; simp
    _ ≤ c ^ (N : ℝ) * Y ^ (-(N : ℝ)) := by gcongr
    _ = c ^ N * Y ^ (-(N : ℝ)) := by rw [Real.rpow_natCast]

/-- The scale-0 decay inequality behind the adaptedness of `κ ψ_{v+m,n}`. -/
theorem core_decay_bound {N : ℕ} {A : ℝ} (hA : 0 < A) {κ : ℂ} {m z : ℝ}
    (hκ : ‖κ‖ ≤ ((3 / 2 : ℝ) ^ N * ((π + 1) * A))⁻¹ * (1 + |m|) ^ (-(N : ℝ))) :
    ‖κ‖ * ((π + 1) * A * wt N z) ≤ wt N (z + m - 1 / 2) := by
  have hX : 0 < 1 + |z| := by positivity
  have hY : 0 < 1 + |z + m - 1 / 2| := by positivity
  have hm : 0 < 1 + |m| := by positivity
  have hc : 0 < (3 / 2) * (1 + |m|) := by positivity
  have h1 := rpow_neg_nat_le (N := N) hX hY hc (one_add_abs_le_shift z m)
  have hπ : 0 < π + 1 := by positivity
  have hC : 0 < (3 / 2 : ℝ) ^ N * ((π + 1) * A) := by positivity
  unfold wt
  calc ‖κ‖ * ((π + 1) * A * (1 + |z|) ^ (-(N : ℝ)))
      ≤ (((3 / 2 : ℝ) ^ N * ((π + 1) * A))⁻¹ * (1 + |m|) ^ (-(N : ℝ))) *
          ((π + 1) * A * (((3 / 2) * (1 + |m|)) ^ N * (1 + |z + m - 1 / 2|) ^ (-(N : ℝ)))) := by
        gcongr
    _ = (1 + |z + m - 1 / 2|) ^ (-(N : ℝ)) * ((1 + |m|) ^ (-(N : ℝ)) * (1 + |m|) ^ N) *
          (((3 / 2 : ℝ) ^ N * ((π + 1) * A))⁻¹ * ((3 / 2 : ℝ) ^ N * ((π + 1) * A))) := by
        rw [mul_pow]; ring
    _ = (1 + |z + m - 1 / 2|) ^ (-(N : ℝ)) := by
        have e1 : (1 + |m|) ^ (-(N : ℝ)) * (1 + |m|) ^ N = 1 := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hm]; simp
        rw [e1, inv_mul_cancel₀ hC.ne']; ring

/-! ## The demodulated packet -/

theorem centre_Ico {a b : ℝ} (h : a < b) :
    PrimeBHT.Statements.intervalCentre (Set.Ico a b) = (a + b) / 2 := by
  unfold PrimeBHT.Statements.intervalCentre
  rw [csInf_Ico h, csSup_Ico h]

theorem toReal_volume_Ico_scale (s v : ℤ) :
    (volume (Set.Ico ((2 : ℝ) ^ s * (v : ℝ)) ((2 : ℝ) ^ s * ((v : ℝ) + 1)))).toReal = (2 : ℝ) ^ s := by
  have h : (2 : ℝ) ^ s * ((v : ℝ) + 1) - (2 : ℝ) ^ s * (v : ℝ) = (2 : ℝ) ^ s := by ring
  rw [Real.volume_Ico, h, ENNReal.toReal_ofReal (zpow_pos (by norm_num) s).le]

theorem exp_neg_eq_ePhase (c y : ℝ) :
    Complex.exp (-(2 * (π : ℂ) * Complex.I * (c : ℂ) * (y : ℂ))) = ePhase (-(c * y)) := by
  unfold ePhase
  congr 1
  push_cast
  ring

/-- **The demodulated packet.** With `c(ω) = σ⁻¹ (n/3 + 1/2)`, `σ = 2^s`:
`e^{-2πi c(ω) y} κ ψ^{(s)}_{v',n}(y) = (κ σ^{-1/2} e(-n v'/3)) · e(-σ⁻¹ y / 2) ρ(σ⁻¹ y - v')`. -/
theorem demod_scaledPacket (ρ : ℝ → ℂ) (s : ℤ) (v' : ℤ) (n : ℤ) (κ : ℂ) (y : ℝ) :
    Complex.exp (-(2 * (π : ℂ) * Complex.I *
        ((((2 : ℝ) ^ s)⁻¹ * ((n : ℝ) / 3) + ((2 : ℝ) ^ s)⁻¹ * ((n : ℝ) / 3 + 1)) / 2 : ℝ) *
          (y : ℂ))) * (κ * scaledPacket ρ s v' n y) =
      (κ * ((((2 : ℝ) ^ s) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * ePhase (-((n : ℝ) * (v' : ℝ) / 3))) *
        (ePhase (-(((2 : ℝ) ^ s)⁻¹ * y / 2)) * ρ (((2 : ℝ) ^ s)⁻¹ * y - (v' : ℝ))) := by
  rw [exp_neg_eq_ePhase, scaledPacket_apply]
  unfold wavePacket
  have e : ePhase (-((((2 : ℝ) ^ s)⁻¹ * ((n : ℝ) / 3) + ((2 : ℝ) ^ s)⁻¹ * ((n : ℝ) / 3 + 1)) / 2 * y)) *
      ePhase ((n : ℝ) * (((2 : ℝ) ^ s)⁻¹ * y - (v' : ℝ)) / 3) =
      ePhase (-((n : ℝ) * (v' : ℝ) / 3)) * ePhase (-(((2 : ℝ) ^ s)⁻¹ * y / 2)) := by
    rw [← ePhase_add, ← ePhase_add]
    congr 1
    ring
  calc _ = (ePhase (-((((2 : ℝ) ^ s)⁻¹ * ((n : ℝ) / 3) + ((2 : ℝ) ^ s)⁻¹ * ((n : ℝ) / 3 + 1)) / 2 * y)) *
      ePhase ((n : ℝ) * (((2 : ℝ) ^ s)⁻¹ * y - (v' : ℝ)) / 3)) *
        (κ * ((((2 : ℝ) ^ s) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * ρ (((2 : ℝ) ^ s)⁻¹ * y - (v' : ℝ))) := by ring
    _ = _ := by rw [e]; ring

theorem hasDerivAt_ePhase_mul (c y : ℝ) :
    HasDerivAt (fun y : ℝ => ePhase (c * y)) (ePhase (c * y) * (2 * (π : ℂ) * Complex.I * (c : ℂ))) y := by
  have h1 : HasDerivAt (fun y : ℝ => ((c * y : ℝ) : ℂ)) (c : ℂ) y := by
    have := ((hasDerivAt_id y).const_mul c).ofReal_comp
    simpa using this
  have h2 := (h1.const_mul (2 * (π : ℂ) * Complex.I)).cexp
  unfold ePhase
  exact h2

theorem hasDerivAt_demodCore (ρ : 𝓢(ℝ, ℂ)) (σ v' y : ℝ) :
    HasDerivAt (fun y : ℝ => ePhase (-(σ⁻¹ * y / 2)) * ρ (σ⁻¹ * y - v'))
      (ePhase (-(σ⁻¹ * y / 2)) * (-((π : ℂ) * Complex.I * ((σ⁻¹ : ℝ) : ℂ))) * ρ (σ⁻¹ * y - v') +
        ePhase (-(σ⁻¹ * y / 2)) * (((σ⁻¹ : ℝ) : ℂ) * deriv ρ (σ⁻¹ * y - v'))) y := by
  have e : (fun y : ℝ => ePhase (-(σ⁻¹ * y / 2)) * ρ (σ⁻¹ * y - v')) =
      (fun y : ℝ => ePhase (-(σ⁻¹ / 2) * y)) * (fun y : ℝ => ρ (σ⁻¹ * y - v')) := by
    funext y
    simp only [Pi.mul_apply]
    congr 2
    ring
  have h1 := hasDerivAt_ePhase_mul (-(σ⁻¹ / 2)) y
  have h2 : HasDerivAt (fun y : ℝ => σ⁻¹ * y - v') σ⁻¹ y := by
    have := ((hasDerivAt_id y).const_mul σ⁻¹).sub_const v'
    simpa using this
  have h3 : HasDerivAt (fun y : ℝ => ρ (σ⁻¹ * y - v')) (σ⁻¹ • deriv ρ (σ⁻¹ * y - v')) y :=
    (SchwartzMap.hasDerivAt ρ (σ⁻¹ * y - v')).scomp y h2
  have h4 := h1.mul h3
  rw [e]
  convert h4 using 1
  simp only [Complex.real_smul]
  have : (-(σ⁻¹ * y / 2)) = -(σ⁻¹ / 2) * y := by ring
  rw [this]
  push_cast
  ring

/-! ## Adaptedness (frozen `IsAdapted`, constant exactly `1`) -/

theorem norm_demod_mul (κ : ℂ) (δ : ℝ) (hδ : 0 ≤ δ) (θ θ' : ℝ) (r : ℂ) :
    ‖κ * (δ : ℂ) * ePhase θ * (ePhase θ' * r)‖ = ‖κ‖ * δ * ‖r‖ := by
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_ePhase, norm_ePhase, Complex.norm_real,
    Real.norm_of_nonneg hδ]
  ring

/-- **Adaptedness of scaled packets, in the frozen sense.** There is `C = C(ρ, N) > 0` such that every
`κ ψ^{(s)}_{v+m,n}` with `‖κ‖ ≤ C⁻¹ (1+|m|)^{-N}` is `PrimeBHT.Statements.IsAdapted N I ω` for
`I = 2^s [v, v+1)` (`timeInt` of the tile `(s, v, ·)`) and `ω = 2^{-s} [n/3, n/3 + 1)` (`freqInt`). -/
theorem exists_isAdapted_scaledPacket {ρ : 𝓢(ℝ, ℂ)} (hρ : IsFrameWindow ρ) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s v m n : ℤ) (κ : ℂ), ‖κ‖ ≤ C⁻¹ * (1 + |(m : ℝ)|) ^ (-(N : ℝ)) →
      PrimeBHT.Statements.IsAdapted N
        (Set.Ico ((2 : ℝ) ^ s * (v : ℝ)) ((2 : ℝ) ^ s * ((v : ℝ) + 1)))
        (Set.Ico ((2 : ℝ) ^ (-s) * ((n : ℝ) / 3)) ((2 : ℝ) ^ (-s) * ((n : ℝ) / 3 + 1)))
        (fun x => κ * scaledPacket ρ s (v + m) n x) := by
  obtain ⟨A₁, hA₁0, hA₁⟩ := exists_schwartz_decay ρ (N : ℝ)
  obtain ⟨A₂, hA₂0, hA₂⟩ := exists_schwartz_decay (SchwartzMap.derivCLM ℝ ℂ ρ) (N : ℝ)
  set A : ℝ := max (max A₁ A₂) 1 with hAdef
  have hA : 0 < A := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hA1le : A₁ ≤ A := (le_max_left A₁ A₂).trans (le_max_left _ 1)
  have hA2le : A₂ ≤ A := (le_max_right A₁ A₂).trans (le_max_left _ 1)
  have hρA : ∀ z, ‖ρ z‖ ≤ A * wt N z := fun z =>
    (hA₁ z).trans (mul_le_mul_of_nonneg_right hA1le (wt_nonneg _ _))
  have hρ'A : ∀ z, ‖deriv ρ z‖ ≤ A * wt N z := fun z => by
    have h := (hA₂ z).trans (mul_le_mul_of_nonneg_right hA2le (wt_nonneg (N : ℝ) z))
    simpa using h
  refine ⟨(3 / 2 : ℝ) ^ N * ((π + 1) * A), by positivity, ?_⟩
  intro s v m n κ hκ
  have hσ : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) s
  have hneg : (2 : ℝ) ^ (-s) = ((2 : ℝ) ^ s)⁻¹ := zpow_neg 2 s
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (contDiff_const.mul (contDiff_scaledPacket ρ s (v + m) n)).of_le (by exact_mod_cast le_top)
  · exact (integrable_scaledPacket ρ s (v + m) n).const_mul κ
  · intro ξ hξ
    rw [fourier_const_mul', fourier_scaledPacket_eq_zero hρ s (v + m) n hξ, mul_zero]
  · intro k hk x
    beta_reduce
    have hlt : (2 : ℝ) ^ (-s) * ((n : ℝ) / 3) < (2 : ℝ) ^ (-s) * ((n : ℝ) / 3 + 1) :=
      mul_lt_mul_of_pos_left (by linarith) (zpow_pos (by norm_num) _)
    have hlt' : (2 : ℝ) ^ s * (v : ℝ) < (2 : ℝ) ^ s * ((v : ℝ) + 1) :=
      mul_lt_mul_of_pos_left (by linarith) hσ
    set σ : ℝ := (2 : ℝ) ^ s with hσdef
    set δ : ℝ := σ ^ (-(1 : ℝ) / 2) with hδdef
    have hδ : 0 ≤ δ := Real.rpow_nonneg hσ.le _
    set K0 : ℂ := κ * (δ : ℂ) * ePhase (-((n : ℝ) * ((v + m : ℤ) : ℝ) / 3)) with hK0
    have hfun : (fun y : ℝ => Complex.exp (-(2 * (π : ℂ) * Complex.I *
        (PrimeBHT.Statements.intervalCentre (Set.Ico ((2 : ℝ) ^ (-s) * ((n : ℝ) / 3))
          ((2 : ℝ) ^ (-s) * ((n : ℝ) / 3 + 1))) : ℂ) * (y : ℂ))) * (κ * scaledPacket ρ s (v + m) n y)) =
        fun y => K0 * (ePhase (-(σ⁻¹ * y / 2)) * ρ (σ⁻¹ * y - ((v + m : ℤ) : ℝ))) := by
      funext y
      rw [centre_Ico hlt, hneg]
      exact demod_scaledPacket ρ s (v + m) n κ y
    have hκ' : ‖κ‖ ≤ ((3 / 2 : ℝ) ^ N * ((π + 1) * A))⁻¹ * (1 + |(m : ℝ)|) ^ (-(N : ℝ)) := hκ
    have hcore := core_decay_bound hA hκ' (m := (m : ℝ)) (z := σ⁻¹ * x - ((v + m : ℤ) : ℝ))
    have hz : σ⁻¹ * x - ((v + m : ℤ) : ℝ) + (m : ℝ) - 1 / 2 =
        σ⁻¹ * x - ((v : ℝ) + 1 / 2) := by push_cast; ring
    rw [hz] at hcore
    have hcentre : x - (σ * (v : ℝ) + σ * ((v : ℝ) + 1)) / 2 = σ * (σ⁻¹ * x - ((v : ℝ) + 1 / 2)) := by
      field_simp
      ring
    have habs : |x - (σ * (v : ℝ) + σ * ((v : ℝ) + 1)) / 2| / σ = |σ⁻¹ * x - ((v : ℝ) + 1 / 2)| := by
      rw [hcentre, abs_mul, abs_of_pos hσ, mul_div_cancel_left₀ _ hσ.ne']
    have hwt : (1 + |x - PrimeBHT.Statements.intervalCentre (Set.Ico (σ * (v : ℝ)) (σ * ((v : ℝ) + 1)))| /
        (volume (Set.Ico (σ * (v : ℝ)) (σ * ((v : ℝ) + 1)))).toReal) ^ (-(N : ℝ)) =
        wt N (σ⁻¹ * x - ((v : ℝ) + 1 / 2)) := by
      rw [centre_Ico hlt', toReal_volume_Ico_scale, ← hσdef, habs]
      rfl
    rw [hwt, toReal_volume_Ico_scale, ← hσdef]
    have hπ : 0 < π + 1 := by positivity
    have hwz : 0 ≤ wt N (σ⁻¹ * x - ((v + m : ℤ) : ℝ)) := wt_nonneg _ _
    interval_cases k
    · have hfx := congrFun hfun x
      beta_reduce at hfx
      rw [iteratedDeriv_zero, hfx, hK0, norm_demod_mul κ δ hδ]
      have h0 : σ ^ (-((0 : ℕ) : ℝ) - 1 / 2) = δ := by
        rw [hδdef]; congr 1; norm_num
      rw [h0]
      calc ‖κ‖ * δ * ‖ρ (σ⁻¹ * x - ((v + m : ℤ) : ℝ))‖
          ≤ δ * (‖κ‖ * ((π + 1) * A * wt N (σ⁻¹ * x - ((v + m : ℤ) : ℝ)))) := by
            have h1 := hρA (σ⁻¹ * x - ((v + m : ℤ) : ℝ))
            have h2 : A * wt N (σ⁻¹ * x - ((v + m : ℤ) : ℝ)) ≤
                (π + 1) * A * wt N (σ⁻¹ * x - ((v + m : ℤ) : ℝ)) := by
              have := mul_nonneg hA.le hwz
              nlinarith [Real.pi_pos]
            have hk0 := norm_nonneg κ
            nlinarith [mul_nonneg hk0 hδ]
        _ ≤ δ * wt N (σ⁻¹ * x - ((v : ℝ) + 1 / 2)) := by gcongr
    · have hD := (hasDerivAt_demodCore ρ σ ((v + m : ℤ) : ℝ) x).const_mul K0
      rw [iteratedDeriv_one, hfun, hD.deriv]
      have hσi : 0 < σ⁻¹ := inv_pos.2 hσ
      have hr : K0 * (ePhase (-(σ⁻¹ * x / 2)) * (-((π : ℂ) * Complex.I * ((σ⁻¹ : ℝ) : ℂ))) *
            ρ (σ⁻¹ * x - ((v + m : ℤ) : ℝ)) +
          ePhase (-(σ⁻¹ * x / 2)) * (((σ⁻¹ : ℝ) : ℂ) * deriv ρ (σ⁻¹ * x - ((v + m : ℤ) : ℝ)))) =
          κ * (δ : ℂ) * ePhase (-((n : ℝ) * ((v + m : ℤ) : ℝ) / 3)) *
            (ePhase (-(σ⁻¹ * x / 2)) * (-((π : ℂ) * Complex.I * ((σ⁻¹ : ℝ) : ℂ)) *
              ρ (σ⁻¹ * x - ((v + m : ℤ) : ℝ)) +
              ((σ⁻¹ : ℝ) : ℂ) * deriv ρ (σ⁻¹ * x - ((v + m : ℤ) : ℝ)))) := by
        rw [hK0]; ring
      rw [hr, norm_demod_mul κ δ hδ]
      have hr_norm : ‖-((π : ℂ) * Complex.I * ((σ⁻¹ : ℝ) : ℂ)) * ρ (σ⁻¹ * x - ((v + m : ℤ) : ℝ)) +
          ((σ⁻¹ : ℝ) : ℂ) * deriv ρ (σ⁻¹ * x - ((v + m : ℤ) : ℝ))‖ ≤
          σ⁻¹ * ((π + 1) * A * wt N (σ⁻¹ * x - ((v + m : ℤ) : ℝ))) := by
        have h1 := hρA (σ⁻¹ * x - ((v + m : ℤ) : ℝ))
        have h2 := hρ'A (σ⁻¹ * x - ((v + m : ℤ) : ℝ))
        calc _ ≤ ‖-((π : ℂ) * Complex.I * ((σ⁻¹ : ℝ) : ℂ)) * ρ (σ⁻¹ * x - ((v + m : ℤ) : ℝ))‖ +
              ‖((σ⁻¹ : ℝ) : ℂ) * deriv ρ (σ⁻¹ * x - ((v + m : ℤ) : ℝ))‖ := norm_add_le _ _
          _ = σ⁻¹ * (π * ‖ρ (σ⁻¹ * x - ((v + m : ℤ) : ℝ))‖ +
                ‖deriv ρ (σ⁻¹ * x - ((v + m : ℤ) : ℝ))‖) := by
              simp only [norm_mul, norm_neg, Complex.norm_I, Complex.norm_real,
                Real.norm_of_nonneg hσi.le, Real.norm_of_nonneg Real.pi_pos.le]
              ring
          _ ≤ σ⁻¹ * (π * (A * wt N (σ⁻¹ * x - ((v + m : ℤ) : ℝ))) +
                A * wt N (σ⁻¹ * x - ((v + m : ℤ) : ℝ))) := by gcongr
          _ = _ := by ring
      have h1 : σ ^ (-((1 : ℕ) : ℝ) - 1 / 2) = δ * σ⁻¹ := by
        rw [hδdef, ← Real.rpow_neg_one, ← Real.rpow_add hσ]
        congr 1; push_cast; ring
      rw [h1]
      calc ‖κ‖ * δ * ‖-((π : ℂ) * Complex.I * ((σ⁻¹ : ℝ) : ℂ)) * ρ (σ⁻¹ * x - ((v + m : ℤ) : ℝ)) +
            ((σ⁻¹ : ℝ) : ℂ) * deriv ρ (σ⁻¹ * x - ((v + m : ℤ) : ℝ))‖
          ≤ ‖κ‖ * δ * (σ⁻¹ * ((π + 1) * A * wt N (σ⁻¹ * x - ((v + m : ℤ) : ℝ)))) := by
            gcongr
        _ = (δ * σ⁻¹) * (‖κ‖ * ((π + 1) * A * wt N (σ⁻¹ * x - ((v + m : ℤ) : ℝ)))) := by ring
        _ ≤ (δ * σ⁻¹) * wt N (σ⁻¹ * x - ((v : ℝ) + 1 / 2)) := by gcongr

end PrimeBHT.TimeFrequency.RealLine

end
