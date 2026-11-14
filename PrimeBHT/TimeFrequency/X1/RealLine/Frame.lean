module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Real-line wave-packet frame (blueprint node R4, parts (setup) and (a); `docs/x1-blueprint.md`)

Conventions. `𝓕` is Mathlib's Fourier transform `𝓕 f ξ = ∫ e(-xξ) f x dx` (BD26 L500), `e t = exp(2πit)`
is `ePhase`. The pairing is `pairing f φ = ∫ f conj φ` (the convention of `drafts/M1Statement.lean.txt`,
which is also the one for which `f̂` has `⟨f, ψ_{v,ℓ}⟩ = ∫ conj(ρ̂(η-ℓ/3)) f̂(η) e^{2πivη} dη`).

* `IsFrameWindow ρ`: `ρ` Schwartz, `ρ̂` supported in `[0.1, 0.9]`, `∑_ℓ |ρ̂(ξ - ℓ/3)|² = 1` for all `ξ`.
* `wavePacket ρ v ℓ x = e^{2πiℓ(x-v)/3} ρ(x-v)` (`ψ_{v,ℓ}`); `fourier_wavePacket`:
  `ψ̂_{v,ℓ}(ξ) = e(-vξ) ρ̂(ξ - ℓ/3)`.
* `pairing_wavePacket`: `⟨f, ψ_{v,ℓ}⟩ = ∫ conj(ρ̂(η - ℓ/3)) f̂(η) e(vη) dη` (Parseval, for Schwartz `f`).
* **(a)** `hasSum_frame`: for Schwartz `f` and every `x`, the family
  `(v, ℓ) ↦ ⟨f, ψ_{v,ℓ}⟩ ψ_{v,ℓ}(x)` on `ℤ × ℤ` has sum `f x` (`HasSum`, i.e. unconditional), and
  `summable_norm_frame` says it is absolutely summable.
* `exists_isFrameWindow`: a frame window exists (`ρ̂ = ϑ / (∑_ℓ ϑ(· - ℓ/3)²)^{1/2}` for a smooth bump `ϑ`).
* A more general Fourier-side statement `hasSum_frame_of_fourier`: for `Ĝ` continuous with
  absolutely summable Fourier-side coefficients `coeffF ρ Ĝ v ℓ`, `∫ Ĝ(ξ) e(ξx) dξ = ∑ coeffF ψ_{v,ℓ}(x)`.
  It is used in `Coefficients.lean` for `B_1(ψ, ψ_{v₁ℓ₁}, ψ_{v₂ℓ₂})`, which is not (known to be) Schwartz.

Proof route: Poisson summation (`Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`) for the
compactly supported `η ↦ conj ρ̂(η-ℓ/3) Ĝ(η)`, the identity `Ĝ = ∑_ℓ |ρ̂(·-ℓ/3)|² Ĝ`, termwise Fourier
inversion (`hasSum_integral_of_summable_integral_norm`), and for Schwartz `f` the quadratic decay of
the Fourier coefficients (`Real.one_add_sq_mul_norm_fourier_le`) uniformly in `ℓ`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform Real SchwartzMap ContDiff

namespace PrimeBHT.TimeFrequency.RealLine

/-- `ePhase t = e^{2πit}`. -/
def ePhase (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))

theorem ePhase_add (s t : ℝ) : ePhase (s + t) = ePhase s * ePhase t := by
  unfold ePhase; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem norm_ePhase (t : ℝ) : ‖ePhase t‖ = 1 := by
  unfold ePhase
  rw [Complex.norm_exp]
  simp

theorem conj_ePhase (t : ℝ) : (starRingEnd ℂ) (ePhase t) = ePhase (-t) := by
  unfold ePhase
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul, map_ofNat]

theorem continuous_ePhase : Continuous ePhase := by
  unfold ePhase; fun_prop

theorem ePhase_eq_coe_fourierChar (t : ℝ) : ePhase t = ((Real.fourierChar t : Circle) : ℂ) := by
  rw [Real.fourierChar_apply]
  unfold ePhase
  congr 1
  push_cast
  ring

theorem fourier_eq_integral_ePhase (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 f ξ = ∫ x : ℝ, ePhase (-(x * ξ)) * f x := by
  rw [Real.fourier_real_eq]
  simp only [Circle.smul_def, ePhase_eq_coe_fourierChar, smul_eq_mul]

theorem fourierInv_eq_integral_ePhase (f : ℝ → ℂ) (t : ℝ) :
    𝓕⁻ f t = ∫ ξ : ℝ, ePhase (ξ * t) * f ξ := by
  rw [Real.fourierInv_eq]
  simp only [Circle.smul_def, ePhase_eq_coe_fourierChar, RCLike.inner_apply, conj_trivial,
    smul_eq_mul]
  congr 1
  ext ξ
  rw [mul_comm t ξ]


/-! ## Wave packets -/

/-- The wave packet `ψ_{v,ℓ}(x) = e^{2πiℓ(x-v)/3} ρ(x-v)` (BD26 L977-990). -/
def wavePacket (ρ : ℝ → ℂ) (v ℓ : ℤ) (x : ℝ) : ℂ :=
  ePhase ((ℓ : ℝ) * (x - v) / 3) * ρ (x - v)

/-- The pairing `⟨h, φ⟩ = ∫ h conj φ` (same convention as the M1 draft). -/
def pairing (h φ : ℝ → ℂ) : ℂ := ∫ x, h x * (starRingEnd ℂ) (φ x)

/-- `ρ` is a *frame window*: Schwartz with `ρ̂` supported in `[0.1, 0.9]` and
`∑_ℓ |ρ̂(ξ - ℓ/3)|² = 1` for all `ξ`. -/
def IsFrameWindow (ρ : 𝓢(ℝ, ℂ)) : Prop :=
  (∀ ξ : ℝ, ξ ∉ Set.Icc (1 / 10 : ℝ) (9 / 10) → 𝓕 (ρ : ℝ → ℂ) ξ = 0) ∧
  ∀ ξ : ℝ, HasSum (fun ℓ : ℤ => ‖𝓕 (ρ : ℝ → ℂ) (ξ - (ℓ : ℝ) / 3)‖ ^ 2) 1

theorem fourier_wavePacket (ρ : ℝ → ℂ) (v ℓ : ℤ) (ξ : ℝ) :
    𝓕 (wavePacket ρ v ℓ) ξ = ePhase (-((v : ℝ) * ξ)) * 𝓕 ρ (ξ - (ℓ : ℝ) / 3) := by
  rw [fourier_eq_integral_ePhase, fourier_eq_integral_ePhase, ← integral_const_mul,
    ← integral_add_right_eq_self _ (v : ℝ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [wavePacket, add_sub_cancel_right]
  have h : ePhase (-((x + v) * ξ)) * ePhase ((ℓ : ℝ) * x / 3) =
      ePhase (-((v : ℝ) * ξ)) * ePhase (-(x * (ξ - (ℓ : ℝ) / 3))) := by
    rw [← ePhase_add, ← ePhase_add]; congr 1; ring
  calc ePhase (-((x + v) * ξ)) * (ePhase ((ℓ : ℝ) * x / 3) * ρ x)
      = (ePhase (-((x + v) * ξ)) * ePhase ((ℓ : ℝ) * x / 3)) * ρ x := by ring
    _ = _ := by rw [h]; ring

/-- Parseval-type identity: for `Ĝ, φ` continuous and integrable, `g := 𝓕⁻ Ĝ`,
`∫ g conj φ = ∫ Ĝ conj φ̂`. -/
theorem integral_fourierInv_mul_conj {G φ : ℝ → ℂ} (hG : Continuous G) (hGi : Integrable G)
    (hφ : Continuous φ) (hφi : Integrable φ) :
    ∫ x, (∫ ξ, ePhase (ξ * x) * G ξ) * (starRingEnd ℂ) (φ x) =
      ∫ ξ, G ξ * (starRingEnd ℂ) (𝓕 φ ξ) := by
  have h1 : ∀ x, (∫ ξ, ePhase (ξ * x) * G ξ) * (starRingEnd ℂ) (φ x) =
      ∫ ξ, ePhase (ξ * x) * G ξ * (starRingEnd ℂ) (φ x) := fun x => by
    rw [integral_mul_const]
  have h2 : ∀ ξ, G ξ * (starRingEnd ℂ) (𝓕 φ ξ) =
      ∫ x, ePhase (ξ * x) * G ξ * (starRingEnd ℂ) (φ x) := fun ξ => by
    rw [fourier_eq_integral_ePhase, ← integral_conj, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [map_mul, conj_ePhase, neg_neg]
    rw [mul_comm x ξ]; ring
  simp_rw [h1, h2]
  refine integral_integral_swap (f := fun x ξ => ePhase (ξ * x) * G ξ * (starRingEnd ℂ) (φ x)) ?_
  have hint : Integrable (fun z : ℝ × ℝ => (fun x => ‖φ x‖) z.1 * (fun ξ => ‖G ξ‖) z.2)
      (volume.prod volume) := hφi.norm.mul_prod hGi.norm
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · have : Continuous (Function.uncurry fun (x ξ : ℝ) => ePhase (ξ * x) * G ξ * (starRingEnd ℂ) (φ x)) := by
      have := continuous_ePhase
      fun_prop
    exact this.aestronglyMeasurable
  · simp only [Function.uncurry, norm_mul, norm_ePhase, one_mul, Complex.norm_conj]
    rw [mul_comm]


/-! ## The Fourier-side coefficients and the Poisson step -/

/-- The Fourier-side coefficient `∫ conj(ρ̂(η - ℓ/3)) Ĝ(η) e(vη) dη`. -/
def coeffF (ρ : ℝ → ℂ) (G : ℝ → ℂ) (v ℓ : ℤ) : ℂ :=
  ∫ η, (starRingEnd ℂ) (𝓕 ρ (η - (ℓ : ℝ) / 3)) * G η * ePhase ((v : ℝ) * η)

theorem fourier_coe_one (n : ℤ) (ξ : ℝ) : fourier n (ξ : UnitAddCircle) = ePhase (n * ξ) := by
  rw [fourier_coe_apply]
  unfold ePhase
  congr 1
  push_cast
  ring

/-- Poisson summation step for a continuous compactly supported function with summable Fourier
transform on `ℤ`. -/
theorem hasSum_poisson_step {Gl : ℝ → ℂ} (hc : Continuous Gl) (hcs : HasCompactSupport Gl)
    (hs : Summable (fun n : ℤ => 𝓕 Gl n)) (ξ : ℝ) :
    HasSum (fun n : ℤ => 𝓕 Gl n * ePhase (n * ξ)) (∑' n : ℤ, Gl (ξ + n)) := by
  have hev : Gl =ᶠ[Filter.cocompact ℝ] 0 := by
    have := hasCompactSupport_iff_eventuallyEq.1 hcs
    rwa [Filter.coclosedCompact_eq_cocompact] at this
  have hO : Gl =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) :=
    (Asymptotics.isBigO_zero _ _).congr' hev.symm Filter.EventuallyEq.rfl
  have h := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hc (b := 2) one_lt_two hO hs ξ
  simp_rw [fourier_coe_one] at h
  rw [h]
  refine Summable.hasSum ?_
  refine hs.norm.of_norm_bounded fun n => ?_
  rw [norm_mul, norm_ePhase, mul_one]


theorem exists_norm_le (g : 𝓢(ℝ, ℂ)) : ∃ R : ℝ, 0 ≤ R ∧ ∀ t, ‖g t‖ ≤ R :=
  ⟨SchwartzMap.seminorm ℝ 0 0 g, apply_nonneg _ _, SchwartzMap.norm_le_seminorm ℝ g⟩

theorem fourier_coe' (ρ : 𝓢(ℝ, ℂ)) : ⇑(𝓕 ρ : 𝓢(ℝ, ℂ)) = 𝓕 (ρ : ℝ → ℂ) := SchwartzMap.fourier_coe ρ

theorem continuous_fourier_rho (ρ : 𝓢(ℝ, ℂ)) : Continuous (𝓕 (ρ : ℝ → ℂ)) := by
  rw [← fourier_coe']; exact (𝓕 ρ : 𝓢(ℝ, ℂ)).continuous

theorem integrable_fourier_rho (ρ : 𝓢(ℝ, ℂ)) : Integrable (𝓕 (ρ : ℝ → ℂ)) := by
  rw [← fourier_coe']; exact (𝓕 ρ : 𝓢(ℝ, ℂ)).integrable

theorem exists_norm_fourier_le (ρ : 𝓢(ℝ, ℂ)) : ∃ R : ℝ, 0 ≤ R ∧ ∀ t, ‖𝓕 (ρ : ℝ → ℂ) t‖ ≤ R := by
  rw [← fourier_coe']; exact exists_norm_le _

/-- On the support of the window, only the term `n = 0` of the periodization survives. -/
theorem rho_hat_mul_tsum (ρ : 𝓢(ℝ, ℂ)) (hρ : IsFrameWindow ρ) (G : ℝ → ℂ) (ℓ : ℤ) (ξ : ℝ) :
    𝓕 (ρ : ℝ → ℂ) (ξ - (ℓ : ℝ) / 3) *
        ∑' n : ℤ, (starRingEnd ℂ) (𝓕 (ρ : ℝ → ℂ) (ξ + n - (ℓ : ℝ) / 3)) * G (ξ + n) =
      ((‖𝓕 (ρ : ℝ → ℂ) (ξ - (ℓ : ℝ) / 3)‖ ^ 2 : ℝ) : ℂ) * G ξ := by
  by_cases h : ξ - (ℓ : ℝ) / 3 ∈ Set.Icc (1 / 10 : ℝ) (9 / 10)
  · rw [tsum_eq_single 0]
    · simp only [Int.cast_zero, add_zero]
      rw [← mul_assoc, Complex.mul_conj']
      push_cast
      ring
    · intro n hn
      have h0 : 𝓕 (ρ : ℝ → ℂ) (ξ + n - (ℓ : ℝ) / 3) = 0 := by
        refine hρ.1 _ ?_
        intro hm
        obtain ⟨hm1, hm2⟩ := hm
        obtain ⟨h1, h2⟩ := h
        rcases lt_or_gt_of_ne hn with hneg | hpos
        · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
          linarith
        · have : (1 : ℝ) ≤ n := by exact_mod_cast hpos
          linarith
      rw [h0]; simp
  · have h0 : 𝓕 (ρ : ℝ → ℂ) (ξ - (ℓ : ℝ) / 3) = 0 := hρ.1 _ h
    rw [h0]; simp

/-- Fiberwise Fourier-series identity for fixed `ℓ`. -/
theorem hasSum_fiber (ρ : 𝓢(ℝ, ℂ)) (hρ : IsFrameWindow ρ) {G : ℝ → ℂ} (hG : Continuous G) (ℓ : ℤ)
    (hs : Summable (fun v : ℤ => ‖coeffF ρ G v ℓ‖)) (ξ : ℝ) :
    HasSum (fun v : ℤ => coeffF ρ G v ℓ * ePhase (-((v : ℝ) * ξ)))
      (∑' n : ℤ, (starRingEnd ℂ) (𝓕 (ρ : ℝ → ℂ) (ξ + n - (ℓ : ℝ) / 3)) * G (ξ + n)) := by
  set Gl : ℝ → ℂ := fun η => (starRingEnd ℂ) (𝓕 (ρ : ℝ → ℂ) (η - (ℓ : ℝ) / 3)) * G η with hGl
  have hc : Continuous Gl := by
    have := continuous_fourier_rho ρ
    simp only [hGl]; fun_prop
  have hcs : HasCompactSupport Gl := by
    refine HasCompactSupport.intro (K := Set.Icc ((ℓ : ℝ) / 3) ((ℓ : ℝ) / 3 + 1)) isCompact_Icc ?_
    intro η hη
    have : 𝓕 (ρ : ℝ → ℂ) (η - (ℓ : ℝ) / 3) = 0 := by
      refine hρ.1 _ ?_
      intro hm
      apply hη
      obtain ⟨h1, h2⟩ := hm
      constructor <;> linarith
    simp only [hGl, this, map_zero, zero_mul]
  have hF : ∀ n : ℤ, 𝓕 Gl n = coeffF ρ G (-n) ℓ := by
    intro n
    rw [fourier_eq_integral_ePhase]
    unfold coeffF
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    simp only [hGl, Int.cast_neg]
    rw [mul_comm η (n : ℝ), neg_mul]
    ring
  have hs' : Summable (fun n : ℤ => 𝓕 Gl n) := by
    refine Summable.of_norm ?_
    have : Summable (fun n : ℤ => ‖coeffF ρ G (-n) ℓ‖) :=
      (Equiv.summable_iff (f := fun v : ℤ => ‖coeffF ρ G v ℓ‖) (Equiv.neg ℤ)).2 hs
    simpa only [hF] using this
  have h := hasSum_poisson_step hc hcs hs' ξ
  have h2 := (Equiv.neg ℤ).hasSum_iff.2 h
  convert h2 using 1
  funext v
  simp only [Function.comp_apply, Equiv.neg_apply, hF, neg_neg, Int.cast_neg, neg_mul]

/-- Pointwise (in `ξ`) Fourier-side frame identity: `Ĝ(ξ) = ∑_{ℓ,v} c_{v,ℓ} ψ̂_{v,ℓ}(ξ)`. -/
theorem hasSum_fourier_frame (ρ : 𝓢(ℝ, ℂ)) (hρ : IsFrameWindow ρ) {G : ℝ → ℂ} (hG : Continuous G)
    (hs : Summable (fun p : ℤ × ℤ => ‖coeffF ρ G p.1 p.2‖)) (ξ : ℝ) :
    HasSum (fun p : ℤ × ℤ => coeffF ρ G p.1 p.2 * 𝓕 (wavePacket ρ p.1 p.2) ξ) (G ξ) := by
  obtain ⟨R, hR0, hR⟩ := exists_norm_fourier_le ρ
  have hsum : Summable (fun p : ℤ × ℤ => coeffF ρ G p.1 p.2 * 𝓕 (wavePacket ρ p.1 p.2) ξ) := by
    refine Summable.of_norm_bounded (hs.mul_right R) fun p => ?_
    rw [fourier_wavePacket, norm_mul, norm_mul, norm_ePhase, one_mul]
    exact mul_le_mul_of_nonneg_left (hR _) (norm_nonneg _)
  set f' : ℤ × ℤ → ℂ := fun q => coeffF ρ G q.2 q.1 * 𝓕 (wavePacket ρ q.2 q.1) ξ with hf'
  have hsum' : Summable f' := by
    have := (Equiv.prodComm ℤ ℤ).summable_iff.2 hsum
    exact this
  have hfib : ∀ ℓ : ℤ, HasSum (fun v : ℤ => f' (ℓ, v))
      (((‖𝓕 (ρ : ℝ → ℂ) (ξ - (ℓ : ℝ) / 3)‖ ^ 2 : ℝ) : ℂ) * G ξ) := by
    intro ℓ
    have hs' : Summable (fun q : ℤ × ℤ => ‖coeffF ρ G q.2 q.1‖) :=
      (Equiv.summable_iff (f := fun p : ℤ × ℤ => ‖coeffF ρ G p.1 p.2‖) (Equiv.prodComm ℤ ℤ)).2 hs
    have hsℓ : Summable (fun v : ℤ => ‖coeffF ρ G v ℓ‖) := hs'.prod_factor ℓ
    have h1 := hasSum_fiber ρ hρ hG ℓ hsℓ ξ
    have h2 := h1.mul_left (𝓕 (ρ : ℝ → ℂ) (ξ - (ℓ : ℝ) / 3))
    rw [rho_hat_mul_tsum ρ hρ G ℓ ξ] at h2
    convert h2 using 1
    funext v
    simp only [hf', fourier_wavePacket]
    ring
  have hT := hsum'.hasSum
  have hwin : HasSum (fun ℓ : ℤ => ((‖𝓕 (ρ : ℝ → ℂ) (ξ - (ℓ : ℝ) / 3)‖ ^ 2 : ℝ) : ℂ) * G ξ) (G ξ) := by
    have h2 := (Complex.hasSum_ofReal.2 (hρ.2 ξ)).mul_right (G ξ)
    simpa using h2
  have hg := hT.prod_fiberwise hfib
  have heq := hg.unique hwin
  rw [heq] at hT
  exact (Equiv.prodComm ℤ ℤ).hasSum_iff.1 hT


/-! ## From the Fourier side to the line -/

theorem norm_wavePacket (ρ : ℝ → ℂ) (v ℓ : ℤ) (x : ℝ) : ‖wavePacket ρ v ℓ x‖ = ‖ρ (x - v)‖ := by
  simp only [wavePacket, norm_mul, norm_ePhase, one_mul]

theorem continuous_wavePacket (ρ : 𝓢(ℝ, ℂ)) (v ℓ : ℤ) : Continuous (wavePacket ρ v ℓ) := by
  unfold wavePacket
  have := continuous_ePhase
  have := ρ.continuous
  fun_prop

theorem integrable_wavePacket (ρ : 𝓢(ℝ, ℂ)) (v ℓ : ℤ) : Integrable (wavePacket ρ v ℓ) := by
  have h : Integrable (fun x : ℝ => ρ (x - v)) := ρ.integrable.comp_sub_right (v : ℝ)
  refine h.norm.mono' (continuous_wavePacket ρ v ℓ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_wavePacket]

theorem integrable_fourier_wavePacket (ρ : 𝓢(ℝ, ℂ)) (v ℓ : ℤ) :
    Integrable (𝓕 (wavePacket ρ v ℓ)) := by
  have h : Integrable (fun ξ : ℝ => 𝓕 (ρ : ℝ → ℂ) (ξ - (ℓ : ℝ) / 3)) :=
    (integrable_fourier_rho ρ).comp_sub_right ((ℓ : ℝ) / 3)
  have hc : Continuous (𝓕 (wavePacket ρ v ℓ)) := by
    have : 𝓕 (wavePacket ρ v ℓ) = fun ξ => ePhase (-((v : ℝ) * ξ)) * 𝓕 (ρ : ℝ → ℂ) (ξ - (ℓ : ℝ) / 3) :=
      funext (fourier_wavePacket ρ v ℓ)
    rw [this]
    have := continuous_ePhase
    have := continuous_fourier_rho ρ
    fun_prop
  refine h.norm.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  rw [fourier_wavePacket, norm_mul, norm_ePhase, one_mul]

theorem fourierInv_wavePacket (ρ : 𝓢(ℝ, ℂ)) (v ℓ : ℤ) (x : ℝ) :
    ∫ ξ, ePhase (ξ * x) * 𝓕 (wavePacket ρ v ℓ) ξ = wavePacket ρ v ℓ x := by
  rw [← fourierInv_eq_integral_ePhase]
  exact congrFun ((continuous_wavePacket ρ v ℓ).fourierInv_fourier_eq (integrable_wavePacket ρ v ℓ)
    (integrable_fourier_wavePacket ρ v ℓ)) x

/-- **Frame identity on the line, from the Fourier side.** If `Ĝ` is continuous and the
Fourier-side coefficients are absolutely summable, then `g(x) = ∫ Ĝ(ξ) e(ξx) dξ` equals
`∑_{v,ℓ} c_{v,ℓ} ψ_{v,ℓ}(x)` (absolutely convergent). -/
theorem hasSum_frame_of_fourier (ρ : 𝓢(ℝ, ℂ)) (hρ : IsFrameWindow ρ) {G : ℝ → ℂ}
    (hG : Continuous G)
    (hs : Summable (fun p : ℤ × ℤ => ‖coeffF ρ G p.1 p.2‖)) (x : ℝ) :
    HasSum (fun p : ℤ × ℤ => coeffF ρ G p.1 p.2 * wavePacket ρ p.1 p.2 x)
      (∫ ξ, ePhase (ξ * x) * G ξ) := by
  set F : ℤ × ℤ → ℝ → ℂ := fun p ξ =>
    coeffF ρ G p.1 p.2 * 𝓕 (wavePacket ρ p.1 p.2) ξ * ePhase (ξ * x) with hF
  have hFint : ∀ p, Integrable (F p) := by
    intro p
    have h1 := integrable_fourier_wavePacket ρ p.1 p.2
    refine (h1.norm.const_mul ‖coeffF ρ G p.1 p.2‖).mono' ?_ (Filter.Eventually.of_forall fun ξ => ?_)
    · have hc : Continuous (fun ξ : ℝ => ePhase (ξ * x)) :=
        continuous_ePhase.comp (continuous_id.mul continuous_const)
      exact ((h1.aestronglyMeasurable.const_mul _).mul hc.aestronglyMeasurable)
    · simp only [hF, norm_mul, norm_ePhase, mul_one, le_refl]
  have hnorm : ∀ p : ℤ × ℤ, ∫ ξ, ‖F p ξ‖ = ‖coeffF ρ G p.1 p.2‖ * ∫ ξ, ‖𝓕 (ρ : ℝ → ℂ) ξ‖ := by
    intro p
    have : ∀ ξ, ‖F p ξ‖ = ‖coeffF ρ G p.1 p.2‖ * ‖𝓕 (ρ : ℝ → ℂ) (ξ - (p.2 : ℝ) / 3)‖ := by
      intro ξ; simp only [hF, fourier_wavePacket, norm_mul, norm_ePhase, mul_one, one_mul]
    simp_rw [this]
    rw [integral_const_mul,
      integral_sub_right_eq_self (fun ξ => ‖𝓕 (ρ : ℝ → ℂ) ξ‖) ((p.2 : ℝ) / 3)]
  have hFsum : Summable (fun p : ℤ × ℤ => ∫ ξ, ‖F p ξ‖) := by
    simp_rw [hnorm]; exact hs.mul_right _
  have h := hasSum_integral_of_summable_integral_norm hFint hFsum
  have h1 : ∀ p : ℤ × ℤ, ∫ ξ, F p ξ = coeffF ρ G p.1 p.2 * wavePacket ρ p.1 p.2 x := by
    intro p
    rw [← fourierInv_wavePacket ρ p.1 p.2 x, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [hF]; ring
  have h2 : ∀ ξ, ∑' p : ℤ × ℤ, F p ξ = ePhase (ξ * x) * G ξ := by
    intro ξ
    have := (hasSum_fourier_frame ρ hρ hG hs ξ).mul_right (ePhase (ξ * x))
    rw [mul_comm]; exact this.tsum_eq
  simp_rw [h1, h2] at h
  exact h


/-! ## Decay of the coefficients of a Schwartz function -/

theorem coeffF_eq_fourier (ρ : ℝ → ℂ) (G : ℝ → ℂ) (v ℓ : ℤ) :
    coeffF ρ G v ℓ =
      𝓕 (fun η => (starRingEnd ℂ) (𝓕 ρ (η - (ℓ : ℝ) / 3)) * G η) (-(v : ℝ)) := by
  rw [fourier_eq_integral_ePhase]
  unfold coeffF
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  beta_reduce
  have : -(η * -(v : ℝ)) = (v : ℝ) * η := by ring
  rw [this]; ring

section Decay

variable (ρ : 𝓢(ℝ, ℂ)) (h : 𝓢(ℝ, ℂ))

/-- The window function `windowProd ρ h ℓ = conj(ρ̂(· - ℓ/3)) h`. -/
def windowProd (ℓ : ℤ) : ℝ → ℂ :=
  fun η => (starRingEnd ℂ) (𝓕 (ρ : ℝ → ℂ) (η - (ℓ : ℝ) / 3)) * h η

theorem contDiff_windowProd (ℓ : ℤ) : ContDiff ℝ 2 (windowProd ρ h ℓ) := by
  have h1 : ContDiff ℝ 2 (fun η : ℝ => (𝓕 ρ : 𝓢(ℝ, ℂ)) (η - (ℓ : ℝ) / 3)) :=
    ((𝓕 ρ : 𝓢(ℝ, ℂ)).smooth 2).comp (contDiff_id.sub contDiff_const)
  have h2 : ContDiff ℝ 2 (fun η : ℝ => (starRingEnd ℂ) ((𝓕 ρ : 𝓢(ℝ, ℂ)) (η - (ℓ : ℝ) / 3))) :=
    Complex.conjCLE.contDiff.comp h1
  have h3 := h.smooth 2
  unfold windowProd
  simp only [fourier_coe'] at h2
  exact h2.mul h3


theorem one_add_sq_le (ℓ : ℤ) {η : ℝ} (hη : η ∈ Set.Icc ((ℓ : ℝ) / 3) ((ℓ : ℝ) / 3 + 1)) :
    1 + (ℓ : ℝ) ^ 2 ≤ 19 * (1 + η ^ 2) := by
  obtain ⟨h1, h2⟩ := hη
  set θ := η - (ℓ : ℝ) / 3 with hθ
  have hθ0 : 0 ≤ θ := by linarith
  have hθ1 : θ ≤ 1 := by linarith
  have hl : (ℓ : ℝ) = 3 * (η - θ) := by rw [hθ]; ring
  have : θ ^ 2 ≤ 1 := by nlinarith
  rw [hl]
  nlinarith [sq_nonneg (η + θ)]

theorem norm_iteratedFDeriv_le_decay (j : ℕ) (η : ℝ) :
    (1 + η ^ 2) * ‖iteratedFDeriv ℝ j h η‖ ≤
      SchwartzMap.seminorm ℝ 0 j h + SchwartzMap.seminorm ℝ 2 j h := by
  have h0 := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ h j η
  have h2 := SchwartzMap.le_seminorm ℝ 2 j h η
  rw [Real.norm_eq_abs, sq_abs] at h2
  nlinarith

theorem norm_iteratedFDeriv_window_le (ℓ : ℤ) (i : ℕ) (η : ℝ) :
    ‖iteratedFDeriv ℝ i (fun η : ℝ => (starRingEnd ℂ) ((𝓕 ρ : 𝓢(ℝ, ℂ)) (η - (ℓ : ℝ) / 3))) η‖ ≤
      SchwartzMap.seminorm ℝ 0 i (𝓕 ρ : 𝓢(ℝ, ℂ)) := by
  have := LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) Complex.conjLIE
    (fun η : ℝ => (𝓕 ρ : 𝓢(ℝ, ℂ)) (η - (ℓ : ℝ) / 3)) η i
  have e : (fun η : ℝ => (starRingEnd ℂ) ((𝓕 ρ : 𝓢(ℝ, ℂ)) (η - (ℓ : ℝ) / 3))) =
      ⇑Complex.conjLIE ∘ (fun η : ℝ => (𝓕 ρ : 𝓢(ℝ, ℂ)) (η - (ℓ : ℝ) / 3)) := rfl
  rw [e, this, iteratedFDeriv_comp_sub]
  exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ _ i _

theorem exists_bound_iteratedDeriv_windowProd (k : ℕ) (hk : k ≤ 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ℓ : ℤ) (η : ℝ), η ∈ Set.Icc ((ℓ : ℝ) / 3) ((ℓ : ℝ) / 3 + 1) →
      ‖iteratedDeriv k (windowProd ρ h ℓ) η‖ ≤ B / (1 + (ℓ : ℝ) ^ 2) := by
  set r : ℕ → ℝ := fun i => SchwartzMap.seminorm ℝ 0 i (𝓕 ρ : 𝓢(ℝ, ℂ)) with hr
  set Sg : ℕ → ℝ := fun j => SchwartzMap.seminorm ℝ 0 j h + SchwartzMap.seminorm ℝ 2 j h with hSg
  have hr0 : ∀ i, 0 ≤ r i := fun i => apply_nonneg _ _
  have hS0 : ∀ j, 0 ≤ Sg j := fun j => add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  refine ⟨19 * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * r i * Sg (k - i), ?_, ?_⟩
  · refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => ?_)
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hr0 _)) (hS0 _)
  intro ℓ η hη
  have hcd : ContDiff ℝ 2 (fun η : ℝ => (starRingEnd ℂ) ((𝓕 ρ : 𝓢(ℝ, ℂ)) (η - (ℓ : ℝ) / 3))) :=
    Complex.conjCLE.contDiff.comp (((𝓕 ρ : 𝓢(ℝ, ℂ)).smooth 2).comp (contDiff_id.sub contDiff_const))
  have hGl : windowProd ρ h ℓ = fun η : ℝ => (starRingEnd ℂ) ((𝓕 ρ : 𝓢(ℝ, ℂ)) (η - (ℓ : ℝ) / 3)) * h η := by
    unfold windowProd; simp only [fourier_coe']
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, hGl]
  refine (norm_iteratedFDeriv_mul_le hcd (h.smooth 2) η (by exact_mod_cast hk)).trans ?_
  have h19 := one_add_sq_le ℓ hη
  have hpos : (0 : ℝ) < 1 + (ℓ : ℝ) ^ 2 := by positivity
  have hpos' : (0 : ℝ) < 1 + η ^ 2 := by positivity
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  have hA := norm_iteratedFDeriv_window_le ρ ℓ i η
  have hB := norm_iteratedFDeriv_le_decay h (k - i) η
  have hB' : ‖iteratedFDeriv ℝ (k - i) h η‖ ≤ Sg (k - i) * 19 / (1 + (ℓ : ℝ) ^ 2) := by
    rw [le_div_iff₀ hpos]
    calc ‖iteratedFDeriv ℝ (k - i) h η‖ * (1 + (ℓ : ℝ) ^ 2)
        ≤ ‖iteratedFDeriv ℝ (k - i) h η‖ * (19 * (1 + η ^ 2)) :=
          mul_le_mul_of_nonneg_left h19 (norm_nonneg _)
      _ = 19 * ((1 + η ^ 2) * ‖iteratedFDeriv ℝ (k - i) h η‖) := by ring
      _ ≤ 19 * Sg (k - i) := mul_le_mul_of_nonneg_left hB (by norm_num)
      _ = Sg (k - i) * 19 := by ring
  calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun η : ℝ =>
          (starRingEnd ℂ) ((𝓕 ρ : 𝓢(ℝ, ℂ)) (η - (ℓ : ℝ) / 3))) η‖ * ‖iteratedFDeriv ℝ (k - i) h η‖
      ≤ (k.choose i : ℝ) * r i * (Sg (k - i) * 19 / (1 + (ℓ : ℝ) ^ 2)) := by
        have := mul_le_mul hA hB' (norm_nonneg _) (hr0 i)
        calc _ = (k.choose i : ℝ) * (‖iteratedFDeriv ℝ i (fun η : ℝ =>
            (starRingEnd ℂ) ((𝓕 ρ : 𝓢(ℝ, ℂ)) (η - (ℓ : ℝ) / 3))) η‖ * ‖iteratedFDeriv ℝ (k - i) h η‖) := by ring
          _ ≤ (k.choose i : ℝ) * (r i * (Sg (k - i) * 19 / (1 + (ℓ : ℝ) ^ 2))) :=
            mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
          _ = _ := by ring
    _ = 19 * ((k.choose i : ℝ) * r i * Sg (k - i)) / (1 + (ℓ : ℝ) ^ 2) := by ring


theorem windowProd_eq_zero (hρ : IsFrameWindow ρ) (ℓ : ℤ) {η : ℝ}
    (hη : η ∉ Set.Icc ((ℓ : ℝ) / 3) ((ℓ : ℝ) / 3 + 1)) : windowProd ρ h ℓ η = 0 := by
  have : 𝓕 (ρ : ℝ → ℂ) (η - (ℓ : ℝ) / 3) = 0 := by
    refine hρ.1 _ ?_
    intro hm
    apply hη
    obtain ⟨h1, h2⟩ := hm
    constructor <;> linarith
  simp only [windowProd, this, map_zero, zero_mul]

theorem iteratedDeriv_windowProd_eq_zero (hρ : IsFrameWindow ρ) (ℓ : ℤ) (k : ℕ) {η : ℝ}
    (hη : η ∉ Set.Icc ((ℓ : ℝ) / 3) ((ℓ : ℝ) / 3 + 1)) : iteratedDeriv k (windowProd ρ h ℓ) η = 0 := by
  have hev : windowProd ρ h ℓ =ᶠ[nhds η] (0 : ℝ → ℂ) := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hη] with y hy
    exact windowProd_eq_zero ρ h hρ ℓ hy
  rw [hev.iteratedDeriv_eq k]
  exact iteratedDeriv_const_zero

theorem integral_norm_iteratedDeriv_windowProd_le (hρ : IsFrameWindow ρ) (k : ℕ) (hk : k ≤ 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ℓ : ℤ, ∫ η, ‖iteratedDeriv k (windowProd ρ h ℓ) η‖ ≤ B / (1 + (ℓ : ℝ) ^ 2) := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_iteratedDeriv_windowProd ρ h k hk
  refine ⟨B, hB0, fun ℓ => ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc ((ℓ : ℝ) / 3) ((ℓ : ℝ) / 3 + 1))
    (fun η hη => by simp [iteratedDeriv_windowProd_eq_zero ρ h hρ ℓ k hη])]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Set.Icc ((ℓ : ℝ) / 3) ((ℓ : ℝ) / 3 + 1))
    (f := fun η => ‖iteratedDeriv k (windowProd ρ h ℓ) η‖) (C := B / (1 + (ℓ : ℝ) ^ 2))
    (by simp [Real.volume_Icc]) (fun η hη => by simpa using hB ℓ η hη)
  refine (Real.le_norm_self _).trans (this.trans ?_)
  simp [Measure.real, Real.volume_Icc]

theorem summable_inv_one_add_sq_int : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2)⁻¹) := by
  have h2 : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) := Real.summable_one_div_int_pow.2 (by norm_num)
  refine Summable.of_norm_bounded_eventually h2 ?_
  have : ∀ᶠ n : ℤ in Filter.cofinite, n ≠ 0 := by
    simpa using (Set.finite_singleton (0 : ℤ)).compl_mem_cofinite
  filter_upwards [this] with n hn
  have hn' : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), one_div]
  exact inv_anti₀ hn' (by linarith)

theorem summable_coeffF (hρ : IsFrameWindow ρ) :
    Summable (fun p : ℤ × ℤ => ‖coeffF ρ (h : ℝ → ℂ) p.1 p.2‖) := by
  obtain ⟨B0, hB0, h0⟩ := integral_norm_iteratedDeriv_windowProd_le ρ h hρ 0 (by norm_num)
  obtain ⟨B2, hB2, h2⟩ := integral_norm_iteratedDeriv_windowProd_le ρ h hρ 2 (by norm_num)
  set C : ℝ := B0 + (4 * Real.pi ^ 2)⁻¹ * B2 with hC
  have hC0 : 0 ≤ C := by positivity
  have hsum : Summable (fun p : ℤ × ℤ => C * ((1 + ((p.1 : ℤ) : ℝ) ^ 2)⁻¹ * (1 + ((p.2 : ℤ) : ℝ) ^ 2)⁻¹)) := by
    refine Summable.mul_left _ ?_
    exact Summable.mul_of_nonneg (f := fun n : ℤ => (1 + (n : ℝ) ^ 2)⁻¹)
      (g := fun n : ℤ => (1 + (n : ℝ) ^ 2)⁻¹) summable_inv_one_add_sq_int
      summable_inv_one_add_sq_int (fun n => by positivity) (fun n => by positivity)
  refine Summable.of_norm_bounded hsum fun p => ?_
  obtain ⟨v, ℓ⟩ := p
  simp only
  rw [norm_norm, coeffF_eq_fourier]
  have hcd := contDiff_windowProd ρ h ℓ
  have hint : ∀ k ≤ 2, Integrable (iteratedDeriv k (windowProd ρ h ℓ)) := by
    intro k hk
    refine (hcd.continuous_iteratedDeriv k (by exact_mod_cast hk)).integrable_of_hasCompactSupport ?_
    exact HasCompactSupport.intro (K := Set.Icc ((ℓ : ℝ) / 3) ((ℓ : ℝ) / 3 + 1)) isCompact_Icc
      (fun η hη => iteratedDeriv_windowProd_eq_zero ρ h hρ ℓ k hη)
  have hF := Real.one_add_sq_mul_norm_fourier_le hcd hint (-(v : ℝ))
  have hpos : (0 : ℝ) < 1 + (-(v : ℝ)) ^ 2 := by positivity
  have hpos' : (0 : ℝ) < 1 + (ℓ : ℝ) ^ 2 := by positivity
  have hI : (∫ η, ‖windowProd ρ h ℓ η‖) + (4 * Real.pi ^ 2)⁻¹ * ∫ η, ‖iteratedDeriv 2 (windowProd ρ h ℓ) η‖ ≤
      C / (1 + (ℓ : ℝ) ^ 2) := by
    have e0 := h0 ℓ
    simp only [iteratedDeriv_zero] at e0
    have e2 := h2 ℓ
    calc _ ≤ B0 / (1 + (ℓ : ℝ) ^ 2) + (4 * Real.pi ^ 2)⁻¹ * (B2 / (1 + (ℓ : ℝ) ^ 2)) :=
          add_le_add e0 (mul_le_mul_of_nonneg_left e2 (by positivity))
      _ = C / (1 + (ℓ : ℝ) ^ 2) := by rw [hC]; ring
  have : ‖𝓕 (windowProd ρ h ℓ) (-(v : ℝ))‖ ≤ C / (1 + (ℓ : ℝ) ^ 2) / (1 + (-(v : ℝ)) ^ 2) := by
    rw [le_div_iff₀ hpos, mul_comm]
    exact hF.trans hI
  refine this.trans ?_
  rw [neg_sq]
  apply le_of_eq
  field_simp

end Decay


/-! ## (a) The frame identity for Schwartz functions -/

/-- Fourier inversion for a Schwartz function, in the form `f x = ∫ e(ξ x) f̂(ξ) dξ`. -/
theorem fourierInv_schwartz (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ∫ ξ, ePhase (ξ * x) * 𝓕 (f : ℝ → ℂ) ξ = f x := by
  rw [← fourierInv_eq_integral_ePhase]
  have hi : Integrable (𝓕 (f : ℝ → ℂ)) := by
    rw [← fourier_coe']; exact (𝓕 f : 𝓢(ℝ, ℂ)).integrable
  exact congrFun (f.continuous.fourierInv_fourier_eq f.integrable hi) x

/-- **(a), coefficients.** `⟨f, ψ_{v,ℓ}⟩ = ∫ conj(ρ̂(η - ℓ/3)) f̂(η) e^{2πivη} dη`
(pairing `⟨f, φ⟩ = ∫ f conj φ`). -/
theorem pairing_wavePacket (ρ f : 𝓢(ℝ, ℂ)) (v ℓ : ℤ) :
    pairing (f : ℝ → ℂ) (wavePacket ρ v ℓ) =
      ∫ η, (starRingEnd ℂ) (𝓕 (ρ : ℝ → ℂ) (η - (ℓ : ℝ) / 3)) * 𝓕 (f : ℝ → ℂ) η *
        ePhase ((v : ℝ) * η) := by
  have hG : Continuous (𝓕 (f : ℝ → ℂ)) := by rw [← fourier_coe']; exact (𝓕 f : 𝓢(ℝ, ℂ)).continuous
  have hGi : Integrable (𝓕 (f : ℝ → ℂ)) := by rw [← fourier_coe']; exact (𝓕 f : 𝓢(ℝ, ℂ)).integrable
  have h1 := integral_fourierInv_mul_conj hG hGi (continuous_wavePacket ρ v ℓ)
    (integrable_wavePacket ρ v ℓ)
  unfold pairing
  have h2 : ∀ x, (f : ℝ → ℂ) x = ∫ ξ, ePhase (ξ * x) * 𝓕 (f : ℝ → ℂ) ξ :=
    fun x => (fourierInv_schwartz f x).symm
  simp_rw [← h2] at h1
  rw [h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  beta_reduce
  rw [fourier_wavePacket, map_mul, conj_ePhase, neg_neg]
  ring

theorem summable_pairing_wavePacket (ρ : 𝓢(ℝ, ℂ)) (hρ : IsFrameWindow ρ) (f : 𝓢(ℝ, ℂ)) :
    Summable (fun p : ℤ × ℤ => ‖pairing (f : ℝ → ℂ) (wavePacket ρ p.1 p.2)‖) := by
  have := summable_coeffF ρ (𝓕 f : 𝓢(ℝ, ℂ)) hρ
  simp only [fourier_coe'] at this
  refine this.congr fun p => ?_
  rw [pairing_wavePacket]; rfl

/-- **(a) Frame identity** (BD26 L977-990). For Schwartz `f` and a frame window `ρ`, for every `x`
the double family `⟨f, ψ_{v,ℓ}⟩ ψ_{v,ℓ}(x)` over `(v, ℓ) ∈ ℤ × ℤ` is absolutely summable with sum
`f x`. -/
theorem hasSum_frame (ρ : 𝓢(ℝ, ℂ)) (hρ : IsFrameWindow ρ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasSum (fun p : ℤ × ℤ => pairing (f : ℝ → ℂ) (wavePacket ρ p.1 p.2) * wavePacket ρ p.1 p.2 x)
      (f x) := by
  have hs := summable_coeffF ρ (𝓕 f : 𝓢(ℝ, ℂ)) hρ
  have hG : Continuous (𝓕 (f : ℝ → ℂ)) := by rw [← fourier_coe']; exact (𝓕 f : 𝓢(ℝ, ℂ)).continuous
  simp only [fourier_coe'] at hs
  have h := hasSum_frame_of_fourier ρ hρ hG hs x
  rw [fourierInv_schwartz f x] at h
  have e : ∀ p : ℤ × ℤ, pairing (f : ℝ → ℂ) (wavePacket ρ p.1 p.2) =
      coeffF ρ (𝓕 (f : ℝ → ℂ)) p.1 p.2 := fun p => pairing_wavePacket ρ f p.1 p.2
  simp_rw [e]
  exact h


theorem summable_norm_frame (ρ : 𝓢(ℝ, ℂ)) (hρ : IsFrameWindow ρ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Summable (fun p : ℤ × ℤ =>
      ‖pairing (f : ℝ → ℂ) (wavePacket ρ p.1 p.2) * wavePacket ρ p.1 p.2 x‖) := by
  obtain ⟨R, hR0, hR⟩ := exists_norm_le ρ
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
    ((summable_pairing_wavePacket ρ hρ f).mul_right R)
  rw [norm_mul, norm_wavePacket]
  exact mul_le_mul_of_nonneg_left (hR _) (norm_nonneg _)

/-! ## Existence of a frame window -/

/-- A smooth bump, positive exactly on `(0.1, 0.9)`. -/
def bumpTheta (ξ : ℝ) : ℝ :=
  expNegInvGlue (ξ - 1 / 10) * expNegInvGlue (9 / 10 - ξ)

theorem bumpTheta_pos {ξ : ℝ} (h1 : 1 / 10 < ξ) (h2 : ξ < 9 / 10) : 0 < bumpTheta ξ :=
  mul_pos (expNegInvGlue.pos_of_pos (by linarith)) (expNegInvGlue.pos_of_pos (by linarith))

theorem bumpTheta_eq_zero {ξ : ℝ} (h : ¬ (1 / 10 < ξ ∧ ξ < 9 / 10)) : bumpTheta ξ = 0 := by
  unfold bumpTheta
  by_cases h1 : 1 / 10 < ξ
  · have h2 : 9 / 10 ≤ ξ := by
      by_contra h2
      exact h ⟨h1, by linarith⟩
    rw [expNegInvGlue.zero_of_nonpos (by linarith : 9 / 10 - ξ ≤ 0), mul_zero]
  · rw [expNegInvGlue.zero_of_nonpos (by linarith : ξ - 1 / 10 ≤ 0), zero_mul]

theorem contDiff_bumpTheta : ContDiff ℝ ∞ bumpTheta := by
  unfold bumpTheta
  exact (expNegInvGlue.contDiff.comp (contDiff_id.sub contDiff_const)).mul
    (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

/-- The periodised square `D(ξ) = ∑_ℓ ϑ(ξ - ℓ/3)²` (a locally finite sum). -/
def thetaPer (ξ : ℝ) : ℝ := ∑' ℓ : ℤ, bumpTheta (ξ - (ℓ : ℝ) / 3) ^ 2

/-- Only `ℓ ∈ [⌊3ξ₀⌋ - 4, ⌊3ξ₀⌋ + 3]` contribute for `ξ` within `1/3` of `ξ₀`. -/
theorem bumpTheta_term_eq_zero {ξ₀ ξ : ℝ} (hξ : |ξ - ξ₀| < 1 / 3) {ℓ : ℤ}
    (hℓ : ℓ ∉ Finset.Icc (⌊3 * ξ₀⌋ - 4) (⌊3 * ξ₀⌋ + 3)) :
    bumpTheta (ξ - (ℓ : ℝ) / 3) = 0 := by
  apply bumpTheta_eq_zero
  rintro ⟨h1, h2⟩
  apply hℓ
  rw [Finset.mem_Icc]
  have hf1 := Int.floor_le (3 * ξ₀)
  have hf2 := Int.lt_floor_add_one (3 * ξ₀)
  have ha := abs_lt.1 hξ
  have e1 : (ℓ : ℝ) < 3 * ξ - 3 / 10 := by linarith
  have e2 : 3 * ξ - 27 / 10 < (ℓ : ℝ) := by linarith
  constructor
  · have : (⌊3 * ξ₀⌋ : ℝ) - 5 < (ℓ : ℝ) := by linarith [ha.1, ha.2]
    have : ((⌊3 * ξ₀⌋ - 5 : ℤ) : ℝ) < (ℓ : ℝ) := by push_cast; linarith
    have := Int.cast_lt.1 this
    omega
  · have : (ℓ : ℝ) < (⌊3 * ξ₀⌋ : ℝ) + 4 := by linarith [ha.1, ha.2]
    have : (ℓ : ℝ) < ((⌊3 * ξ₀⌋ + 4 : ℤ) : ℝ) := by push_cast; linarith
    have := Int.cast_lt.1 this
    omega

theorem summable_bumpTheta_sq (ξ : ℝ) :
    Summable (fun ℓ : ℤ => bumpTheta (ξ - (ℓ : ℝ) / 3) ^ 2) :=
  summable_of_ne_finset_zero (s := Finset.Icc (⌊3 * ξ⌋ - 4) (⌊3 * ξ⌋ + 3)) fun ℓ hℓ => by
    rw [bumpTheta_term_eq_zero (ξ₀ := ξ) (by simp) hℓ]; simp

theorem thetaPer_eventuallyEq (ξ₀ : ℝ) :
    thetaPer =ᶠ[nhds ξ₀] fun ξ => ∑ ℓ ∈ Finset.Icc (⌊3 * ξ₀⌋ - 4) (⌊3 * ξ₀⌋ + 3),
      bumpTheta (ξ - (ℓ : ℝ) / 3) ^ 2 := by
  have : Set.Ioo (ξ₀ - 1 / 3) (ξ₀ + 1 / 3) ∈ nhds ξ₀ := Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [this] with ξ hξ
  have hξ' : |ξ - ξ₀| < 1 / 3 := abs_lt.2 ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
  unfold thetaPer
  exact tsum_eq_sum fun ℓ hℓ => by rw [bumpTheta_term_eq_zero hξ' hℓ]; simp

theorem contDiff_thetaPer : ContDiff ℝ ∞ thetaPer := by
  rw [contDiff_iff_contDiffAt]
  intro ξ₀
  have : ContDiff ℝ ∞ (fun ξ : ℝ => ∑ ℓ ∈ Finset.Icc (⌊3 * ξ₀⌋ - 4) (⌊3 * ξ₀⌋ + 3),
      bumpTheta (ξ - (ℓ : ℝ) / 3) ^ 2) := by
    refine ContDiff.sum fun ℓ _ => ?_
    exact (contDiff_bumpTheta.comp (contDiff_id.sub contDiff_const)).pow 2
  exact this.contDiffAt.congr_of_eventuallyEq (thetaPer_eventuallyEq ξ₀)

theorem thetaPer_pos (ξ : ℝ) : 0 < thetaPer ξ := by
  have h1 := Int.floor_le (3 * ξ)
  have h2 := Int.lt_floor_add_one (3 * ξ)
  have hpos : 0 < bumpTheta (ξ - ((⌊3 * ξ⌋ - 1 : ℤ) : ℝ) / 3) :=
    bumpTheta_pos (by push_cast; linarith) (by push_cast; linarith)
  have := (summable_bumpTheta_sq ξ).le_tsum (⌊3 * ξ⌋ - 1) (fun j _ => by positivity)
  exact lt_of_lt_of_le (by positivity) this

theorem thetaPer_sub (ξ : ℝ) (m : ℤ) : thetaPer (ξ - (m : ℝ) / 3) = thetaPer ξ := by
  unfold thetaPer
  rw [← (Equiv.addRight m).tsum_eq (fun ℓ : ℤ => bumpTheta (ξ - (ℓ : ℝ) / 3) ^ 2)]
  refine tsum_congr fun ℓ => ?_
  simp only [Equiv.coe_addRight, Int.cast_add]
  congr 2
  ring

/-- The Fourier transform of the frame window. -/
def rhoHat (ξ : ℝ) : ℝ := bumpTheta ξ / √(thetaPer ξ)

theorem contDiff_rhoHat : ContDiff ℝ ∞ rhoHat :=
  contDiff_bumpTheta.div (contDiff_thetaPer.sqrt fun x => (thetaPer_pos x).ne')
    fun x => (Real.sqrt_pos.2 (thetaPer_pos x)).ne'

theorem rhoHat_eq_zero {ξ : ℝ} (h : ξ ∉ Set.Icc (1 / 10 : ℝ) (9 / 10)) : rhoHat ξ = 0 := by
  unfold rhoHat
  rw [bumpTheta_eq_zero, zero_div]
  rintro ⟨h1, h2⟩
  exact h ⟨h1.le, h2.le⟩

theorem hasSum_rhoHat_sq (ξ : ℝ) :
    HasSum (fun ℓ : ℤ => ‖(rhoHat (ξ - (ℓ : ℝ) / 3) : ℂ)‖ ^ 2) 1 := by
  have hD := thetaPer_pos ξ
  have h := ((summable_bumpTheta_sq ξ).hasSum).div_const (thetaPer ξ)
  rw [show (∑' ℓ : ℤ, bumpTheta (ξ - (ℓ : ℝ) / 3) ^ 2) = thetaPer ξ from rfl,
    div_self hD.ne'] at h
  convert h using 1
  funext ℓ
  simp only [rhoHat, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
    Real.sq_sqrt hD.le, thetaPer_sub]

/-- **Existence of a frame window** (blueprint R4, setup): there is a Schwartz function `ρ` with
`ρ̂` supported in `[0.1, 0.9]` and `∑_ℓ |ρ̂(ξ - ℓ/3)|² = 1`. Here `ρ̂ = ϑ / (∑_ℓ ϑ(· - ℓ/3)²)^{1/2}`
for the smooth bump `ϑ` positive exactly on `(0.1, 0.9)`. -/
theorem exists_isFrameWindow : ∃ ρ : 𝓢(ℝ, ℂ), IsFrameWindow ρ := by
  have hc : HasCompactSupport (fun ξ : ℝ => (rhoHat ξ : ℂ)) := by
    refine HasCompactSupport.intro (K := Set.Icc (1 / 10 : ℝ) (9 / 10)) isCompact_Icc fun ξ hξ => ?_
    simp [rhoHat_eq_zero hξ]
  have hs : ContDiff ℝ ∞ (fun ξ : ℝ => (rhoHat ξ : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_rhoHat
  set g : 𝓢(ℝ, ℂ) := hc.toSchwartzMap hs with hg
  set ρ : 𝓢(ℝ, ℂ) := 𝓕⁻ g with hρ
  refine ⟨ρ, ?_⟩
  have h1 : (𝓕 ρ : 𝓢(ℝ, ℂ)) = g := FourierInvPair.fourier_fourierInv_eq g
  have h2 : 𝓕 (ρ : ℝ → ℂ) = fun ξ => (rhoHat ξ : ℂ) := by
    rw [← fourier_coe', h1]
    rfl
  refine ⟨fun ξ hξ => ?_, fun ξ => ?_⟩
  · rw [h2]; simp [rhoHat_eq_zero hξ]
  · rw [h2]; exact hasSum_rhoHat_sq ξ

end PrimeBHT.TimeFrequency.RealLine
