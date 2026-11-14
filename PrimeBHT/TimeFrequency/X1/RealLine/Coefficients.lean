module

public import PrimeBHT.TimeFrequency.X1.RealLine.Frame
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.PSeries

/-!
# Real-line wave-packet frame: coefficients of one scale (blueprint node R4 (b), (c))

See `Frame.lean` for the setup, conventions and part (a) (`IsFrameWindow`, `wavePacket`, `pairing`,
`hasSum_frame`). Here `B_1(ψ, f₁, f₂)(x) = ∫ f₁(x-y) f₂(x+y) ψ(y) dy` is `bilinB1` (complex profile `ψ`;
the real-profile `dilAvg` of `Dilation.lean` is the case `t = 1`, `φ` real), and `ψ` ranges over
`IsBandProfile M ψ`: `ψ` a.e. strongly measurable (needed for `ψ̂` to be meaningful), `|ψ(x)| ≤ (1+|x|)^{-M}`,
`supp ψ̂ ⊆ [8, 9]`.

* **(b)** `coeff3 ρ ψ v₁ v₂ v₃ ℓ₁ ℓ₂ ℓ₃ = ⟨B_1(ψ, ψ_{v₁ℓ₁}, ψ_{v₂ℓ₂}), ψ_{v₃ℓ₃}⟩`:
  `coeff3_eq_integral` (the double Fourier integral, with `ψ̂_{v₃ℓ₃}` *conjugated*: the blueprint's
  formula, valid for the pairing `⟨·, φ⟩ = ∫ · conj φ`; BD26 (e:0) omits the conjugate because BD26 pairs with
  `conj ψ_{v₃ℓ₃}`), `coeff3_eq_zero` (support: `ℓ₁ - ℓ₂ ∈ [21, 30]`, `ℓ₁ + ℓ₂ - ℓ₃ ∈ [-6, 3]`; actually
  `[22, 29]` and `[-5, 2]`), `norm_coeff3_le` (`|c| ≤ C_M (1+|n|)^{-(M-2)}`, `C_M` depending on `M, ρ` only).
* The decay proof is the blueprint's: after `x ↦ x + v₃`, `key_pointwise` (`A + B ≥ |n|/4` or
  `C₁ + C₂ > |n|/2`), `norm_triple_integral_le`.
* The Fourier side: `bilinB1_eq_integral_density` (`B_1 = 𝓕⁻ B̃` with the density
  `B̃(ξ) = ∫ f̂₁(ξ₁) f̂₂(ξ-ξ₁) ψ̂(2ξ₁-ξ) dξ₁`), `hasSum_frame_bilinB1` (the frame identity for
  `B_1(ψ, ψ_{v₁ℓ₁}, ψ_{v₂ℓ₂})`, which is not shown to be Schwartz: it is obtained from the Fourier-side
  `hasSum_frame_of_fourier`).
* **(c)** `hasSum_representation` (the six-fold family over `(a, b, n₁, n₂, v, ℓ) ∈ ℤ⁶` is summable with
  sum `B_1(ψ, f₁, f₂)(x)`; `summable_norm_representation`: absolutely), `repTerm_eq_zero` (only
  `a ∈ [21, 30]`, `b ∈ [-6, 3]` contribute), `representation` (the blueprint's form with the finite sums
  over `a`, `b`).
All results need only `3 < M` (the blueprint's `M ≥ 100` is a special case).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform Real SchwartzMap

namespace PrimeBHT.TimeFrequency.RealLine

/-- The weight `(1+|t|)^{-M}`. -/
def wt (M : ℝ) (t : ℝ) : ℝ := (1 + |t|) ^ (-M)

theorem wt_pos (M t : ℝ) : 0 < wt M t := Real.rpow_pos_of_pos (by positivity) _

theorem wt_nonneg (M t : ℝ) : 0 ≤ wt M t := (wt_pos M t).le

theorem wt_le_one {M : ℝ} (hM : 0 ≤ M) (t : ℝ) : wt M t ≤ 1 := by
  unfold wt
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) (by linarith)

theorem rpow_neg_anti {u v s : ℝ} (hu : 0 < u) (huv : u ≤ v) (hs : 0 ≤ s) :
    v ^ (-s) ≤ u ^ (-s) := by
  rw [Real.rpow_neg (hu.le.trans huv), Real.rpow_neg hu.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hu s) (Real.rpow_le_rpow hu.le huv hs)

theorem wt_split (M : ℝ) (t : ℝ) : wt M t = (1 + |t|) ^ (-(M - 2)) * wt 2 t := by
  unfold wt
  rw [← Real.rpow_add (by positivity)]; congr 1; ring

/-- Case 1 of the decay estimate: `A + B` is large. -/
theorem wt_mul_wt_le {M : ℝ} (hM : 2 ≤ M) (x y N : ℝ) (h : N ≤ 4 * (|x| + |y|)) (hN : 0 ≤ N) :
    wt M x * wt M y ≤ (1 + N / 4) ^ (-(M - 2)) * (wt 2 x * wt 2 y) := by
  rw [wt_split M x, wt_split M y]
  have h1 : (1 + |x|) ^ (-(M - 2)) * (1 + |y|) ^ (-(M - 2)) ≤ (1 + N / 4) ^ (-(M - 2)) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    refine rpow_neg_anti (by positivity) ?_ (by linarith)
    nlinarith [abs_nonneg x, abs_nonneg y, mul_nonneg (abs_nonneg x) (abs_nonneg y)]
  calc _ = ((1 + |x|) ^ (-(M - 2)) * (1 + |y|) ^ (-(M - 2))) * (wt 2 x * wt 2 y) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 (mul_nonneg (wt_nonneg _ _) (wt_nonneg _ _))

/-- The pointwise estimate behind the decay of the coefficients. -/
theorem key_pointwise {M : ℝ} (hM : 2 ≤ M) (n₁ n₂ x y : ℝ) :
    wt M x * wt M (x - y - n₁) * wt M (x + y - n₂) * wt M y ≤
      (1 + (|n₁| + |n₂|) / 4) ^ (-(M - 2)) * (wt 2 x * wt 2 y + wt M x * wt M y) := by
  set N := |n₁| + |n₂| with hN
  have hN0 : 0 ≤ N := by positivity
  have hM0 : 0 ≤ M := by linarith
  have h1 := wt_le_one hM0 (x - y - n₁)
  have h2 := wt_le_one hM0 (x + y - n₂)
  have hx := wt_nonneg M x
  have hy := wt_nonneg M y
  have hxy : wt M x * wt M y ≤ wt M x * wt M y := le_rfl
  by_cases hc : N ≤ 4 * (|x| + |y|)
  · have := wt_mul_wt_le hM x y N hc hN0
    have hle : wt M x * wt M (x - y - n₁) * wt M (x + y - n₂) * wt M y ≤ wt M x * wt M y := by
      have e : wt M x * wt M (x - y - n₁) * wt M (x + y - n₂) * wt M y =
          (wt M x * wt M y) * (wt M (x - y - n₁) * wt M (x + y - n₂)) := by ring
      rw [e]
      calc _ ≤ (wt M x * wt M y) * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hx hy)
            calc wt M (x - y - n₁) * wt M (x + y - n₂) ≤ 1 * 1 :=
                  mul_le_mul h1 h2 (wt_nonneg _ _) zero_le_one
              _ = 1 := one_mul 1
        _ = _ := mul_one _
    refine hle.trans (this.trans ?_)
    have : 0 ≤ (1 + N / 4) ^ (-(M - 2)) := Real.rpow_nonneg (by positivity) _
    nlinarith [mul_nonneg this (mul_nonneg hx hy)]
  · push Not at hc
    -- some `C_i > N / 4`
    have hn1 : |n₁| ≤ |x| + |y| + |x - y - n₁| := by
      have : n₁ = x - y - (x - y - n₁) := by ring
      calc |n₁| = |x - y - (x - y - n₁)| := by rw [← this]
        _ ≤ |x - y| + |x - y - n₁| := abs_sub _ _
        _ ≤ |x| + |y| + |x - y - n₁| := by linarith [abs_sub x y]
    have hn2 : |n₂| ≤ |x| + |y| + |x + y - n₂| := by
      have : n₂ = x + y - (x + y - n₂) := by ring
      calc |n₂| = |x + y - (x + y - n₂)| := by rw [← this]
        _ ≤ |x + y| + |x + y - n₂| := abs_sub _ _
        _ ≤ |x| + |y| + |x + y - n₂| := by linarith [abs_add_le x y]
    have hbig : N / 4 < |x - y - n₁| ∨ N / 4 < |x + y - n₂| := by
      by_contra hcon
      push Not at hcon
      linarith [hcon.1, hcon.2]
    have hpow : ∀ c : ℝ, N / 4 < |c| → wt M c ≤ (1 + N / 4) ^ (-(M - 2)) := by
      intro c hcN
      unfold wt
      calc (1 + |c|) ^ (-M) ≤ (1 + N / 4) ^ (-M) :=
            rpow_neg_anti (by positivity) (by linarith) hM0
        _ ≤ (1 + N / 4) ^ (-(M - 2)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    set K := (1 + N / 4) ^ (-(M - 2)) with hK
    have hK0 : 0 ≤ K := Real.rpow_nonneg (by positivity) _
    have hfin : ∀ P : ℝ, 0 ≤ P → P ≤ K → wt M x * wt M y * P ≤
        K * (wt 2 x * wt 2 y + wt M x * wt M y) := by
      intro P hP hPK
      have h3 : 0 ≤ wt 2 x * wt 2 y := mul_nonneg (wt_nonneg _ _) (wt_nonneg _ _)
      have h4 : 0 ≤ wt M x * wt M y := mul_nonneg hx hy
      nlinarith [mul_le_mul_of_nonneg_left hPK h4, mul_nonneg hK0 h3]
    have e : wt M x * wt M (x - y - n₁) * wt M (x + y - n₂) * wt M y =
        wt M x * wt M y * (wt M (x - y - n₁) * wt M (x + y - n₂)) := by ring
    rw [e]
    rcases hbig with hb | hb
    · refine hfin _ (mul_nonneg (wt_nonneg _ _) (wt_nonneg _ _)) ?_
      calc wt M (x - y - n₁) * wt M (x + y - n₂) ≤ K * 1 :=
            mul_le_mul (hpow _ hb) h2 (wt_nonneg _ _) hK0
        _ = K := mul_one _
    · refine hfin _ (mul_nonneg (wt_nonneg _ _) (wt_nonneg _ _)) ?_
      calc wt M (x - y - n₁) * wt M (x + y - n₂) ≤ 1 * K :=
            mul_le_mul h1 (hpow _ hb) (wt_nonneg _ _) zero_le_one
        _ = K := one_mul _


theorem integrable_wt {r : ℝ} (hr : 1 < r) : Integrable (wt r) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := r) (by simpa using hr)
  have h : (fun x : ℝ => (1 + ‖x‖) ^ (-r)) = wt r := by
    funext x; simp [wt, Real.norm_eq_abs]
  rwa [h] at this

/-- **Decay of the triple overlap** (blueprint R4(b), the estimate after `x → x + v₃`): if `ψ, f₁, f₂, f₃`
are bounded by `C` times the weights `wt M` centred at `0, v₁, v₂, v₃`, then
`|∫ (∫ f₁(x-y) f₂(x+y) ψ(y) dy) conj f₃(x) dx| ≲ (1 + (|v₁-v₃| + |v₂-v₃|)/4)^{-(M-2)}`. -/
theorem norm_triple_integral_le {M C : ℝ} (hM : 2 < M) (hC : 0 ≤ C) (v₁ v₂ v₃ : ℝ)
    {ψ f₁ f₂ f₃ : ℝ → ℂ}
    (hψ : ∀ y, ‖ψ y‖ ≤ C * wt M y) (h₁ : ∀ t, ‖f₁ t‖ ≤ C * wt M (t - v₁))
    (h₂ : ∀ t, ‖f₂ t‖ ≤ C * wt M (t - v₂)) (h₃ : ∀ t, ‖f₃ t‖ ≤ C * wt M (t - v₃)) :
    ‖∫ x, (∫ y, f₁ (x - y) * f₂ (x + y) * ψ y) * (starRingEnd ℂ) (f₃ x)‖ ≤
      C ^ 4 * ((∫ t, wt 2 t) ^ 2 + (∫ t, wt M t) ^ 2) *
        (1 + (|v₁ - v₃| + |v₂ - v₃|) / 4) ^ (-(M - 2)) := by
  set n₁ := v₁ - v₃ with hn₁
  set n₂ := v₂ - v₃ with hn₂
  set K := (1 + (|n₁| + |n₂|) / 4) ^ (-(M - 2)) with hK
  have hK0 : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  set I2 := ∫ t, wt 2 t with hI2
  set IM := ∫ t, wt M t with hIM
  have hint2 : Integrable (wt 2) := integrable_wt (by norm_num)
  have hintM : Integrable (wt M) := integrable_wt (by linarith)
  rw [← integral_add_right_eq_self _ v₃]
  have hpt : ∀ x y : ℝ, ‖f₁ (x + v₃ - y) * f₂ (x + v₃ + y) * ψ y * (starRingEnd ℂ) (f₃ (x + v₃))‖ ≤
      C ^ 4 * K * (wt 2 x * wt 2 y + wt M x * wt M y) := by
    intro x y
    have e1 : x + v₃ - y - v₁ = x - y - n₁ := by rw [hn₁]; ring
    have e2 : x + v₃ + y - v₂ = x + y - n₂ := by rw [hn₂]; ring
    have b1 := h₁ (x + v₃ - y)
    have b2 := h₂ (x + v₃ + y)
    have b3 := h₃ (x + v₃)
    rw [e1] at b1
    rw [e2] at b2
    rw [add_sub_cancel_right] at b3
    have hk := key_pointwise (le_of_lt hM) n₁ n₂ x y
    simp only [norm_mul, Complex.norm_conj]
    calc ‖f₁ (x + v₃ - y)‖ * ‖f₂ (x + v₃ + y)‖ * ‖ψ y‖ * ‖f₃ (x + v₃)‖
        ≤ (C * wt M (x - y - n₁)) * (C * wt M (x + y - n₂)) * (C * wt M y) * (C * wt M x) := by
          have p1 : 0 ≤ C * wt M (x - y - n₁) := mul_nonneg hC (wt_nonneg _ _)
          have p2 : 0 ≤ C * wt M (x + y - n₂) := mul_nonneg hC (wt_nonneg _ _)
          have p3 : 0 ≤ C * wt M y := mul_nonneg hC (wt_nonneg _ _)
          exact mul_le_mul (mul_le_mul (mul_le_mul b1 b2 (norm_nonneg _) p1) (hψ y)
            (norm_nonneg _) (mul_nonneg p1 p2)) b3 (norm_nonneg _) (mul_nonneg (mul_nonneg p1 p2) p3)
      _ = C ^ 4 * (wt M x * wt M (x - y - n₁) * wt M (x + y - n₂) * wt M y) := by ring
      _ ≤ C ^ 4 * (K * (wt 2 x * wt 2 y + wt M x * wt M y)) :=
          mul_le_mul_of_nonneg_left hk (by positivity)
      _ = _ := by ring
  have hinner : ∀ x : ℝ, ‖(∫ y, f₁ (x + v₃ - y) * f₂ (x + v₃ + y) * ψ y) *
      (starRingEnd ℂ) (f₃ (x + v₃))‖ ≤ C ^ 4 * K * (I2 * wt 2 x + IM * wt M x) := by
    intro x
    rw [← integral_mul_const]
    have hg : Integrable (fun y => C ^ 4 * K * (wt 2 x * wt 2 y + wt M x * wt M y)) :=
      ((hint2.const_mul (wt 2 x)).add (hintM.const_mul (wt M x))).const_mul _
    refine (norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun y => hpt x y)).trans ?_
    rw [integral_const_mul, integral_add (hint2.const_mul _) (hintM.const_mul _),
      integral_const_mul, integral_const_mul]
    apply le_of_eq
    ring
  have hG : Integrable (fun x => C ^ 4 * K * (I2 * wt 2 x + IM * wt M x)) :=
    ((hint2.const_mul I2).add (hintM.const_mul IM)).const_mul _
  refine (norm_integral_le_of_norm_le hG (Filter.Eventually.of_forall hinner)).trans ?_
  rw [integral_const_mul, integral_add (hint2.const_mul _) (hintM.const_mul _),
    integral_const_mul, integral_const_mul]
  apply le_of_eq
  rw [hn₁, hn₂] at hK
  ring


/-! ## The Fourier representation of `B_1` -/

/-- The one-scale average `B_1(ψ, f₁, f₂)(x) = ∫ f₁(x - y) f₂(x + y) ψ(y) dy` for a *complex* profile `ψ`
(the real-profile `dilAvg` of `Dilation.lean` is the case `t = 1`). -/
def bilinB1 (ψ f₁ f₂ : ℝ → ℂ) (x : ℝ) : ℂ := ∫ y, f₁ (x - y) * f₂ (x + y) * ψ y

section Fourier

variable {F₁ F₂ f₁ f₂ ψ : ℝ → ℂ}

theorem bilinB1_eq_integral_prod (hF₁ : Continuous F₁) (hF₂ : Continuous F₂)
    (hi₁ : Integrable F₁) (hi₂ : Integrable F₂)
    (hf₁ : ∀ t, f₁ t = ∫ ξ, ePhase (ξ * t) * F₁ ξ) (hf₂ : ∀ t, f₂ t = ∫ ξ, ePhase (ξ * t) * F₂ ξ)
    (hψ : Integrable ψ) (x : ℝ) :
    bilinB1 ψ f₁ f₂ x =
      ∫ z : ℝ × ℝ, F₁ z.1 * F₂ z.2 * 𝓕 ψ (z.1 - z.2) * ePhase ((z.1 + z.2) * x) := by
  have S1 : ∀ y, f₁ (x - y) * f₂ (x + y) = ∫ z : ℝ × ℝ,
      (ePhase (z.1 * (x - y)) * F₁ z.1) * (ePhase (z.2 * (x + y)) * F₂ z.2) := by
    intro y
    rw [Measure.volume_eq_prod, integral_prod_mul (fun ξ => ePhase (ξ * (x - y)) * F₁ ξ)
      (fun ξ => ePhase (ξ * (x + y)) * F₂ ξ), hf₁, hf₂]
  unfold bilinB1
  simp_rw [S1, ← integral_mul_const]
  have hK : Integrable (Function.uncurry fun (y : ℝ) (z : ℝ × ℝ) =>
      (ePhase (z.1 * (x - y)) * F₁ z.1) * (ePhase (z.2 * (x + y)) * F₂ z.2) * ψ y)
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := by
    have hbd : Integrable (fun p : ℝ × (ℝ × ℝ) => ‖ψ p.1‖ * (‖F₁ p.2.1‖ * ‖F₂ p.2.2‖))
        ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) :=
      hψ.norm.mul_prod (hi₁.norm.mul_prod hi₂.norm)
    refine hbd.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · have c1 : Continuous (fun p : ℝ × (ℝ × ℝ) => (ePhase (p.2.1 * (x - p.1)) * F₁ p.2.1) *
          (ePhase (p.2.2 * (x + p.1)) * F₂ p.2.2)) := by
        have := continuous_ePhase
        fun_prop
      exact c1.aestronglyMeasurable.mul hψ.aestronglyMeasurable.comp_fst
    · simp only [Function.uncurry, norm_mul, norm_ePhase, one_mul]
      apply le_of_eq; ring
  rw [integral_integral_swap hK]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  beta_reduce
  rw [fourier_eq_integral_ePhase, ← integral_const_mul, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have h : ePhase (z.1 * (x - y)) * ePhase (z.2 * (x + y)) =
      ePhase (-(y * (z.1 - z.2))) * ePhase ((z.1 + z.2) * x) := by
    rw [← ePhase_add, ← ePhase_add]; congr 1; ring
  calc ePhase (z.1 * (x - y)) * F₁ z.1 * (ePhase (z.2 * (x + y)) * F₂ z.2) * ψ y
      = F₁ z.1 * F₂ z.2 * ((ePhase (z.1 * (x - y)) * ePhase (z.2 * (x + y))) * ψ y) := by ring
    _ = _ := by rw [h]; ring


/-- The shear `(ξ₁, ξ₂) ↦ (ξ₁, ξ₁ + ξ₂)`:
`∬ H(ξ₁, ξ₂) k(ξ₁+ξ₂) = ∫ (∫ H(ξ₁, ξ - ξ₁) dξ₁) k(ξ) dξ` for bounded continuous `k`. -/
theorem integral_shear {H : ℝ × ℝ → ℂ} (hH : Integrable H) {k : ℝ → ℂ} (hk : Continuous k)
    {C : ℝ} (hkb : ∀ t, ‖k t‖ ≤ C) :
    ∫ z : ℝ × ℝ, H z * k (z.1 + z.2) = ∫ ξ : ℝ, (∫ ξ₁ : ℝ, H (ξ₁, ξ - ξ₁)) * k ξ := by
  have hmp : MeasurePreserving (MeasurableEquiv.shearSubRight ℝ) (volume : Measure (ℝ × ℝ))
      (volume : Measure (ℝ × ℝ)) := measurePreserving_prod_sub volume volume
  set g : ℝ × ℝ → ℂ := fun z => H z * k (z.1 + z.2) with hgdef
  have hg : Integrable g := by
    refine hH.mul_bdd (c := C) ?_ (Filter.Eventually.of_forall fun z => hkb _)
    exact (hk.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable
  have hint : Integrable (fun w : ℝ × ℝ => g (MeasurableEquiv.shearSubRight ℝ w)) :=
    hmp.integrable_comp_of_integrable hg
  have h1 : ∫ z : ℝ × ℝ, g z = ∫ w : ℝ × ℝ, g (MeasurableEquiv.shearSubRight ℝ w) :=
    (hmp.integral_comp' g).symm
  show ∫ z : ℝ × ℝ, g z = _
  rw [h1, Measure.volume_eq_prod, integral_prod_symm _ (by simpa [Measure.volume_eq_prod] using hint)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  beta_reduce
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ₁ => ?_)
  simp [hgdef, MeasurableEquiv.shearSubRight]

theorem continuous_fourier_of_integrable {φ : ℝ → ℂ} (hφ : Integrable φ) : Continuous (𝓕 φ) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by simp only [innerₗ_apply_apply]; exact continuous_inner) hφ

/-- The Fourier-side density `B̃(ξ) = ∫ F₁(ξ₁) F₂(ξ - ξ₁) Ψ(2ξ₁ - ξ) dξ₁` of `B_1(ψ, f₁, f₂)`. -/
def bilinDensity (F₁ F₂ Ψ : ℝ → ℂ) (ξ : ℝ) : ℂ := ∫ ξ₁, F₁ ξ₁ * F₂ (ξ - ξ₁) * Ψ (2 * ξ₁ - ξ)

theorem integrable_pairIntegrand {Ψ : ℝ → ℂ} (hi₁ : Integrable F₁) (hi₂ : Integrable F₂)
    (hΨ : Continuous Ψ) {C : ℝ} (hb : ∀ t, ‖Ψ t‖ ≤ C) :
    Integrable (fun z : ℝ × ℝ => F₁ z.1 * F₂ z.2 * Ψ (z.1 - z.2)) := by
  have h1 : Integrable (fun z : ℝ × ℝ => F₁ z.1 * F₂ z.2) (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]; exact hi₁.mul_prod hi₂
  refine h1.mul_bdd (c := C) ?_ (Filter.Eventually.of_forall fun z => hb _)
  exact (hΨ.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable

/-- `B_1(ψ, f₁, f₂) = 𝓕⁻ B̃`, pointwise. -/
theorem bilinB1_eq_integral_density (hF₁ : Continuous F₁) (hF₂ : Continuous F₂)
    (hi₁ : Integrable F₁) (hi₂ : Integrable F₂)
    (hf₁ : ∀ t, f₁ t = ∫ ξ, ePhase (ξ * t) * F₁ ξ) (hf₂ : ∀ t, f₂ t = ∫ ξ, ePhase (ξ * t) * F₂ ξ)
    (hψ : Integrable ψ) (x : ℝ) :
    bilinB1 ψ f₁ f₂ x = ∫ ξ, ePhase (ξ * x) * bilinDensity F₁ F₂ (𝓕 ψ) ξ := by
  rw [bilinB1_eq_integral_prod hF₁ hF₂ hi₁ hi₂ hf₁ hf₂ hψ x]
  have hI := integrable_pairIntegrand (F₁ := F₁) (F₂ := F₂) hi₁ hi₂ (continuous_fourier_of_integrable hψ)
    (fun t => Real.norm_fourier_le_integral_norm ψ t)
  have := integral_shear (H := fun z : ℝ × ℝ => F₁ z.1 * F₂ z.2 * 𝓕 ψ (z.1 - z.2)) hI
    (k := fun ξ => ePhase (ξ * x)) (by have := continuous_ePhase; fun_prop) (C := 1)
    (fun t => by simp [norm_ePhase])
  rw [this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  beta_reduce
  unfold bilinDensity
  rw [mul_comm]
  congr 2
  funext ξ₁
  congr 2
  ring_nf

theorem bilinDensity_eq_shear (F₁ F₂ Ψ : ℝ → ℂ) (ξ : ℝ) :
    bilinDensity F₁ F₂ Ψ ξ =
      ∫ ξ₁ : ℝ, (fun z : ℝ × ℝ => F₁ z.1 * F₂ z.2 * Ψ (z.1 - z.2)) (ξ₁, ξ - ξ₁) := by
  unfold bilinDensity
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ₁ => ?_)
  beta_reduce
  have : ξ₁ - (ξ - ξ₁) = 2 * ξ₁ - ξ := by ring
  rw [this]

theorem integrable_bilinDensity {Ψ : ℝ → ℂ} (hi₁ : Integrable F₁) (hi₂ : Integrable F₂)
    (hΨ : Continuous Ψ) {C : ℝ} (hb : ∀ t, ‖Ψ t‖ ≤ C) : Integrable (bilinDensity F₁ F₂ Ψ) := by
  have hI := integrable_pairIntegrand hi₁ hi₂ hΨ hb
  have hmp : MeasurePreserving (MeasurableEquiv.shearSubRight ℝ) (volume : Measure (ℝ × ℝ))
      (volume : Measure (ℝ × ℝ)) := measurePreserving_prod_sub volume volume
  have h1 := hmp.integrable_comp_of_integrable hI
  rw [Measure.volume_eq_prod] at h1
  have h2 := h1.integral_prod_right
  have : bilinDensity F₁ F₂ Ψ = fun ξ => ∫ ξ₁ : ℝ,
      ((fun z : ℝ × ℝ => F₁ z.1 * F₂ z.2 * Ψ (z.1 - z.2)) ∘ (MeasurableEquiv.shearSubRight ℝ))
        (ξ₁, ξ) := by
    funext ξ
    rw [bilinDensity_eq_shear]
    rfl
  rw [this]
  exact h2

theorem continuous_bilinDensity {Ψ : ℝ → ℂ} (hi₁ : Integrable F₁) (hF₂ : Continuous F₂)
    (hΨ : Continuous Ψ) {C₂ CΨ : ℝ} (hb₂ : ∀ t, ‖F₂ t‖ ≤ C₂) (hbΨ : ∀ t, ‖Ψ t‖ ≤ CΨ) :
    Continuous (bilinDensity F₁ F₂ Ψ) := by
  unfold bilinDensity
  refine continuous_of_dominated (bound := fun ξ₁ => ‖F₁ ξ₁‖ * (C₂ * CΨ)) ?_ ?_ ?_ ?_
  · intro ξ
    have c2 : Continuous (fun ξ₁ : ℝ => F₂ (ξ - ξ₁)) := by fun_prop
    have c3 : Continuous (fun ξ₁ : ℝ => Ψ (2 * ξ₁ - ξ)) := by fun_prop
    exact (hi₁.aestronglyMeasurable.mul c2.aestronglyMeasurable).mul c3.aestronglyMeasurable
  · intro ξ
    refine Filter.Eventually.of_forall fun ξ₁ => ?_
    simp only [norm_mul]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hb₂ _) (hbΨ _) (norm_nonneg _)
      ((norm_nonneg _).trans (hb₂ 0))) (norm_nonneg _)
  · exact hi₁.norm.mul_const _
  · refine Filter.Eventually.of_forall fun ξ₁ => ?_
    fun_prop

/-- **The Fourier formula for the pairing** (BD26 (e:0)):
`⟨B_1(ψ, f₁, f₂), φ⟩ = ∬ f̂₁(ξ₁) f̂₂(ξ₂) conj(φ̂(ξ₁+ξ₂)) ψ̂(ξ₁-ξ₂) dξ₁ dξ₂`. -/
theorem pairing_bilinB1_eq {C₂ : ℝ} (hF₁ : Continuous F₁) (hF₂ : Continuous F₂)
    (hi₁ : Integrable F₁) (hi₂ : Integrable F₂) (hb₂ : ∀ t, ‖F₂ t‖ ≤ C₂)
    (hf₁ : ∀ t, f₁ t = ∫ ξ, ePhase (ξ * t) * F₁ ξ) (hf₂ : ∀ t, f₂ t = ∫ ξ, ePhase (ξ * t) * F₂ ξ)
    (hψ : Integrable ψ) {φ : ℝ → ℂ} (hφc : Continuous φ) (hφi : Integrable φ) :
    pairing (bilinB1 ψ f₁ f₂) φ =
      ∫ z : ℝ × ℝ, F₁ z.1 * F₂ z.2 * (starRingEnd ℂ) (𝓕 φ (z.1 + z.2)) * 𝓕 ψ (z.1 - z.2) := by
  have hΨc := continuous_fourier_of_integrable hψ
  have hΨb : ∀ t, ‖𝓕 ψ t‖ ≤ ∫ v, ‖ψ v‖ := fun t => Real.norm_fourier_le_integral_norm ψ t
  have hBi := integrable_bilinDensity hi₁ hi₂ hΨc hΨb
  have hBc := continuous_bilinDensity hi₁ hF₂ hΨc hb₂ hΨb
  have hI := integrable_pairIntegrand hi₁ hi₂ hΨc hΨb
  unfold pairing
  have hB := fun x => bilinB1_eq_integral_density hF₁ hF₂ hi₁ hi₂ hf₁ hf₂ hψ x
  simp_rw [hB]
  rw [integral_fourierInv_mul_conj hBc hBi hφc hφi]
  have hk : Continuous (fun ξ => (starRingEnd ℂ) (𝓕 φ ξ)) :=
    Complex.continuous_conj.comp (continuous_fourier_of_integrable hφi)
  have hkb : ∀ t, ‖(starRingEnd ℂ) (𝓕 φ t)‖ ≤ ∫ v, ‖φ v‖ := fun t => by
    rw [Complex.norm_conj]; exact Real.norm_fourier_le_integral_norm φ t
  have := integral_shear (H := fun z : ℝ × ℝ => F₁ z.1 * F₂ z.2 * 𝓕 ψ (z.1 - z.2)) hI hk hkb
  have e1 : ∀ z : ℝ × ℝ, F₁ z.1 * F₂ z.2 * (starRingEnd ℂ) (𝓕 φ (z.1 + z.2)) * 𝓕 ψ (z.1 - z.2) =
      (fun z : ℝ × ℝ => F₁ z.1 * F₂ z.2 * 𝓕 ψ (z.1 - z.2)) z *
        (fun ξ => (starRingEnd ℂ) (𝓕 φ ξ)) (z.1 + z.2) := fun z => by beta_reduce; ring
  simp_rw [e1]
  rw [this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  beta_reduce
  rw [bilinDensity_eq_shear]

end Fourier

/-! ## (b) The coefficients -/

/-- The profiles `ψ` of Theorem Θ (BD26 `Θ_0`): measurable (so that `ψ̂` is meaningful),
`|ψ(x)| ≤ (1+|x|)^{-M}` and `supp ψ̂ ⊆ [8, 9]`. -/
structure IsBandProfile (M : ℝ) (ψ : ℝ → ℂ) : Prop where
  aesm : AEStronglyMeasurable ψ volume
  decay : ∀ x, ‖ψ x‖ ≤ (1 + |x|) ^ (-M)
  fourier_supp : ∀ ξ : ℝ, ξ ∉ Set.Icc (8 : ℝ) 9 → 𝓕 ψ ξ = 0

theorem IsBandProfile.integrable {M : ℝ} (hM : 1 < M) {ψ : ℝ → ℂ} (h : IsBandProfile M ψ) :
    Integrable ψ :=
  (integrable_wt hM).mono' h.aesm (Filter.Eventually.of_forall h.decay)

/-- The coefficient `c_{v₁v₂v₃ℓ₁ℓ₂ℓ₃} = ⟨B_1(ψ, ψ_{v₁ℓ₁}, ψ_{v₂ℓ₂}), ψ_{v₃ℓ₃}⟩`. -/
def coeff3 (ρ : 𝓢(ℝ, ℂ)) (ψ : ℝ → ℂ) (v₁ v₂ v₃ ℓ₁ ℓ₂ ℓ₃ : ℤ) : ℂ :=
  pairing (bilinB1 ψ (wavePacket ρ v₁ ℓ₁) (wavePacket ρ v₂ ℓ₂)) (wavePacket ρ v₃ ℓ₃)

theorem continuous_fourier_wavePacket (ρ : 𝓢(ℝ, ℂ)) (v ℓ : ℤ) : Continuous (𝓕 (wavePacket ρ v ℓ)) :=
  continuous_fourier_of_integrable (integrable_wavePacket ρ v ℓ)

/-- **(b), the Fourier formula** (BD26 (e:0)): `c = ∬ ψ̂_{v₁ℓ₁}(ξ₁) ψ̂_{v₂ℓ₂}(ξ₂) conj(ψ̂_{v₃ℓ₃}(ξ₁+ξ₂)) ψ̂(ξ₁-ξ₂)`
(`ψ̂_{v₃ℓ₃}` is conjugated: this is the correct formula for the pairing `⟨·, ψ_{v₃ℓ₃}⟩ = ∫ · conj ψ_{v₃ℓ₃}`). -/
theorem coeff3_eq_integral (ρ : 𝓢(ℝ, ℂ)) {M : ℝ} (hM : 1 < M) {ψ : ℝ → ℂ} (hψ : IsBandProfile M ψ)
    (v₁ v₂ v₃ ℓ₁ ℓ₂ ℓ₃ : ℤ) :
    coeff3 ρ ψ v₁ v₂ v₃ ℓ₁ ℓ₂ ℓ₃ =
      ∫ z : ℝ × ℝ, 𝓕 (wavePacket ρ v₁ ℓ₁) z.1 * 𝓕 (wavePacket ρ v₂ ℓ₂) z.2 *
        (starRingEnd ℂ) (𝓕 (wavePacket ρ v₃ ℓ₃) (z.1 + z.2)) * 𝓕 ψ (z.1 - z.2) := by
  unfold coeff3
  refine pairing_bilinB1_eq (continuous_fourier_wavePacket ρ v₁ ℓ₁)
    (continuous_fourier_wavePacket ρ v₂ ℓ₂) (integrable_fourier_wavePacket ρ v₁ ℓ₁)
    (integrable_fourier_wavePacket ρ v₂ ℓ₂)
    (fun t => Real.norm_fourier_le_integral_norm _ t)
    (fun t => (fourierInv_wavePacket ρ v₁ ℓ₁ t).symm)
    (fun t => (fourierInv_wavePacket ρ v₂ ℓ₂ t).symm) (hψ.integrable hM)
    (continuous_wavePacket ρ v₃ ℓ₃) (integrable_wavePacket ρ v₃ ℓ₃)

theorem fourier_wavePacket_eq_zero {ρ : 𝓢(ℝ, ℂ)} (hρ : IsFrameWindow ρ) (v ℓ : ℤ) {ξ : ℝ}
    (h : ξ - (ℓ : ℝ) / 3 ∉ Set.Icc (1 / 10 : ℝ) (9 / 10)) : 𝓕 (wavePacket ρ v ℓ) ξ = 0 := by
  rw [fourier_wavePacket, hρ.1 _ h, mul_zero]

/-- **(b), support.** `c = 0` unless `ℓ₁ - ℓ₂ ∈ [21, 30]` and `ℓ₁ + ℓ₂ - ℓ₃ ∈ [-6, 3]`. -/
theorem coeff3_eq_zero {ρ : 𝓢(ℝ, ℂ)} (hρ : IsFrameWindow ρ) {M : ℝ} (hM : 1 < M) {ψ : ℝ → ℂ}
    (hψ : IsBandProfile M ψ) (v₁ v₂ v₃ ℓ₁ ℓ₂ ℓ₃ : ℤ)
    (h : ℓ₁ - ℓ₂ ∉ Set.Icc (21 : ℤ) 30 ∨ ℓ₁ + ℓ₂ - ℓ₃ ∉ Set.Icc (-6 : ℤ) 3) :
    coeff3 ρ ψ v₁ v₂ v₃ ℓ₁ ℓ₂ ℓ₃ = 0 := by
  rw [coeff3_eq_integral ρ hM hψ]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun z => ?_)
  by_contra hne
  have h1 : 𝓕 (wavePacket ρ v₁ ℓ₁) z.1 ≠ 0 := fun h0 => hne (by simp [h0])
  have h2 : 𝓕 (wavePacket ρ v₂ ℓ₂) z.2 ≠ 0 := fun h0 => hne (by simp [h0])
  have h3 : 𝓕 (wavePacket ρ v₃ ℓ₃) (z.1 + z.2) ≠ 0 := fun h0 => hne (by simp [h0])
  have h4 : 𝓕 ψ (z.1 - z.2) ≠ 0 := fun h0 => hne (by simp [h0])
  have m1 : z.1 - (ℓ₁ : ℝ) / 3 ∈ Set.Icc (1 / 10 : ℝ) (9 / 10) :=
    not_not.1 fun hn => h1 (fourier_wavePacket_eq_zero hρ _ _ hn)
  have m2 : z.2 - (ℓ₂ : ℝ) / 3 ∈ Set.Icc (1 / 10 : ℝ) (9 / 10) :=
    not_not.1 fun hn => h2 (fourier_wavePacket_eq_zero hρ _ _ hn)
  have m3 : z.1 + z.2 - (ℓ₃ : ℝ) / 3 ∈ Set.Icc (1 / 10 : ℝ) (9 / 10) :=
    not_not.1 fun hn => h3 (fourier_wavePacket_eq_zero hρ _ _ hn)
  have m4 : z.1 - z.2 ∈ Set.Icc (8 : ℝ) 9 := not_not.1 fun hn => h4 (hψ.fourier_supp _ hn)
  obtain ⟨a1, a2⟩ := m1
  obtain ⟨b1, b2⟩ := m2
  obtain ⟨c1, c2⟩ := m3
  obtain ⟨d1, d2⟩ := m4
  rcases h with h | h
  · apply h
    constructor
    · have : (21 : ℝ) ≤ ((ℓ₁ - ℓ₂ : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : ((ℓ₁ - ℓ₂ : ℤ) : ℝ) ≤ 30 := by push_cast; linarith
      exact_mod_cast this
  · apply h
    constructor
    · have : (-6 : ℝ) ≤ ((ℓ₁ + ℓ₂ - ℓ₃ : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : ((ℓ₁ + ℓ₂ - ℓ₃ : ℤ) : ℝ) ≤ 3 := by push_cast; linarith
      exact_mod_cast this

theorem exists_schwartz_decay (ρ : 𝓢(ℝ, ℂ)) (M : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℝ, ‖ρ s‖ ≤ A * wt M s := by
  set k : ℕ := ⌈M⌉₊ with hk
  set A : ℝ := 2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) ρ with hA
  refine ⟨A, by positivity, fun s => ?_⟩
  have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0)
    le_rfl le_rfl ρ s
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
  have hb : (1 : ℝ) ≤ 1 + |s| := by linarith [abs_nonneg s]
  have h2 : (1 + |s|) ^ M ≤ (1 + |s|) ^ k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hb (Nat.le_ceil M)
  have hpos : 0 < (1 + |s|) ^ M := Real.rpow_pos_of_pos (by linarith) _
  unfold wt
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖ρ s‖ * (1 + |s|) ^ M ≤ ‖ρ s‖ * (1 + |s|) ^ k := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = (1 + |s|) ^ k * ‖ρ s‖ := by ring
    _ ≤ A := h1

theorem exists_wavePacket_decay (ρ : 𝓢(ℝ, ℂ)) (M : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (v ℓ : ℤ) (t : ℝ), ‖wavePacket ρ v ℓ t‖ ≤ C * wt M (t - v) := by
  obtain ⟨A, hA0, hA⟩ := exists_schwartz_decay ρ M
  refine ⟨max 1 A, le_max_left _ _, fun v ℓ t => ?_⟩
  rw [norm_wavePacket]
  exact (hA _).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (wt_nonneg _ _))

theorem rpow_neg_quarter_le {N s : ℝ} (hN : 0 ≤ N) (hs : 0 ≤ s) :
    (1 + N / 4) ^ (-s) ≤ 4 ^ s * (1 + N) ^ (-s) := by
  have h1 : (1 + N) ≤ 4 * (1 + N / 4) := by linarith
  have h2 := rpow_neg_anti (by positivity : (0 : ℝ) < 1 + N) h1 hs
  rw [Real.mul_rpow (by norm_num) (by positivity)] at h2
  have h4 : (0 : ℝ) < 4 ^ s := Real.rpow_pos_of_pos (by norm_num) _
  have e : (4 : ℝ) ^ (-s) = (4 ^ s)⁻¹ := Real.rpow_neg (by norm_num) _
  rw [e] at h2
  rw [← div_le_iff₀' h4, div_eq_inv_mul]
  exact h2

/-- **(b), decay.** `|c| ≤ C_M (1+|n|)^{-(M-2)}`, `n = (v₁-v₃, v₂-v₃)`, `|n| = |n₁|+|n₂|`, with `C_M`
depending only on `M` and `ρ` (not on `ψ`, nor on the indices `ℓ_i`). -/
theorem norm_coeff3_le (ρ : 𝓢(ℝ, ℂ)) {M : ℝ} (hM : 2 < M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : ℝ → ℂ, IsBandProfile M ψ → ∀ v₁ v₂ v₃ ℓ₁ ℓ₂ ℓ₃ : ℤ,
      ‖coeff3 ρ ψ v₁ v₂ v₃ ℓ₁ ℓ₂ ℓ₃‖ ≤
        C * (1 + (|((v₁ - v₃ : ℤ) : ℝ)| + |((v₂ - v₃ : ℤ) : ℝ)|)) ^ (-(M - 2)) := by
  obtain ⟨Cρ, hC1, hρ⟩ := exists_wavePacket_decay ρ M
  have hC0 : 0 ≤ Cρ := by linarith
  refine ⟨Cρ ^ 4 * ((∫ t, wt 2 t) ^ 2 + (∫ t, wt M t) ^ 2) * 4 ^ (M - 2), ?_, ?_⟩
  · have h1 : 0 ≤ ∫ t, wt 2 t := integral_nonneg fun t => wt_nonneg _ _
    have h2 : 0 ≤ ∫ t, wt M t := integral_nonneg fun t => wt_nonneg _ _
    positivity
  intro ψ hψ v₁ v₂ v₃ ℓ₁ ℓ₂ ℓ₃
  have hb := norm_triple_integral_le (M := M) (C := Cρ) hM hC0 (v₁ : ℝ) (v₂ : ℝ) (v₃ : ℝ)
    (ψ := ψ) (f₁ := wavePacket ρ v₁ ℓ₁) (f₂ := wavePacket ρ v₂ ℓ₂) (f₃ := wavePacket ρ v₃ ℓ₃)
    (fun y => (hψ.decay y).trans (by
      calc (1 + |y|) ^ (-M) = 1 * wt M y := by simp [wt]
        _ ≤ Cρ * wt M y := mul_le_mul_of_nonneg_right hC1 (wt_nonneg _ _)))
    (hρ v₁ ℓ₁) (hρ v₂ ℓ₂) (hρ v₃ ℓ₃)
  have e : coeff3 ρ ψ v₁ v₂ v₃ ℓ₁ ℓ₂ ℓ₃ = ∫ x, (∫ y, wavePacket ρ v₁ ℓ₁ (x - y) *
      wavePacket ρ v₂ ℓ₂ (x + y) * ψ y) * (starRingEnd ℂ) (wavePacket ρ v₃ ℓ₃ x) := rfl
  rw [e]
  refine hb.trans ?_
  push_cast
  have hN : 0 ≤ |(v₁ : ℝ) - v₃| + |(v₂ : ℝ) - v₃| := by positivity
  have := rpow_neg_quarter_le hN (by linarith : 0 ≤ M - 2)
  have hI : 0 ≤ Cρ ^ 4 * ((∫ t, wt 2 t) ^ 2 + (∫ t, wt M t) ^ 2) := by
    have h1 : 0 ≤ ∫ t, wt 2 t := integral_nonneg fun t => wt_nonneg _ _
    have h2 : 0 ≤ ∫ t, wt M t := integral_nonneg fun t => wt_nonneg _ _
    positivity
  calc Cρ ^ 4 * ((∫ t, wt 2 t) ^ 2 + (∫ t, wt M t) ^ 2) *
        (1 + (|(v₁ : ℝ) - v₃| + |(v₂ : ℝ) - v₃|) / 4) ^ (-(M - 2))
      ≤ Cρ ^ 4 * ((∫ t, wt 2 t) ^ 2 + (∫ t, wt M t) ^ 2) *
        (4 ^ (M - 2) * (1 + (|(v₁ : ℝ) - v₃| + |(v₂ : ℝ) - v₃|)) ^ (-(M - 2))) :=
        mul_le_mul_of_nonneg_left this hI
    _ = _ := by ring

/-! ## (c) The representation -/

theorem summable_one_add_abs_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℤ => (1 + |(n : ℝ)|) ^ (-s)) := by
  refine Summable.of_norm_bounded_eventually (Real.summable_abs_int_rpow hs) ?_
  have : ∀ᶠ n : ℤ in Filter.cofinite, n ≠ 0 := by
    simpa using (Set.finite_singleton (0 : ℤ)).compl_mem_cofinite
  filter_upwards [this] with n hn
  have hn' : (0 : ℝ) < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact rpow_neg_anti hn' (by linarith) (by linarith)

/-- For fixed `(v₁, v₂, ℓ₁, ℓ₂)` the coefficients `c_{v₁v₂v₃ℓ₁ℓ₂ℓ₃}` are absolutely summable in
`(v₃, ℓ₃)`, with a total mass bounded uniformly in `(v₁, v₂, ℓ₁, ℓ₂)` and in `ψ`: only ten values
of `ℓ₃` contribute (by (b), support) and `|c| ≲ (1+|v₁-v₃|)^{-(M-2)}` (by (b), decay). -/
theorem summable_tsum_coeff3_le (ρ : 𝓢(ℝ, ℂ)) (hρ : IsFrameWindow ρ) {M : ℝ} (hM : 3 < M) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ ψ : ℝ → ℂ, IsBandProfile M ψ → ∀ v₁ v₂ ℓ₁ ℓ₂ : ℤ,
      Summable (fun p : ℤ × ℤ => ‖coeff3 ρ ψ v₁ v₂ p.1 ℓ₁ ℓ₂ p.2‖) ∧
      ∑' p : ℤ × ℤ, ‖coeff3 ρ ψ v₁ v₂ p.1 ℓ₁ ℓ₂ p.2‖ ≤ U := by
  obtain ⟨C, hC0, hC⟩ := norm_coeff3_le ρ (by linarith : 2 < M)
  have h0 := summable_one_add_abs_rpow (s := M - 2) (by linarith)
  refine ⟨C * (∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-(M - 2))) * 10, by
    have : 0 ≤ ∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-(M - 2)) := tsum_nonneg fun n => by positivity
    positivity, ?_⟩
  intro ψ hψ v₁ v₂ ℓ₁ ℓ₂
  set g1 : ℤ → ℝ := fun v₃ => C * (1 + |((v₁ - v₃ : ℤ) : ℝ)|) ^ (-(M - 2)) with hg1
  set g2 : ℤ → ℝ := fun ℓ₃ => if ℓ₃ ∈ Finset.Icc (ℓ₁ + ℓ₂ - 3) (ℓ₁ + ℓ₂ + 6) then 1 else 0 with hg2
  have hs1 : Summable g1 := by
    have h1 : Summable (fun v₃ : ℤ => (1 + |((v₁ - v₃ : ℤ) : ℝ)|) ^ (-(M - 2))) :=
      (Equiv.summable_iff (f := fun n : ℤ => (1 + |(n : ℝ)|) ^ (-(M - 2))) (Equiv.subLeft v₁)).2 h0
    exact h1.mul_left C
  have hs2 : Summable g2 := summable_of_ne_finset_zero (s := Finset.Icc (ℓ₁ + ℓ₂ - 3) (ℓ₁ + ℓ₂ + 6))
    (fun ℓ₃ hn => by rw [hg2]; simp only [hn, ↓reduceIte])
  have hprod := Summable.mul_of_nonneg hs1 hs2
    (fun v => by simp only [hg1]; positivity) (fun l => by simp only [hg2]; split_ifs <;> norm_num)
  have hle : ∀ p : ℤ × ℤ, ‖coeff3 ρ ψ v₁ v₂ p.1 ℓ₁ ℓ₂ p.2‖ ≤ g1 p.1 * g2 p.2 := by
    rintro ⟨v₃, ℓ₃⟩
    simp only [hg1, hg2]
    by_cases hmem : ℓ₃ ∈ Finset.Icc (ℓ₁ + ℓ₂ - 3) (ℓ₁ + ℓ₂ + 6)
    · simp only [hmem, ↓reduceIte, mul_one]
      refine (hC ψ hψ v₁ v₂ v₃ ℓ₁ ℓ₂ ℓ₃).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hC0
      refine rpow_neg_anti (by positivity) ?_ (by linarith)
      have : 0 ≤ |((v₂ - v₃ : ℤ) : ℝ)| := abs_nonneg _
      linarith
    · simp only [hmem, ↓reduceIte, mul_zero]
      have : coeff3 ρ ψ v₁ v₂ v₃ ℓ₁ ℓ₂ ℓ₃ = 0 := by
        refine coeff3_eq_zero hρ (by linarith) hψ _ _ _ _ _ _ (Or.inr ?_)
        intro hb
        apply hmem
        simp only [Set.mem_Icc] at hb
        simp only [Finset.mem_Icc]
        constructor <;> linarith [hb.1, hb.2]
      rw [this]; simp
  have hsum : Summable (fun p : ℤ × ℤ => ‖coeff3 ρ ψ v₁ v₂ p.1 ℓ₁ ℓ₂ p.2‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) hle hprod
  refine ⟨hsum, ?_⟩
  calc ∑' p : ℤ × ℤ, ‖coeff3 ρ ψ v₁ v₂ p.1 ℓ₁ ℓ₂ p.2‖ ≤ ∑' p : ℤ × ℤ, g1 p.1 * g2 p.2 :=
        hsum.tsum_le_tsum hle hprod
    _ = (∑' v₃, g1 v₃) * ∑' ℓ₃, g2 ℓ₃ := (hs1.tsum_mul_tsum hs2 hprod).symm
    _ = C * (∑' n : ℤ, (1 + |(n : ℝ)|) ^ (-(M - 2))) * 10 := by
        congr 1
        · simp only [hg1]
          rw [tsum_mul_left]
          congr 1
          exact (Equiv.subLeft v₁).tsum_eq (fun n : ℤ => (1 + |(n : ℝ)|) ^ (-(M - 2)))
        · rw [tsum_eq_sum (s := Finset.Icc (ℓ₁ + ℓ₂ - 3) (ℓ₁ + ℓ₂ + 6))
            (fun ℓ₃ hn => by rw [hg2]; simp only [hn, ↓reduceIte])]
          simp only [hg2, Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, Int.card_Icc]
          have : (ℓ₁ + ℓ₂ + 6 + 1 - (ℓ₁ + ℓ₂ - 3)).toNat = 10 := by omega
          rw [this]
          norm_num

theorem summable_coeff3 (ρ : 𝓢(ℝ, ℂ)) (hρ : IsFrameWindow ρ) {M : ℝ} (hM : 3 < M) {ψ : ℝ → ℂ}
    (hψ : IsBandProfile M ψ) (v₁ v₂ ℓ₁ ℓ₂ : ℤ) :
    Summable (fun p : ℤ × ℤ => ‖coeff3 ρ ψ v₁ v₂ p.1 ℓ₁ ℓ₂ p.2‖) :=
  (summable_tsum_coeff3_le ρ hρ hM).choose_spec.2 ψ hψ v₁ v₂ ℓ₁ ℓ₂ |>.1

section Frame

variable (ρ : 𝓢(ℝ, ℂ)) {M : ℝ} {ψ : ℝ → ℂ}

theorem coeff3_eq_coeffF (hM : 1 < M) (hψ : IsBandProfile M ψ) (v₁ v₂ ℓ₁ ℓ₂ v₃ ℓ₃ : ℤ) :
    coeff3 ρ ψ v₁ v₂ v₃ ℓ₁ ℓ₂ ℓ₃ =
      coeffF ρ (bilinDensity (𝓕 (wavePacket ρ v₁ ℓ₁)) (𝓕 (wavePacket ρ v₂ ℓ₂)) (𝓕 ψ)) v₃ ℓ₃ := by
  have hψi := hψ.integrable hM
  have hΨc := continuous_fourier_of_integrable hψi
  have hΨb : ∀ t, ‖𝓕 ψ t‖ ≤ ∫ v, ‖ψ v‖ := fun t => Real.norm_fourier_le_integral_norm ψ t
  have hb₂ : ∀ t, ‖𝓕 (wavePacket ρ v₂ ℓ₂) t‖ ≤ ∫ v, ‖wavePacket ρ v₂ ℓ₂ v‖ :=
    fun t => Real.norm_fourier_le_integral_norm _ t
  have hGi := integrable_bilinDensity (integrable_fourier_wavePacket ρ v₁ ℓ₁)
    (integrable_fourier_wavePacket ρ v₂ ℓ₂) hΨc hΨb
  have hGc := continuous_bilinDensity (integrable_fourier_wavePacket ρ v₁ ℓ₁)
    (continuous_fourier_wavePacket ρ v₂ ℓ₂) hΨc hb₂ hΨb
  have hB := fun x => bilinB1_eq_integral_density (continuous_fourier_wavePacket ρ v₁ ℓ₁)
    (continuous_fourier_wavePacket ρ v₂ ℓ₂) (integrable_fourier_wavePacket ρ v₁ ℓ₁)
    (integrable_fourier_wavePacket ρ v₂ ℓ₂) (fun t => (fourierInv_wavePacket ρ v₁ ℓ₁ t).symm)
    (fun t => (fourierInv_wavePacket ρ v₂ ℓ₂ t).symm) hψi x
  unfold coeff3 pairing
  simp_rw [hB]
  rw [integral_fourierInv_mul_conj hGc hGi (continuous_wavePacket ρ v₃ ℓ₃)
    (integrable_wavePacket ρ v₃ ℓ₃)]
  unfold coeffF
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  beta_reduce
  rw [fourier_wavePacket, map_mul, conj_ePhase, neg_neg]
  ring

/-- The frame identity for `B_1(ψ, ψ_{v₁ℓ₁}, ψ_{v₂ℓ₂})` (which is not known to be Schwartz): it is
`∑_{v₃,ℓ₃} c_{v₁v₂v₃ℓ₁ℓ₂ℓ₃} ψ_{v₃ℓ₃}(x)`. -/
theorem hasSum_frame_bilinB1 (hρ : IsFrameWindow ρ) (hM : 3 < M) (hψ : IsBandProfile M ψ)
    (v₁ v₂ ℓ₁ ℓ₂ : ℤ) (x : ℝ) :
    HasSum (fun p : ℤ × ℤ => coeff3 ρ ψ v₁ v₂ p.1 ℓ₁ ℓ₂ p.2 * wavePacket ρ p.1 p.2 x)
      (bilinB1 ψ (wavePacket ρ v₁ ℓ₁) (wavePacket ρ v₂ ℓ₂) x) := by
  have hM1 : 1 < M := by linarith
  have hψi := hψ.integrable hM1
  have hΨc := continuous_fourier_of_integrable hψi
  have hΨb : ∀ t, ‖𝓕 ψ t‖ ≤ ∫ v, ‖ψ v‖ := fun t => Real.norm_fourier_le_integral_norm ψ t
  have hb₂ : ∀ t, ‖𝓕 (wavePacket ρ v₂ ℓ₂) t‖ ≤ ∫ v, ‖wavePacket ρ v₂ ℓ₂ v‖ :=
    fun t => Real.norm_fourier_le_integral_norm _ t
  have hGc := continuous_bilinDensity (integrable_fourier_wavePacket ρ v₁ ℓ₁)
    (continuous_fourier_wavePacket ρ v₂ ℓ₂) hΨc hb₂ hΨb
  have hs := summable_coeff3 ρ hρ hM hψ v₁ v₂ ℓ₁ ℓ₂
  have e : ∀ p : ℤ × ℤ, coeff3 ρ ψ v₁ v₂ p.1 ℓ₁ ℓ₂ p.2 =
      coeffF ρ (bilinDensity (𝓕 (wavePacket ρ v₁ ℓ₁)) (𝓕 (wavePacket ρ v₂ ℓ₂)) (𝓕 ψ)) p.1 p.2 :=
    fun p => coeff3_eq_coeffF ρ hM1 hψ v₁ v₂ ℓ₁ ℓ₂ p.1 p.2
  simp_rw [e] at hs ⊢
  have h := hasSum_frame_of_fourier ρ hρ hGc hs x
  rw [← bilinB1_eq_integral_density (continuous_fourier_wavePacket ρ v₁ ℓ₁)
    (continuous_fourier_wavePacket ρ v₂ ℓ₂) (integrable_fourier_wavePacket ρ v₁ ℓ₁)
    (integrable_fourier_wavePacket ρ v₂ ℓ₂) (fun t => (fourierInv_wavePacket ρ v₁ ℓ₁ t).symm)
    (fun t => (fourierInv_wavePacket ρ v₂ ℓ₂ t).symm) hψi x] at h
  exact h

/-- Expansion of `B_1(ψ, f₁, f₂)` in the products of the frame expansions of `f₁` and `f₂`. -/
theorem hasSum_bilinB1_expansion (hρ : IsFrameWindow ρ) (hM : 1 < M) (hψ : IsBandProfile M ψ)
    (f₁ f₂ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasSum (fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
      pairing (f₁ : ℝ → ℂ) (wavePacket ρ q.1.1 q.1.2) * pairing (f₂ : ℝ → ℂ) (wavePacket ρ q.2.1 q.2.2) *
        bilinB1 ψ (wavePacket ρ q.1.1 q.1.2) (wavePacket ρ q.2.1 q.2.2) x)
      (bilinB1 ψ f₁ f₂ x) := by
  obtain ⟨R, hR0, hR⟩ := exists_norm_le ρ
  have hψi := hψ.integrable hM
  set c₁ : ℤ × ℤ → ℂ := fun p => pairing (f₁ : ℝ → ℂ) (wavePacket ρ p.1 p.2) with hc₁
  set c₂ : ℤ × ℤ → ℂ := fun p => pairing (f₂ : ℝ → ℂ) (wavePacket ρ p.1 p.2) with hc₂
  have hs₁ : Summable (fun p => ‖c₁ p‖) := summable_pairing_wavePacket ρ hρ f₁
  have hs₂ : Summable (fun p => ‖c₂ p‖) := summable_pairing_wavePacket ρ hρ f₂
  set F : (ℤ × ℤ) × (ℤ × ℤ) → ℝ → ℂ := fun q y =>
    (c₁ q.1 * wavePacket ρ q.1.1 q.1.2 (x - y)) * (c₂ q.2 * wavePacket ρ q.2.1 q.2.2 (x + y)) * ψ y
    with hF
  have hbound : ∀ q y, ‖F q y‖ ≤ ‖c₁ q.1‖ * ‖c₂ q.2‖ * R ^ 2 * ‖ψ y‖ := by
    intro q y
    simp only [hF, norm_mul]
    have h1 : ‖wavePacket ρ q.1.1 q.1.2 (x - y)‖ ≤ R := by
      rw [norm_wavePacket]; exact hR _
    have h2 : ‖wavePacket ρ q.2.1 q.2.2 (x + y)‖ ≤ R := by
      rw [norm_wavePacket]; exact hR _
    calc ‖c₁ q.1‖ * ‖wavePacket ρ q.1.1 q.1.2 (x - y)‖ *
          (‖c₂ q.2‖ * ‖wavePacket ρ q.2.1 q.2.2 (x + y)‖) * ‖ψ y‖
        ≤ ‖c₁ q.1‖ * R * (‖c₂ q.2‖ * R) * ‖ψ y‖ := by gcongr
      _ = _ := by ring
  have hFint : ∀ q, Integrable (F q) := by
    intro q
    refine (hψi.norm.const_mul (‖c₁ q.1‖ * ‖c₂ q.2‖ * R ^ 2)).mono' ?_
      (Filter.Eventually.of_forall fun y => (hbound q y).trans (le_of_eq (by ring)))
    have c1 : Continuous (fun y : ℝ => (c₁ q.1 * wavePacket ρ q.1.1 q.1.2 (x - y)) *
        (c₂ q.2 * wavePacket ρ q.2.1 q.2.2 (x + y))) := by
      have h1 := continuous_wavePacket ρ q.1.1 q.1.2
      have h2 := continuous_wavePacket ρ q.2.1 q.2.2
      fun_prop
    exact c1.aestronglyMeasurable.mul hψ.aesm
  have hnorm : Summable (fun q : (ℤ × ℤ) × (ℤ × ℤ) => ∫ y, ‖F q y‖) := by
    refine Summable.of_nonneg_of_le (fun q => integral_nonneg fun y => norm_nonneg _) (fun q => ?_)
      (((Summable.mul_of_nonneg hs₁ hs₂ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_right
        (R ^ 2 * ∫ y, ‖ψ y‖)))
    calc ∫ y, ‖F q y‖ ≤ ∫ y, ‖c₁ q.1‖ * ‖c₂ q.2‖ * R ^ 2 * ‖ψ y‖ :=
          integral_mono (hFint q).norm (hψi.norm.const_mul _) (fun y => hbound q y)
      _ = _ := by rw [integral_const_mul]; ring
  have h := hasSum_integral_of_summable_integral_norm hFint hnorm
  have h1 : ∀ q : (ℤ × ℤ) × (ℤ × ℤ), ∫ y, F q y =
      pairing (f₁ : ℝ → ℂ) (wavePacket ρ q.1.1 q.1.2) * pairing (f₂ : ℝ → ℂ) (wavePacket ρ q.2.1 q.2.2) *
        bilinB1 ψ (wavePacket ρ q.1.1 q.1.2) (wavePacket ρ q.2.1 q.2.2) x := by
    intro q
    unfold bilinB1
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hF, hc₁, hc₂]
    ring
  have h2 : ∀ y, ∑' q : (ℤ × ℤ) × (ℤ × ℤ), F q y = f₁ (x - y) * f₂ (x + y) * ψ y := by
    intro y
    have a1 := hasSum_frame ρ hρ f₁ (x - y)
    have a2 := hasSum_frame ρ hρ f₂ (x + y)
    have hsum : Summable (fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
        (c₁ q.1 * wavePacket ρ q.1.1 q.1.2 (x - y)) * (c₂ q.2 * wavePacket ρ q.2.1 q.2.2 (x + y))) := by
      refine Summable.of_norm ?_
      simp only [norm_mul]
      exact Summable.mul_of_nonneg (f := fun p : ℤ × ℤ => ‖c₁ p‖ * ‖wavePacket ρ p.1 p.2 (x - y)‖)
        (g := fun p : ℤ × ℤ => ‖c₂ p‖ * ‖wavePacket ρ p.1 p.2 (x + y)‖)
        (by simpa [norm_mul] using summable_norm_frame ρ hρ f₁ (x - y))
        (by simpa [norm_mul] using summable_norm_frame ρ hρ f₂ (x + y))
        (fun _ => by positivity) (fun _ => by positivity)
    have a3 := (a1.mul a2 hsum).mul_right (ψ y)
    exact a3.tsum_eq
  simp_rw [h1, h2] at h
  exact h

/-- The triple family `⟨f₁, ψ_{p₁}⟩ ⟨f₂, ψ_{p₂}⟩ c_{p₁p₂p₃} ψ_{p₃}(x)`, summed over `p₁, p₂, p₃ ∈ ℤ × ℤ`. -/
theorem hasSum_triple (hρ : IsFrameWindow ρ) (hM : 3 < M) (hψ : IsBandProfile M ψ)
    (f₁ f₂ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasSum (fun r : ((ℤ × ℤ) × (ℤ × ℤ)) × (ℤ × ℤ) =>
      pairing (f₁ : ℝ → ℂ) (wavePacket ρ r.1.1.1 r.1.1.2) *
        pairing (f₂ : ℝ → ℂ) (wavePacket ρ r.1.2.1 r.1.2.2) *
        coeff3 ρ ψ r.1.1.1 r.1.2.1 r.2.1 r.1.1.2 r.1.2.2 r.2.2 * wavePacket ρ r.2.1 r.2.2 x)
      (bilinB1 ψ f₁ f₂ x) := by
  have hM1 : 1 < M := by linarith
  obtain ⟨R, hR0, hR⟩ := exists_norm_le ρ
  obtain ⟨U, hU0, hU⟩ := summable_tsum_coeff3_le ρ hρ hM
  set c₁ : ℤ × ℤ → ℂ := fun p => pairing (f₁ : ℝ → ℂ) (wavePacket ρ p.1 p.2) with hc₁
  set c₂ : ℤ × ℤ → ℂ := fun p => pairing (f₂ : ℝ → ℂ) (wavePacket ρ p.1 p.2) with hc₂
  have hs₁ : Summable (fun p => ‖c₁ p‖) := summable_pairing_wavePacket ρ hρ f₁
  have hs₂ : Summable (fun p => ‖c₂ p‖) := summable_pairing_wavePacket ρ hρ f₂
  set T : ((ℤ × ℤ) × (ℤ × ℤ)) × (ℤ × ℤ) → ℂ := fun r =>
    c₁ r.1.1 * c₂ r.1.2 * coeff3 ρ ψ r.1.1.1 r.1.2.1 r.2.1 r.1.1.2 r.1.2.2 r.2.2 *
      wavePacket ρ r.2.1 r.2.2 x with hT
  have hTb : ∀ q p₃, ‖T (q, p₃)‖ ≤ (‖c₁ q.1‖ * ‖c₂ q.2‖ * R) *
      ‖coeff3 ρ ψ q.1.1 q.2.1 p₃.1 q.1.2 q.2.2 p₃.2‖ := by
    intro q p₃
    simp only [hT, norm_mul]
    have : ‖wavePacket ρ p₃.1 p₃.2 x‖ ≤ R := by rw [norm_wavePacket]; exact hR _
    calc ‖c₁ q.1‖ * ‖c₂ q.2‖ * ‖coeff3 ρ ψ q.1.1 q.2.1 p₃.1 q.1.2 q.2.2 p₃.2‖ *
          ‖wavePacket ρ p₃.1 p₃.2 x‖
        ≤ ‖c₁ q.1‖ * ‖c₂ q.2‖ * ‖coeff3 ρ ψ q.1.1 q.2.1 p₃.1 q.1.2 q.2.2 p₃.2‖ * R :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have hfiber : ∀ q : (ℤ × ℤ) × (ℤ × ℤ), Summable (fun p₃ => ‖T (q, p₃)‖) := fun q =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p₃ => hTb q p₃)
      ((summable_coeff3 ρ hρ hM hψ q.1.1 q.2.1 q.1.2 q.2.2).mul_left _)
  have hout : Summable (fun q : (ℤ × ℤ) × (ℤ × ℤ) => ∑' p₃, ‖T (q, p₃)‖) := by
    refine Summable.of_nonneg_of_le (fun q => tsum_nonneg fun _ => norm_nonneg _) (fun q => ?_)
      ((Summable.mul_of_nonneg hs₁ hs₂ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_right
        (R * U))
    calc ∑' p₃, ‖T (q, p₃)‖
        ≤ ∑' p₃ : ℤ × ℤ, (‖c₁ q.1‖ * ‖c₂ q.2‖ * R) *
            ‖coeff3 ρ ψ q.1.1 q.2.1 p₃.1 q.1.2 q.2.2 p₃.2‖ :=
          (hfiber q).tsum_le_tsum (fun p₃ => hTb q p₃)
            ((summable_coeff3 ρ hρ hM hψ q.1.1 q.2.1 q.1.2 q.2.2).mul_left _)
      _ = (‖c₁ q.1‖ * ‖c₂ q.2‖ * R) * ∑' p₃ : ℤ × ℤ,
            ‖coeff3 ρ ψ q.1.1 q.2.1 p₃.1 q.1.2 q.2.2 p₃.2‖ := tsum_mul_left
      _ ≤ (‖c₁ q.1‖ * ‖c₂ q.2‖ * R) * U :=
          mul_le_mul_of_nonneg_left (hU ψ hψ q.1.1 q.2.1 q.1.2 q.2.2).2 (by positivity)
      _ = _ := by ring
  have hTs : Summable T := by
    refine Summable.of_norm ?_
    exact (summable_prod_of_nonneg (f := fun r => ‖T r‖) (fun _ => norm_nonneg _)).2 ⟨hfiber, hout⟩
  have hfib : ∀ q : (ℤ × ℤ) × (ℤ × ℤ), HasSum (fun p₃ : ℤ × ℤ => T (q, p₃))
      (c₁ q.1 * c₂ q.2 * bilinB1 ψ (wavePacket ρ q.1.1 q.1.2) (wavePacket ρ q.2.1 q.2.2) x) := by
    intro q
    have := (hasSum_frame_bilinB1 ρ hρ hM hψ q.1.1 q.2.1 q.1.2 q.2.2 x).mul_left (c₁ q.1 * c₂ q.2)
    convert this using 1
    funext p₃
    simp only [hT]
    ring
  have hA := hasSum_bilinB1_expansion ρ hρ hM1 hψ f₁ f₂ x
  have hg := hTs.hasSum.prod_fiberwise hfib
  have heq : ∑' r, T r = bilinB1 ψ f₁ f₂ x := hg.unique hA
  rw [← heq]
  exact hTs.hasSum

/-- The summand of (c): `⟨f₁, ψ_{v+n₁,ℓ}⟩ ⟨f₂, ψ_{v+n₂,ℓ-a}⟩ c_{n,v,ℓ,a,b} ψ_{v,2ℓ-a-b}(x)`, with
`c_{n,v,ℓ,a,b} = c_{v+n₁, v+n₂, v, ℓ, ℓ-a, 2ℓ-a-b}`. -/
def repTerm (ρ : 𝓢(ℝ, ℂ)) (ψ f₁ f₂ : ℝ → ℂ) (x : ℝ) (a b n₁ n₂ v ℓ : ℤ) : ℂ :=
  pairing f₁ (wavePacket ρ (v + n₁) ℓ) * pairing f₂ (wavePacket ρ (v + n₂) (ℓ - a)) *
    coeff3 ρ ψ (v + n₁) (v + n₂) v ℓ (ℓ - a) (2 * ℓ - a - b) * wavePacket ρ v (2 * ℓ - a - b) x

/-- The coefficient `c_{n,v,ℓ,a,b} := c_{v+n₁, v+n₂, v, ℓ, ℓ-a, 2ℓ-a-b}` of (c). -/
def coeffRep (ρ : 𝓢(ℝ, ℂ)) (ψ : ℝ → ℂ) (a b n₁ n₂ v ℓ : ℤ) : ℂ :=
  coeff3 ρ ψ (v + n₁) (v + n₂) v ℓ (ℓ - a) (2 * ℓ - a - b)

/-- The reindexing `(a, b, n₁, n₂, v, ℓ) ↦ ((v+n₁, ℓ), (v+n₂, ℓ-a)), (v, 2ℓ-a-b)`. -/
def repEquiv : (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) ≃ ((ℤ × ℤ) × (ℤ × ℤ)) × (ℤ × ℤ) where
  toFun q := (((q.2.2.2.2.1 + q.2.2.1, q.2.2.2.2.2), (q.2.2.2.2.1 + q.2.2.2.1, q.2.2.2.2.2 - q.1)),
    (q.2.2.2.2.1, 2 * q.2.2.2.2.2 - q.1 - q.2.1))
  invFun r := (r.1.1.2 - r.1.2.2, r.1.1.2 + r.1.2.2 - r.2.2, r.1.1.1 - r.2.1, r.1.2.1 - r.2.1,
    r.2.1, r.1.1.2)
  left_inv := by
    rintro ⟨a, b, n₁, n₂, v, ℓ⟩
    simp only [Prod.mk.injEq, and_true]
    omega
  right_inv := by
    rintro ⟨⟨⟨v₁, ℓ₁⟩, ⟨v₂, ℓ₂⟩⟩, ⟨v₃, ℓ₃⟩⟩
    simp only [Prod.mk.injEq, and_true, true_and]
    omega

theorem repTerm_eq_zero (hρ : IsFrameWindow ρ) (hM : 1 < M) (hψ : IsBandProfile M ψ)
    (f₁ f₂ : ℝ → ℂ) (x : ℝ) (a b n₁ n₂ v ℓ : ℤ)
    (h : a ∉ Set.Icc (21 : ℤ) 30 ∨ b ∉ Set.Icc (-6 : ℤ) 3) :
    repTerm ρ ψ f₁ f₂ x a b n₁ n₂ v ℓ = 0 := by
  unfold repTerm
  have : coeff3 ρ ψ (v + n₁) (v + n₂) v ℓ (ℓ - a) (2 * ℓ - a - b) = 0 := by
    refine coeff3_eq_zero hρ hM hψ _ _ _ _ _ _ ?_
    have e1 : ℓ - (ℓ - a) = a := by ring
    have e2 : ℓ + (ℓ - a) - (2 * ℓ - a - b) = b := by ring
    rw [e1, e2]
    exact h
  rw [this]; simp

/-- **Decay of the coefficients of (c)** (used for the weights `w_n` of (d)):
`|c_{n,v,ℓ,a,b}| ≤ C_M (1+|n₁|+|n₂|)^{-(M-2)}`, `C_M` depending on `M, ρ` only. -/
theorem exists_norm_coeffRep_le (hM : 2 < M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : ℝ → ℂ, IsBandProfile M ψ → ∀ a b n₁ n₂ v ℓ : ℤ,
      ‖coeffRep ρ ψ a b n₁ n₂ v ℓ‖ ≤ C * (1 + (|(n₁ : ℝ)| + |(n₂ : ℝ)|)) ^ (-(M - 2)) := by
  obtain ⟨C, hC0, hC⟩ := norm_coeff3_le ρ hM
  refine ⟨C, hC0, fun ψ hψ a b n₁ n₂ v ℓ => ?_⟩
  have := hC ψ hψ (v + n₁) (v + n₂) v ℓ (ℓ - a) (2 * ℓ - a - b)
  simpa only [coeffRep, add_sub_cancel_left] using this

/-- **(c), representation, full form.** The six-fold family
`(a, b, n₁, n₂, v, ℓ) ↦ ⟨f₁,ψ_{v+n₁,ℓ}⟩⟨f₂,ψ_{v+n₂,ℓ-a}⟩ c_{n,v,ℓ,a,b} ψ_{v,2ℓ-a-b}(x)` over `ℤ⁶` is
absolutely summable (for each `x`) with sum `B_1(ψ, f₁, f₂)(x)`; the terms vanish unless
`a ∈ [21, 30]` and `b ∈ [-6, 3]` (`repTerm_eq_zero`). -/
theorem hasSum_representation (hρ : IsFrameWindow ρ) (hM : 3 < M) (hψ : IsBandProfile M ψ)
    (f₁ f₂ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasSum (fun q : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ =>
      repTerm ρ ψ f₁ f₂ x q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2)
      (bilinB1 ψ f₁ f₂ x) :=
  (Equiv.hasSum_iff (f := fun r : ((ℤ × ℤ) × (ℤ × ℤ)) × (ℤ × ℤ) =>
    pairing (f₁ : ℝ → ℂ) (wavePacket ρ r.1.1.1 r.1.1.2) *
      pairing (f₂ : ℝ → ℂ) (wavePacket ρ r.1.2.1 r.1.2.2) *
      coeff3 ρ ψ r.1.1.1 r.1.2.1 r.2.1 r.1.1.2 r.1.2.2 r.2.2 * wavePacket ρ r.2.1 r.2.2 x)
    repEquiv).2 (hasSum_triple ρ hρ hM hψ f₁ f₂ x)

end Frame

end PrimeBHT.TimeFrequency.RealLine
