module

public import PrimeBHT.TimeFrequency.X2.TopSelect
public import PrimeBHT.TimeFrequency.X2.EngTail.Top
public import PrimeBHT.TimeFrequency.X2.ModelOpTools
public import PrimeBHT.TimeFrequency.X2.Ortho.Fourier

/-!
# X2, node V12-top: one-sided top multipliers and the `±` split

* `partPlus ζ m = 1_{η > ζ} m`, `partMinus ζ m = 1_{η < ζ} m`: since a top multiplier vanishes in the hole around
  `ζ = ξ f_k`, they are smooth and locally equal to `m` or to `0`; their derivatives are those of `m` (or `0`), so the
  class constant does NOT change (no smooth cutoff is needed);
* `InTopMultS σ`: one-sided top multipliers (`σ = 1`: supported on `η > ξ f_k`; `σ = -1`: on `η < ξ f_k`);
* the shell `[shellLo σ, shellUp σ]` (the Fourier support), centre `shellC σ`, and `InTopMultS.inMult`: a one-sided top
  multiplier is a multiplier of the class `{𝔭 with β := 12}` centred in the middle of its shell;
* `tmult_add_mult`: `T_{m₁ + m₂} = T_{m₁} + T_{m₂}`;
* `valS σ`: the `σ`-side value of a top datum (`≤ topOpNorm`), and `topOpNorm_le_valS_add`:
  `topOpNorm ≤ valS 1 + valS (-1)` (Hilbert slots `q = 2`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform ComplexConjugate ContDiff Real
open PrimeBHT.TimeFrequency.Tile PrimeBHT.Statements

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-! ## The two parts of a top multiplier -/

/-- The part of `m` on `η > ζ`. -/
def partPlus (ζ : ℝ) (m : ℝ → ℂ) : ℝ → ℂ := fun η => if ζ < η then m η else 0

/-- The part of `m` on `η < ζ`. -/
def partMinus (ζ : ℝ) (m : ℝ → ℂ) : ℝ → ℂ := fun η => if η < ζ then m η else 0

theorem partPlus_add_partMinus {ζ : ℝ} {m : ℝ → ℂ} {h : ℝ} (hm : ∀ η, |η - ζ| < h → m η = 0) (hh : 0 < h)
    (η : ℝ) : partPlus ζ m η + partMinus ζ m η = m η := by
  unfold partPlus partMinus
  rcases lt_trichotomy ζ η with h1 | h1 | h1
  · simp [h1, not_lt.2 h1.le]
  · subst h1
    have := hm ζ (by simpa using hh)
    simp [this]
  · simp [h1, not_lt.2 h1.le]

/-- Local description of `partPlus`: it equals `m` on `(ζ - h/2, ∞)` and `0` on `(-∞, ζ + h/2)`. -/
theorem partPlus_eq_on {ζ : ℝ} {m : ℝ → ℂ} {h : ℝ} (hm : ∀ η, |η - ζ| < h → m η = 0) (hh : 0 < h) :
    (∀ η, ζ - h / 2 < η → partPlus ζ m η = m η) ∧ (∀ η, η < ζ + h / 2 → partPlus ζ m η = 0) := by
  constructor
  · intro η hη
    unfold partPlus
    by_cases hc : ζ < η
    · simp [hc]
    · rw [ite_eq_right hc]
      symm
      refine hm η ?_
      rw [abs_lt]; constructor <;> linarith [not_lt.1 hc]
  · intro η hη
    unfold partPlus
    by_cases hc : ζ < η
    · rw [ite_eq_left hc]
      refine hm η ?_
      rw [abs_lt]; constructor <;> linarith
    · rw [ite_eq_right hc]

theorem partMinus_eq_on {ζ : ℝ} {m : ℝ → ℂ} {h : ℝ} (hm : ∀ η, |η - ζ| < h → m η = 0) (hh : 0 < h) :
    (∀ η, η < ζ + h / 2 → partMinus ζ m η = m η) ∧ (∀ η, ζ - h / 2 < η → partMinus ζ m η = 0) := by
  constructor
  · intro η hη
    unfold partMinus
    by_cases hc : η < ζ
    · simp [hc]
    · rw [ite_eq_right hc]
      symm
      refine hm η ?_
      rw [abs_lt]; constructor <;> linarith [not_lt.1 hc]
  · intro η hη
    unfold partMinus
    by_cases hc : η < ζ
    · rw [ite_eq_left hc]
      refine hm η ?_
      rw [abs_lt]; constructor <;> linarith
    · rw [ite_eq_right hc]

/-- `partPlus` / `partMinus` are smooth and their iterated derivatives are those of `m` or `0`. -/
theorem contDiff_partPlus {ζ : ℝ} {m : ℝ → ℂ} {h : ℝ} (hm : ∀ η, |η - ζ| < h → m η = 0) (hh : 0 < h)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) m) : ContDiff ℝ (⊤ : ℕ∞) (partPlus ζ m) := by
  obtain ⟨h1, h2⟩ := partPlus_eq_on hm hh
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : ζ - h / 2 < x
  · refine (hsm.contDiffAt (x := x)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with η hη using h1 η hη
  · have hx' : x < ζ + h / 2 := by linarith [not_lt.1 hx]
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx'] with η hη using h2 η hη

theorem contDiff_partMinus {ζ : ℝ} {m : ℝ → ℂ} {h : ℝ} (hm : ∀ η, |η - ζ| < h → m η = 0) (hh : 0 < h)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) m) : ContDiff ℝ (⊤ : ℕ∞) (partMinus ζ m) := by
  obtain ⟨h1, h2⟩ := partMinus_eq_on hm hh
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x < ζ + h / 2
  · refine (hsm.contDiffAt (x := x)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with η hη using h1 η hη
  · have hx' : ζ - h / 2 < x := by linarith [not_lt.1 hx]
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx'] with η hη using h2 η hη

theorem norm_iteratedDeriv_partPlus_le {ζ : ℝ} {m : ℝ → ℂ} {h : ℝ} (hm : ∀ η, |η - ζ| < h → m η = 0)
    (hh : 0 < h) (k : ℕ) (η : ℝ) : ‖iteratedDeriv k (partPlus ζ m) η‖ ≤ ‖iteratedDeriv k m η‖ := by
  obtain ⟨h1, h2⟩ := partPlus_eq_on hm hh
  by_cases hx : ζ - h / 2 < η
  · have : partPlus ζ m =ᶠ[𝓝 η] m := by
      filter_upwards [Ioi_mem_nhds hx] with t ht using h1 t ht
    rw [this.iteratedDeriv_eq k]
  · have hx' : η < ζ + h / 2 := by linarith [not_lt.1 hx]
    have : partPlus ζ m =ᶠ[𝓝 η] fun _ => (0 : ℂ) := by
      filter_upwards [Iio_mem_nhds hx'] with t ht using h2 t ht
    rw [this.iteratedDeriv_eq k, iteratedDeriv_const]
    split_ifs <;> simp

theorem norm_iteratedDeriv_partMinus_le {ζ : ℝ} {m : ℝ → ℂ} {h : ℝ} (hm : ∀ η, |η - ζ| < h → m η = 0)
    (hh : 0 < h) (k : ℕ) (η : ℝ) : ‖iteratedDeriv k (partMinus ζ m) η‖ ≤ ‖iteratedDeriv k m η‖ := by
  obtain ⟨h1, h2⟩ := partMinus_eq_on hm hh
  by_cases hx : η < ζ + h / 2
  · have : partMinus ζ m =ᶠ[𝓝 η] m := by
      filter_upwards [Iio_mem_nhds hx] with t ht using h1 t ht
    rw [this.iteratedDeriv_eq k]
  · have hx' : ζ - h / 2 < η := by linarith [not_lt.1 hx]
    have : partMinus ζ m =ᶠ[𝓝 η] fun _ => (0 : ℂ) := by
      filter_upwards [Ioi_mem_nhds hx'] with t ht using h2 t ht
    rw [this.iteratedDeriv_eq k, iteratedDeriv_const]
    split_ifs <;> simp

/-! ## One-sided top multipliers -/

/-- A one-sided top multiplier: `σ = 1` supported on `η > ξ f_k`, `σ = -1` on `η < ξ f_k`. -/
def InTopMultS (𝔭 : Params) (σ : ℝ) (W : ℤ × ℤ) (ξ : ℝ) (k : Fin 3) (m : ℝ → ℂ) : Prop :=
  InTopMult 𝔭 W ξ k m ∧ ∀ η, σ * (η - ξ * freqDir k) < 0 → m η = 0

theorem topHole_pos : 0 < topHole := by unfold topHole; norm_num

/-- The two parts of a top multiplier are one-sided top multipliers (same class constant). -/
theorem inTopMultS_partPlus {𝔭 : Params} {W : ℤ × ℤ} {ξ : ℝ} {k : Fin 3} {m : ℝ → ℂ}
    (hm : InTopMult 𝔭 W ξ k m) : InTopMultS 𝔭 1 W ξ k (partPlus (ξ * freqDir k) m) := by
  obtain ⟨hsm, hsupp, hhole, hder⟩ := hm
  have ha : (0 : ℝ) < (2 : ℝ) ^ (-W.1) := zpow_pos (by norm_num) _
  have hh : 0 < topHole * (2 : ℝ) ^ (-W.1) := mul_pos topHole_pos ha
  have hhole' : ∀ η, |η - ξ * freqDir k| < topHole * (2 : ℝ) ^ (-W.1) → m η = 0 := fun η h => hhole η h
  refine ⟨⟨contDiff_partPlus hhole' hh hsm, fun η hη => ?_, fun η hη => ?_, fun a ha' η => ?_⟩, fun η hη => ?_⟩
  · unfold partPlus; rw [hsupp η hη]; simp
  · unfold partPlus; rw [hhole η hη]; simp
  · refine le_trans (mul_le_mul_of_nonneg_left (norm_iteratedDeriv_partPlus_le hhole' hh a η) (by positivity)) ?_
    exact hder a ha' η
  · unfold partPlus
    rw [ite_eq_right]
    linarith

theorem inTopMultS_partMinus {𝔭 : Params} {W : ℤ × ℤ} {ξ : ℝ} {k : Fin 3} {m : ℝ → ℂ}
    (hm : InTopMult 𝔭 W ξ k m) : InTopMultS 𝔭 (-1) W ξ k (partMinus (ξ * freqDir k) m) := by
  obtain ⟨hsm, hsupp, hhole, hder⟩ := hm
  have ha : (0 : ℝ) < (2 : ℝ) ^ (-W.1) := zpow_pos (by norm_num) _
  have hh : 0 < topHole * (2 : ℝ) ^ (-W.1) := mul_pos topHole_pos ha
  have hhole' : ∀ η, |η - ξ * freqDir k| < topHole * (2 : ℝ) ^ (-W.1) → m η = 0 := fun η h => hhole η h
  refine ⟨⟨contDiff_partMinus hhole' hh hsm, fun η hη => ?_, fun η hη => ?_, fun a ha' η => ?_⟩, fun η hη => ?_⟩
  · unfold partMinus; rw [hsupp η hη]; simp
  · unfold partMinus; rw [hhole η hη]; simp
  · refine le_trans (mul_le_mul_of_nonneg_left (norm_iteratedDeriv_partMinus_le hhole' hh a η) (by positivity)) ?_
    exact hder a ha' η
  · unfold partMinus
    rw [ite_eq_right]
    linarith

/-! ## The shell, and the class of a one-sided top multiplier -/

/-- The centre of the shell of the `σ` side of the top multiplier at `(W, ξ)`, slot `k`. -/
def shellC (σ : ℝ) (k : Fin 3) (W : ℤ × ℤ) (ξ : ℝ) : ℝ :=
  ξ * freqDir k + σ * (49 / 8) * (2 : ℝ) ^ (-W.1)

/-- The shell `[shellLo, shellUp]`: `σ = 1`: `[ξ f + a/4, ξ f + 12 a]`; `σ = -1`: `[ξ f - 12 a, ξ f - a/4]`. -/
def shellLo (σ : ℝ) (k : Fin 3) (W : ℤ × ℤ) (ξ : ℝ) : ℝ := shellC σ k W ξ - (47 / 8) * (2 : ℝ) ^ (-W.1)

def shellUp (σ : ℝ) (k : Fin 3) (W : ℤ × ℤ) (ξ : ℝ) : ℝ := shellC σ k W ξ + (47 / 8) * (2 : ℝ) ^ (-W.1)

theorem shellLo_one (k : Fin 3) (W : ℤ × ℤ) (ξ : ℝ) :
    shellLo 1 k W ξ = ξ * freqDir k + topHole * (2 : ℝ) ^ (-W.1) := by
  unfold shellLo shellC topHole; ring

theorem shellUp_one (k : Fin 3) (W : ℤ × ℤ) (ξ : ℝ) :
    shellUp 1 k W ξ = ξ * freqDir k + topRad * (2 : ℝ) ^ (-W.1) := by
  unfold shellUp shellC topRad; ring

theorem shellLo_neg (k : Fin 3) (W : ℤ × ℤ) (ξ : ℝ) :
    shellLo (-1) k W ξ = ξ * freqDir k - topRad * (2 : ℝ) ^ (-W.1) := by
  unfold shellLo shellC topRad; ring

theorem shellUp_neg (k : Fin 3) (W : ℤ × ℤ) (ξ : ℝ) :
    shellUp (-1) k W ξ = ξ * freqDir k - topHole * (2 : ℝ) ^ (-W.1) := by
  unfold shellUp shellC topHole; ring

/-- A one-sided top multiplier vanishes off its shell. -/
theorem InTopMultS.zero_off_shell {𝔭 : Params} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {W : ℤ × ℤ} {ξ : ℝ}
    {k : Fin 3} {m : ℝ → ℂ} (hm : InTopMultS 𝔭 σ W ξ k m) {η : ℝ}
    (hη : η ∉ Icc (shellLo σ k W ξ) (shellUp σ k W ξ)) : m η = 0 := by
  obtain ⟨⟨-, hsupp, hhole, -⟩, hone⟩ := hm
  have ha : (0 : ℝ) < (2 : ℝ) ^ (-W.1) := zpow_pos (by norm_num) _
  rcases hσ with rfl | rfl
  · rw [shellLo_one, shellUp_one, Set.mem_Icc, not_and_or, not_le, not_le] at hη
    rcases hη with h1 | h1
    · by_cases hc : η - ξ * freqDir k < 0
      · exact hone η (by linarith)
      · refine hhole η ?_
        rw [abs_lt]; constructor <;> linarith [not_lt.1 hc]
    · exact hsupp η (by rw [lt_abs]; left; linarith)
  · rw [shellLo_neg, shellUp_neg, Set.mem_Icc, not_and_or, not_le, not_le] at hη
    rcases hη with h1 | h1
    · exact hsupp η (by rw [lt_abs]; right; linarith)
    · by_cases hc : 0 < η - ξ * freqDir k
      · exact hone η (by linarith)
      · refine hhole η ?_
        rw [abs_lt]; constructor <;> linarith [not_lt.1 hc]

/-- The class parameters of the duals of top multipliers: `β = 12` (the shell lies in `[c - 6a, c + 6a]`). -/
def Params.shellCls (𝔭 : Params) : Params := { 𝔭 with β := 12 }

@[simp] theorem Params.shellCls_N (𝔭 : Params) : 𝔭.shellCls.N = 𝔭.N := rfl
@[simp] theorem Params.shellCls_D (𝔭 : Params) : 𝔭.shellCls.D = 𝔭.D := rfl
@[simp] theorem Params.shellCls_C (𝔭 : Params) : 𝔭.shellCls.C = 𝔭.C := rfl
@[simp] theorem Params.shellCls_β (𝔭 : Params) : 𝔭.shellCls.β = 12 := rfl

/-- A one-sided top multiplier is a multiplier of the class `𝔭.shellCls` centred at the middle of its shell. -/
theorem InTopMultS.inMult {𝔭 : Params} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {W : ℤ × ℤ} {ξ : ℝ} {k : Fin 3}
    {m : ℝ → ℂ} (hm : InTopMultS 𝔭 σ W ξ k m) : InMult 𝔭.shellCls W.1 (shellC σ k W ξ) m := by
  have ha : (0 : ℝ) < (2 : ℝ) ^ (-W.1) := zpow_pos (by norm_num) _
  refine ⟨hm.1.1, fun η hη => ?_, fun a ha' η => hm.1.2.2.2 a ha' η⟩
  refine hm.zero_off_shell hσ ?_
  simp only [Params.shellCls_β] at hη
  rw [Set.mem_Icc, not_and_or, not_le, not_le]
  unfold shellLo shellUp
  rcases lt_abs.1 hη with h1 | h1
  · right; linarith
  · left; linarith

/-! ## Additivity of `tmult` in the multiplier -/

theorem fourierInv_add' {m₁ m₂ : ℝ → ℂ} (h₁ : Integrable m₁) (h₂ : Integrable m₂) (w : ℝ) :
    𝓕⁻ (fun η => m₁ η + m₂ η) w = 𝓕⁻ m₁ w + 𝓕⁻ m₂ w := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg]
  rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq, ← integral_add]
  · congr 1; ext v; simp [smul_add]
  · exact (Real.fourierIntegral_convergent_iff _).2 h₁
  · exact (Real.fourierIntegral_convergent_iff _).2 h₂

/-- The kernel of a top multiplier is good (integrable, continuous, bounded). -/
theorem goodKernel_inTopMult {𝔭 : Params} {W : ℤ × ℤ} {ξ : ℝ} {k : Fin 3} {m : ℝ → ℂ}
    (hm : InTopMult 𝔭 W ξ k m) : GoodKernel m := by
  refine ⟨integrable_fourierInv_of_smooth (c := ξ * freqDir k) (r := topRad * (2 : ℝ) ^ (-W.1)) hm.1 hm.2.1,
    continuous_fourierInv_inTopMult hm, ⟨2 ^ (0 + 1) * (2 * (topRad * (2 : ℝ) ^ (-W.1))) * 𝔭.C, fun w => ?_⟩⟩
  have := norm_fourierInv_inTopMult_le_pow (M := 0) (Nat.zero_le _) hm w
  simpa using this

theorem integrable_inTopMult {𝔭 : Params} {W : ℤ × ℤ} {ξ : ℝ} {k : Fin 3} {m : ℝ → ℂ}
    (hm : InTopMult 𝔭 W ξ k m) : Integrable m :=
  integrable_of_far hm.1.continuous hm.2.1

theorem tmult_add_mult {P : ℕ} {m₁ m₂ : ℝ → ℂ} (h₁ : GoodKernel m₁) (h₂ : GoodKernel m₂) (i₁ : Integrable m₁)
    (i₂ : Integrable m₂) {F : ℝ → ZMod P → ℂ} (hF : IsBddC F) :
    tmult (fun η => m₁ η + m₂ η) F = tmult m₁ F + tmult m₂ F := by
  funext x y
  simp only [tmult_apply, Pi.add_apply]
  rw [← integral_add (integrable_tmult_integrand h₁ hF x y) (integrable_tmult_integrand h₂ hF x y)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [fourierInv_add' i₁ i₂, add_mul]

end PrimeBHT.TimeFrequency.X2
