module

public import PrimeBHT.TimeFrequency.X2.Psp.O2Comm
public import PrimeBHT.TimeFrequency.X2.Psp.OverlapConstruct

/-!
# X2, V13 O2 (e): the single-endpoint estimate (MTT2 `infty-inside`, the terms (d5), (d6))

Frame centred at `0`.  `m₀` is a layer multiplier (`Sym0 σ M C₀`), `τ + J ≤ σ` a finer lattice scale, `F̂` a bounded measurable
`Y`-valued function, `ĝ = T_{lpSym J τ} F̂` (= `e(-θ·) S_τ F` of the construction), `x` an endpoint, `β` a bump of mass `2^τ`
(`BumpData`) and `c = 2^{-τ} ∫ tilPhi(x - a) ĝ(a) da` the coefficient.  The theorem `endpoint_bound` bounds

`‖∫ K₀(x₀ - z) [H_x(z) ĝ(z) - β(z) c] dz‖_{L²(Y)} ≤ C (A_g + A_c) 2^{-2(σ-τ)} ⟨(x₀ - x)/2^σ⟩^{-M}`

from the growth `‖ĝ(b)‖ ≤ A_g ⟨(b - x)/2^τ⟩^N` and `‖c‖ ≤ A_c`.  The proof: `ĝ` is reproduced by `ovTilSym`, which annihilates `m₀`, so
`∫ K₀(x₀ - ·) H_x ĝ = ∫ K₀(x₀ - ·) [H_x, S̃''] ĝ`; the commutator has the same mean as `c β` (`integral_commOp_eq`); subtracting
`K₀(x₀ - x)` times the vanishing mean gives the kernel increments `K₀(x₀ - z) - K₀(x₀ - x)` (`Sym0.norm_ker_diff_le`), and the
commutator decays at the scale `2^{τ+J+1}` (`yNorm_commV_decay`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform ContDiff Real Convolution
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

theorem integral_tent {a b h : ℝ} (hab : a < b) : ∫ y, tent a b h y = h * (b - a) / 2 := by
  have hr : 0 < (b - a) / 2 := by linarith
  set m := (a + b) / 2 with hm
  have hsupp : ∀ y, y ∉ Set.Ioc a b → tent a b h y = 0 := fun y hy => by
    apply tent_eq_zero hab
    intro hyy
    exact hy ⟨hyy.1, hyy.2.le⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, ← intervalIntegral.integral_of_le hab.le]
  have hm1 : a ≤ m := by rw [hm]; linarith
  have hm2 : m ≤ b := by rw [hm]; linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := m) (c := b)
    (by exact (continuous_tent a b h).intervalIntegrable _ _) (by exact (continuous_tent a b h).intervalIntegrable _ _)]
  have e1 : ∫ y in a..m, tent a b h y = ∫ y in a..m, (h / ((b - a) / 2)) * (y - a) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le hm1] at hy
    simp only [tent]
    have : |y - m| = m - y := by rw [abs_of_nonpos (by linarith [hy.2])]; ring
    rw [this]
    have h2 : 0 ≤ 1 - (m - y) / ((b - a) / 2) := by
      rw [sub_nonneg, div_le_one hr]; rw [hm]; linarith [hy.1]
    rw [max_eq_right h2]
    field_simp
    rw [hm]; ring
  have e2 : ∫ y in m..b, tent a b h y = ∫ y in m..b, (h / ((b - a) / 2)) * (b - y) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le hm2] at hy
    simp only [tent]
    have : |y - m| = y - m := by rw [abs_of_nonneg (by linarith [hy.1])]
    rw [this]
    have h2 : 0 ≤ 1 - (y - m) / ((b - a) / 2) := by
      rw [sub_nonneg, div_le_one hr]; rw [hm]; linarith [hy.2]
    rw [max_eq_right h2]
    field_simp
    rw [hm]; ring
  rw [e1, e2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have i1 : ∫ y in a..m, (y - a) = (m - a) ^ 2 / 2 := by
    rw [intervalIntegral.integral_comp_sub_right (fun t => t) a]
    simp [integral_id]
  have i2 : ∫ y in m..b, (b - y) = (b - m) ^ 2 / 2 := by
    rw [intervalIntegral.integral_comp_sub_left (fun t => t) b]
    simp [integral_id]
  rw [i1, i2]
  have hba : b - a ≠ 0 := by linarith
  rw [hm]
  field_simp
  ring

/-- A bump of mass `L` adapted to `x`: `0 ≤ β ≤ 8`, `β = 0` off `[x - L, x + L]`. -/
structure BumpData (L x : ℝ) (β : ℝ → ℝ) : Prop where
  cont : Continuous β
  nonneg : ∀ z, 0 ≤ β z
  le8 : ∀ z, β z ≤ 8
  supp : ∀ z, L < |z - x| → β z = 0
  mass : ∫ z, β z = L

theorem integral_leftPhi (σ : ℤ) (x : ℝ) : ∫ z, leftPhi σ x z = (2 : ℝ) ^ σ := by
  unfold leftPhi
  rw [integral_tent (leftBump_lt σ x)]
  have e := zpow_eq_four_mul σ
  have e1 := zpow_sub_one_eq σ
  nlinarith

theorem integral_rightPhi (σ : ℤ) (x : ℝ) : ∫ z, rightPhi σ x z = (2 : ℝ) ^ σ := by
  unfold rightPhi
  rw [integral_tent (rightBump_lt σ x)]
  have e := zpow_eq_four_mul σ
  have e1 := zpow_sub_one_eq σ
  nlinarith

theorem bumpData_leftPhi (σ : ℤ) (x : ℝ) : BumpData ((2 : ℝ) ^ σ) x (leftPhi σ x) := by
  refine ⟨continuous_leftPhi σ x, leftPhi_nonneg σ x, leftPhi_le σ x, fun z hz => ?_, integral_leftPhi σ x⟩
  apply leftPhi_eq_zero
  intro hmem
  obtain ⟨h1, h2⟩ := hmem
  have e1 := zpow_sub_one_eq σ
  have hp := zpow_two_pos (σ - 2)
  have e3 := zpow_eq_four_mul σ
  rw [lt_abs] at hz
  rcases hz with h | h <;> nlinarith

theorem bumpData_rightPhi (σ : ℤ) (x : ℝ) : BumpData ((2 : ℝ) ^ σ) x (rightPhi σ x) := by
  refine ⟨continuous_rightPhi σ x, rightPhi_nonneg σ x, rightPhi_le σ x, fun z hz => ?_, integral_rightPhi σ x⟩
  apply rightPhi_eq_zero
  intro hmem
  obtain ⟨h1, h2⟩ := hmem
  have e1 := zpow_sub_one_eq σ
  have hp := zpow_two_pos (σ - 2)
  have e3 := zpow_eq_four_mul σ
  rw [lt_abs] at hz
  rcases hz with h | h <;> nlinarith

/-! ## The kernel increments of a layer multiplier, in multiplicative form -/

namespace Sym0

variable {σ : ℤ} {M : ℕ} {C₀ : ℝ} {m₀ : ℝ → ℂ}

/-- `‖K₀(w)‖ ⟨w/T⟩^M ≤ c₁ T⁻¹`, `T = 2^σ`. -/
theorem norm_ker_mul_le (h : Sym0 σ M C₀ m₀) (w : ℝ) :
    ‖𝓕⁻ m₀ w‖ * jb (w / (2 : ℝ) ^ σ) ^ M ≤ (6 * 2 ^ (M + 1) * C₀) * ((2 : ℝ) ^ σ)⁻¹ := by
  have hp := zpow_two_pos σ
  have hq := zpow_two_pos (-σ)
  have h1 := h.norm_ker_le w
  have e : jb (w / (2 : ℝ) ^ σ) = 1 + (2 : ℝ) ^ (-σ) * |w| := by
    unfold jb; rw [abs_div, abs_of_pos hp, zpow_neg, div_eq_mul_inv, mul_comm]
  rw [e]
  have hpos : 0 < 1 + (2 : ℝ) ^ (-σ) * |w| := by positivity
  calc ‖𝓕⁻ m₀ w‖ * (1 + (2 : ℝ) ^ (-σ) * |w|) ^ M
      ≤ (2 ^ (M + 1) * (2 * (3 * (2 : ℝ) ^ (-σ))) * C₀ * ((1 + (2 : ℝ) ^ (-σ) * |w|)⁻¹) ^ M) *
        (1 + (2 : ℝ) ^ (-σ) * |w|) ^ M := by gcongr
    _ = (6 * 2 ^ (M + 1) * C₀) * ((2 : ℝ) ^ σ)⁻¹ := by
        have hi : ((1 + (2 : ℝ) ^ (-σ) * |w|)⁻¹) ^ M * (1 + (2 : ℝ) ^ (-σ) * |w|) ^ M = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ hpos.ne', one_pow]
        rw [mul_assoc _ (((1 + (2 : ℝ) ^ (-σ) * |w|)⁻¹) ^ M) ((1 + (2 : ℝ) ^ (-σ) * |w|) ^ M), hi, mul_one, zpow_neg]
        ring

theorem norm_ker_diff_mul_le (h : Sym0 σ M C₀ m₀) (u hh : ℝ) (hh1 : |hh| ≤ (2 : ℝ) ^ σ) :
    ‖𝓕⁻ m₀ (u + hh) - 𝓕⁻ m₀ u‖ * jb (u / (2 : ℝ) ^ σ) ^ M ≤
      (6 * 2 ^ (M + 1) * C₀ * (6 * π + (1 + 2 * π) ^ M)) * ((2 : ℝ) ^ σ)⁻¹ * (|hh| / (2 : ℝ) ^ σ) := by
  have hp := zpow_two_pos σ
  have hq := zpow_two_pos (-σ)
  have h1 := h.norm_ker_diff_le u hh hh1
  have e : jb (u / (2 : ℝ) ^ σ) = 1 + (2 : ℝ) ^ (-σ) * |u| := by
    unfold jb; rw [abs_div, abs_of_pos hp, zpow_neg, div_eq_mul_inv, mul_comm]
  rw [e]
  have hpos : 0 < 1 + (2 : ℝ) ^ (-σ) * |u| := by positivity
  calc ‖𝓕⁻ m₀ (u + hh) - 𝓕⁻ m₀ u‖ * (1 + (2 : ℝ) ^ (-σ) * |u|) ^ M
      ≤ (2 ^ (M + 1) * (2 * (3 * (2 : ℝ) ^ (-σ))) *
        (C₀ * (|hh| / (2 : ℝ) ^ σ) * (6 * π + (1 + 2 * π) ^ M)) * ((1 + (2 : ℝ) ^ (-σ) * |u|)⁻¹) ^ M) *
        (1 + (2 : ℝ) ^ (-σ) * |u|) ^ M := by gcongr
    _ = _ := by
        have hi : ((1 + (2 : ℝ) ^ (-σ) * |u|)⁻¹) ^ M * (1 + (2 : ℝ) ^ (-σ) * |u|) ^ M = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ hpos.ne', one_pow]
        rw [mul_assoc _ (((1 + (2 : ℝ) ^ (-σ) * |u|)⁻¹) ^ M) ((1 + (2 : ℝ) ^ (-σ) * |u|) ^ M), hi, mul_one, zpow_neg]
        ring

/-- **The kernel increment, all increments**:
`‖K₀(u + h) - K₀(u)‖ ⟨u/T⟩^M ≤ c₃ T⁻¹ (|h|/T) ⟨h/T⟩^M`. -/
theorem norm_dK_le (h : Sym0 σ M C₀ m₀) (u hh : ℝ) :
    ‖𝓕⁻ m₀ (u + hh) - 𝓕⁻ m₀ u‖ * jb (u / (2 : ℝ) ^ σ) ^ M ≤
      ((6 * 2 ^ (M + 1) * C₀ * (6 * π + (1 + 2 * π) ^ M)) + 2 ^ (M + 1) * (6 * 2 ^ (M + 1) * C₀)) *
        ((2 : ℝ) ^ σ)⁻¹ * (|hh| / (2 : ℝ) ^ σ) * jb (hh / (2 : ℝ) ^ σ) ^ M := by
  have hp := zpow_two_pos σ
  have hC := h.C_nonneg
  have hpi : 0 < π := Real.pi_pos
  set T : ℝ := (2 : ℝ) ^ σ with hT
  set c₁ : ℝ := 6 * 2 ^ (M + 1) * C₀ with hc₁
  set c₂ : ℝ := 6 * 2 ^ (M + 1) * C₀ * (6 * π + (1 + 2 * π) ^ M) with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hTi : 0 ≤ T⁻¹ := by positivity
  have hjh : 1 ≤ jb (hh / T) ^ M := one_le_pow₀ (one_le_jb _)
  have hju : 1 ≤ jb (u / T) ^ M := one_le_pow₀ (one_le_jb _)
  have hK : ∀ w, ‖𝓕⁻ m₀ w‖ ≤ c₁ * T⁻¹ := fun w => by
    have := h.norm_ker_mul_le w
    have h2 : 1 ≤ jb (w / T) ^ M := one_le_pow₀ (one_le_jb _)
    calc ‖𝓕⁻ m₀ w‖ = ‖𝓕⁻ m₀ w‖ * 1 := (mul_one _).symm
      _ ≤ ‖𝓕⁻ m₀ w‖ * jb (w / T) ^ M := by gcongr
      _ ≤ _ := this
  have hKm : ∀ w, ‖𝓕⁻ m₀ w‖ * jb (w / T) ^ M ≤ c₁ * T⁻¹ := fun w => h.norm_ker_mul_le w
  have hn : 0 ≤ ‖𝓕⁻ m₀ (u + hh) - 𝓕⁻ m₀ u‖ := norm_nonneg _
  have hac : 0 ≤ |hh| / T := by positivity
  by_cases ha : |hh| ≤ T
  · have h1 := h.norm_ker_diff_mul_le u hh ha
    calc ‖𝓕⁻ m₀ (u + hh) - 𝓕⁻ m₀ u‖ * jb (u / T) ^ M ≤ c₂ * T⁻¹ * (|hh| / T) := h1
      _ = c₂ * T⁻¹ * (|hh| / T) * 1 := (mul_one _).symm
      _ ≤ c₂ * T⁻¹ * (|hh| / T) * jb (hh / T) ^ M := by gcongr
      _ ≤ (c₂ + 2 ^ (M + 1) * c₁) * T⁻¹ * (|hh| / T) * jb (hh / T) ^ M := by
          have : 0 ≤ 2 ^ (M + 1) * c₁ := by positivity
          gcongr
          linarith
  · push Not at ha
    have haT : 1 ≤ |hh| / T := by rw [le_div_iff₀ hp]; linarith
    have hfin : ∀ t : ℝ, t ≤ 2 ^ (M + 1) * c₁ * T⁻¹ * jb (hh / T) ^ M →
        t ≤ (c₂ + 2 ^ (M + 1) * c₁) * T⁻¹ * (|hh| / T) * jb (hh / T) ^ M := by
      intro t ht
      refine ht.trans ?_
      have h0 : 0 ≤ 2 ^ (M + 1) * c₁ * T⁻¹ * jb (hh / T) ^ M := by positivity
      calc 2 ^ (M + 1) * c₁ * T⁻¹ * jb (hh / T) ^ M
          ≤ (c₂ + 2 ^ (M + 1) * c₁) * T⁻¹ * 1 * jb (hh / T) ^ M := by
            have : 0 ≤ c₂ := hc₂0
            have : 0 ≤ jb (hh / T) ^ M := by positivity
            have : 2 ^ (M + 1) * c₁ * T⁻¹ ≤ (c₂ + 2 ^ (M + 1) * c₁) * T⁻¹ * 1 := by
              rw [mul_one]; gcongr; linarith
            gcongr
        _ ≤ (c₂ + 2 ^ (M + 1) * c₁) * T⁻¹ * (|hh| / T) * jb (hh / T) ^ M := by
            have : 0 ≤ (c₂ + 2 ^ (M + 1) * c₁) * T⁻¹ := by positivity
            have : 0 ≤ jb (hh / T) ^ M := by positivity
            gcongr
    by_cases hr : |u| / 2 ≤ |hh|
    · have hjj : jb (u / T) ≤ 2 * jb (hh / T) := by
        unfold jb
        rw [abs_div, abs_div, abs_of_pos hp]
        have : |u| / T ≤ 2 * (|hh| / T) := by
          rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (by linarith) hp.le
        linarith
      have hjj' : jb (u / T) ^ M ≤ 2 ^ M * jb (hh / T) ^ M := by
        calc jb (u / T) ^ M ≤ (2 * jb (hh / T)) ^ M := pow_le_pow_left₀ (jb_pos _).le hjj M
          _ = _ := mul_pow _ _ _
      have h1 : ‖𝓕⁻ m₀ (u + hh) - 𝓕⁻ m₀ u‖ ≤ 2 * (c₁ * T⁻¹) :=
        (norm_sub_le _ _).trans (by linarith [hK (u + hh), hK u])
      apply hfin
      calc ‖𝓕⁻ m₀ (u + hh) - 𝓕⁻ m₀ u‖ * jb (u / T) ^ M
          ≤ (2 * (c₁ * T⁻¹)) * (2 ^ M * jb (hh / T) ^ M) := mul_le_mul h1 hjj' (by positivity) (by positivity)
        _ = 2 ^ (M + 1) * c₁ * T⁻¹ * jb (hh / T) ^ M := by ring
    · push Not at hr
      have hjw : jb (u / T) ≤ 2 * jb ((u + hh) / T) := by
        unfold jb
        rw [abs_div, abs_div, abs_of_pos hp]
        have h1 : |u| ≤ 2 * |u + hh| := by
          have := abs_sub_abs_le_abs_sub u (-hh)
          rw [sub_neg_eq_add, abs_neg] at this
          linarith
        have : |u| / T ≤ 2 * (|u + hh| / T) := by
          rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right h1 hp.le
        linarith
      have hjw' : jb (u / T) ^ M ≤ 2 ^ M * jb ((u + hh) / T) ^ M := by
        calc jb (u / T) ^ M ≤ (2 * jb ((u + hh) / T)) ^ M := pow_le_pow_left₀ (jb_pos _).le hjw M
          _ = _ := mul_pow _ _ _
      have e1 : ‖𝓕⁻ m₀ (u + hh)‖ * jb (u / T) ^ M ≤ 2 ^ M * (c₁ * T⁻¹) := by
        calc ‖𝓕⁻ m₀ (u + hh)‖ * jb (u / T) ^ M
            ≤ ‖𝓕⁻ m₀ (u + hh)‖ * (2 ^ M * jb ((u + hh) / T) ^ M) := by gcongr
          _ = 2 ^ M * (‖𝓕⁻ m₀ (u + hh)‖ * jb ((u + hh) / T) ^ M) := by ring
          _ ≤ 2 ^ M * (c₁ * T⁻¹) := mul_le_mul_of_nonneg_left (hKm _) (by positivity)
      have e2 : ‖𝓕⁻ m₀ u‖ * jb (u / T) ^ M ≤ c₁ * T⁻¹ := hKm u
      apply hfin
      have h2M : (1 : ℝ) ≤ 2 ^ M := one_le_pow₀ (by norm_num)
      have h0 : 0 ≤ c₁ * T⁻¹ := by positivity
      calc ‖𝓕⁻ m₀ (u + hh) - 𝓕⁻ m₀ u‖ * jb (u / T) ^ M
          ≤ (‖𝓕⁻ m₀ (u + hh)‖ + ‖𝓕⁻ m₀ u‖) * jb (u / T) ^ M := by gcongr; exact norm_sub_le _ _
        _ = ‖𝓕⁻ m₀ (u + hh)‖ * jb (u / T) ^ M + ‖𝓕⁻ m₀ u‖ * jb (u / T) ^ M := by ring
        _ ≤ 2 ^ M * (c₁ * T⁻¹) + c₁ * T⁻¹ := add_le_add e1 e2
        _ ≤ 2 ^ (M + 1) * c₁ * T⁻¹ := by rw [pow_succ]; nlinarith
        _ = 2 ^ (M + 1) * c₁ * T⁻¹ * 1 := (mul_one _).symm
        _ ≤ 2 ^ (M + 1) * c₁ * T⁻¹ * jb (hh / T) ^ M := by
            have : 0 ≤ 2 ^ (M + 1) * c₁ * T⁻¹ := by positivity
            gcongr

end Sym0

namespace BumpData

variable {L x : ℝ} {β : ℝ → ℝ}

theorem hasCompactSupport (h : BumpData L x β) : HasCompactSupport β :=
  HasCompactSupport.intro (isCompact_Icc (a := x - L) (b := x + L)) fun z hz => by
    refine h.supp z ?_
    simp only [Set.mem_Icc, not_and_or, not_le] at hz
    rw [lt_abs]
    rcases hz with h' | h'
    · right; linarith
    · left; linarith

theorem integrable (h : BumpData L x β) : Integrable β :=
  h.cont.integrable_of_hasCompactSupport h.hasCompactSupport

theorem measurable (h : BumpData L x β) : Measurable β := h.cont.measurable

theorem norm_le (h : BumpData L x β) (z : ℝ) : ‖((β z : ℝ) : ℂ)‖ ≤ 8 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h.nonneg z)]; exact h.le8 z

end BumpData

/-! ## Integrable domination -/

theorem integral_dom_le {κ ℓ L Ag N p x z : ℝ} (hℓ : 0 < ℓ) (hp1 : 1 < p) {Φ : ℝ → ℝ} (hΦm : Measurable Φ)
    (hΦ : ∀ b, Φ b ≤ κ * Ag * (ℓ / L) ^ N * (jb ((z - x) / ℓ) ^ (-p) * jb ((z - b) / ℓ) ^ (-p)))
    (hΦ0 : ∀ b, 0 ≤ Φ b) :
    Integrable Φ ∧ ∫ b, Φ b ≤ κ * Ag * (ℓ / L) ^ N * (2 * ℓ / (p - 1)) * jb ((z - x) / ℓ) ^ (-p) := by
  have hint : Integrable (fun b => κ * Ag * (ℓ / L) ^ N * (jb ((z - x) / ℓ) ^ (-p) * jb ((z - b) / ℓ) ^ (-p))) := by
    have := (integrable_jb_rpow (c := z) hℓ (r := p) hp1).const_mul (κ * Ag * (ℓ / L) ^ N * jb ((z - x) / ℓ) ^ (-p))
    refine this.congr (Filter.Eventually.of_forall fun b => ?_)
    beta_reduce
    rw [jb_sub_comm z b ℓ]; ring
  have hi : Integrable Φ := by
    refine hint.mono' hΦm.aestronglyMeasurable (Filter.Eventually.of_forall fun b => ?_)
    rw [Real.norm_of_nonneg (hΦ0 b)]
    exact hΦ b
  refine ⟨hi, (integral_mono hi hint hΦ).trans (le_of_eq ?_)⟩
  have e : ∫ b, κ * Ag * (ℓ / L) ^ N * (jb ((z - x) / ℓ) ^ (-p) * jb ((z - b) / ℓ) ^ (-p)) =
      κ * Ag * (ℓ / L) ^ N * jb ((z - x) / ℓ) ^ (-p) * ∫ b, jb ((b - z) / ℓ) ^ (-p) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    beta_reduce
    rw [jb_sub_comm z b ℓ]; ring
  rw [e, integral_jb_rpow z hℓ hp1]
  ring

/-- **Scalar decay of the commutator.** -/
theorem norm_commOp_decay {A : ℝ → ℂ} (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A) {g : ℝ → ℂ}
    (hg : Measurable g) {B : ℝ} (hB : ∀ b, ‖g b‖ ≤ B) {κ ℓ L Ag N q p x : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L)
    (hLℓ : L ≤ ℓ) (hκ : 0 ≤ κ) (hAg : 0 ≤ Ag) (hN : 0 ≤ N) (hp1 : 1 < p)
    (hk : ∀ w, ‖𝓕⁻ A w‖ ≤ κ * jb (w / ℓ) ^ (-q)) (hq : N + 2 * p ≤ q)
    (hgrow : ∀ b, ‖g b‖ ≤ Ag * jb ((b - x) / L) ^ N) (z : ℝ) :
    ‖commOp A x g z‖ ≤ κ * Ag * (ℓ / L) ^ N * (2 * ℓ / (p - 1)) * jb ((z - x) / ℓ) ^ (-p) := by
  obtain ⟨hkc, hki⟩ := kernel_facts hA hAc
  rw [commOp_eq hA hAc hg hB x z]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hp0 : 0 ≤ p := by linarith
  have hdom : ∀ b, ‖𝓕⁻ A (z - b) * (((heav (z - x) - heav (b - x) : ℝ) : ℂ) * g b)‖ ≤
      κ * Ag * (ℓ / L) ^ N * (jb ((z - x) / ℓ) ^ (-p) * jb ((z - b) / ℓ) ^ (-p)) := by
    intro b
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact comm_integrand_le hℓ hL hLℓ hκ hAg hN hp0 hk hq (norm_nonneg _) (hgrow b)
  have hmeas : Measurable (fun b => ‖𝓕⁻ A (z - b) * (((heav (z - x) - heav (b - x) : ℝ) : ℂ) * g b)‖) := by
    have h1 : Measurable (fun b : ℝ => 𝓕⁻ A (z - b)) := (hkc.comp (continuous_const.sub continuous_id)).measurable
    have h2 : Measurable (fun b : ℝ => (((heav (z - x) - heav (b - x) : ℝ)) : ℂ)) :=
      Complex.measurable_ofReal.comp ((measurable_const).sub (measurable_heav.comp (measurable_id.sub measurable_const)))
    exact (h1.mul (h2.mul hg)).norm
  exact (integral_dom_le hℓ hp1 hmeas hdom (fun b => norm_nonneg _)).2

theorem integrable_commOp {A : ℝ → ℂ} (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A) {g : ℝ → ℂ}
    (hg : Measurable g) {B : ℝ} (hB : ∀ b, ‖g b‖ ≤ B) {κ ℓ L Ag N q x : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L)
    (hLℓ : L ≤ ℓ) (hκ : 0 ≤ κ) (hAg : 0 ≤ Ag) (hN : 0 ≤ N)
    (hk : ∀ w, ‖𝓕⁻ A w‖ ≤ κ * jb (w / ℓ) ^ (-q)) (hq : N + 4 ≤ q)
    (hgrow : ∀ b, ‖g b‖ ≤ Ag * jb ((b - x) / L) ^ N) : Integrable (commOp A x g) := by
  have hmeas := (commOp_bounds hA hAc hg hB x).1
  have hint : Integrable (fun z => (κ * Ag * (ℓ / L) ^ N * (2 * ℓ / (2 - 1))) * jb ((z - x) / ℓ) ^ (-(2 : ℝ))) :=
    (integrable_jb_rpow (c := x) hℓ (r := 2) (by norm_num)).const_mul _
  refine hint.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  have := norm_commOp_decay hA hAc hg hB hℓ hL hLℓ hκ hAg hN (p := 2) (by norm_num) hk (by linarith) hgrow z
  simpa [mul_assoc] using this

/-! ## The error identity -/

/-- **MTT2's cancellation**: `ĝ = T_{lpSym} f` is reproduced by `ovTilSym`, which annihilates the layer multiplier `m₀`, hence
`∫ K₀(x₀ - ·) [H_x ĝ - c β] = ∫ (K₀(x₀ - ·) - K₀(x₀ - x)) [[H_x, S̃''] ĝ - c β]` (the commutator and `c β` have the same mean). -/
theorem err_identity {J : ℕ} {τ σ : ℤ} (hστ : τ + (J : ℤ) ≤ σ) {M : ℕ} {C₀ : ℝ} {m₀ : ℝ → ℂ}
    (hm : Sym0 σ M C₀ m₀) {f : ℝ → ℂ} (hf : Measurable f) {Bf : ℝ} (hBf : ∀ z, ‖f z‖ ≤ Bf)
    {x Ag N : ℝ} (hAg : 0 ≤ Ag) (hN : 0 ≤ N) {q : ℕ} (hq : N + 4 ≤ q) {g : ℝ → ℂ}
    (hgdef : g = tm (lpSym J τ) f) (hgrow : ∀ b, ‖g b‖ ≤ Ag * jb ((b - x) / (2 : ℝ) ^ τ) ^ N)
    {c : ℂ} (hc : c = ((((2 : ℝ) ^ τ)⁻¹ : ℝ) : ℂ) * ∫ a, tilPhi J τ (x - a) * g a)
    {β : ℝ → ℝ} (hβ : BumpData ((2 : ℝ) ^ τ) x β) (x₀ : ℝ) :
    ∫ z, 𝓕⁻ m₀ (x₀ - z) * (((heav (z - x) : ℝ) : ℂ) * g z - ((β z : ℝ) : ℂ) * c) =
      ∫ z, (𝓕⁻ m₀ (x₀ - z) - 𝓕⁻ m₀ (x₀ - x)) * (commOp (ovTilSym J τ) x g z - ((β z : ℝ) : ℂ) * c) := by
  have hLp := contDiff_lpSym J τ
  have hLpc := hasCompactSupport_lpSym J τ
  have hTil := contDiff_tilSym J τ
  have hTilc := hasCompactSupport_tilSym J τ
  have hOv := contDiff_ovTilSym J τ
  have hOvc := hasCompactSupport_ovTilSym J τ
  have hpτ := zpow_two_pos τ
  have hgm : Measurable g := by rw [hgdef]; exact measurable_tm hLp hLpc hf
  have hgb : ∀ z, ‖g z‖ ≤ Bf * ∫ w, ‖𝓕⁻ (lpSym J τ) w‖ := fun z => by
    rw [hgdef]; exact norm_tm_le_gen hLp hLpc hf hBf z
  have hgA : ∀ z, tm (tilSym J τ) g z = g z := fun z => by
    rw [hgdef]; exact tm_comp_self hTil hTilc hLp hLpc (tilSym_mul_lpSym J τ) hf hBf z
  have hgB : ∀ z, tm (ovTilSym J τ) g z = g z := fun z => by
    rw [hgdef]; exact tm_comp_self hOv hOvc hLp hLpc (ovTilSym_mul_lpSym J τ) hf hBf z
  set Bg : ℝ := Bf * ∫ w, ‖𝓕⁻ (lpSym J τ) w‖ with hBg
  obtain ⟨hkc, hki⟩ := kernel_facts hm.smooth hm.compact
  -- the commutator
  set Cm : ℝ → ℂ := commOp (ovTilSym J τ) x g with hCm
  obtain ⟨hCm_m, hCm_b⟩ := commOp_bounds hOv hOvc hgm hgb x
  have hℓ : (0 : ℝ) < (2 : ℝ) ^ (τ + (J : ℤ) + 1) := zpow_two_pos _
  have hLℓ : (2 : ℝ) ^ τ ≤ (2 : ℝ) ^ (τ + (J : ℤ) + 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hκ : 0 ≤ tilConst q * (2 : ℝ) ^ (-τ) := by
    have := tilConst_pos q; have := zpow_two_pos (-τ); positivity
  have hIB : Integrable Cm :=
    integrable_commOp hOv hOvc hgm hgb hℓ hpτ hLℓ hκ hAg hN (fun w => ovTilKer_decay J τ q w) hq hgrow
  have hIA : Integrable (commOp (tilSym J τ) x g) :=
    integrable_commOp hTil hTilc hgm hgb hℓ hpτ hLℓ hκ hAg hN (fun w => tilKer_decay J τ q w) hq hgrow
  -- the mean of the commutator
  have hmean : ∫ z, Cm z = ((2 : ℝ) ^ τ : ℝ) * c := by
    have h1 := integral_commOp_eq hTil hTilc hOv hOvc (tilSym_zero J τ) (ovTilSym_zero J τ) hgm hgb hgA hgB hIA hIB
    have h2 := integral_commOp_tilSym J τ hgm hgb hAg hN hq hgrow
    rw [hCm, ← h1, h2, hc, ← mul_assoc]
    have : (((2 : ℝ) ^ τ : ℝ) : ℂ) * ((((2 : ℝ) ^ τ)⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hpτ.ne']; simp
    rw [this, one_mul]
  have hβmass : ∫ z, ((β z : ℝ) : ℂ) = ((2 : ℝ) ^ τ : ℝ) := by
    rw [integral_complex_ofReal, hβ.mass]
  -- bounded measurable pieces
  set kx : ℂ := 𝓕⁻ m₀ (x₀ - x) with hkx
  have hβc_m : Measurable (fun z => ((β z : ℝ) : ℂ) * c) :=
    (Complex.measurable_ofReal.comp hβ.measurable).mul measurable_const
  have hβc_b : ∀ z, ‖((β z : ℝ) : ℂ) * c‖ ≤ 8 * ‖c‖ := fun z => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hβ.norm_le z) (norm_nonneg _)
  have hHg_m := measurable_Hg (x := x) hgm
  have hHg_b := norm_Hg_le (x := x) hgb
  have iA : Integrable (fun z => 𝓕⁻ m₀ (x₀ - z) * Cm z) := integrable_kmul hki hCm_m hCm_b x₀ hkc
  have iB : Integrable (fun z => 𝓕⁻ m₀ (x₀ - z) * (((β z : ℝ) : ℂ) * c)) := integrable_kmul hki hβc_m hβc_b x₀ hkc
  have iC : Integrable (fun z => kx * Cm z) := hIB.const_mul kx
  have iD : Integrable (fun z => kx * (((β z : ℝ) : ℂ) * c)) := by
    have : Integrable (fun z => ((β z : ℝ) : ℂ)) := hβ.integrable.ofReal
    exact (this.mul_const c).const_mul kx
  have iE : Integrable (fun z => 𝓕⁻ m₀ (x₀ - z) * (((heav (z - x) : ℝ) : ℂ) * g z)) :=
    integrable_kmul hki hHg_m hHg_b x₀ hkc
  -- `∫ K₀ H ĝ = ∫ K₀ Cm`
  have hI1 : ∫ z, 𝓕⁻ m₀ (x₀ - z) * (((heav (z - x) : ℝ) : ℂ) * g z) = ∫ z, 𝓕⁻ m₀ (x₀ - z) * Cm z := by
    set f' : ℝ → ℂ := fun z => ((heav (z - x) : ℝ) : ℂ) * g z with hf'
    have hsplit : ∀ z, f' z = Cm z + tm (ovTilSym J τ) f' z := by
      intro z
      simp only [hCm, hf', commOp, hgB z]
      ring
    have hT_m : Measurable (tm (ovTilSym J τ) f') := measurable_tm hOv hOvc hHg_m
    have hT_b : ∀ z, ‖tm (ovTilSym J τ) f' z‖ ≤ Bg * ∫ w, ‖𝓕⁻ (ovTilSym J τ) w‖ :=
      fun z => norm_tm_le_gen hOv hOvc hHg_m (norm_Hg_le (x := x) hgb) z
    have hzero : tm m₀ (tm (ovTilSym J τ) f') x₀ = 0 := by
      refine tm_comp_zero hm.smooth hm.compact hOv hOvc (fun ξ => ?_) hHg_m (norm_Hg_le (x := x) hgb) x₀
      rw [mul_comm]
      exact ovTilSym_mul_m hστ hm.supp ξ
    have e1 : tm m₀ f' x₀ = tm m₀ Cm x₀ + tm m₀ (tm (ovTilSym J τ) f') x₀ := by
      have hfe : f' = fun z => Cm z + tm (ovTilSym J τ) f' z := funext hsplit
      conv_lhs => rw [hfe]
      exact tm_add hm.smooth hm.compact hCm_m hT_m hCm_b hT_b x₀
    show tm m₀ f' x₀ = tm m₀ Cm x₀
    rw [e1, hzero, add_zero]
  -- expand both sides
  have hL : ∫ z, 𝓕⁻ m₀ (x₀ - z) * (((heav (z - x) : ℝ) : ℂ) * g z - ((β z : ℝ) : ℂ) * c) =
      (∫ z, 𝓕⁻ m₀ (x₀ - z) * Cm z) - ∫ z, 𝓕⁻ m₀ (x₀ - z) * (((β z : ℝ) : ℂ) * c) := by
    rw [← hI1, ← integral_sub iE iB]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce; ring
  have hR : ∫ z, (𝓕⁻ m₀ (x₀ - z) - kx) * (Cm z - ((β z : ℝ) : ℂ) * c) =
      (∫ z, 𝓕⁻ m₀ (x₀ - z) * Cm z) - (∫ z, 𝓕⁻ m₀ (x₀ - z) * (((β z : ℝ) : ℂ) * c)) -
        (∫ z, kx * Cm z) + (∫ z, kx * (((β z : ℝ) : ℂ) * c)) := by
    have : ∀ z, (𝓕⁻ m₀ (x₀ - z) - kx) * (Cm z - ((β z : ℝ) : ℂ) * c) =
        𝓕⁻ m₀ (x₀ - z) * Cm z - 𝓕⁻ m₀ (x₀ - z) * (((β z : ℝ) : ℂ) * c) - kx * Cm z + kx * (((β z : ℝ) : ℂ) * c) :=
      fun z => by ring
    simp_rw [this]
    have iAB : Integrable (fun z => 𝓕⁻ m₀ (x₀ - z) * Cm z - 𝓕⁻ m₀ (x₀ - z) * (((β z : ℝ) : ℂ) * c)) := iA.sub iB
    have iABC : Integrable (fun z => 𝓕⁻ m₀ (x₀ - z) * Cm z - 𝓕⁻ m₀ (x₀ - z) * (((β z : ℝ) : ℂ) * c) - kx * Cm z) :=
      iAB.sub iC
    rw [integral_add iABC iD, integral_sub iAB iC, integral_sub iA iB]
  have hk1 : ∫ z, kx * Cm z = kx * (((2 : ℝ) ^ τ : ℝ) * c) := by rw [integral_const_mul, hmean]
  have hk2 : ∫ z, kx * (((β z : ℝ) : ℂ) * c) = kx * (((2 : ℝ) ^ τ : ℝ) * c) := by
    rw [integral_const_mul, integral_mul_const, hβmass]
    try ring
  rw [hL, hR, hk1, hk2]
  ring

/-! ## The vector bound -/

/-- Pure arithmetic of the commutator term: with `a = |z - x|`, `j = ⟨a/ℓ⟩`. -/
theorem commutator_term_le {T ℓ c₃ Acc W a dK s : ℝ} {M : ℕ} (hT : 0 < T) (hℓ : 0 < ℓ) (hℓT : ℓ ≤ 2 * T)
    (hc₃ : 0 ≤ c₃) (hAcc : 0 ≤ Acc) (hW : 0 ≤ W) (ha : 0 ≤ a) (hs0 : 0 ≤ s) (_hdK0 : 0 ≤ dK)
    (hdK : dK ≤ c₃ * T⁻¹ * (a / T) * jb (a / T) ^ M * W)
    (hs : s ≤ Acc * jb (a / ℓ) ^ (-((M : ℝ) + 3))) :
    dK * s ≤ (c₃ * 2 ^ M * Acc * (ℓ / T) * T⁻¹ * W) * jb (a / ℓ) ^ (-(2 : ℝ)) := by
  set j : ℝ := jb (a / ℓ) with hj
  have hj1 : 1 ≤ j := one_le_jb _
  have hj0 : 0 < j := by linarith
  have hjj : j = 1 + a / ℓ := by
    rw [hj]; unfold jb; rw [abs_div, abs_of_pos hℓ, abs_of_nonneg ha]
  have h1 : a / T ≤ (ℓ / T) * j := by
    have : a / ℓ ≤ j := by rw [hjj]; linarith
    calc a / T = (ℓ / T) * (a / ℓ) := by field_simp
      _ ≤ (ℓ / T) * j := by gcongr
  have h2 : jb (a / T) ≤ 2 * j := by
    unfold jb
    rw [abs_div, abs_of_pos hT, abs_of_nonneg ha]
    have : a / T ≤ 2 * (a / ℓ) := by
      rw [div_le_iff₀ hT]
      have : a / ℓ * ℓ = a := by field_simp
      nlinarith [div_nonneg ha hℓ.le]
    rw [hjj]
    linarith
  have h3 : jb (a / T) ^ M ≤ 2 ^ M * j ^ M := by
    calc jb (a / T) ^ M ≤ (2 * j) ^ M := pow_le_pow_left₀ (jb_pos _).le h2 M
      _ = _ := mul_pow _ _ _
  have h4 : j * j ^ M * j ^ (-((M : ℝ) + 3)) = j ^ (-(2 : ℝ)) := by
    have : j * j ^ M = j ^ ((1 : ℝ) + M) := by rw [Real.rpow_add hj0, Real.rpow_one, Real.rpow_natCast]
    rw [this, ← Real.rpow_add hj0]; congr 1; ring
  have hjbT : 0 ≤ jb (a / T) := (jb_pos _).le
  have hP : 0 ≤ c₃ * T⁻¹ * (a / T) * jb (a / T) ^ M * W := by positivity
  have hQ : 0 ≤ Acc * j ^ (-((M : ℝ) + 3)) := by positivity
  calc dK * s ≤ (c₃ * T⁻¹ * (a / T) * jb (a / T) ^ M * W) * (Acc * j ^ (-((M : ℝ) + 3))) :=
        mul_le_mul hdK hs hs0 hP
    _ ≤ (c₃ * T⁻¹ * ((ℓ / T) * j) * (2 ^ M * j ^ M) * W) * (Acc * j ^ (-((M : ℝ) + 3))) := by
        have hT' : 0 ≤ c₃ * T⁻¹ := by positivity
        have hjM : 0 ≤ j ^ M := by positivity
        have hw : 0 ≤ (ℓ / T) * j := by positivity
        gcongr
    _ = (c₃ * 2 ^ M * Acc * (ℓ / T) * T⁻¹ * W) * (j * j ^ M * j ^ (-((M : ℝ) + 3))) := by ring
    _ = _ := by rw [h4]

/-- The constant of the commutator decay: `Q = C_q 2^{J+2} (2^{J+1})^N / (M + 2)`. -/
def endQ (J M q : ℕ) (N : ℝ) : ℝ :=
  tilConst q * (2 : ℝ) ^ ((J : ℤ) + 2) * ((2 : ℝ) ^ ((J : ℤ) + 1)) ^ N / ((M : ℝ) + 2)

/-- The constant of the kernel increments. -/
def endC3 (M : ℕ) (C₀ : ℝ) : ℝ :=
  (6 * 2 ^ (M + 1) * C₀ * (6 * π + (1 + 2 * π) ^ M)) + 2 ^ (M + 1) * (6 * 2 ^ (M + 1) * C₀)

theorem endQ_nonneg (J M q : ℕ) {N : ℝ} : 0 ≤ endQ J M q N := by
  have := tilConst_pos q
  unfold endQ
  positivity

theorem endC3_nonneg (M : ℕ) {C₀ : ℝ} (h : 0 ≤ C₀) : 0 ≤ endC3 M C₀ := by
  unfold endC3; positivity

section EndpointVec

variable {P : ℕ} [NeZero P]

theorem endpoint_coord {J : ℕ} {τ σ : ℤ} (hστ : τ + (J : ℤ) ≤ σ) {M : ℕ} {C₀ : ℝ} {m₀ : ℝ → ℂ}
    (hm : Sym0 σ M C₀ m₀) {Fh : ℝ → ZMod P → ℂ} (hFh : Measurable Fh) {BF : ℝ} (hBF : ∀ z y, ‖Fh z y‖ ≤ BF)
    {x Ag N : ℝ} (hAg : 0 ≤ Ag) (hN : 0 ≤ N) {q : ℕ} (hq : N + 4 ≤ q)
    (hgrow : ∀ b, yNorm 2 (tmult (lpSym J τ) Fh b) ≤ Ag * jb ((b - x) / (2 : ℝ) ^ τ) ^ N)
    {c : ZMod P → ℂ} (hc : ∀ y, c y = ((((2 : ℝ) ^ τ)⁻¹ : ℝ) : ℂ) * ∫ a, tilPhi J τ (x - a) * tmult (lpSym J τ) Fh a y)
    {β : ℝ → ℝ} (hβ : BumpData ((2 : ℝ) ^ τ) x β) (x₀ : ℝ) (y : ZMod P) :
    ∫ z, 𝓕⁻ m₀ (x₀ - z) * (((heav (z - x) : ℝ) : ℂ) * tmult (lpSym J τ) Fh z y - ((β z : ℝ) : ℂ) * c y) =
      ∫ z, (𝓕⁻ m₀ (x₀ - z) - 𝓕⁻ m₀ (x₀ - x)) *
        (commV (ovTilSym J τ) x (tmult (lpSym J τ) Fh) z y - ((β z : ℝ) : ℂ) * c y) := by
  have hP : 0 ≤ (P : ℝ) ^ (2 : ℝ)⁻¹ := by positivity
  refine err_identity hστ hm (f := fun z => Fh z y) (measurable_pi_iff.1 hFh y) (Bf := BF) (fun z => hBF z y)
    (Ag := (P : ℝ) ^ (2 : ℝ)⁻¹ * Ag) (by positivity) hN hq (g := fun z => tmult (lpSym J τ) Fh z y) rfl
    (fun b => ?_) (c := c y) (hc y) hβ x₀
  have h1 := norm_apply_le_rpow_mul_yNorm (s := 2) (by norm_num) (tmult (lpSym J τ) Fh b) y
  calc ‖tmult (lpSym J τ) Fh b y‖ ≤ (P : ℝ) ^ (2 : ℝ)⁻¹ * yNorm 2 (tmult (lpSym J τ) Fh b) := h1
    _ ≤ (P : ℝ) ^ (2 : ℝ)⁻¹ * (Ag * jb ((b - x) / (2 : ℝ) ^ τ) ^ N) := mul_le_mul_of_nonneg_left (hgrow b) hP
    _ = _ := by ring

/-- **The single-endpoint estimate** (MTT2 (d5), (d6) for one endpoint): see the module docstring. -/
theorem endpoint_bound {J : ℕ} {τ σ : ℤ} (hστ : τ + (J : ℤ) ≤ σ) {M : ℕ} {C₀ : ℝ} {m₀ : ℝ → ℂ}
    (hm : Sym0 σ M C₀ m₀) {Fh : ℝ → ZMod P → ℂ} (hFh : Measurable Fh) {BF : ℝ} (hBF : ∀ z y, ‖Fh z y‖ ≤ BF)
    {x Ag N A₁ : ℝ} (hAg : 0 ≤ Ag) (hN : 0 ≤ N) (hA₁ : 0 ≤ A₁) {q : ℕ} (hq : N + 2 * ((M : ℝ) + 3) ≤ q)
    (hgrow : ∀ b, yNorm 2 (tmult (lpSym J τ) Fh b) ≤ Ag * jb ((b - x) / (2 : ℝ) ^ τ) ^ N)
    {c : ZMod P → ℂ} (hc : ∀ y, c y = ((((2 : ℝ) ^ τ)⁻¹ : ℝ) : ℂ) * ∫ a, tilPhi J τ (x - a) * tmult (lpSym J τ) Fh a y)
    (hcn : yNorm 2 c ≤ A₁) {β : ℝ → ℝ} (hβ : BumpData ((2 : ℝ) ^ τ) x β) (x₀ : ℝ) :
    yNorm 2 (fun y => ∫ z, 𝓕⁻ m₀ (x₀ - z) *
        (((heav (z - x) : ℝ) : ℂ) * tmult (lpSym J τ) Fh z y - ((β z : ℝ) : ℂ) * c y)) ≤
      (endC3 M C₀ * 2 ^ M * (2 * endQ J M q N * ((2 : ℝ) ^ ((J : ℤ) + 1)) ^ 2 + 1)) * (Ag + A₁) *
        ((2 : ℝ) ^ (τ - σ)) ^ 2 * jb ((x₀ - x) / (2 : ℝ) ^ σ) ^ (-(M : ℝ)) := by
  have hLp := contDiff_lpSym J τ
  have hLpc := hasCompactSupport_lpSym J τ
  have hOv := contDiff_ovTilSym J τ
  have hOvc := hasCompactSupport_ovTilSym J τ
  obtain ⟨hkc, hki⟩ := kernel_facts hm.smooth hm.compact
  have hT : (0 : ℝ) < (2 : ℝ) ^ σ := zpow_two_pos σ
  have hL : (0 : ℝ) < (2 : ℝ) ^ τ := zpow_two_pos τ
  have hℓ : (0 : ℝ) < (2 : ℝ) ^ (τ + (J : ℤ) + 1) := zpow_two_pos _
  have hℓT : (2 : ℝ) ^ (τ + (J : ℤ) + 1) ≤ 2 * (2 : ℝ) ^ σ := by
    have : (2 : ℝ) ^ (τ + (J : ℤ) + 1) ≤ (2 : ℝ) ^ (σ + 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    calc (2 : ℝ) ^ (τ + (J : ℤ) + 1) ≤ (2 : ℝ) ^ (σ + 1) := this
      _ = 2 * (2 : ℝ) ^ σ := by rw [zpow_add_one₀ (by norm_num), mul_comm]
  have hLℓ : (2 : ℝ) ^ τ ≤ (2 : ℝ) ^ (τ + (J : ℤ) + 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hLT : (2 : ℝ) ^ τ ≤ (2 : ℝ) ^ σ := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hℓL : (2 : ℝ) ^ (τ + (J : ℤ) + 1) / (2 : ℝ) ^ τ = (2 : ℝ) ^ ((J : ℤ) + 1) := by
    rw [div_eq_iff hL.ne', ← zpow_add₀ (by norm_num)]; congr 1; ring
  have hρ : (2 : ℝ) ^ τ / (2 : ℝ) ^ σ = (2 : ℝ) ^ (τ - σ) := by rw [zpow_sub₀ (by norm_num)]
  have hC₀ : 0 ≤ C₀ := hm.C_nonneg
  have hc₃ : 0 ≤ endC3 M C₀ := endC3_nonneg M hC₀
  have hQ : 0 ≤ endQ J M q N := endQ_nonneg J M q
  have hp1 : (1 : ℝ) < (M : ℝ) + 3 := by have := M.cast_nonneg (α := ℝ); linarith
  have hqN : N + 4 ≤ (q : ℝ) := by have := M.cast_nonneg (α := ℝ); linarith
  -- the function `G`
  set G := tmult (lpSym J τ) Fh with hG
  have hGm : Measurable G := measurable_tmult_of_cont_kernel (kernel_facts hLp hLpc).1 hFh
  set BG : ℝ := BF * ∫ w, ‖𝓕⁻ (lpSym J τ) w‖ with hBG
  have hGb : ∀ z y, ‖G z y‖ ≤ BG := fun z y =>
    norm_tm_le_gen hLp hLpc (measurable_pi_iff.1 hFh y) (fun w => hBF w y) z
  -- scale abbreviations
  set T : ℝ := (2 : ℝ) ^ σ with hTdef
  set L : ℝ := (2 : ℝ) ^ τ with hLdef
  set ℓ : ℝ := (2 : ℝ) ^ (τ + (J : ℤ) + 1) with hℓdef
  set ρ : ℝ := (2 : ℝ) ^ (τ - σ) with hρdef
  set r : ℝ := (2 : ℝ) ^ ((J : ℤ) + 1) with hrdef
  have hr0 : 0 < r := zpow_two_pos _
  have hρ0 : 0 < ρ := zpow_two_pos _
  -- the coordinatewise identity
  have hcoord : ∀ y, ∫ z, 𝓕⁻ m₀ (x₀ - z) * (((heav (z - x) : ℝ) : ℂ) * G z y - ((β z : ℝ) : ℂ) * c y) =
      ∫ z, (𝓕⁻ m₀ (x₀ - z) - 𝓕⁻ m₀ (x₀ - x)) *
        (commV (ovTilSym J τ) x G z y - ((β z : ℝ) : ℂ) * c y) :=
    fun y => endpoint_coord hστ hm hFh hBF hAg hN hqN hgrow hc hβ x₀ y
  -- kernel facts
  have hK : ∀ w, ‖𝓕⁻ m₀ w‖ ≤ (6 * 2 ^ (M + 1) * C₀) * T⁻¹ := fun w => by
    have h1 := hm.norm_ker_mul_le w
    have h2 : 1 ≤ jb (w / T) ^ M := one_le_pow₀ (one_le_jb _)
    calc ‖𝓕⁻ m₀ w‖ = ‖𝓕⁻ m₀ w‖ * 1 := (mul_one _).symm
      _ ≤ ‖𝓕⁻ m₀ w‖ * jb (w / T) ^ M := by gcongr
      _ ≤ _ := h1
  set W : ℝ := jb ((x₀ - x) / T) ^ (-(M : ℝ)) with hW
  have hW0 : 0 < W := Real.rpow_pos_of_pos (jb_pos _) _
  have hΔpt : ∀ z, ‖𝓕⁻ m₀ (x₀ - z) - 𝓕⁻ m₀ (x₀ - x)‖ ≤
      endC3 M C₀ * T⁻¹ * (|z - x| / T) * jb (|z - x| / T) ^ M * W := by
    intro z
    have h := hm.norm_dK_le (x₀ - x) (x - z)
    have e1 : x₀ - x + (x - z) = x₀ - z := by ring
    rw [e1] at h
    have e2 : |x - z| = |z - x| := abs_sub_comm _ _
    have e4 : jb ((x - z) / T) = jb (|z - x| / T) := by
      unfold jb; rw [abs_div, abs_div, abs_abs, abs_of_pos hT, abs_sub_comm x z]
    rw [e2, e4] at h
    have hpos : 0 < jb ((x₀ - x) / T) ^ M := pow_pos (jb_pos _) _
    have e3 : W = (jb ((x₀ - x) / T) ^ M)⁻¹ := by rw [hW, Real.rpow_neg (jb_pos _).le, Real.rpow_natCast]
    rw [e3]
    have h' : ‖𝓕⁻ m₀ (x₀ - z) - 𝓕⁻ m₀ (x₀ - x)‖ * jb ((x₀ - x) / T) ^ M ≤
        endC3 M C₀ * T⁻¹ * (|z - x| / T) * jb (|z - x| / T) ^ M := h
    calc ‖𝓕⁻ m₀ (x₀ - z) - 𝓕⁻ m₀ (x₀ - x)‖
        = ‖𝓕⁻ m₀ (x₀ - z) - 𝓕⁻ m₀ (x₀ - x)‖ * jb ((x₀ - x) / T) ^ M * (jb ((x₀ - x) / T) ^ M)⁻¹ := by
          field_simp
      _ ≤ (endC3 M C₀ * T⁻¹ * (|z - x| / T) * jb (|z - x| / T) ^ M) * (jb ((x₀ - x) / T) ^ M)⁻¹ := by
          gcongr
  have hΔb : ∀ z, ‖𝓕⁻ m₀ (x₀ - z) - 𝓕⁻ m₀ (x₀ - x)‖ ≤ 2 * ((6 * 2 ^ (M + 1) * C₀) * T⁻¹) := fun z =>
    (norm_sub_le _ _).trans (by linarith [hK (x₀ - z), hK (x₀ - x)])
  -- commutator decay
  have hκ : 0 ≤ tilConst q * (2 : ℝ) ^ (-τ) := by
    have := tilConst_pos q; have := zpow_two_pos (-τ); positivity
  have hdec : ∀ z, yNorm 2 (commV (ovTilSym J τ) x G z) ≤
      (tilConst q * (2 : ℝ) ^ (-τ)) * Ag * (ℓ / L) ^ N * (2 * ℓ / (((M : ℝ) + 3) - 1)) *
        jb ((z - x) / ℓ) ^ (-((M : ℝ) + 3)) := fun z =>
    yNorm_commV_decay hOv hOvc hGm hGb (q := (q : ℝ)) hℓ hL hLℓ hκ hAg hN hp1
      (fun w => ovTilKer_decay J τ q w) hq hgrow z
  have hAcc : (tilConst q * (2 : ℝ) ^ (-τ)) * Ag * (ℓ / L) ^ N * (2 * ℓ / (((M : ℝ) + 3) - 1)) =
      Ag * endQ J M q N := by
    have e1 : (2 : ℝ) ^ (-τ) * (2 * ℓ) = (2 : ℝ) ^ ((J : ℤ) + 2) := by
      have : (2 : ℝ) * (2 : ℝ) ^ (τ + (J : ℤ) + 1) = (2 : ℝ) ^ (τ + (J : ℤ) + 2) := by
        rw [show τ + (J : ℤ) + 2 = (τ + (J : ℤ) + 1) + 1 by ring,
          zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0) (τ + (J : ℤ) + 1), mul_comm]
      rw [hℓdef, this, ← zpow_add₀ (by norm_num)]; congr 1; ring
    have e2 : ((M : ℝ) + 3) - 1 = (M : ℝ) + 2 := by ring
    unfold endQ
    rw [e2, hℓL, div_eq_mul_inv, div_eq_mul_inv, ← e1]
    ring
  set Acc : ℝ := Ag * endQ J M q N with hAccdef
  have hAcc0 : 0 ≤ Acc := mul_nonneg hAg hQ
  have hdec' : ∀ z, yNorm 2 (commV (ovTilSym J τ) x G z) ≤ Acc * jb (|z - x| / ℓ) ^ (-((M : ℝ) + 3)) := fun z => by
    have := hdec z
    rw [hAcc] at this
    have e : jb (|z - x| / ℓ) = jb ((z - x) / ℓ) := by unfold jb; rw [abs_div, abs_div, abs_abs]
    rw [e]; exact this
  -- coordinatewise growth and integrability
  have hP : 0 ≤ (P : ℝ) ^ (2 : ℝ)⁻¹ := by positivity
  have hcg : ∀ b y, ‖G b y‖ ≤ (P : ℝ) ^ (2 : ℝ)⁻¹ * Ag * jb ((b - x) / L) ^ N := fun b y => by
    have h1 := norm_apply_le_rpow_mul_yNorm (s := 2) (by norm_num) (G b) y
    calc ‖G b y‖ ≤ (P : ℝ) ^ (2 : ℝ)⁻¹ * yNorm 2 (G b) := h1
      _ ≤ (P : ℝ) ^ (2 : ℝ)⁻¹ * (Ag * jb ((b - x) / L) ^ N) := mul_le_mul_of_nonneg_left (hgrow b) hP
      _ = _ := by ring
  have hCmI : ∀ y, Integrable (fun z => commV (ovTilSym J τ) x G z y) := fun y =>
    integrable_commOp hOv hOvc ((measurable_pi_apply y).comp hGm) (B := BG) (fun b => hGb b y)
      (q := (q : ℝ)) hℓ hL hLℓ hκ (mul_nonneg hP hAg) hN (fun w => ovTilKer_decay J τ q w) hqN
      (fun b => by simpa using hcg b y)
  set ΔK : ℝ → ℂ := fun z => 𝓕⁻ m₀ (x₀ - z) - 𝓕⁻ m₀ (x₀ - x) with hΔK
  have hΔc : Continuous ΔK := (hkc.comp (continuous_const.sub continuous_id)).sub continuous_const
  have hVi : ∀ y, Integrable (fun z => ΔK z * (commV (ovTilSym J τ) x G z y - ((β z : ℝ) : ℂ) * c y)) := fun y => by
    have h1 : Integrable (fun z => commV (ovTilSym J τ) x G z y - ((β z : ℝ) : ℂ) * c y) :=
      (hCmI y).sub ((hβ.integrable.ofReal).mul_const (c y))
    exact h1.bdd_mul (c := 2 * ((6 * 2 ^ (M + 1) * C₀) * T⁻¹)) hΔc.aestronglyMeasurable
      (Filter.Eventually.of_forall hΔb)
  have hMink := yNorm_integral_le_of_one_le (s := 2) (by norm_num)
    (fun z y => ΔK z * (commV (ovTilSym J τ) x G z y - ((β z : ℝ) : ℂ) * c y)) hVi
  have hLHS : (fun y => ∫ z, 𝓕⁻ m₀ (x₀ - z) * (((heav (z - x) : ℝ) : ℂ) * G z y - ((β z : ℝ) : ℂ) * c y)) =
      fun y => ∫ z, ΔK z * (commV (ovTilSym J τ) x G z y - ((β z : ℝ) : ℂ) * c y) := funext hcoord
  rw [hLHS]
  refine hMink.trans ?_
  have hpt : ∀ z, yNorm 2 (fun y => ΔK z * (commV (ovTilSym J τ) x G z y - ((β z : ℝ) : ℂ) * c y)) ≤
      ‖ΔK z‖ * yNorm 2 (commV (ovTilSym J τ) x G z) + A₁ * (‖ΔK z‖ * β z) := by
    intro z
    rw [yNorm_fun_const_mul (by norm_num)]
    have h1 : yNorm 2 (fun y => commV (ovTilSym J τ) x G z y - ((β z : ℝ) : ℂ) * c y) ≤
        yNorm 2 (commV (ovTilSym J τ) x G z) + β z * A₁ := by
      have h0 := yNorm_sub_ov (s := 2) (by norm_num) (commV (ovTilSym J τ) x G z) (fun y => ((β z : ℝ) : ℂ) * c y)
      refine h0.trans ?_
      rw [yNorm_fun_const_mul (by norm_num), Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hβ.nonneg z)]
      have := hβ.nonneg z
      gcongr
    calc ‖ΔK z‖ * yNorm 2 (fun y => commV (ovTilSym J τ) x G z y - ((β z : ℝ) : ℂ) * c y)
        ≤ ‖ΔK z‖ * (yNorm 2 (commV (ovTilSym J τ) x G z) + β z * A₁) := by gcongr
      _ = _ := by ring
  have hpA : ∀ z, ‖ΔK z‖ * yNorm 2 (commV (ovTilSym J τ) x G z) ≤
      (endC3 M C₀ * 2 ^ M * Acc * (ℓ / T) * T⁻¹ * W) * jb ((z - x) / ℓ) ^ (-(2 : ℝ)) := fun z => by
    have h := commutator_term_le (M := M) hT hℓ hℓT hc₃ hAcc0 hW0.le (abs_nonneg (z - x))
      (yNorm_nonneg' 2 _) (norm_nonneg _) (hΔpt z) (hdec' z)
    have e : jb (|z - x| / ℓ) = jb ((z - x) / ℓ) := by unfold jb; rw [abs_div, abs_div, abs_abs]
    rw [e] at h; exact h
  have hpB : ∀ z, ‖ΔK z‖ * β z ≤ (endC3 M C₀ * 2 ^ M * T⁻¹ * (L / T) * W) * β z := fun z => by
    by_cases hz : L < |z - x|
    · rw [hβ.supp z hz]; simp
    · push Not at hz
      have h1 := hΔpt z
      have hA : |z - x| / T ≤ L / T := div_le_div_of_nonneg_right hz hT.le
      have hjb : jb (|z - x| / T) ≤ 2 := by
        unfold jb
        rw [abs_of_nonneg (by positivity)]
        have : L / T ≤ 1 := (div_le_one hT).2 hLT
        linarith
      have hjM : jb (|z - x| / T) ^ M ≤ 2 ^ M := pow_le_pow_left₀ (jb_pos _).le hjb M
      have hβ0 := hβ.nonneg z
      have hT' : 0 ≤ endC3 M C₀ * T⁻¹ := by positivity
      calc ‖ΔK z‖ * β z ≤ (endC3 M C₀ * T⁻¹ * (|z - x| / T) * jb (|z - x| / T) ^ M * W) * β z :=
            mul_le_mul_of_nonneg_right h1 hβ0
        _ ≤ (endC3 M C₀ * T⁻¹ * (L / T) * 2 ^ M * W) * β z := by
            have : 0 ≤ jb (|z - x| / T) ^ M := pow_nonneg (jb_pos _).le M
            gcongr
        _ = _ := by ring
  have hBA : Integrable (fun z => (endC3 M C₀ * 2 ^ M * Acc * (ℓ / T) * T⁻¹ * W) * jb ((z - x) / ℓ) ^ (-(2 : ℝ))) :=
    (integrable_jb_rpow (c := x) hℓ (r := 2) (by norm_num)).const_mul _
  have hBB : Integrable (fun z => A₁ * ((endC3 M C₀ * 2 ^ M * T⁻¹ * (L / T) * W) * β z)) :=
    (hβ.integrable.const_mul _).const_mul _
  have hint_le := integral_mono_of_nonneg
    (f := fun z => yNorm 2 (fun y => ΔK z * (commV (ovTilSym J τ) x G z y - ((β z : ℝ) : ℂ) * c y)))
    (g := fun z => (endC3 M C₀ * 2 ^ M * Acc * (ℓ / T) * T⁻¹ * W) * jb ((z - x) / ℓ) ^ (-(2 : ℝ)) +
      A₁ * ((endC3 M C₀ * 2 ^ M * T⁻¹ * (L / T) * W) * β z))
    (Filter.Eventually.of_forall fun z => yNorm_nonneg' _ _) (hBA.add hBB)
    (Filter.Eventually.of_forall fun z => (hpt z).trans (add_le_add (hpA z) (mul_le_mul_of_nonneg_left (hpB z) hA₁)))
  refine hint_le.trans ?_
  rw [integral_add hBA hBB, integral_const_mul, integral_const_mul, integral_const_mul, integral_jb_rpow x hℓ (by norm_num),
    hβ.mass]
  -- final algebra
  have hℓT_eq : ℓ / T = r * ρ := by rw [← hℓL, ← hρ]; field_simp
  have e1 : (ℓ / T) * T⁻¹ * (2 * ℓ / (2 - 1)) = 2 * (r * ρ) ^ 2 := by
    rw [← hℓT_eq]; field_simp; ring
  have e2 : T⁻¹ * (L / T) * L = ρ ^ 2 := by rw [← hρ]; field_simp
  have hM2 : (0 : ℝ) ≤ 2 ^ M := by positivity
  have hW' : 0 ≤ W := hW0.le
  have hρ2 : 0 ≤ ρ ^ 2 := by positivity
  have hr2 : 0 ≤ r ^ 2 := by positivity
  have hc3M : 0 ≤ endC3 M C₀ * 2 ^ M * W * ρ ^ 2 := by positivity
  calc (endC3 M C₀ * 2 ^ M * Acc * (ℓ / T) * T⁻¹ * W) * (2 * ℓ / (2 - 1)) +
        A₁ * ((endC3 M C₀ * 2 ^ M * T⁻¹ * (L / T) * W) * L)
      = (endC3 M C₀ * 2 ^ M * W * ρ ^ 2) * (2 * Acc * r ^ 2 + A₁) := by
        have : (endC3 M C₀ * 2 ^ M * Acc * (ℓ / T) * T⁻¹ * W) * (2 * ℓ / (2 - 1)) =
            endC3 M C₀ * 2 ^ M * Acc * W * ((ℓ / T) * T⁻¹ * (2 * ℓ / (2 - 1))) := by ring
        rw [this, e1]
        have : (endC3 M C₀ * 2 ^ M * T⁻¹ * (L / T) * W) * L = endC3 M C₀ * 2 ^ M * W * (T⁻¹ * (L / T) * L) := by ring
        rw [this, e2]
        ring
    _ ≤ (endC3 M C₀ * 2 ^ M * W * ρ ^ 2) * ((2 * endQ J M q N * r ^ 2 + 1) * (Ag + A₁)) := by
        refine mul_le_mul_of_nonneg_left ?_ hc3M
        have hQ' := hQ
        rw [hAccdef]
        linarith only [mul_nonneg (mul_nonneg hQ' hr2) hA₁, hAg]
    _ = _ := by rw [hW]; ring

end EndpointVec

end PrimeBHT.TimeFrequency.X2
