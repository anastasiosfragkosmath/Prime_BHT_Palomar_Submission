module

public import PrimeBHT.TimeFrequency.X2.Psp.O2Compose

/-!
# X2, V13 O2 (b): the symbols of the overlapping projection error estimate (frame centred at `0`)

* `lpSym J τ = lowSym 0 τ - lowSym 0 (τ + J)`: the symbol of `S_τ` (frame `0`); it vanishes for `|ξ| ≤ 4 · 2^{-(τ+J)}` and
  for `|ξ| ≥ (17/4) 2^{-τ}`;
* `tilSym J τ` (`OverlapCoef`): `= 1` on `4 · 2^{-(τ+J)} ≤ |ξ| ≤ (17/4) 2^{-τ}` (`tilSym_eq_one_ann`), so `tilSym · lpSym = lpSym`;
* `ovTilSym J τ = lowSym 0 (τ-1) - lowSym 0 (τ+J) (5/4 ·)`: a second reproducing symbol, `= 1` on the same annulus
  (`ovTilSym_eq_one`) and `= 0` on `|ξ| ≤ 3 · 2^{-(τ+J)}` (`ovTilSym_eq_zero_of_le`): it ANNIHILATES every multiplier supported in
  `|ξ| ≤ 3 · 2^{-σ}`, `τ + J ≤ σ` (the overlapping multipliers of a tree layer; `tilSym` does not for `τ = σ - J`);
* the kernel `ovTilKer = 𝓕⁻ ovTilSym`: decay of every order, `∫ ovTilKer = 0`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-! ## The symbol of `S_τ` in the frame centred at `0` -/

/-- `S_τ = T_τ - T_{τ+J}` (frame `0`). -/
def lpSym (J : ℕ) (τ : ℤ) (ξ : ℝ) : ℂ := lowSym 0 τ ξ - lowSym 0 (τ + (J : ℤ)) ξ

theorem contDiff_lpSym (J : ℕ) (τ : ℤ) : ContDiff ℝ ∞ (lpSym J τ) :=
  (contDiff_lowSym 0 _).sub (contDiff_lowSym 0 _)

theorem zpow_neg_add_le {τ : ℤ} {J : ℕ} : (2 : ℝ) ^ (-(τ + (J : ℤ))) ≤ (2 : ℝ) ^ (-τ) :=
  zpow_le_zpow_right₀ (by norm_num) (by omega)

theorem zpow_neg_sub_one (τ : ℤ) : (2 : ℝ) ^ (-(τ - 1)) = 2 * (2 : ℝ) ^ (-τ) := by
  rw [show -(τ - 1) = -τ + 1 by ring, zpow_add₀ (by norm_num)]; simp [mul_comm]

theorem lpSym_eq_zero_of_le {J : ℕ} {τ : ℤ} {ξ : ℝ} (h : |ξ| ≤ 4 * (2 : ℝ) ^ (-(τ + (J : ℤ)))) :
    lpSym J τ ξ = 0 := by
  have h1 : |ξ - 0| ≤ 4 * (2 : ℝ) ^ (-(τ + (J : ℤ))) := by rwa [sub_zero]
  have h2 : |ξ - 0| ≤ 4 * (2 : ℝ) ^ (-τ) := h1.trans (by have := zpow_neg_add_le (τ := τ) (J := J); linarith)
  unfold lpSym
  rw [lowSym_eq_one h2, lowSym_eq_one h1, sub_self]

theorem lpSym_eq_zero_of_ge {J : ℕ} {τ : ℤ} {ξ : ℝ} (h : 17 / 4 * (2 : ℝ) ^ (-τ) ≤ |ξ|) : lpSym J τ ξ = 0 := by
  have h1 : 17 / 4 * (2 : ℝ) ^ (-τ) ≤ |ξ - 0| := by rwa [sub_zero]
  have h2 : 17 / 4 * (2 : ℝ) ^ (-(τ + (J : ℤ))) ≤ |ξ - 0| := by
    refine le_trans ?_ h1
    have := zpow_neg_add_le (τ := τ) (J := J)
    linarith
  unfold lpSym
  rw [lowSym_eq_zero h1, lowSym_eq_zero h2, sub_self]

/-! ## The reproducing symbols -/

theorem tilSym_eq_one_ann (J : ℕ) (τ : ℤ) {ξ : ℝ} (h1 : 4 * (2 : ℝ) ^ (-(τ + (J : ℤ))) ≤ |ξ|)
    (h2 : |ξ| ≤ 17 / 4 * (2 : ℝ) ^ (-τ)) : tilSym J τ ξ = 1 := by
  have hp := zpow_two_pos (-τ)
  have e1 := zpow_neg_sub_one τ
  have e2 : (2 : ℝ) ^ (-(τ + (J : ℤ) + 1)) = (2 : ℝ) ^ (-(τ + (J : ℤ))) / 2 := by
    rw [show -(τ + (J : ℤ) + 1) = -(τ + (J : ℤ)) - 1 by ring, zpow_sub₀ (by norm_num), zpow_one]
  have hq := zpow_two_pos (-(τ + (J : ℤ)))
  unfold tilSym
  rw [lowSym_eq_one (θ := 0) (σ := τ - 1) (by rw [sub_zero, e1]; linarith),
    lowSym_eq_zero (θ := 0) (σ := τ + (J : ℤ) + 1) (by rw [sub_zero, e2]; linarith), sub_zero]

theorem tilSym_mul_lpSym (J : ℕ) (τ : ℤ) (ξ : ℝ) : tilSym J τ ξ * lpSym J τ ξ = lpSym J τ ξ := by
  by_cases h1 : |ξ| ≤ 4 * (2 : ℝ) ^ (-(τ + (J : ℤ)))
  · rw [lpSym_eq_zero_of_le h1, mul_zero]
  by_cases h2 : 17 / 4 * (2 : ℝ) ^ (-τ) ≤ |ξ|
  · rw [lpSym_eq_zero_of_ge h2, mul_zero]
  push Not at h1 h2
  rw [tilSym_eq_one_ann J τ h1.le h2.le, one_mul]

/-- The second reproducing symbol `S̃''`: `lowSym 0 (τ-1) - lowSym 0 (τ+J) (5/4 ·)`. -/
def ovTilSym (J : ℕ) (τ : ℤ) (ξ : ℝ) : ℂ := lowSym 0 (τ - 1) ξ - lowSym 0 (τ + (J : ℤ)) ((5 / 4) * ξ)

theorem contDiff_ovTilSym (J : ℕ) (τ : ℤ) : ContDiff ℝ ∞ (ovTilSym J τ) :=
  (contDiff_lowSym 0 _).sub ((contDiff_lowSym 0 _).comp (contDiff_const.mul contDiff_id))

theorem ovTilSym_eq_zero_of_le {J : ℕ} {τ : ℤ} {ξ : ℝ} (h : |ξ| ≤ 3 * (2 : ℝ) ^ (-(τ + (J : ℤ)))) :
    ovTilSym J τ ξ = 0 := by
  have hq := zpow_two_pos (-(τ + (J : ℤ)))
  have e1 := zpow_neg_sub_one τ
  have h3 := zpow_neg_add_le (τ := τ) (J := J)
  have hp := zpow_two_pos (-τ)
  unfold ovTilSym
  rw [lowSym_eq_one (θ := 0) (σ := τ - 1) (by rw [sub_zero, e1]; linarith),
    lowSym_eq_one (θ := 0) (σ := τ + (J : ℤ)) (by
      rw [sub_zero, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4)]; linarith), sub_self]

theorem ovTilSym_eq_one {J : ℕ} {τ : ℤ} {ξ : ℝ} (h1 : 4 * (2 : ℝ) ^ (-(τ + (J : ℤ))) ≤ |ξ|)
    (h2 : |ξ| ≤ 17 / 4 * (2 : ℝ) ^ (-τ)) : ovTilSym J τ ξ = 1 := by
  have hq := zpow_two_pos (-(τ + (J : ℤ)))
  have e1 := zpow_neg_sub_one τ
  have hp := zpow_two_pos (-τ)
  unfold ovTilSym
  rw [lowSym_eq_one (θ := 0) (σ := τ - 1) (by rw [sub_zero, e1]; linarith),
    lowSym_eq_zero (θ := 0) (σ := τ + (J : ℤ)) (by
      rw [sub_zero, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4)]; linarith), sub_zero]

theorem ovTilSym_mul_lpSym (J : ℕ) (τ : ℤ) (ξ : ℝ) : ovTilSym J τ ξ * lpSym J τ ξ = lpSym J τ ξ := by
  by_cases h1 : |ξ| ≤ 4 * (2 : ℝ) ^ (-(τ + (J : ℤ)))
  · rw [lpSym_eq_zero_of_le h1, mul_zero]
  by_cases h2 : 17 / 4 * (2 : ℝ) ^ (-τ) ≤ |ξ|
  · rw [lpSym_eq_zero_of_ge h2, mul_zero]
  push Not at h1 h2
  rw [ovTilSym_eq_one h1.le h2.le, one_mul]

/-- `ovTilSym` annihilates a symbol supported in `|ξ| ≤ 3 · 2^{-σ}` when `τ + J ≤ σ`. -/
theorem ovTilSym_mul_m {J : ℕ} {τ σ : ℤ} (hστ : τ + (J : ℤ) ≤ σ) {m : ℝ → ℂ}
    (hm : ∀ ξ, 3 * (2 : ℝ) ^ (-σ) < |ξ| → m ξ = 0) (ξ : ℝ) : ovTilSym J τ ξ * m ξ = 0 := by
  by_cases h : 3 * (2 : ℝ) ^ (-σ) < |ξ|
  · rw [hm ξ h, mul_zero]
  push Not at h
  have : (2 : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-(τ + (J : ℤ))) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  rw [ovTilSym_eq_zero_of_le (by linarith), zero_mul]

theorem hasCompactSupport_ovTilSym (J : ℕ) (τ : ℤ) : HasCompactSupport (ovTilSym J τ) := by
  refine hasCompactSupport_of_far (c := 0) (r := 9 * (2 : ℝ) ^ (-τ)) fun ξ hξ => ?_
  rw [sub_zero] at hξ
  have hp := zpow_two_pos (-τ)
  have e1 := zpow_neg_sub_one τ
  have h3 := zpow_neg_add_le (τ := τ) (J := J)
  unfold ovTilSym
  rw [lowSym_eq_zero (θ := 0) (σ := τ - 1) (by rw [sub_zero, e1]; linarith),
    lowSym_eq_zero (θ := 0) (σ := τ + (J : ℤ)) (by
      rw [sub_zero, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4)]; linarith), sub_self]

theorem hasCompactSupport_lpSym (J : ℕ) (τ : ℤ) : HasCompactSupport (lpSym J τ) := by
  refine hasCompactSupport_of_far (c := 0) (r := 9 * (2 : ℝ) ^ (-τ)) fun ξ hξ => ?_
  rw [sub_zero] at hξ
  have hp := zpow_two_pos (-τ)
  exact lpSym_eq_zero_of_ge (by linarith)

theorem hasCompactSupport_tilSym (J : ℕ) (τ : ℤ) : HasCompactSupport (tilSym J τ) :=
  hasCompactSupport_of_far (c := 0) (r := 9 * (2 : ℝ) ^ (-τ)) fun ξ hξ =>
    tilSym_eq_zero_of_far J τ (by simpa using hξ)

theorem ovTilSym_eq_zero_of_far (J : ℕ) (τ : ℤ) {ξ : ℝ} (h : 9 * (2 : ℝ) ^ (-τ) < |ξ|) : ovTilSym J τ ξ = 0 := by
  have hp := zpow_two_pos (-τ)
  have e1 := zpow_neg_sub_one τ
  have h3 := zpow_neg_add_le (τ := τ) (J := J)
  unfold ovTilSym
  rw [lowSym_eq_zero (θ := 0) (σ := τ - 1) (by rw [sub_zero, e1]; linarith),
    lowSym_eq_zero (θ := 0) (σ := τ + (J : ℤ)) (by
      rw [sub_zero, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4)]; linarith), sub_self]

/-! ## The kernel of `ovTilSym` -/

/-- The kernel of `S̃''` (frame `0`). -/
def ovTilKer (J : ℕ) (τ : ℤ) : ℝ → ℂ := 𝓕⁻ (ovTilSym J τ)

theorem norm_ovTilSym_le (J : ℕ) (τ : ℤ) (ξ : ℝ) : ‖ovTilSym J τ ξ‖ ≤ 2 := by
  unfold ovTilSym
  have h : ∀ (τ' : ℤ) (x : ℝ), ‖lowSym 0 τ' x‖ ≤ 1 := fun τ' x => by
    unfold lowSym
    rw [Complex.norm_real, Real.norm_of_nonneg (lowProfile_nonneg _)]
    exact lowProfile_le_one _
  calc ‖lowSym 0 (τ - 1) ξ - lowSym 0 (τ + (J : ℤ)) ((5 / 4) * ξ)‖
      ≤ ‖lowSym 0 (τ - 1) ξ‖ + ‖lowSym 0 (τ + (J : ℤ)) ((5 / 4) * ξ)‖ := norm_sub_le _ _
    _ ≤ 2 := by linarith [h (τ - 1) ξ, h (τ + (J : ℤ)) ((5 / 4) * ξ)]

theorem norm_iteratedDeriv_ovTilSym_le {M : ℕ} {Λ : ℝ}
    (hΛ : ∀ a ≤ M, ∀ u : ℝ, ‖iteratedDeriv a (fun u : ℝ => ((lowProfile u : ℝ) : ℂ)) u‖ ≤ Λ)
    (J : ℕ) (τ : ℤ) (ξ : ℝ) :
    ‖iteratedDeriv M (ovTilSym J τ) ξ‖ ≤ 2 * Λ * ((2 : ℝ) ^ (τ + (J : ℤ) + 1)) ^ M := by
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0 (Nat.zero_le _) 0)
  have h1 := norm_iteratedDeriv_lowSym_le hΛ 0 (τ - 1) (le_refl M) ξ
  have hf : ContDiff ℝ M (lowSym 0 (τ + (J : ℤ))) :=
    (contDiff_lowSym 0 _).of_le (by exact_mod_cast le_top)
  have e0 : iteratedDeriv M (fun x => lowSym 0 (τ + (J : ℤ)) ((5 / 4) * x)) ξ =
      (5 / 4 : ℝ) ^ M • iteratedDeriv M (lowSym 0 (τ + (J : ℤ))) ((5 / 4) * ξ) := by
    have := congrFun (iteratedDeriv_comp_const_smul (n := M) (f := lowSym 0 (τ + (J : ℤ))) hf (5 / 4 : ℝ)) ξ
    simpa only [smul_eq_mul] using this
  have h2 := norm_iteratedDeriv_lowSym_le hΛ 0 (τ + (J : ℤ)) (le_refl M) ((5 / 4) * ξ)
  have e : iteratedDeriv M (ovTilSym J τ) ξ =
      iteratedDeriv M (lowSym 0 (τ - 1)) ξ -
        iteratedDeriv M (fun x => lowSym 0 (τ + (J : ℤ)) ((5 / 4) * x)) ξ := by
    unfold ovTilSym
    exact iteratedDeriv_sub ((contDiff_lowSym 0 _).contDiffAt.of_le (by exact_mod_cast le_top))
      (((contDiff_lowSym 0 _).comp (contDiff_const.mul contDiff_id)).contDiffAt.of_le (by exact_mod_cast le_top))
  have h3 : ((2 : ℝ) ^ (τ - 1)) ^ M ≤ ((2 : ℝ) ^ (τ + (J : ℤ) + 1)) ^ M :=
    pow_le_pow_left₀ (zpow_two_pos _).le (zpow_le_zpow_right₀ (by norm_num) (by omega)) M
  have h4 : (5 / 4 : ℝ) ^ M * ((2 : ℝ) ^ (τ + (J : ℤ))) ^ M ≤ ((2 : ℝ) ^ (τ + (J : ℤ) + 1)) ^ M := by
    rw [← mul_pow, zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
    refine pow_le_pow_left₀ (by positivity) ?_ M
    have := zpow_two_pos (τ + (J : ℤ))
    nlinarith
  rw [e, e0]
  calc ‖iteratedDeriv M (lowSym 0 (τ - 1)) ξ - (5 / 4 : ℝ) ^ M • iteratedDeriv M (lowSym 0 (τ + (J : ℤ))) ((5 / 4) * ξ)‖
      ≤ ‖iteratedDeriv M (lowSym 0 (τ - 1)) ξ‖ +
        ‖(5 / 4 : ℝ) ^ M • iteratedDeriv M (lowSym 0 (τ + (J : ℤ))) ((5 / 4) * ξ)‖ := norm_sub_le _ _
    _ ≤ ((2 : ℝ) ^ (τ - 1)) ^ M * Λ + (5 / 4 : ℝ) ^ M * (((2 : ℝ) ^ (τ + (J : ℤ))) ^ M * Λ) := by
        refine add_le_add h1 ?_
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ 2 * Λ * ((2 : ℝ) ^ (τ + (J : ℤ) + 1)) ^ M := by
        nlinarith [mul_le_mul_of_nonneg_right h3 hΛ0, mul_le_mul_of_nonneg_right h4 hΛ0]

/-- **Kernel decay of `S̃''`**: `‖𝓕⁻ ovTilSym (w)‖ ≤ C_M 2^{-τ} (1 + 2^{-(τ+J+1)} |w|)^{-M}`. -/
theorem norm_ovTilKer_le (M : ℕ) (J : ℕ) (τ : ℤ) (w : ℝ) :
    ‖ovTilKer J τ w‖ ≤ tilConst M * (2 : ℝ) ^ (-τ) * ((1 + (2 : ℝ) ^ (-(τ + (J : ℤ) + 1)) * |w|)⁻¹) ^ M := by
  obtain ⟨hΛ0, hΛ⟩ := Classical.choose_spec (exists_lowProfile_deriv_bound M)
  set Λ := Classical.choose (exists_lowProfile_deriv_bound M) with hΛdef
  set A : ℝ := max 2 (2 * Λ) with hA
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-(τ + (J : ℤ) + 1)) := zpow_two_pos _
  have hp := zpow_two_pos (-τ)
  have h := norm_fourierInv_le_pow (n := ovTilSym J τ) (c := 0) (r := 9 * (2 : ℝ) ^ (-τ)) (A := A)
    (l := (2 : ℝ) ^ (-(τ + (J : ℤ) + 1))) M (by positivity) hl
    ((contDiff_ovTilSym J τ).of_le (by exact_mod_cast le_top))
    (fun ξ hξ => ovTilSym_eq_zero_of_far J τ (by simpa using hξ))
    (fun ξ => (norm_ovTilSym_le J τ ξ).trans (le_max_left _ _))
    (fun ξ => by
      refine (norm_iteratedDeriv_ovTilSym_le hΛ J τ ξ).trans ?_
      have : ((2 : ℝ) ^ (-(τ + (J : ℤ) + 1)))⁻¹ = (2 : ℝ) ^ (τ + (J : ℤ) + 1) := by
        rw [← zpow_neg, neg_neg]
      rw [this]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) w
  refine h.trans (le_of_eq ?_)
  unfold tilConst
  rw [← hΛdef, ← hA]
  ring

theorem ovTilSym_zero (J : ℕ) (τ : ℤ) : ovTilSym J τ 0 = 0 := by
  have := ovTilSym_eq_zero_of_le (J := J) (τ := τ) (ξ := 0) (by
    rw [abs_zero]; have := zpow_two_pos (-(τ + (J : ℤ))); linarith)
  exact this

/-! ## The multipliers of a layer in the frame centred at `θ`: support -/

/-- A multiplier of the class `M_ω(𝔭)` (`β ≤ 11/4`) of an overlapping slot (`|θ - c| ≤ 13/8 · 2^{-σ}`) is supported in
`|ξ - θ| ≤ 3 · 2^{-σ}`. -/
theorem inMult_supp_theta {𝔭 : Params} {σ : ℤ} {c θ : ℝ} {m : ℝ → ℂ} (hm : InMult 𝔭 σ c m) (hβ : 𝔭.β ≤ 11 / 4)
    (hθ : |θ - c| ≤ 13 / 8 * (2 : ℝ) ^ (-σ)) {ξ : ℝ} (hξ : 3 * (2 : ℝ) ^ (-σ) < |ξ - θ|) : m ξ = 0 := by
  have hp := zpow_two_pos (-σ)
  refine hm.2.1 ξ ?_
  have h1 : |ξ - θ| ≤ |ξ - c| + |θ - c| := by
    have := abs_sub_le ξ c θ
    rw [abs_sub_comm c θ] at this
    exact this
  nlinarith [h1, hθ, hm.2.1]

end PrimeBHT.TimeFrequency.X2
