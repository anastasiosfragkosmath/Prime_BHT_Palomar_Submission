module

public import PrimeBHT.TimeFrequency.Interp.Discrete
public import PrimeBHT.TimeFrequency.Interp.Duality
public import Mathlib.MeasureTheory.Function.SimpleFunc
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# R6c: restricted type ⇒ strong type (abstract), including the quasi-Banach range `r ≤ 1`

Blueprint `docs/x1-blueprint.md`, node R6c (R6c-I, R6c-II, Corollary (MB)); discrete lemmas D1,
D2 in `PrimeBHT.TimeFrequency.Interp.Discrete`. Phase-1 re-derivation (X1-Q5):
`docs/audits/R6c-rederivation.md`. **Verdict: the blueprint's argument is correct.** Corrections
(none strengthens a target): `p_i > 1` is not needed by D1/D2 (only `p_i > 0`); no normalization
`‖f_i‖ = 1` is needed; (RS) is needed only at the two points `a* ± δ₀(1,-1)` of the segment
`a₁ + a₂ = 1/r` (a full ball is not needed); the zero-measure levels need positive exponents at
the points used (`δ₀ < 1/p₂` for R6c-I, `δ₀/2 < 1/p₂, 1/p₃` for R6c-II); the measurability of
the outputs of `T` follows from the finiteness of the restricted bound (Mathlib's `eLpNorm` is `∞`
for non-measurable functions), so it is not a hypothesis; R6c-II does not use `Λ ≥ 0`. D2 is
proved with the weight `pairWeight(μ₁,μ₂)^γ pairWeight(μ₁,μ₃)^γ`, obtained from two independent
pair choices `±δ₀/2` for the pairs `(1,2)`, `(1,3)`; it dominates the blueprint's
`(μ_min/μ_max)^(2γ)` (`tripleWeight_le_pairWeight`), so the blueprint's D2 follows.

## Setting

`α` (inputs) and `β` (output) are arbitrary measurable spaces with measures `μ`, `ν` (for X1:
`α = β = ℝ`, `μ = ν = volume`); inputs take values in a real normed space `F` (for X1: `ℂ`),
outputs in a real normed space `E` (`ℂ`). "Simple" = Mathlib `SimpleFunc α F` (finite range,
measurable fibres). Exponents are real; Lebesgue exponents enter as `ENNReal.ofReal p`.
Dyadic level sets: `levelSet f n = {f ≠ 0, Int.log 2 ‖f‖ = n}`, `piece f n = 2^(-(n+1)) f 1_{F_n}`,
`f = Σ_{n ∈ levels f} 2^(n+1) • piece f n` (`eq_sum_smul_piece`).

## Final signatures (all proved, axioms `propext, Classical.choice, Quot.sound`)

* `eLpNorm_le_of_restrictedStrong` (**R6c-I**, `r ≤ 1`): hypotheses `0 < p₁ p₂ r`, `r ≤ 1`,
  `1/r = 1/p₁ + 1/p₂`, `0 < δ₀ < 1/p₂`, `0 ≤ K`; `T : (α → F) → (α → F) → β → E` additive and
  real-homogeneous in each slot on simple functions (`hadd₁ hsmul₁ hadd₂ hsmul₂`); and
  `hRS : ∀ t, |t| < 2δ₀ → ∀ E₁ E₂ measurable of finite measure, ∀ simple g₁ g₂ with
  ‖gᵢ‖ ≤ 1_{Eᵢ}, eLpNorm (T g₁ g₂) (ofReal r) ν ≤ ofReal K * μ E₁ ^ (1/p₁ + t) * μ E₂ ^ (1/p₂ - t)`.
  Conclusion for simple `f₁ f₂` with finite `eLpNorm fᵢ (ofReal pᵢ) μ`:
  `eLpNorm (T f₁ f₂) (ofReal r) ν ≤ ofReal (strongConstI p₁ p₂ r δ₀ K) * ‖f₁‖_{p₁} * ‖f₂‖_{p₂}`,
  `strongConstI = (K^r 4^r d1Const p₁ p₂ (r/p₁) (δ₀ r))^(1/r)`.
* `eLpNorm_le_of_restrictedStrong_of_ae_tendsto`: the same for arbitrary `f₁ f₂ : α → F` with
  finite `L^{pᵢ}` norm, given simple `sᵢ : ℕ → α →ₛ F`, `‖sᵢ j x‖ ≤ M ‖fᵢ x‖`, and
  `T (s₁ j) (s₂ j) → T f₁ f₂` `ν`-a.e. (Fatou); constant `strongConstI * M * M`.
* `eLpNorm_le_of_restrictedStrong_of_continuous` (**Corollary (MB)**, `r ≤ 1`): measurable
  `f₁ f₂` (`[BorelSpace F] [SeparableSpace F]`), with the continuity hypothesis `hcont` (for every
  simple approximation with `‖sᵢ j‖ ≤ 2‖fᵢ‖` converging pointwise, `T(s₁ j, s₂ j) → T(f₁,f₂)` a.e.);
  constant `strongConstI * 2 * 2`. The approximants are Mathlib's `SimpleFunc.approxOn`.
* `form_le_of_restrictedType` (**R6c-II**): `0 < p₁ p₂ p₃`, `Σ 1/pᵢ = 1`, `0 < δ₀`,
  `δ₀/2 < 1/p₂`, `δ₀/2 < 1/p₃`, `0 ≤ K`; `Λ : (α → F) → (α → F) → (α → F) → ℝ` subadditive and
  nonnegatively homogeneous in each slot on simple functions; `hRT`: for all `d` with `Σ dᵢ = 0`,
  `|dᵢ| ≤ δ₀`, all measurable finite-measure `Eᵢ` and simple `‖gᵢ‖ ≤ 1_{Eᵢ}`:
  `Λ g₁ g₂ g₃ ≤ K * Π (μ Eᵢ).toReal ^ (1/pᵢ + dᵢ)`. Conclusion for simple `fᵢ ∈ L^{pᵢ}`:
  `Λ f₁ f₂ f₃ ≤ strongConstII p₁ p₂ p₃ δ₀ K * Π (eLpNorm fᵢ (ofReal pᵢ) μ).toReal`,
  `strongConstII = 8 K d2Const p₁ p₂ p₃ (δ₀/2)`.
* `form_le_of_restrictedType_of_tendsto`: the same for general `fᵢ` along simple approximants
  `‖sᵢ j‖ ≤ M‖fᵢ‖` with `Λ(s₁ j, s₂ j, s₃ j) → Λ(f₁,f₂,f₃)`; constant `strongConstII * M^3`.
* `eLpNorm_le_of_restrictedType` (**R6c-II, operator form**, `1 < r`; `α = β`, `F = E = ℂ`,
  `μ = ν` σ-finite): with `p₃ := r/(r-1)`, the hypotheses of `form_le_of_restrictedType` on `Λ`,
  `hTmeas : ∀ simple f₁ f₂, AEStronglyMeasurable (T f₁ f₂) μ` and
  `hdom : ∀ simple f₁ f₂ h, ‖∫ T f₁ f₂ · h‖ ≤ Λ f₁ f₂ h`, conclusion for simple `fᵢ ∈ L^{pᵢ}`:
  `eLpNorm (T f₁ f₂) (ofReal r) μ ≤ ofReal (2 * (strongConstII p₁ p₂ (r/(r-1)) δ₀ K * ‖f₁‖ * ‖f₂‖))`
  (via the duality lemma `eLpNorm_le_of_forall_simpleFunc` of `…Interp.Duality`).
* `eLpNorm_le_of_restrictedType_of_ae_tendsto` (**Corollary (MB), `r > 1`**): the same for general
  inputs along simple approximants (`‖sᵢ j‖ ≤ M‖fᵢ‖`, a.e. convergence of `T`), constant `· M²`.

## How R6b instantiates the hypotheses

* R6c-I: `T := Π_P` (`Π_P(f₁,f₂) = Σ_{t∈P} |I_t|^{-1/2} ⟨f₁,φ_{t,1}⟩⟨f₂,φ_{t,2}⟩ φ_{t,3}`), `F = E = ℂ`,
  `p₁ = p`, `p₂ = q`; `hadd/hsmul` hold for all bounded measurable inputs since the packets are
  integrable (linearity of the Bochner integral). R6b (RS) at `a = (1/p + t, 1/q - t) ∈ U_*` with
  `r_a = r` gives `hRS` with `K := sup_{|t| ≤ δ₀} C'_a` (finite: `C'_a` locally bounded). Choose
  `δ₀` with `B(a*, 2δ₀) ⊆ U_*`; then `δ₀ < 1/q` holds.
* R6c-II: `Λ := Λ_P` (absolute values of the coefficients), `p₃ = r'`; subadditivity and
  homogeneity are those of `|⟨·,φ⟩|`; `hRT` is R6a at `α* + d ∈ (0,1)³`.
* (MB): `hcont` for `Π_P` (finite `P`) is dominated convergence in each coefficient
  `⟨sᵢ j, φ⟩ → ⟨fᵢ, φ⟩` (`‖sᵢ j‖ ≤ 2‖fᵢ‖`, `fᵢ φ ∈ L¹`), the sum over `P` being finite.

## Left to the consumer

* The hypotheses themselves: (RS)/(RT) with one constant `K` on the stated exponent sets (from
  R6a/R6b with locally bounded constants), the structural identities of `Π_P`, `Λ_P`
  (`hadd/hsmul`, `hsub/hhom`, `hdom : |⟨Π_P(f₁,f₂),h⟩| ≤ Λ_P(f₁,f₂,h)`, `hTmeas`), and the
  continuity `hcont`/`hlim` along simple approximations (dominated convergence in each coefficient).
* At `r = 1` use R6c-I (R6c-II needs `p₃ = r' < ∞`).
-/

@[expose] public section

namespace PrimeBHT.TimeFrequency.Interp

open MeasureTheory Finset
open scoped ENNReal

local infixr:25 " →ₛ " => SimpleFunc

variable {α β F E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Dyadic level sets of a simple function -/

/-- The `n`-th dyadic level set `{x : f x ≠ 0, 2^n ≤ ‖f x‖ < 2^(n+1)}` (window `Int.log 2`). -/
def levelSet (f : α → F) (n : ℤ) : Set α := {x | f x ≠ 0 ∧ Int.log 2 ‖f x‖ = n}

omit [NormedSpace ℝ F] in
lemma measurableSet_levelSet (f : α →ₛ F) (n : ℤ) : MeasurableSet (levelSet f n) :=
  f.measurableSet_preimage {v | v ≠ 0 ∧ Int.log 2 ‖v‖ = n}

open Classical in
/-- The (finite) set of nonempty dyadic levels of a simple function. -/
noncomputable def levels (f : α →ₛ F) : Finset ℤ :=
  (f.range.filter (· ≠ 0)).image (fun v => Int.log 2 ‖v‖)

omit [NormedSpace ℝ F] in
open Classical in
lemma mem_levels {f : α →ₛ F} {x : α} (hx : f x ≠ 0) : Int.log 2 ‖f x‖ ∈ levels f :=
  mem_image.2 ⟨f x, mem_filter.2 ⟨f.mem_range_self x, hx⟩, rfl⟩

/-- The normalized `n`-th piece `2^(-(n+1)) f 1_{F_n}`, so that `‖piece f n‖ ≤ 1_{F_n}`. -/
noncomputable def piece (f : α →ₛ F) (n : ℤ) : α →ₛ F :=
  ((2 : ℝ) ^ (n + 1))⁻¹ • f.restrict (levelSet f n)

lemma piece_apply (f : α →ₛ F) (n : ℤ) (x : α) :
    piece f n x = ((2 : ℝ) ^ (n + 1))⁻¹ • (levelSet f n).indicator f x := by
  simp only [piece, SimpleFunc.coe_smul, Pi.smul_apply,
    SimpleFunc.coe_restrict _ (measurableSet_levelSet f n)]

omit [MeasurableSpace α] [NormedSpace ℝ F] in
lemma norm_lt_of_mem_levelSet {f : α → F} {n : ℤ} {x : α} (hx : x ∈ levelSet f n) :
    (2 : ℝ) ^ n ≤ ‖f x‖ ∧ ‖f x‖ < (2 : ℝ) ^ (n + 1) := by
  obtain ⟨h0, hn⟩ := hx
  have a1 := Int.lt_zpow_succ_log_self (R := ℝ) (b := 2) (by norm_num) ‖f x‖
  have a2 := Int.zpow_log_le_self (R := ℝ) (b := 2) (by norm_num) (norm_pos_iff.2 h0)
  push_cast at a1 a2
  rw [hn] at a1 a2
  exact ⟨a2, a1⟩

lemma norm_piece_le (f : α →ₛ F) (n : ℤ) (x : α) :
    ‖piece f n x‖ ≤ (levelSet f n).indicator (fun _ => (1 : ℝ)) x := by
  rw [piece_apply]
  by_cases hx : x ∈ levelSet f n
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, norm_smul, norm_inv,
      Real.norm_of_nonneg (by positivity)]
    have h := (norm_lt_of_mem_levelSet hx).2
    have hpos : (0 : ℝ) < 2 ^ (n + 1) := by positivity
    rw [inv_mul_le_iff₀ hpos, mul_one]
    exact h.le
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, smul_zero, norm_zero]

omit [NormedSpace ℝ F] in
lemma simpleFunc_finset_sum_apply {ι : Type*} (s : Finset ι) (u : ι → α →ₛ F) (x : α) :
    (∑ i ∈ s, u i) x = ∑ i ∈ s, u i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, SimpleFunc.coe_add, Pi.add_apply, ih]

/-- Level decomposition `f = Σ_n 2^(n+1) • piece f n`. -/
lemma eq_sum_smul_piece (f : α →ₛ F) :
    f = ∑ n ∈ levels f, ((2 : ℝ) ^ (n + 1)) • piece f n := by
  ext x
  rw [simpleFunc_finset_sum_apply]
  have hterm : ∀ n, (((2 : ℝ) ^ (n + 1)) • piece f n) x = (levelSet f n).indicator f x := by
    intro n
    rw [SimpleFunc.smul_apply, piece_apply, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  simp only [hterm]
  by_cases hx : f x = 0
  · rw [hx]
    refine (sum_eq_zero fun n _ => ?_).symm
    rw [Set.indicator_of_notMem (fun h => h.1 hx)]
  · rw [sum_eq_single (Int.log 2 ‖f x‖)]
    · rw [Set.indicator_of_mem (show x ∈ levelSet f (Int.log 2 ‖f x‖) from ⟨hx, rfl⟩)]
    · intro n _ hn
      exact Set.indicator_of_notMem (fun h => hn h.2.symm) _
    · intro h
      exact absurd (mem_levels hx) h

omit [NormedSpace ℝ F] in
/-- Chebyshev on the dyadic levels: `Σ_n 2^(p n) μ(F_n) ≤ ∫ ‖f‖^p`. -/
lemma sum_levels_le_lintegral (f : α →ₛ F) {p : ℝ} (hp : 0 < p) (μ : Measure α) :
    ∑ n ∈ levels f, ENNReal.ofReal ((2 : ℝ) ^ (p * n)) * μ (levelSet f n) ≤
      ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  have hpt : ∀ x, ∑ n ∈ levels f,
      (levelSet f n).indicator (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (p * n))) x ≤ ‖f x‖ₑ ^ p := by
    intro x
    by_cases hx : f x = 0
    · rw [sum_eq_zero fun n _ => Set.indicator_of_notMem (fun h => h.1 hx) _]
      exact zero_le
    · rw [sum_eq_single (Int.log 2 ‖f x‖)]
      · have hmem : x ∈ levelSet f (Int.log 2 ‖f x‖) := ⟨hx, rfl⟩
        rw [Set.indicator_of_mem hmem, ← ofReal_norm,
          ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
        apply ENNReal.ofReal_le_ofReal
        have h1 := (norm_lt_of_mem_levelSet hmem).1
        rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_intCast]
        gcongr
      · intro n _ hn
        exact Set.indicator_of_notMem (fun h => hn h.2.symm) _
      · intro h
        exact absurd (mem_levels hx) h
  calc ∑ n ∈ levels f, ENNReal.ofReal ((2 : ℝ) ^ (p * n)) * μ (levelSet f n)
      = ∑ n ∈ levels f, ∫⁻ x, (levelSet f n).indicator
          (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (p * n))) x ∂μ := by
        refine sum_congr rfl fun n _ => ?_
        rw [lintegral_indicator_const (measurableSet_levelSet f n)]
    _ = ∫⁻ x, ∑ n ∈ levels f, (levelSet f n).indicator
          (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (p * n))) x ∂μ := by
        rw [lintegral_finsetSum]
        intro n _
        exact measurable_const.indicator (measurableSet_levelSet f n)
    _ ≤ ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := lintegral_mono hpt

omit [NormedSpace ℝ F] in
lemma lintegral_enorm_rpow_eq {f : α → F} {μ : Measure α} {p : ℝ} (hp : 0 < p)
    (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖f x‖ₑ ^ p ∂μ = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

omit [NormedSpace ℝ E] in
lemma lintegral_enorm_rpow_eq' {f : β → E} {ν : Measure β} {p : ℝ} (hp : 0 < p)
    (hf : AEStronglyMeasurable f ν) :
    ∫⁻ x, ‖f x‖ₑ ^ p ∂ν = eLpNorm f (ENNReal.ofReal p) ν ^ p := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

omit [NormedSpace ℝ F] in
lemma measure_levelSet_lt_top (f : α →ₛ F) {p : ℝ} (hp : 0 < p) {μ : Measure α}
    (hf : eLpNorm f (ENNReal.ofReal p) μ < ∞) {n : ℤ} (hn : n ∈ levels f) :
    μ (levelSet f n) < ∞ := by
  have h1 : ENNReal.ofReal ((2 : ℝ) ^ (p * n)) * μ (levelSet f n) ≤ ∫⁻ x, ‖f x‖ₑ ^ p ∂μ :=
    (single_le_sum (f := fun n : ℤ => ENNReal.ofReal ((2 : ℝ) ^ (p * n)) * μ (levelSet f n))
      (fun _ _ => zero_le) hn).trans (sum_levels_le_lintegral f hp μ)
  rw [lintegral_enorm_rpow_eq hp f.aestronglyMeasurable] at h1
  have h2 : eLpNorm f (ENNReal.ofReal p) μ ^ p < ∞ := ENNReal.rpow_lt_top_of_nonneg hp.le hf.ne
  have h3 := h1.trans_lt h2
  rcases ENNReal.mul_lt_top_iff.1 h3 with h | h | h
  · exact h.2
  · exact absurd h (by simp only [ENNReal.ofReal_eq_zero, not_le]; positivity)
  · rw [h]; exact ENNReal.zero_lt_top

omit [NormedSpace ℝ F] in
/-- The `p`-sum of the level data is bounded by `‖f‖_p^p`. -/
lemma ofReal_sum_levels_le (f : α →ₛ F) {p : ℝ} (hp : 0 < p) {μ : Measure α}
    (hf : eLpNorm f (ENNReal.ofReal p) μ < ∞) :
    ENNReal.ofReal (∑ n ∈ levels f, (2 : ℝ) ^ (p * n) * (μ (levelSet f n)).toReal) ≤
      eLpNorm f (ENNReal.ofReal p) μ ^ p := by
  rw [← lintegral_enorm_rpow_eq hp f.aestronglyMeasurable,
    ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)]
  refine le_trans (le_of_eq (sum_congr rfl fun n hn => ?_)) (sum_levels_le_lintegral f hp μ)
  rw [ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_toReal (measure_levelSet_lt_top f hp hf hn).ne]

/-! ### The `r`-triangle inequality, `r ≤ 1` -/

lemma ennreal_sum_rpow_le_sum_rpow {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) : (∑ i ∈ s, a i) ^ r ≤ ∑ i ∈ s, a i ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos hr0]
  | insert b s hb ih =>
    rw [sum_insert hb, sum_insert hb]
    exact (ENNReal.rpow_add_le_add_rpow _ _ hr0.le hr1).trans (by gcongr)

omit [NormedSpace ℝ E] in
lemma enorm_sum_rpow_le {ι : Type*} (s : Finset ι) (v : ι → E) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r ≤ 1) : ‖∑ i ∈ s, v i‖ₑ ^ r ≤ ∑ i ∈ s, ‖v i‖ₑ ^ r :=
  (ENNReal.rpow_le_rpow (enorm_sum_le s v) hr0.le).trans
    (ennreal_sum_rpow_le_sum_rpow s _ hr0 hr1)

/-! ### Bilinear expansion -/

section Bilinear

variable {T : (α → F) → (α → F) → β → E}

omit [MeasurableSpace β] in
lemma map_sum_left_of_bilinear
    (hadd₁ : ∀ f f' g : α →ₛ F, T ⇑(f + f') ⇑g = T ⇑f ⇑g + T ⇑f' ⇑g)
    (hsmul₁ : ∀ (c : ℝ) (f g : α →ₛ F), T ⇑(c • f) ⇑g = c • T ⇑f ⇑g)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → α →ₛ F) (g : α →ₛ F) :
    T ⇑(∑ i ∈ s, c i • u i) ⇑g = ∑ i ∈ s, c i • T ⇑(u i) ⇑g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := hsmul₁ 0 0 g
    rw [zero_smul, zero_smul] at h
    simpa using h
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, hadd₁, hsmul₁, ih]

omit [MeasurableSpace β] in
lemma map_sum_right_of_bilinear
    (hadd₂ : ∀ f g g' : α →ₛ F, T ⇑f ⇑(g + g') = T ⇑f ⇑g + T ⇑f ⇑g')
    (hsmul₂ : ∀ (c : ℝ) (f g : α →ₛ F), T ⇑f ⇑(c • g) = c • T ⇑f ⇑g)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → α →ₛ F) (f : α →ₛ F) :
    T ⇑f ⇑(∑ i ∈ s, c i • u i) = ∑ i ∈ s, c i • T ⇑f ⇑(u i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := hsmul₂ 0 f 0
    rw [zero_smul, zero_smul] at h
    simpa using h
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, hadd₂, hsmul₂, ih]

end Bilinear

/-! ### The pair exponent choice -/

lemma pair_term_eq {p₁ p₂ r t : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (n m : ℤ) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) :
    ((2 : ℝ) ^ (n : ℝ) * u ^ (1 / p₁ + t) * ((2 : ℝ) ^ (m : ℝ) * v ^ (1 / p₂ - t))) ^ r =
      ((2 : ℝ) ^ (p₁ * n) * u) ^ (r / p₁) * ((2 : ℝ) ^ (p₂ * m) * v) ^ (r / p₂) *
        (u / v) ^ (t * r) := by
  have h2n : ((2 : ℝ) ^ (n : ℝ)) ^ r = ((2 : ℝ) ^ (p₁ * n)) ^ (r / p₁) := by
    rw [← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
    congr 1
    field_simp
  have h2m : ((2 : ℝ) ^ (m : ℝ)) ^ r = ((2 : ℝ) ^ (p₂ * m)) ^ (r / p₂) := by
    rw [← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
    congr 1
    field_simp
  have hu' : (u ^ (1 / p₁ + t)) ^ r = u ^ (r / p₁) * u ^ (t * r) := by
    rw [← Real.rpow_mul hu.le, ← Real.rpow_add hu]
    congr 1
    field_simp
  have hv' : (v ^ (1 / p₂ - t)) ^ r = v ^ (r / p₂) * (v ^ (t * r))⁻¹ := by
    rw [← Real.rpow_mul hv.le, ← Real.rpow_neg hv.le, ← Real.rpow_add hv]
    congr 1
    field_simp
    ring
  have e1 : ((2 : ℝ) ^ (p₁ * n) * u) ^ (r / p₁) = ((2 : ℝ) ^ (p₁ * n)) ^ (r / p₁) * u ^ (r / p₁) :=
    Real.mul_rpow (by positivity) hu.le
  have e2 : ((2 : ℝ) ^ (p₂ * m) * v) ^ (r / p₂) = ((2 : ℝ) ^ (p₂ * m)) ^ (r / p₂) * v ^ (r / p₂) :=
    Real.mul_rpow (by positivity) hv.le
  have e4 : ((2 : ℝ) ^ (n : ℝ) * u ^ (1 / p₁ + t) * ((2 : ℝ) ^ (m : ℝ) * v ^ (1 / p₂ - t))) ^ r =
      ((2 : ℝ) ^ (n : ℝ)) ^ r * (u ^ (1 / p₁ + t)) ^ r *
        (((2 : ℝ) ^ (m : ℝ)) ^ r * (v ^ (1 / p₂ - t)) ^ r) := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]
  rw [e4, e1, e2, Real.div_rpow hu.le hv.le, h2n, hu', h2m, hv']
  ring

/-- For each pair of levels one of the two exponents `1/p₁ ± δ₀` turns the pair term into the
D1 summand. -/
lemma exists_pair_exponent {p₁ p₂ r δ₀ : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hr : 0 < r)
    (hδ₀ : 0 < δ₀) (hδ₂ : δ₀ < 1 / p₂) (n m : ℤ) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ∃ t, (t = δ₀ ∨ (t = -δ₀ ∧ 0 < u ∧ 0 < v)) ∧
      ((2 : ℝ) ^ (n : ℝ) * u ^ (1 / p₁ + t) * ((2 : ℝ) ^ (m : ℝ) * v ^ (1 / p₂ - t))) ^ r ≤
        ((2 : ℝ) ^ (p₁ * n) * u) ^ (r / p₁) * ((2 : ℝ) ^ (p₂ * m) * v) ^ (r / p₂) *
          pairWeight u v ^ (δ₀ * r) := by
  by_cases huv : 0 < u ∧ 0 < v
  · obtain ⟨hu, hv⟩ := huv
    have hpw : pairWeight u v = min (u / v) (v / u) := by
      unfold pairWeight; simp only [hu, hv, and_self, ↓reduceIte]
    rcases le_total u v with h | h
    · refine ⟨δ₀, Or.inl rfl, le_of_eq ?_⟩
      rw [pair_term_eq hp₁ hp₂ n m hu hv, hpw, min_eq_left]
      rw [div_le_div_iff₀ hv hu]
      nlinarith
    · refine ⟨-δ₀, Or.inr ⟨rfl, hu, hv⟩, le_of_eq ?_⟩
      rw [pair_term_eq hp₁ hp₂ n m hu hv, hpw, min_eq_right, neg_mul, Real.rpow_neg
        (div_nonneg hu.le hv.le), ← Real.inv_rpow (div_nonneg hu.le hv.le), inv_div]
      rw [div_le_div_iff₀ hu hv]
      nlinarith
  · refine ⟨δ₀, Or.inl rfl, ?_⟩
    have hR : 0 ≤ ((2 : ℝ) ^ (p₁ * n) * u) ^ (r / p₁) * ((2 : ℝ) ^ (p₂ * m) * v) ^ (r / p₂) *
        pairWeight u v ^ (δ₀ * r) := by
      have := pairWeight_nonneg u v
      positivity
    refine le_trans (le_of_eq ?_) hR
    have h0 : u ^ (1 / p₁ + δ₀) * v ^ (1 / p₂ - δ₀) = 0 := by
      rcases not_and_or.1 huv with h | h
      · rw [le_antisymm (not_lt.1 h) hu, Real.zero_rpow (by positivity), zero_mul]
      · rw [le_antisymm (not_lt.1 h) hv, Real.zero_rpow (by linarith), mul_zero]
    have : (2 : ℝ) ^ (n : ℝ) * u ^ (1 / p₁ + δ₀) * ((2 : ℝ) ^ (m : ℝ) * v ^ (1 / p₂ - δ₀)) =
        (2 : ℝ) ^ (n : ℝ) * (2 : ℝ) ^ (m : ℝ) * (u ^ (1 / p₁ + δ₀) * v ^ (1 / p₂ - δ₀)) := by
      ring
    rw [this, h0, mul_zero, Real.zero_rpow hr.ne']

/-! ### R6c-I -/

/-- The constant of R6c-I: `(K^r 4^r C_{D1}(p₁, p₂, r/p₁, δ₀ r))^(1/r)`. -/
noncomputable def strongConstI (p₁ p₂ r δ₀ K : ℝ) : ℝ :=
  (K ^ r * 4 ^ r * d1Const p₁ p₂ (r / p₁) (δ₀ * r)) ^ (1 / r)

private lemma ofReal_rpow_of_nonneg_or_pos {w e : ℝ} (hw : 0 ≤ w) (h : 0 ≤ e ∨ 0 < w) :
    ENNReal.ofReal w ^ e = ENNReal.ofReal (w ^ e) := by
  rcases h with he | hw'
  · exact ENNReal.ofReal_rpow_of_nonneg hw he
  · exact ENNReal.ofReal_rpow_of_pos hw'

/-- One pair of levels: measurability of the output and the bound of its `r`-th power integral
by the D1 summand. -/
private lemma pair_level_bound {T : (α → F) → (α → F) → β → E} {μ : Measure α}
    {ν : Measure β} {p₁ p₂ r δ₀ K : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hr : 0 < r)
    (hδ₀ : 0 < δ₀) (hδ₂ : δ₀ < 1 / p₂) (hK : 0 ≤ K)
    (hRS : ∀ t : ℝ, |t| < 2 * δ₀ → ∀ E₁ E₂ : Set α, MeasurableSet E₁ → MeasurableSet E₂ →
      μ E₁ < ∞ → μ E₂ < ∞ → ∀ g₁ g₂ : α →ₛ F,
      (∀ x, ‖g₁ x‖ ≤ E₁.indicator (fun _ => (1 : ℝ)) x) →
      (∀ x, ‖g₂ x‖ ≤ E₂.indicator (fun _ => (1 : ℝ)) x) →
      eLpNorm (T g₁ g₂) (ENNReal.ofReal r) ν ≤
        ENNReal.ofReal K * μ E₁ ^ (1 / p₁ + t) * μ E₂ ^ (1 / p₂ - t))
    (f₁ f₂ : α →ₛ F) (n m : ℤ) (hfin₁ : μ (levelSet f₁ n) < ∞)
    (hfin₂ : μ (levelSet f₂ m) < ∞) :
    AEStronglyMeasurable (T (piece f₁ n) (piece f₂ m)) ν ∧
    ∫⁻ x, ‖(((2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (m + 1)) • T (piece f₁ n) (piece f₂ m)) x‖ₑ ^ r ∂ν ≤
      ENNReal.ofReal (K ^ r * 4 ^ r *
        (((2 : ℝ) ^ (p₁ * n) * (μ (levelSet f₁ n)).toReal) ^ (r / p₁) *
          ((2 : ℝ) ^ (p₂ * m) * (μ (levelSet f₂ m)).toReal) ^ (r / p₂) *
          pairWeight (μ (levelSet f₁ n)).toReal (μ (levelSet f₂ m)).toReal ^ (δ₀ * r))) := by
  set u := (μ (levelSet f₁ n)).toReal
  set v := (μ (levelSet f₂ m)).toReal
  have hu : 0 ≤ u := ENNReal.toReal_nonneg
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  obtain ⟨t, ht, hineq⟩ := exists_pair_exponent hp₁ hp₂ hr hδ₀ hδ₂ n m hu hv
  have htabs : |t| < 2 * δ₀ := by
    rcases ht with rfl | ⟨rfl, -⟩
    · rw [abs_of_pos hδ₀]; linarith
    · rw [abs_neg, abs_of_pos hδ₀]; linarith
  have hRSnm := hRS t htabs _ _ (measurableSet_levelSet f₁ n) (measurableSet_levelSet f₂ m)
    hfin₁ hfin₂ (piece f₁ n) (piece f₂ m) (norm_piece_le f₁ n) (norm_piece_le f₂ m)
  have hexp : (0 ≤ 1 / p₁ + t ∨ 0 < u) ∧ (0 ≤ 1 / p₂ - t ∨ 0 < v) := by
    rcases ht with rfl | ⟨rfl, hu', hv'⟩
    · exact ⟨Or.inl (by positivity), Or.inl (by linarith)⟩
    · exact ⟨Or.inr hu', Or.inr hv'⟩
  rw [← ENNReal.ofReal_toReal hfin₁.ne, ← ENNReal.ofReal_toReal hfin₂.ne,
    ofReal_rpow_of_nonneg_or_pos hu hexp.1, ofReal_rpow_of_nonneg_or_pos hv hexp.2,
    ← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_mul (by positivity)] at hRSnm
  set B := K * u ^ (1 / p₁ + t) * v ^ (1 / p₂ - t)
  have hB : 0 ≤ B := by positivity
  have hmeas : AEStronglyMeasurable (T (piece f₁ n) (piece f₂ m)) ν :=
    aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hRSnm)
  refine ⟨hmeas, ?_⟩
  set k : ℝ := (2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (m + 1)
  have hk : 0 ≤ k := by positivity
  have hpt : ∀ x, ‖(k • T (piece f₁ n) (piece f₂ m)) x‖ₑ ^ r =
      ENNReal.ofReal (k ^ r) * ‖T (piece f₁ n) (piece f₂ m) x‖ₑ ^ r := by
    intro x
    rw [Pi.smul_apply, enorm_smul, Real.enorm_eq_ofReal hk, ENNReal.mul_rpow_of_nonneg _ _ hr.le,
      ENNReal.ofReal_rpow_of_nonneg hk hr.le]
  have hreal : k ^ r * B ^ r ≤ K ^ r * 4 ^ r *
      (((2 : ℝ) ^ (p₁ * n) * u) ^ (r / p₁) * ((2 : ℝ) ^ (p₂ * m) * v) ^ (r / p₂) *
        pairWeight u v ^ (δ₀ * r)) := by
    have e : k * B = K * 4 * ((2 : ℝ) ^ (n : ℝ) * u ^ (1 / p₁ + t) *
        ((2 : ℝ) ^ (m : ℝ) * v ^ (1 / p₂ - t))) := by
      simp only [k, B, zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0), zpow_one, Real.rpow_intCast]
      ring
    rw [← Real.mul_rpow hk hB, e, Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow hK (by norm_num)]
    gcongr
  calc ∫⁻ x, ‖(k • T (piece f₁ n) (piece f₂ m)) x‖ₑ ^ r ∂ν
      = ENNReal.ofReal (k ^ r) * ∫⁻ x, ‖T (piece f₁ n) (piece f₂ m) x‖ₑ ^ r ∂ν := by
        simp_rw [hpt]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (k ^ r) * eLpNorm (T (piece f₁ n) (piece f₂ m)) (ENNReal.ofReal r) ν ^ r := by
        rw [lintegral_enorm_rpow_eq' hr hmeas]
    _ ≤ ENNReal.ofReal (k ^ r) * ENNReal.ofReal B ^ r := by
        gcongr
    _ = ENNReal.ofReal (k ^ r * B ^ r) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hB hr.le, ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- **R6c-I** (restricted strong type on the segment `a₁ + a₂ = 1/r` ⇒ strong type on simple
functions, `r ≤ 1`). `T` is real-bilinear on simple functions; `(RS)` is assumed for the
exponents `(1/p₁ + t, 1/p₂ - t)`, `|t| < 2δ₀`, with one constant `K` (only `t = ±δ₀` is used). -/
theorem eLpNorm_le_of_restrictedStrong {T : (α → F) → (α → F) → β → E} {μ : Measure α}
    {ν : Measure β} {p₁ p₂ r δ₀ K : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hr : 0 < r) (hr1 : r ≤ 1)
    (hpr : 1 / r = 1 / p₁ + 1 / p₂) (hδ₀ : 0 < δ₀) (hδ₂ : δ₀ < 1 / p₂) (hK : 0 ≤ K)
    (hadd₁ : ∀ f f' g : α →ₛ F, T ⇑(f + f') ⇑g = T ⇑f ⇑g + T ⇑f' ⇑g)
    (hsmul₁ : ∀ (c : ℝ) (f g : α →ₛ F), T ⇑(c • f) ⇑g = c • T ⇑f ⇑g)
    (hadd₂ : ∀ f g g' : α →ₛ F, T ⇑f ⇑(g + g') = T ⇑f ⇑g + T ⇑f ⇑g')
    (hsmul₂ : ∀ (c : ℝ) (f g : α →ₛ F), T ⇑f ⇑(c • g) = c • T ⇑f ⇑g)
    (hRS : ∀ t : ℝ, |t| < 2 * δ₀ → ∀ E₁ E₂ : Set α, MeasurableSet E₁ → MeasurableSet E₂ →
      μ E₁ < ∞ → μ E₂ < ∞ → ∀ g₁ g₂ : α →ₛ F,
      (∀ x, ‖g₁ x‖ ≤ E₁.indicator (fun _ => (1 : ℝ)) x) →
      (∀ x, ‖g₂ x‖ ≤ E₂.indicator (fun _ => (1 : ℝ)) x) →
      eLpNorm (T g₁ g₂) (ENNReal.ofReal r) ν ≤
        ENNReal.ofReal K * μ E₁ ^ (1 / p₁ + t) * μ E₂ ^ (1 / p₂ - t))
    (f₁ f₂ : α →ₛ F) (hf₁ : eLpNorm f₁ (ENNReal.ofReal p₁) μ < ∞)
    (hf₂ : eLpNorm f₂ (ENNReal.ofReal p₂) μ < ∞) :
    eLpNorm (T f₁ f₂) (ENNReal.ofReal r) ν ≤
      ENNReal.ofReal (strongConstI p₁ p₂ r δ₀ K) * eLpNorm f₁ (ENNReal.ofReal p₁) μ *
        eLpNorm f₂ (ENNReal.ofReal p₂) μ := by
  -- exponents
  have hsum : r / p₁ + r / p₂ = 1 := by
    calc r / p₁ + r / p₂ = r * (1 / p₁ + 1 / p₂) := by ring
      _ = r * (1 / r) := by rw [hpr]
      _ = 1 := by field_simp
  have hθ0 : 0 < r / p₁ := div_pos hr hp₁
  have hθ1 : r / p₁ < 1 := by have : 0 < r / p₂ := div_pos hr hp₂; linarith
  have h1θ : r / p₂ = 1 - r / p₁ := by linarith
  -- the level decomposition
  have hdec : T f₁ f₂ = ∑ n ∈ levels f₁, ∑ m ∈ levels f₂,
      ((2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (m + 1)) • T (piece f₁ n) (piece f₂ m) := by
    have e1 := map_sum_left_of_bilinear hadd₁ hsmul₁ (levels f₁) (fun n => (2 : ℝ) ^ (n + 1))
      (piece f₁) f₂
    beta_reduce at e1
    rw [← eq_sum_smul_piece f₁] at e1
    rw [e1]
    refine sum_congr rfl fun n _ => ?_
    have e2 := map_sum_right_of_bilinear hadd₂ hsmul₂ (levels f₂) (fun m => (2 : ℝ) ^ (m + 1))
      (piece f₂) (piece f₁ n)
    beta_reduce at e2
    rw [← eq_sum_smul_piece f₂] at e2
    rw [e2, smul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [smul_smul]
  have hpair := fun n (hn : n ∈ levels f₁) m (hm : m ∈ levels f₂) =>
    pair_level_bound hp₁ hp₂ hr hδ₀ hδ₂ hK hRS f₁ f₂ n m (measure_levelSet_lt_top f₁ hp₁ hf₁ hn)
      (measure_levelSet_lt_top f₂ hp₂ hf₂ hm)
  set u : ℤ → ℝ := fun n => (μ (levelSet f₁ n)).toReal
  set v : ℤ → ℝ := fun m => (μ (levelSet f₂ m)).toReal
  set D : ℤ → ℤ → ℝ := fun n m => ((2 : ℝ) ^ (p₁ * n) * u n) ^ (r / p₁) *
    ((2 : ℝ) ^ (p₂ * m) * v m) ^ (1 - r / p₁) * pairWeight (u n) (v m) ^ (δ₀ * r)
  have hD : ∀ n m, 0 ≤ D n m := fun n m => by
    have := pairWeight_nonneg (u n) (v m)
    have : 0 ≤ u n := ENNReal.toReal_nonneg
    have : 0 ≤ v m := ENNReal.toReal_nonneg
    positivity
  set A₁ := eLpNorm f₁ (ENNReal.ofReal p₁) μ
  set A₂ := eLpNorm f₂ (ENNReal.ofReal p₂) μ
  set C₀ : ℝ := K ^ r * 4 ^ r * d1Const p₁ p₂ (r / p₁) (δ₀ * r)
  have hC₀ : 0 ≤ C₀ := by
    have := d1Const_nonneg hp₁ hp₂ hθ0 hθ1 (mul_pos hδ₀ hr)
    positivity
  -- measurability of the output
  have hmeasT : AEStronglyMeasurable (T f₁ f₂) ν := by
    rw [hdec]
    refine Finset.aestronglyMeasurable_sum _ fun n hn => ?_
    refine Finset.aestronglyMeasurable_sum _ fun m hm => ?_
    exact (hpair n hn m hm).1.const_smul _
  -- the integral bound
  have hmain : ∫⁻ x, ‖T f₁ f₂ x‖ₑ ^ r ∂ν ≤
      ENNReal.ofReal (K ^ r * 4 ^ r * ∑ n ∈ levels f₁, ∑ m ∈ levels f₂, D n m) := by
    rw [mul_sum, ENNReal.ofReal_sum_of_nonneg (fun n _ =>
      mul_nonneg (by positivity) (sum_nonneg fun m _ => hD n m))]
    calc ∫⁻ x, ‖T f₁ f₂ x‖ₑ ^ r ∂ν
        ≤ ∫⁻ x, ∑ n ∈ levels f₁, ∑ m ∈ levels f₂,
            ‖(((2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (m + 1)) • T (piece f₁ n) (piece f₂ m)) x‖ₑ ^ r ∂ν := by
          refine lintegral_mono fun x => ?_
          rw [hdec, Finset.sum_apply]
          refine (enorm_sum_rpow_le _ _ hr hr1).trans (sum_le_sum fun n _ => ?_)
          rw [Finset.sum_apply]
          exact enorm_sum_rpow_le _ _ hr hr1
      _ = ∑ n ∈ levels f₁, ∑ m ∈ levels f₂,
            ∫⁻ x, ‖(((2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (m + 1)) •
              T (piece f₁ n) (piece f₂ m)) x‖ₑ ^ r ∂ν := by
          rw [lintegral_finsetSum']
          · refine sum_congr rfl fun n hn => ?_
            rw [lintegral_finsetSum']
            intro m hm
            exact (((hpair n hn m hm).1.const_smul _).enorm.pow_const r)
          · intro n hn
            exact Finset.aemeasurable_fun_sum _ fun m hm =>
              (((hpair n hn m hm).1.const_smul _).enorm.pow_const r)
      _ ≤ ∑ n ∈ levels f₁, ENNReal.ofReal (K ^ r * 4 ^ r * ∑ m ∈ levels f₂, D n m) := by
          refine sum_le_sum fun n hn => ?_
          rw [mul_sum, ENNReal.ofReal_sum_of_nonneg (fun m _ => by have := hD n m; positivity)]
          refine sum_le_sum fun m hm => ?_
          refine (hpair n hn m hm).2.trans (le_of_eq ?_)
          simp only [D, u, v, h1θ]
  -- D1
  have hd1 := d1 hp₁ hp₂ hθ0 hθ1 (mul_pos hδ₀ hr) u v (fun n => ENNReal.toReal_nonneg)
    (fun m => ENNReal.toReal_nonneg) (levels f₁) (levels f₂)
  set X := ∑ n ∈ levels f₁, (2 : ℝ) ^ (p₁ * n) * u n
  set Y := ∑ m ∈ levels f₂, (2 : ℝ) ^ (p₂ * m) * v m
  have hX : 0 ≤ X := sum_nonneg fun n _ => by have : 0 ≤ u n := ENNReal.toReal_nonneg; positivity
  have hY : 0 ≤ Y := sum_nonneg fun m _ => by have : 0 ≤ v m := ENNReal.toReal_nonneg; positivity
  have hXA : ENNReal.ofReal (X ^ (r / p₁)) ≤ A₁ ^ r := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hX hθ0.le]
    calc ENNReal.ofReal X ^ (r / p₁) ≤ (A₁ ^ p₁) ^ (r / p₁) := by
          gcongr
          exact ofReal_sum_levels_le f₁ hp₁ hf₁
      _ = A₁ ^ r := by
          rw [← ENNReal.rpow_mul]
          congr 1
          field_simp
  have hYA : ENNReal.ofReal (Y ^ (1 - r / p₁)) ≤ A₂ ^ r := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hY (by linarith)]
    calc ENNReal.ofReal Y ^ (1 - r / p₁) ≤ (A₂ ^ p₂) ^ (1 - r / p₁) := by
          gcongr
          exact ofReal_sum_levels_le f₂ hp₂ hf₂
      _ = A₂ ^ r := by
          rw [← ENNReal.rpow_mul, ← h1θ]
          congr 1
          field_simp
  have hpow : eLpNorm (T f₁ f₂) (ENNReal.ofReal r) ν ^ r ≤
      ENNReal.ofReal C₀ * A₁ ^ r * A₂ ^ r := by
    rw [← lintegral_enorm_rpow_eq' hr hmeasT]
    refine hmain.trans ?_
    calc ENNReal.ofReal (K ^ r * 4 ^ r * ∑ n ∈ levels f₁, ∑ m ∈ levels f₂, D n m)
        ≤ ENNReal.ofReal (C₀ * (X ^ (r / p₁) * Y ^ (1 - r / p₁))) := by
          apply ENNReal.ofReal_le_ofReal
          simp only [C₀, mul_assoc]
          gcongr
      _ = ENNReal.ofReal C₀ * ENNReal.ofReal (X ^ (r / p₁)) *
            ENNReal.ofReal (Y ^ (1 - r / p₁)) := by
          rw [← mul_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hC₀]
      _ ≤ ENNReal.ofReal C₀ * A₁ ^ r * A₂ ^ r := by gcongr
  calc eLpNorm (T f₁ f₂) (ENNReal.ofReal r) ν
      = (eLpNorm (T f₁ f₂) (ENNReal.ofReal r) ν ^ r) ^ (1 / r) := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one]
    _ ≤ (ENNReal.ofReal C₀ * A₁ ^ r * A₂ ^ r) ^ (1 / r) := by gcongr
    _ = ENNReal.ofReal (strongConstI p₁ p₂ r δ₀ K) * A₁ * A₂ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          mul_one_div_cancel hr.ne', ENNReal.rpow_one, ENNReal.rpow_one,
          ENNReal.ofReal_rpow_of_nonneg hC₀ (by positivity)]
        rfl

/-! ### R6c-II -/

/-- A subadditive, nonnegatively homogeneous functional on simple functions is bounded on a
finite nonnegative combination by the combination of its values. -/
lemma sublinear_sum_le (φ : (α →ₛ F) → ℝ) (hsub : ∀ f f', φ (f + f') ≤ φ f + φ f')
    (hhom : ∀ c : ℝ, 0 ≤ c → ∀ f, φ (c • f) = c * φ f) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (u : ι → α →ₛ F) :
    φ (∑ i ∈ s, c i • u i) ≤ ∑ i ∈ s, c i * φ (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := hhom 0 le_rfl 0
    rw [smul_zero, zero_mul] at h
    simp [h]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (hsub _ _).trans (by rw [hhom _ (hc a)]; gcongr)

lemma exists_rpow_div_eq_pairWeight {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (γ : ℝ) :
    ∃ e, (e = γ ∨ e = -γ) ∧ (u / v) ^ e = pairWeight u v ^ γ := by
  have hpw : pairWeight u v = min (u / v) (v / u) := by
    unfold pairWeight; simp only [hu, hv, and_self, ↓reduceIte]
  rcases le_total u v with h | h
  · refine ⟨γ, Or.inl rfl, ?_⟩
    rw [hpw, min_eq_left]
    rw [div_le_div_iff₀ hv hu]
    nlinarith
  · refine ⟨-γ, Or.inr rfl, ?_⟩
    rw [hpw, min_eq_right, Real.rpow_neg (div_nonneg hu.le hv.le),
      ← Real.inv_rpow (div_nonneg hu.le hv.le), inv_div]
    rw [div_le_div_iff₀ hu hv]
    nlinarith

lemma two_zpow_mul_rpow_eq {p : ℝ} (hp : 0 < p) (n : ℤ) {u : ℝ} (hu : 0 < u) (s : ℝ) :
    (2 : ℝ) ^ (n : ℝ) * u ^ (1 / p + s) = ((2 : ℝ) ^ (p * n) * u) ^ (1 / p) * u ^ s := by
  rw [Real.mul_rpow (by positivity) hu.le, ← Real.rpow_mul (by norm_num), Real.rpow_add hu]
  have : p * n * (1 / p) = n := by field_simp
  rw [this]
  ring

/-- For each triple of levels, an exponent perturbation `d` (`Σ dᵢ = 0`, `|dᵢ| ≤ δ₀`) turns the
triple term into the D2 summand (weights `pairWeight^(δ₀/2)` for the pairs `(1,2)`, `(1,3)`). -/
lemma exists_triple_exponent {p₁ p₂ p₃ δ₀ : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hp₃ : 0 < p₃)
    (hδ₀ : 0 < δ₀) (hδ₂ : δ₀ / 2 < 1 / p₂) (hδ₃ : δ₀ / 2 < 1 / p₃) (n m k : ℤ) {u v w : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    ∃ d₁ d₂ d₃ : ℝ, d₁ + d₂ + d₃ = 0 ∧ |d₁| ≤ δ₀ ∧ |d₂| ≤ δ₀ ∧ |d₃| ≤ δ₀ ∧
      (2 : ℝ) ^ (n : ℝ) * u ^ (1 / p₁ + d₁) * ((2 : ℝ) ^ (m : ℝ) * v ^ (1 / p₂ + d₂)) *
          ((2 : ℝ) ^ (k : ℝ) * w ^ (1 / p₃ + d₃)) ≤
        ((2 : ℝ) ^ (p₁ * n) * u) ^ (1 / p₁) * ((2 : ℝ) ^ (p₂ * m) * v) ^ (1 / p₂) *
          ((2 : ℝ) ^ (p₃ * k) * w) ^ (1 / p₃) *
          (pairWeight u v ^ (δ₀ / 2) * pairWeight u w ^ (δ₀ / 2)) := by
  have hR : 0 ≤ ((2 : ℝ) ^ (p₁ * n) * u) ^ (1 / p₁) * ((2 : ℝ) ^ (p₂ * m) * v) ^ (1 / p₂) *
      ((2 : ℝ) ^ (p₃ * k) * w) ^ (1 / p₃) *
      (pairWeight u v ^ (δ₀ / 2) * pairWeight u w ^ (δ₀ / 2)) := by
    have := pairWeight_nonneg u v
    have := pairWeight_nonneg u w
    positivity
  by_cases hpos : 0 < u ∧ 0 < v ∧ 0 < w
  · obtain ⟨hu', hv', hw'⟩ := hpos
    obtain ⟨e, he, hev⟩ := exists_rpow_div_eq_pairWeight hu' hv' (δ₀ / 2)
    obtain ⟨e', he', hew⟩ := exists_rpow_div_eq_pairWeight hu' hw' (δ₀ / 2)
    have hea : |e| = δ₀ / 2 := by
      rcases he with rfl | rfl
      · exact abs_of_pos (by positivity)
      · rw [abs_neg]; exact abs_of_pos (by positivity)
    have hea' : |e'| = δ₀ / 2 := by
      rcases he' with rfl | rfl
      · exact abs_of_pos (by positivity)
      · rw [abs_neg]; exact abs_of_pos (by positivity)
    refine ⟨e + e', -e, -e', by ring, ?_, ?_, ?_, le_of_eq ?_⟩
    · calc |e + e'| ≤ |e| + |e'| := abs_add_le _ _
        _ = δ₀ := by rw [hea, hea']; ring
    · rw [abs_neg, hea]; linarith
    · rw [abs_neg, hea']; linarith
    rw [two_zpow_mul_rpow_eq hp₁ n hu', two_zpow_mul_rpow_eq hp₂ m hv',
      two_zpow_mul_rpow_eq hp₃ k hw', ← hev, ← hew, Real.div_rpow hu'.le hv'.le,
      Real.div_rpow hu'.le hw'.le, Real.rpow_add hu', Real.rpow_neg hv'.le, Real.rpow_neg hw'.le]
    field_simp
  · refine ⟨δ₀, -(δ₀ / 2), -(δ₀ / 2), by ring, by rw [abs_of_pos hδ₀], ?_, ?_, ?_⟩
    · rw [abs_neg, abs_of_pos (by positivity)]; linarith
    · rw [abs_neg, abs_of_pos (by positivity)]; linarith
    refine le_trans (le_of_eq ?_) hR
    have h0 : u ^ (1 / p₁ + δ₀) * v ^ (1 / p₂ + -(δ₀ / 2)) * w ^ (1 / p₃ + -(δ₀ / 2)) = 0 := by
      rcases not_and_or.1 hpos with h | h
      · rw [le_antisymm (not_lt.1 h) hu, Real.zero_rpow (by positivity)]; ring
      rcases not_and_or.1 h with h | h
      · rw [le_antisymm (not_lt.1 h) hv, Real.zero_rpow (by linarith)]; ring
      · rw [le_antisymm (not_lt.1 h) hw, Real.zero_rpow (by linarith)]; ring
    calc (2 : ℝ) ^ (n : ℝ) * u ^ (1 / p₁ + δ₀) * ((2 : ℝ) ^ (m : ℝ) * v ^ (1 / p₂ + -(δ₀ / 2))) *
          ((2 : ℝ) ^ (k : ℝ) * w ^ (1 / p₃ + -(δ₀ / 2)))
        = (2 : ℝ) ^ (n : ℝ) * (2 : ℝ) ^ (m : ℝ) * (2 : ℝ) ^ (k : ℝ) *
          (u ^ (1 / p₁ + δ₀) * v ^ (1 / p₂ + -(δ₀ / 2)) * w ^ (1 / p₃ + -(δ₀ / 2))) := by ring
      _ = 0 := by rw [h0, mul_zero]

/-- The constant of R6c-II. -/
noncomputable def strongConstII (p₁ p₂ p₃ δ₀ K : ℝ) : ℝ :=
  8 * K * d2Const p₁ p₂ p₃ (δ₀ / 2)

omit [NormedSpace ℝ F] in
lemma sum_levels_le_toReal (f : α →ₛ F) {p : ℝ} (hp : 0 < p) {μ : Measure α}
    (hf : eLpNorm f (ENNReal.ofReal p) μ < ∞) :
    (∑ n ∈ levels f, (2 : ℝ) ^ (p * n) * (μ (levelSet f n)).toReal) ^ (1 / p) ≤
      (eLpNorm f (ENNReal.ofReal p) μ).toReal := by
  have h := ofReal_sum_levels_le f hp hf
  have hS : 0 ≤ ∑ n ∈ levels f, (2 : ℝ) ^ (p * n) * (μ (levelSet f n)).toReal :=
    sum_nonneg fun n _ => by positivity
  have h' : ∑ n ∈ levels f, (2 : ℝ) ^ (p * n) * (μ (levelSet f n)).toReal ≤
      (eLpNorm f (ENNReal.ofReal p) μ).toReal ^ p := by
    rw [ENNReal.toReal_rpow, ← ENNReal.ofReal_le_iff_le_toReal]
    · exact h
    · exact (ENNReal.rpow_lt_top_of_nonneg hp.le hf.ne).ne
  calc (∑ n ∈ levels f, (2 : ℝ) ^ (p * n) * (μ (levelSet f n)).toReal) ^ (1 / p)
      ≤ ((eLpNorm f (ENNReal.ofReal p) μ).toReal ^ p) ^ (1 / p) := by gcongr
    _ = _ := by
        rw [← Real.rpow_mul ENNReal.toReal_nonneg, mul_one_div_cancel hp.ne', Real.rpow_one]

/-- **R6c-II** (restricted type ⇒ strong type for a sublinear trilinear form, Banach range).
`Λ` is subadditive and nonnegatively homogeneous in each slot on simple functions,
and satisfies the restricted bound `Λ(g₁,g₂,g₃) ≤ K Π μ(Eᵢ)^(1/pᵢ + dᵢ)` for `|gᵢ| ≤ 1_{Eᵢ}`,
at all exponent perturbations `Σ dᵢ = 0`, `|dᵢ| ≤ δ₀`. Then
`Λ(f₁,f₂,f₃) ≤ C ‖f₁‖_{p₁} ‖f₂‖_{p₂} ‖f₃‖_{p₃}` for simple `fᵢ ∈ L^{pᵢ}`. -/
theorem form_le_of_restrictedType {Λ : (α → F) → (α → F) → (α → F) → ℝ} {μ : Measure α}
    {p₁ p₂ p₃ δ₀ K : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hp₃ : 0 < p₃)
    (hp : 1 / p₁ + 1 / p₂ + 1 / p₃ = 1) (hδ₀ : 0 < δ₀) (hδ₂ : δ₀ / 2 < 1 / p₂)
    (hδ₃ : δ₀ / 2 < 1 / p₃) (hK : 0 ≤ K)
    (hsub₁ : ∀ f f' g h : α →ₛ F, Λ ⇑(f + f') g h ≤ Λ f g h + Λ f' g h)
    (hsub₂ : ∀ f g g' h : α →ₛ F, Λ f ⇑(g + g') h ≤ Λ f g h + Λ f g' h)
    (hsub₃ : ∀ f g h h' : α →ₛ F, Λ f g ⇑(h + h') ≤ Λ f g h + Λ f g h')
    (hhom₁ : ∀ c : ℝ, 0 ≤ c → ∀ f g h : α →ₛ F, Λ ⇑(c • f) g h = c * Λ f g h)
    (hhom₂ : ∀ c : ℝ, 0 ≤ c → ∀ f g h : α →ₛ F, Λ f ⇑(c • g) h = c * Λ f g h)
    (hhom₃ : ∀ c : ℝ, 0 ≤ c → ∀ f g h : α →ₛ F, Λ f g ⇑(c • h) = c * Λ f g h)
    (hRT : ∀ d₁ d₂ d₃ : ℝ, d₁ + d₂ + d₃ = 0 → |d₁| ≤ δ₀ → |d₂| ≤ δ₀ → |d₃| ≤ δ₀ →
      ∀ E₁ E₂ E₃ : Set α, MeasurableSet E₁ → MeasurableSet E₂ → MeasurableSet E₃ →
      μ E₁ < ∞ → μ E₂ < ∞ → μ E₃ < ∞ → ∀ g₁ g₂ g₃ : α →ₛ F,
      (∀ x, ‖g₁ x‖ ≤ E₁.indicator (fun _ => (1 : ℝ)) x) →
      (∀ x, ‖g₂ x‖ ≤ E₂.indicator (fun _ => (1 : ℝ)) x) →
      (∀ x, ‖g₃ x‖ ≤ E₃.indicator (fun _ => (1 : ℝ)) x) →
      Λ g₁ g₂ g₃ ≤ K * (μ E₁).toReal ^ (1 / p₁ + d₁) * (μ E₂).toReal ^ (1 / p₂ + d₂) *
        (μ E₃).toReal ^ (1 / p₃ + d₃))
    (f₁ f₂ f₃ : α →ₛ F) (hf₁ : eLpNorm f₁ (ENNReal.ofReal p₁) μ < ∞)
    (hf₂ : eLpNorm f₂ (ENNReal.ofReal p₂) μ < ∞) (hf₃ : eLpNorm f₃ (ENNReal.ofReal p₃) μ < ∞) :
    Λ f₁ f₂ f₃ ≤ strongConstII p₁ p₂ p₃ δ₀ K * (eLpNorm f₁ (ENNReal.ofReal p₁) μ).toReal *
      (eLpNorm f₂ (ENNReal.ofReal p₂) μ).toReal * (eLpNorm f₃ (ENNReal.ofReal p₃) μ).toReal := by
  set c : ℤ → ℝ := fun n => (2 : ℝ) ^ (n + 1)
  have hc : ∀ n, 0 ≤ c n := fun n => by positivity
  -- expansion in the three slots
  have hexp : Λ f₁ f₂ f₃ ≤ ∑ n ∈ levels f₁, c n * ∑ m ∈ levels f₂, c m *
      ∑ k ∈ levels f₃, c k * Λ (piece f₁ n) (piece f₂ m) (piece f₃ k) := by
    have e₁ := sublinear_sum_le (fun f => Λ f f₂ f₃) (fun f f' => hsub₁ f f' f₂ f₃)
      (fun c hc f => hhom₁ c hc f f₂ f₃) (levels f₁) c hc (piece f₁)
    simp only [c, ← eq_sum_smul_piece f₁] at e₁
    refine e₁.trans (sum_le_sum fun n _ => mul_le_mul_of_nonneg_left ?_ (hc n))
    have e₂ := sublinear_sum_le (fun g => Λ (piece f₁ n) g f₃)
      (fun g g' => hsub₂ (piece f₁ n) g g' f₃) (fun c hc g => hhom₂ c hc (piece f₁ n) g f₃)
      (levels f₂) c hc (piece f₂)
    simp only [c, ← eq_sum_smul_piece f₂] at e₂
    refine e₂.trans (sum_le_sum fun m _ => mul_le_mul_of_nonneg_left ?_ (hc m))
    have e₃ := sublinear_sum_le (fun h => Λ (piece f₁ n) (piece f₂ m) h)
      (fun h h' => hsub₃ (piece f₁ n) (piece f₂ m) h h')
      (fun c hc h => hhom₃ c hc (piece f₁ n) (piece f₂ m) h) (levels f₃) c hc (piece f₃)
    simp only [c, ← eq_sum_smul_piece f₃] at e₃
    exact e₃
  set u : ℤ → ℝ := fun n => (μ (levelSet f₁ n)).toReal
  set v : ℤ → ℝ := fun m => (μ (levelSet f₂ m)).toReal
  set w : ℤ → ℝ := fun k => (μ (levelSet f₃ k)).toReal
  have hu : ∀ n, 0 ≤ u n := fun n => ENNReal.toReal_nonneg
  have hv : ∀ m, 0 ≤ v m := fun m => ENNReal.toReal_nonneg
  have hw : ∀ k, 0 ≤ w k := fun k => ENNReal.toReal_nonneg
  set D : ℤ → ℤ → ℤ → ℝ := fun n m k => ((2 : ℝ) ^ (p₁ * n) * u n) ^ (1 / p₁) *
    ((2 : ℝ) ^ (p₂ * m) * v m) ^ (1 / p₂) * ((2 : ℝ) ^ (p₃ * k) * w k) ^ (1 / p₃) *
    (pairWeight (u n) (v m) ^ (δ₀ / 2) * pairWeight (u n) (w k) ^ (δ₀ / 2))
  -- one triple
  have hterm : ∀ n ∈ levels f₁, ∀ m ∈ levels f₂, ∀ k ∈ levels f₃,
      c n * (c m * (c k * Λ (piece f₁ n) (piece f₂ m) (piece f₃ k))) ≤ 8 * K * D n m k := by
    intro n hn m hm k hk
    obtain ⟨d₁, d₂, d₃, hd, hd₁, hd₂, hd₃, hineq⟩ :=
      exists_triple_exponent hp₁ hp₂ hp₃ hδ₀ hδ₂ hδ₃ n m k (hu n) (hv m) (hw k)
    have hRTnmk := hRT d₁ d₂ d₃ hd hd₁ hd₂ hd₃ _ _ _ (measurableSet_levelSet f₁ n)
      (measurableSet_levelSet f₂ m) (measurableSet_levelSet f₃ k)
      (measure_levelSet_lt_top f₁ hp₁ hf₁ hn) (measure_levelSet_lt_top f₂ hp₂ hf₂ hm)
      (measure_levelSet_lt_top f₃ hp₃ hf₃ hk) (piece f₁ n) (piece f₂ m) (piece f₃ k)
      (norm_piece_le f₁ n) (norm_piece_le f₂ m) (norm_piece_le f₃ k)
    have hcn : ∀ j : ℤ, c j = 2 * (2 : ℝ) ^ (j : ℝ) := fun j => by
      simp only [c, zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0), zpow_one, Real.rpow_intCast]
      ring
    have hccc : 0 ≤ c n * c m * c k := by have := hc n; have := hc m; have := hc k; positivity
    calc c n * (c m * (c k * Λ (piece f₁ n) (piece f₂ m) (piece f₃ k)))
        = c n * c m * c k * Λ (piece f₁ n) (piece f₂ m) (piece f₃ k) := by ring
      _ ≤ c n * c m * c k * (K * u n ^ (1 / p₁ + d₁) * v m ^ (1 / p₂ + d₂) *
            w k ^ (1 / p₃ + d₃)) := mul_le_mul_of_nonneg_left hRTnmk hccc
      _ = 8 * K * ((2 : ℝ) ^ (n : ℝ) * u n ^ (1 / p₁ + d₁) *
            ((2 : ℝ) ^ (m : ℝ) * v m ^ (1 / p₂ + d₂)) *
            ((2 : ℝ) ^ (k : ℝ) * w k ^ (1 / p₃ + d₃))) := by
          rw [hcn n, hcn m, hcn k]; ring
      _ ≤ 8 * K * D n m k := by gcongr
  have hsum : Λ f₁ f₂ f₃ ≤ 8 * K * ∑ n ∈ levels f₁, ∑ m ∈ levels f₂, ∑ k ∈ levels f₃,
      D n m k := by
    refine hexp.trans ?_
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    rw [mul_sum, mul_sum]
    refine sum_le_sum fun m hm => ?_
    rw [mul_sum, mul_sum, mul_sum]
    refine sum_le_sum fun k hk => ?_
    exact hterm n hn m hm k hk
  have hd2 := d2 hp₁ hp₂ hp₃ hp (by positivity : 0 < δ₀ / 2) u v w hu hv hw (levels f₁)
    (levels f₂) (levels f₃)
  have h1 := sum_levels_le_toReal f₁ hp₁ hf₁
  have h2 := sum_levels_le_toReal f₂ hp₂ hf₂
  have h3 := sum_levels_le_toReal f₃ hp₃ hf₃
  have hC : 0 ≤ d2Const p₁ p₂ p₃ (δ₀ / 2) := d2Const_nonneg hp₁ hp₂ hp₃ (by positivity)
  calc Λ f₁ f₂ f₃ ≤ 8 * K * ∑ n ∈ levels f₁, ∑ m ∈ levels f₂, ∑ k ∈ levels f₃, D n m k := hsum
    _ ≤ 8 * K * (d2Const p₁ p₂ p₃ (δ₀ / 2) *
          ((∑ n ∈ levels f₁, (2 : ℝ) ^ (p₁ * n) * u n) ^ (1 / p₁) *
          (∑ m ∈ levels f₂, (2 : ℝ) ^ (p₂ * m) * v m) ^ (1 / p₂) *
          (∑ k ∈ levels f₃, (2 : ℝ) ^ (p₃ * k) * w k) ^ (1 / p₃))) := by
        gcongr
    _ ≤ 8 * K * (d2Const p₁ p₂ p₃ (δ₀ / 2) *
          ((eLpNorm f₁ (ENNReal.ofReal p₁) μ).toReal * (eLpNorm f₂ (ENNReal.ofReal p₂) μ).toReal *
            (eLpNorm f₃ (ENNReal.ofReal p₃) μ).toReal)) := by
        have : 0 ≤ (∑ n ∈ levels f₁, (2 : ℝ) ^ (p₁ * n) * u n) ^ (1 / p₁) :=
          Real.rpow_nonneg (sum_nonneg fun n _ => by have := hu n; positivity) _
        have : 0 ≤ (∑ m ∈ levels f₂, (2 : ℝ) ^ (p₂ * m) * v m) ^ (1 / p₂) :=
          Real.rpow_nonneg (sum_nonneg fun m _ => by have := hv m; positivity) _
        have : 0 ≤ (∑ k ∈ levels f₃, (2 : ℝ) ^ (p₃ * k) * w k) ^ (1 / p₃) :=
          Real.rpow_nonneg (sum_nonneg fun k _ => by have := hw k; positivity) _
        gcongr
    _ = _ := by simp only [strongConstII]; ring

/-! ### Corollary (MB): from simple to general inputs (Fatou) -/

open Filter Topology in
/-- **R6c-I for general inputs**, given simple approximants `s_{i,j}` with
`‖s_{i,j}‖ ≤ M ‖f_i‖` pointwise and `T(s_{1,j}, s_{2,j}) → T(f₁, f₂)` a.e. (Fatou). -/
theorem eLpNorm_le_of_restrictedStrong_of_ae_tendsto {T : (α → F) → (α → F) → β → E}
    {μ : Measure α} {ν : Measure β} {p₁ p₂ r δ₀ K M : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hr : 0 < r) (hr1 : r ≤ 1) (hpr : 1 / r = 1 / p₁ + 1 / p₂) (hδ₀ : 0 < δ₀)
    (hδ₂ : δ₀ < 1 / p₂) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hadd₁ : ∀ f f' g : α →ₛ F, T ⇑(f + f') ⇑g = T ⇑f ⇑g + T ⇑f' ⇑g)
    (hsmul₁ : ∀ (c : ℝ) (f g : α →ₛ F), T ⇑(c • f) ⇑g = c • T ⇑f ⇑g)
    (hadd₂ : ∀ f g g' : α →ₛ F, T ⇑f ⇑(g + g') = T ⇑f ⇑g + T ⇑f ⇑g')
    (hsmul₂ : ∀ (c : ℝ) (f g : α →ₛ F), T ⇑f ⇑(c • g) = c • T ⇑f ⇑g)
    (hRS : ∀ t : ℝ, |t| < 2 * δ₀ → ∀ E₁ E₂ : Set α, MeasurableSet E₁ → MeasurableSet E₂ →
      μ E₁ < ∞ → μ E₂ < ∞ → ∀ g₁ g₂ : α →ₛ F,
      (∀ x, ‖g₁ x‖ ≤ E₁.indicator (fun _ => (1 : ℝ)) x) →
      (∀ x, ‖g₂ x‖ ≤ E₂.indicator (fun _ => (1 : ℝ)) x) →
      eLpNorm (T g₁ g₂) (ENNReal.ofReal r) ν ≤
        ENNReal.ofReal K * μ E₁ ^ (1 / p₁ + t) * μ E₂ ^ (1 / p₂ - t))
    (f₁ f₂ : α → F) (hf₁ : eLpNorm f₁ (ENNReal.ofReal p₁) μ < ∞)
    (hf₂ : eLpNorm f₂ (ENNReal.ofReal p₂) μ < ∞) (s₁ s₂ : ℕ → α →ₛ F)
    (hs₁ : ∀ j x, ‖s₁ j x‖ ≤ M * ‖f₁ x‖) (hs₂ : ∀ j x, ‖s₂ j x‖ ≤ M * ‖f₂ x‖)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun j => T (s₁ j) (s₂ j) x) atTop (𝓝 (T f₁ f₂ x))) :
    eLpNorm (T f₁ f₂) (ENNReal.ofReal r) ν ≤
      ENNReal.ofReal (strongConstI p₁ p₂ r δ₀ K * M * M) * eLpNorm f₁ (ENNReal.ofReal p₁) μ *
        eLpNorm f₂ (ENNReal.ofReal p₂) μ := by
  set A₁ := eLpNorm f₁ (ENNReal.ofReal p₁) μ
  set A₂ := eLpNorm f₂ (ENNReal.ofReal p₂) μ
  set C := ENNReal.ofReal (strongConstI p₁ p₂ r δ₀ K)
  set B := C * (ENNReal.ofReal M * A₁) * (ENNReal.ofReal M * A₂)
  have hB : B < ∞ := by
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_) ?_
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf₁
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf₂
  have hsj₁ : ∀ j, eLpNorm (s₁ j) (ENNReal.ofReal p₁) μ ≤ ENNReal.ofReal M * A₁ := fun j =>
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (s₁ j).aestronglyMeasurable (ae_of_all _ (hs₁ j)) _
  have hsj₂ : ∀ j, eLpNorm (s₂ j) (ENNReal.ofReal p₂) μ ≤ ENNReal.ofReal M * A₂ := fun j =>
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (s₂ j).aestronglyMeasurable (ae_of_all _ (hs₂ j)) _
  have hb : ∀ j, eLpNorm (T (s₁ j) (s₂ j)) (ENNReal.ofReal r) ν ≤ B := by
    intro j
    refine (eLpNorm_le_of_restrictedStrong hp₁ hp₂ hr hr1 hpr hδ₀ hδ₂ hK hadd₁ hsmul₁ hadd₂ hsmul₂
      hRS (s₁ j) (s₂ j) ((hsj₁ j).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf₁))
      ((hsj₂ j).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf₂))).trans ?_
    exact mul_le_mul' (mul_le_mul' le_rfl (hsj₁ j)) (hsj₂ j)
  have hmeas : ∀ j, AEStronglyMeasurable (T (s₁ j) (s₂ j)) ν := fun j =>
    aestronglyMeasurable_of_eLpNorm_ne_top ((hb j).trans_lt hB).ne
  have hTmeas : AEStronglyMeasurable (T f₁ f₂) ν :=
    aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim
  calc eLpNorm (T f₁ f₂) (ENNReal.ofReal r) ν
      ≤ atTop.liminf fun j => eLpNorm (T (s₁ j) (s₂ j)) (ENNReal.ofReal r) ν :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm hmeas _ hTmeas hlim
    _ ≤ B := liminf_le_of_frequently_le' (Frequently.of_forall hb)
    _ = _ := by
        have hC : 0 ≤ strongConstI p₁ p₂ r δ₀ K := by
          unfold strongConstI
          exact Real.rpow_nonneg (by
            have := d1Const_nonneg hp₁ hp₂ (div_pos hr hp₁) (by
              have : 0 < r / p₂ := div_pos hr hp₂
              have hsum : r / p₁ + r / p₂ = 1 := by
                calc r / p₁ + r / p₂ = r * (1 / p₁ + 1 / p₂) := by ring
                  _ = r * (1 / r) := by rw [hpr]
                  _ = 1 := by field_simp
              linarith) (mul_pos hδ₀ hr)
            positivity) _
        simp only [B, C]
        rw [ENNReal.ofReal_mul (mul_nonneg hC hM), ENNReal.ofReal_mul hC]
        ring

omit [NormedSpace ℝ F] in
open Filter Topology in
/-- Simple approximants with `‖s_j‖ ≤ 2 ‖f‖` and pointwise convergence (Mathlib's
`SimpleFunc.approxOn` with `s = univ`, `y₀ = 0`). -/
lemma exists_simpleFunc_approx [MeasurableSpace F] [BorelSpace F]
    [TopologicalSpace.SeparableSpace F] {f : α → F} (hf : Measurable f) :
    ∃ s : ℕ → α →ₛ F, (∀ j x, ‖s j x‖ ≤ 2 * ‖f x‖) ∧
      ∀ x, Tendsto (fun j => s j x) atTop (𝓝 (f x)) := by
  refine ⟨fun j => SimpleFunc.approxOn f hf Set.univ 0 (Set.mem_univ 0) j, fun j x => ?_,
    fun x => SimpleFunc.tendsto_approxOn hf (Set.mem_univ 0) (by simp)⟩
  have := SimpleFunc.norm_approxOn_zero_le hf (Set.mem_univ 0) x j
  linarith

open Filter Topology in
/-- **Corollary (MB) form of R6c-I**: strong type for all measurable `L^{p_i}` inputs, assuming the
continuity of `T` along dominated pointwise simple approximations (`hcont`; for the finite model
sums `Π_P` this is dominated convergence in each wave-packet coefficient). -/
theorem eLpNorm_le_of_restrictedStrong_of_continuous [MeasurableSpace F] [BorelSpace F]
    [TopologicalSpace.SeparableSpace F] {T : (α → F) → (α → F) → β → E}
    {μ : Measure α} {ν : Measure β} {p₁ p₂ r δ₀ K : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hr : 0 < r) (hr1 : r ≤ 1) (hpr : 1 / r = 1 / p₁ + 1 / p₂) (hδ₀ : 0 < δ₀)
    (hδ₂ : δ₀ < 1 / p₂) (hK : 0 ≤ K)
    (hadd₁ : ∀ f f' g : α →ₛ F, T ⇑(f + f') ⇑g = T ⇑f ⇑g + T ⇑f' ⇑g)
    (hsmul₁ : ∀ (c : ℝ) (f g : α →ₛ F), T ⇑(c • f) ⇑g = c • T ⇑f ⇑g)
    (hadd₂ : ∀ f g g' : α →ₛ F, T ⇑f ⇑(g + g') = T ⇑f ⇑g + T ⇑f ⇑g')
    (hsmul₂ : ∀ (c : ℝ) (f g : α →ₛ F), T ⇑f ⇑(c • g) = c • T ⇑f ⇑g)
    (hRS : ∀ t : ℝ, |t| < 2 * δ₀ → ∀ E₁ E₂ : Set α, MeasurableSet E₁ → MeasurableSet E₂ →
      μ E₁ < ∞ → μ E₂ < ∞ → ∀ g₁ g₂ : α →ₛ F,
      (∀ x, ‖g₁ x‖ ≤ E₁.indicator (fun _ => (1 : ℝ)) x) →
      (∀ x, ‖g₂ x‖ ≤ E₂.indicator (fun _ => (1 : ℝ)) x) →
      eLpNorm (T g₁ g₂) (ENNReal.ofReal r) ν ≤
        ENNReal.ofReal K * μ E₁ ^ (1 / p₁ + t) * μ E₂ ^ (1 / p₂ - t))
    (f₁ f₂ : α → F) (hm₁ : Measurable f₁) (hm₂ : Measurable f₂)
    (hf₁ : eLpNorm f₁ (ENNReal.ofReal p₁) μ < ∞) (hf₂ : eLpNorm f₂ (ENNReal.ofReal p₂) μ < ∞)
    (hcont : ∀ s₁ s₂ : ℕ → α →ₛ F, (∀ j x, ‖s₁ j x‖ ≤ 2 * ‖f₁ x‖) →
      (∀ j x, ‖s₂ j x‖ ≤ 2 * ‖f₂ x‖) → (∀ x, Tendsto (fun j => s₁ j x) atTop (𝓝 (f₁ x))) →
      (∀ x, Tendsto (fun j => s₂ j x) atTop (𝓝 (f₂ x))) →
      ∀ᵐ x ∂ν, Tendsto (fun j => T (s₁ j) (s₂ j) x) atTop (𝓝 (T f₁ f₂ x))) :
    eLpNorm (T f₁ f₂) (ENNReal.ofReal r) ν ≤
      ENNReal.ofReal (strongConstI p₁ p₂ r δ₀ K * 2 * 2) * eLpNorm f₁ (ENNReal.ofReal p₁) μ *
        eLpNorm f₂ (ENNReal.ofReal p₂) μ := by
  obtain ⟨s₁, hs₁, ht₁⟩ := exists_simpleFunc_approx hm₁
  obtain ⟨s₂, hs₂, ht₂⟩ := exists_simpleFunc_approx hm₂
  exact eLpNorm_le_of_restrictedStrong_of_ae_tendsto hp₁ hp₂ hr hr1 hpr hδ₀ hδ₂ hK zero_le_two
    hadd₁ hsmul₁ hadd₂ hsmul₂ hRS f₁ f₂ hf₁ hf₂ s₁ s₂ hs₁ hs₂ (hcont s₁ s₂ hs₁ hs₂ ht₁ ht₂)

omit [NormedSpace ℝ F] in
lemma toReal_eLpNorm_le_of_le_mul {f : α → F} (s : α →ₛ F) {μ : Measure α} {p M : ℝ}
    (hM : 0 ≤ M) (hf : eLpNorm f (ENNReal.ofReal p) μ < ∞) (hs : ∀ x, ‖s x‖ ≤ M * ‖f x‖) :
    (eLpNorm s (ENNReal.ofReal p) μ).toReal ≤ M * (eLpNorm f (ENNReal.ofReal p) μ).toReal := by
  have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul s.aestronglyMeasurable (ae_of_all _ hs)
    (ENNReal.ofReal p) (μ := μ)
  have hfin : ENNReal.ofReal M * eLpNorm f (ENNReal.ofReal p) μ ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf).ne
  calc (eLpNorm s (ENNReal.ofReal p) μ).toReal
      ≤ (ENNReal.ofReal M * eLpNorm f (ENNReal.ofReal p) μ).toReal := ENNReal.toReal_mono hfin h
    _ = M * (eLpNorm f (ENNReal.ofReal p) μ).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM]

/-! ### R6c-II, operator form (`r > 1`), via duality -/

/-- **R6c-II, operator form** (`1 < r`): if `|⟨T(f₁,f₂), h⟩| ≤ Λ(f₁,f₂,h)` on simple functions and
`Λ` satisfies the hypotheses of `form_le_of_restrictedType` with `p₃ = r' = r/(r-1)`, then
`‖T(f₁,f₂)‖_r ≤ 2 C ‖f₁‖_{p₁} ‖f₂‖_{p₂}` for simple `fᵢ ∈ L^{pᵢ}` (`C = strongConstII`). -/
theorem eLpNorm_le_of_restrictedType {T : (α → ℂ) → (α → ℂ) → α → ℂ}
    {Λ : (α → ℂ) → (α → ℂ) → (α → ℂ) → ℝ} {μ : Measure α} [SigmaFinite μ]
    {p₁ p₂ r δ₀ K : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hr : 1 < r)
    (hpr : 1 / r = 1 / p₁ + 1 / p₂) (hδ₀ : 0 < δ₀) (hδ₂ : δ₀ / 2 < 1 / p₂)
    (hδ₃ : δ₀ / 2 < 1 / (r / (r - 1))) (hK : 0 ≤ K)
    (hsub₁ : ∀ f f' g h : α →ₛ ℂ, Λ ⇑(f + f') g h ≤ Λ f g h + Λ f' g h)
    (hsub₂ : ∀ f g g' h : α →ₛ ℂ, Λ f ⇑(g + g') h ≤ Λ f g h + Λ f g' h)
    (hsub₃ : ∀ f g h h' : α →ₛ ℂ, Λ f g ⇑(h + h') ≤ Λ f g h + Λ f g h')
    (hhom₁ : ∀ c : ℝ, 0 ≤ c → ∀ f g h : α →ₛ ℂ, Λ ⇑(c • f) g h = c * Λ f g h)
    (hhom₂ : ∀ c : ℝ, 0 ≤ c → ∀ f g h : α →ₛ ℂ, Λ f ⇑(c • g) h = c * Λ f g h)
    (hhom₃ : ∀ c : ℝ, 0 ≤ c → ∀ f g h : α →ₛ ℂ, Λ f g ⇑(c • h) = c * Λ f g h)
    (hRT : ∀ d₁ d₂ d₃ : ℝ, d₁ + d₂ + d₃ = 0 → |d₁| ≤ δ₀ → |d₂| ≤ δ₀ → |d₃| ≤ δ₀ →
      ∀ E₁ E₂ E₃ : Set α, MeasurableSet E₁ → MeasurableSet E₂ → MeasurableSet E₃ →
      μ E₁ < ∞ → μ E₂ < ∞ → μ E₃ < ∞ → ∀ g₁ g₂ g₃ : α →ₛ ℂ,
      (∀ x, ‖g₁ x‖ ≤ E₁.indicator (fun _ => (1 : ℝ)) x) →
      (∀ x, ‖g₂ x‖ ≤ E₂.indicator (fun _ => (1 : ℝ)) x) →
      (∀ x, ‖g₃ x‖ ≤ E₃.indicator (fun _ => (1 : ℝ)) x) →
      Λ g₁ g₂ g₃ ≤ K * (μ E₁).toReal ^ (1 / p₁ + d₁) * (μ E₂).toReal ^ (1 / p₂ + d₂) *
        (μ E₃).toReal ^ (1 / (r / (r - 1)) + d₃))
    (hTmeas : ∀ f₁ f₂ : α →ₛ ℂ, AEStronglyMeasurable (T f₁ f₂) μ)
    (hdom : ∀ f₁ f₂ h : α →ₛ ℂ, ‖∫ x, T f₁ f₂ x * h x ∂μ‖ ≤ Λ f₁ f₂ h)
    (f₁ f₂ : α →ₛ ℂ) (hf₁ : eLpNorm f₁ (ENNReal.ofReal p₁) μ < ∞)
    (hf₂ : eLpNorm f₂ (ENNReal.ofReal p₂) μ < ∞) :
    eLpNorm (T f₁ f₂) (ENNReal.ofReal r) μ ≤ ENNReal.ofReal (2 *
      (strongConstII p₁ p₂ (r / (r - 1)) δ₀ K * (eLpNorm f₁ (ENNReal.ofReal p₁) μ).toReal *
        (eLpNorm f₂ (ENNReal.ofReal p₂) μ).toReal)) := by
  have hr0 : 0 < r := by linarith
  have hp₃ : 0 < r / (r - 1) := div_pos hr0 (by linarith)
  have hp : 1 / p₁ + 1 / p₂ + 1 / (r / (r - 1)) = 1 := by
    rw [← hpr]
    field_simp
    ring
  have hC : 0 ≤ strongConstII p₁ p₂ (r / (r - 1)) δ₀ K := by
    have := d2Const_nonneg hp₁ hp₂ hp₃ (by positivity : 0 < δ₀ / 2)
    unfold strongConstII
    positivity
  refine eLpNorm_le_of_forall_simpleFunc hr (by positivity) (hTmeas f₁ f₂) fun g hg => ?_
  refine (hdom f₁ f₂ g).trans ?_
  refine (form_le_of_restrictedType hp₁ hp₂ hp₃ hp hδ₀ hδ₂ hδ₃ hK hsub₁ hsub₂ hsub₃ hhom₁ hhom₂
    hhom₃ hRT f₁ f₂ g hf₁ hf₂ hg).trans (le_of_eq ?_)
  ring

open Filter Topology in
/-- **Corollary (MB), `r > 1`**: R6c-II operator form for general inputs along simple
approximants `‖sᵢ j‖ ≤ M ‖fᵢ‖` with `T(s₁ j, s₂ j) → T(f₁, f₂)` a.e. (Fatou). -/
theorem eLpNorm_le_of_restrictedType_of_ae_tendsto {T : (α → ℂ) → (α → ℂ) → α → ℂ}
    {Λ : (α → ℂ) → (α → ℂ) → (α → ℂ) → ℝ} {μ : Measure α} [SigmaFinite μ]
    {p₁ p₂ r δ₀ K M : ℝ} (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hr : 1 < r)
    (hpr : 1 / r = 1 / p₁ + 1 / p₂) (hδ₀ : 0 < δ₀) (hδ₂ : δ₀ / 2 < 1 / p₂)
    (hδ₃ : δ₀ / 2 < 1 / (r / (r - 1))) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hsub₁ : ∀ f f' g h : α →ₛ ℂ, Λ ⇑(f + f') g h ≤ Λ f g h + Λ f' g h)
    (hsub₂ : ∀ f g g' h : α →ₛ ℂ, Λ f ⇑(g + g') h ≤ Λ f g h + Λ f g' h)
    (hsub₃ : ∀ f g h h' : α →ₛ ℂ, Λ f g ⇑(h + h') ≤ Λ f g h + Λ f g h')
    (hhom₁ : ∀ c : ℝ, 0 ≤ c → ∀ f g h : α →ₛ ℂ, Λ ⇑(c • f) g h = c * Λ f g h)
    (hhom₂ : ∀ c : ℝ, 0 ≤ c → ∀ f g h : α →ₛ ℂ, Λ f ⇑(c • g) h = c * Λ f g h)
    (hhom₃ : ∀ c : ℝ, 0 ≤ c → ∀ f g h : α →ₛ ℂ, Λ f g ⇑(c • h) = c * Λ f g h)
    (hRT : ∀ d₁ d₂ d₃ : ℝ, d₁ + d₂ + d₃ = 0 → |d₁| ≤ δ₀ → |d₂| ≤ δ₀ → |d₃| ≤ δ₀ →
      ∀ E₁ E₂ E₃ : Set α, MeasurableSet E₁ → MeasurableSet E₂ → MeasurableSet E₃ →
      μ E₁ < ∞ → μ E₂ < ∞ → μ E₃ < ∞ → ∀ g₁ g₂ g₃ : α →ₛ ℂ,
      (∀ x, ‖g₁ x‖ ≤ E₁.indicator (fun _ => (1 : ℝ)) x) →
      (∀ x, ‖g₂ x‖ ≤ E₂.indicator (fun _ => (1 : ℝ)) x) →
      (∀ x, ‖g₃ x‖ ≤ E₃.indicator (fun _ => (1 : ℝ)) x) →
      Λ g₁ g₂ g₃ ≤ K * (μ E₁).toReal ^ (1 / p₁ + d₁) * (μ E₂).toReal ^ (1 / p₂ + d₂) *
        (μ E₃).toReal ^ (1 / (r / (r - 1)) + d₃))
    (hTmeas : ∀ f₁ f₂ : α →ₛ ℂ, AEStronglyMeasurable (T f₁ f₂) μ)
    (hdom : ∀ f₁ f₂ h : α →ₛ ℂ, ‖∫ x, T f₁ f₂ x * h x ∂μ‖ ≤ Λ f₁ f₂ h)
    (f₁ f₂ : α → ℂ) (hf₁ : eLpNorm f₁ (ENNReal.ofReal p₁) μ < ∞)
    (hf₂ : eLpNorm f₂ (ENNReal.ofReal p₂) μ < ∞) (s₁ s₂ : ℕ → α →ₛ ℂ)
    (hs₁ : ∀ j x, ‖s₁ j x‖ ≤ M * ‖f₁ x‖) (hs₂ : ∀ j x, ‖s₂ j x‖ ≤ M * ‖f₂ x‖)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun j => T (s₁ j) (s₂ j) x) atTop (𝓝 (T f₁ f₂ x))) :
    eLpNorm (T f₁ f₂) (ENNReal.ofReal r) μ ≤ ENNReal.ofReal (2 *
      (strongConstII p₁ p₂ (r / (r - 1)) δ₀ K * M * M *
        (eLpNorm f₁ (ENNReal.ofReal p₁) μ).toReal * (eLpNorm f₂ (ENNReal.ofReal p₂) μ).toReal)) := by
  have hr0 : 0 < r := by linarith
  have hp₃ : 0 < r / (r - 1) := div_pos hr0 (by linarith)
  have hC : 0 ≤ strongConstII p₁ p₂ (r / (r - 1)) δ₀ K := by
    have := d2Const_nonneg hp₁ hp₂ hp₃ (by positivity : 0 < δ₀ / 2)
    unfold strongConstII
    positivity
  have hfin : ∀ (f : α → ℂ) (s : α →ₛ ℂ) (p : ℝ), eLpNorm f (ENNReal.ofReal p) μ < ∞ →
      (∀ x, ‖s x‖ ≤ M * ‖f x‖) → eLpNorm s (ENNReal.ofReal p) μ < ∞ := by
    intro f s p hf hs
    exact (eLpNorm_le_mul_eLpNorm_of_ae_le_mul s.aestronglyMeasurable (ae_of_all _ hs) _).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf)
  have hb : ∀ j, eLpNorm (T (s₁ j) (s₂ j)) (ENNReal.ofReal r) μ ≤ ENNReal.ofReal (2 *
      (strongConstII p₁ p₂ (r / (r - 1)) δ₀ K * M * M *
        (eLpNorm f₁ (ENNReal.ofReal p₁) μ).toReal * (eLpNorm f₂ (ENNReal.ofReal p₂) μ).toReal)) := by
    intro j
    refine (eLpNorm_le_of_restrictedType hp₁ hp₂ hr hpr hδ₀ hδ₂ hδ₃ hK hsub₁ hsub₂ hsub₃ hhom₁
      hhom₂ hhom₃ hRT hTmeas hdom (s₁ j) (s₂ j) (hfin _ _ _ hf₁ (hs₁ j))
      (hfin _ _ _ hf₂ (hs₂ j))).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 := toReal_eLpNorm_le_of_le_mul (s₁ j) hM hf₁ (hs₁ j)
    have h2 := toReal_eLpNorm_le_of_le_mul (s₂ j) hM hf₂ (hs₂ j)
    calc 2 * (strongConstII p₁ p₂ (r / (r - 1)) δ₀ K *
          (eLpNorm (s₁ j) (ENNReal.ofReal p₁) μ).toReal * (eLpNorm (s₂ j) (ENNReal.ofReal p₂) μ).toReal)
        ≤ 2 * (strongConstII p₁ p₂ (r / (r - 1)) δ₀ K *
          (M * (eLpNorm f₁ (ENNReal.ofReal p₁) μ).toReal) *
          (M * (eLpNorm f₂ (ENNReal.ofReal p₂) μ).toReal)) := by gcongr
      _ = _ := by ring
  have hTm : AEStronglyMeasurable (T f₁ f₂) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun j => hTmeas (s₁ j) (s₂ j)) hlim
  calc eLpNorm (T f₁ f₂) (ENNReal.ofReal r) μ
      ≤ atTop.liminf fun j => eLpNorm (T (s₁ j) (s₂ j)) (ENNReal.ofReal r) μ :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm (fun j => hTmeas (s₁ j) (s₂ j)) _ hTm hlim
    _ ≤ _ := liminf_le_of_frequently_le' (Frequently.of_forall hb)

end PrimeBHT.TimeFrequency.Interp
