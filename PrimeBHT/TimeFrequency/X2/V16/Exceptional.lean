module

public import PrimeBHT.TimeFrequency.Tile.Inside

/-!
# X2, node V16: the exceptional set `Ω(E, τ)`, the major subset `Ẽ(E, τ)` and tail-aware masses

Steps B1 and B2 of `docs/audits/X2-V16B-route-check.md` §2.3. Everything is stated for plain sets and
dyadic intervals (no tiles, no tri-tile structure), so any later node can consume it.

## Notation

* `tailWeight M t = ⟨t⟩^{-M} = (1 + t²)^{-M/2}` (`M : ℝ`), the Japanese bracket `⟨t⟩ = (1 + t²)^{1/2}`.
* `tailMass M f I = λ_M(f; I) = |I|⁻¹ ∫ ‖f(x)‖ ⟨(x - c(I))/|I|⟩^{-M} dx` (the normalization of the audit
  §2.1, `c(I) = intervalCentre I`, `|I| = (volume I).toReal`; `f : ℝ → V` into any seminormed group).
  `tailMass_le_tailMass_indicator` transfers every bound for `1_E` to a function with `‖f‖ ≤ 1_E`.
* `exceptionalOmega C₀ E τ = Ω(E, τ) = ⋃_{v ≠ τ} exceptionalSet (E v) (C₀/|E τ|)`
  `= ⋃_{v ≠ τ} {M 1_{E v} > C₀ |E v|/|E τ|}`; `M` is the uncentered maximal function `maximalHLR` of X1.
* `exceptionalMajor C₀ E τ = Ẽ(E, τ) = insideMajor Ω (E τ) = E τ ∖ ⋃_{J ∈ maxDyadicKeys Ω} 3J`. It is a
  definition from `(C₀, E, τ)` alone.
* `excMass C₀ E τ v = μ_v = C₀ |E v|/|E τ|`, `excMassTrunc C₀ E τ v = μ''_v = min (1, 2 μ_v)`.
* Constants (depending on `M` only): `tailConst M = 2^{M/2+1}/(M-1)` (`∫ ⟨t⟩^{-M} dt ≤ tailConst M`,
  `M > 1`) and `tailC M = max (80, tailConst M)`.

## Main results

* **B1** (`isOpen_exceptionalOmega`, `volume_exceptionalOmega_le`, `two_mul_volume_insideTildeF_exceptionalOmega_le`,
  `volume_le_two_mul_insideMajor_of_two_mul_le`, `exceptionalMajor_facts`): for measurable `E i` of finite
  positive measure, any `τ` and `C₀ ≥ 48`: `Ω` open; `|Ω| ≤ 8|E τ|/C₀`; `|F̃| ≤ 3|Ω| ≤ 24|E τ|/C₀ ≤ |E τ|/2`;
  `Ẽ` measurable, `Ẽ ⊆ E τ`, `|E τ| ≤ 2|Ẽ|`.
* **B2(a)** `tailMass_indicator_le_of_mem`: `x₀ ∈ I`, `M 1_E(x₀) ≤ μ` ⇒ `λ_M(1_E; I) ≤ 45 μ` (`M ≥ 2`).
* **B2(b)** `tailMass_indicator_le_of_maxDyadicKeys` (general `Ω`, `μ`) and `tailMass_indicator_le_excMass`
  (for `Ω(E, τ)`, `v ≠ τ`): `λ_M(1_{E v}; I) ≤ 80 · 2^{n+1} μ_v`; `tailMass_indicator_le_tailConst`:
  `λ_M(1_E; I) ≤ C_M`; combined (`..._tailC_mul`, `..._excMassTrunc`): `≤ tailC M · 2^{n+1} · μ''_v`.
* **B2(c)** `tailMass_exceptionalMajor_le`: `λ_M(1_Ẽ; I) ≤ tailConst M · 2^{-n(M-1)}` (`M > 1`).
* **B2(d)** `integral_indicator_mul_tailWeight_le_excMassTrunc`:
  `∫ 1_{E v} ⟨(x - c(J))/|J|⟩^{-K} ≤ 2 tailC K · |J| μ''_v` (`K ≥ 2`) and
  `integral_exceptionalMajor_mul_tailWeight_le`: `∫ 1_Ẽ ⟨…⟩^{-K} ≤ tailConst K · |J|` (`K > 1`).

Depth bookkeeping: `I = dyadicInt s w ⊆ J = dyadicInt J.1 J.2`, `J ∈ maxDyadicKeys Ω` and `J.1 = s + n`
(so `|J| = 2^n |I|`). For the key `q` of `I` and `J = dyadicAnc q n` the hypotheses are
`dyadicInt_subset_dyadicAnc q n` and `dyadicAnc_fst q n` (the `_of_dyadicAnc` forms do this).

## Remarks and corrections to the audit

* **B1 needs neither the normalization `|E τ| ∈ (1/2, 1]` nor `|E τ| = max_i |E i|`.** The X1 lemma
  `volume_le_two_mul_insideMajor` (`1/2 < |E|`, `|F̃| ≤ 1/4`) is replaced by
  `volume_le_two_mul_insideMajor_of_two_mul_le` (`2|F̃| ≤ |E|` ⇒ `|E| ≤ 2|E ∖ F̃|`). The weak `(1,1)`
  constant of `volume_exceptionalSet_le` is `4`, so `|Ω| ≤ 8|E τ|/C₀` as printed; `|F̃| ≤ 3|Ω| ≤ |E τ|/2`
  holds iff `C₀ ≥ 48` (the audit's `C₀ = 48`; `C₀ = 100` of X1 is also fine). The maximality of `|E τ|` is
  only a downstream convenience (it gives `μ_v ≤ C₀`).
* **B2(b) is correct as printed, with the factor `2^{n+1}`**: the base point `x₀ ∈ Ĵ ∖ Ω` is within
  `|Ĵ| = 2^{n+1}|I|` of `c(I)`. The constant is explicit: `80` (for any `M ≥ 2`), the second bound is
  `tailConst M`. No shell sum over `⟨·⟩^{-M}` is needed: for `M ≥ 2`, `⟨t⟩^{-M} ≤ ⟨t⟩^{-2} ≤ 2 (1+|t|)^{-2}`
  and the weight bound `lintegral_weight_le_maximalHLR` of X1 applies (the decay beyond `2` is only used
  for the `M`-dependent bounds (c) and the constant `C_M`). So B2(a), (b) hold for all `M ≥ 2` (the audit
  asks `M ≥ 3`), and (c), (d) for `M > 1`, `K > 1` (`K ≥ 2` is not needed for the `Ẽ` half).
* **B2(d)**: `μ''_v` is taken as the audit's `min (1, 2 μ_v)`; the proven constant is `2 tailC K` (the `2`
  is the `2^{n+1}` of (b) at `n = 0`).
* The integrals are Bochner integrals (the integral of a non-integrable function is `0`); all bounds
  are for `1_E` or, via `tailMass_le_tailMass_indicator`, for functions with `‖f‖ ≤ 1_E`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile
open PrimeCarleson.Proof.Common
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.V16

/-! ### The tail weight `⟨t⟩^{-M}` -/

/-- The tail weight `⟨t⟩^{-M} = (1 + t²)^{-M/2}` (Japanese bracket). -/
def tailWeight (M t : ℝ) : ℝ := (1 + t ^ 2) ^ (-(M / 2))

theorem tailWeight_pos (M t : ℝ) : 0 < tailWeight M t :=
  Real.rpow_pos_of_pos (by positivity) _

theorem tailWeight_nonneg (M t : ℝ) : 0 ≤ tailWeight M t := (tailWeight_pos M t).le

theorem continuous_tailWeight (M : ℝ) : Continuous (tailWeight M) := by
  unfold tailWeight
  exact Continuous.rpow_const (by fun_prop) fun t => Or.inl (by positivity)

theorem measurable_tailWeight (M : ℝ) : Measurable (tailWeight M) :=
  (continuous_tailWeight M).measurable

theorem one_add_abs_sq_le (t : ℝ) : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by
  nlinarith [sq_abs t, sq_nonneg (|t| - 1)]

/-- `⟨t⟩^{-M} ≤ 2^{M/2} (1 + |t|)^{-M}` for `M ≥ 0`. -/
theorem tailWeight_le_rpow {M : ℝ} (hM : 0 ≤ M) (t : ℝ) :
    tailWeight M t ≤ 2 ^ (M / 2) * (1 + |t|) ^ (-M) := by
  have h1 : (1 + |t|) ^ 2 / 2 ≤ 1 + t ^ 2 := by linarith [one_add_abs_sq_le t]
  have hpos : 0 < (1 + |t|) ^ 2 / 2 := by positivity
  have h0 : (0 : ℝ) ≤ 1 + |t| := by positivity
  calc tailWeight M t ≤ ((1 + |t|) ^ 2 / 2) ^ (-(M / 2)) :=
        Real.rpow_le_rpow_of_nonpos hpos h1 (by linarith)
    _ = 2 ^ (M / 2) * (1 + |t|) ^ (-M) := by
        rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_natCast,
          ← Real.rpow_mul h0, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        have : ((2 : ℕ) : ℝ) * (-(M / 2)) = -M := by push_cast; ring
        rw [this]
        field_simp

/-- `⟨t⟩^{-M} ≤ 2 (1 + |t|)^{-2}` for `M ≥ 2`. -/
theorem tailWeight_le_two_mul_zpow {M : ℝ} (hM : 2 ≤ M) (t : ℝ) :
    tailWeight M t ≤ 2 * (1 + |t|) ^ (-2 : ℤ) := by
  have h1 : (1 : ℝ) ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  calc tailWeight M t ≤ (1 + t ^ 2) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    _ = (1 + t ^ 2)⁻¹ := Real.rpow_neg_one _
    _ ≤ 2 * (1 + |t|) ^ (-2 : ℤ) := by
        rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv, inv_eq_one_div,
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [one_add_abs_sq_le t]


theorem tailWeight_le_rpow_sub {M : ℝ} (hM : 0 ≤ M) (c : ℝ) {L : ℝ} (hL : 0 < L) (x : ℝ) :
    tailWeight M ((x - c) / L) ≤ 2 ^ (M / 2) * (1 + |x - c| / L) ^ (-M) := by
  have := tailWeight_le_rpow hM ((x - c) / L)
  rwa [abs_div, abs_of_pos hL] at this

theorem tailWeight_le_two_mul_zpow_sub {M : ℝ} (hM : 2 ≤ M) (c : ℝ) {L : ℝ} (hL : 0 < L) (x : ℝ) :
    tailWeight M ((x - c) / L) ≤ 2 * (1 + |x - c| / L) ^ (-2 : ℤ) := by
  have := tailWeight_le_two_mul_zpow hM ((x - c) / L)
  rwa [abs_div, abs_of_pos hL] at this

/-- The constant `C_M = 2^{M/2+1}/(M-1)`: `∫ ⟨t⟩^{-M} dt ≤ C_M` for `M > 1`. -/
def tailConst (M : ℝ) : ℝ := 2 ^ (M / 2 + 1) / (M - 1)

theorem tailConst_pos {M : ℝ} (hM : 1 < M) : 0 < tailConst M :=
  div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by linarith)

theorem integrable_tailWeight {M : ℝ} (hM : 1 < M) (c : ℝ) {L : ℝ} (hL : 0 < L) :
    Integrable (fun x : ℝ => tailWeight M ((x - c) / L)) := by
  refine ((integrable_one_add_abs_sub_div_rpow hM c hL).const_mul (2 ^ (M / 2))).mono'
    ((measurable_tailWeight M).comp (by fun_prop)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (tailWeight_nonneg _ _)]
  exact tailWeight_le_rpow_sub (by linarith) c hL x

/-! ### The tail-aware mass `λ_M` -/

/-- The tail-aware mass `λ_M(f; I) = |I|⁻¹ ∫ ‖f(x)‖ ⟨(x - c(I))/|I|⟩^{-M} dx`. -/
def tailMass {V : Type*} [Norm V] (M : ℝ) (f : ℝ → V) (I : Set ℝ) : ℝ :=
  (volume I).toReal⁻¹ *
    ∫ x, ‖f x‖ * tailWeight M ((x - intervalCentre I) / (volume I).toReal)

theorem tailConst_eq {M : ℝ} (hM : 1 < M) {L : ℝ} (hL : 0 < L) :
    L⁻¹ * (2 ^ (M / 2) * (2 * L / (M - 1))) = tailConst M := by
  unfold tailConst
  rw [Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
  have : M - 1 ≠ 0 := by linarith
  field_simp

/-- A bounded function has `λ_M ≤ C_M`. -/
theorem tailMass_le_tailConst {V : Type*} [SeminormedAddGroup V] {M : ℝ} (hM : 1 < M) {f : ℝ → V} {I : Set ℝ}
    (hL : 0 < (volume I).toReal) (hf : ∀ x, ‖f x‖ ≤ 1) : tailMass M f I ≤ tailConst M := by
  set L := (volume I).toReal with hLdef
  set c := intervalCentre I with hcdef
  have hint := integrable_tailWeight hM c hL
  have hint2 := (integrable_one_add_abs_sub_div_rpow hM c hL).const_mul (2 ^ (M / 2))
  have h1 : ∫ x, ‖f x‖ * tailWeight M ((x - c) / L) ≤ ∫ x, tailWeight M ((x - c) / L) :=
    integral_mono_of_nonneg
      (ae_of_all _ fun x => mul_nonneg (norm_nonneg _) (tailWeight_nonneg _ _)) hint
      (ae_of_all _ fun x => mul_le_of_le_one_left (tailWeight_nonneg _ _) (hf x))
  have h2 : ∫ x, tailWeight M ((x - c) / L) ≤
      ∫ x, 2 ^ (M / 2) * (1 + |x - c| / L) ^ (-M) :=
    integral_mono hint hint2 fun x => tailWeight_le_rpow_sub (by linarith) c hL x
  rw [integral_const_mul, integral_one_add_abs_sub_div_rpow hM c hL] at h2
  unfold tailMass
  rw [← tailConst_eq hM hL]
  exact mul_le_mul_of_nonneg_left (h1.trans h2) (inv_nonneg.2 hL.le)

/-- Tail bound: if `‖f‖ ≤ 1_S` with `S` at distance `> r` from the centre `c(I)`, then
`λ_M(f; I) ≤ C_M (1 + r/|I|)^{1-M}`. -/
theorem tailMass_le_of_far {V : Type*} [SeminormedAddGroup V] {M : ℝ} (hM : 1 < M) {f : ℝ → V} {I S : Set ℝ}
    (hL : 0 < (volume I).toReal) {r : ℝ} (hr : 0 ≤ r)
    (hS : ∀ y ∈ S, r < |y - intervalCentre I|)
    (hf : ∀ x, ‖f x‖ ≤ S.indicator (1 : ℝ → ℝ) x) :
    tailMass M f I ≤ tailConst M * (1 + r / (volume I).toReal) ^ (1 - M) := by
  set L := (volume I).toReal with hLdef
  set c := intervalCentre I with hcdef
  have hsm : MeasurableSet {x : ℝ | r < |x - c|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hint := integrable_tailWeight hM c hL
  have hint2 : Integrable (fun x : ℝ => 2 ^ (M / 2) *
      {x : ℝ | r < |x - c|}.indicator (fun x => (1 + |x - c| / L) ^ (-M)) x) :=
    ((integrable_one_add_abs_sub_div_rpow hM c hL).indicator hsm).const_mul _
  have h1 : ∫ x, ‖f x‖ * tailWeight M ((x - c) / L) ≤ ∫ x, 2 ^ (M / 2) *
      {x : ℝ | r < |x - c|}.indicator (fun x => (1 + |x - c| / L) ^ (-M)) x := by
    refine integral_mono_of_nonneg
      (ae_of_all _ fun x => mul_nonneg (norm_nonneg _) (tailWeight_nonneg _ _)) hint2
      (ae_of_all _ fun x => ?_)
    beta_reduce
    by_cases hx : x ∈ S
    · have hx' : x ∈ {x : ℝ | r < |x - c|} := hS x hx
      rw [Set.indicator_of_mem hx']
      have hfx : ‖f x‖ ≤ 1 := by simpa [hx] using hf x
      calc ‖f x‖ * tailWeight M ((x - c) / L) ≤ tailWeight M ((x - c) / L) :=
            mul_le_of_le_one_left (tailWeight_nonneg _ _) hfx
        _ ≤ _ := tailWeight_le_rpow_sub (by linarith) c hL x
    · have hfx : ‖f x‖ ≤ 0 := by simpa [hx] using hf x
      have h0 : 0 ≤ {x : ℝ | r < |x - c|}.indicator (fun x => (1 + |x - c| / L) ^ (-M)) x :=
        Set.indicator_nonneg (fun _ _ => by positivity) x
      have : ‖f x‖ * tailWeight M ((x - c) / L) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hfx (tailWeight_nonneg _ _)
      exact this.trans (by positivity)
  rw [integral_const_mul, integral_indicator_one_add_abs_sub_div_rpow hM c hL hr] at h1
  unfold tailMass
  have h2 : L⁻¹ * (2 ^ (M / 2) * (2 * L * ((1 + r / L) ^ (1 - M) / (M - 1)))) =
      tailConst M * (1 + r / L) ^ (1 - M) := by
    unfold tailConst
    rw [Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
    have : M - 1 ≠ 0 := by linarith
    field_simp
  rw [← h2]
  exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hL.le)


/-! ### Maximal-function control of the mass of an indicator -/

theorem norm_indicator_one (E : Set ℝ) (x : ℝ) :
    ‖E.indicator (1 : ℝ → ℝ) x‖ = E.indicator (1 : ℝ → ℝ) x := by
  by_cases hx : x ∈ E <;> simp [hx]

/-- **Weighted integral against an indicator.** If `M 1_E (x₀) ≤ μ`, `|x₀ - c| ≤ R L'`, `L ≤ L'`, and
`0 ≤ w(y) ≤ A (1 + |y - c|/L)^{-2}`, then `∫ 1_E w ≤ A · 10 (1 + R)² L' μ`. -/
theorem integral_indicator_mul_le_of_maximalHLR {w : ℝ → ℝ} (hwm : Measurable w)
    (hw0 : ∀ y, 0 ≤ w y) {A L L' R c x₀ μ : ℝ} (hA : 0 ≤ A) (hL : 0 < L) (hLL : L ≤ L')
    (hR : 0 ≤ R) (hx₀ : |x₀ - c| ≤ R * L')
    (hw : ∀ y, w y ≤ A * (1 + |y - c| / L) ^ (-2 : ℤ)) {E : Set ℝ} (hE : MeasurableSet E)
    (hμ : 0 ≤ μ) (hM : maximalHLR (E.indicator (1 : ℝ → ℝ)) x₀ ≤ ENNReal.ofReal μ) :
    ∫ y, E.indicator (1 : ℝ → ℝ) y * w y ≤ A * (10 * (1 + R) ^ 2 * L' * μ) := by
  have hL' : 0 ≤ L' := (hL.trans_le hLL).le
  have hnn : 0 ≤ᵐ[volume] fun y => E.indicator (1 : ℝ → ℝ) y * w y :=
    ae_of_all _ fun y => mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) y) (hw0 y)
  have hmeas : Measurable fun y => E.indicator (1 : ℝ → ℝ) y * w y :=
    (measurable_const.indicator hE).mul hwm
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  set W : ℝ → ℝ≥0∞ := fun y => E.indicator (fun _ => (1 : ℝ≥0∞)) y with hWdef
  have hW : Measurable W := measurable_const.indicator hE
  have hlin := lintegral_weight_le_maximalHLR hL hLL hR hx₀ hW
  have hMW : maximalHLR W x₀ ≤ ENNReal.ofReal μ := by
    refine le_trans (le_of_eq (maximalHLR_congr_enorm (fun y => ?_) x₀)) hM
    by_cases hy : y ∈ E <;> simp [hWdef, hy]
  calc ∫⁻ y, ENNReal.ofReal (E.indicator (1 : ℝ → ℝ) y * w y)
      ≤ ∫⁻ y, ENNReal.ofReal A *
          (ENNReal.ofReal ((1 + |y - c| / L) ^ (-2 : ℤ)) * W y) := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ E
        · simp only [hWdef, Set.indicator_of_mem hy, Pi.one_apply, one_mul, mul_one]
          rw [← ENNReal.ofReal_mul hA]
          exact ENNReal.ofReal_le_ofReal (hw y)
        · simp [hy]
    _ = ENNReal.ofReal A *
          ∫⁻ y, ENNReal.ofReal ((1 + |y - c| / L) ^ (-2 : ℤ)) * W y :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal A * (ENNReal.ofReal (10 * (1 + R) ^ 2 * L') * ENNReal.ofReal μ) := by
        gcongr
        exact hlin.trans (mul_le_mul' le_rfl hMW)
    _ = ENNReal.ofReal (A * (10 * (1 + R) ^ 2 * L' * μ)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hA]

/-- **Core bound for (a) and (b).** Let `0 < |I|`, `|I| ≤ L'`, `|x₀ - c(I)| ≤ R L'`, `M ≥ 2` and
`M 1_E (x₀) ≤ μ`. Then `λ_M(1_E; I) ≤ 20 (1 + R)² (L'/|I|) μ`. -/
theorem tailMass_indicator_le_of_maximalHLR {M : ℝ} (hM : 2 ≤ M) {I E : Set ℝ}
    (hE : MeasurableSet E) (hL : 0 < (volume I).toReal) {L' R x₀ μ : ℝ}
    (hLL : (volume I).toReal ≤ L') (hR : 0 ≤ R) (hx₀ : |x₀ - intervalCentre I| ≤ R * L')
    (hμ : 0 ≤ μ) (hmax : maximalHLR (E.indicator (1 : ℝ → ℝ)) x₀ ≤ ENNReal.ofReal μ) :
    tailMass M (E.indicator (1 : ℝ → ℝ)) I ≤
      20 * (1 + R) ^ 2 * (L' / (volume I).toReal) * μ := by
  set L := (volume I).toReal with hLdef
  set c := intervalCentre I with hcdef
  have h := integral_indicator_mul_le_of_maximalHLR (w := fun y => tailWeight M ((y - c) / L))
    ((measurable_tailWeight M).comp (by fun_prop)) (fun y => tailWeight_nonneg _ _)
    (A := 2) (by norm_num) hL hLL hR hx₀
    (fun y => tailWeight_le_two_mul_zpow_sub hM c hL y) hE hμ hmax
  unfold tailMass
  simp_rw [norm_indicator_one]
  calc L⁻¹ * ∫ x, E.indicator (1 : ℝ → ℝ) x * tailWeight M ((x - c) / L)
      ≤ L⁻¹ * (2 * (10 * (1 + R) ^ 2 * L' * μ)) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.2 hL.le)
    _ = 20 * (1 + R) ^ 2 * (L' / L) * μ := by
        field_simp
        ring


/-- **B2(a).** If `x₀ ∈ I` and `M 1_E (x₀) ≤ μ` then `λ_M(1_E; I) ≤ 45 μ` (`M ≥ 2`; the constant does
not depend on `M`). -/
theorem tailMass_indicator_le_of_mem {M : ℝ} (hM : 2 ≤ M) {I E : Set ℝ} (hI : I.OrdConnected)
    (hE : MeasurableSet E) (hL : 0 < (volume I).toReal) {x₀ μ : ℝ} (hx₀ : x₀ ∈ I) (hμ : 0 ≤ μ)
    (hmax : maximalHLR (E.indicator (1 : ℝ → ℝ)) x₀ ≤ ENNReal.ofReal μ) :
    tailMass M (E.indicator (1 : ℝ → ℝ)) I ≤ 45 * μ := by
  have h := tailMass_indicator_le_of_maximalHLR hM hE hL (L' := (volume I).toReal) (R := 1 / 2)
    le_rfl (by norm_num) (x₀ := x₀)
    (by rw [mul_comm]; exact (abs_sub_intervalCentre_le_of_mem hI hL hx₀).trans_eq (by ring)) hμ hmax
  refine h.trans_eq ?_
  rw [div_self hL.ne']
  norm_num

/-- The parent of the dyadic interval `J = (j, w)` with `j = s + n` has length `2^{n+1} 2^s`. -/
theorem toReal_volume_parent_of_eq {j s : ℤ} {n : ℕ} (hn : j = s + n) (w : ℤ) :
    (volume (dyadicInt (dyadicParent (j, w)).1 (dyadicParent (j, w)).2)).toReal =
      (2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ s := by
  rw [toReal_volume_dyadicInt]
  simp only [dyadicParent]
  rw [hn, show s + (n : ℤ) + 1 = s + ((n + 1 : ℕ) : ℤ) by push_cast; ring,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, mul_comm]

/-- **B2(b), general form.** Let `J ∈ maxDyadicKeys Ω` (a maximal dyadic interval of `Ω`), `I = 2^s[v, v+1)
⊆ J` with `|J| = 2^n |I|`, and suppose `M 1_E ≤ μ` outside `Ω`. Then, for `M ≥ 2`,
`λ_M(1_E; I) ≤ 80 · 2^{n+1} μ`. (Proof: the parent `Ĵ` of `J` is not inside `Ω`; pick `x₀ ∈ Ĵ ∖ Ω`; then
`|x₀ - c(I)| ≤ |Ĵ| = 2^{n+1} |I|`.) -/
theorem tailMass_indicator_le_of_maxDyadicKeys {M : ℝ} (hM : 2 ≤ M) {Ω E : Set ℝ}
    (hE : MeasurableSet E) {μ : ℝ} (hμ : 0 ≤ μ)
    (hΩ : ∀ x, x ∉ Ω → maximalHLR (E.indicator (1 : ℝ → ℝ)) x ≤ ENNReal.ofReal μ)
    {J : ℤ × ℤ} (hJ : J ∈ maxDyadicKeys Ω) {s v : ℤ} {n : ℕ}
    (hIJ : dyadicInt s v ⊆ dyadicInt J.1 J.2) (hn : J.1 = s + n) :
    tailMass M (E.indicator (1 : ℝ → ℝ)) (dyadicInt s v) ≤ 80 * (2 : ℝ) ^ (n + 1) * μ := by
  obtain ⟨j, w⟩ := J
  obtain ⟨x₀, hx₀J, hx₀Ω⟩ := Set.not_subset.1 hJ.2
  have hIJh : dyadicInt s v ⊆ dyadicInt (dyadicParent (j, w)).1 (dyadicParent (j, w)).2 :=
    hIJ.trans (dyadicInt_subset_parent j w)
  have hLI : (volume (dyadicInt s v)).toReal = (2 : ℝ) ^ s := toReal_volume_dyadicInt s v
  have hLI0 : 0 < (volume (dyadicInt s v)).toReal := by rw [hLI]; positivity
  have hLJh := toReal_volume_parent_of_eq (n := n) (s := s) hn w
  have hLJh0 : 0 < (volume (dyadicInt (dyadicParent (j, w)).1 (dyadicParent (j, w)).2)).toReal := by
    rw [hLJh]; positivity
  have hdist := abs_sub_intervalCentre_le_of_subset (Set.ordConnected_Ico (a := (2 : ℝ) ^ s * v))
    hLI0 (Set.ordConnected_Ico (a := (2 : ℝ) ^ (dyadicParent (j, w)).1 * ((dyadicParent (j, w)).2 : ℝ)))
    hLJh0 hIJh hx₀J
  have h := tailMass_indicator_le_of_maximalHLR hM hE hLI0
    (L' := (volume (dyadicInt (dyadicParent (j, w)).1 (dyadicParent (j, w)).2)).toReal) (R := 1)
    (x₀ := x₀) ?_ (by norm_num) (by rw [one_mul]; exact hdist) hμ (hΩ x₀ hx₀Ω)
  · refine h.trans_eq ?_
    rw [hLJh, hLI]
    field_simp
    ring
  · rw [hLI, hLJh]
    have : (1 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
    have hp : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
    nlinarith


theorem indicator_one_le_one (E : Set ℝ) (x : ℝ) : E.indicator (1 : ℝ → ℝ) x ≤ 1 := by
  by_cases hx : x ∈ E <;> simp [hx]

/-- **B2(b), second half.** Every indicator has `λ_M(1_E; I) ≤ C_M` (`M > 1`). -/
theorem tailMass_indicator_le_tailConst {M : ℝ} (hM : 1 < M) (E : Set ℝ) {I : Set ℝ}
    (hL : 0 < (volume I).toReal) : tailMass M (E.indicator (1 : ℝ → ℝ)) I ≤ tailConst M :=
  tailMass_le_tailConst hM hL fun x => (norm_indicator_one E x).trans_le (indicator_one_le_one E x)

/-- Monotonicity in the integrand: if `‖f‖ ≤ 1_E` with `E` measurable, then `λ_M(f; I) ≤ λ_M(1_E; I)`.
(Every statement about `λ_M(1_E; I)` below therefore applies to a function with `‖f‖ ≤ 1_E`.) -/
theorem tailMass_le_tailMass_indicator {V : Type*} [SeminormedAddGroup V] {M : ℝ} (hM : 1 < M)
    {f : ℝ → V} {I E : Set ℝ} (hE : MeasurableSet E) (hL : 0 < (volume I).toReal)
    (hf : ∀ x, ‖f x‖ ≤ E.indicator (1 : ℝ → ℝ) x) :
    tailMass M f I ≤ tailMass M (E.indicator (1 : ℝ → ℝ)) I := by
  set L := (volume I).toReal with hLdef
  set c := intervalCentre I with hcdef
  have hint : Integrable (fun x => ‖E.indicator (1 : ℝ → ℝ) x‖ * tailWeight M ((x - c) / L)) := by
    refine (integrable_tailWeight hM c hL).mono'
      (((measurable_const.indicator hE).norm.mul
        ((measurable_tailWeight M).comp (by fun_prop))).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    rw [norm_mul, norm_norm, Real.norm_eq_abs (tailWeight M _),
      abs_of_nonneg (tailWeight_nonneg _ _)]
    exact mul_le_of_le_one_left (tailWeight_nonneg _ _)
      ((norm_indicator_one E x).trans_le (indicator_one_le_one E x))
  unfold tailMass
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hL.le)
  refine integral_mono_of_nonneg
    (ae_of_all _ fun x => mul_nonneg (norm_nonneg _) (tailWeight_nonneg _ _)) hint
    (ae_of_all _ fun x => ?_)
  exact mul_le_mul_of_nonneg_right ((hf x).trans (norm_indicator_one E x).ge)
    (tailWeight_nonneg _ _)

/-- The constant `C_M = max (80, 2^{M/2+1}/(M-1))` of B2(b), (c), (d). -/
def tailC (M : ℝ) : ℝ := max 80 (tailConst M)

theorem le_tailC_left (M : ℝ) : 80 ≤ tailC M := le_max_left _ _

theorem tailConst_le_tailC (M : ℝ) : tailConst M ≤ tailC M := le_max_right _ _

theorem tailC_nonneg (M : ℝ) : 0 ≤ tailC M := (by norm_num : (0 : ℝ) ≤ 80).trans (le_tailC_left M)

/-- **B2(b), combined form.** In the situation of `tailMass_indicator_le_of_maxDyadicKeys`:
`λ_M(1_E; I) ≤ C_M · 2^{n+1} · min (1, 2 μ)` (this contains both `C_M 2^{n+1} μ` and `C_M`). -/
theorem tailMass_indicator_le_tailC_mul {M : ℝ} (hM : 2 ≤ M) {Ω E : Set ℝ}
    (hE : MeasurableSet E) {μ : ℝ} (hμ : 0 ≤ μ)
    (hΩ : ∀ x, x ∉ Ω → maximalHLR (E.indicator (1 : ℝ → ℝ)) x ≤ ENNReal.ofReal μ)
    {J : ℤ × ℤ} (hJ : J ∈ maxDyadicKeys Ω) {s v : ℤ} {n : ℕ}
    (hIJ : dyadicInt s v ⊆ dyadicInt J.1 J.2) (hn : J.1 = s + n) :
    tailMass M (E.indicator (1 : ℝ → ℝ)) (dyadicInt s v) ≤
      tailC M * ((2 : ℝ) ^ (n + 1) * min 1 (2 * μ)) := by
  have h1 := tailMass_indicator_le_of_maxDyadicKeys hM hE hμ hΩ hJ hIJ hn
  have hL : 0 < (volume (dyadicInt s v)).toReal := by
    rw [toReal_volume_dyadicInt]; positivity
  have h2 := tailMass_indicator_le_tailConst (by linarith : 1 < M) E hL
  have ha : (1 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
  have hC := le_tailC_left M
  have hC2 := tailConst_le_tailC M
  rcases le_total (2 * μ) 1 with h | h
  · rw [min_eq_right h]
    have : 0 ≤ (2 : ℝ) ^ (n + 1) * μ := by positivity
    nlinarith
  · rw [min_eq_left h]
    nlinarith [tailC_nonneg M]

/-- **B2(c), general form.** If `S` avoids `3J` for a maximal dyadic interval `J = 2^{s+n}[·]` and
`I = 2^s[v, v+1) ⊆ J`, then `λ_M(1_S; I) ≤ C_M 2^{-n(M-1)}` (`M > 1`; `C_M = 2^{M/2+1}/(M-1)`, which is
`≤ 2^{M/2+1}/2` for `M ≥ 3`). -/
theorem tailMass_indicator_le_of_far_dyadic {M : ℝ} (hM : 1 < M) {S : Set ℝ} {J : ℤ × ℤ}
    {s v : ℤ} {n : ℕ} (hIJ : dyadicInt s v ⊆ dyadicInt J.1 J.2) (hn : J.1 = s + n)
    (hS : ∀ y ∈ S, y ∉ dilate 3 (dyadicInt J.1 J.2)) :
    tailMass M (S.indicator (1 : ℝ → ℝ)) (dyadicInt s v) ≤
      tailConst M * (2 : ℝ) ^ (-(M - 1) * (n : ℝ)) := by
  have hLI : (volume (dyadicInt s v)).toReal = (2 : ℝ) ^ s := toReal_volume_dyadicInt s v
  have hL : 0 < (volume (dyadicInt s v)).toReal := by rw [hLI]; positivity
  have hfar : ∀ y ∈ S, (2 : ℝ) ^ J.1 < |y - intervalCentre (dyadicInt s v)| := fun y hy =>
    lt_abs_sub_intervalCentre_of_notMem_dilate hIJ (hS y hy)
  have h := tailMass_le_of_far hM (f := S.indicator (1 : ℝ → ℝ)) hL (r := (2 : ℝ) ^ J.1)
    (by positivity) hfar fun x => (norm_indicator_one S x).le
  have hr : (2 : ℝ) ^ J.1 / (volume (dyadicInt s v)).toReal = (2 : ℝ) ^ n := by
    rw [hLI, hn, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
    field_simp
  rw [hr] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (tailConst_pos hM).le)
  have hK0 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  calc (1 + (2 : ℝ) ^ n) ^ (1 - M) ≤ ((2 : ℝ) ^ n) ^ (1 - M) :=
        Real.rpow_le_rpow_of_nonpos hK0 (by linarith) (by linarith)
    _ = (2 : ℝ) ^ (-(M - 1) * (n : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1
        ring

theorem integral_norm_mul_tailWeight_eq {V : Type*} [Norm V] (M : ℝ) (f : ℝ → V) {I : Set ℝ}
    (hL : 0 < (volume I).toReal) :
    ∫ x, ‖f x‖ * tailWeight M ((x - intervalCentre I) / (volume I).toReal) =
      (volume I).toReal * tailMass M f I := by
  unfold tailMass
  rw [← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]

/-- **B2(d), second half.** For every set `S` and every dyadic `J = 2^j[w, w+1)` and `K > 1`,
`∫ 1_S(x) ⟨(x - c(J))/|J|⟩^{-K} dx ≤ C_K |J|`. -/
theorem integral_indicator_mul_tailWeight_le {K : ℝ} (hK : 1 < K) (S : Set ℝ) (j w : ℤ) :
    ∫ x, S.indicator (1 : ℝ → ℝ) x *
        tailWeight K ((x - intervalCentre (dyadicInt j w)) / (2 : ℝ) ^ j) ≤
      tailConst K * (2 : ℝ) ^ j := by
  have hLI : (volume (dyadicInt j w)).toReal = (2 : ℝ) ^ j := toReal_volume_dyadicInt j w
  have hL : 0 < (volume (dyadicInt j w)).toReal := by rw [hLI]; positivity
  have h := integral_norm_mul_tailWeight_eq K (S.indicator (1 : ℝ → ℝ)) hL
  have h2 := tailMass_indicator_le_tailConst hK S hL
  simp_rw [norm_indicator_one, hLI] at h
  rw [h, mul_comm]
  exact mul_le_mul_of_nonneg_right h2 (by positivity)

/-- **B2(d), first half, general form.** In the situation of `tailMass_indicator_le_of_maxDyadicKeys`
(with `I = J`, `n = 0`): for `K ≥ 2`,
`∫ 1_E(x) ⟨(x - c(J))/|J|⟩^{-K} dx ≤ 2 C_K |J| min (1, 2 μ)`. -/
theorem integral_indicator_mul_tailWeight_le_of_maxDyadicKeys {K : ℝ} (hK : 2 ≤ K)
    {Ω E : Set ℝ} (hE : MeasurableSet E) {μ : ℝ} (hμ : 0 ≤ μ)
    (hΩ : ∀ x, x ∉ Ω → maximalHLR (E.indicator (1 : ℝ → ℝ)) x ≤ ENNReal.ofReal μ)
    {J : ℤ × ℤ} (hJ : J ∈ maxDyadicKeys Ω) :
    ∫ x, E.indicator (1 : ℝ → ℝ) x *
        tailWeight K ((x - intervalCentre (dyadicInt J.1 J.2)) / (2 : ℝ) ^ J.1) ≤
      2 * tailC K * (2 : ℝ) ^ J.1 * min 1 (2 * μ) := by
  have hLI : (volume (dyadicInt J.1 J.2)).toReal = (2 : ℝ) ^ J.1 := toReal_volume_dyadicInt _ _
  have hL : 0 < (volume (dyadicInt J.1 J.2)).toReal := by rw [hLI]; positivity
  have h := integral_norm_mul_tailWeight_eq K (E.indicator (1 : ℝ → ℝ)) hL
  have h2 := tailMass_indicator_le_tailC_mul hK hE hμ hΩ hJ (s := J.1) (v := J.2) (n := 0)
    subset_rfl (by simp)
  simp_rw [norm_indicator_one, hLI] at h
  rw [h]
  calc (2 : ℝ) ^ J.1 * tailMass K (E.indicator (1 : ℝ → ℝ)) (dyadicInt J.1 J.2)
      ≤ (2 : ℝ) ^ J.1 * (tailC K * ((2 : ℝ) ^ (0 + 1) * min 1 (2 * μ))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 * tailC K * (2 : ℝ) ^ J.1 * min 1 (2 * μ) := by ring


/-! ### B1: the exceptional set `Ω(E, τ)` and the major subset `Ẽ(E, τ)` -/

/-- **`Ω(E, τ)`** `:= ⋃_{v ≠ τ} {M 1_{E v} > C₀ |E v| / |E τ|}` (`exceptionalSet (E v) (C₀ / |E τ|)`). -/
def exceptionalOmega (C₀ : ℝ) (E : Fin 3 → Set ℝ) (τ : Fin 3) : Set ℝ :=
  ⋃ v : Fin 3, ⋃ _ : v ≠ τ, exceptionalSet (E v) (C₀ / (volume (E τ)).toReal)

/-- **`Ẽ(E, τ)`** `:= E τ ∖ F̃` with `F̃ = ⋃_{J ∈ maxDyadicKeys Ω} 3J`, `Ω = Ω(E, τ)`. It is a function of
`C₀, E, τ` only (`insideMajor Ω (E τ)`). -/
def exceptionalMajor (C₀ : ℝ) (E : Fin 3 → Set ℝ) (τ : Fin 3) : Set ℝ :=
  insideMajor (exceptionalOmega C₀ E τ) (E τ)

/-- The exceptional mass `μ_v = C₀ |E v| / |E τ|`: the threshold of `M 1_{E v}` outside `Ω(E, τ)`. -/
def excMass (C₀ : ℝ) (E : Fin 3 → Set ℝ) (τ v : Fin 3) : ℝ :=
  C₀ * (volume (E v)).toReal / (volume (E τ)).toReal

/-- The truncated exceptional mass `μ''_v = min (1, 2 μ_v)`. -/
def excMassTrunc (C₀ : ℝ) (E : Fin 3 → Set ℝ) (τ v : Fin 3) : ℝ :=
  min 1 (2 * excMass C₀ E τ v)

theorem excMass_nonneg {C₀ : ℝ} (hC : 0 ≤ C₀) (E : Fin 3 → Set ℝ) (τ v : Fin 3) :
    0 ≤ excMass C₀ E τ v := by
  unfold excMass; positivity

theorem mem_exceptionalOmega {C₀ : ℝ} {E : Fin 3 → Set ℝ} {τ : Fin 3} {x : ℝ} :
    x ∈ exceptionalOmega C₀ E τ ↔
      ∃ v, v ≠ τ ∧ x ∈ exceptionalSet (E v) (C₀ / (volume (E τ)).toReal) := by
  simp only [exceptionalOmega, Set.mem_iUnion, exists_prop]

theorem exceptionalOmega_eq_biUnion (C₀ : ℝ) (E : Fin 3 → Set ℝ) (τ : Fin 3) :
    exceptionalOmega C₀ E τ =
      ⋃ v ∈ (Finset.univ.erase τ : Finset (Fin 3)),
        exceptionalSet (E v) (C₀ / (volume (E τ)).toReal) := by
  ext x
  simp [mem_exceptionalOmega]

/-- **B1.** `Ω(E, τ)` is open. -/
theorem isOpen_exceptionalOmega (C₀ : ℝ) (E : Fin 3 → Set ℝ) (τ : Fin 3) :
    IsOpen (exceptionalOmega C₀ E τ) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_exceptionalSet _ _

/-- **B1.** `|Ω(E, τ)| ≤ 8 |E τ| / C₀` (weak type `(1,1)` with constant `4` for each of the two slots
`v ≠ τ`). No normalization of `|E τ|` and no maximality of `|E τ|` is used. -/
theorem volume_exceptionalOmega_le {E : Fin 3 → Set ℝ} (hEm : ∀ i, MeasurableSet (E i))
    (h0 : ∀ i, volume (E i) ≠ 0) (htop : ∀ i, volume (E i) ≠ ⊤) {C₀ : ℝ} (hC : 0 < C₀)
    (τ : Fin 3) :
    volume (exceptionalOmega C₀ E τ) ≤ ENNReal.ofReal (8 * (volume (E τ)).toReal / C₀) := by
  have hτ : 0 < (volume (E τ)).toReal := ENNReal.toReal_pos (h0 τ) (htop τ)
  have hc : 0 < C₀ / (volume (E τ)).toReal := div_pos hC hτ
  rw [exceptionalOmega_eq_biUnion]
  calc volume (⋃ v ∈ (Finset.univ.erase τ : Finset (Fin 3)),
        exceptionalSet (E v) (C₀ / (volume (E τ)).toReal))
      ≤ ∑ v ∈ (Finset.univ.erase τ : Finset (Fin 3)),
          volume (exceptionalSet (E v) (C₀ / (volume (E τ)).toReal)) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ v ∈ (Finset.univ.erase τ : Finset (Fin 3)),
          ENNReal.ofReal (4 * (volume (E τ)).toReal / C₀) := by
        refine Finset.sum_le_sum fun v _ => ?_
        refine (volume_exceptionalSet_le (hEm v) (h0 v) (htop v) hc).trans_eq ?_
        congr 1
        field_simp
    _ = ENNReal.ofReal (8 * (volume (E τ)).toReal / C₀) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ τ), Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        rw [show (((3 - 1 : ℕ) : ℝ≥0∞)) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

theorem volume_exceptionalOmega_ne_top {E : Fin 3 → Set ℝ} (hEm : ∀ i, MeasurableSet (E i))
    (h0 : ∀ i, volume (E i) ≠ 0) (htop : ∀ i, volume (E i) ≠ ⊤) {C₀ : ℝ} (hC : 0 < C₀)
    (τ : Fin 3) : volume (exceptionalOmega C₀ E τ) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (volume_exceptionalOmega_le hEm h0 htop hC τ)

/-- **B1.** `|F̃| ≤ 3 |Ω| ≤ 24 |E τ| / C₀`. -/
theorem volume_insideTildeF_exceptionalOmega_le {E : Fin 3 → Set ℝ}
    (hEm : ∀ i, MeasurableSet (E i)) (h0 : ∀ i, volume (E i) ≠ 0) (htop : ∀ i, volume (E i) ≠ ⊤)
    {C₀ : ℝ} (hC : 0 < C₀) (τ : Fin 3) :
    volume (insideTildeF (exceptionalOmega C₀ E τ)) ≤
      ENNReal.ofReal (24 * (volume (E τ)).toReal / C₀) := by
  refine (volume_insideTildeF_le _).trans ?_
  calc 3 * volume (exceptionalOmega C₀ E τ)
      ≤ 3 * ENNReal.ofReal (8 * (volume (E τ)).toReal / C₀) := by
        gcongr
        exact volume_exceptionalOmega_le hEm h0 htop hC τ
    _ = ENNReal.ofReal (24 * (volume (E τ)).toReal / C₀) := by
        rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

/-- **B1.** For `C₀ ≥ 48`: `2 |F̃| ≤ |E τ|`, i.e. `|F̃| ≤ |E τ| / 2`. -/
theorem two_mul_volume_insideTildeF_exceptionalOmega_le {E : Fin 3 → Set ℝ}
    (hEm : ∀ i, MeasurableSet (E i)) (h0 : ∀ i, volume (E i) ≠ 0) (htop : ∀ i, volume (E i) ≠ ⊤)
    {C₀ : ℝ} (hC : 48 ≤ C₀) (τ : Fin 3) :
    2 * volume (insideTildeF (exceptionalOmega C₀ E τ)) ≤ volume (E τ) := by
  have hC0 : 0 < C₀ := by linarith
  have hτ : 0 < (volume (E τ)).toReal := ENNReal.toReal_pos (h0 τ) (htop τ)
  have h := volume_insideTildeF_exceptionalOmega_le hEm h0 htop hC0 τ
  calc 2 * volume (insideTildeF (exceptionalOmega C₀ E τ))
      ≤ 2 * ENNReal.ofReal (24 * (volume (E τ)).toReal / C₀) := by gcongr
    _ ≤ 2 * ENNReal.ofReal ((volume (E τ)).toReal / 2) := by
        refine mul_le_mul_right ?_ _
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_div_iff₀ hC0 (by norm_num)]
        nlinarith
    _ = volume (E τ) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
          mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), ENNReal.ofReal_toReal (htop τ)]

/-- **Unnormalized variant of `volume_le_two_mul_insideMajor`**: if `E` has finite measure and
`2 |F̃| ≤ |E|`, then `|E| ≤ 2 |E ∖ F̃|`. (The X1 lemma needs `1/2 < |E|` and `|F̃| ≤ 1/4`.) -/
theorem volume_le_two_mul_insideMajor_of_two_mul_le {F E : Set ℝ} (hEtop : volume E ≠ ⊤)
    (hF : 2 * volume (insideTildeF F) ≤ volume E) :
    volume E ≤ 2 * volume (insideMajor F E) := by
  have hMtop : volume (insideMajor F E) ≠ ⊤ :=
    ne_top_of_le_ne_top hEtop (measure_mono (insideMajor_subset F E))
  have hFttop : volume (insideTildeF F) ≠ ⊤ :=
    ne_top_of_le_ne_top hEtop (le_trans (le_mul_of_one_le_left zero_le one_le_two) hF)
  have h1 : volume E ≤ volume (insideMajor F E) + volume (insideTildeF F) :=
    (measure_mono (Set.subset_sdiff_union E (insideTildeF F))).trans (measure_union_le _ _)
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hMtop, hFttop⟩) h1
  rw [ENNReal.toReal_add hMtop hFttop] at h2
  have h3 : 2 * (volume (insideTildeF F)).toReal ≤ (volume E).toReal := by
    have := ENNReal.toReal_mono hEtop hF
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at this
  rw [← ENNReal.ofReal_toReal hEtop, ← ENNReal.ofReal_toReal hMtop,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **B1 (summary).** For measurable `E i` of finite positive measure, any `τ` and `C₀ ≥ 48`, with
`Ω = Ω(E, τ)` and `Ẽ = Ẽ(E, τ)`: `Ω` is open, `|Ω| ≤ 8 |E τ|/C₀`, `|F̃| ≤ 3|Ω|`, `|F̃| ≤ |E τ|/2`
(`2|F̃| ≤ |E τ|`), `Ẽ` is measurable, `Ẽ ⊆ E τ`, and `|E τ| ≤ 2 |Ẽ|`. -/
theorem exceptionalMajor_facts {E : Fin 3 → Set ℝ} (hEm : ∀ i, MeasurableSet (E i))
    (h0 : ∀ i, volume (E i) ≠ 0) (htop : ∀ i, volume (E i) ≠ ⊤) {C₀ : ℝ} (hC : 48 ≤ C₀)
    (τ : Fin 3) :
    IsOpen (exceptionalOmega C₀ E τ) ∧
      volume (exceptionalOmega C₀ E τ) ≤ ENNReal.ofReal (8 * (volume (E τ)).toReal / C₀) ∧
      volume (insideTildeF (exceptionalOmega C₀ E τ)) ≤ 3 * volume (exceptionalOmega C₀ E τ) ∧
      2 * volume (insideTildeF (exceptionalOmega C₀ E τ)) ≤ volume (E τ) ∧
      MeasurableSet (exceptionalMajor C₀ E τ) ∧ exceptionalMajor C₀ E τ ⊆ E τ ∧
      volume (E τ) ≤ 2 * volume (exceptionalMajor C₀ E τ) := by
  have hC0 : 0 < C₀ := by linarith
  have h2 := two_mul_volume_insideTildeF_exceptionalOmega_le hEm h0 htop hC τ
  exact ⟨isOpen_exceptionalOmega C₀ E τ, volume_exceptionalOmega_le hEm h0 htop hC0 τ,
    volume_insideTildeF_le _, h2, measurableSet_insideMajor _ (hEm τ), insideMajor_subset _ _,
    volume_le_two_mul_insideMajor_of_two_mul_le (htop τ) h2⟩


/-! ### B2 for `Ω(E, τ)`, `Ẽ(E, τ)` -/

/-- Off `Ω(E, τ)`, `M 1_{E v} ≤ μ_v = C₀ |E v| / |E τ|` for every `v ≠ τ`. -/
theorem maximalHLR_indicator_le_excMass {C₀ : ℝ} (hC : 0 ≤ C₀) {E : Fin 3 → Set ℝ}
    {τ v : Fin 3} (hv : v ≠ τ) (htop : volume (E v) ≠ ⊤) {x : ℝ}
    (hx : x ∉ exceptionalOmega C₀ E τ) :
    maximalHLR ((E v).indicator (1 : ℝ → ℝ)) x ≤ ENNReal.ofReal (excMass C₀ E τ v) := by
  have hx' : x ∉ exceptionalSet (E v) (C₀ / (volume (E τ)).toReal) := fun h =>
    hx (mem_exceptionalOmega.2 ⟨v, hv, h⟩)
  refine (maximalHLR_indicator_le_of_notMem hx').trans_eq ?_
  unfold excMass
  rw [show C₀ * (volume (E v)).toReal / (volume (E τ)).toReal =
      C₀ / (volume (E τ)).toReal * (volume (E v)).toReal by ring,
    ENNReal.ofReal_mul (div_nonneg hC ENNReal.toReal_nonneg), ENNReal.ofReal_toReal htop]

/-- Points of `Ẽ(E, τ) = insideMajor Ω (E τ)` stay outside `3J` for every `J ∈ maxDyadicKeys Ω`. -/
theorem notMem_dilate_of_mem_insideMajor {Ω E : Set ℝ} {J : ℤ × ℤ} (hJ : J ∈ maxDyadicKeys Ω)
    {y : ℝ} (hy : y ∈ insideMajor Ω E) : y ∉ dilate 3 (dyadicInt J.1 J.2) := fun hmem =>
  hy.2 (Set.mem_biUnion hJ hmem)

/-- **B2(a) for `Ω(E, τ)`.** If the interval `I` is not contained in `Ω(E, τ)`, then for `v ≠ τ`,
`λ_M(1_{E v}; I) ≤ 45 μ_v` (`M ≥ 2`). -/
theorem tailMass_indicator_le_excMass_of_not_subset {M : ℝ} (hM : 2 ≤ M) {C₀ : ℝ} (hC : 0 ≤ C₀)
    {E : Fin 3 → Set ℝ} {τ v : Fin 3} (hv : v ≠ τ) (hEm : MeasurableSet (E v))
    (htop : volume (E v) ≠ ⊤) {I : Set ℝ} (hI : I.OrdConnected) (hL : 0 < (volume I).toReal)
    (hnot : ¬ I ⊆ exceptionalOmega C₀ E τ) :
    tailMass M ((E v).indicator (1 : ℝ → ℝ)) I ≤ 45 * excMass C₀ E τ v := by
  obtain ⟨x₀, hx₀I, hx₀⟩ := Set.not_subset.1 hnot
  exact tailMass_indicator_le_of_mem hM hI hEm hL hx₀I (excMass_nonneg hC E τ v)
    (maximalHLR_indicator_le_excMass hC hv htop hx₀)

/-- **B2(b) for `Ω(E, τ)`, combined form** (both bounds `C_M 2^{n+1} μ_v` and `C_M`, in the truncated
form used by B11): `λ_M(1_{E v}; I) ≤ C_M · 2^{n+1} · μ''_v`, `μ''_v = min (1, 2 μ_v)`,
`C_M = max (80, 2^{M/2+1}/(M-1))`. -/
theorem tailMass_indicator_le_excMassTrunc {M : ℝ} (hM : 2 ≤ M) {C₀ : ℝ} (hC : 0 ≤ C₀)
    {E : Fin 3 → Set ℝ} {τ v : Fin 3} (hv : v ≠ τ) (hEm : MeasurableSet (E v))
    (htop : volume (E v) ≠ ⊤) {J : ℤ × ℤ} (hJ : J ∈ maxDyadicKeys (exceptionalOmega C₀ E τ))
    {s w : ℤ} {n : ℕ} (hIJ : dyadicInt s w ⊆ dyadicInt J.1 J.2) (hn : J.1 = s + n) :
    tailMass M ((E v).indicator (1 : ℝ → ℝ)) (dyadicInt s w) ≤
      tailC M * ((2 : ℝ) ^ (n + 1) * excMassTrunc C₀ E τ v) :=
  tailMass_indicator_le_tailC_mul hM hEm (excMass_nonneg hC E τ v)
    (fun _ hx => maximalHLR_indicator_le_excMass hC hv htop hx) hJ hIJ hn

/-- **B2(c).** Let `J ∈ maxDyadicKeys Ω(E, τ)` and `I = 2^s[w, w+1) ⊆ J`, `J = 2^{s+n}[·]`. Then
`λ_M(1_{Ẽ}; I) ≤ C_M 2^{-n(M-1)}` (`M > 1`, `C_M = 2^{M/2+1}/(M-1)`; `Ẽ ∩ 3J = ∅`). -/
theorem tailMass_exceptionalMajor_le {M : ℝ} (hM : 1 < M) {C₀ : ℝ} {E : Fin 3 → Set ℝ}
    {τ : Fin 3} {J : ℤ × ℤ} (hJ : J ∈ maxDyadicKeys (exceptionalOmega C₀ E τ)) {s w : ℤ} {n : ℕ}
    (hIJ : dyadicInt s w ⊆ dyadicInt J.1 J.2) (hn : J.1 = s + n) :
    tailMass M ((exceptionalMajor C₀ E τ).indicator (1 : ℝ → ℝ)) (dyadicInt s w) ≤
      tailConst M * (2 : ℝ) ^ (-(M - 1) * (n : ℝ)) :=
  tailMass_indicator_le_of_far_dyadic hM hIJ hn fun _ hy => notMem_dilate_of_mem_insideMajor hJ hy

/-- **B2(d), `E v`.** For `J ∈ maxDyadicKeys Ω(E, τ)`, `v ≠ τ`, `K ≥ 2`:
`∫ 1_{E v}(x) ⟨(x - c(J))/|J|⟩^{-K} dx ≤ 2 C_K |J| μ''_v`, `μ''_v = min (1, 2 μ_v)`. -/
theorem integral_indicator_mul_tailWeight_le_excMassTrunc {K : ℝ} (hK : 2 ≤ K) {C₀ : ℝ}
    (hC : 0 ≤ C₀) {E : Fin 3 → Set ℝ} {τ v : Fin 3} (hv : v ≠ τ) (hEm : MeasurableSet (E v))
    (htop : volume (E v) ≠ ⊤) {J : ℤ × ℤ} (hJ : J ∈ maxDyadicKeys (exceptionalOmega C₀ E τ)) :
    ∫ x, (E v).indicator (1 : ℝ → ℝ) x *
        tailWeight K ((x - intervalCentre (dyadicInt J.1 J.2)) / (2 : ℝ) ^ J.1) ≤
      2 * tailC K * (2 : ℝ) ^ J.1 * excMassTrunc C₀ E τ v :=
  integral_indicator_mul_tailWeight_le_of_maxDyadicKeys hK hEm (excMass_nonneg hC E τ v)
    (fun _ hx => maximalHLR_indicator_le_excMass hC hv htop hx) hJ

/-- **B2(d), `Ẽ`.** `∫ 1_Ẽ(x) ⟨(x - c(J))/|J|⟩^{-K} dx ≤ C_K |J|` for every dyadic `J` and `K > 1`. -/
theorem integral_exceptionalMajor_mul_tailWeight_le {K : ℝ} (hK : 1 < K) (C₀ : ℝ)
    (E : Fin 3 → Set ℝ) (τ : Fin 3) (j w : ℤ) :
    ∫ x, (exceptionalMajor C₀ E τ).indicator (1 : ℝ → ℝ) x *
        tailWeight K ((x - intervalCentre (dyadicInt j w)) / (2 : ℝ) ^ j) ≤
      tailConst K * (2 : ℝ) ^ j :=
  integral_indicator_mul_tailWeight_le hK _ j w


theorem exceptionalMajor_subset (C₀ : ℝ) (E : Fin 3 → Set ℝ) (τ : Fin 3) :
    exceptionalMajor C₀ E τ ⊆ E τ :=
  insideMajor_subset _ _

theorem measurableSet_exceptionalMajor {E : Fin 3 → Set ℝ} (C₀ : ℝ) (τ : Fin 3)
    (hE : MeasurableSet (E τ)) : MeasurableSet (exceptionalMajor C₀ E τ) :=
  measurableSet_insideMajor _ hE

theorem tailMass_nonneg {V : Type*} [SeminormedAddGroup V] (M : ℝ) (f : ℝ → V) (I : Set ℝ) :
    0 ≤ tailMass M f I :=
  mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
    (integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (tailWeight_nonneg _ _))

end PrimeBHT.TimeFrequency.X2.V16
