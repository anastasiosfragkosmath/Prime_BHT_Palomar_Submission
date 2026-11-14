module

public import PrimeBHT.TimeFrequency.Interp.Hull.Exponents
public import PrimeBHT.TimeFrequency.Interp.Hull.Glue
public import PrimeBHT.TimeFrequency.Interp.Hull.ModelForm
public import PrimeBHT.TimeFrequency.Interp.Hull.Bilinear
public import PrimeBHT.TimeFrequency.Interp.Hull.Chain
public import PrimeBHT.TimeFrequency.Interp.Hull.ChainR6b
public import PrimeBHT.TimeFrequency.Interp.Strong
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The model bound (MB): `‖Π_P(f₁, f₂)‖_{L^r} ≤ C_MB ‖f₁‖_p ‖f₂‖_q` for Schwartz functions

Blueprint `docs/x1-blueprint.md`, nodes R5 (statement of (MB)) and R6c (Corollary (MB)).  This file
connects the abstract chain R6a/R6b/R6c (`PrimeBHT.TimeFrequency.Interp.{Restricted, Strong}`) and
the C11 glue (`PrimeBHT.TimeFrequency.Interp.Hull.*`) to the model bound required by R5.

## Main definitions and results

* `ModelBound p q r N C`: for every valid `ν = (a, b, s', α)`, finite `P ⊆ triIdx s' α`, packets `φ`
  adapted with exponent `N` to the tri-tiles of `P`, and Schwartz `f₁ f₂`,
  `‖Π_P(f₁, f₂)‖_{L^r} ≤ C ‖f₁‖_{L^p} ‖f₂‖_{L^q}` with `Π_P = modelOp P φ` (`ModelForm.lean`).
* `modelBound_of_m1` (**the model bound, conditional on `M1Prop`**): for `1 < p`, `1 < q`,
  `1/r = 1/p + 1/q`, `2/3 < r` there are `N` and `C` (depending on `p, q` only) with
  `ModelBound p q r N C`.  `M1Prop` is the type of the frozen M1(ε) (`Glue.lean`).
* `exists_modelBound_le_one_of_m1` (R6c-I, `r ≤ 1`, via `hRS_modelOp_of_m1`) and
  `exists_modelBound_one_lt_of_m1` (R6c-II, `r > 1`, via `hRT_triForm_of_m1`): the two cases.
* `tendsto_pairing_of_dominated`, `tendsto_modelOp`: the continuity `hcont`/`hlim` of the model
  operator along dominated simple approximations (dominated convergence in each coefficient).

## Proof

Both cases approximate the Schwartz inputs by Mathlib's `SimpleFunc.approxOn` (`‖s_j‖ ≤ 2 ‖f‖`,
pointwise convergence: `exists_simpleFunc_approx`).  For finite `P` and adapted (bounded, continuous,
integrable) packets, `⟨s_j, φ_{t,k}⟩ → ⟨f, φ_{t,k}⟩` by dominated convergence (`2 |f| ‖φ‖_∞`
integrable since a Schwartz function is integrable), so `Π_P(s₁ j, s₂ j) → Π_P(f₁, f₂)` pointwise
everywhere; Fatou is inside `eLpNorm_le_of_restrictedStrong_of_continuous` (R6c-I) and
`eLpNorm_le_of_restrictedType_of_ae_tendsto` (R6c-II) of `Strong.lean`.

* `r ≤ 1`: `hRS` of R6c-I is `hRS_modelOp_of_m1` at `η = m/2`, `δ₀ = m/8` with
  `m = min(1/p, 1/q, 1 - 1/p, 1 - 1/q, 3/2 - 1/r) > 0`; `hadd`, `hsmul` are `Bilinear.lean`.
* `r > 1`: `Λ = conjForm (triForm P φ)` (the conjugate form, so that `hdom` is
  `isDominated_modelOp_of_adapted`), `hsub` from `IsSubadditive.conjForm`, `hhom` from
  `Bilinear.lean`, `hRT` from `hRT_triForm_of_m1` at `ε = 2η`, `η = min(m/2, 1/8)`,
  `δ₀ = m/2`, `m = min(1/p, 1/q, 1 - 1/r)`, applied to the conjugated third test function.
-/

@[expose] public section

namespace PrimeBHT.TimeFrequency.Interp.Hull

open MeasureTheory Filter Topology
open PrimeBHT.Statements
open PrimeBHT.TimeFrequency.Interp.Restricted
open scoped ENNReal

/-- **The model bound** (MB): for every valid `ν = (a, b, s', α)`, finite `P ⊆ triIdx s' α`, packets
`φ` adapted with exponent `N` to the tri-tiles of `P` and Schwartz functions `f₁ f₂`,
`‖Π_P(f₁, f₂)‖_{L^r} ≤ C ‖f₁‖_{L^p} ‖f₂‖_{L^q}` (`Π_P = modelOp P φ`). -/
def ModelBound (p q r : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ (a b s' α : ℤ), TriValid a b s' α →
    ∀ (P : Finset (ℤ × ℤ × ℤ)), (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α →
      ∀ φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ,
        (∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) →
        ∀ f₁ f₂ : SchwartzMap ℝ ℂ,
          eLpNorm (modelOp P φ ⇑f₁ ⇑f₂) (ENNReal.ofReal r) volume ≤
            ENNReal.ofReal C * eLpNorm (⇑f₁) (ENNReal.ofReal p) volume *
              eLpNorm (⇑f₂) (ENNReal.ofReal q) volume

/-! ### Continuity of the model operator along dominated simple approximations -/

/-- Dominated convergence for one coefficient: `⟨s_j, φ⟩ → ⟨f, φ⟩` if `f` is integrable, `φ` is
bounded and measurable, and `s_j → f` pointwise with `‖s_j‖ ≤ 2 ‖f‖`. -/
lemma tendsto_pairing_of_dominated {f : ℝ → ℂ} {s : ℕ → ℝ → ℂ} {φ : ℝ → ℂ} {B : ℝ}
    (hf : Integrable f) (hs : ∀ j, AEStronglyMeasurable (s j) volume)
    (hφm : AEStronglyMeasurable φ volume) (hφ : ∀ x, ‖φ x‖ ≤ B)
    (hdom : ∀ j x, ‖s j x‖ ≤ 2 * ‖f x‖)
    (hlim : ∀ x, Tendsto (fun j => s j x) atTop (𝓝 (f x))) :
    Tendsto (fun j => pairing (s j) φ) atTop (𝓝 (pairing f φ)) := by
  unfold pairing
  refine tendsto_integral_of_dominated_convergence (fun x => 2 * ‖f x‖ * B) (fun j => ?_) ?_
    (fun j => ?_) ?_
  · exact (hs j).mul (Complex.continuous_conj.comp_aestronglyMeasurable hφm)
  · exact (hf.norm.const_mul 2).mul_const B
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hdom j x) (hφ x) (norm_nonneg _) (by positivity)
  · exact Filter.Eventually.of_forall fun x => (hlim x).mul tendsto_const_nhds

/-- `Π_P(s₁ j, s₂ j) → Π_P(f₁, f₂)` pointwise, for finite `P`, adapted packets, integrable `fᵢ` and
dominated pointwise approximations `sᵢ j → fᵢ`, `‖sᵢ j‖ ≤ 2 ‖fᵢ‖`. -/
lemma tendsto_modelOp {P : Finset (ℤ × ℤ × ℤ)} {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {N : ℕ} {a b : ℤ}
    (hφ : ∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k))
    {f₁ f₂ : ℝ → ℂ} (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) {s₁ s₂ : ℕ → ℝ → ℂ}
    (hs₁m : ∀ j, AEStronglyMeasurable (s₁ j) volume)
    (hs₂m : ∀ j, AEStronglyMeasurable (s₂ j) volume)
    (hs₁ : ∀ j x, ‖s₁ j x‖ ≤ 2 * ‖f₁ x‖) (hs₂ : ∀ j x, ‖s₂ j x‖ ≤ 2 * ‖f₂ x‖)
    (ht₁ : ∀ x, Tendsto (fun j => s₁ j x) atTop (𝓝 (f₁ x)))
    (ht₂ : ∀ x, Tendsto (fun j => s₂ j x) atTop (𝓝 (f₂ x))) (x : ℝ) :
    Tendsto (fun j => modelOp P φ (s₁ j) (s₂ j) x) atTop (𝓝 (modelOp P φ f₁ f₂ x)) := by
  unfold modelOp
  refine tendsto_finsetSum _ fun t ht => ?_
  have h0 := tendsto_pairing_of_dominated hf₁ hs₁m
    (measurable_of_isAdapted (hφ t ht 0)).aestronglyMeasurable
    (norm_le_tileWeight_of_isAdapted (hφ t ht 0)) hs₁ ht₁
  have h1 := tendsto_pairing_of_dominated hf₂ hs₂m
    (measurable_of_isAdapted (hφ t ht 1)).aestronglyMeasurable
    (norm_le_tileWeight_of_isAdapted (hφ t ht 1)) hs₂ ht₂
  exact (tendsto_const_nhds.mul (h0.mul h1)).mul tendsto_const_nhds


/-! ### Choice of the exponent neighbourhood -/

/-- Exponents for R6c-I (`r ≤ 1`): `η > 0` and `δ₀ > 0` such that the points `(1/p + t, 1/q - t)`,
`|t| < 2δ₀`, lie in `InReg η` (the hypotheses of `hRS_modelOp_of_m1`). -/
lemma exists_exponents_le_one {p q r : ℝ} (hp : 1 < p) (hq : 1 < q) (hr' : 2 / 3 < r) :
    ∃ η δ₀ : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ 0 < δ₀ ∧ η + 2 * δ₀ ≤ 1 / p ∧ η + 2 * δ₀ ≤ 1 / q ∧
      1 / p + 2 * δ₀ ≤ 1 - η ∧ 1 / q + 2 * δ₀ ≤ 1 - η ∧ 1 / r ≤ 3 / 2 - η ∧ δ₀ < 1 / q := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hr0 : 0 < r := by linarith
  have h1p : 0 < 1 / p := by positivity
  have h1q : 0 < 1 / q := by positivity
  have h1p' : 1 / p < 1 := (div_lt_one hp0).2 hp
  have h1q' : 1 / q < 1 := (div_lt_one hq0).2 hq
  have h1r : 1 / r < 3 / 2 := by
    have := one_div_lt_one_div_of_lt (show (0 : ℝ) < 2 / 3 by norm_num) hr'
    have e : (1 : ℝ) / (2 / 3) = 3 / 2 := by norm_num
    linarith
  obtain ⟨m, hm, hm1, hm2, hm3, hm4, hm5⟩ : ∃ m : ℝ, 0 < m ∧ m ≤ 1 / p ∧ m ≤ 1 / q ∧
      m ≤ 1 - 1 / p ∧ m ≤ 1 - 1 / q ∧ m ≤ 3 / 2 - 1 / r :=
    ⟨min (min (1 / p) (1 / q)) (min (min (1 - 1 / p) (1 - 1 / q)) (3 / 2 - 1 / r)),
      lt_min (lt_min h1p h1q) (lt_min (lt_min (by linarith) (by linarith)) (by linarith)),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  refine ⟨m / 2, m / 8, by positivity, by linarith, by positivity, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith⟩

/-- Exponents for R6c-II (`r > 1`): `0 < η ≤ 1/8`, `δ₀ > 0` with `η + δ₀ ≤ 1/p, 1/q, 1 - 1/r` and
`δ₀/2 < 1/q, 1 - 1/r`. -/
lemma exists_exponents_one_lt {p q r : ℝ} (hp : 1 < p) (hq : 1 < q) (hr1 : 1 < r) :
    ∃ η δ₀ : ℝ, 0 < η ∧ η ≤ 1 / 8 ∧ 0 < δ₀ ∧ η + δ₀ ≤ 1 / p ∧ η + δ₀ ≤ 1 / q ∧
      η + δ₀ ≤ 1 - 1 / r ∧ δ₀ / 2 < 1 / q ∧ δ₀ / 2 < 1 - 1 / r := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hr0 : 0 < r := by linarith
  have h1p : 0 < 1 / p := by positivity
  have h1q : 0 < 1 / q := by positivity
  have h1r : 1 / r < 1 := (div_lt_one hr0).2 hr1
  obtain ⟨m, hm, hm1, hm2, hm3⟩ : ∃ m : ℝ, 0 < m ∧ m ≤ 1 / p ∧ m ≤ 1 / q ∧ m ≤ 1 - 1 / r :=
    ⟨min (1 / p) (min (1 / q) (1 - 1 / r)), lt_min h1p (lt_min h1q (by linarith)),
      min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  have hη₁ : min (m / 2) (1 / 8) ≤ m / 2 := min_le_left _ _
  have hη₂ : min (m / 2) (1 / 8) ≤ 1 / 8 := min_le_right _ _
  refine ⟨min (m / 2) (1 / 8), m / 2, lt_min (by positivity) (by norm_num), hη₂, by positivity,
    by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-! ### Small algebraic helpers -/

lemma ofReal_mul_toReal_mul_toReal {c : ℝ} (hc : 0 ≤ c) {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    ENNReal.ofReal (c * a.toReal * b.toReal) = ENNReal.ofReal c * a * b := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hc, ENNReal.ofReal_toReal ha,
    ENNReal.ofReal_toReal hb]

lemma conjSlot_vec3 (f g h : ℝ → ℂ) :
    conjSlot ![f, g, h] = ![f, g, fun x => (starRingEnd ℂ) (h x)] := by
  ext i x
  fin_cases i <;> simp [conjSlot, Function.update]

lemma conjForm_vec3 (Λ : (Fin 3 → ℝ → ℂ) → ℝ) (f g h : ℝ → ℂ) :
    conjForm Λ ![f, g, h] = Λ ![f, g, fun x => (starRingEnd ℂ) (h x)] := by
  unfold conjForm
  rw [conjSlot_vec3]


/-! ### The case `r ≤ 1` (R6c-I) -/

/-- **(MB), `r ≤ 1`** (R6c-I, via `hRS_modelOp_of_m1`; conditional on `M1Prop`). -/
theorem exists_modelBound_le_one_of_m1 (hM1 : M1Prop) {p q r : ℝ} (hp : 1 < p) (hq : 1 < q)
    (hr : 1 / r = 1 / p + 1 / q) (hr' : 2 / 3 < r) (hr1 : r ≤ 1) :
    ∃ (N : ℕ) (C : ℝ), ModelBound p q r N C := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hr0 : 0 < r := by linarith
  obtain ⟨η, δ₀, hη, hη4, hδ₀, h1, h2, h3, h4, h5, h6⟩ := exists_exponents_le_one hp hq hr'
  obtain ⟨N, C₀, hC₀, H⟩ := hRS_modelOp_of_m1 hM1 hη
  have hW : 0 ≤ weakBound (η / 2) C₀ := le_max_of_le_left (by positivity)
  have hr1' : 1 ≤ 1 / r := (one_le_div hr0).2 hr1
  have hK : 0 ≤ rsConst (1 / r) (η / 2) (weakBound (η / 2) C₀) (weakBound (η / 2) C₀) :=
    rsConst_nonneg (by linarith) (by positivity) (by linarith) hW hW
  refine ⟨N, strongConstI p q r δ₀
    (rsConst (1 / r) (η / 2) (weakBound (η / 2) C₀) (weakBound (η / 2) C₀)) * 2 * 2,
    fun a b s' α hν P hP φ hφ f₁ f₂ => ?_⟩
  have hint : ∀ t ∈ P, ∀ k, Integrable (φ t k) := fun t ht k => integrable_of_isAdapted (hφ t ht k)
  exact eLpNorm_le_of_restrictedStrong_of_continuous (T := modelOp P φ) (μ := volume)
    (ν := volume) hp0 hq0 hr0 hr1 hr hδ₀ h6 hK (modelOp_hadd₁ hint) (modelOp_hsmul₁ P φ)
    (modelOp_hadd₂ hint) (modelOp_hsmul₂ P φ)
    (fun t ht E₁ E₂ hE₁ hE₂ hE₁f hE₂f g₁ g₂ hg₁ hg₂ =>
      H a b s' α hν P hP φ hφ hr h1 h2 h3 h4 h5 t ht E₁ E₂ hE₁ hE₂ hE₁f hE₂f g₁ g₂ g₁.measurable
        g₂.measurable hg₁ hg₂)
    f₁ f₂ f₁.continuous.measurable f₂.continuous.measurable
    ((f₁.memLp _ _).eLpNorm_lt_top) ((f₂.memLp _ _).eLpNorm_lt_top)
    (fun s₁ s₂ hs₁ hs₂ ht₁ ht₂ => Filter.Eventually.of_forall fun x =>
      tendsto_modelOp hφ f₁.integrable f₂.integrable (fun j => (s₁ j).aestronglyMeasurable)
        (fun j => (s₂ j).aestronglyMeasurable) hs₁ hs₂ ht₁ ht₂ x)


/-! ### The case `r > 1` (R6c-II) -/

/-- **(MB), `r > 1`** (R6c-II, via `hRT_triForm_of_m1`; conditional on `M1Prop`). -/
theorem exists_modelBound_one_lt_of_m1 (hM1 : M1Prop) {p q r : ℝ} (hp : 1 < p) (hq : 1 < q)
    (hr : 1 / r = 1 / p + 1 / q) (hr1 : 1 < r) :
    ∃ (N : ℕ) (C : ℝ), ModelBound p q r N C := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hr0 : 0 < r := by linarith
  have hr1' : r - 1 ≠ 0 := by linarith
  obtain ⟨η, δ₀, hη, hη8, hδ₀, h1, h2, h3, h4, h5⟩ := exists_exponents_one_lt hp hq hr1
  obtain ⟨N, C₀, hC₀, H⟩ := hRT_triForm_of_m1 hM1 (ε := 2 * η) (by linarith) (by linarith)
  have hp3e : 1 / (r / (r - 1)) = 1 - 1 / r := by
    field_simp
  have hp3 : 1 / p + 1 / q + 1 / (r / (r - 1)) = 1 := by
    rw [hp3e, ← hr]
    ring
  have hp3pos : 0 < r / (r - 1) := div_pos hr0 (by linarith)
  have hq : 0 < 1 - (2 : ℝ) ^ (-η) := by
    have : (2 : ℝ) ^ (-η) < 1 := by
      rw [Real.rpow_neg (by norm_num)]
      exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) hη)
    linarith
  have hK : 0 ≤ C₀ / (1 - (2 : ℝ) ^ (-η)) := div_nonneg hC₀.le hq.le
  have hS : 0 ≤ strongConstII p q (r / (r - 1)) δ₀ (C₀ / (1 - (2 : ℝ) ^ (-η))) := by
    have := d2Const_nonneg hp0 hq0 hp3pos (by positivity : 0 < δ₀ / 2)
    unfold strongConstII
    positivity
  refine ⟨N, 2 * (strongConstII p q (r / (r - 1)) δ₀ (C₀ / (1 - (2 : ℝ) ^ (-η))) * 2 * 2),
    fun a b s' α hν P hP φ hφ f₁ f₂ => ?_⟩
  have hint : ∀ t ∈ P, ∀ k, Integrable (φ t k) := fun t ht k => integrable_of_isAdapted (hφ t ht k)
  have hRT := H a b s' α hν P hP φ hφ (p₁ := p) (p₂ := q) (p₃ := r / (r - 1)) (δ₀ := δ₀)
    (η := η) hp3 hη le_rfl hδ₀.le h1 h2 (by linarith)
  have hsub := (isSubadditive_triForm_of_adapted hφ).conjForm
  obtain ⟨s₁, hs₁, ht₁⟩ := exists_simpleFunc_approx f₁.continuous.measurable
  obtain ⟨s₂, hs₂, ht₂⟩ := exists_simpleFunc_approx f₂.continuous.measurable
  have key := eLpNorm_le_of_restrictedType_of_ae_tendsto (T := modelOp P φ)
    (Λ := fun f g h => conjForm (triForm P φ) ![f, g, h]) (μ := volume) (p₁ := p) (p₂ := q)
    (r := r) (δ₀ := δ₀) (K := C₀ / (1 - (2 : ℝ) ^ (-η))) (M := 2) hp0 hq0 hr1 hr hδ₀
    (by linarith) (by rw [hp3e]; exact h5) hK zero_le_two
    (fun f f' g h => hsub.sub₁ f f' g h) (fun f g g' h => hsub.sub₂ f g g' h)
    (fun f g h h' => hsub.sub₃ f g h h')
    (fun c hc f g h => by
      show conjForm (triForm P φ) ![⇑(c • f), ⇑g, ⇑h] = c * conjForm (triForm P φ) ![⇑f, ⇑g, ⇑h]
      rw [conjForm_vec3, conjForm_vec3, SimpleFunc.coe_smul]
      exact triForm_smul_first P φ hc _ _ _)
    (fun c hc f g h => by
      show conjForm (triForm P φ) ![⇑f, ⇑(c • g), ⇑h] = c * conjForm (triForm P φ) ![⇑f, ⇑g, ⇑h]
      rw [conjForm_vec3, conjForm_vec3, SimpleFunc.coe_smul]
      exact triForm_smul_second P φ hc _ _ _)
    (fun c hc f g h => by
      show conjForm (triForm P φ) ![⇑f, ⇑g, ⇑(c • h)] = c * conjForm (triForm P φ) ![⇑f, ⇑g, ⇑h]
      have e : (fun x => (starRingEnd ℂ) ((c • ⇑h) x)) =
          c • fun x => (starRingEnd ℂ) (h x) := by
        funext x
        simp [Complex.real_smul]
      rw [conjForm_vec3, conjForm_vec3, SimpleFunc.coe_smul, e]
      exact triForm_smul_third P φ hc _ _ _)
    (fun d₁ d₂ d₃ hd hd₁ hd₂ hd₃ E₁ E₂ E₃ hE₁ hE₂ hE₃ hE₁f hE₂f hE₃f g₁ g₂ g₃ hg₁ hg₂ hg₃ => by
      have := hRT d₁ d₂ d₃ hd hd₁ hd₂ hd₃ E₁ E₂ E₃ hE₁ hE₂ hE₃ hE₁f hE₂f hE₃f g₁ g₂
        (fun x => (starRingEnd ℂ) (g₃ x)) g₁.measurable g₂.measurable
        (measurable_conj_fun g₃.measurable) hg₁ hg₂ (DominatedBy.conj hg₃)
      show conjForm (triForm P φ) ![⇑g₁, ⇑g₂, ⇑g₃] ≤ _
      rw [conjForm_vec3]
      exact this)
    (fun f₁ f₂ => (measurable_modelOp_of_adapted hφ _ _).aestronglyMeasurable)
    (fun f₁ f₂ h => isDominated_modelOp_of_adapted hφ f₁ f₂ h (IsBdd.of_simpleFunc f₁)
      (IsBdd.of_simpleFunc f₂) (IsBdd.of_simpleFunc h))
    f₁ f₂ ((f₁.memLp _ _).eLpNorm_lt_top) ((f₂.memLp _ _).eLpNorm_lt_top) s₁ s₂ hs₁ hs₂
    (Filter.Eventually.of_forall fun x =>
      tendsto_modelOp hφ f₁.integrable f₂.integrable (fun j => (s₁ j).aestronglyMeasurable)
        (fun j => (s₂ j).aestronglyMeasurable) hs₁ hs₂ ht₁ ht₂ x)
  refine key.trans (le_of_eq ?_)
  have hfin₁ : eLpNorm (⇑f₁) (ENNReal.ofReal p) volume ≠ ⊤ := ((f₁.memLp _ _).eLpNorm_lt_top).ne
  have hfin₂ : eLpNorm (⇑f₂) (ENNReal.ofReal q) volume ≠ ⊤ := ((f₂.memLp _ _).eLpNorm_lt_top).ne
  have hc : 0 ≤ 2 * (strongConstII p q (r / (r - 1)) δ₀ (C₀ / (1 - (2 : ℝ) ^ (-η))) * 2 * 2) := by
    positivity
  rw [← ofReal_mul_toReal_mul_toReal hc hfin₁ hfin₂]
  congr 1
  ring


/-! ### The model bound -/

/-- **The model bound (MB)** (blueprint R5/R6c), conditional on `M1Prop` (the type of the frozen
M1(ε)): for `1 < p`, `1 < q`, `1/r = 1/p + 1/q` and `2/3 < r` there are `N` and `C`, depending on
`p, q` only, such that `‖Π_P(f₁, f₂)‖_{L^r} ≤ C ‖f₁‖_{L^p} ‖f₂‖_{L^q}` for all valid `ν`, finite
`P ⊆ triIdx s' α`, packets adapted with exponent `N`, and Schwartz `f₁ f₂`. -/
theorem modelBound_of_m1 (hM1 : M1Prop) {p q r : ℝ} (hp : 1 < p) (hq : 1 < q)
    (hr : 1 / r = 1 / p + 1 / q) (hr' : 2 / 3 < r) :
    ∃ (N : ℕ) (C : ℝ), ModelBound p q r N C := by
  rcases le_or_gt r 1 with h | h
  · exact exists_modelBound_le_one_of_m1 hM1 hp hq hr hr' h
  · exact exists_modelBound_one_lt_of_m1 hM1 hp hq hr h

end PrimeBHT.TimeFrequency.Interp.Hull
