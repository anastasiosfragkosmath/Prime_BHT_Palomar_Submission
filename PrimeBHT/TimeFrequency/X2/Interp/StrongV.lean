module

public import PrimeBHT.TimeFrequency.X2.Interp.OperatorV
public import PrimeBHT.TimeFrequency.Interp.Strong
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# X2, node V17 (I3, I4): restricted strong type ⇒ strong type at `(2, 2, ∞)`, and the pairing

Instantiation of the verified X1 theorem R6c-I (`PrimeBHT.TimeFrequency.Interp.eLpNorm_le_of_restrictedStrong`,
`Interp/Strong.lean`, used UNCHANGED: it is already stated for arbitrary normed `ℝ`-spaces `F` (inputs) and
`E` (outputs) and a general `T : (α → F) → (α → F) → β → E`) at `p₁ = p₂ = 2`, `r = 1`, on top of
`OperatorV.lean` (R6b, the hypothesis `hRS`) and `FormV.lean` (R6a).  Source of the mathematics:
`docs/audits/X2-V16B-route-check.md` §1.1.

## Setting

As in `OperatorV.lean`, with the first two slot norms the norm of the normed space `W`:
`ν 0 w = ‖w‖`, `ν 1 w = ‖w‖` (X2: `W = YVec P 2 = (ℂ^P, yNorm 2)`, a type synonym of `ZMod P → ℂ`; the third
slot norm `ν 2 = yNorm u` is a function on the same carrier, not the norm of `W`).  The output space is a
normed `ℝ`-space `E` (X2: `X_u'`), `pr : E → W → ℂ` the duality pairing.

## Results

* `InCornerNbhd R β` (defined in `FormV.lean`): the corner region `𝒩_R = {Σβ = 1, |β₁ - 1/2| ≤ 1/(8R), |β₂ - 1/2| ≤ 1/(8R)}` of the
  route check §1.2.
* `weakPoint_corner` (the verification of the audit's numbers): for `R ≥ 1`, `|t| < 1/(32R)` (`= 2δ₀`),
  `|e| ≤ 1/(64R)` (`= ε`), the exponent `a = (1/2 + t + e, 1/2 - t)` satisfies `WeakPoint (InCornerNbhd R)
  κ m a₁ a₂` with `κ = 1/(16R)`, `m = 3/(64R)`: `α(a)`, `α(a - κ e₁)`, `α(a - κ e₂)` lie in `𝒩_R` (the largest
  deviation from `1/2` is `7/(64R) < 1/(8R)`) and the sub-case points have all exponents `≥ 3/(64R)`.
* `eLpNorm_le_of_hullBound_corner_simple` (**I3**, R6c-I at `p₁ = p₂ = 2`, `r = 1`): from
  `VHullBound` on `𝒩_R` with constant `K > 0` (plus `IsSubadditiveV`, `IsSmallV`, domination, bilinearity on
  simple functions), `‖T(f₁,f₂)‖_{L¹} ≤ (cornerConst R) K ‖f₁‖_{L²} ‖f₂‖_{L²}` for simple `f_i ∈ L²`.
* `eLpNorm_le_of_hullBound_corner`: the same for measurable `f_i ∈ L²` under the continuity hypothesis `hcont`
  (Corollary (MB) of R6c-I), constant `4 (cornerConst R) K`, for every `K ≥ 0` (the case `K = 0` by a limit).
* `enorm_integral_pair_le` (**I4**): `‖∫ pr (F x) (g x)‖ₑ ≤ ‖F‖_{L¹(E)} · ‖ν₂ ∘ g‖_{L^∞}` (Hölder with the
  pairing bound `‖pr e v‖ ≤ ‖e‖ ν₂ v`); it is a short lemma.
* `v17_abstract`: the combination, the abstract form of the V17 statement:
  `‖∫ pr (T F₁ F₂ x) (F₃ x) dμ‖ₑ ≤ C₁ K ‖F₁‖_{L²} ‖F₂‖_{L²} ‖ν₂ ∘ F₃‖_{L^∞}` with `C₁ = 4 · cornerConst R`
  LINEAR in `K`.

## What is left to the instantiation (X2 assembly)

The concrete data: `W := YVec P 2` and the norm identification `‖w‖ = yNorm 2 w` (so `ν = slotNorms u`),
the near-norming of `yPair` on `X_u' × X_u` (Hölder's equality case; the field `norming` of `IsDualPairing`),
`IsDualPairing (yNorm u) yPair` (the Lipschitz field is Hölder `‖yPair a b‖ ≤ yNorm u' a · yNorm u b`), and the
bilinearity/continuity of the model operator.
-/

@[expose] public section

namespace PrimeBHT.TimeFrequency.X2.Interp

open MeasureTheory Filter Topology
open scoped ENNReal
open PrimeBHT.TimeFrequency.Interp (strongConstI d1Const d1Const_nonneg
  eLpNorm_le_of_restrictedStrong eLpNorm_le_of_restrictedStrong_of_continuous)
open PrimeBHT.TimeFrequency.Interp.Restricted (alphaOf rsConst rsConst_nonneg)

local infixr:25 " →ₛ " => SimpleFunc

/-! ### The audit's points (`InCornerNbhd` is defined in `FormV.lean`) -/

/-- **The audit's numbers (verified).**  For `R ≥ 1`, `|t| < 1/(32R)` and `|e| ≤ 1/(64R)`, the exponent
`a = (1/2 + t + e, 1/2 - t)` is admissible for the weak-type bound with region `𝒩_R`, `κ = 1/(16R)`,
`m = 3/(64R)`: the three points `α(a)`, `α(a - κ e₁)`, `α(a - κ e₂)` lie in `𝒩_R` (deviation from `1/2` at
most `7/(64R) < 1/(8R)`), and `α(a - κ e₁)`, `α(a - κ e₂)` have all exponents `≥ 3/(64R)`. -/
theorem weakPoint_corner {R : ℝ} (hR : 1 ≤ R) {t e : ℝ} (ht : |t| < 1 / (32 * R))
    (he : |e| ≤ 1 / (64 * R)) :
    WeakPoint (InCornerNbhd R) (1 / (16 * R)) (3 / (64 * R)) (1 / 2 + t + e) (1 / 2 - t) := by
  have hR0 : 0 < R := by linarith
  set r : ℝ := 1 / (64 * R) with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r ≤ 1 / 64 := by
    rw [hr, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have e1 : 1 / (32 * R) = 2 * r := by rw [hr]; field_simp; ring
  have e2 : 1 / (16 * R) = 4 * r := by rw [hr]; field_simp; ring
  have e3 : 3 / (64 * R) = 3 * r := by rw [hr]; field_simp
  have e4 : 1 / (8 * R) = 8 * r := by rw [hr]; field_simp; ring
  rw [e1] at ht
  rw [e2, e3]
  have ht' := abs_lt.1 ht
  have he' := abs_le.1 he
  have hcorner : ∀ b₁ b₂ : ℝ, |b₁ - 1 / 2| ≤ 8 * r → |b₂ - 1 / 2| ≤ 8 * r →
      InCornerNbhd R (alphaOf b₁ b₂) := by
    intro b₁ b₂ h₁ h₂
    refine ⟨?_, ?_, ?_⟩
    · show b₁ + b₂ + (1 - b₁ - b₂) = 1
      ring
    · rw [e4]; exact h₁
    · rw [e4]; exact h₂
  refine ⟨by linarith, by linarith, ?_, ?_, ?_, ?_, ?_⟩
  · refine hcorner _ _ (abs_le.2 ⟨by linarith, by linarith⟩) (abs_le.2 ⟨by linarith, by linarith⟩)
  · refine hcorner _ _ (abs_le.2 ⟨by linarith, by linarith⟩) (abs_le.2 ⟨by linarith, by linarith⟩)
  · refine hcorner _ _ (abs_le.2 ⟨by linarith, by linarith⟩) (abs_le.2 ⟨by linarith, by linarith⟩)
  · intro i
    fin_cases i
    · show 3 * r ≤ 1 / 2 + t + e - 4 * r
      linarith
    · show 3 * r ≤ 1 / 2 - t
      linarith
    · show 3 * r ≤ 1 - (1 / 2 + t + e - 4 * r) - (1 / 2 - t)
      linarith
  · intro i
    fin_cases i
    · show 3 * r ≤ 1 / 2 + t + e
      linarith
    · show 3 * r ≤ 1 / 2 - t - 4 * r
      linarith
    · show 3 * r ≤ 1 - (1 / 2 + t + e) - (1 / 2 - t - 4 * r)
      linarith

/-! ### The constants -/

/-- The explicit constant of the strong bound at the corner: with `m = 3/(64R)`, `ε = δ₀ = 1/(64R)`,
`cornerConst R = wk m · rsConst 1 ε 1 1 · 4 · d1Const 2 2 (1/2) δ₀` (`R6c-I`'s `strongConstI 2 2 1 δ₀ K'`
with `K' = K · wk m · rsConst 1 ε 1 1`, linear in `K`). -/
noncomputable def cornerConst (R : ℝ) : ℝ :=
  wk (3 / (64 * R)) * rsConst 1 (1 / (64 * R)) 1 1 * 4 * d1Const 2 2 (1 / 2) (1 / (64 * R))

lemma strongConstI_one (δ₀ K' : ℝ) :
    strongConstI 2 2 1 δ₀ K' = K' * 4 * d1Const 2 2 (1 / 2) δ₀ := by
  unfold strongConstI
  simp

lemma cornerConst_nonneg {R : ℝ} (hR : 1 ≤ R) : 0 ≤ cornerConst R := by
  have hR0 : 0 < R := by linarith
  have h1 : 0 < 1 / (64 * R) := by positivity
  have h2 : 1 / (64 * R) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  unfold cornerConst
  have := wk_nonneg (3 / (64 * R))
  have := rsConst_nonneg (s := 1) (ε := 1 / (64 * R)) (Kp := 1) (Km := 1) one_pos h1 h2
    zero_le_one zero_le_one
  have := d1Const_nonneg (p₁ := 2) (p₂ := 2) (θ := 1 / 2) (γ := 1 / (64 * R)) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h1
  positivity

/-! ### Simple functions as bounded test functions -/

section Strong

variable {α W E : Type*} [MeasurableSpace α] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace W] [BorelSpace W] [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] {μ : Measure α}

omit [NormedSpace ℝ W] [BorelSpace W] in
lemma isBddV_simpleFunc {ν₀ : W → ℝ} (hν₀ : ∀ w, ν₀ w = ‖w‖) (f : α →ₛ W) :
    IsBddV ν₀ (f : α → W) := by
  obtain ⟨M, hM⟩ := f.exists_forall_norm_le
  exact ⟨f.measurable, M, fun x => by rw [hν₀]; exact hM x⟩

omit [NormedSpace ℝ W] [MeasurableSpace W] [BorelSpace W] in
lemma isSlotNorm_norm {ν₀ : W → ℝ} (hν₀ : ∀ w, ν₀ w = ‖w‖) : IsSlotNorm ν₀ := fun w => by
  rw [hν₀]; exact norm_le_zero_iff

omit [NormedSpace ℝ W] [MeasurableSpace W] [BorelSpace W] in
lemma isSlotNorm_fin3 {ν : Fin 3 → W → ℝ} (hν0 : ∀ w, ν 0 w = ‖w‖) (hν1 : ∀ w, ν 1 w = ‖w‖)
    (hν2 : IsSlotNorm (ν 2)) : ∀ i, IsSlotNorm (ν i) := by
  intro i
  fin_cases i
  · exact isSlotNorm_norm hν0
  · exact isSlotNorm_norm hν1
  · exact hν2

end Strong

/-! ### From simple to measurable inputs, and `K = 0` -/

/-- A bound `X ≤ c K' Y` for every `K' > K` passes to `K' = K` (`Y < ∞`). -/
lemma ennreal_le_mul_of_forall_gt {X Y : ℝ≥0∞} {c K : ℝ} (hY : Y ≠ ⊤)
    (h : ∀ K' : ℝ, K < K' → X ≤ ENNReal.ofReal (c * K') * Y) :
    X ≤ ENNReal.ofReal (c * K) * Y := by
  have hlim : Tendsto (fun K' : ℝ => ENNReal.ofReal (c * K') * Y) (𝓝[>] K)
      (𝓝 (ENNReal.ofReal (c * K) * Y)) := by
    have h1 : Tendsto (fun K' : ℝ => ENNReal.ofReal (c * K')) (𝓝[>] K)
        (𝓝 (ENNReal.ofReal (c * K))) :=
      ((ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)).tendsto K).mono_left
        nhdsWithin_le_nhds
    exact ENNReal.Tendsto.mul_const h1 (Or.inr hY)
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun K' hK' => h K' hK')

section Strong2

variable {α W E : Type*} [MeasurableSpace α] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace W] [BorelSpace W] [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] {μ : Measure α}

open Filter Topology in
/-- **R6c-I at the corner for measurable inputs** (Corollary (MB)): for measurable `f_i ∈ L²` and every
`K ≥ 0`, `‖T(f₁,f₂)‖_{L¹} ≤ 4 (cornerConst R) K ‖f₁‖_{L²} ‖f₂‖_{L²}`, under the continuity hypothesis
`hcont` of `T` along dominated pointwise simple approximations (for the model sums: dominated
convergence). -/
theorem eLpNorm_le_of_hullBound_corner [SigmaFinite μ] [TopologicalSpace.SeparableSpace W]
    {ν : Fin 3 → W → ℝ} {Λ : (Fin 3 → α → W) → ℝ} {K R : ℝ} {pr : E → W → ℂ}
    {T : (α → W) → (α → W) → α → E}
    (hν0 : ∀ w, ν 0 w = ‖w‖) (hν1 : ∀ w, ν 1 w = ‖w‖) (hν2 : IsSlotNorm (ν 2))
    (hR : 1 ≤ R) (hK : 0 ≤ K) (hsub : IsSubadditiveV ν Λ) (hsmall : IsSmallV μ ν Λ)
    (hpr : IsDualPairing (ν 2) pr)
    (hhull : ∀ β, InCornerNbhd R β → VHullBound μ ν Λ β K) (hdom : IsDominatedV μ ν pr T Λ)
    (hmeas : ∀ f₁ f₂, IsBddV (ν 0) f₁ → IsBddV (ν 1) f₂ → Measurable (T f₁ f₂))
    (hadd₁ : ∀ f f' g : α → W, IsBddV (ν 0) f → IsBddV (ν 0) f' → IsBddV (ν 1) g →
      T (f + f') g = T f g + T f' g)
    (hsmul₁ : ∀ (c : ℝ) (f g : α → W), IsBddV (ν 0) f → IsBddV (ν 1) g → T (c • f) g = c • T f g)
    (hadd₂ : ∀ f g g' : α → W, IsBddV (ν 0) f → IsBddV (ν 1) g → IsBddV (ν 1) g' →
      T f (g + g') = T f g + T f g')
    (hsmul₂ : ∀ (c : ℝ) (f g : α → W), IsBddV (ν 0) f → IsBddV (ν 1) g → T f (c • g) = c • T f g)
    (f₁ f₂ : α → W) (hm₁ : Measurable f₁) (hm₂ : Measurable f₂) (hf₁ : eLpNorm f₁ 2 μ < ∞)
    (hf₂ : eLpNorm f₂ 2 μ < ∞)
    (hcont : ∀ s₁ s₂ : ℕ → α →ₛ W, (∀ j x, ‖s₁ j x‖ ≤ 2 * ‖f₁ x‖) →
      (∀ j x, ‖s₂ j x‖ ≤ 2 * ‖f₂ x‖) → (∀ x, Tendsto (fun j => s₁ j x) atTop (𝓝 (f₁ x))) →
      (∀ x, Tendsto (fun j => s₂ j x) atTop (𝓝 (f₂ x))) →
      ∀ᵐ x ∂μ, Tendsto (fun j => T (s₁ j) (s₂ j) x) atTop (𝓝 (T f₁ f₂ x))) :
    eLpNorm (T f₁ f₂) 1 μ ≤
      ENNReal.ofReal (4 * cornerConst R * K) * eLpNorm f₁ 2 μ * eLpNorm f₂ 2 μ := by
  have hν := isSlotNorm_fin3 hν0 hν1 hν2
  have hR0 : 0 < R := by linarith
  have hδ0 : 0 < 1 / (64 * R) := by positivity
  have hδ2 : 1 / (64 * R) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hfin : eLpNorm f₁ 2 μ * eLpNorm f₂ 2 μ ≠ ⊤ := (ENNReal.mul_lt_top hf₁ hf₂).ne
  have hmain : ∀ K' : ℝ, K < K' → eLpNorm (T f₁ f₂) 1 μ ≤
      ENNReal.ofReal (4 * cornerConst R * K') * (eLpNorm f₁ 2 μ * eLpNorm f₂ 2 μ) := by
    intro K' hK'
    have hK'0 : 0 < K' := lt_of_le_of_lt hK hK'
    have hhull' : ∀ β, InCornerNbhd R β → VHullBound μ ν Λ β K' := fun β hβ =>
      (hhull β hβ).mono hK'.le
    have hKw : 0 ≤ K' * wk (3 / (64 * R)) * rsConst (1 / 1) (1 / (64 * R)) 1 1 :=
      mul_nonneg (mul_nonneg hK'0.le (wk_nonneg _))
        (rsConst_nonneg (by norm_num) hδ0 (by
          rw [div_one, div_lt_one (by positivity)]
          linarith) zero_le_one zero_le_one)
    have hRS := hRS_of_hullBound (p₁ := 2) (p₂ := 2) (r := 1) (δ₀ := 1 / (64 * R))
      (ε := 1 / (64 * R)) (κ := 1 / (16 * R)) (m := 3 / (64 * R)) hν hK'0 hsub hsmall hpr hhull'
      hdom hmeas (by norm_num) hδ0 (fun t ht => by
        have ht' : |t| < 1 / (32 * R) := by
          have : 2 * (1 / (64 * R)) = 1 / (32 * R) := by field_simp; ring
          rwa [this] at ht
        refine ⟨weakPoint_corner hR ht' (by rw [abs_of_pos hδ0]), ?_⟩
        have := weakPoint_corner hR ht' (e := -(1 / (64 * R))) (by rw [abs_neg, abs_of_pos hδ0])
        rwa [← sub_eq_add_neg] at this)
    have hbdd : ∀ g : α →ₛ W, IsBddV (ν 0) (g : α → W) := fun g => isBddV_simpleFunc hν0 g
    have hbdd1 : ∀ g : α →ₛ W, IsBddV (ν 1) (g : α → W) := fun g => isBddV_simpleFunc hν1 g
    have key := eLpNorm_le_of_restrictedStrong_of_continuous (T := T) (μ := μ) (ν := μ)
      (p₁ := 2) (p₂ := 2) (r := 1) (δ₀ := 1 / (64 * R))
      (K := K' * wk (3 / (64 * R)) * rsConst (1 / 1) (1 / (64 * R)) 1 1) (by norm_num)
      (by norm_num) (by norm_num) le_rfl (by norm_num) hδ0 hδ2 hKw
      (fun f f' g => by
        rw [SimpleFunc.coe_add]; exact hadd₁ f f' g (hbdd f) (hbdd f') (hbdd1 g))
      (fun c f g => by
        rw [SimpleFunc.coe_smul]; exact hsmul₁ c f g (hbdd f) (hbdd1 g))
      (fun f g g' => by
        rw [SimpleFunc.coe_add]; exact hadd₂ f g g' (hbdd f) (hbdd1 g) (hbdd1 g'))
      (fun c f g => by
        rw [SimpleFunc.coe_smul]; exact hsmul₂ c f g (hbdd f) (hbdd1 g))
      (fun t ht E₁ E₂ hE₁ hE₂ hE₁f hE₂f g₁ g₂ hg₁ hg₂ =>
        hRS t ht E₁ E₂ hE₁ hE₂ hE₁f hE₂f g₁ g₂ g₁.measurable g₂.measurable
          (fun x => by rw [hν0]; exact hg₁ x) (fun x => by rw [hν1]; exact hg₂ x))
      f₁ f₂ hm₁ hm₂ (by simpa using hf₁) (by simpa using hf₂) hcont
    simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat, strongConstI_one] at key
    refine key.trans (le_of_eq ?_)
    rw [mul_assoc]
    congr 2
    unfold cornerConst
    norm_num
    ring
  have := ennreal_le_mul_of_forall_gt (c := 4 * cornerConst R) hfin hmain
  rwa [← mul_assoc] at this

end Strong2

/-! ### (I4) The pairing -/

section Pairing

variable {α W E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}

/-- **(I4) Pairing bound.**  `‖∫ pr (F x) (g x) dμ‖ₑ ≤ ‖F‖_{L¹(E)} · ‖ν₂ ∘ g‖_{L^∞}`, from the pairing bound
`‖pr e v‖ ≤ ‖e‖ ν₂ v` (Hölder; `IsDualPairing.norm_le`). -/
theorem enorm_integral_pair_le [AddCommMonoid W] [MeasurableSpace W] {ν₂ : W → ℝ} {pr : E → W → ℂ}
    (hpr : IsDualPairing ν₂ pr) {F : α → E} (hF : AEStronglyMeasurable F μ) {g : α → W}
    (hg : AEStronglyMeasurable (fun x => ν₂ (g x)) μ) :
    ‖∫ x, pr (F x) (g x) ∂μ‖ₑ ≤ eLpNorm F 1 μ * eLpNorm (fun x => ν₂ (g x)) ⊤ μ := by
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [eLpNorm_one_eq_lintegral_enorm hF, eLpNorm_exponent_top hg,
    ← lintegral_mul_const'' _ hF.enorm]
  refine lintegral_mono_ae ?_
  filter_upwards [enorm_ae_le_eLpNormEssSup (fun x => ν₂ (g x)) μ] with x hx
  have h1 : ‖pr (F x) (g x)‖ ≤ ‖F x‖ * ν₂ (g x) := hpr.norm_le _ _
  calc ‖pr (F x) (g x)‖ₑ = ENNReal.ofReal ‖pr (F x) (g x)‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (‖F x‖ * ν₂ (g x)) := ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal ‖F x‖ * ENNReal.ofReal (ν₂ (g x)) := ENNReal.ofReal_mul (norm_nonneg _)
    _ ≤ ‖F x‖ₑ * eLpNormEssSup (fun x => ν₂ (g x)) μ := by
        gcongr
        · exact (ofReal_norm _).le
        · refine le_trans ?_ hx
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (le_trans (le_abs_self _) (by simp))

end Pairing

/-! ### The abstract V17 statement -/

section V17

variable {α W E : Type*} [MeasurableSpace α] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace W] [BorelSpace W] [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] {μ : Measure α}

open Filter Topology in
/-- **V17, abstract form (I1-I4 combined).**  `VHullBound` with constant `K ≥ 0` on the corner region
`𝒩_R` (`R ≥ 1`) for an `IsSubadditiveV`, `IsSmallV` form `Λ`, an operator `T` dominated by `Λ` through the
duality pairing, bilinear and continuous as above, implies
`‖∫ pr (T F₁ F₂ x) (F₃ x) dμ‖ₑ ≤ (4 cornerConst R · K) ‖F₁‖_{L²} ‖F₂‖_{L²} ‖ν₂ ∘ F₃‖_{L^∞}`
for measurable `F_i` with `F₁, F₂ ∈ L²` (norms of `W`, i.e. `ν₀ = ν₁ = ‖·‖`) and `ν₂ ∘ F₃` a.e. strongly
measurable.  The constant `C₁ = 4 cornerConst R` depends on `R` only and the bound is linear in `K`. -/
theorem v17_abstract [SigmaFinite μ] [TopologicalSpace.SeparableSpace W]
    {ν : Fin 3 → W → ℝ} {Λ : (Fin 3 → α → W) → ℝ} {K R : ℝ} {pr : E → W → ℂ}
    {T : (α → W) → (α → W) → α → E}
    (hν0 : ∀ w, ν 0 w = ‖w‖) (hν1 : ∀ w, ν 1 w = ‖w‖) (hν2 : IsSlotNorm (ν 2))
    (hR : 1 ≤ R) (hK : 0 ≤ K) (hsub : IsSubadditiveV ν Λ) (hsmall : IsSmallV μ ν Λ)
    (hpr : IsDualPairing (ν 2) pr)
    (hhull : ∀ β, InCornerNbhd R β → VHullBound μ ν Λ β K) (hdom : IsDominatedV μ ν pr T Λ)
    (hmeas : ∀ f₁ f₂, IsBddV (ν 0) f₁ → IsBddV (ν 1) f₂ → Measurable (T f₁ f₂))
    (hadd₁ : ∀ f f' g : α → W, IsBddV (ν 0) f → IsBddV (ν 0) f' → IsBddV (ν 1) g →
      T (f + f') g = T f g + T f' g)
    (hsmul₁ : ∀ (c : ℝ) (f g : α → W), IsBddV (ν 0) f → IsBddV (ν 1) g → T (c • f) g = c • T f g)
    (hadd₂ : ∀ f g g' : α → W, IsBddV (ν 0) f → IsBddV (ν 1) g → IsBddV (ν 1) g' →
      T f (g + g') = T f g + T f g')
    (hsmul₂ : ∀ (c : ℝ) (f g : α → W), IsBddV (ν 0) f → IsBddV (ν 1) g → T f (c • g) = c • T f g)
    (F₁ F₂ F₃ : α → W) (hm₁ : Measurable F₁) (hm₂ : Measurable F₂) (hF₁ : eLpNorm F₁ 2 μ < ∞)
    (hF₂ : eLpNorm F₂ 2 μ < ∞) (hF₃ : AEStronglyMeasurable (fun x => ν 2 (F₃ x)) μ)
    (hcont : ∀ s₁ s₂ : ℕ → α →ₛ W, (∀ j x, ‖s₁ j x‖ ≤ 2 * ‖F₁ x‖) →
      (∀ j x, ‖s₂ j x‖ ≤ 2 * ‖F₂ x‖) → (∀ x, Tendsto (fun j => s₁ j x) atTop (𝓝 (F₁ x))) →
      (∀ x, Tendsto (fun j => s₂ j x) atTop (𝓝 (F₂ x))) →
      ∀ᵐ x ∂μ, Tendsto (fun j => T (s₁ j) (s₂ j) x) atTop (𝓝 (T F₁ F₂ x))) :
    ‖∫ x, pr (T F₁ F₂ x) (F₃ x) ∂μ‖ₑ ≤
      ENNReal.ofReal (4 * cornerConst R * K) * eLpNorm F₁ 2 μ * eLpNorm F₂ 2 μ *
        eLpNorm (fun x => ν 2 (F₃ x)) ⊤ μ := by
  have hL1 := eLpNorm_le_of_hullBound_corner hν0 hν1 hν2 hR hK hsub hsmall hpr hhull hdom hmeas
    hadd₁ hsmul₁ hadd₂ hsmul₂ F₁ F₂ hm₁ hm₂ hF₁ hF₂ hcont
  have hfin : ENNReal.ofReal (4 * cornerConst R * K) * eLpNorm F₁ 2 μ * eLpNorm F₂ 2 μ < ∞ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF₁) hF₂
  have hTm : AEStronglyMeasurable (T F₁ F₂) μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top (hL1.trans_lt hfin).ne
  exact (enorm_integral_pair_le hpr hTm hF₃).trans (mul_le_mul_left hL1 _)

end V17

end PrimeBHT.TimeFrequency.X2.Interp
