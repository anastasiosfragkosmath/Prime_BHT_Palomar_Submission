module

public import PrimeBHT.TimeFrequency.X2.Interp.FormV
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# X2, node V17 (I2): R6b for an `E`-valued bilinear operator, with an abstract exponent region

Vector-valued COPY-ADAPT of `PrimeBHT/TimeFrequency/Interp/Restricted/Operator.lean` (R6b: `weak_core`,
`weak_type_of_hullBound`, `eLpNorm_le_of_hullBound`, `hRS_of_hullBound`); the X1 files are untouched and the
layer-cake engine `Interpolate.lean` (`eLpNorm_le_of_weak_pair`, `rsConst`) is reused unchanged.  Source of
the mathematics: `docs/audits/X2-V16B-route-check.md` §1.1.  The slot setting is that of `FormV.lean`
(one carrier `W`, one norm function `ν i` per slot).

## Setting

* `T : (α → W) → (α → W) → α → E` is the (bilinear) operator, with values in a normed group `E`
  (X2: `X_u'`); `pr : E → W → ℂ` is the duality pairing of `E` with the third slot (X2: the normalized
  pairing `yPair`).  `IsDualPairing ν₂ pr` says: `pr 0 v = 0`, `‖pr e v - pr d v‖ ≤ ‖e - d‖ ν₂ v` (Hölder, with
  additivity in `e` it is `|⟨e - d, v⟩| ≤ ‖e - d‖_{X_u'} ν₂(v)`) and near-norming: for `θ < 1` every `e`
  has a `v` with `ν₂ v ≤ 1` and `θ ‖e‖ ≤ Re ⟨e, v⟩`.  For finite-dimensional dual pairs `X_u' = (X_u)*` this
  is exact norming (Hölder's equality case), which is left to the instantiation.
* `IsDominatedV μ ν pr T Λ`: `‖∫ pr (T f₁ f₂ x) (h x) dμ‖ ≤ Λ(f₁, f₂, h)` for bounded measurable `f₁ f₂ h`
  (the pairing `|⟨B(f₁,f₂), h⟩| ≤ Λ(f₁,f₂,h)`).
* The exponent region is an abstract predicate `Reg : (Fin 3 → ℝ) → Prop` on exponent triples `β`
  (X2: `InCornerNbhd R`), and the hull hypothesis is `hhull : ∀ β, Reg β → VHullBound μ ν Λ β K` with ONE
  constant `K` (so every constant below is linear in `K`).
* `WeakPoint Reg κ m a₁ a₂`: the exponent `a = (a₁, a₂)` is admissible for the weak-type bound, i.e. `α(a)`,
  `α(a - κ e₁)`, `α(a - κ e₂)` lie in `Reg`, and the exponents of the two sub-case points have margin `m`:
  `m ≤ α(b)_i`.  These are exactly the points at which the hull bound is evaluated in `weak_core`.

## Main results

* `exists_test_of_level` (the selection lemma): for measurable `F : α → E` with `t < ‖F‖ ≤ N` on `G`, and
  `0 ≤ θ < 1`, a MEASURABLE `h : α → W` with `ν₂ ∘ h ≤ 1_G` and `θ t μ(G) ≤ ‖∫ pr (F x) (h x)‖`.  The vector
  `h(x)` is a norming vector for a dense-sequence approximation `d n` of `F x` (first index with
  `‖F x - d n‖ < ε`); `h` takes countably many values, hence is measurable.  `E` is only assumed second
  countable (the brief's "finite net" is replaced by a countable dense sequence; finite-dimensional
  spaces are covered, and no compactness and no upper bound `N` is needed).
* `weak_core_of_pair`, `weak_core`: `t μ(G)^{a₁+a₂} ≤ K (max 2 (1/(1-2^{-m}))) μ(E₁)^{a₁} μ(E₂)^{a₂}`.
* `weak_type_of_hullBound` (RWT, in `ℝ≥0∞`), `eLpNorm_le_of_weak_pair_lin` (the K-homogeneous layer-cake
  interpolation), `eLpNorm_le_of_hullBound` (RS), `hRS_of_hullBound` (the hypothesis `hRS` of R6c-I).

## Corrections to the route check §1.1

1. **Sub-case 2** is as in the audit: `b = a - κ e₂` if `|G| < |E₂|` (`a - κ e₁` if `|G| < |E₁|`), `κ ≥ 0`:
   R6a at `b` (margin `m ≤ α(b)_i`) gives `t|G|^{a₁+a₂-κ} ≤ K'|E₁|^{a₁}|E₂|^{a₂-κ}`, and
   `|G|^κ ≤ |E₂|^κ`, i.e. `t|G|^{a₁+a₂} ≤ K'|E₁|^{a₁}|E₂|^{a₂-κ}|G|^κ ≤ K'|E₁|^{a₁}|E₂|^{a₂}`
   (VERIFIED; only `κ ≥ 0` is used).  The point `b` must be in `Reg` and have all exponents `≥ m > 0`
   (the structure `WeakPoint`); for `Reg = 𝒩_R` and the audit's `δ₀ = ε = 1/(64R)`, `κ = 1/(16R)` this is
   checked in `StrongV.lean` (`weakPoint_corner`).
2. **Linearity in `K`.** X1's `eLpNorm_le_of_weak_pair` has the constant `rsConst s ε Kp Km` with
   `Kp^{1/(s+ε)}`, `Km^{1/(s-ε)}`: NOT linear in `K` (the crossing point `L` is `K`-independent).  The audit's
   "`C₁` linear in `K`" is true but needs the crossing point `L ~ K`; here it is obtained by homogeneity
   (apply the unscaled lemma to `K⁻¹ ‖F‖`): `eLpNorm_le_of_weak_pair_lin`, constant `K · rsConst s ε 1 1`.
3. `K = 0` is excluded in the interpolation steps (`0 < K`); the final theorem of `StrongV.lean` recovers
   `K = 0` by `VHullBound.mono` and a limit.
-/

@[expose] public section

namespace PrimeBHT.TimeFrequency.X2.Interp

open MeasureTheory Function Finset Filter Topology
open scoped ENNReal ComplexConjugate
open PrimeBHT.TimeFrequency.Interp.Restricted (alphaOf forall_vec3 prod_vec3 arith_sub1 arith_sub2
  ofReal_mul_rpow_mul_rpow rsConst rsConst_nonneg eLpNorm_le_of_weak_pair)

variable {α W E : Type*} [MeasurableSpace α] [MeasurableSpace W] [AddCommMonoid W]
  [NormedAddCommGroup E] {μ : Measure α}

/-! ### The duality pairing and the measurable selection of norming vectors -/

/-- The duality pairing between the output space `E` (X2: `X_u'`) and the third slot (norm function
`ν₂`; X2: `X_u`). -/
structure IsDualPairing (ν₂ : W → ℝ) (pr : E → W → ℂ) : Prop where
  zero_left : ∀ v, pr 0 v = 0
  lipschitz : ∀ e d v, ‖pr e v - pr d v‖ ≤ ‖e - d‖ * ν₂ v
  norming : ∀ e : E, ∀ θ : ℝ, θ < 1 → ∃ v : W, ν₂ v ≤ 1 ∧ θ * ‖e‖ ≤ (pr e v).re

omit [MeasurableSpace α] [MeasurableSpace W] in
lemma IsDualPairing.right_zero {ν₂ : W → ℝ} (hν : IsSlotNorm ν₂) {pr : E → W → ℂ}
    (hpr : IsDualPairing ν₂ pr) (e : E) : pr e 0 = 0 := by
  have h := hpr.lipschitz e 0 0
  have h0 : ν₂ 0 ≤ 0 := (hν 0).2 rfl
  have : ‖e - 0‖ * ν₂ 0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) h0
  have h2 : ‖pr e 0 - pr 0 0‖ ≤ 0 := h.trans this
  rw [hpr.zero_left, sub_zero] at h2
  exact norm_le_zero_iff.1 h2

omit [MeasurableSpace α] [MeasurableSpace W] [AddCommMonoid W] in
lemma IsDualPairing.norm_le {ν₂ : W → ℝ} {pr : E → W → ℂ} (hpr : IsDualPairing ν₂ pr) (e : E)
    (v : W) : ‖pr e v‖ ≤ ‖e‖ * ν₂ v := by
  have h := hpr.lipschitz e 0 v
  rwa [hpr.zero_left, sub_zero, sub_zero] at h

omit [MeasurableSpace α] [MeasurableSpace W] [AddCommMonoid W] in
lemma IsDualPairing.continuous_left {ν₂ : W → ℝ} {pr : E → W → ℂ} (hpr : IsDualPairing ν₂ pr)
    (v : W) : Continuous fun e => pr e v := by
  have : LipschitzWith (ν₂ v).toNNReal fun e => pr e v := by
    refine LipschitzWith.of_dist_le_mul fun e d => ?_
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖pr e v - pr d v‖ ≤ ‖e - d‖ * ν₂ v := hpr.lipschitz e d v
      _ ≤ ‖e - d‖ * ((ν₂ v).toNNReal : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.le_coe_toNNReal _) (norm_nonneg _)
      _ = _ := mul_comm _ _
  exact this.continuous

open Classical in
/-- **Measurable near-norming test function.**  Let `F : α → E` be measurable, `t < ‖F x‖ ≤ N` on a
measurable set `G` of finite measure, `0 ≤ θ < 1`.  Then there is a measurable `h : α → W` with
`ν₂ ∘ h ≤ 1_G` and `θ t μ(G) ≤ ‖∫ pr (F x) (h x) dμ‖`.  The selection is by a dense sequence `d` of `E`
(first index with `‖F x - d n‖ < ε`) and a norming vector `v n` for each `d n`, so `h` is measurable
(countably many values); `E` is only assumed second countable (finite-dimensional spaces qualify). -/
theorem exists_test_of_level [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {ν₂ : W → ℝ} (hν₂ : IsSlotNorm ν₂) {pr : E → W → ℂ} (hpr : IsDualPairing ν₂ pr)
    {F : α → E} (hF : Measurable F) {t N θ : ℝ} (ht : 0 < t) (hθ0 : 0 ≤ θ)
    (hθ : θ < 1) {G : Set α} (hG : MeasurableSet G) (hGf : μ G < ∞)
    (hlow : ∀ x ∈ G, t < ‖F x‖) (hup : ∀ x ∈ G, ‖F x‖ ≤ N) :
    ∃ h : α → W, Measurable h ∧ VDominatedBy ν₂ G h ∧
      θ * t * (μ G).toReal ≤ ‖∫ x, pr (F x) (h x) ∂μ‖ := by
  set θ₀ : ℝ := (1 + θ) / 2 with hθ₀
  have hθ₀1 : θ₀ < 1 := by rw [hθ₀]; linarith
  set ε : ℝ := (1 - θ) * t / 4 with hε
  have hε0 : 0 < ε := by
    rw [hε]
    have : 0 < 1 - θ := by linarith
    positivity
  -- dense sequence and norming vectors
  have : Nonempty E := ⟨0⟩
  set d : ℕ → E := TopologicalSpace.denseSeq E with hd
  have hdense : DenseRange d := TopologicalSpace.denseRange_denseSeq E
  choose v hv1 hv2 using fun n => hpr.norming (d n) θ₀ hθ₀1
  have hex : ∀ x, ∃ n, ‖F x - d n‖ < ε := by
    intro x
    obtain ⟨n, hn⟩ := Metric.denseRange_iff.1 hdense (F x) ε hε0
    exact ⟨n, by rwa [dist_eq_norm] at hn⟩
  set idx : α → ℕ := fun x => Nat.find (hex x) with hidx
  have hidxm : Measurable idx := by
    refine measurable_find hex fun k => ?_
    exact measurableSet_lt (measurable_norm.comp (hF.sub_const (d k))) measurable_const
  have hidx_lt : ∀ x, ‖F x - d (idx x)‖ < ε := fun x => Nat.find_spec (hex x)
  set h : α → W := G.indicator (fun x => v (idx x)) with hh
  have hhm : Measurable h := (measurable_from_nat (f := v) |>.comp hidxm).indicator hG
  refine ⟨h, hhm, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ G
    · simp only [hh, Set.indicator_of_mem hx]
      exact hv1 _
    · simp only [hh, Set.indicator_of_notMem hx]
      exact (hν₂ 0).2 rfl
  · -- the integrand
    set ψ : α → ℂ := fun x => pr (F x) (v (idx x)) with hψ
    have hψm : Measurable ψ := by
      have : Measurable fun p : E × ℕ => pr p.1 (v p.2) :=
        measurable_from_prod_countable_left fun n => (hpr.continuous_left (v n)).measurable
      exact this.comp (hF.prodMk hidxm)
    have hint_eq : (fun x => pr (F x) (h x)) = G.indicator ψ := by
      funext x
      by_cases hx : x ∈ G
      · simp [hh, hψ, Set.indicator_of_mem hx]
      · simp [hh, Set.indicator_of_notMem hx, hpr.right_zero hν₂]
    -- pointwise lower bound on `G`
    have hlowψ : ∀ x ∈ G, θ * t ≤ (ψ x).re := by
      intro x hx
      have h1 := hpr.lipschitz (F x) (d (idx x)) (v (idx x))
      have h2 : ‖pr (F x) (v (idx x)) - pr (d (idx x)) (v (idx x))‖ ≤ ε := by
        refine h1.trans ?_
        calc ‖F x - d (idx x)‖ * ν₂ (v (idx x)) ≤ ‖F x - d (idx x)‖ * 1 :=
              mul_le_mul_of_nonneg_left (hv1 _) (norm_nonneg _)
          _ ≤ ε := by rw [mul_one]; exact (hidx_lt x).le
      have h3 : |(ψ x).re - (pr (d (idx x)) (v (idx x))).re| ≤ ε := by
        have := Complex.abs_re_le_norm (pr (F x) (v (idx x)) - pr (d (idx x)) (v (idx x)))
        rw [Complex.sub_re] at this
        exact this.trans h2
      have h4 : ‖F x‖ - ‖d (idx x)‖ ≤ ε := (norm_sub_norm_le _ _).trans (hidx_lt x).le
      have h5 := hv2 (idx x)
      have hFt := hlow x hx
      have h6 : (1 - θ) * t ≤ (1 - θ) * ‖F x‖ :=
        mul_le_mul_of_nonneg_left hFt.le (by linarith)
      have hθ₀0 : 0 ≤ θ₀ := by rw [hθ₀]; linarith
      have h7 : θ₀ * ‖d (idx x)‖ ≥ θ₀ * (‖F x‖ - ε) := by
        apply mul_le_mul_of_nonneg_left _ hθ₀0
        linarith
      have h8 : θ₀ * ε ≤ ε := by nlinarith
      have h9 : ‖F x‖ * θ ≥ t * θ := mul_le_mul_of_nonneg_right hFt.le hθ0
      have := abs_le.1 h3
      rw [hθ₀, hε] at *
      nlinarith
    have hψbound : ∀ x ∈ G, ‖ψ x‖ ≤ N := by
      intro x hx
      refine (hpr.norm_le _ _).trans ?_
      calc ‖F x‖ * ν₂ (v (idx x)) ≤ ‖F x‖ * 1 :=
            mul_le_mul_of_nonneg_left (hv1 _) (norm_nonneg _)
        _ ≤ N := by rw [mul_one]; exact hup x hx
    have hψint : IntegrableOn ψ G μ :=
      Measure.integrableOn_of_bounded (M := N) hGf.ne hψm.aestronglyMeasurable
        (ae_restrict_of_forall_mem hG hψbound)
    have hreint : IntegrableOn (fun x => (ψ x).re) G μ := hψint.re
    rw [hint_eq, integral_indicator hG]
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    refine le_trans ?_ (le_abs_self _)
    have hre : ∫ x in G, (ψ x).re ∂μ = (∫ x in G, ψ x ∂μ).re := by
      have := integral_re (μ := μ.restrict G) (f := ψ) hψint
      simpa using this
    rw [← hre]
    have := setIntegral_ge_of_const_le_real hG hGf.ne hlowψ hreint
    simpa [Measure.real] using this

/-! ### Exponents, constants, the admissible points -/

/-- `α(a₁, a₂, ·)` components. -/
lemma alphaOf_zero (a₁ a₂ : ℝ) : alphaOf a₁ a₂ 0 = a₁ := rfl
lemma alphaOf_one (a₁ a₂ : ℝ) : alphaOf a₁ a₂ 1 = a₂ := rfl

/-- `a = (a₁, a₂)` is an admissible exponent for the weak-type bound: `α(a)`, `α(a - κ e₁)` and
`α(a - κ e₂)` lie in the region `Reg`, and the exponents of the sub-case points `α(a - κ e₁)`,
`α(a - κ e₂)` are all `≥ m > 0` (`0 ≤ κ`).  These are exactly the points at which `weak_core` evaluates the
hull bound (route check §1.1: sub-case 1 at `α(a)`, sub-case 2 at `b = a - κ e₂` or `b = a - κ e₁`). -/
structure WeakPoint (Reg : (Fin 3 → ℝ) → Prop) (κ m a₁ a₂ : ℝ) : Prop where
  kappa_nonneg : 0 ≤ κ
  m_pos : 0 < m
  at_a : Reg (alphaOf a₁ a₂)
  at_b₁ : Reg (alphaOf (a₁ - κ) a₂)
  at_b₂ : Reg (alphaOf a₁ (a₂ - κ))
  margin₁ : ∀ i, m ≤ alphaOf (a₁ - κ) a₂ i
  margin₂ : ∀ i, m ≤ alphaOf a₁ (a₂ - κ) i

lemma WeakPoint.a₁_pos {Reg : (Fin 3 → ℝ) → Prop} {κ m a₁ a₂ : ℝ} (h : WeakPoint Reg κ m a₁ a₂) :
    0 < a₁ := by
  have := h.margin₂ 0
  have := h.m_pos
  rw [alphaOf_zero] at *
  linarith

lemma WeakPoint.a₂_pos {Reg : (Fin 3 → ℝ) → Prop} {κ m a₁ a₂ : ℝ} (h : WeakPoint Reg κ m a₁ a₂) :
    0 < a₂ := by
  have := h.margin₁ 1
  have := h.m_pos
  rw [alphaOf_one] at *
  linarith

/-- The constant of the restricted-type step: `max 2 (1/(1 - 2^{-m}))` (sub-case 1 gives `2K`, sub-case 2
gives `K/(1 - 2^{-m})`). -/
noncomputable def wk (m : ℝ) : ℝ := max 2 (1 / (1 - (2 : ℝ) ^ (-m)))

lemma two_le_wk (m : ℝ) : 2 ≤ wk m := le_max_left _ _

lemma wk_nonneg (m : ℝ) : 0 ≤ wk m := (by norm_num : (0 : ℝ) ≤ 2).trans (two_le_wk m)

lemma div_le_mul_wk {K : ℝ} (hK : 0 ≤ K) {m : ℝ} :
    K / (1 - (2 : ℝ) ^ (-m)) ≤ K * wk m := by
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hK

omit [MeasurableSpace α] [MeasurableSpace W] [AddCommMonoid W] in
lemma vdom_vec3 {ν : Fin 3 → W → ℝ} {E₁ E₂ E₃ : Set α} {f₁ f₂ f₃ : α → W}
    (h₁ : VDominatedBy (ν 0) E₁ f₁) (h₂ : VDominatedBy (ν 1) E₂ f₂)
    (h₃ : VDominatedBy (ν 2) E₃ f₃) :
    ∀ i, VDominatedBy (ν i) (![E₁, E₂, E₃] i) (![f₁, f₂, f₃] i) := by
  intro i
  fin_cases i
  · exact h₁
  · exact h₂
  · exact h₃

omit [MeasurableSpace α] [MeasurableSpace W] [AddCommMonoid W] [NormedAddCommGroup E] in
lemma real_le_of_forall_lt_mul_le {X Y : ℝ} (hY : 0 ≤ Y)
    (h : ∀ θ : ℝ, 0 < θ → θ < 1 → θ * X ≤ Y) : X ≤ Y := by
  by_contra hlt
  push Not at hlt
  have hX : 0 < X := lt_of_le_of_lt hY hlt
  have hθ0 : 0 < (X + Y) / (2 * X) := by positivity
  have hθ1 : (X + Y) / (2 * X) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have := h _ hθ0 hθ1
  have h2 : (X + Y) / (2 * X) * X = (X + Y) / 2 := by field_simp
  rw [h2] at this
  linarith

/-! ### The core of (RWT) -/

/-- Core of (RWT) once a test function is available at every sub-level set (`hpair`): the real-valued
weak-type bound `t μ(G)^{a₁+a₂} ≤ K · wk m · μ(E₁)^{a₁} μ(E₂)^{a₂}` for a set `G` of finite measure. -/
theorem weak_core_of_pair {ν : Fin 3 → W → ℝ} {Λ : (Fin 3 → α → W) → ℝ} {K : ℝ}
    (hν : ∀ i, IsSlotNorm (ν i)) (hK : 0 ≤ K) (hsub : IsSubadditiveV ν Λ)
    (hsmall : IsSmallV μ ν Λ) {Reg : (Fin 3 → ℝ) → Prop}
    (hhull : ∀ β, Reg β → VHullBound μ ν Λ β K) {κ m a₁ a₂ : ℝ} (ha : WeakPoint Reg κ m a₁ a₂)
    {E₁ E₂ : Set α} (hE₁m : MeasurableSet E₁) (hE₂m : MeasurableSet E₂) (hE₁f : μ E₁ < ∞)
    (hE₂f : μ E₂ < ∞) {f₁ f₂ : α → W} (hf₁m : Measurable f₁) (hf₂m : Measurable f₂)
    (hf₁ : VDominatedBy (ν 0) E₁ f₁) (hf₂ : VDominatedBy (ν 1) E₂ f₂) {t : ℝ} (ht : 0 < t)
    {G : Set α} (hGm : MeasurableSet G) (hGf : μ G < ∞)
    (hpair : ∀ G' : Set α, MeasurableSet G' → G' ⊆ G → ∃ h : α → W, Measurable h ∧
      VDominatedBy (ν 2) G' h ∧ t * (μ G').toReal ≤ Λ ![f₁, f₂, h]) :
    t * (μ G).toReal ^ (a₁ + a₂) ≤
      K * wk m * ((μ E₁).toReal ^ a₁ * (μ E₂).toReal ^ a₂) := by
  have hκ := ha.kappa_nonneg
  have hm := ha.m_pos
  have ha1 := ha.a₁_pos
  have ha2 := ha.a₂_pos
  have hs : 0 < a₁ + a₂ := by linarith
  have hW0 : 0 ≤ K * wk m := mul_nonneg hK (wk_nonneg m)
  have hP0 : 0 ≤ (μ E₁).toReal ^ a₁ * (μ E₂).toReal ^ a₂ :=
    mul_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  obtain ⟨A, hA, hsm⟩ := hsmall
  have hm3 : ∀ G : Set α, MeasurableSet G → ∀ i, MeasurableSet (![E₁, E₂, G] i) := fun G hG =>
    forall_vec3 hE₁m hE₂m hG
  have hfin3 : ∀ G : Set α, μ G < ∞ → ∀ i, μ (![E₁, E₂, G] i) < ∞ := fun G hG =>
    forall_vec3 (P := fun S => μ S < ∞) hE₁f hE₂f hG
  by_cases hG0 : μ G = 0
  · rw [hG0, ENNReal.toReal_zero, Real.zero_rpow hs.ne', mul_zero]
    exact mul_nonneg hW0 hP0
  by_cases hE0 : μ E₁ = 0 ∨ μ E₂ = 0
  · exfalso
    obtain ⟨h, hm', hd, hle⟩ := hpair G hGm subset_rfl
    have hΛ := hsm ![f₁, f₂, h] ![E₁, E₂, G] (hm3 G hGm) (hfin3 G hGf)
      (forall_vec3 hf₁m hf₂m hm') (vdom_vec3 hf₁ hf₂ hd)
    have hprod : ∏ i, (μ (![E₁, E₂, G] i)).toReal = 0 := by
      rw [Fin.prod_univ_three]
      rcases hE0 with h0 | h0 <;> simp [h0]
    rw [hprod, mul_zero] at hΛ
    have h1 : (μ G).toReal ≤ 0 := by
      by_contra hcon
      have := mul_pos ht (not_le.1 hcon)
      linarith
    exact hG0 ((ENNReal.toReal_eq_zero_iff _).1 (le_antisymm h1 ENNReal.toReal_nonneg)
      |>.resolve_right hGf.ne)
  rw [not_or] at hE0
  have hx₁ : 0 < (μ E₁).toReal := ENNReal.toReal_pos hE0.1 hE₁f.ne
  have hx₂ : 0 < (μ E₂).toReal := ENNReal.toReal_pos hE0.2 hE₂f.ne
  have hg : 0 < (μ G).toReal := ENNReal.toReal_pos hG0 hGf.ne
  have hpos3 : ∀ i, 0 < μ (![E₁, E₂, G] i) :=
    forall_vec3 (P := fun S => 0 < μ S) (pos_iff_ne_zero.2 hE0.1) (pos_iff_ne_zero.2 hE0.2)
      (pos_iff_ne_zero.2 hG0)
  by_cases hlarge : μ E₁ ≤ μ G ∧ μ E₂ ≤ μ G
  · -- sub-case 1: `G` is a largest set
    have hmax : ∀ i, μ (![E₁, E₂, G] i) ≤ μ (![E₁, E₂, G] 2) := by
      intro i
      fin_cases i
      · exact hlarge.1
      · exact hlarge.2
      · exact le_rfl
    obtain ⟨Et, hEtm, hEtsub, hEt2, hbd⟩ :=
      hhull _ ha.at_a ![E₁, E₂, G] (hm3 G hGm) hpos3 (hfin3 G hGf) 2 hmax
    obtain ⟨h, hm', hd, hle⟩ := hpair Et hEtm hEtsub
    have hdom : ∀ i : Fin 3, i ≠ 2 → VDominatedBy (ν i) (![E₁, E₂, G] i) (![f₁, f₂, h] i) := by
      intro i hi
      fin_cases i
      · exact hf₁
      · exact hf₂
      · exact (hi rfl).elim
    have hΛ := hbd ![f₁, f₂, h] (forall_vec3 hf₁m hf₂m hm') hdom hd
    rw [prod_vec3] at hΛ
    have hEtfin : μ Et < ∞ := (measure_mono hEtsub).trans_lt hGf
    have hge : (μ G).toReal ≤ 2 * (μ Et).toReal := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hEtfin.ne) hEt2
      simpa [ENNReal.toReal_mul] using this
    have hmain : t * (μ G).toReal ≤
        2 * (K * ((μ E₁).toReal ^ a₁ * (μ E₂).toReal ^ a₂) *
          (μ G).toReal ^ (1 - a₁ - a₂)) := by
      calc t * (μ G).toReal ≤ t * (2 * (μ Et).toReal) :=
            mul_le_mul_of_nonneg_left hge ht.le
        _ = 2 * (t * (μ Et).toReal) := by ring
        _ ≤ 2 * (K * ((μ E₁).toReal ^ alphaOf a₁ a₂ 0 * (μ E₂).toReal ^ alphaOf a₁ a₂ 1 *
              (μ G).toReal ^ alphaOf a₁ a₂ 2)) :=
            mul_le_mul_of_nonneg_left (hle.trans hΛ) (by norm_num)
        _ = _ := by simp [alphaOf]; ring
    have h1 := arith_sub1 hg hmain
    rw [show (1 : ℝ) - (1 - a₁ - a₂) = a₁ + a₂ by ring] at h1
    refine h1.trans ?_
    have h2 : 2 * K ≤ K * wk m := by
      have := mul_le_mul_of_nonneg_left (two_le_wk m) hK
      linarith
    calc 2 * (K * ((μ E₁).toReal ^ a₁ * (μ E₂).toReal ^ a₂))
        = (2 * K) * ((μ E₁).toReal ^ a₁ * (μ E₂).toReal ^ a₂) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 hP0
  · -- sub-case 2: some input set is larger than `G`
    have r6a : ∀ b₁ b₂ : ℝ, Reg (alphaOf b₁ b₂) → (∀ i, m ≤ alphaOf b₁ b₂ i) →
        t * (μ G).toReal ≤ K / (1 - (2 : ℝ) ^ (-m)) *
          ((μ E₁).toReal ^ b₁ * (μ E₂).toReal ^ b₂ * (μ G).toReal ^ (1 - b₁ - b₂)) := by
      intro b₁ b₂ hb hmb
      obtain ⟨h, hm', hd, hle⟩ := hpair G hGm subset_rfl
      have hΛ := restrictedType_of_hullBound hν hmb hm hK hsub ⟨A, hA, hsm⟩
        (hhull _ hb) (E := ![E₁, E₂, G]) (hm3 G hGm) (hfin3 G hGf) (h := ![f₁, f₂, h])
        (forall_vec3 hf₁m hf₂m hm') (vdom_vec3 hf₁ hf₂ hd)
      rw [prod_vec3] at hΛ
      refine hle.trans (hΛ.trans (le_of_eq ?_))
      simp [alphaOf]
    have hK' : 0 ≤ K / (1 - (2 : ℝ) ^ (-m)) := by
      have : (2 : ℝ) ^ (-m) < 1 := by
        rw [Real.rpow_neg (by norm_num)]
        exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) hm)
      exact div_nonneg hK (by linarith)
    rcases not_and_or.1 hlarge with h1 | h2
    · -- `μ G < μ E₁`: `b = a - κ e₁`
      have hgx : (μ G).toReal ≤ (μ E₁).toReal :=
        ENNReal.toReal_mono hE₁f.ne (not_le.1 h1).le
      have h3 := r6a (a₁ - κ) a₂ ha.at_b₁ ha.margin₁
      have h4 := arith_sub2 (x := (μ E₂).toReal) (y := (μ E₁).toReal) (p := a₂) (q := a₁ - κ)
        (e := 1 - (a₁ - κ) - a₂) (d := κ) hg hx₁ hx₂ hK' hκ hgx (by ring)
        (by
          refine h3.trans (le_of_eq ?_)
          ring)
      rw [show a₂ + (a₁ - κ) + κ = a₁ + a₂ by ring,
        show (a₁ - κ) + κ = a₁ by ring] at h4
      refine h4.trans ?_
      calc K / (1 - (2 : ℝ) ^ (-m)) * (μ E₂).toReal ^ a₂ * (μ E₁).toReal ^ a₁
          = K / (1 - (2 : ℝ) ^ (-m)) * ((μ E₁).toReal ^ a₁ * (μ E₂).toReal ^ a₂) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_mul_wk hK) hP0
    · -- `μ G < μ E₂`: `b = a - κ e₂`
      have hgx : (μ G).toReal ≤ (μ E₂).toReal :=
        ENNReal.toReal_mono hE₂f.ne (not_le.1 h2).le
      have h3 := r6a a₁ (a₂ - κ) ha.at_b₂ ha.margin₂
      have h4 := arith_sub2 (x := (μ E₁).toReal) (y := (μ E₂).toReal) (p := a₁) (q := a₂ - κ)
        (e := 1 - a₁ - (a₂ - κ)) (d := κ) hg hx₂ hx₁ hK' hκ hgx (by ring)
        (by
          refine h3.trans (le_of_eq ?_)
          ring)
      rw [show a₁ + (a₂ - κ) + κ = a₁ + a₂ by ring,
        show (a₂ - κ) + κ = a₂ by ring] at h4
      refine h4.trans ?_
      calc K / (1 - (2 : ℝ) ^ (-m)) * (μ E₁).toReal ^ a₁ * (μ E₂).toReal ^ a₂
          = K / (1 - (2 : ℝ) ^ (-m)) * ((μ E₁).toReal ^ a₁ * (μ E₂).toReal ^ a₂) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_mul_wk hK) hP0

/-- **Core of (RWT)** (route check §1.1, with the test function `h₃ = 1_{G'} v(x)`, `v(x)` a measurably
selected near-norming vector of `F(x) = B(f₁,f₂)(x)`): for a measurable `F : α → E` dominated in the
pairing sense by `Λ(f₁, f₂, ·)` (`hpair`) and a set `G` of finite measure on which `t < ‖F‖ ≤ N`,
`t μ(G)^{a₁+a₂} ≤ K · wk m · μ(E₁)^{a₁} μ(E₂)^{a₂}`. -/
theorem weak_core [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {ν : Fin 3 → W → ℝ} {Λ : (Fin 3 → α → W) → ℝ} {K : ℝ} {pr : E → W → ℂ}
    (hν : ∀ i, IsSlotNorm (ν i)) (hK : 0 ≤ K) (hsub : IsSubadditiveV ν Λ)
    (hsmall : IsSmallV μ ν Λ) (hpr : IsDualPairing (ν 2) pr) {Reg : (Fin 3 → ℝ) → Prop}
    (hhull : ∀ β, Reg β → VHullBound μ ν Λ β K) {κ m a₁ a₂ : ℝ} (ha : WeakPoint Reg κ m a₁ a₂)
    {E₁ E₂ : Set α} (hE₁m : MeasurableSet E₁) (hE₂m : MeasurableSet E₂) (hE₁f : μ E₁ < ∞)
    (hE₂f : μ E₂ < ∞) {f₁ f₂ : α → W} (hf₁m : Measurable f₁) (hf₂m : Measurable f₂)
    (hf₁ : VDominatedBy (ν 0) E₁ f₁) (hf₂ : VDominatedBy (ν 1) E₂ f₂) {F : α → E}
    (hF : Measurable F)
    (hpair : ∀ h : α → W, IsBddV (ν 2) h → ‖∫ x, pr (F x) (h x) ∂μ‖ ≤ Λ ![f₁, f₂, h])
    {t N : ℝ} (ht : 0 < t) {G : Set α} (hGm : MeasurableSet G) (hGf : μ G < ∞)
    (hlow : ∀ x ∈ G, t < ‖F x‖) (hup : ∀ x ∈ G, ‖F x‖ ≤ N) :
    t * (μ G).toReal ^ (a₁ + a₂) ≤
      K * wk m * ((μ E₁).toReal ^ a₁ * (μ E₂).toReal ^ a₂) := by
  have hP0 : 0 ≤ (μ E₁).toReal ^ a₁ * (μ E₂).toReal ^ a₂ :=
    mul_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  refine real_le_of_forall_lt_mul_le (mul_nonneg (mul_nonneg hK (wk_nonneg m)) hP0) ?_
  intro θ hθ0 hθ1
  have key := weak_core_of_pair (t := θ * t) hν hK hsub hsmall hhull ha hE₁m hE₂m hE₁f hE₂f hf₁m
    hf₂m hf₁ hf₂ (mul_pos hθ0 ht) hGm hGf (by
      intro G' hG' hsub'
      obtain ⟨h, hm, hd, hle⟩ := exists_test_of_level (μ := μ) (hν 2) hpr hF ht hθ0.le hθ1 hG'
        ((measure_mono hsub').trans_lt hGf) (fun x hx => hlow x (hsub' hx))
        (fun x hx => hup x (hsub' hx))
      exact ⟨h, hm, hd, hle.trans (hpair h (hd.isBddV hm))⟩)
  calc θ * (t * (μ G).toReal ^ (a₁ + a₂)) = θ * t * (μ G).toReal ^ (a₁ + a₂) := by ring
    _ ≤ _ := key

/-! ### (RWT) in `ℝ≥0∞` -/

/-- `‖∫ pr (T f₁ f₂ x) (h x) dμ‖ ≤ Λ(f₁, f₂, h)` for bounded measurable `f₁ f₂ h`: the pairing of the
operator output with the third slot is dominated by the form. -/
def IsDominatedV (μ : Measure α) (ν : Fin 3 → W → ℝ) (pr : E → W → ℂ)
    (T : (α → W) → (α → W) → α → E) (Λ : (Fin 3 → α → W) → ℝ) : Prop :=
  ∀ f₁ f₂ h : α → W, IsBddV (ν 0) f₁ → IsBddV (ν 1) f₂ → IsBddV (ν 2) h →
    ‖∫ x, pr (T f₁ f₂ x) (h x) ∂μ‖ ≤ Λ ![f₁, f₂, h]

/-- **(RWT)**: for an admissible exponent `a` (`WeakPoint`), bounded `f_i` with `ν_i ∘ f_i ≤ 1_{E_i}` and
every `t > 0`, `t μ{‖T(f₁,f₂)‖ > t}^{a₁+a₂} ≤ K · wk m · μ(E₁)^{a₁} μ(E₂)^{a₂}`. -/
theorem weak_type_of_hullBound [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [SigmaFinite μ] {ν : Fin 3 → W → ℝ} {Λ : (Fin 3 → α → W) → ℝ} {K : ℝ} {pr : E → W → ℂ}
    {T : (α → W) → (α → W) → α → E} (hν : ∀ i, IsSlotNorm (ν i)) (hK : 0 ≤ K)
    (hsub : IsSubadditiveV ν Λ) (hsmall : IsSmallV μ ν Λ) (hpr : IsDualPairing (ν 2) pr)
    {Reg : (Fin 3 → ℝ) → Prop} (hhull : ∀ β, Reg β → VHullBound μ ν Λ β K)
    (hdom : IsDominatedV μ ν pr T Λ)
    (hmeas : ∀ f₁ f₂, IsBddV (ν 0) f₁ → IsBddV (ν 1) f₂ → Measurable (T f₁ f₂))
    {κ m a₁ a₂ : ℝ} (ha : WeakPoint Reg κ m a₁ a₂) {E₁ E₂ : Set α} (hE₁m : MeasurableSet E₁)
    (hE₂m : MeasurableSet E₂) (hE₁f : μ E₁ < ∞) (hE₂f : μ E₂ < ∞) {f₁ f₂ : α → W}
    (hf₁m : Measurable f₁) (hf₂m : Measurable f₂) (hf₁ : VDominatedBy (ν 0) E₁ f₁)
    (hf₂ : VDominatedBy (ν 1) E₂ f₂) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal t * μ {x | t < ‖T f₁ f₂ x‖} ^ (a₁ + a₂) ≤
      ENNReal.ofReal (K * wk m) * μ E₁ ^ a₁ * μ E₂ ^ a₂ := by
  have ha1 := ha.a₁_pos
  have ha2 := ha.a₂_pos
  have hs : 0 < a₁ + a₂ := by linarith
  have hb1 := hf₁.isBddV hf₁m
  have hb2 := hf₂.isBddV hf₂m
  have hF := hmeas f₁ f₂ hb1 hb2
  set F := T f₁ f₂ with hFdef
  let G : ℕ → Set α := fun n =>
    {x | t < ‖F x‖ ∧ ‖F x‖ ≤ n} ∩ spanningSets μ n
  have hGm : ∀ n, MeasurableSet (G n) := fun n =>
    ((measurableSet_lt measurable_const hF.norm).inter (measurableSet_le hF.norm
      measurable_const)).inter (measurableSet_spanningSets μ n)
  have hGf : ∀ n, μ (G n) < ∞ := fun n =>
    (measure_mono Set.inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)
  have hGmono : Monotone G := by
    intro n m hnm x hx
    refine ⟨⟨hx.1.1, hx.1.2.trans (by exact_mod_cast hnm)⟩, monotone_spanningSets μ hnm hx.2⟩
  have hGU : (⋃ n, G n) = {x | t < ‖F x‖} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, G, Set.mem_inter_iff]
    constructor
    · rintro ⟨n, ⟨h1, -⟩, -⟩
      exact h1
    · intro hx
      obtain ⟨n₁, hn₁⟩ : ∃ n₁, x ∈ spanningSets μ n₁ := by
        have : x ∈ ⋃ i, spanningSets μ i := by rw [iUnion_spanningSets]; trivial
        exact Set.mem_iUnion.1 this
      obtain ⟨n₂, hn₂⟩ := exists_nat_ge ‖F x‖
      refine ⟨max n₁ n₂, ⟨hx, hn₂.trans (by exact_mod_cast le_max_right _ _)⟩,
        monotone_spanningSets μ (le_max_left _ _) hn₁⟩
  have hpair : ∀ h : α → W, IsBddV (ν 2) h → ‖∫ x, pr (F x) (h x) ∂μ‖ ≤ Λ ![f₁, f₂, h] :=
    fun h hh => hdom f₁ f₂ h hb1 hb2 hh
  have hn : ∀ n, ENNReal.ofReal t * μ (G n) ^ (a₁ + a₂) ≤
      ENNReal.ofReal (K * wk m) * μ E₁ ^ a₁ * μ E₂ ^ a₂ := by
    intro n
    have h1 := weak_core hν hK hsub hsmall hpr hhull ha hE₁m hE₂m hE₁f hE₂f hf₁m hf₂m hf₁ hf₂ hF
      hpair ht (N := n) (hGm n) (hGf n) (fun x hx => hx.1.1) (fun x hx => hx.1.2)
    calc ENNReal.ofReal t * μ (G n) ^ (a₁ + a₂)
        = ENNReal.ofReal (t * (μ (G n)).toReal ^ (a₁ + a₂)) := by
          rw [ENNReal.ofReal_mul ht.le,
            ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hs.le,
            ENNReal.ofReal_toReal (hGf n).ne]
      _ ≤ ENNReal.ofReal (K * wk m * ((μ E₁).toReal ^ a₁ * (μ E₂).toReal ^ a₂)) :=
          ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (K * wk m) * μ E₁ ^ a₁ * μ E₂ ^ a₂ := by
          rw [← mul_assoc]
          exact ofReal_mul_rpow_mul_rpow hE₁f hE₂f (mul_nonneg hK (wk_nonneg m)) ha1.le ha2.le
  have hlim := (ENNReal.continuous_rpow_const (y := a₁ + a₂)).tendsto _ |>.comp
    (tendsto_measure_iUnion_atTop (μ := μ) hGmono)
  rw [hGU] at hlim
  have hlim2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal t) hlim (Or.inr ENNReal.ofReal_ne_top)
  exact le_of_tendsto' hlim2 hn

/-! ### (RS): the `K`-homogeneous layer-cake interpolation and restricted strong type -/

/-- **K-homogeneous (RS) from two weak-type bounds.**  The weak bounds
`t μ{‖F‖ > t}^{s ± ε} ≤ K x₁^{a₁ ± ε} x₂^{a₂}` (`s = a₁ + a₂`, one constant `K > 0`) give
`‖F‖_{L^{1/s}} ≤ K · rsConst s ε 1 1 · x₁^{a₁} x₂^{a₂}`.  (X1's `eLpNorm_le_of_weak_pair` has
`rsConst s ε K K`, not linear in `K`; here the scaling `F ↦ K⁻¹‖F‖` restores linearity.) -/
theorem eLpNorm_le_of_weak_pair_lin {F : α → E} (hF : AEStronglyMeasurable F μ)
    {a₁ a₂ ε x₁ x₂ K : ℝ} (ha₁ : ε < a₁) (ha₂ : 0 < a₂) (hε : 0 < ε) (hx₁ : 0 < x₁)
    (hx₂ : 0 < x₂) (hK : 0 < K)
    (hwp : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {x | t < ‖F x‖} ^ (a₁ + a₂ + ε) ≤
      ENNReal.ofReal (K * x₁ ^ (a₁ + ε) * x₂ ^ a₂))
    (hwm : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {x | t < ‖F x‖} ^ (a₁ + a₂ - ε) ≤
      ENNReal.ofReal (K * x₁ ^ (a₁ - ε) * x₂ ^ a₂)) :
    eLpNorm F (ENNReal.ofReal (1 / (a₁ + a₂))) μ ≤
      ENNReal.ofReal (K * rsConst (a₁ + a₂) ε 1 1 * (x₁ ^ a₁ * x₂ ^ a₂)) := by
  set F' : α → ℝ := fun x => K⁻¹ * ‖F x‖ with hF'
  have hnorm : ∀ x, ‖F' x‖ = K⁻¹ * ‖F x‖ := fun x => by
    rw [hF', Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hset : ∀ t : ℝ, {x | t < ‖F' x‖} = {x | K * t < ‖F x‖} := by
    intro t
    ext x
    simp only [Set.mem_ofPred_eq, hnorm]
    rw [inv_mul_eq_div, lt_div_iff₀ hK, mul_comm]
  have hcancel : ∀ (A B : ℝ≥0∞), ENNReal.ofReal K * A ≤ ENNReal.ofReal K * B → A ≤ B := fun A B h =>
    (ENNReal.mul_le_mul_iff_right (by simpa using hK) ENNReal.ofReal_ne_top).1 h
  have hfac : ∀ (c : ℝ), ENNReal.ofReal (K * c) = ENNReal.ofReal K * ENNReal.ofReal c :=
    fun c => ENNReal.ofReal_mul hK.le
  have hwp' : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {x | t < ‖F' x‖} ^ (a₁ + a₂ + ε) ≤
      ENNReal.ofReal (1 * x₁ ^ (a₁ + ε) * x₂ ^ a₂) := by
    intro t ht
    have h := hwp (K * t) (mul_pos hK ht)
    rw [← hset t, show K * x₁ ^ (a₁ + ε) * x₂ ^ a₂ = K * (1 * x₁ ^ (a₁ + ε) * x₂ ^ a₂) by ring,
      hfac, hfac, mul_assoc] at h
    exact hcancel _ _ h
  have hwm' : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {x | t < ‖F' x‖} ^ (a₁ + a₂ - ε) ≤
      ENNReal.ofReal (1 * x₁ ^ (a₁ - ε) * x₂ ^ a₂) := by
    intro t ht
    have h := hwm (K * t) (mul_pos hK ht)
    rw [← hset t, show K * x₁ ^ (a₁ - ε) * x₂ ^ a₂ = K * (1 * x₁ ^ (a₁ - ε) * x₂ ^ a₂) by ring,
      hfac, hfac, mul_assoc] at h
    exact hcancel _ _ h
  have hF'm : AEStronglyMeasurable F' μ := hF.norm.const_mul K⁻¹
  have key := eLpNorm_le_of_weak_pair hF'm ha₁ ha₂ hε hx₁ hx₂ zero_le_one zero_le_one hwp' hwm'
  have hscale : eLpNorm F' (ENNReal.ofReal (1 / (a₁ + a₂))) μ =
      ENNReal.ofReal K⁻¹ * eLpNorm F (ENNReal.ofReal (1 / (a₁ + a₂))) μ := by
    have h1 : F' = K⁻¹ • fun x => ‖F x‖ := by
      funext x; simp [hF']
    rw [h1, eLpNorm_const_smul, eLpNorm_norm F hF, Real.enorm_eq_ofReal (inv_nonneg.2 hK.le)]
  rw [hscale] at key
  have hK1 : ENNReal.ofReal K * ENNReal.ofReal K⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hK.le, mul_inv_cancel₀ hK.ne', ENNReal.ofReal_one]
  calc eLpNorm F (ENNReal.ofReal (1 / (a₁ + a₂))) μ
      = ENNReal.ofReal K * (ENNReal.ofReal K⁻¹ * eLpNorm F (ENNReal.ofReal (1 / (a₁ + a₂))) μ) := by
        rw [← mul_assoc, hK1, one_mul]
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (rsConst (a₁ + a₂) ε 1 1 * (x₁ ^ a₁ * x₂ ^ a₂)) :=
        mul_le_mul_right key _
    _ = _ := by rw [← ENNReal.ofReal_mul hK.le]; congr 1; ring

/-- **(RS)**: restricted strong type from two admissible weak-type points `a ± ε e₁`: for bounded `f_i`
with `ν_i ∘ f_i ≤ 1_{E_i}`, `‖T(f₁,f₂)‖_{L^{1/(a₁+a₂)}} ≤ K · wk m · rsConst (a₁+a₂) ε 1 1 ·
μ(E₁)^{a₁} μ(E₂)^{a₂}` (`K > 0`).  Linear in `K`. -/
theorem eLpNorm_le_of_hullBound [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [SigmaFinite μ] {ν : Fin 3 → W → ℝ} {Λ : (Fin 3 → α → W) → ℝ} {K : ℝ} {pr : E → W → ℂ}
    {T : (α → W) → (α → W) → α → E} (hν : ∀ i, IsSlotNorm (ν i)) (hK : 0 < K)
    (hsub : IsSubadditiveV ν Λ) (hsmall : IsSmallV μ ν Λ) (hpr : IsDualPairing (ν 2) pr)
    {Reg : (Fin 3 → ℝ) → Prop} (hhull : ∀ β, Reg β → VHullBound μ ν Λ β K)
    (hdom : IsDominatedV μ ν pr T Λ)
    (hmeas : ∀ f₁ f₂, IsBddV (ν 0) f₁ → IsBddV (ν 1) f₂ → Measurable (T f₁ f₂))
    {κ m a₁ a₂ ε : ℝ} (hε : 0 < ε) (hap : WeakPoint Reg κ m (a₁ + ε) a₂)
    (ham : WeakPoint Reg κ m (a₁ - ε) a₂) {E₁ E₂ : Set α} (hE₁m : MeasurableSet E₁)
    (hE₂m : MeasurableSet E₂) (hE₁f : μ E₁ < ∞) (hE₂f : μ E₂ < ∞) {f₁ f₂ : α → W}
    (hf₁m : Measurable f₁) (hf₂m : Measurable f₂) (hf₁ : VDominatedBy (ν 0) E₁ f₁)
    (hf₂ : VDominatedBy (ν 1) E₂ f₂) :
    eLpNorm (T f₁ f₂) (ENNReal.ofReal (1 / (a₁ + a₂))) μ ≤
      ENNReal.ofReal (K * wk m * rsConst (a₁ + a₂) ε 1 1) * μ E₁ ^ a₁ * μ E₂ ^ a₂ := by
  have hamp1 := ham.a₁_pos
  have hεa : ε < a₁ := by linarith
  have ha1 : 0 < a₁ := by linarith
  have ha2 := ham.a₂_pos
  have hb1 := hf₁.isBddV hf₁m
  have hb2 := hf₂.isBddV hf₂m
  have hF := hmeas f₁ f₂ hb1 hb2
  have hKw : 0 < K * wk m :=
    mul_pos hK (lt_of_lt_of_le (by norm_num) (two_le_wk m))
  have hwp := fun t (ht : 0 < t) => weak_type_of_hullBound hν hK.le hsub hsmall hpr hhull hdom hmeas
    hap hE₁m hE₂m hE₁f hE₂f hf₁m hf₂m hf₁ hf₂ ht
  have hwm := fun t (ht : 0 < t) => weak_type_of_hullBound hν hK.le hsub hsmall hpr hhull hdom hmeas
    ham hE₁m hE₂m hE₁f hE₂f hf₁m hf₂m hf₁ hf₂ ht
  by_cases hE0 : μ E₁ = 0 ∨ μ E₂ = 0
  · -- `T(f₁,f₂) = 0` a.e.
    have hnull : ∀ t : ℝ, 0 < t → μ {x | t < ‖T f₁ f₂ x‖} = 0 := by
      intro t ht
      have h := hwp t ht
      have hR : ENNReal.ofReal (K * wk m) * μ E₁ ^ (a₁ + ε) * μ E₂ ^ a₂ = 0 := by
        rcases hE0 with h0 | h0
        · simp [h0, ENNReal.zero_rpow_of_pos (by linarith : 0 < a₁ + ε)]
        · simp [h0, ENNReal.zero_rpow_of_pos ha2]
      rw [hR, nonpos_iff_eq_zero, mul_eq_zero] at h
      rcases h with h | h
      · exact absurd h (by simpa using ht)
      · exact (ENNReal.rpow_eq_zero_iff_of_pos (by linarith)).1 h
    have hae : T f₁ f₂ =ᵐ[μ] 0 := by
      rw [Filter.EventuallyEq, ae_iff]
      refine measure_mono_null (t := ⋃ n : ℕ, {x | 1 / ((n : ℝ) + 1) < ‖T f₁ f₂ x‖}) ?_
        (measure_iUnion_null fun n => hnull _ (by positivity))
      intro x hx
      have hx' : 0 < ‖T f₁ f₂ x‖ := norm_pos_iff.2 hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx'
      exact Set.mem_iUnion.2 ⟨n, hn⟩
    rw [eLpNorm_congr_ae hae, eLpNorm_zero]
    exact zero_le
  · rw [not_or] at hE0
    have hx₁ : 0 < (μ E₁).toReal := ENNReal.toReal_pos hE0.1 hE₁f.ne
    have hx₂ : 0 < (μ E₂).toReal := ENNReal.toReal_pos hE0.2 hE₂f.ne
    have hwp' : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {x | t < ‖T f₁ f₂ x‖} ^ (a₁ + a₂ + ε) ≤
        ENNReal.ofReal (K * wk m * (μ E₁).toReal ^ (a₁ + ε) * (μ E₂).toReal ^ a₂) := by
      intro t ht
      have h := hwp t ht
      rw [show a₁ + ε + a₂ = a₁ + a₂ + ε by ring] at h
      refine h.trans (le_of_eq ?_)
      exact (ofReal_mul_rpow_mul_rpow hE₁f hE₂f hKw.le (by linarith) ha2.le).symm
    have hwm' : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {x | t < ‖T f₁ f₂ x‖} ^ (a₁ + a₂ - ε) ≤
        ENNReal.ofReal (K * wk m * (μ E₁).toReal ^ (a₁ - ε) * (μ E₂).toReal ^ a₂) := by
      intro t ht
      have h := hwm t ht
      rw [show a₁ - ε + a₂ = a₁ + a₂ - ε by ring] at h
      refine h.trans (le_of_eq ?_)
      exact (ofReal_mul_rpow_mul_rpow hE₁f hE₂f hKw.le (by linarith) ha2.le).symm
    have key := eLpNorm_le_of_weak_pair_lin hF.aestronglyMeasurable hεa ha2 hε hx₁ hx₂ hKw
      hwp' hwm'
    refine key.trans (le_of_eq ?_)
    rw [← mul_assoc]
    exact ofReal_mul_rpow_mul_rpow hE₁f hE₂f
      (mul_nonneg hKw.le (rsConst_nonneg (by linarith) hε (by linarith) zero_le_one zero_le_one))
      ha1.le ha2.le

/-- **(RS) in the shape of the hypothesis `hRS` of R6c-I** (`Interp.eLpNorm_le_of_restrictedStrong`): on
the segment `a = (1/p₁ + t, 1/p₂ - t)`, `|t| < 2δ₀`, with `1/r = 1/p₁ + 1/p₂` fixed, the output exponent is
`r` for every `t`, with the single constant `K · wk m · rsConst (1/r) ε 1 1`; all the points `a ± ε e₁`
must be admissible (`hW`).  The `g_i` are measurable (simple functions are). -/
theorem hRS_of_hullBound [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [SigmaFinite μ] {ν : Fin 3 → W → ℝ} {Λ : (Fin 3 → α → W) → ℝ} {K : ℝ} {pr : E → W → ℂ}
    {T : (α → W) → (α → W) → α → E} (hν : ∀ i, IsSlotNorm (ν i)) (hK : 0 < K)
    (hsub : IsSubadditiveV ν Λ) (hsmall : IsSmallV μ ν Λ) (hpr : IsDualPairing (ν 2) pr)
    {Reg : (Fin 3 → ℝ) → Prop} (hhull : ∀ β, Reg β → VHullBound μ ν Λ β K)
    (hdom : IsDominatedV μ ν pr T Λ)
    (hmeas : ∀ f₁ f₂, IsBddV (ν 0) f₁ → IsBddV (ν 1) f₂ → Measurable (T f₁ f₂))
    {p₁ p₂ r δ₀ ε κ m : ℝ} (hpr' : 1 / r = 1 / p₁ + 1 / p₂) (hε : 0 < ε)
    (hW : ∀ t : ℝ, |t| < 2 * δ₀ → WeakPoint Reg κ m (1 / p₁ + t + ε) (1 / p₂ - t) ∧
      WeakPoint Reg κ m (1 / p₁ + t - ε) (1 / p₂ - t)) :
    ∀ t : ℝ, |t| < 2 * δ₀ → ∀ E₁ E₂ : Set α, MeasurableSet E₁ → MeasurableSet E₂ →
      μ E₁ < ∞ → μ E₂ < ∞ → ∀ g₁ g₂ : α → W, Measurable g₁ → Measurable g₂ →
      VDominatedBy (ν 0) E₁ g₁ → VDominatedBy (ν 1) E₂ g₂ →
      eLpNorm (T g₁ g₂) (ENNReal.ofReal r) μ ≤
        ENNReal.ofReal (K * wk m * rsConst (1 / r) ε 1 1) * μ E₁ ^ (1 / p₁ + t) *
          μ E₂ ^ (1 / p₂ - t) := by
  intro t ht E₁ E₂ hE₁m hE₂m hE₁f hE₂f g₁ g₂ hg₁m hg₂m hg₁ hg₂
  have hsum : (1 / p₁ + t) + (1 / p₂ - t) = 1 / r := by linarith
  have key := eLpNorm_le_of_hullBound hν hK hsub hsmall hpr hhull hdom hmeas hε (hW t ht).1
    (hW t ht).2 hE₁m hE₂m hE₁f hE₂f hg₁m hg₂m hg₁ hg₂
  rw [hsum, one_div_one_div] at key
  exact key

end PrimeBHT.TimeFrequency.X2.Interp
