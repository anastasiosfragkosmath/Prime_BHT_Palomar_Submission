module

public import PrimeBHT.TimeFrequency.Interp.Restricted.Form
public import PrimeBHT.TimeFrequency.Interp.Restricted.Interpolate
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# R6b: operator-level restricted weak type and restricted strong type

Blueprint `docs/x1-blueprint.md`, node R6b (`RL.rwt_op`), on top of R6a
(`PrimeBHT.TimeFrequency.Interp.Restricted.Form`).  See the module docstring of `Form.lean` for the
abstract setting (`Λ : (Fin 3 → α → ℂ) → ℝ`, `IsSubadditive`, `IsSmall`, `HullBound`).

`T : (α → ℂ) → (α → ℂ) → α → ℂ` is the abstract output operator (for X1:
`T(f₁,f₂) = Σ_{t∈P} |I_t|^{-1/2}⟨f₁,φ_{t,1}⟩⟨f₂,φ_{t,2}⟩φ_{t,3}`, a bounded integrable function).

Operator hypotheses, matching the shapes consumed by `PrimeBHT.TimeFrequency.Interp.Strong`:
* `IsDominated μ T Λ` (the blueprint's `|⟨T(f₁,f₂),h⟩| ≤ Λ(f₁,f₂,h)`), with the *bilinear* pairing
  `∫ T(f₁,f₂) · h` (no conjugate, as in `Strong.lean`'s `hdom`) for bounded measurable `f₁ f₂ h`;
  for the conjugate pairing `∫ T conj h` use `Λ'(f,g,h) := Λ(f,g,conj ∘ h)`, which keeps every
  hypothesis (`IsSubadditive`, `IsSmall`, `HullBound`) since `|conj h| = |h|`.
* `hmeas`: `T(f₁,f₂)` is measurable for bounded measurable `f₁,f₂`.

Exponents: `InUstar a₁ a₂` is `U_* = {a ∈ (0,1)² : a₁ + a₂ < 3/2}`; `alphaOf a₁ a₂ = (a₁,a₂,1-a₁-a₂)`.
The hull family is a hypothesis `hhull : ∀ b ∈ InReg ρ, HullBound μ Λ (alphaOf b) (C b)` with `0 ≤ C`,
on the compact part `InReg ρ` of `U_*` only (see correction 7).

## Main results

* `weak_type_of_hullBound` (RWT): `ofReal t * μ{‖T(f₁,f₂)‖ > t}^{a₁+a₂} ≤ ofReal (weakConst C a₁ a₂)
  * μ E₁^{a₁} * μ E₂^{a₂}` for `a ∈ U_*` (`1/r_a = a₁ + a₂`).  `SigmaFinite μ`.
* `eLpNorm_le_of_hullBound` (RS): for `a ± ε(1,0) ∈ U_*`:
  `eLpNorm (T f₁ f₂) (ofReal (1/(a₁+a₂))) μ ≤ ofReal (rsConst (a₁+a₂) ε (weakConst C (a₁+ε) a₂)
  (weakConst C (a₁-ε) a₂)) * μ E₁^{a₁} * μ E₂^{a₂}` (layer cake in `Interpolate.lean`).
* `eLpNorm_le_of_hullBound_of_inReg` (RS, uniform constants): on `InReg η` (a compact exhaustion
  of `U_*`), with `C ≤ K₀` on `InReg (η/4)`, the constant is `rsConst (a₁+a₂) (η/2) W W`,
  `W = weakBound (η/2) K₀`: on a segment `a₁ + a₂ = s` it does not depend on `a`.  This is the
  "locally bounded" statement of the blueprint, made explicit.
* `hRS_of_hullBound`: the hypothesis `hRS` of `Strong.lean`'s `eLpNorm_le_of_restrictedStrong`
  (R6c-I), literally (`g_i` measurable; for simple `g_i` use `g_i.measurable`); the constant is
  `K = rsConst (1/r) (η/2) W W`.
* `restrictedType_of_hullBound_hRT`: the hypothesis `hRT` of `Strong.lean`'s `form_le_of_restrictedType`
  / `eLpNorm_le_of_restrictedType` (R6c-II) for `Λ' f g h := Λ ![f, g, h]`, constant
  `K₀/(1 - 2^{-η})`.
* `IsSubadditive.sub₁/₂/₃`, `IsBdd.of_simpleFunc`: the curried subadditivity and boundedness facts
  that `Strong.lean` asks for on simple functions (`hsub₁₂₃`, and `hdom` from `IsDominated`).
  Homogeneity (`hhom`) and bilinearity of `T` on simple functions (`hadd`, `hsmul`) are *not*
  consequences of the hypotheses here and stay hypotheses of the consumer.

## Corrections to the blueprint (R6b)
1. `U_*` is only *contained* in the preimage of the open hexagon under `a ↦ α(a)` (the preimage is
   `{-1/2 < a_i < 1, 0 < a₁+a₂ < 3/2}`, larger), not equal to it.
2. The sign function: with the bilinear pairing `∫ T h` the test function is
   `h₃ = conj(sgn T)·1_{G'}` (the blueprint's), with `∫ T conj h` it is `sgn T · 1_{G'}`.
3. `G = {|T| > λ}` need not be known to have finite measure a priori; the proof works on subsets
   `G' = G ∩ {|T| ≤ N} ∩ (spanning set)` (finite measure, `T` bounded on them, so `∫_{G'} |T|`
   makes sense as a Bochner integral) and passes to the limit (`SigmaFinite μ`).
4. **Case `α₃ > 0` (R6a at `α(a)`) is not locally bounded** as `a₁ + a₂ ↑ 1`: its constant
   `C_a/(1 - 2^{-min α_i})` blows up like `1/α₃`.  The blueprint's claim (iii) ("both continuous")
   overlooks that `α_min → 0`.  Fix used here: *one* argument for all `a ∈ U_*`: sub-case 1
   (`|G| ≥ max(|E₁|,|E₂|)`: `HullBound` at `α(a)`, constant `2 C_a`) and sub-case 2
   (`|G| < |E₂|`: R6a at `b = (a₁, min(a₂, (1-a₁)/2))`, all `α(b)_i ≥ min(a₁,b₂) > 0`, and the
   remaining power `|G|^{a₂-b₂} ≤ |E₂|^{a₂-b₂}` with `a₂ - b₂ ≥ 0`; symmetric for `|E₁|`).  The
   constant `weakConst` depends only on `C` at `α(a)` and at the two points `b`, and on
   `min(a₁,a₂,(1-a₁)/2,(1-a₂)/2)`, so it stays bounded where `a` stays away from the boundary of
   `U_*` (*including* the line `a₁ + a₂ = 1`).
5. Watch item (ii) is inaccurate: sub-case 2 uses R6a (restricted type of the *form*, major subset
   nowhere), not a Banach-range strong-type estimate.
6. Null `E_i` (or null `G`): handled via `IsSmall` (`Λ ≤ A Π μ(S_i)`): the blueprint's
   `HullBound` is only for positive measures.

7. **The hull hypothesis is only needed on a compact part of `U_*`.**  The original statements asked
   `hhull : ∀ b ∈ U_*, HullBound μ Λ (alphaOf b) (C b)`.  For the tri-tile form this cannot be
   supplied by M1(ε) with packets adapted with one exponent `N` (`N(ε)` may grow as `ε → 0`, i.e.
   near the boundary of `U_*`).  The proofs only evaluate `hhull` at `a`, at the points
   `(a₁, min a₂ ((1-a₁)/2))`, `(min a₁ ((1-a₂)/2), a₂)` and at `a ± (ε, 0)`: for `a ∈ InReg (2ρ)`
   all of these lie in `InReg ρ` (`InReg.sub_left`, `InReg.sub_right`).  So `hhull` is now
   `∀ b, InReg ρ b → HullBound …` (`weak_core`, `weak_type_of_hullBound`, `eLpNorm_le_of_hullBound`,
   with `a ∈ InReg (2ρ)`, resp. `a ± (ε, 0) ∈ InReg (2ρ)`), `InReg (η/4)` for
   `eLpNorm_le_of_hullBound_of_inReg` and `hRS_of_hullBound`, `InReg η` for
   `restrictedType_of_hullBound_hRT`; `InReg` and its lemmas moved before `weak_core`.  No proof
   changed except for the membership arguments.
-/

@[expose] public section

namespace PrimeBHT.TimeFrequency.Interp.Restricted

open MeasureTheory Function Finset Filter Topology
open scoped ENNReal ComplexConjugate

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The exponent region `U_* = {a ∈ (0,1)² : a₁ + a₂ < 3/2}` of the blueprint. -/
def InUstar (a₁ a₂ : ℝ) : Prop :=
  0 < a₁ ∧ a₁ < 1 ∧ 0 < a₂ ∧ a₂ < 1 ∧ a₁ + a₂ < 3 / 2

/-- `α(a) = (a₁, a₂, 1 - a₁ - a₂)`. -/
def alphaOf (a₁ a₂ : ℝ) : Fin 3 → ℝ := ![a₁, a₂, 1 - a₁ - a₂]

/-- `|∫ T(f₁,f₂) h| ≤ Λ(f₁,f₂,h)` for bounded measurable `f₁ f₂ h`. -/
def IsDominated (μ : Measure α) (T : (α → ℂ) → (α → ℂ) → α → ℂ)
    (Λ : (Fin 3 → α → ℂ) → ℝ) : Prop :=
  ∀ f₁ f₂ h : α → ℂ, IsBdd f₁ → IsBdd f₂ → IsBdd h →
    ‖∫ x, T f₁ f₂ x * h x ∂μ‖ ≤ Λ ![f₁, f₂, h]

/-- The constant of R6a at `m`: `C/(1 - 2^{-m})`. -/
noncomputable def restrictedConst (C m : ℝ) : ℝ := C / (1 - (2 : ℝ) ^ (-m))

/-- The constant of (RWT) in terms of the hull constants `C`. -/
noncomputable def weakConst (C : ℝ → ℝ → ℝ) (a₁ a₂ : ℝ) : ℝ :=
  max (2 * C a₁ a₂)
    (max (restrictedConst (C a₁ (min a₂ ((1 - a₁) / 2))) (min a₁ (min a₂ ((1 - a₁) / 2))))
      (restrictedConst (C (min a₁ ((1 - a₂) / 2)) a₂) (min (min a₁ ((1 - a₂) / 2)) a₂)))

lemma restrictedConst_nonneg {C m : ℝ} (hC : 0 ≤ C) (hm : 0 < m) : 0 ≤ restrictedConst C m := by
  unfold restrictedConst
  have : (2 : ℝ) ^ (-m) < 1 := by
    rw [Real.rpow_neg (by norm_num)]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) hm)
  exact div_nonneg hC (by linarith)

lemma weakConst_nonneg {C : ℝ → ℝ → ℝ} (hC : ∀ b₁ b₂, 0 ≤ C b₁ b₂) (a₁ a₂ : ℝ) :
    0 ≤ weakConst C a₁ a₂ :=
  le_max_of_le_left (mul_nonneg (by norm_num) (hC _ _))

lemma forall_vec3 {β : Type*} {P : β → Prop} {x y z : β} (hx : P x) (hy : P y) (hz : P z) :
    ∀ i : Fin 3, P (![x, y, z] i) := by
  intro i
  fin_cases i <;> simpa

lemma prod_vec3 (E₁ E₂ G : Set α) (μ : Measure α) (b : Fin 3 → ℝ) :
    ∏ i, (μ (![E₁, E₂, G] i)).toReal ^ b i =
      (μ E₁).toReal ^ b 0 * (μ E₂).toReal ^ b 1 * (μ G).toReal ^ b 2 := by
  simp [Fin.prod_univ_three]

/-! ### The pairing step -/

/-- On a finite-measure set `G` where `t < ‖F‖ ≤ N`, there is a test function `h` dominated by
`1_G` with `t μ(G) ≤ ‖∫ F h‖`. -/
lemma exists_test_of_level {F : α → ℂ} (hF : Measurable F) {t N : ℝ} (ht : 0 < t) {G : Set α}
    (hG : MeasurableSet G) (hGf : μ G < ∞) (hlow : ∀ x ∈ G, t < ‖F x‖)
    (hup : ∀ x ∈ G, ‖F x‖ ≤ N) :
    ∃ h : α → ℂ, Measurable h ∧ DominatedBy G h ∧ t * (μ G).toReal ≤ ‖∫ x, F x * h x ∂μ‖ := by
  classical
  set h : α → ℂ := G.indicator (fun x => (starRingEnd ℂ) (F x) / ((‖F x‖ : ℝ) : ℂ)) with hh
  have hFm : Measurable fun x => (starRingEnd ℂ) (F x) / ((‖F x‖ : ℝ) : ℂ) :=
    (Complex.continuous_conj.measurable.comp hF).div (Complex.measurable_ofReal.comp hF.norm)
  have hpos : ∀ x ∈ G, 0 < ‖F x‖ := fun x hx => ht.trans (hlow x hx)
  refine ⟨h, hFm.indicator hG, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ G
    · simp only [hh, Set.indicator_of_mem hx]
      have : ‖F x‖ ≠ 0 := (hpos x hx).ne'
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        RCLike.norm_conj, div_self this]
    · simp [hh, Set.indicator_of_notMem hx]
  · have hprod : ∀ x, F x * h x = (((G.indicator (fun x => ‖F x‖) x : ℝ)) : ℂ) := by
      intro x
      by_cases hx : x ∈ G
      · simp only [hh, Set.indicator_of_mem hx]
        have hne : ((‖F x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos x hx).ne'
        rw [mul_div_assoc', Complex.mul_conj, Complex.normSq_eq_norm_sq, div_eq_iff hne]
        push_cast
        ring
      · simp [hh, Set.indicator_of_notMem hx]
    have hint : IntegrableOn (fun x => ‖F x‖) G μ :=
      Measure.integrableOn_of_bounded (M := N) hGf.ne hF.norm.aestronglyMeasurable
        (ae_restrict_of_forall_mem hG fun x hx => by simpa using hup x hx)
    simp_rw [hprod]
    rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs, integral_indicator hG]
    refine le_trans ?_ (le_abs_self _)
    exact setIntegral_ge_of_const_le_real hG hGf.ne (fun x hx => (hlow x hx).le) hint

/-! ### Real arithmetic -/

lemma arith_sub1 {t g K P q : ℝ} (hg : 0 < g) (h : t * g ≤ 2 * (K * P * g ^ q)) :
    t * g ^ (1 - q) ≤ 2 * (K * P) := by
  have hq : 0 < g ^ q := Real.rpow_pos_of_pos hg q
  rw [Real.rpow_sub hg, Real.rpow_one, ← mul_div_assoc, div_le_iff₀ hq]
  linarith

lemma arith_sub2 {t g x y K p q e d : ℝ} (hg : 0 < g) (hy : 0 < y) (hx : 0 < x) (hK : 0 ≤ K)
    (hd : 0 ≤ d) (hgy : g ≤ y) (he : p + q + e = 1)
    (h : t * g ≤ K * x ^ p * y ^ q * g ^ e) :
    t * g ^ (p + q + d) ≤ K * x ^ p * y ^ (q + d) := by
  have hge : 0 < g ^ e := Real.rpow_pos_of_pos hg e
  have h1 : t * g ^ (1 - e) ≤ K * x ^ p * y ^ q := by
    rw [Real.rpow_sub hg, Real.rpow_one, ← mul_div_assoc, div_le_iff₀ hge]
    exact h
  have h2 : p + q + d = (1 - e) + d := by linarith
  have hxp : 0 ≤ K * x ^ p * y ^ q :=
    mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hx.le _)) (Real.rpow_nonneg hy.le _)
  calc t * g ^ (p + q + d) = (t * g ^ (1 - e)) * g ^ d := by
        rw [h2, Real.rpow_add hg]; ring
    _ ≤ (K * x ^ p * y ^ q) * g ^ d := by gcongr
    _ ≤ (K * x ^ p * y ^ q) * y ^ d := by
        have := Real.rpow_le_rpow hg.le hgy hd
        gcongr
    _ = K * x ^ p * y ^ (q + d) := by rw [Real.rpow_add hy]; ring

lemma forall_vec3₂ {β γ : Type*} {P : β → γ → Prop} {x y z : β} {x' y' z' : γ} (hx : P x x')
    (hy : P y y') (hz : P z z') : ∀ i : Fin 3, P (![x, y, z] i) (![x', y', z'] i) := by
  intro i
  fin_cases i <;> simpa

/-- `U_*` away from its boundary: the compact exhaustion `{a : η ≤ a_i ≤ 1 - η, a₁ + a₂ ≤ 3/2 - η}`
used to turn "locally bounded" into explicit uniform constants. -/
def InReg (η b₁ b₂ : ℝ) : Prop :=
  η ≤ b₁ ∧ b₁ ≤ 1 - η ∧ η ≤ b₂ ∧ b₂ ≤ 1 - η ∧ b₁ + b₂ ≤ 3 / 2 - η

lemma InReg.inUstar {η b₁ b₂ : ℝ} (hη : 0 < η) (h : InReg η b₁ b₂) : InUstar b₁ b₂ :=
  ⟨by linarith [h.1], by linarith [h.2.1], by linarith [h.2.2.1], by linarith [h.2.2.2.1],
    by linarith [h.2.2.2.2]⟩

lemma InReg.mono {η η' b₁ b₂ : ℝ} (h : InReg η b₁ b₂) (hη : η' ≤ η) : InReg η' b₁ b₂ :=
  ⟨by linarith [h.1], by linarith [h.2.1], by linarith [h.2.2.1], by linarith [h.2.2.2.1],
    by linarith [h.2.2.2.2]⟩


lemma InReg.sub_left {ρ a₁ a₂ : ℝ} (hρ : 0 < ρ) (h : InReg (2 * ρ) a₁ a₂) :
    InReg ρ (min a₁ ((1 - a₂) / 2)) a₂ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨le_min (by linarith) (by linarith), ?_, by linarith, by linarith, ?_⟩
  · have := min_le_left a₁ ((1 - a₂) / 2)
    linarith
  · have := min_le_left a₁ ((1 - a₂) / 2)
    linarith

lemma InReg.sub_right {ρ a₁ a₂ : ℝ} (hρ : 0 < ρ) (h : InReg (2 * ρ) a₁ a₂) :
    InReg ρ a₁ (min a₂ ((1 - a₁) / 2)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by linarith, by linarith, le_min (by linarith) (by linarith), ?_, ?_⟩
  · have := min_le_left a₂ ((1 - a₁) / 2)
    linarith
  · have := min_le_left a₂ ((1 - a₁) / 2)
    linarith

/-! ### The core of (RWT) -/

/-- Core of (RWT): the real-valued weak-type bound on a finite-measure piece `G` of a level set
on which `t < ‖F‖ ≤ N`, where `F` is dominated by `Λ(f₁, f₂, ·)` in the sense of `hpair`. -/
theorem weak_core {Λ : (Fin 3 → α → ℂ) → ℝ} {C : ℝ → ℝ → ℝ}
    (hsub : IsSubadditive Λ) (hsmall : IsSmall μ Λ) (hC0 : ∀ b₁ b₂, 0 ≤ C b₁ b₂)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hhull : ∀ b₁ b₂, InReg ρ b₁ b₂ → HullBound μ Λ (alphaOf b₁ b₂) (C b₁ b₂))
    {a₁ a₂ : ℝ} (ha : InReg (2 * ρ) a₁ a₂) {E₁ E₂ : Set α} (hE₁m : MeasurableSet E₁)
    (hE₂m : MeasurableSet E₂) (hE₁f : μ E₁ < ∞) (hE₂f : μ E₂ < ∞)
    {f₁ f₂ : α → ℂ} (hf₁m : Measurable f₁) (hf₂m : Measurable f₂)
    (hf₁ : DominatedBy E₁ f₁) (hf₂ : DominatedBy E₂ f₂) {F : α → ℂ} (hF : Measurable F)
    (hpair : ∀ h : α → ℂ, IsBdd h → ‖∫ x, F x * h x ∂μ‖ ≤ Λ ![f₁, f₂, h])
    {t N : ℝ} (ht : 0 < t) {G : Set α} (hGm : MeasurableSet G) (hGf : μ G < ∞)
    (hlow : ∀ x ∈ G, t < ‖F x‖) (hup : ∀ x ∈ G, ‖F x‖ ≤ N) :
    t * (μ G).toReal ^ (a₁ + a₂) ≤
      weakConst C a₁ a₂ * ((μ E₁).toReal ^ a₁ * (μ E₂).toReal ^ a₂) := by
  obtain ⟨ha1, ha1', ha2, ha2', ha12⟩ := ha.inUstar (by linarith)
  have hs : 0 < a₁ + a₂ := by linarith
  have hW0 : 0 ≤ weakConst C a₁ a₂ := weakConst_nonneg hC0 a₁ a₂
  have hP0 : 0 ≤ (μ E₁).toReal ^ a₁ * (μ E₂).toReal ^ a₂ :=
    mul_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  obtain ⟨A, hA, hsm⟩ := hsmall
  have pair : ∀ G' : Set α, MeasurableSet G' → G' ⊆ G →
      ∃ h : α → ℂ, Measurable h ∧ DominatedBy G' h ∧ t * (μ G').toReal ≤ Λ ![f₁, f₂, h] := by
    intro G' hG' hsub'
    obtain ⟨h, hm, hd, hle⟩ := exists_test_of_level hF ht hG' ((measure_mono hsub').trans_lt hGf)
      (fun x hx => hlow x (hsub' hx)) (fun x hx => hup x (hsub' hx))
    exact ⟨h, hm, hd, hle.trans (hpair h (hd.isBdd hm))⟩
  by_cases hG0 : μ G = 0
  · rw [hG0, ENNReal.toReal_zero, Real.zero_rpow hs.ne', mul_zero]
    exact mul_nonneg hW0 hP0
  by_cases hE0 : μ E₁ = 0 ∨ μ E₂ = 0
  · exfalso
    obtain ⟨h, hm, hd, hle⟩ := pair G hGm subset_rfl
    have hΛ := hsm ![f₁, f₂, h] ![E₁, E₂, G] (forall_vec3 hE₁m hE₂m hGm)
      (forall_vec3 (P := fun S => μ S < ∞) hE₁f hE₂f hGf) (forall_vec3 hf₁m hf₂m hm)
      (forall_vec3₂ (P := DominatedBy) hf₁ hf₂ hd)
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
  have hfin3 : ∀ i, μ (![E₁, E₂, G] i) < ∞ := forall_vec3 (P := fun S => μ S < ∞) hE₁f hE₂f hGf
  have hm3 : ∀ i, MeasurableSet (![E₁, E₂, G] i) := forall_vec3 hE₁m hE₂m hGm
  by_cases hlarge : μ E₁ ≤ μ G ∧ μ E₂ ≤ μ G
  · -- sub-case 1: `G` is a largest set
    have hmax : ∀ i, μ (![E₁, E₂, G] i) ≤ μ (![E₁, E₂, G] 2) := by
      intro i
      fin_cases i
      · exact hlarge.1
      · exact hlarge.2
      · exact le_rfl
    obtain ⟨Et, hEtm, hEtsub, hEt2, hbd⟩ := hhull a₁ a₂ (ha.mono (by linarith)) ![E₁, E₂, G] hm3 hpos3 hfin3 2 hmax
    obtain ⟨h, hm, hd, hle⟩ := pair Et hEtm hEtsub
    have hdom : ∀ i : Fin 3, i ≠ 2 → DominatedBy (![E₁, E₂, G] i) (![f₁, f₂, h] i) := by
      intro i hi
      fin_cases i
      · exact hf₁
      · exact hf₂
      · exact (hi rfl).elim
    have hΛ := hbd ![f₁, f₂, h] (forall_vec3 hf₁m hf₂m hm) hdom hd
    rw [prod_vec3] at hΛ
    have hEtfin : μ Et < ∞ := (measure_mono hEtsub).trans_lt hGf
    have hge : (μ G).toReal ≤ 2 * (μ Et).toReal := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hEtfin.ne) hEt2
      simpa [ENNReal.toReal_mul] using this
    have hmain : t * (μ G).toReal ≤
        2 * (C a₁ a₂ * ((μ E₁).toReal ^ a₁ * (μ E₂).toReal ^ a₂) *
          (μ G).toReal ^ (1 - a₁ - a₂)) := by
      calc t * (μ G).toReal ≤ t * (2 * (μ Et).toReal) :=
            mul_le_mul_of_nonneg_left hge ht.le
        _ = 2 * (t * (μ Et).toReal) := by ring
        _ ≤ 2 * (C a₁ a₂ * ((μ E₁).toReal ^ alphaOf a₁ a₂ 0 * (μ E₂).toReal ^ alphaOf a₁ a₂ 1 *
              (μ G).toReal ^ alphaOf a₁ a₂ 2)) :=
            mul_le_mul_of_nonneg_left (hle.trans hΛ) (by norm_num)
        _ = _ := by simp [alphaOf]; ring
    have h1 := arith_sub1 hg hmain
    rw [show (1 : ℝ) - (1 - a₁ - a₂) = a₁ + a₂ by ring] at h1
    refine h1.trans ?_
    have : 2 * C a₁ a₂ ≤ weakConst C a₁ a₂ := le_max_left _ _
    nlinarith
  · -- sub-case 2: some input set is larger than `G`
    have r6a : ∀ b₁ b₂ : ℝ, InReg ρ b₁ b₂ → ∀ m : ℝ, 0 < m → (∀ i, m ≤ alphaOf b₁ b₂ i) →
        t * (μ G).toReal ≤ restrictedConst (C b₁ b₂) m *
          ((μ E₁).toReal ^ b₁ * (μ E₂).toReal ^ b₂ * (μ G).toReal ^ (1 - b₁ - b₂)) := by
      intro b₁ b₂ hb m hm hmb
      obtain ⟨h, hm', hd, hle⟩ := pair G hGm subset_rfl
      have hΛ := restrictedType_of_hullBound hmb hm (hC0 b₁ b₂) hsub ⟨A, hA, hsm⟩
        (hhull b₁ b₂ hb) (E := ![E₁, E₂, G]) hm3 hfin3 (h := ![f₁, f₂, h])
        (forall_vec3 hf₁m hf₂m hm') (forall_vec3₂ (P := DominatedBy) hf₁ hf₂ hd)
      rw [prod_vec3] at hΛ
      refine hle.trans (hΛ.trans (le_of_eq ?_))
      simp [alphaOf, restrictedConst]
    rcases not_and_or.1 hlarge with h1 | h2
    · -- `μ G < μ E₁`
      have hgx : (μ G).toReal ≤ (μ E₁).toReal :=
        ENNReal.toReal_mono hE₁f.ne (not_le.1 h1).le
      set b₁ := min a₁ ((1 - a₂) / 2) with hb₁
      have hb1a : b₁ ≤ a₁ := min_le_left _ _
      have hb1h : b₁ ≤ (1 - a₂) / 2 := min_le_right _ _
      have hb1pos : 0 < b₁ := lt_min ha1 (by linarith)
      have hbU : InReg ρ b₁ a₂ := ha.sub_left hρ
      have hmb : ∀ i, min b₁ a₂ ≤ alphaOf b₁ a₂ i := by
        intro i
        fin_cases i
        · exact min_le_left _ _
        · exact min_le_right _ _
        · show min b₁ a₂ ≤ 1 - b₁ - a₂
          have := min_le_left b₁ a₂
          linarith
      have h3 := r6a b₁ a₂ hbU (min b₁ a₂) (lt_min hb1pos ha2) hmb
      have h4 := arith_sub2 (x := (μ E₂).toReal) (y := (μ E₁).toReal) (p := a₂) (q := b₁)
        (e := 1 - b₁ - a₂) (d := a₁ - b₁) hg hx₁ hx₂
        (restrictedConst_nonneg (hC0 _ _) (lt_min hb1pos ha2)) (by linarith) hgx (by ring)
        (by
          refine h3.trans (le_of_eq ?_)
          ring)
      rw [show a₂ + b₁ + (a₁ - b₁) = a₁ + a₂ by ring,
        show b₁ + (a₁ - b₁) = a₁ by ring] at h4
      refine h4.trans ?_
      have : restrictedConst (C b₁ a₂) (min b₁ a₂) ≤ weakConst C a₁ a₂ :=
        le_max_of_le_right (le_max_right _ _)
      calc _ = restrictedConst (C b₁ a₂) (min b₁ a₂) *
            ((μ E₁).toReal ^ a₁ * (μ E₂).toReal ^ a₂) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right this hP0
    · -- `μ G < μ E₂`
      have hgx : (μ G).toReal ≤ (μ E₂).toReal :=
        ENNReal.toReal_mono hE₂f.ne (not_le.1 h2).le
      set b₂ := min a₂ ((1 - a₁) / 2) with hb₂
      have hb2a : b₂ ≤ a₂ := min_le_left _ _
      have hb2h : b₂ ≤ (1 - a₁) / 2 := min_le_right _ _
      have hb2pos : 0 < b₂ := lt_min ha2 (by linarith)
      have hbU : InReg ρ a₁ b₂ := ha.sub_right hρ
      have hmb : ∀ i, min a₁ b₂ ≤ alphaOf a₁ b₂ i := by
        intro i
        fin_cases i
        · exact min_le_left _ _
        · exact min_le_right _ _
        · show min a₁ b₂ ≤ 1 - a₁ - b₂
          have := min_le_right a₁ b₂
          linarith
      have h3 := r6a a₁ b₂ hbU (min a₁ b₂) (lt_min ha1 hb2pos) hmb
      have h4 := arith_sub2 (x := (μ E₁).toReal) (y := (μ E₂).toReal) (p := a₁) (q := b₂)
        (e := 1 - a₁ - b₂) (d := a₂ - b₂) hg hx₂ hx₁
        (restrictedConst_nonneg (hC0 _ _) (lt_min ha1 hb2pos)) (by linarith) hgx (by ring)
        (by
          refine h3.trans (le_of_eq ?_)
          ring)
      rw [show a₁ + b₂ + (a₂ - b₂) = a₁ + a₂ by ring,
        show b₂ + (a₂ - b₂) = a₂ by ring] at h4
      refine h4.trans ?_
      have : restrictedConst (C a₁ b₂) (min a₁ b₂) ≤ weakConst C a₁ a₂ :=
        le_max_of_le_right (le_max_left _ _)
      calc _ = restrictedConst (C a₁ b₂) (min a₁ b₂) *
            ((μ E₁).toReal ^ a₁ * (μ E₂).toReal ^ a₂) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right this hP0

/-! ### (RWT) in `ℝ≥0∞` -/

lemma ofReal_mul_rpow_mul_rpow {m₁ m₂ : ℝ≥0∞} (h₁ : m₁ < ∞) (h₂ : m₂ < ∞) {K b₁ b₂ : ℝ}
    (hK : 0 ≤ K) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) :
    ENNReal.ofReal (K * m₁.toReal ^ b₁ * m₂.toReal ^ b₂) =
      ENNReal.ofReal K * m₁ ^ b₁ * m₂ ^ b₂ := by
  rw [ENNReal.ofReal_mul (mul_nonneg hK (Real.rpow_nonneg ENNReal.toReal_nonneg _)),
    ENNReal.ofReal_mul hK, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hb₁,
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hb₂, ENNReal.ofReal_toReal h₁.ne,
    ENNReal.ofReal_toReal h₂.ne]

/-- **(RWT)**: for `a ∈ U_*`, bounded `f_i` with `|f_i| ≤ 1_{E_i}` and every `t > 0`,
`t μ{‖T(f₁,f₂)‖ > t}^{a₁+a₂} ≤ weakConst C a · μ(E₁)^{a₁} μ(E₂)^{a₂}`
(i.e. `t μ{·}^{1/r_a} ≤ C_a |E₁|^{a₁}|E₂|^{a₂}`, `1/r_a = a₁ + a₂`). -/
theorem weak_type_of_hullBound [SigmaFinite μ] {Λ : (Fin 3 → α → ℂ) → ℝ}
    {T : (α → ℂ) → (α → ℂ) → α → ℂ} {C : ℝ → ℝ → ℝ}
    (hsub : IsSubadditive Λ) (hsmall : IsSmall μ Λ) (hC0 : ∀ b₁ b₂, 0 ≤ C b₁ b₂)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hhull : ∀ b₁ b₂, InReg ρ b₁ b₂ → HullBound μ Λ (alphaOf b₁ b₂) (C b₁ b₂))
    (hdom : IsDominated μ T Λ) (hmeas : ∀ f₁ f₂, IsBdd f₁ → IsBdd f₂ → Measurable (T f₁ f₂))
    {a₁ a₂ : ℝ} (ha : InReg (2 * ρ) a₁ a₂) {E₁ E₂ : Set α} (hE₁m : MeasurableSet E₁)
    (hE₂m : MeasurableSet E₂) (hE₁f : μ E₁ < ∞) (hE₂f : μ E₂ < ∞)
    {f₁ f₂ : α → ℂ} (hf₁m : Measurable f₁) (hf₂m : Measurable f₂)
    (hf₁ : DominatedBy E₁ f₁) (hf₂ : DominatedBy E₂ f₂) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal t * μ {x | t < ‖T f₁ f₂ x‖} ^ (a₁ + a₂) ≤
      ENNReal.ofReal (weakConst C a₁ a₂) * μ E₁ ^ a₁ * μ E₂ ^ a₂ := by
  obtain ⟨ha1, -, ha2, -, -⟩ := ha.inUstar (by linarith)
  have hs : 0 < a₁ + a₂ := by linarith
  have hb1 := hf₁.isBdd hf₁m
  have hb2 := hf₂.isBdd hf₂m
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
  have hpair : ∀ h : α → ℂ, IsBdd h → ‖∫ x, F x * h x ∂μ‖ ≤ Λ ![f₁, f₂, h] :=
    fun h hh => hdom f₁ f₂ h hb1 hb2 hh
  have hn : ∀ n, ENNReal.ofReal t * μ (G n) ^ (a₁ + a₂) ≤
      ENNReal.ofReal (weakConst C a₁ a₂) * μ E₁ ^ a₁ * μ E₂ ^ a₂ := by
    intro n
    have h1 := weak_core hsub hsmall hC0 hρ hhull ha hE₁m hE₂m hE₁f hE₂f hf₁m hf₂m hf₁ hf₂ hF
      hpair ht (N := n) (hGm n) (hGf n) (fun x hx => hx.1.1) (fun x hx => hx.1.2)
    calc ENNReal.ofReal t * μ (G n) ^ (a₁ + a₂)
        = ENNReal.ofReal (t * (μ (G n)).toReal ^ (a₁ + a₂)) := by
          rw [ENNReal.ofReal_mul ht.le,
            ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hs.le,
            ENNReal.ofReal_toReal (hGf n).ne]
      _ ≤ ENNReal.ofReal (weakConst C a₁ a₂ * ((μ E₁).toReal ^ a₁ * (μ E₂).toReal ^ a₂)) :=
          ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (weakConst C a₁ a₂) * μ E₁ ^ a₁ * μ E₂ ^ a₂ := by
          rw [← mul_assoc]
          exact ofReal_mul_rpow_mul_rpow hE₁f hE₂f (weakConst_nonneg hC0 a₁ a₂) ha1.le ha2.le
  have hlim := (ENNReal.continuous_rpow_const (y := a₁ + a₂)).tendsto _ |>.comp
    (tendsto_measure_iUnion_atTop (μ := μ) hGmono)
  rw [hGU] at hlim
  have hlim2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal t) hlim (Or.inr ENNReal.ofReal_ne_top)
  exact le_of_tendsto' hlim2 hn

/-! ### (RS): restricted strong type -/

/-- **(RS)**: for `a ∈ U_*` with `a ± ε(1,0) ∈ U_*`, `0 < ε`, bounded `f_i` with `|f_i| ≤ 1_{E_i}`:
`‖T(f₁,f₂)‖_{L^{1/(a₁+a₂)}} ≤ rsConst (a₁+a₂) ε C_{a⁺} C_{a⁻} · μ(E₁)^{a₁} μ(E₂)^{a₂}`
with `C_{a^±} = weakConst C (a₁ ± ε) a₂`. -/
theorem eLpNorm_le_of_hullBound [SigmaFinite μ] {Λ : (Fin 3 → α → ℂ) → ℝ}
    {T : (α → ℂ) → (α → ℂ) → α → ℂ} {C : ℝ → ℝ → ℝ}
    (hsub : IsSubadditive Λ) (hsmall : IsSmall μ Λ) (hC0 : ∀ b₁ b₂, 0 ≤ C b₁ b₂)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hhull : ∀ b₁ b₂, InReg ρ b₁ b₂ → HullBound μ Λ (alphaOf b₁ b₂) (C b₁ b₂))
    (hdom : IsDominated μ T Λ) (hmeas : ∀ f₁ f₂, IsBdd f₁ → IsBdd f₂ → Measurable (T f₁ f₂))
    {a₁ a₂ ε : ℝ} (ha : InUstar a₁ a₂) (hε : 0 < ε) (hap : InReg (2 * ρ) (a₁ + ε) a₂)
    (ham : InReg (2 * ρ) (a₁ - ε) a₂) {E₁ E₂ : Set α} (hE₁m : MeasurableSet E₁)
    (hE₂m : MeasurableSet E₂) (hE₁f : μ E₁ < ∞) (hE₂f : μ E₂ < ∞)
    {f₁ f₂ : α → ℂ} (hf₁m : Measurable f₁) (hf₂m : Measurable f₂)
    (hf₁ : DominatedBy E₁ f₁) (hf₂ : DominatedBy E₂ f₂) :
    eLpNorm (T f₁ f₂) (ENNReal.ofReal (1 / (a₁ + a₂))) μ ≤
      ENNReal.ofReal (rsConst (a₁ + a₂) ε (weakConst C (a₁ + ε) a₂)
        (weakConst C (a₁ - ε) a₂)) * μ E₁ ^ a₁ * μ E₂ ^ a₂ := by
  obtain ⟨ha1, -, ha2, -, -⟩ := ha
  have hamU := ham.inUstar (by linarith)
  have hεa : ε < a₁ := by linarith [hamU.1]
  have hb1 := hf₁.isBdd hf₁m
  have hb2 := hf₂.isBdd hf₂m
  have hF := hmeas f₁ f₂ hb1 hb2
  have hwp := fun t (ht : 0 < t) => weak_type_of_hullBound hsub hsmall hC0 hρ hhull hdom hmeas hap
    hE₁m hE₂m hE₁f hE₂f hf₁m hf₂m hf₁ hf₂ ht
  have hwm := fun t (ht : 0 < t) => weak_type_of_hullBound hsub hsmall hC0 hρ hhull hdom hmeas ham
    hE₁m hE₂m hE₁f hE₂f hf₁m hf₂m hf₁ hf₂ ht
  by_cases hE0 : μ E₁ = 0 ∨ μ E₂ = 0
  · -- `T(f₁,f₂) = 0` a.e.
    have hnull : ∀ t : ℝ, 0 < t → μ {x | t < ‖T f₁ f₂ x‖} = 0 := by
      intro t ht
      have h := hwp t ht
      have hR : ENNReal.ofReal (weakConst C (a₁ + ε) a₂) * μ E₁ ^ (a₁ + ε) * μ E₂ ^ a₂ = 0 := by
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
    have hKp := weakConst_nonneg hC0 (a₁ + ε) a₂
    have hKm := weakConst_nonneg hC0 (a₁ - ε) a₂
    have hwp' : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {x | t < ‖T f₁ f₂ x‖} ^ (a₁ + a₂ + ε) ≤
        ENNReal.ofReal (weakConst C (a₁ + ε) a₂ * (μ E₁).toReal ^ (a₁ + ε) *
          (μ E₂).toReal ^ a₂) := by
      intro t ht
      have h := hwp t ht
      rw [show a₁ + ε + a₂ = a₁ + a₂ + ε by ring] at h
      refine h.trans (le_of_eq ?_)
      exact (ofReal_mul_rpow_mul_rpow hE₁f hE₂f hKp (by linarith) ha2.le).symm
    have hwm' : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {x | t < ‖T f₁ f₂ x‖} ^ (a₁ + a₂ - ε) ≤
        ENNReal.ofReal (weakConst C (a₁ - ε) a₂ * (μ E₁).toReal ^ (a₁ - ε) *
          (μ E₂).toReal ^ a₂) := by
      intro t ht
      have h := hwm t ht
      rw [show a₁ - ε + a₂ = a₁ + a₂ - ε by ring] at h
      refine h.trans (le_of_eq ?_)
      exact (ofReal_mul_rpow_mul_rpow hE₁f hE₂f hKm (by linarith [hamU.1]) ha2.le).symm
    have key := eLpNorm_le_of_weak_pair hF.aestronglyMeasurable hεa ha2 hε hx₁ hx₂ hKp hKm
      hwp' hwm'
    refine key.trans (le_of_eq ?_)
    rw [← mul_assoc]
    exact ofReal_mul_rpow_mul_rpow hE₁f hE₂f
      (rsConst_nonneg (by linarith) hε (by linarith) hKp hKm) ha1.le ha2.le

/-! ### Uniform constants on compact parts of `U_*` -/

/-- Uniform bound for `weakConst` on `InReg η`, given `C ≤ K₀` on `InReg (η/2)`. -/
noncomputable def weakBound (η K₀ : ℝ) : ℝ := max (2 * K₀) (K₀ / (1 - (2 : ℝ) ^ (-(η / 2))))

lemma restrictedConst_le {C K₀ m η : ℝ} (hη : 0 < η) (hC : 0 ≤ C) (hCK : C ≤ K₀)
    (hm : η / 2 ≤ m) : restrictedConst C m ≤ K₀ / (1 - (2 : ℝ) ^ (-(η / 2))) := by
  unfold restrictedConst
  have h1 : (2 : ℝ) ^ (-(η / 2)) < 1 := by
    rw [Real.rpow_neg (by norm_num)]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by linarith))
  have h2 : (2 : ℝ) ^ (-m) ≤ (2 : ℝ) ^ (-(η / 2)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  exact div_le_div₀ (hC.trans hCK) hCK (by linarith) (by linarith)

lemma weakConst_le_weakBound {C : ℝ → ℝ → ℝ} (hC0 : ∀ b₁ b₂, 0 ≤ C b₁ b₂) {η K₀ : ℝ}
    (hη : 0 < η) (hCb : ∀ b₁ b₂, InReg (η / 2) b₁ b₂ → C b₁ b₂ ≤ K₀) {a₁ a₂ : ℝ}
    (ha : InReg η a₁ a₂) : weakConst C a₁ a₂ ≤ weakBound η K₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ha
  have hCa : C a₁ a₂ ≤ K₀ := hCb a₁ a₂ ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith⟩
  have hb2 : InReg (η / 2) a₁ (min a₂ ((1 - a₁) / 2)) := by
    refine ⟨by linarith, by linarith, ?_, ?_, ?_⟩
    · exact le_min (by linarith) (by linarith)
    · have := min_le_left a₂ ((1 - a₁) / 2)
      linarith
    · have := min_le_left a₂ ((1 - a₁) / 2)
      linarith
  have hb1 : InReg (η / 2) (min a₁ ((1 - a₂) / 2)) a₂ := by
    refine ⟨?_, ?_, by linarith, by linarith, ?_⟩
    · exact le_min (by linarith) (by linarith)
    · have := min_le_left a₁ ((1 - a₂) / 2)
      linarith
    · have := min_le_left a₁ ((1 - a₂) / 2)
      linarith
  unfold weakConst weakBound
  refine max_le (le_max_of_le_left (by linarith)) (max_le (le_max_of_le_right ?_)
    (le_max_of_le_right ?_))
  · refine restrictedConst_le hη (hC0 _ _) (hCb _ _ hb2) ?_
    exact le_min (by linarith) (le_min (by linarith) (by linarith))
  · refine restrictedConst_le hη (hC0 _ _) (hCb _ _ hb1) ?_
    exact le_min (le_min (by linarith) (by linarith)) (by linarith)

/-- **(RS), uniform constants.**  If `C ≤ K₀` on `InReg (η/4)`, then for every `a ∈ InReg η`
(and `ε = η/2`): `‖T(f₁,f₂)‖_{L^{1/(a₁+a₂)}} ≤ K · μ(E₁)^{a₁} μ(E₂)^{a₂}` with
`K = rsConst (a₁+a₂) (η/2) W W`, `W = weakBound (η/2) K₀`; on a segment `a₁ + a₂ = s` the constant
does not depend on `a`. -/
theorem eLpNorm_le_of_hullBound_of_inReg [SigmaFinite μ] {Λ : (Fin 3 → α → ℂ) → ℝ}
    {T : (α → ℂ) → (α → ℂ) → α → ℂ} {C : ℝ → ℝ → ℝ}
    (hsub : IsSubadditive Λ) (hsmall : IsSmall μ Λ) (hC0 : ∀ b₁ b₂, 0 ≤ C b₁ b₂)
    {η K₀ : ℝ} (hη : 0 < η)
    (hhull : ∀ b₁ b₂, InReg (η / 4) b₁ b₂ → HullBound μ Λ (alphaOf b₁ b₂) (C b₁ b₂))
    (hdom : IsDominated μ T Λ) (hmeas : ∀ f₁ f₂, IsBdd f₁ → IsBdd f₂ → Measurable (T f₁ f₂)) (hCb : ∀ b₁ b₂, InReg (η / 4) b₁ b₂ → C b₁ b₂ ≤ K₀)
    {a₁ a₂ : ℝ} (ha : InReg η a₁ a₂) {E₁ E₂ : Set α} (hE₁m : MeasurableSet E₁)
    (hE₂m : MeasurableSet E₂) (hE₁f : μ E₁ < ∞) (hE₂f : μ E₂ < ∞)
    {f₁ f₂ : α → ℂ} (hf₁m : Measurable f₁) (hf₂m : Measurable f₂)
    (hf₁ : DominatedBy E₁ f₁) (hf₂ : DominatedBy E₂ f₂) :
    eLpNorm (T f₁ f₂) (ENNReal.ofReal (1 / (a₁ + a₂))) μ ≤
      ENNReal.ofReal (rsConst (a₁ + a₂) (η / 2) (weakBound (η / 2) K₀)
        (weakBound (η / 2) K₀)) * μ E₁ ^ a₁ * μ E₂ ^ a₂ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ha
  have hε : 0 < η / 2 := by linarith
  have hap : InReg (η / 2) (a₁ + η / 2) a₂ := ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith⟩
  have ham : InReg (η / 2) (a₁ - η / 2) a₂ := ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith⟩
  have hCb' : ∀ b₁ b₂, InReg (η / 2 / 2) b₁ b₂ → C b₁ b₂ ≤ K₀ := fun b₁ b₂ hb =>
    hCb b₁ b₂ (by simpa [div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hb)
  have hKp := weakConst_le_weakBound hC0 hε hCb' hap
  have hKm := weakConst_le_weakBound hC0 hε hCb' ham
  have h22 : 2 * (η / 4) = η / 2 := by ring
  have key := eLpNorm_le_of_hullBound hsub hsmall hC0 (ρ := η / 4) (by linarith) hhull hdom hmeas
    (ha := (InReg.inUstar hη ⟨h1, h2, h3, h4, h5⟩)) hε (by rw [h22]; exact hap)
    (by rw [h22]; exact ham)
    hE₁m hE₂m hE₁f hE₂f hf₁m hf₂m hf₁ hf₂
  have hrs := ENNReal.ofReal_le_ofReal (rsConst_mono (s := a₁ + a₂) (ε := η / 2)
    (by linarith) hε (by linarith) (weakConst_nonneg hC0 _ _) (weakConst_nonneg hC0 _ _) hKp hKm)
  exact key.trans (mul_le_mul_left (mul_le_mul_left hrs _) _)

/-- **(RS) in the shape of the hypothesis `hRS` of `eLpNorm_le_of_restrictedStrong`** (R6c-I):
on the segment `a = (1/p₁ + t, 1/p₂ - t)`, `|t| < 2δ₀`, with `1/r = 1/p₁ + 1/p₂` fixed, the output
exponent is `r` for every `t`, with the single constant
`K = rsConst (1/r) (η/2) W W`, `W = weakBound (η/2) K₀` (`C ≤ K₀` on `InReg (η/4)`).  The
functions `g_i` are measurable (simple functions are, `SimpleFunc.measurable`). -/
theorem hRS_of_hullBound [SigmaFinite μ] {Λ : (Fin 3 → α → ℂ) → ℝ}
    {T : (α → ℂ) → (α → ℂ) → α → ℂ} {C : ℝ → ℝ → ℝ}
    (hsub : IsSubadditive Λ) (hsmall : IsSmall μ Λ) (hC0 : ∀ b₁ b₂, 0 ≤ C b₁ b₂)
    {p₁ p₂ r δ₀ η K₀ : ℝ} (hpr : 1 / r = 1 / p₁ + 1 / p₂) (hη : 0 < η)
    (hhull : ∀ b₁ b₂, InReg (η / 4) b₁ b₂ → HullBound μ Λ (alphaOf b₁ b₂) (C b₁ b₂))
    (hdom : IsDominated μ T Λ) (hmeas : ∀ f₁ f₂, IsBdd f₁ → IsBdd f₂ → Measurable (T f₁ f₂))
    (hδ₁ : η + 2 * δ₀ ≤ 1 / p₁) (hδ₂ : η + 2 * δ₀ ≤ 1 / p₂) (hδ₁' : 1 / p₁ + 2 * δ₀ ≤ 1 - η)
    (hδ₂' : 1 / p₂ + 2 * δ₀ ≤ 1 - η) (hs : 1 / r ≤ 3 / 2 - η)
    (hCb : ∀ b₁ b₂, InReg (η / 4) b₁ b₂ → C b₁ b₂ ≤ K₀) :
    ∀ t : ℝ, |t| < 2 * δ₀ → ∀ E₁ E₂ : Set α, MeasurableSet E₁ → MeasurableSet E₂ →
      μ E₁ < ∞ → μ E₂ < ∞ → ∀ g₁ g₂ : α → ℂ, Measurable g₁ → Measurable g₂ →
      (∀ x, ‖g₁ x‖ ≤ E₁.indicator (fun _ => (1 : ℝ)) x) →
      (∀ x, ‖g₂ x‖ ≤ E₂.indicator (fun _ => (1 : ℝ)) x) →
      eLpNorm (T g₁ g₂) (ENNReal.ofReal r) μ ≤
        ENNReal.ofReal (rsConst (1 / r) (η / 2) (weakBound (η / 2) K₀)
          (weakBound (η / 2) K₀)) * μ E₁ ^ (1 / p₁ + t) * μ E₂ ^ (1 / p₂ - t) := by
  intro t ht E₁ E₂ hE₁m hE₂m hE₁f hE₂f g₁ g₂ hg₁m hg₂m hg₁ hg₂
  have a1 := abs_lt.1 ht
  have hreg : InReg η (1 / p₁ + t) (1 / p₂ - t) :=
    ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have hsum : (1 / p₁ + t) + (1 / p₂ - t) = 1 / r := by linarith
  have key := eLpNorm_le_of_hullBound_of_inReg hsub hsmall hC0 hη hhull hdom hmeas hCb hreg
    hE₁m hE₂m hE₁f hE₂f hg₁m hg₂m hg₁ hg₂
  rw [hsum, one_div_one_div] at key
  exact key

/-! ### Interface with simple functions (for `Strong.lean`) -/

lemma IsBdd.of_simpleFunc (f : SimpleFunc α ℂ) : IsBdd (f : α → ℂ) := by
  obtain ⟨M, hM⟩ := f.exists_forall_norm_le
  exact ⟨f.measurable, M, hM⟩

lemma update_vec3_zero {β : Type*} (x y z w : β) : update ![x, y, z] 0 w = ![w, y, z] := by
  ext i; fin_cases i <;> simp [update]

lemma update_vec3_one {β : Type*} (x y z w : β) : update ![x, y, z] 1 w = ![x, w, z] := by
  ext i; fin_cases i <;> simp [update]

lemma update_vec3_two {β : Type*} (x y z w : β) : update ![x, y, z] 2 w = ![x, y, w] := by
  ext i; fin_cases i <;> simp [update]

/-- Slot-wise subadditivity on simple functions, in the curried form of `Strong.lean`
(`hsub₁`, `hsub₂`, `hsub₃` for `Λ' f g h := Λ ![f, g, h]`). -/
lemma IsSubadditive.sub₁ {Λ : (Fin 3 → α → ℂ) → ℝ} (hΛ : IsSubadditive Λ)
    (f f' g h : SimpleFunc α ℂ) :
    Λ ![⇑(f + f'), g, h] ≤ Λ ![f, g, h] + Λ ![f', g, h] := by
  have := hΛ ![f, g, h] 0 f f' (forall_vec3 (IsBdd.of_simpleFunc f) (IsBdd.of_simpleFunc g)
    (IsBdd.of_simpleFunc h)) (IsBdd.of_simpleFunc f) (IsBdd.of_simpleFunc f')
  rw [update_vec3_zero, update_vec3_zero, update_vec3_zero] at this
  simpa using this

lemma IsSubadditive.sub₂ {Λ : (Fin 3 → α → ℂ) → ℝ} (hΛ : IsSubadditive Λ)
    (f g g' h : SimpleFunc α ℂ) :
    Λ ![f, ⇑(g + g'), h] ≤ Λ ![f, g, h] + Λ ![f, g', h] := by
  have := hΛ ![f, g, h] 1 g g' (forall_vec3 (IsBdd.of_simpleFunc f) (IsBdd.of_simpleFunc g)
    (IsBdd.of_simpleFunc h)) (IsBdd.of_simpleFunc g) (IsBdd.of_simpleFunc g')
  rw [update_vec3_one, update_vec3_one, update_vec3_one] at this
  simpa using this

lemma IsSubadditive.sub₃ {Λ : (Fin 3 → α → ℂ) → ℝ} (hΛ : IsSubadditive Λ)
    (f g h h' : SimpleFunc α ℂ) :
    Λ ![f, g, ⇑(h + h')] ≤ Λ ![f, g, h] + Λ ![f, g, h'] := by
  have := hΛ ![f, g, h] 2 h h' (forall_vec3 (IsBdd.of_simpleFunc f) (IsBdd.of_simpleFunc g)
    (IsBdd.of_simpleFunc h)) (IsBdd.of_simpleFunc h) (IsBdd.of_simpleFunc h')
  rw [update_vec3_two, update_vec3_two, update_vec3_two] at this
  simpa using this

/-! ### The conjugate pairing `∫ T conj h`

The blueprint's `⟨T, h⟩ = ∫ T · conj h` is reduced to the bilinear pairing above by conjugating
the third slot of the form: `conjForm Λ (h₀,h₁,h₂) = Λ (h₀,h₁,conj ∘ h₂)`.  All hypotheses
(`IsSubadditive`, `IsSmall`, `HullBound`) pass from `Λ` to `conjForm Λ` unchanged (they only
involve `|h_i|`). -/

/-- Conjugate the third slot. -/
def conjSlot (h : Fin 3 → α → ℂ) : Fin 3 → α → ℂ :=
  update h 2 fun x => (starRingEnd ℂ) (h 2 x)

/-- `Λ` with the third slot conjugated. -/
def conjForm (Λ : (Fin 3 → α → ℂ) → ℝ) : (Fin 3 → α → ℂ) → ℝ := fun h => Λ (conjSlot h)

/-- The domination hypothesis for the conjugate pairing `‖∫ T(f₁,f₂) conj h‖ ≤ Λ(f₁,f₂,h)`. -/
def IsDominatedConj (μ : Measure α) (T : (α → ℂ) → (α → ℂ) → α → ℂ)
    (Λ : (Fin 3 → α → ℂ) → ℝ) : Prop :=
  ∀ f₁ f₂ h : α → ℂ, IsBdd f₁ → IsBdd f₂ → IsBdd h →
    ‖∫ x, T f₁ f₂ x * (starRingEnd ℂ) (h x) ∂μ‖ ≤ Λ ![f₁, f₂, h]

omit [MeasurableSpace α] in
lemma conjSlot_apply_of_ne {h : Fin 3 → α → ℂ} {i : Fin 3} (hi : i ≠ 2) : conjSlot h i = h i := by
  simp [conjSlot, update_of_ne hi]

omit [MeasurableSpace α] in
lemma conjSlot_apply_two (h : Fin 3 → α → ℂ) :
    conjSlot h 2 = fun x => (starRingEnd ℂ) (h 2 x) := by
  simp [conjSlot]

omit [MeasurableSpace α] in
lemma conjSlot_update (h : Fin 3 → α → ℂ) (j : Fin 3) (f : α → ℂ) :
    conjSlot (update h j f) =
      update (conjSlot h) j (if j = 2 then fun x => (starRingEnd ℂ) (f x) else f) := by
  ext i x
  fin_cases i <;> fin_cases j <;> simp [conjSlot, update]

lemma IsBdd.conj {f : α → ℂ} (hf : IsBdd f) : IsBdd fun x => (starRingEnd ℂ) (f x) := by
  obtain ⟨hm, M, hM⟩ := hf
  exact ⟨Complex.continuous_conj.measurable.comp hm, M, fun x => by simpa using hM x⟩

omit [MeasurableSpace α] in
lemma DominatedBy.conj {E : Set α} {f : α → ℂ} (hf : DominatedBy E f) :
    DominatedBy E fun x => (starRingEnd ℂ) (f x) := fun x => by simpa using hf x

lemma measurable_conj_fun {f : α → ℂ} (hf : Measurable f) :
    Measurable fun x => (starRingEnd ℂ) (f x) := Complex.continuous_conj.measurable.comp hf

lemma conjSlot_measurable {h : Fin 3 → α → ℂ} (hh : ∀ i, Measurable (h i)) :
    ∀ i, Measurable (conjSlot h i) := by
  intro i
  by_cases hi : i = 2
  · subst hi; rw [conjSlot_apply_two]; exact measurable_conj_fun (hh 2)
  · rw [conjSlot_apply_of_ne hi]; exact hh i

omit [MeasurableSpace α] in
lemma conjSlot_dominatedBy {h : Fin 3 → α → ℂ} {E : Set α} {i : Fin 3}
    (hh : DominatedBy E (h i)) : DominatedBy E (conjSlot h i) := by
  by_cases hi : i = 2
  · subst hi; rw [conjSlot_apply_two]; exact hh.conj
  · rw [conjSlot_apply_of_ne hi]; exact hh

lemma conjSlot_isBdd {h : Fin 3 → α → ℂ} (hh : ∀ i, IsBdd (h i)) : ∀ i, IsBdd (conjSlot h i) := by
  intro i
  by_cases hi : i = 2
  · subst hi; rw [conjSlot_apply_two]; exact (hh 2).conj
  · rw [conjSlot_apply_of_ne hi]; exact hh i

lemma IsSubadditive.conjForm {Λ : (Fin 3 → α → ℂ) → ℝ} (hΛ : IsSubadditive Λ) :
    IsSubadditive (conjForm Λ) := by
  intro h j f g hh hf hg
  simp only [PrimeBHT.TimeFrequency.Interp.Restricted.conjForm]
  rw [conjSlot_update, conjSlot_update, conjSlot_update]
  by_cases hj : j = 2
  · subst hj
    simp only [ite_true]
    have := hΛ (conjSlot h) 2 (fun x => (starRingEnd ℂ) (f x)) (fun x => (starRingEnd ℂ) (g x))
      (conjSlot_isBdd hh) hf.conj hg.conj
    convert this using 3
    ext x; simp
  · simp only [hj, ite_false]
    exact hΛ (conjSlot h) j f g (conjSlot_isBdd hh) hf hg

lemma IsSmall.conjForm {Λ : (Fin 3 → α → ℂ) → ℝ} (hΛ : IsSmall μ Λ) :
    IsSmall μ (conjForm Λ) := by
  obtain ⟨A, hA, hsm⟩ := hΛ
  refine ⟨A, hA, fun h S hSm hSf hhm hhd => ?_⟩
  exact hsm (conjSlot h) S hSm hSf (conjSlot_measurable hhm) fun i => conjSlot_dominatedBy (hhd i)

lemma HullBound.conjForm {Λ : (Fin 3 → α → ℂ) → ℝ} {a : Fin 3 → ℝ} {C : ℝ}
    (hΛ : HullBound μ Λ a C) : HullBound μ (conjForm Λ) a C := by
  intro E hEm hEpos hEf j hj
  obtain ⟨Et, hEtm, hEtsub, hEt2, hbd⟩ := hΛ E hEm hEpos hEf j hj
  refine ⟨Et, hEtm, hEtsub, hEt2, fun h hhm hhd hhj => ?_⟩
  exact hbd (conjSlot h) (conjSlot_measurable hhm) (fun i hi => conjSlot_dominatedBy (hhd i hi))
    (conjSlot_dominatedBy hhj)

lemma IsDominatedConj.conjForm {Λ : (Fin 3 → α → ℂ) → ℝ} {T : (α → ℂ) → (α → ℂ) → α → ℂ}
    (hT : IsDominatedConj μ T Λ) : IsDominated μ T (conjForm Λ) := by
  intro f₁ f₂ h hf₁ hf₂ hh
  have := hT f₁ f₂ (fun x => (starRingEnd ℂ) (h x)) hf₁ hf₂ hh.conj
  simp only [Complex.conj_conj] at this
  simpa [PrimeBHT.TimeFrequency.Interp.Restricted.conjForm, conjSlot, update_vec3_two] using this

end PrimeBHT.TimeFrequency.Interp.Restricted
