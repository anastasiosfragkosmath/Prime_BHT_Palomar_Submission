module

public import PrimeBHT.TimeFrequency.X2.Classes
public import PrimeBHT.TimeFrequency.X2.V16.Defs
public import PrimeBHT.TimeFrequency.X2.YVec
public import PrimeBHT.TimeFrequency.X2.ModelOpTools
import PrimeBHT.TimeFrequency.X2.ClassKernel
import PrimeBHT.TimeFrequency.X2.ClassLemmas

/-!
# X2: the model operator `B_Ps` and the structural facts V17 needs about the model form

Promoted from `drafts/x2-interface/70-ModelOperator.lean.txt` (design doc §3, "Model operator"), with every
structural lemma PROVED.

`B_Ps(F₁,F₂)(x) = Σ_P T_{conj m_{P,3}}[χ_P · w(T_{m_{P,1}}F₁, T_{m_{P,2}}F₂)](x)`, where `w(a,b) = rieszVec T a b` is
the Riesz vector of the conjugate-linear functional `Π(a,b,·)` for the normalized pairing (`Π(a,b,c) =
yPair (rieszVec T a b) c`, `yPair_rieszVec`), and `T_m^* = T_{conj m}` (`𝓕⁻ (conj m) (-w) = conj (𝓕⁻ m w)`).

## Final statements (namespace `PrimeBHT.TimeFrequency.X2`)

* `modelOp`, the predicates `IsBddV`, `IsDominatedV`, `IsBilinOpV` (the X2-side form of the hypotheses of the V17
  statement; `IsBddV f` is `Interp.IsBddV (yNorm 2) f`);
* `modelForm_eq_integral_yPair` (Fubini: `χ_P ∈ L¹`, `T_m` of bounded functions bounded, kernels integrable);
* `isSubadditiveV_modelForm`, `isSmallV_modelForm` (for `Interp.IsSubadditiveV (slotNorms u)`,
  `Interp.IsSmallV volume (slotNorms u)`; they need `1 < u` only to know `u > 0`),
  `isBilinOpV_modelOp` (the continuity field `cont` by dominated convergence with the bound
  `|T_m s_n| ≤ ‖𝓕⁻ m‖₁ sup|s_n|`), `isDominatedV_modelOp`.

All data enter through `GoodModel` (continuous bounded integrable cutoffs, good kernels), which follows from
`IsModelData` for admissible `𝔭` (`goodModel_of_isModelData`).

## Deviations from the draft

* `isSubadditiveV_modelForm`, `isSmallV_modelForm` take `hu : 1 < u` and are stated for the predicates of the V17
  chain (`Interp.IsSubadditiveV (slotNorms u)`, `Interp.IsSmallV volume (slotNorms u)`), not for the draft's own
  copies; the boundedness class of those predicates is `slotNorms`-bounded, which for fixed `P` is the same as
  coordinatewise bounded (`isBddV_iff`).
* `modelOp` is written through `modelInner` (the draft's body, abstracted).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform ComplexConjugate ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

variable {P : ℕ} [NeZero P]

/-- The vector function `χ_P · w(T_{m_{P,1}}F₁, T_{m_{P,2}}F₂)` inside the model operator. -/
def modelInner (T : Form P) (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ) (Q : TriTile)
    (F₁ F₂ : ℝ → ZMod P → ℂ) : ℝ → ZMod P → ℂ :=
  fun z => ((χ Q z : ℝ) : ℂ) • rieszVec T (tmult (m Q 0) F₁ z) (tmult (m Q 1) F₂ z)

/-- **The model operator** `B_Ps(F₁,F₂) = Σ_P T_{conj m_{P,3}}[χ_P · rieszVec(T_{m_{P,1}}F₁, T_{m_{P,2}}F₂)]`. -/
def modelOp (T : Form P) (Ps : Finset TriTile) (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ)
    (F₁ F₂ : ℝ → ZMod P → ℂ) : ℝ → ZMod P → ℂ :=
  fun x => ∑ Q ∈ Ps, tmult (fun ξ => conj (m Q 2 ξ)) (modelInner T χ m Q F₁ F₂) x

/-- Bounded measurable vector functions (the test class of the interpolation chain, `yNorm 2`-bounded). -/
def IsBddV (f : ℝ → ZMod P → ℂ) : Prop := Measurable f ∧ ∃ M : ℝ, ∀ x, yNorm 2 (f x) ≤ M

theorem isBddV_iff_isBddC {f : ℝ → ZMod P → ℂ} : IsBddV f ↔ IsBddC f :=
  isBddV_iff (by norm_num : (0 : ℝ) < 2)

/-- `|∫ ⟨B(f,g), h⟩_Y| ≤ Λ(f, g, h)` for bounded measurable `f, g, h`. -/
def IsDominatedV (B : (ℝ → ZMod P → ℂ) → (ℝ → ZMod P → ℂ) → ℝ → ZMod P → ℂ)
    (Λ : (Fin 3 → ℝ → ZMod P → ℂ) → ℝ) : Prop :=
  ∀ f g h : ℝ → ZMod P → ℂ, IsBddV f → IsBddV g → IsBddV h →
    ‖∫ x, yPair (B f g x) (h x)‖ ≤ Λ ![f, g, h]

/-- `B` is complex-bilinear on bounded measurable inputs, has measurable outputs, and is continuous
along dominated pointwise approximations (the hypothesis `hcont` of X1's Corollary (MB)). -/
structure IsBilinOpV (B : (ℝ → ZMod P → ℂ) → (ℝ → ZMod P → ℂ) → ℝ → ZMod P → ℂ) : Prop where
  add₁ : ∀ f f' g, IsBddV f → IsBddV f' → IsBddV g → B (f + f') g = B f g + B f' g
  smul₁ : ∀ (c : ℂ) f g, IsBddV f → IsBddV g → B (c • f) g = c • B f g
  add₂ : ∀ f g g', IsBddV f → IsBddV g → IsBddV g' → B f (g + g') = B f g + B f g'
  smul₂ : ∀ (c : ℂ) f g, IsBddV f → IsBddV g → B f (c • g) = c • B f g
  meas : ∀ f g, IsBddV f → IsBddV g → Measurable (B f g)
  cont : ∀ (F₁ F₂ : ℝ → ZMod P → ℂ) (s₁ s₂ : ℕ → ℝ → ZMod P → ℂ), IsBddV F₁ → IsBddV F₂ →
    (∀ n, IsBddV (s₁ n)) → (∀ n, IsBddV (s₂ n)) →
    (∀ n x, yNorm 2 (s₁ n x) ≤ 2 * yNorm 2 (F₁ x)) → (∀ n x, yNorm 2 (s₂ n x) ≤ 2 * yNorm 2 (F₂ x)) →
    (∀ x, Filter.Tendsto (fun n => s₁ n x) Filter.atTop (nhds (F₁ x))) →
    (∀ x, Filter.Tendsto (fun n => s₂ n x) Filter.atTop (nhds (F₂ x))) →
    ∀ᵐ x, Filter.Tendsto (fun n => B (s₁ n) (s₂ n) x) Filter.atTop (nhds (B F₁ F₂ x))

/-! ### The data: continuous bounded integrable cutoffs, good kernels -/

/-- The analytic content of `IsModelData` used below. -/
structure GoodModel (Ps : Finset TriTile) (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ) : Prop where
  cont : ∀ Q ∈ Ps, Continuous (χ Q)
  bdd : ∀ Q ∈ Ps, ∃ C : ℝ, ∀ x, |χ Q x| ≤ C
  integrable : ∀ Q ∈ Ps, Integrable (fun x => ((χ Q x : ℝ) : ℂ))
  kernel : ∀ Q ∈ Ps, ∀ k, GoodKernel (m Q k)

theorem goodModel_of_isModelData {𝔭 : Params} (h𝔭 : 𝔭.Admissible) {Ps : Finset TriTile}
    {χ : TriTile → ℝ → ℝ} {m : TriTile → Fin 3 → ℝ → ℂ} (hd : IsModelData 𝔭 Ps χ m) :
    GoodModel Ps χ m := by
  obtain ⟨hN, hD, hβ, hC⟩ := h𝔭.bounds
  have hψ : ∀ Q ∈ Ps, Continuous (fun x => ((χ Q x : ℝ) : ℂ)) ∧
      ∀ x, ‖((χ Q x : ℝ) : ℂ)‖ ≤ 𝔭.C * jb ((x - dyCentre Q.box.scale Q.pos) / (2 : ℝ) ^ Q.box.scale) ^
        (-(𝔭.N : ℝ)) := fun Q hQ =>
    ⟨(hd.1 Q hQ).1.1.1, (hd.1 Q hQ).1.1.2.1⟩
  have hcont : ∀ Q ∈ Ps, Continuous (χ Q) := fun Q hQ =>
    (Complex.continuous_re.comp (hψ Q hQ).1).congr fun x => by simp
  refine ⟨hcont, fun Q hQ => ⟨𝔭.C, fun x => ?_⟩, fun Q hQ => ?_, fun Q hQ k => ?_⟩
  · have h1 := (hψ Q hQ).2 x
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    refine h1.trans ?_
    have h2 : jb ((x - dyCentre Q.box.scale Q.pos) / (2 : ℝ) ^ Q.box.scale) ^ (-(𝔭.N : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (one_le_jb _) (by simp)
    nlinarith
  · have hL : (0 : ℝ) < (2 : ℝ) ^ Q.box.scale := zpow_pos (by norm_num) _
    have hint := (integrable_jb_rpow (c := dyCentre Q.box.scale Q.pos) hL (r := (𝔭.N : ℝ))
      (by have : (400 : ℝ) ≤ 𝔭.N := by exact_mod_cast hN
          linarith)).const_mul 𝔭.C
    exact hint.mono' (Complex.continuous_ofReal.comp (hcont Q hQ)).aestronglyMeasurable
      (Eventually.of_forall fun x => (hψ Q hQ).2 x)
  · exact goodKernel_of_inMult h𝔭 ((hd.1 Q hQ).2 k)

/-! ### Closure properties -/

section Closure

variable {T : Form P} {Ps : Finset TriTile} {χ : TriTile → ℝ → ℝ} {m : TriTile → Fin 3 → ℝ → ℂ}
  {Q : TriTile}

theorem GoodModel.measurable_χ (hg : GoodModel Ps χ m) (hQ : Q ∈ Ps) : Measurable (χ Q) :=
  (hg.cont Q hQ).measurable

theorem GoodModel.measurable_χC (hg : GoodModel Ps χ m) (hQ : Q ∈ Ps) :
    Measurable (fun x => ((χ Q x : ℝ) : ℂ)) :=
  Complex.measurable_ofReal.comp (hg.measurable_χ hQ)

theorem isBddC_modelInner (hg : GoodModel Ps χ m) (hQ : Q ∈ Ps) {F₁ F₂ : ℝ → ZMod P → ℂ}
    (h₁ : IsBddC F₁) (h₂ : IsBddC F₂) : IsBddC (modelInner T χ m Q F₁ F₂) := by
  have ha := IsBddC.tmult (hg.kernel Q hQ 0) h₁
  have hb := IsBddC.tmult (hg.kernel Q hQ 1) h₂
  obtain ⟨A, hA0, hA⟩ := ha.nonneg_bound
  obtain ⟨B, hB0, hB⟩ := hb.nonneg_bound
  obtain ⟨Cχ, hCχ⟩ := hg.bdd Q hQ
  have hCχ0 : 0 ≤ Cχ := (abs_nonneg _).trans (hCχ 0)
  refine ⟨fun y => ?_, Cχ * (rieszBound T * (A * B)), fun x y => ?_⟩
  · exact (hg.measurable_χC hQ).mul (measurable_rieszVec T ha.1 hb.1 y)
  · simp only [modelInner, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hCχ x) (norm_rieszVec_le T hA0 hB0 (hA x) (hB x) y) (norm_nonneg _) hCχ0

theorem isBddC_modelOp (hg : GoodModel Ps χ m) {F₁ F₂ : ℝ → ZMod P → ℂ} (h₁ : IsBddC F₁)
    (h₂ : IsBddC F₂) : IsBddC (modelOp T Ps χ m F₁ F₂) :=
  IsBddC.sum Ps fun Q hQ => IsBddC.tmult (hg.kernel Q hQ 2).conj (isBddC_modelInner hg hQ h₁ h₂)

/-- Each integrand of the model form is integrable. -/
theorem integrable_modelIntegrand (hg : GoodModel Ps χ m) (hQ : Q ∈ Ps) {F₁ F₂ F₃ : ℝ → ZMod P → ℂ}
    (h₁ : IsBddC F₁) (h₂ : IsBddC F₂) (h₃ : IsBddC F₃) :
    Integrable (fun x => ((χ Q x : ℝ) : ℂ) *
      T (tmult (m Q 0) F₁ x) (tmult (m Q 1) F₂ x) (tmult (m Q 2) F₃ x)) := by
  have ha := IsBddC.tmult (hg.kernel Q hQ 0) h₁
  have hb := IsBddC.tmult (hg.kernel Q hQ 1) h₂
  have hc := IsBddC.tmult (hg.kernel Q hQ 2) h₃
  obtain ⟨A, hA0, hA⟩ := ha.nonneg_bound
  obtain ⟨B, hB0, hB⟩ := hb.nonneg_bound
  obtain ⟨C, hC0, hC⟩ := hc.nonneg_bound
  refine (hg.integrable Q hQ).mul_bdd (c := rieszBound T * (A * B) * C)
    (measurable_T T ha.1 hb.1 hc.1).aestronglyMeasurable
    (Eventually.of_forall fun x => norm_T_le T hA0 hB0 (hA x) (hB x) (hC x))

/-- Each coordinate of `χ_P · w(T_{m_{P,1}}F₁, T_{m_{P,2}}F₂)` is integrable. -/
theorem integrable_modelInner_coord (hg : GoodModel Ps χ m) (hQ : Q ∈ Ps) {F₁ F₂ : ℝ → ZMod P → ℂ}
    (h₁ : IsBddC F₁) (h₂ : IsBddC F₂) (y : ZMod P) :
    Integrable (fun x => modelInner T χ m Q F₁ F₂ x y) := by
  have ha := IsBddC.tmult (hg.kernel Q hQ 0) h₁
  have hb := IsBddC.tmult (hg.kernel Q hQ 1) h₂
  obtain ⟨A, hA0, hA⟩ := ha.nonneg_bound
  obtain ⟨B, hB0, hB⟩ := hb.nonneg_bound
  have := (hg.integrable Q hQ).mul_bdd (c := rieszBound T * (A * B))
    (measurable_rieszVec T ha.1 hb.1 y).aestronglyMeasurable
    (Eventually.of_forall fun x => norm_rieszVec_le T hA0 hB0 (hA x) (hB x) y)
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp [modelInner]

/-- **Fubini for one tile**: the `Q`-term of the model form is the pairing of the `Q`-term of the model operator
with `F₃`, and both integrands are integrable. -/
theorem integral_modelIntegrand_eq (hg : GoodModel Ps χ m) (hQ : Q ∈ Ps) {F₁ F₂ F₃ : ℝ → ZMod P → ℂ}
    (h₁ : IsBddC F₁) (h₂ : IsBddC F₂) (h₃ : IsBddC F₃) :
    Integrable (fun z => yPair (tmult (fun ξ => conj (m Q 2 ξ)) (modelInner T χ m Q F₁ F₂) z) (F₃ z)) ∧
    ∫ x, ((χ Q x : ℝ) : ℂ) * T (tmult (m Q 0) F₁ x) (tmult (m Q 1) F₂ x) (tmult (m Q 2) F₃ x) =
      ∫ z, yPair (tmult (fun ξ => conj (m Q 2 ξ)) (modelInner T χ m Q F₁ F₂) z) (F₃ z) := by
  have hGint : ∀ y, Integrable (fun x => modelInner T χ m Q F₁ F₂ x y) :=
    integrable_modelInner_coord hg hQ h₁ h₂
  have hK := hg.kernel Q hQ 2
  have hκ : Integrable (fun w => conj (𝓕⁻ (m Q 2) w)) := integrable_conj_fun hK.integrable
  obtain ⟨C₃, hC3⟩ := h₃.2
  have hA : ∀ y, Integrable (fun x => modelInner T χ m Q F₁ F₂ x y *
        ∫ z, conj (𝓕⁻ (m Q 2) (x - z)) * conj (F₃ z y)) ∧
      Integrable (fun z => (∫ x, conj (𝓕⁻ (m Q 2) (x - z)) * modelInner T χ m Q F₁ F₂ x y) *
        conj (F₃ z y)) ∧
      ∫ x, modelInner T χ m Q F₁ F₂ x y * ∫ z, conj (𝓕⁻ (m Q 2) (x - z)) * conj (F₃ z y) =
        ∫ z, (∫ x, conj (𝓕⁻ (m Q 2) (x - z)) * modelInner T χ m Q F₁ F₂ x y) * conj (F₃ z y) :=
    fun y => adjoint_scalar (hGint y) hκ (Complex.continuous_conj.measurable.comp (h₃.1 y)) (C := C₃)
      (fun z => by rw [Complex.norm_conj]; exact hC3 z y)
  have E1 : ∀ x y, conj (tmult (m Q 2) F₃ x y) = ∫ z, conj (𝓕⁻ (m Q 2) (x - z)) * conj (F₃ z y) := by
    intro x y
    rw [tmult_apply, ← integral_conj]
    simp only [map_mul]
  have E2 : ∀ z y, tmult (fun ξ => conj (m Q 2 ξ)) (modelInner T χ m Q F₁ F₂) z y =
      ∫ x, conj (𝓕⁻ (m Q 2) (x - z)) * modelInner T χ m Q F₁ F₂ x y := by
    intro z y
    rw [tmult_apply]
    congr 1; ext x
    rw [fourierInv_conj, neg_sub]
  have hpt : ∀ x, ((χ Q x : ℝ) : ℂ) * T (tmult (m Q 0) F₁ x) (tmult (m Q 1) F₂ x) (tmult (m Q 2) F₃ x) =
      (P : ℂ)⁻¹ * ∑ y, modelInner T χ m Q F₁ F₂ x y * conj (tmult (m Q 2) F₃ x y) := by
    intro x
    rw [T_eq_yPair, ← yPair_smul_left]
    rfl
  have hint1 : ∀ y, Integrable (fun x => modelInner T χ m Q F₁ F₂ x y * conj (tmult (m Q 2) F₃ x y)) := by
    intro y
    refine (hA y).1.congr (Eventually.of_forall fun x => ?_)
    simp only [E1]
  have hint2 : ∀ y, Integrable (fun z => tmult (fun ξ => conj (m Q 2 ξ)) (modelInner T χ m Q F₁ F₂) z y *
      conj (F₃ z y)) := by
    intro y
    refine (hA y).2.1.congr (Eventually.of_forall fun z => ?_)
    simp only [E2]
  refine ⟨?_, ?_⟩
  · have := (integrable_finsetSum (Finset.univ : Finset (ZMod P)) fun y _ => hint2 y).const_mul
      ((P : ℂ)⁻¹)
    simpa only [yPair] using this
  · simp_rw [hpt]
    unfold yPair
    rw [integral_const_mul, integral_const_mul, integral_finsetSum _ fun y _ => hint1 y,
      integral_finsetSum _ fun y _ => hint2 y]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    have := (hA y).2.2
    simp only [E1, E2]
    exact this

/-- The model form is the pairing of the model operator with the third function (Fubini; all three functions
bounded measurable, `χ_P` integrable, kernels integrable and bounded). -/
theorem modelForm_eq_integral_yPair_of_goodModel (hg : GoodModel Ps χ m) {F₁ F₂ F₃ : ℝ → ZMod P → ℂ}
    (h₁ : IsBddC F₁) (h₂ : IsBddC F₂) (h₃ : IsBddC F₃) :
    modelForm T Ps χ m F₁ F₂ F₃ = ∫ x, yPair (modelOp T Ps χ m F₁ F₂ x) (F₃ x) := by
  have key : ∀ Q ∈ Ps, Integrable (fun z => yPair (tmult (fun ξ => conj (m Q 2 ξ))
      (modelInner T χ m Q F₁ F₂) z) (F₃ z)) := fun Q hQ =>
    (integral_modelIntegrand_eq (T := T) hg hQ h₁ h₂ h₃).1
  have hsum : ∀ x, yPair (modelOp T Ps χ m F₁ F₂ x) (F₃ x) = ∑ Q ∈ Ps,
      yPair (tmult (fun ξ => conj (m Q 2 ξ)) (modelInner T χ m Q F₁ F₂) x) (F₃ x) := fun x =>
    yPair_sum_left Ps _ _
  simp_rw [hsum]
  rw [integral_finsetSum _ key]
  unfold modelForm
  exact Finset.sum_congr rfl fun Q hQ => (integral_modelIntegrand_eq (T := T) hg hQ h₁ h₂ h₃).2

/-- The model form is the pairing of the model operator with the third function (Fubini; all three
functions bounded measurable, `χ_P` integrable, kernels Schwartz). -/
theorem modelForm_eq_integral_yPair (𝔭 : Params) (h𝔭 : 𝔭.Admissible) (T : Form P) (Ps : Finset TriTile)
    (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ) (hd : IsModelData 𝔭 Ps χ m)
    (F₁ F₂ F₃ : ℝ → ZMod P → ℂ) (h₁ : IsBddV F₁) (h₂ : IsBddV F₂) (h₃ : IsBddV F₃) :
    modelForm T Ps χ m F₁ F₂ F₃ = ∫ x, yPair (modelOp T Ps χ m F₁ F₂ x) (F₃ x) :=
  modelForm_eq_integral_yPair_of_goodModel (goodModel_of_isModelData h𝔭 hd)
    (isBddV_iff_isBddC.1 h₁) (isBddV_iff_isBddC.1 h₂) (isBddV_iff_isBddC.1 h₃)

/-- From `modelForm_eq_integral_yPair` (equality, so the domination is `≤` by `le_of_eq`). -/
theorem isDominatedV_modelOp (𝔭 : Params) (h𝔭 : 𝔭.Admissible) (T : Form P) (Ps : Finset TriTile)
    (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ) (hd : IsModelData 𝔭 Ps χ m) :
    IsDominatedV (modelOp T Ps χ m) (fun h => ‖modelForm T Ps χ m (h 0) (h 1) (h 2)‖) := by
  intro f g h hf hg hh
  show _ ≤ ‖modelForm T Ps χ m f g h‖
  rw [modelForm_eq_integral_yPair 𝔭 h𝔭 T Ps χ m hd _ _ _ hf hg hh]

end Closure

/-! ### Bilinearity and continuity of the model operator -/

section Bilinear

variable {T : Form P} {Ps : Finset TriTile} {χ : TriTile → ℝ → ℝ} {m : TriTile → Fin 3 → ℝ → ℂ}
  {Q : TriTile} {F₁ F₁' F₂ F₂' : ℝ → ZMod P → ℂ}

omit [NeZero P] in
theorem modelInner_add_left (hg : GoodModel Ps χ m) (hQ : Q ∈ Ps) (h₁ : IsBddC F₁) (h₁' : IsBddC F₁') :
    modelInner T χ m Q (F₁ + F₁') F₂ = modelInner T χ m Q F₁ F₂ + modelInner T χ m Q F₁' F₂ := by
  funext z
  simp only [modelInner, tmult_add (hg.kernel Q hQ 0) h₁ h₁', Pi.add_apply, rieszVec_add_left,
    smul_add]

omit [NeZero P] in
theorem modelInner_add_right (hg : GoodModel Ps χ m) (hQ : Q ∈ Ps) (h₂ : IsBddC F₂) (h₂' : IsBddC F₂') :
    modelInner T χ m Q F₁ (F₂ + F₂') = modelInner T χ m Q F₁ F₂ + modelInner T χ m Q F₁ F₂' := by
  funext z
  simp only [modelInner, tmult_add (hg.kernel Q hQ 1) h₂ h₂', Pi.add_apply, rieszVec_add_right,
    smul_add]

omit [NeZero P] in
theorem modelInner_smul_left (c : ℂ) (F₁ F₂ : ℝ → ZMod P → ℂ) :
    modelInner T χ m Q (c • F₁) F₂ = c • modelInner T χ m Q F₁ F₂ := by
  funext z
  simp only [modelInner, tmult_smul, Pi.smul_apply, rieszVec_smul_left, smul_comm _ c]

omit [NeZero P] in
theorem modelInner_smul_right (c : ℂ) (F₁ F₂ : ℝ → ZMod P → ℂ) :
    modelInner T χ m Q F₁ (c • F₂) = c • modelInner T χ m Q F₁ F₂ := by
  funext z
  simp only [modelInner, tmult_smul, Pi.smul_apply, rieszVec_smul_right, smul_comm _ c]

theorem modelOp_add_left (hg : GoodModel Ps χ m) (h₁ : IsBddC F₁) (h₁' : IsBddC F₁') (h₂ : IsBddC F₂) :
    modelOp T Ps χ m (F₁ + F₁') F₂ = modelOp T Ps χ m F₁ F₂ + modelOp T Ps χ m F₁' F₂ := by
  funext x
  simp only [modelOp, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [modelInner_add_left hg hQ h₁ h₁', tmult_add (hg.kernel Q hQ 2).conj
    (isBddC_modelInner hg hQ h₁ h₂) (isBddC_modelInner hg hQ h₁' h₂)]
  rfl

theorem modelOp_add_right (hg : GoodModel Ps χ m) (h₁ : IsBddC F₁) (h₂ : IsBddC F₂) (h₂' : IsBddC F₂') :
    modelOp T Ps χ m F₁ (F₂ + F₂') = modelOp T Ps χ m F₁ F₂ + modelOp T Ps χ m F₁ F₂' := by
  funext x
  simp only [modelOp, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [modelInner_add_right hg hQ h₂ h₂', tmult_add (hg.kernel Q hQ 2).conj
    (isBddC_modelInner hg hQ h₁ h₂) (isBddC_modelInner hg hQ h₁ h₂')]
  rfl

omit [NeZero P] in
theorem modelOp_smul_left (c : ℂ) (F₁ F₂ : ℝ → ZMod P → ℂ) :
    modelOp T Ps χ m (c • F₁) F₂ = c • modelOp T Ps χ m F₁ F₂ := by
  funext x
  simp only [modelOp, Pi.smul_apply, modelInner_smul_left, tmult_smul, Finset.smul_sum]

omit [NeZero P] in
theorem modelOp_smul_right (c : ℂ) (F₁ F₂ : ℝ → ZMod P → ℂ) :
    modelOp T Ps χ m F₁ (c • F₂) = c • modelOp T Ps χ m F₁ F₂ := by
  funext x
  simp only [modelOp, Pi.smul_apply, modelInner_smul_right, tmult_smul, Finset.smul_sum]

/-- Dominated convergence for the model operator. -/
theorem tendsto_modelOp (hg : GoodModel Ps χ m) {s₁ s₂ : ℕ → ℝ → ZMod P → ℂ} {F₁ F₂ : ℝ → ZMod P → ℂ}
    (hs₁ : ∀ n, IsBddC (s₁ n)) (hs₂ : ∀ n, IsBddC (s₂ n)) {M₁ M₂ : ℝ}
    (hb₁ : ∀ n z y, ‖s₁ n z y‖ ≤ M₁) (hb₂ : ∀ n z y, ‖s₂ n z y‖ ≤ M₂)
    (hl₁ : ∀ z y, Tendsto (fun n => s₁ n z y) atTop (𝓝 (F₁ z y)))
    (hl₂ : ∀ z y, Tendsto (fun n => s₂ n z y) atTop (𝓝 (F₂ z y))) (x : ℝ) :
    Tendsto (fun n => modelOp T Ps χ m (s₁ n) (s₂ n) x) atTop (𝓝 (modelOp T Ps χ m F₁ F₂ x)) := by
  have hM₁ : 0 ≤ M₁ := (norm_nonneg _).trans (hb₁ 0 0 0)
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans (hb₂ 0 0 0)
  unfold modelOp
  refine tendsto_finsetSum _ fun Q hQ => ?_
  have hK0 := hg.kernel Q hQ 0
  have hK1 := hg.kernel Q hQ 1
  have hlA : ∀ z, Tendsto (fun n => tmult (m Q 0) (s₁ n) z) atTop (𝓝 (tmult (m Q 0) F₁ z)) :=
    fun z => tendsto_tmult hK0 (fun n y => (hs₁ n).1 y) hb₁ hl₁ z
  have hlB : ∀ z, Tendsto (fun n => tmult (m Q 1) (s₂ n) z) atTop (𝓝 (tmult (m Q 1) F₂ z)) :=
    fun z => tendsto_tmult hK1 (fun n y => (hs₂ n).1 y) hb₂ hl₂ z
  have hA0 : 0 ≤ kerNorm (m Q 0) * M₁ := mul_nonneg (kerNorm_nonneg _) hM₁
  have hB0 : 0 ≤ kerNorm (m Q 1) * M₂ := mul_nonneg (kerNorm_nonneg _) hM₂
  obtain ⟨Cχ, hCχ⟩ := hg.bdd Q hQ
  refine tendsto_tmult (hg.kernel Q hQ 2).conj
    (M := Cχ * (rieszBound T * ((kerNorm (m Q 0) * M₁) * (kerNorm (m Q 1) * M₂)))) ?_ ?_ ?_ x
  · exact fun n y => (isBddC_modelInner (T := T) hg hQ (hs₁ n) (hs₂ n)).1 y
  · intro n z y
    have hCχ0 : 0 ≤ Cχ := (abs_nonneg _).trans (hCχ 0)
    simp only [modelInner, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hCχ z) (norm_rieszVec_le T hA0 hB0 (fun i => norm_tmult_le hK0 (hb₁ n) z i)
      (fun i => norm_tmult_le hK1 (hb₂ n) z i) y) (norm_nonneg _) hCχ0
  · intro z y
    simp only [modelInner, Pi.smul_apply, smul_eq_mul]
    exact (tendsto_rieszVec T (fun i => tendsto_pi_nhds.1 (hlA z) i)
      (fun j => tendsto_pi_nhds.1 (hlB z) j) y).const_mul _

theorem isBilinOpV_modelOp (𝔭 : Params) (h𝔭 : 𝔭.Admissible) (T : Form P) (Ps : Finset TriTile)
    (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ) (hd : IsModelData 𝔭 Ps χ m) :
    IsBilinOpV (modelOp T Ps χ m) := by
  have hg := goodModel_of_isModelData h𝔭 hd
  refine ⟨fun f f' g hf hf' hg' => modelOp_add_left hg (isBddV_iff_isBddC.1 hf)
      (isBddV_iff_isBddC.1 hf') (isBddV_iff_isBddC.1 hg'),
    fun c f g _ _ => modelOp_smul_left c f g,
    fun f g g' hf hg' hg'' => modelOp_add_right hg (isBddV_iff_isBddC.1 hf)
      (isBddV_iff_isBddC.1 hg') (isBddV_iff_isBddC.1 hg''),
    fun c f g _ _ => modelOp_smul_right c f g,
    fun f g hf hg' => (isBddC_modelOp hg (isBddV_iff_isBddC.1 hf) (isBddV_iff_isBddC.1 hg')).measurable,
    ?_⟩
  intro F₁ F₂ s₁ s₂ h₁ h₂ hs₁ hs₂ hb₁ hb₂ hl₁ hl₂
  refine Eventually.of_forall fun x => ?_
  obtain ⟨N₁, hN₁⟩ := h₁.2
  obtain ⟨N₂, hN₂⟩ := h₂.2
  have hPs : (0 : ℝ) ≤ (P : ℝ) ^ (2 : ℝ)⁻¹ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine tendsto_modelOp hg (fun n => isBddV_iff_isBddC.1 (hs₁ n)) (fun n => isBddV_iff_isBddC.1 (hs₂ n))
    (M₁ := (P : ℝ) ^ (2 : ℝ)⁻¹ * (2 * N₁)) (M₂ := (P : ℝ) ^ (2 : ℝ)⁻¹ * (2 * N₂))
    (fun n z y => ?_) (fun n z y => ?_) (fun z y => tendsto_pi_nhds.1 (hl₁ z) y)
    (fun z y => tendsto_pi_nhds.1 (hl₂ z) y) x
  · refine (norm_apply_le_rpow_mul_yNorm (s := 2) (by norm_num) (s₁ n z) y).trans ?_
    exact mul_le_mul_of_nonneg_left ((hb₁ n z).trans (by linarith [hN₁ z])) hPs
  · refine (norm_apply_le_rpow_mul_yNorm (s := 2) (by norm_num) (s₂ n z) y).trans ?_
    exact mul_le_mul_of_nonneg_left ((hb₂ n z).trans (by linarith [hN₂ z])) hPs

end Bilinear

/-! ### Additivity and smallness of the model form -/

section FormProps

variable {T : Form P} {Ps : Finset TriTile} {χ : TriTile → ℝ → ℝ} {m : TriTile → Fin 3 → ℝ → ℂ}
  {F₁ F₁' F₂ F₂' F₃ F₃' : ℝ → ZMod P → ℂ}

theorem modelForm_add₁ (hg : GoodModel Ps χ m) (h₁ : IsBddC F₁) (h₁' : IsBddC F₁') (h₂ : IsBddC F₂)
    (h₃ : IsBddC F₃) :
    modelForm T Ps χ m (F₁ + F₁') F₂ F₃ = modelForm T Ps χ m F₁ F₂ F₃ + modelForm T Ps χ m F₁' F₂ F₃ := by
  unfold modelForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [← integral_add (integrable_modelIntegrand hg hQ h₁ h₂ h₃)
    (integrable_modelIntegrand hg hQ h₁' h₂ h₃)]
  congr 1; ext x
  rw [tmult_add (hg.kernel Q hQ 0) h₁ h₁']
  simp only [Pi.add_apply, map_add, LinearMap.add_apply, mul_add]

theorem modelForm_add₂ (hg : GoodModel Ps χ m) (h₁ : IsBddC F₁) (h₂ : IsBddC F₂) (h₂' : IsBddC F₂')
    (h₃ : IsBddC F₃) :
    modelForm T Ps χ m F₁ (F₂ + F₂') F₃ = modelForm T Ps χ m F₁ F₂ F₃ + modelForm T Ps χ m F₁ F₂' F₃ := by
  unfold modelForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [← integral_add (integrable_modelIntegrand hg hQ h₁ h₂ h₃)
    (integrable_modelIntegrand hg hQ h₁ h₂' h₃)]
  congr 1; ext x
  rw [tmult_add (hg.kernel Q hQ 1) h₂ h₂']
  simp only [Pi.add_apply, map_add, LinearMap.add_apply, mul_add]

theorem modelForm_add₃ (hg : GoodModel Ps χ m) (h₁ : IsBddC F₁) (h₂ : IsBddC F₂) (h₃ : IsBddC F₃)
    (h₃' : IsBddC F₃') :
    modelForm T Ps χ m F₁ F₂ (F₃ + F₃') = modelForm T Ps χ m F₁ F₂ F₃ + modelForm T Ps χ m F₁ F₂ F₃' := by
  unfold modelForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [← integral_add (integrable_modelIntegrand hg hQ h₁ h₂ h₃)
    (integrable_modelIntegrand hg hQ h₁ h₂ h₃')]
  congr 1; ext x
  rw [tmult_add (hg.kernel Q hQ 2) h₃ h₃']
  simp only [Pi.add_apply, map_add, mul_add]

theorem slotExp_pos {u : ℝ} (hu : 1 < u) (i : Fin 3) : 0 < slotExp u i := by
  fin_cases i <;> simp [slotExp]; linarith

theorem isSubadditiveV_modelForm {u : ℝ} (hu : 1 < u) (𝔭 : Params) (h𝔭 : 𝔭.Admissible) (T : Form P)
    (Ps : Finset TriTile) (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ)
    (hd : IsModelData 𝔭 Ps χ m) :
    Interp.IsSubadditiveV (slotNorms u) (fun h => ‖modelForm T Ps χ m (h 0) (h 1) (h 2)‖) := by
  have hg := goodModel_of_isModelData h𝔭 hd
  intro h j f g hh hf hf'
  have hh' : ∀ i, IsBddC (h i) := fun i => (isBddV_iff (slotExp_pos hu i)).1 (hh i)
  have hf1 : IsBddC f := (isBddV_iff (slotExp_pos hu j)).1 hf
  have hg1 : IsBddC g := (isBddV_iff (slotExp_pos hu j)).1 hf'
  fin_cases j
  · show ‖modelForm T Ps χ m (Function.update h 0 (f + g) 0) (Function.update h 0 (f + g) 1)
        (Function.update h 0 (f + g) 2)‖ ≤ ‖modelForm T Ps χ m (Function.update h 0 f 0)
        (Function.update h 0 f 1) (Function.update h 0 f 2)‖ +
        ‖modelForm T Ps χ m (Function.update h 0 g 0) (Function.update h 0 g 1) (Function.update h 0 g 2)‖
    simp only [Function.update_self, Function.update_of_ne (show (1 : Fin 3) ≠ 0 by decide),
      Function.update_of_ne (show (2 : Fin 3) ≠ 0 by decide)]
    rw [modelForm_add₁ hg hf1 hg1 (hh' 1) (hh' 2)]
    exact norm_add_le _ _
  · show ‖modelForm T Ps χ m (Function.update h 1 (f + g) 0) (Function.update h 1 (f + g) 1)
        (Function.update h 1 (f + g) 2)‖ ≤ ‖modelForm T Ps χ m (Function.update h 1 f 0)
        (Function.update h 1 f 1) (Function.update h 1 f 2)‖ +
        ‖modelForm T Ps χ m (Function.update h 1 g 0) (Function.update h 1 g 1) (Function.update h 1 g 2)‖
    simp only [Function.update_self, Function.update_of_ne (show (0 : Fin 3) ≠ 1 by decide),
      Function.update_of_ne (show (2 : Fin 3) ≠ 1 by decide)]
    rw [modelForm_add₂ hg (hh' 0) hf1 hg1 (hh' 2)]
    exact norm_add_le _ _
  · show ‖modelForm T Ps χ m (Function.update h 2 (f + g) 0) (Function.update h 2 (f + g) 1)
        (Function.update h 2 (f + g) 2)‖ ≤ ‖modelForm T Ps χ m (Function.update h 2 f 0)
        (Function.update h 2 f 1) (Function.update h 2 f 2)‖ +
        ‖modelForm T Ps χ m (Function.update h 2 g 0) (Function.update h 2 g 1) (Function.update h 2 g 2)‖
    simp only [Function.update_self, Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide),
      Function.update_of_ne (show (1 : Fin 3) ≠ 2 by decide)]
    rw [modelForm_add₃ hg (hh' 0) (hh' 1) hf1 hg1]
    exact norm_add_le _ _

/-- Coordinates of a `slotNorms`-dominated function: `‖h z y‖ ≤ 1_S z · P^{1/s}`. -/
theorem coord_le_of_vDominated {s : ℝ} (hs : 0 < s) {h : ℝ → ZMod P → ℂ} {S : Set ℝ}
    (hdom : Interp.VDominatedBy (yNorm s) S h) (z : ℝ) (y : ZMod P) :
    ‖h z y‖ ≤ S.indicator (fun _ => (P : ℝ) ^ s⁻¹) z := by
  have h1 := hdom z
  have h2 := norm_apply_le_rpow_mul_yNorm hs (h z) y
  have hP : (0 : ℝ) ≤ (P : ℝ) ^ s⁻¹ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  by_cases hz : z ∈ S
  · rw [Set.indicator_of_mem hz] at h1 ⊢
    calc ‖h z y‖ ≤ (P : ℝ) ^ s⁻¹ * yNorm s (h z) := h2
      _ ≤ (P : ℝ) ^ s⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 hP
      _ = _ := mul_one _
  · rw [Set.indicator_of_notMem hz] at h1 ⊢
    have : (P : ℝ) ^ s⁻¹ * yNorm s (h z) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hP h1
    exact h2.trans this

theorem isSmallV_modelForm {u : ℝ} (hu : 1 < u) (𝔭 : Params) (h𝔭 : 𝔭.Admissible) (T : Form P)
    (Ps : Finset TriTile) (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ)
    (hd : IsModelData 𝔭 Ps χ m) :
    Interp.IsSmallV (volume : Measure ℝ) (slotNorms u)
      (fun h => ‖modelForm T Ps χ m (h 0) (h 1) (h 2)‖) := by
  have hg := goodModel_of_isModelData h𝔭 hd
  have hk : ∀ (Q : TriTile) (k : Fin 3), ∃ B : ℝ, Q ∈ Ps → ∀ w, ‖𝓕⁻ (m Q k) w‖ ≤ B := by
    intro Q k
    by_cases hQ : Q ∈ Ps
    · obtain ⟨B, hB⟩ := (hg.kernel Q hQ k).bounded
      exact ⟨B, fun _ => hB⟩
    · exact ⟨0, fun h => absurd h hQ⟩
  choose B hB using hk
  have hB0 : ∀ Q ∈ Ps, ∀ k, 0 ≤ B Q k := fun Q hQ k => (norm_nonneg _).trans (hB Q k hQ 0)
  set b : Fin 3 → ℝ := fun i => (P : ℝ) ^ (slotExp u i)⁻¹ with hbdef
  have hb0 : ∀ i, 0 ≤ b i := fun i => Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨∑ Q ∈ Ps, (∫ x, ‖((χ Q x : ℝ) : ℂ)‖) *
    (rieszBound T * ((B Q 0 * b 0) * (B Q 1 * b 1)) * (B Q 2 * b 2)), ?_, ?_⟩
  · refine Finset.sum_nonneg fun Q hQ => mul_nonneg (integral_nonneg fun _ => norm_nonneg _)
      (mul_nonneg (mul_nonneg (rieszBound_nonneg T) (mul_nonneg
        (mul_nonneg (hB0 Q hQ 0) (hb0 0)) (mul_nonneg (hB0 Q hQ 1) (hb0 1))))
        (mul_nonneg (hB0 Q hQ 2) (hb0 2)))
  · intro h S hSm hSf _ hdom
    have hcoord : ∀ i z y, ‖h i z y‖ ≤ (S i).indicator (fun _ => b i) z := fun i z y =>
      coord_le_of_vDominated (slotExp_pos hu i) (hdom i) z y
    show ‖modelForm T Ps χ m (h 0) (h 1) (h 2)‖ ≤ _
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun Q hQ => ?_
    have hS0 := fun i => ENNReal.toReal_nonneg (a := volume (S i))
    have hKa : ∀ i x y, ‖tmult (m Q i) (h i) x y‖ ≤ B Q i * (b i * (volume (S i)).toReal) :=
      fun i x y => norm_tmult_le_of_supp (hB Q i hQ) (hSm i) (hSf i) (hcoord i) x y
    have hA0 : ∀ i, 0 ≤ B Q i * (b i * (volume (S i)).toReal) := fun i =>
      mul_nonneg (hB0 Q hQ i) (mul_nonneg (hb0 i) (hS0 i))
    have hint : Integrable (fun x => ‖((χ Q x : ℝ) : ℂ)‖ *
        (rieszBound T * ((B Q 0 * (b 0 * (volume (S 0)).toReal)) * (B Q 1 * (b 1 * (volume (S 1)).toReal))) *
          (B Q 2 * (b 2 * (volume (S 2)).toReal)))) :=
      (hg.integrable Q hQ).norm.mul_const _
    refine (norm_integral_le_of_norm_le hint (Eventually.of_forall fun x => ?_)).trans (le_of_eq ?_)
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact norm_T_le T (hA0 0) (hA0 1) (fun i => hKa 0 x i) (fun j => hKa 1 x j) (fun k => hKa 2 x k)
    · rw [integral_mul_const, Fin.prod_univ_three]
      ring

end FormProps

end PrimeBHT.TimeFrequency.X2
