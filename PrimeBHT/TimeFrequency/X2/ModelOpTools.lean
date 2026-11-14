module

public import PrimeBHT.TimeFrequency.X2.Classes
public import PrimeBHT.TimeFrequency.X2.YVec
import PrimeBHT.TimeFrequency.X2.ClassKernel
import PrimeBHT.TimeFrequency.X2.ClassLemmas
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# X2: analytic toolbox for the model operator (kernels, coordinatewise bounded functions, `tmult`, `rieszVec`)

Helper lemmas for `X2/ModelOp.lean` (none is a node statement):

* `GoodKernel m` (`𝓕⁻ m` integrable, continuous, bounded) and `goodKernel_of_inMult`, `GoodKernel.conj`
  (`𝓕⁻ (conj m) w = conj (𝓕⁻ m (-w))`);
* `IsBddC F`: coordinatewise measurable and bounded functions `ℝ → ZMod P → ℂ`; `isBddV_iff` (`yNorm s`-bounded
  measurable ⇔ `IsBddC`, for fixed `P`);
* `tmult` on `IsBddC` functions: measurability, bounds, additivity, homogeneity, dominated convergence, smallness;
* `rieszVec` (the Riesz vector of the conjugate-linear functional `Π(a, b, ·)`): coordinate expansion, bilinearity,
  bounds, continuity, `T a b c = yPair (rieszVec T a b) c`;
* `adjoint_scalar`: the Fubini identity `∫ α (κ ⋆ β) = ∫ (κ̃ ⋆ α) β` for `α, κ ∈ L¹`, `β` bounded measurable.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform ComplexConjugate ContDiff Real
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-! ### Kernels -/

theorem fourierInv_conj (m : ℝ → ℂ) (w : ℝ) :
    𝓕⁻ (fun ξ => conj (m ξ)) w = conj (𝓕⁻ m (-w)) := by
  rw [Real.fourierInv_eq', Real.fourierInv_eq', ← integral_conj]
  congr 1; ext v
  simp only [smul_eq_mul, map_mul]
  congr 1
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, inner_neg_right]
  congr 1
  push_cast
  ring

/-- The kernel `𝓕⁻ m` is integrable, continuous and bounded. -/
structure GoodKernel (m : ℝ → ℂ) : Prop where
  integrable : Integrable (𝓕⁻ m)
  continuous : Continuous (𝓕⁻ m)
  bounded : ∃ B : ℝ, ∀ w, ‖𝓕⁻ m w‖ ≤ B

theorem integrable_conj_fun {f : ℝ → ℂ} (hf : Integrable f) : Integrable (fun x => conj (f x)) :=
  Complex.conjCLE.toContinuousLinearMap.integrable_comp hf (𝕜 := ℝ)

theorem GoodKernel.conj {m : ℝ → ℂ} (hm : GoodKernel m) : GoodKernel (fun ξ => conj (m ξ)) := by
  have h : 𝓕⁻ (fun ξ => conj (m ξ)) = fun w => conj (𝓕⁻ m (-w)) := funext (fourierInv_conj m)
  refine ⟨?_, ?_, ?_⟩
  · rw [h]; exact integrable_conj_fun (hm.integrable.comp_neg)
  · rw [h]; exact Complex.continuous_conj.comp (hm.continuous.comp continuous_neg)
  · obtain ⟨B, hB⟩ := hm.bounded
    exact ⟨B, fun w => by rw [h]; simpa [Complex.norm_conj] using hB (-w)⟩

theorem goodKernel_of_inMult {𝔭 : Params} (h𝔭 : 𝔭.Admissible) {s : ℤ} {c : ℝ} {m : ℝ → ℂ}
    (hm : InMult 𝔭 s c m) : GoodKernel m := by
  obtain ⟨hN, hD, hβ, hC⟩ := h𝔭.bounds
  have hint : Integrable (𝓕⁻ m) := integrable_fourierInv_of_smooth hm.1 hm.2.1
  have hmint : Integrable m := integrable_of_far (hm.1.continuous) hm.2.1
  refine ⟨hint, continuous_fourierInv_of_integrable' hmint, ?_⟩
  refine ⟨3 * 𝔭.β * 𝔭.C * (((2 : ℝ) ^ s)⁻¹ * 1), fun w => ?_⟩
  refine (norm_fourierInv_inMult_le (by omega) (by linarith) hm w).trans ?_
  have h1 : (1 + |w| / (2 : ℝ) ^ s) ^ (-2 : ℤ) ≤ 1 := by
    have h2 : (1 : ℝ) ≤ 1 + |w| / (2 : ℝ) ^ s := by
      have : 0 ≤ |w| / (2 : ℝ) ^ s := by positivity
      linarith
    exact zpow_le_one_of_nonpos₀ h2 (by norm_num)
  have h3 : 0 ≤ 3 * 𝔭.β * 𝔭.C := by positivity
  gcongr

/-! ### Coordinatewise bounded measurable vector functions -/

section Bdd

variable {P : ℕ}

/-- Coordinatewise measurable and bounded `F : ℝ → ZMod P → ℂ`. -/
def IsBddC (F : ℝ → ZMod P → ℂ) : Prop :=
  (∀ y, Measurable fun x => F x y) ∧ ∃ M : ℝ, ∀ x y, ‖F x y‖ ≤ M

theorem IsBddC.measurable {F : ℝ → ZMod P → ℂ} (h : IsBddC F) : Measurable F :=
  measurable_pi_iff.2 h.1

theorem IsBddC.nonneg_bound {F : ℝ → ZMod P → ℂ} (h : IsBddC F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x y, ‖F x y‖ ≤ M := by
  obtain ⟨M, hM⟩ := h.2
  exact ⟨max M 0, le_max_right _ _, fun x y => (hM x y).trans (le_max_left _ _)⟩

theorem isBddC_of_measurable {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {M : ℝ}
    (hM : ∀ x y, ‖F x y‖ ≤ M) : IsBddC F :=
  ⟨fun y => (measurable_pi_iff.1 hF) y, M, hM⟩

theorem IsBddC.add {F G : ℝ → ZMod P → ℂ} (hF : IsBddC F) (hG : IsBddC G) : IsBddC (F + G) := by
  obtain ⟨M, hM⟩ := hF.2
  obtain ⟨N, hN⟩ := hG.2
  refine ⟨fun y => (hF.1 y).add (hG.1 y), M + N, fun x y => ?_⟩
  simpa using (norm_add_le _ _).trans (add_le_add (hM x y) (hN x y))

theorem IsBddC.smul {F : ℝ → ZMod P → ℂ} (hF : IsBddC F) (c : ℂ) : IsBddC (c • F) := by
  obtain ⟨M, hM⟩ := hF.2
  refine ⟨fun y => (hF.1 y).const_smul c, ‖c‖ * M, fun x y => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hM x y) (norm_nonneg _)

theorem IsBddC.sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ZMod P → ℂ}
    (h : ∀ i ∈ s, IsBddC (F i)) : IsBddC (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun y => by simp, 0, fun x y => by simp⟩
  | insert a s ha ih =>
    have h1 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have h2 := (h a (Finset.mem_insert_self a s)).add h1
    convert h2 using 2 with x
    rw [Finset.sum_insert ha]; rfl

/-- `yNorm s` is bounded by a sup bound on the coordinates. -/
theorem yNorm_le_of_forall_le [NeZero P] {s : ℝ} (hs : 0 < s) {G : ZMod P → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ y, ‖G y‖ ≤ B) : yNorm s G ≤ B := by
  have hP : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
  unfold yNorm
  have h1 : ∑ y, ‖G y‖ ^ s ≤ ∑ _y : ZMod P, B ^ s :=
    Finset.sum_le_sum fun y _ => Real.rpow_le_rpow (norm_nonneg _) (h y) hs.le
  have h2 : (P : ℝ)⁻¹ * ∑ y, ‖G y‖ ^ s ≤ B ^ s := by
    calc _ ≤ (P : ℝ)⁻¹ * ∑ _y : ZMod P, B ^ s := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hP.le)
      _ = B ^ s := by simp [Finset.sum_const, ZMod.card]; field_simp
  calc _ ≤ (B ^ s) ^ s⁻¹ :=
        Real.rpow_le_rpow (by positivity) h2 (inv_nonneg.2 hs.le)
    _ = B := Real.rpow_rpow_inv hB hs.ne'

/-- Fixed `P`: `yNorm s`-bounded measurable functions are the coordinatewise bounded measurable ones. -/
theorem isBddV_iff [NeZero P] {s : ℝ} (hs : 0 < s) {F : ℝ → ZMod P → ℂ} :
    Interp.IsBddV (yNorm s) F ↔ IsBddC F := by
  constructor
  · rintro ⟨hm, M, hM⟩
    refine ⟨fun y => (measurable_pi_iff.1 hm) y, (P : ℝ) ^ s⁻¹ * M, fun x y => ?_⟩
    exact (norm_apply_le_rpow_mul_yNorm hs (F x) y).trans
      (mul_le_mul_of_nonneg_left (hM x) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · rintro ⟨hm, M, hM⟩
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 0)
    exact ⟨measurable_pi_iff.2 hm, M, fun x => yNorm_le_of_forall_le hs hM0 (hM x)⟩

end Bdd

/-! ### The multiplier `tmult` on coordinatewise bounded functions -/

section Tmult

variable {P : ℕ}

theorem tmult_apply (m : ℝ → ℂ) (F : ℝ → ZMod P → ℂ) (x : ℝ) (y : ZMod P) :
    tmult m F x y = ∫ z, 𝓕⁻ m (x - z) * F z y := rfl

theorem integrable_tmult_integrand {m : ℝ → ℂ} (hK : GoodKernel m) {F : ℝ → ZMod P → ℂ}
    (hF : IsBddC F) (x : ℝ) (y : ZMod P) : Integrable (fun z => 𝓕⁻ m (x - z) * F z y) := by
  obtain ⟨M, hM⟩ := hF.2
  exact (hK.integrable.comp_sub_left x).mul_bdd (hF.1 y).aestronglyMeasurable
    (Eventually.of_forall fun z => hM z y)

/-- `∫ ‖𝓕⁻ m‖`. -/
def kerNorm (m : ℝ → ℂ) : ℝ := ∫ w, ‖𝓕⁻ m w‖

theorem kerNorm_nonneg (m : ℝ → ℂ) : 0 ≤ kerNorm m := integral_nonneg fun _ => norm_nonneg _

theorem norm_tmult_le {m : ℝ → ℂ} (hK : GoodKernel m) {F : ℝ → ZMod P → ℂ} {M : ℝ}
    (hM : ∀ z y, ‖F z y‖ ≤ M) (x : ℝ) (y : ZMod P) : ‖tmult m F x y‖ ≤ kerNorm m * M := by
  have hM0 : ∀ z y, ‖F z y‖ ≤ M := hM
  have hint : Integrable (fun z => ‖𝓕⁻ m (x - z)‖ * M) := (hK.integrable.comp_sub_left x).norm.mul_const M
  have h1 : ‖tmult m F x y‖ ≤ ∫ z, ‖𝓕⁻ m (x - z)‖ * M := by
    refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hM z y) (norm_nonneg _)
  refine h1.trans (le_of_eq ?_)
  rw [integral_mul_const, integral_sub_left_eq_self (fun w => ‖𝓕⁻ m w‖)]
  rfl

theorem IsBddC.tmult {m : ℝ → ℂ} (hK : GoodKernel m) {F : ℝ → ZMod P → ℂ} (hF : IsBddC F) :
    IsBddC (tmult m F) := by
  obtain ⟨M, hM⟩ := hF.2
  refine ⟨fun y => ?_, kerNorm m * M, fun x y => norm_tmult_le hK hM x y⟩
  have hmeas : Measurable fun p : ℝ × ℝ => 𝓕⁻ m (p.1 - p.2) * F p.2 y :=
    (hK.continuous.measurable.comp (measurable_fst.sub measurable_snd)).mul
      ((hF.1 y).comp measurable_snd)
  exact (hmeas.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

theorem tmult_add {m : ℝ → ℂ} (hK : GoodKernel m) {F G : ℝ → ZMod P → ℂ} (hF : IsBddC F)
    (hG : IsBddC G) : tmult m (F + G) = tmult m F + tmult m G := by
  funext x y
  simp only [tmult_apply, Pi.add_apply, mul_add]
  exact integral_add (integrable_tmult_integrand hK hF x y) (integrable_tmult_integrand hK hG x y)

theorem tmult_smul (m : ℝ → ℂ) (c : ℂ) (F : ℝ → ZMod P → ℂ) : tmult m (c • F) = c • tmult m F := by
  funext x y
  simp only [tmult_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; ext z; ring

/-- Dominated convergence for `tmult`: uniformly bounded, coordinatewise convergent inputs. -/
theorem tendsto_tmult {m : ℝ → ℂ} (hK : GoodKernel m) {Fn : ℕ → ℝ → ZMod P → ℂ} {F : ℝ → ZMod P → ℂ}
    {M : ℝ} (hmeas : ∀ n y, Measurable fun z => Fn n z y) (hb : ∀ n z y, ‖Fn n z y‖ ≤ M)
    (hlim : ∀ z y, Tendsto (fun n => Fn n z y) atTop (𝓝 (F z y))) (x : ℝ) :
    Tendsto (fun n => tmult m (Fn n) x) atTop (𝓝 (tmult m F x)) := by
  refine tendsto_pi_nhds.2 fun y => ?_
  refine tendsto_integral_of_dominated_convergence (fun z => ‖𝓕⁻ m (x - z)‖ * M) (fun n => ?_)
    ((hK.integrable.comp_sub_left x).norm.mul_const M) (fun n => Eventually.of_forall fun z => ?_)
    (Eventually.of_forall fun z => ?_)
  · exact ((hK.continuous.measurable.comp (measurable_const.sub measurable_id)).mul
      (hmeas n y)).aestronglyMeasurable
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hb n z y) (norm_nonneg _)
  · exact (hlim z y).const_mul _

/-- Smallness: if `‖F z y‖ ≤ b` on a set `S` of finite measure and `F = 0` off `S`, then
`‖tmult m F x y‖ ≤ B b |S|` (`B` a bound of the kernel). -/
theorem norm_tmult_le_of_supp {m : ℝ → ℂ} {B : ℝ} (hB : ∀ w, ‖𝓕⁻ m w‖ ≤ B) {F : ℝ → ZMod P → ℂ}
    {S : Set ℝ} (hS : MeasurableSet S) (hSf : volume S < ⊤) {b : ℝ}
    (hb : ∀ z y, ‖F z y‖ ≤ S.indicator (fun _ => b) z) (x : ℝ) (y : ZMod P) :
    ‖tmult m F x y‖ ≤ B * (b * (volume S).toReal) := by
  have hint : Integrable (S.indicator (fun _ : ℝ => B * b)) := by
    refine (integrable_indicator_iff hS).2 ?_
    exact integrableOn_const (by simpa using hSf.ne)
  have h1 : ‖tmult m F x y‖ ≤ ∫ z, S.indicator (fun _ : ℝ => B * b) z := by
    refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    by_cases hz : z ∈ S
    · have hb' := hb z y
      rw [Set.indicator_of_mem hz] at hb' ⊢
      exact mul_le_mul (hB _) hb' (norm_nonneg _) ((norm_nonneg _).trans (hB 0))
    · have hb' := hb z y
      rw [Set.indicator_of_notMem hz] at hb' ⊢
      have : ‖F z y‖ = 0 := le_antisymm hb' (norm_nonneg _)
      rw [this, mul_zero]
  refine h1.trans (le_of_eq ?_)
  rw [integral_indicator_const _ hS]
  simp only [measureReal_def, smul_eq_mul]
  ring

end Tmult

/-! ### The Riesz vector of the form `Π` and the pairing `yPair` -/

section Riesz

variable {P : ℕ} [NeZero P]

/-- The Riesz vector of `Π(a, b, ·)`: `w_y = P · Π(a, b, δ_y)`, so that `Π(a,b,c) = yPair (w a b) c`. -/
def rieszVec (T : Form P) (a b : ZMod P → ℂ) : ZMod P → ℂ :=
  fun y => (P : ℂ) * T a b (Pi.single y 1)

/-- The coefficients of the trilinear form in the standard basis. -/
def rieszCoef (T : Form P) (i j y : ZMod P) : ℂ :=
  (P : ℂ) * T (Pi.single i 1) (Pi.single j 1) (Pi.single y 1)

/-- A bound for `‖rieszVec T a b y‖ / (sup‖a‖ sup‖b‖)`. -/
def rieszBound (T : Form P) : ℝ := ∑ i, ∑ j, ∑ y, ‖rieszCoef T i j y‖

theorem rieszBound_nonneg (T : Form P) : 0 ≤ rieszBound T :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem eq_sum_single (c : ZMod P → ℂ) : c = ∑ k, c k • (Pi.single k (1 : ℂ) : ZMod P → ℂ) := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem T_apply_expand (T : Form P) (a b c : ZMod P → ℂ) :
    T a b c = ∑ k, conj (c k) * T a b (Pi.single k 1) := by
  have h : T a b c = T a b (∑ k, c k • (Pi.single k (1 : ℂ) : ZMod P → ℂ)) := by
    rw [← eq_sum_single c]
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ, smul_eq_mul]

theorem yPair_rieszVec (T : Form P) (a b c : ZMod P → ℂ) : yPair (rieszVec T a b) c = T a b c := by
  have hP : (P : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne P)
  rw [T_apply_expand T a b c]
  unfold yPair rieszVec
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp

theorem T_eq_yPair (T : Form P) (a b c : ZMod P → ℂ) : T a b c = yPair (rieszVec T a b) c :=
  (yPair_rieszVec T a b c).symm

theorem linear_apply_expand {N : Type*} [AddCommGroup N] [Module ℂ N]
    (L : (ZMod P → ℂ) →ₗ[ℂ] N) (a : ZMod P → ℂ) :
    L a = ∑ i, a i • L (Pi.single i 1) := by
  conv_lhs => rw [eq_sum_single a]
  rw [map_sum]
  simp only [map_smul]

theorem T_expand_ab (T : Form P) (a b e : ZMod P → ℂ) :
    T a b e = ∑ i, ∑ j, a i * b j * T (Pi.single i 1) (Pi.single j 1) e := by
  have h1 : T a = ∑ i, a i • T (Pi.single i 1) := linear_apply_expand T a
  rw [h1, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, linear_apply_expand (T (Pi.single i 1)) b]
  rw [LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

theorem rieszVec_apply (T : Form P) (a b : ZMod P → ℂ) (y : ZMod P) :
    rieszVec T a b y = ∑ i, ∑ j, a i * b j * rieszCoef T i j y := by
  unfold rieszVec rieszCoef
  rw [T_expand_ab T a b, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

omit [NeZero P] in
theorem rieszVec_add_left (T : Form P) (a a' b : ZMod P → ℂ) :
    rieszVec T (a + a') b = rieszVec T a b + rieszVec T a' b := by
  funext y
  simp only [rieszVec, map_add, LinearMap.add_apply, Pi.add_apply, mul_add]

omit [NeZero P] in
theorem rieszVec_smul_left (T : Form P) (c : ℂ) (a b : ZMod P → ℂ) :
    rieszVec T (c • a) b = c • rieszVec T a b := by
  funext y
  simp only [rieszVec, map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit [NeZero P] in
theorem rieszVec_add_right (T : Form P) (a b b' : ZMod P → ℂ) :
    rieszVec T a (b + b') = rieszVec T a b + rieszVec T a b' := by
  funext y
  simp only [rieszVec, map_add, LinearMap.add_apply, Pi.add_apply, mul_add]

omit [NeZero P] in
theorem rieszVec_smul_right (T : Form P) (c : ℂ) (a b : ZMod P → ℂ) :
    rieszVec T a (c • b) = c • rieszVec T a b := by
  funext y
  simp only [rieszVec, map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem norm_rieszVec_le (T : Form P) {a b : ZMod P → ℂ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ i, ‖a i‖ ≤ A) (hb : ∀ j, ‖b j‖ ≤ B) (y : ZMod P) :
    ‖rieszVec T a b y‖ ≤ rieszBound T * (A * B) := by
  rw [rieszVec_apply]
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ i, ‖∑ j, a i * b j * rieszCoef T i j y‖ ≤ ∑ j, A * B * ‖rieszCoef T i j y‖ := by
    intro i
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (ha i) (hb j) (norm_nonneg _) hA) (norm_nonneg _)
  refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
  unfold rieszBound
  simp_rw [← Finset.mul_sum]
  rw [mul_comm (∑ i, ∑ j, ∑ y, ‖rieszCoef T i j y‖)]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hA hB)
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    Finset.single_le_sum (f := fun y => ‖rieszCoef T i j y‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ y)

theorem tendsto_rieszVec (T : Form P) {an bn : ℕ → ZMod P → ℂ} {a b : ZMod P → ℂ}
    (ha : ∀ i, Tendsto (fun n => an n i) atTop (𝓝 (a i)))
    (hb : ∀ j, Tendsto (fun n => bn n j) atTop (𝓝 (b j))) (y : ZMod P) :
    Tendsto (fun n => rieszVec T (an n) (bn n) y) atTop (𝓝 (rieszVec T a b y)) := by
  simp only [rieszVec_apply]
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
  exact ((ha i).mul (hb j)).mul_const _

theorem measurable_rieszVec {α : Type*} [MeasurableSpace α] (T : Form P) {a b : α → ZMod P → ℂ}
    (ha : ∀ i, Measurable fun x => a x i) (hb : ∀ j, Measurable fun x => b x j) (y : ZMod P) :
    Measurable fun x => rieszVec T (a x) (b x) y := by
  simp only [rieszVec_apply]
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    ((ha i).mul (hb j)).mul_const _

theorem norm_yPair_le_of_coord {w c : ZMod P → ℂ} {W C : ℝ} (hW : 0 ≤ W) (hw : ∀ y, ‖w y‖ ≤ W)
    (hc : ∀ y, ‖c y‖ ≤ C) : ‖yPair w c‖ ≤ W * C := by
  have hP : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
  unfold yPair
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have h1 : ‖∑ y, w y * conj (c y)‖ ≤ ∑ _y : ZMod P, W * C := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hw y) (hc y) (norm_nonneg _) hW
  calc (P : ℝ)⁻¹ * ‖∑ y, w y * conj (c y)‖ ≤ (P : ℝ)⁻¹ * ∑ _y : ZMod P, W * C :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hP.le)
    _ = W * C := by simp [Finset.sum_const, ZMod.card]; field_simp

theorem norm_T_le (T : Form P) {a b c : ZMod P → ℂ} {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ i, ‖a i‖ ≤ A) (hb : ∀ j, ‖b j‖ ≤ B) (hc : ∀ k, ‖c k‖ ≤ C) :
    ‖T a b c‖ ≤ rieszBound T * (A * B) * C := by
  rw [T_eq_yPair]
  exact norm_yPair_le_of_coord (mul_nonneg (rieszBound_nonneg T) (mul_nonneg hA hB))
    (fun y => norm_rieszVec_le T hA hB ha hb y) hc

theorem measurable_T {α : Type*} [MeasurableSpace α] (T : Form P) {a b c : α → ZMod P → ℂ}
    (ha : ∀ i, Measurable fun x => a x i) (hb : ∀ j, Measurable fun x => b x j)
    (hc : ∀ k, Measurable fun x => c x k) : Measurable fun x => T (a x) (b x) (c x) := by
  simp only [T_eq_yPair, yPair]
  refine Measurable.const_mul (Finset.measurable_sum _ fun y _ => ?_) _
  exact (measurable_rieszVec T ha hb y).mul (Complex.continuous_conj.measurable.comp (hc y))

theorem yPair_smul_left (r : ℂ) (w c : ZMod P → ℂ) : yPair (r • w) c = r * yPair w c := by
  unfold yPair
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [← Finset.mul_sum]
  ring

theorem yPair_sum_left {ι : Type*} (s : Finset ι) (w : ι → ZMod P → ℂ) (c : ZMod P → ℂ) :
    yPair (∑ i ∈ s, w i) c = ∑ i ∈ s, yPair (w i) c := by
  unfold yPair
  simp only [Finset.sum_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

end Riesz

/-! ### The Fubini identity for the adjoint of a convolution -/

/-- `∫ α (κ ⋆ β) = ∫ (κ̃ ⋆ α) β` for `α, κ ∈ L¹` and `β` bounded measurable, together with the integrability of
both integrands. -/
theorem adjoint_scalar {α κ β : ℝ → ℂ} (hα : Integrable α) (hκ : Integrable κ)
    (hβm : Measurable β) {C : ℝ} (hβb : ∀ z, ‖β z‖ ≤ C) :
    Integrable (fun x => α x * ∫ z, κ (x - z) * β z) ∧
    Integrable (fun z => (∫ x, κ (x - z) * α x) * β z) ∧
    ∫ x, α x * ∫ z, κ (x - z) * β z = ∫ z, (∫ x, κ (x - z) * α x) * β z := by
  set f : ℝ → ℝ → ℂ := fun z x => α x * (κ (x - z) * β z) with hf
  have hint : Integrable (Function.uncurry f) (volume.prod volume) := by
    have h1 := Integrable.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) (μ := volume)
      (ν := volume) hα hκ.comp_neg
    have h2 := h1.mul_bdd (g := fun p : ℝ × ℝ => β p.1)
      ((hβm.comp measurable_fst).aestronglyMeasurable) (c := C)
      (Eventually.of_forall fun p => hβb p.1)
    refine h2.congr (Eventually.of_forall fun p => ?_)
    simp only [ContinuousLinearMap.mul_apply', Function.uncurry, hf, neg_sub]
    ring
  have e1 : ∀ x, ∫ z, f z x = α x * ∫ z, κ (x - z) * β z := fun x => integral_const_mul _ _
  have e2 : ∀ z, ∫ x, f z x = (∫ x, κ (x - z) * α x) * β z := by
    intro z
    rw [← integral_mul_const]
    congr 1; ext x
    simp only [hf]; ring
  refine ⟨?_, ?_, ?_⟩
  · have := hint.integral_prod_right
    simpa only [Function.uncurry, e1] using this
  · have := hint.integral_prod_left
    simpa only [Function.uncurry, e2] using this
  · have := integral_integral_swap hint
    simpa only [e1, e2] using this.symm

end PrimeBHT.TimeFrequency.X2
