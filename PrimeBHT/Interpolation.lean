module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Topology

/-!
# N60: bilinear complex interpolation with quasi-Banach targets

* `StripPoissonJensen θ`: the strip Poisson-Jensen inequality (SJ), exponentiated form.
* `stripPoissonJensen`: (SJ) holds for every `θ ∈ (0,1)` (blueprint option A: conformal map of
  the unit disc onto the strip with `0 ↦ θ`, Jensen's inequality on circles of radius `ρ < 1`,
  split into the two arcs and exponentiated, then `ρ → 1` by dominated convergence; `ν₀, ν₁` are
  the normalized images of the two boundary arcs).
* `interp_bilinear_of_poissonJensen`: N60 from (SJ) (analytic family, Hölder in `x`).
* `interp_bilinear`, `interp_bilinear_holder`: the unconditional statements.
-/

@[expose] public section

open MeasureTheory Complex Complex.HadamardThreeLines Metric Real
open scoped ENNReal

namespace PrimeBHT.Interpolation

/-! ## Part I: (SJ) and the reduction -/

/-- **(SJ)**, exponentiated form. There are probability measures `ν₀, ν₁` on `ℝ` such that for
every bounded `G`, continuous on the closed strip `0 ≤ re z ≤ 1` and holomorphic inside, and
all exponents `a₀, a₁ > 0`,
`‖G θ‖ ≤ (∫ ‖G(it)‖^a₀ dν₀)^((1-θ)/a₀) * (∫ ‖G(1+it)‖^a₁ dν₁)^(θ/a₁)`.
This follows from the logarithmic form of (SJ) by Jensen's inequality for `exp`, and conversely
implies it by letting `a₀, a₁ → 0` (the `L^a(ν)` quasi-norm of a bounded function tends to its
geometric mean); it is the form step 5 of the blueprint uses. -/
def StripPoissonJensen (θ : ℝ) : Prop :=
  ∃ ν₀ ν₁ : Measure ℝ, IsProbabilityMeasure ν₀ ∧ IsProbabilityMeasure ν₁ ∧
    ∀ G : ℂ → ℂ, DiffContOnCl ℂ G (verticalStrip 0 1) →
      BddAbove ((fun z => ‖G z‖) '' verticalClosedStrip 0 1) →
      ∀ a₀ a₁ : ℝ, 0 < a₀ → 0 < a₁ →
        ‖G θ‖ₑ ≤ (∫⁻ t, ‖G (t * I)‖ₑ ^ a₀ ∂ν₀) ^ ((1 - θ) / a₀) *
          (∫⁻ t, ‖G (1 + t * I)‖ₑ ^ a₁ ∂ν₁) ^ (θ / a₁)

lemma eLpNorm_count_eq (f : ℤ → ℂ) {r : ℝ} (hr : 0 < r) :
    eLpNorm f (ENNReal.ofReal r) Measure.count = (∑' x, ‖f x‖ₑ ^ r) ^ (1 / r) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr) ENNReal.ofReal_ne_top
    (measurable_of_countable f).aestronglyMeasurable, lintegral_count,
    ENNReal.toReal_ofReal hr.le]

lemma eLpNorm_count_rpow (f : ℤ → ℂ) {r : ℝ} (hr : 0 < r) :
    eLpNorm f (ENNReal.ofReal r) Measure.count ^ r = ∑' x, ‖f x‖ₑ ^ r := by
  rw [eLpNorm_count_eq f hr, one_div, ENNReal.rpow_inv_rpow hr.ne']

/-- The power map `w ↦ w |w|^(c-1)` (equal to `sgn w * |w|^c`, and `0` at `0`). -/
noncomputable def powFamily (c w : ℂ) : ℂ := w * ((‖w‖ : ℂ) ^ (c - 1))

lemma powFamily_one (w : ℂ) : powFamily 1 w = w := by simp [powFamily]

lemma powFamily_zero (c : ℂ) : powFamily c 0 = 0 := by simp [powFamily]

lemma norm_powFamily {c : ℂ} (hc : 0 < c.re) (w : ℂ) : ‖powFamily c w‖ = ‖w‖ ^ c.re := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [powFamily, Real.zero_rpow hc.ne']
  have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  rw [powFamily, norm_mul, norm_cpow_eq_rpow_re_of_pos hpos]
  conv_rhs => rw [show c.re = 1 + (c - 1).re by simp]
  rw [Real.rpow_add hpos, Real.rpow_one]

lemma enorm_powFamily_rpow {c : ℂ} (hc : 0 < c.re) (w : ℂ) {p s : ℝ} (hp : 0 < p)
    (hs : c.re * p = s) : ‖powFamily c w‖ₑ ^ p = ‖w‖ₑ ^ s := by
  have hs0 : 0 ≤ s := hs ▸ (mul_pos hc hp).le
  rw [← ofReal_norm, ← ofReal_norm, norm_powFamily hc,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hs0, ← Real.rpow_mul (norm_nonneg _), hs]

lemma differentiable_powFamily (a b : ℂ) (w : ℂ) :
    Differentiable ℂ (fun z => powFamily (a + b * z) w) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [powFamily_zero]
  unfold powFamily
  refine Differentiable.const_mul ?_ _
  refine Differentiable.const_cpow (by fun_prop) (Or.inl ?_)
  exact_mod_cast (norm_pos_iff.2 hw).ne'

/-- `y^s ≤ 1 + y` for `y ≥ 0`, `s ∈ [0,1]`. -/
lemma rpow_le_one_add {y s : ℝ} (hy : 0 ≤ y) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : y ^ s ≤ 1 + y := by
  rcases le_total y 1 with h | h
  · linarith [Real.rpow_le_one hy h hs0]
  · have := Real.rpow_le_rpow_of_exponent_le h hs1
    rw [Real.rpow_one] at this
    linarith

lemma norm_powFamily_le {a b : ℝ} {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1)
    (hpos : 0 < a + b * z.re) (w : ℂ) :
    ‖powFamily (a + b * z) w‖ ≤ ‖w‖ ^ a * (1 + ‖w‖ ^ b) := by
  have hre : ((a : ℂ) + b * z).re = a + b * z.re := by simp
  rw [norm_powFamily (hre ▸ hpos), hre]
  rcases eq_or_ne w 0 with rfl | hw
  · rw [norm_zero, Real.zero_rpow hpos.ne']
    positivity
  have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
  rw [Real.rpow_add hw', Real.rpow_mul hw'.le]
  gcongr
  exact rpow_le_one_add (by positivity) hz0 hz1

/-- The analytic family `f_z(y) = sgn f(y) |f(y)|^(a + b z)` supported on `supp f`. -/
noncomputable def family (f : ℤ →₀ ℂ) (a b : ℝ) (z : ℂ) : ℤ →₀ ℂ :=
  ∑ y ∈ f.support, Finsupp.single y (powFamily (a + b * z) (f y))

lemma family_apply (f : ℤ →₀ ℂ) (a b : ℝ) (z : ℂ) (y : ℤ) :
    family f a b z y = powFamily (a + b * z) (f y) := by
  classical
  simp only [family, Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq',
    Finsupp.mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not.1 h, powFamily_zero]

lemma family_eq_self (f : ℤ →₀ ℂ) {a b : ℝ} {z : ℂ} (hz : (a : ℂ) + b * z = 1) :
    family f a b z = f := by
  ext y
  rw [family_apply, hz, powFamily_one]

/-- Expansion of `T (f_z) (g_z) x` by bilinearity as a finite double sum. -/
lemma apply_family_eq (T : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) (f g : ℤ →₀ ℂ)
    (a b a' b' : ℝ) (z : ℂ) (x : ℤ) :
    T (family f a b z) (family g a' b' z) x =
      ∑ y ∈ f.support, ∑ y' ∈ g.support, powFamily (a + b * z) (f y) *
        powFamily (a' + b' * z) (g y') * T (Finsupp.single y 1) (Finsupp.single y' 1) x := by
  simp only [family, map_sum, LinearMap.coe_sum, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
  rw [← Finsupp.smul_single_one, ← Finsupp.smul_single_one y', map_smul, map_smul,
    LinearMap.smul_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

lemma differentiable_apply_family (T : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ))
    (f g : ℤ →₀ ℂ) (a b a' b' : ℝ) (x : ℤ) :
    Differentiable ℂ (fun z => T (family f a b z) (family g a' b' z) x) := by
  simp_rw [apply_family_eq]
  refine Differentiable.fun_sum fun y _ => Differentiable.fun_sum fun y' _ => ?_
  exact ((differentiable_powFamily _ _ _).mul (differentiable_powFamily _ _ _)).mul_const _

lemma bddAbove_apply_family (T : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ))
    (f g : ℤ →₀ ℂ) {a b a' b' : ℝ} (ha : 0 < a) (hab : 0 < a + b) (ha' : 0 < a')
    (hab' : 0 < a' + b') (x : ℤ) :
    BddAbove ((fun z => ‖T (family f a b z) (family g a' b' z) x‖) '' verticalClosedStrip 0 1) := by
  refine ⟨∑ y ∈ f.support, ∑ y' ∈ g.support, ‖f y‖ ^ a * (1 + ‖f y‖ ^ b) *
    (‖g y'‖ ^ a' * (1 + ‖g y'‖ ^ b')) * ‖T (Finsupp.single y 1) (Finsupp.single y' 1) x‖, ?_⟩
  rintro _ ⟨z, ⟨hz0, hz1⟩, rfl⟩
  have hpos : ∀ {c d : ℝ}, 0 < c → 0 < c + d → 0 < c + d * z.re := fun {c d} hc hcd => by
    nlinarith [mul_nonneg hz0 hcd.le, mul_nonneg (sub_nonneg.2 hz1) hc.le]
  simp only [apply_family_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y' _ => ?_)
  rw [norm_mul, norm_mul]
  gcongr
  · exact norm_powFamily_le hz0 hz1 (hpos ha hab) _
  · exact norm_powFamily_le hz0 hz1 (hpos ha' hab') _

lemma tsum_enorm_family_rpow (f : ℤ →₀ ℂ) {a b : ℝ} {z : ℂ} (hre : 0 < ((a : ℂ) + b * z).re)
    {p s : ℝ} (hp : 0 < p) (hs : ((a : ℂ) + b * z).re * p = s) :
    ∑' y, ‖family f a b z y‖ₑ ^ p = ∑' y, ‖f y‖ₑ ^ s :=
  tsum_congr fun y => by rw [family_apply]; exact enorm_powFamily_rpow hre _ hp hs

lemma eLpNorm_family (f : ℤ →₀ ℂ) {a b : ℝ} {z : ℂ} (hre : 0 < ((a : ℂ) + b * z).re)
    {p s : ℝ} (hp : 0 < p) (hs : ((a : ℂ) + b * z).re * p = s) :
    eLpNorm (family f a b z) (ENNReal.ofReal p) Measure.count =
      (∑' y, ‖f y‖ₑ ^ s) ^ (1 / p) := by
  rw [eLpNorm_count_eq _ hp, tsum_enorm_family_rpow f hre hp hs]

/-- Hölder for nonnegative series with exponents `1/α`, `1/β`, `α + β = 1`. -/
lemma tsum_rpow_mul_rpow_le {u v : ℤ → ℝ≥0∞} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hαβ : α + β = 1) :
    ∑' x, u x ^ α * v x ^ β ≤ (∑' x, u x) ^ α * (∑' x, v x) ^ β := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq Measure.count
    (Real.HolderConjugate.inv_inv hα hβ hαβ) (f := fun x => u x ^ α) (g := fun x => v x ^ β)
    (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable
  simp only [lintegral_count, Pi.mul_apply, ← ENNReal.rpow_mul, mul_inv_cancel₀ hα.ne',
    mul_inv_cancel₀ hβ.ne', ENNReal.rpow_one, one_div, inv_inv] at h
  exact h

/-- **N60, conditional on (SJ).** Bilinear complex interpolation with quasi-Banach targets,
assuming the strip Poisson-Jensen inequality `StripPoissonJensen θ`. -/
theorem interp_bilinear_of_poissonJensen
    (T : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ))
    {p₀ p₁ q₀ q₁ r₀ r₁ M₀ M₁ θ p q r : ℝ}
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₀ : ∀ f g : ℤ →₀ ℂ, eLpNorm (T f g) (ENNReal.ofReal r₀) Measure.count ≤
      ENNReal.ofReal M₀ * eLpNorm f (ENNReal.ofReal p₀) Measure.count *
        eLpNorm g (ENNReal.ofReal q₀) Measure.count)
    (h₁ : ∀ f g : ℤ →₀ ℂ, eLpNorm (T f g) (ENNReal.ofReal r₁) Measure.count ≤
      ENNReal.ofReal M₁ * eLpNorm f (ENNReal.ofReal p₁) Measure.count *
        eLpNorm g (ENNReal.ofReal q₁) Measure.count)
    (hθ : θ ∈ Set.Ioo 0 1) (hp : 1 / p = (1 - θ) / p₀ + θ / p₁)
    (hq : 1 / q = (1 - θ) / q₀ + θ / q₁) (hr : 1 / r = (1 - θ) / r₀ + θ / r₁)
    (hSJ : StripPoissonJensen θ) (f g : ℤ →₀ ℂ) :
    eLpNorm (T f g) (ENNReal.ofReal r) Measure.count ≤
      ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f (ENNReal.ofReal p) Measure.count *
        eLpNorm g (ENNReal.ofReal q) Measure.count := by
  obtain ⟨ν₀, ν₁, hν₀, hν₁, hSJ⟩ := hSJ
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hθ0' : 0 < 1 - θ := by linarith
  have hpp : 0 < p := one_div_pos.1 (hp ▸ by positivity)
  have hqq : 0 < q := one_div_pos.1 (hq ▸ by positivity)
  have hrr : 0 < r := one_div_pos.1 (hr ▸ by positivity)
  -- exponents of the analytic families
  set a := p / p₀
  set b := p / p₁ - p / p₀
  set a' := q / q₀
  set b' := q / q₁ - q / q₀
  have ha : 0 < a := by positivity
  have hab : 0 < a + b := by simp only [a, b]; ring_nf; positivity
  have ha' : 0 < a' := by positivity
  have hab' : 0 < a' + b' := by simp only [a', b']; ring_nf; positivity
  have hθa : (a : ℂ) + b * θ = 1 := by
    have : a + b * θ = p * (1 / p) := by rw [hp]; simp only [a, b]; ring
    rw [mul_one_div_cancel hpp.ne'] at this
    exact_mod_cast this
  have hθa' : (a' : ℂ) + b' * θ = 1 := by
    have : a' + b' * θ = q * (1 / q) := by rw [hq]; simp only [a', b']; ring
    rw [mul_one_div_cancel hqq.ne'] at this
    exact_mod_cast this
  set F : ℤ → ℂ → ℂ := fun x z => T (family f a b z) (family g a' b' z) x with hF
  have hFθ : ∀ x, T f g x = F x θ := fun x => by
    simp only [hF, family_eq_self f hθa, family_eq_self g hθa']
  have hFcont : ∀ x, Continuous (F x) := fun x =>
    (differentiable_apply_family T f g a b a' b' x).continuous
  -- real parts on the boundary lines
  have hre0 : ∀ (c d t : ℝ), ((c : ℂ) + d * (t * I)).re = c := fun c d t => by simp
  have hre1 : ∀ (c d t : ℝ), ((c : ℂ) + d * (1 + t * I)).re = c + d := fun c d t => by simp
  set Sf := ∑' y, ‖f y‖ₑ ^ p
  set Sg := ∑' y, ‖g y‖ₑ ^ q
  set K₀ := ENNReal.ofReal M₀ * Sf ^ (1 / p₀) * Sg ^ (1 / q₀)
  set K₁ := ENNReal.ofReal M₁ * Sf ^ (1 / p₁) * Sg ^ (1 / q₁)
  have hline₀ : ∀ t : ℝ, ∑' x, ‖F x (t * I)‖ₑ ^ r₀ ≤ K₀ ^ r₀ := fun t => by
    have := eLpNorm_count_rpow (T (family f a b (t * I)) (family g a' b' (t * I))) hr₀
    simp only [hF]
    rw [← this]
    gcongr
    refine (h₀ _ _).trans_eq ?_
    rw [eLpNorm_family f (by rw [hre0]; exact ha) hp₀ (s := p) (by rw [hre0]; simp only [a]; field_simp),
      eLpNorm_family g (by rw [hre0]; exact ha') hq₀ (s := q) (by rw [hre0]; simp only [a']; field_simp)]
  have hline₁ : ∀ t : ℝ, ∑' x, ‖F x (1 + t * I)‖ₑ ^ r₁ ≤ K₁ ^ r₁ := fun t => by
    have := eLpNorm_count_rpow (T (family f a b (1 + t * I)) (family g a' b' (1 + t * I))) hr₁
    simp only [hF]
    rw [← this]
    gcongr
    refine (h₁ _ _).trans_eq ?_
    rw [eLpNorm_family f (by rw [hre1]; exact hab) hp₁ (s := p) (by rw [hre1]; simp only [a, b]; field_simp; ring),
      eLpNorm_family g (by rw [hre1]; exact hab') hq₁ (s := q) (by rw [hre1]; simp only [a', b']; field_simp; ring)]
  -- (SJ) pointwise in `x`
  set I₀ : ℤ → ℝ≥0∞ := fun x => ∫⁻ t, ‖F x (t * I)‖ₑ ^ r₀ ∂ν₀
  set I₁ : ℤ → ℝ≥0∞ := fun x => ∫⁻ t, ‖F x (1 + t * I)‖ₑ ^ r₁ ∂ν₁
  set α := (1 - θ) / r₀ * r
  set β := θ / r₁ * r
  have hα : 0 < α := by positivity
  have hβ : 0 < β := by positivity
  have hαβ : α + β = 1 := by
    have : α + β = r * (1 / r) := by rw [hr]; simp only [α, β]; ring
    rwa [mul_one_div_cancel hrr.ne'] at this
  have hpt : ∀ x, ‖F x θ‖ₑ ^ r ≤ I₀ x ^ α * I₁ x ^ β := fun x => by
    have h := hSJ (F x) (differentiable_apply_family T f g a b a' b' x).diffContOnCl
      (bddAbove_apply_family T f g ha hab ha' hab' x) r₀ r₁ hr₀ hr₁
    calc ‖F x θ‖ₑ ^ r ≤ (I₀ x ^ ((1 - θ) / r₀) * I₁ x ^ (θ / r₁)) ^ r :=
          ENNReal.rpow_le_rpow h hrr.le
      _ = I₀ x ^ α * I₁ x ^ β := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hrr.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  -- Tonelli on each boundary line
  have hmeas₀ : ∀ x, AEMeasurable (fun t : ℝ => ‖F x (t * I)‖ₑ ^ r₀) ν₀ := fun x =>
    (((hFcont x).comp (by fun_prop : Continuous fun t : ℝ => (t : ℂ) * I)).measurable.enorm.pow_const
      _).aemeasurable
  have hmeas₁ : ∀ x, AEMeasurable (fun t : ℝ => ‖F x (1 + t * I)‖ₑ ^ r₁) ν₁ := fun x =>
    (((hFcont x).comp (by fun_prop : Continuous fun t : ℝ => 1 + (t : ℂ) * I)).measurable.enorm.pow_const
      _).aemeasurable
  have hsum₀ : ∑' x, I₀ x ≤ K₀ ^ r₀ := by
    simp only [I₀]
    rw [← lintegral_tsum hmeas₀]
    calc ∫⁻ t, ∑' x, ‖F x (t * I)‖ₑ ^ r₀ ∂ν₀ ≤ ∫⁻ _, K₀ ^ r₀ ∂ν₀ := lintegral_mono hline₀
      _ = K₀ ^ r₀ := by simp
  have hsum₁ : ∑' x, I₁ x ≤ K₁ ^ r₁ := by
    simp only [I₁]
    rw [← lintegral_tsum hmeas₁]
    calc ∫⁻ t, ∑' x, ‖F x (1 + t * I)‖ₑ ^ r₁ ∂ν₁ ≤ ∫⁻ _, K₁ ^ r₁ ∂ν₁ := lintegral_mono hline₁
      _ = K₁ ^ r₁ := by simp
  have hmain : ∑' x, ‖T f g x‖ₑ ^ r ≤ (K₀ ^ r₀) ^ α * (K₁ ^ r₁) ^ β := by
    simp only [hFθ]
    calc ∑' x, ‖F x θ‖ₑ ^ r ≤ ∑' x, I₀ x ^ α * I₁ x ^ β := ENNReal.tsum_le_tsum hpt
      _ ≤ (∑' x, I₀ x) ^ α * (∑' x, I₁ x) ^ β := tsum_rpow_mul_rpow_le hα hβ hαβ
      _ ≤ (K₀ ^ r₀) ^ α * (K₁ ^ r₁) ^ β := by gcongr
  -- take the `1/r` power and identify the constant
  rw [eLpNorm_count_eq _ hrr, eLpNorm_count_eq _ hpp, eLpNorm_count_eq _ hqq]
  calc (∑' x, ‖T f g x‖ₑ ^ r) ^ (1 / r) ≤ ((K₀ ^ r₀) ^ α * (K₁ ^ r₁) ^ β) ^ (1 / r) := by
        gcongr
    _ = K₀ ^ (1 - θ) * K₁ ^ θ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        congr 2
        · simp only [α]; field_simp
        · simp only [β]; field_simp
    _ = ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * Sf ^ (1 / p) * Sg ^ (1 / q) := by
        have eSf : Sf ^ (1 / p) = Sf ^ (1 / p₀ * (1 - θ)) * Sf ^ (1 / p₁ * θ) := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hp]; ring_nf
        have eSg : Sg ^ (1 / q) = Sg ^ (1 / q₀ * (1 - θ)) * Sg ^ (1 / q₁ * θ) := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hq]; ring_nf
        rw [eSf, eSg, ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_rpow_of_nonneg hM₀ hθ0'.le, ← ENNReal.ofReal_rpow_of_nonneg hM₁ hθ0.le]
        simp only [K₀, K₁, ENNReal.mul_rpow_of_nonneg _ _ hθ0'.le,
          ENNReal.mul_rpow_of_nonneg _ _ hθ0.le, ← ENNReal.rpow_mul]
        ring

/-- **N60 in the form used by the paper, conditional on (SJ)**: endpoints with
`1/rᵢ = 1/pᵢ + 1/qᵢ`, `1 ≤ pᵢ, qᵢ`; the interpolated output exponent satisfies
`1/r = 1/p + 1/q` as well. -/
theorem interp_bilinear_holder_of_poissonJensen
    (T : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ))
    {p₀ p₁ q₀ q₁ r₀ r₁ M₀ M₁ θ p q r : ℝ}
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁)
    (hr₀ : 1 / r₀ = 1 / p₀ + 1 / q₀) (hr₁ : 1 / r₁ = 1 / p₁ + 1 / q₁)
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : ∀ f g : ℤ →₀ ℂ, eLpNorm (T f g) (ENNReal.ofReal r₀) Measure.count ≤
      ENNReal.ofReal M₀ * eLpNorm f (ENNReal.ofReal p₀) Measure.count *
        eLpNorm g (ENNReal.ofReal q₀) Measure.count)
    (h₁ : ∀ f g : ℤ →₀ ℂ, eLpNorm (T f g) (ENNReal.ofReal r₁) Measure.count ≤
      ENNReal.ofReal M₁ * eLpNorm f (ENNReal.ofReal p₁) Measure.count *
        eLpNorm g (ENNReal.ofReal q₁) Measure.count)
    (hθ : θ ∈ Set.Ioo 0 1) (hp : 1 / p = (1 - θ) / p₀ + θ / p₁)
    (hq : 1 / q = (1 - θ) / q₀ + θ / q₁) (hr : 1 / r = 1 / p + 1 / q)
    (hSJ : StripPoissonJensen θ) (f g : ℤ →₀ ℂ) :
    eLpNorm (T f g) (ENNReal.ofReal r) Measure.count ≤
      ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f (ENNReal.ofReal p) Measure.count *
        eLpNorm g (ENNReal.ofReal q) Measure.count := by
  have hpos : ∀ {s : ℝ}, 1 ≤ s → 0 < s := fun h => by linarith
  have hrpos : ∀ {s u v : ℝ}, 1 ≤ u → 1 ≤ v → 1 / s = 1 / u + 1 / v → 0 < s :=
    fun hu hv h => one_div_pos.1 (h ▸ by have := hpos hu; have := hpos hv; positivity)
  refine interp_bilinear_of_poissonJensen T (hpos hp₀) (hpos hp₁) (hpos hq₀) (hpos hq₁)
    (hrpos hp₀ hq₀ hr₀) (hrpos hp₁ hq₁ hr₁) hM₀.le hM₁.le h₀ h₁ hθ hp hq ?_ hSJ f g
  rw [hr, hp, hq, div_eq_mul_one_div (1 - θ) r₀, div_eq_mul_one_div θ r₁, hr₀, hr₁]
  ring


/-! ## Part II: proof of (SJ) -/

/-- **Jensen's inequality** (zeros contribute with the right sign): for `f` analytic on a
neighbourhood of the closed disc of radius `R > 0` about `c` with `f c ≠ 0`,
`log ‖f c‖ ≤ circleAverage (log ‖f ·‖) c R`. -/
theorem log_norm_le_circleAverage {c : ℂ} {R : ℝ} {f : ℂ → ℂ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c |R|)) (hc : f c ≠ 0) :
    Real.log ‖f c‖ ≤ circleAverage (Real.log ‖f ·‖) c R := by
  rw [hf.circleAverage_log_norm hR.ne' hc]
  refine le_add_of_nonneg_left (finsum_nonneg fun u => ?_)
  have hdiv : (0 : ℤ) ≤ MeromorphicOn.divisor f (closedBall c |R|) u := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf u
  rcases eq_or_ne (MeromorphicOn.divisor f (closedBall c |R|) u) 0 with h0 | h0
  · simp [h0]
  have hu : u ∈ closedBall c |R| :=
    (MeromorphicOn.divisor f (closedBall c |R|)).supportWithinDomain h0
  refine mul_nonneg (by exact_mod_cast hdiv) ?_
  rcases eq_or_ne u c with rfl | huc
  · simp
  have hpos : 0 < ‖c - u‖ := norm_pos_iff.2 (sub_ne_zero.2 huc.symm)
  have hle : ‖c - u‖ ≤ |R| := by rw [norm_sub_rev]; exact mem_closedBall_iff_norm.1 hu
  apply Real.log_nonneg
  rw [abs_of_pos hR] at hle
  rw [← div_eq_mul_inv, one_le_div hpos]
  exact hle

/-! ## The conformal map from the unit disc onto the strip `0 < re z < 1`, `0 ↦ θ` -/

/-- Inverse Cayley map: the unit disc onto the upper half plane, `0 ↦ e^{iπθ}`. -/
noncomputable def cayleyInv (θ : ℝ) (w : ℂ) : ℂ :=
  (exp (π * θ * I) - w * exp (-(π * θ * I))) / (1 - w)

/-- The map from the unit disc onto the strip: `w ↦ 1/2 - i log(-i ζ(w)) / π`. -/
noncomputable def stripMap (θ : ℝ) (w : ℂ) : ℂ :=
  1 / 2 - I * log (-I * cayleyInv θ w) / π

lemma stripMap_re (θ : ℝ) (w : ℂ) :
    (stripMap θ w).re = 1 / 2 + arg (-I * cayleyInv θ w) / π := by
  simp [stripMap, div_ofReal_re, log_im]
  ring

lemma cayleyInv_im (θ : ℝ) (w : ℂ) :
    (cayleyInv θ w).im = Real.sin (π * θ) * (1 - normSq w) / normSq (1 - w) := by
  have h1 : exp (π * θ * I) = (Real.cos (π * θ) : ℂ) + Real.sin (π * θ) * I := by
    rw [show (π : ℂ) * θ * I = ((π * θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
    push_cast; ring
  have h2 : exp (-(π * θ * I)) = (Real.cos (π * θ) : ℂ) - Real.sin (π * θ) * I := by
    rw [show -((π : ℂ) * θ * I) = ((-(π * θ) : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
    push_cast; rw [Complex.cos_neg, Complex.sin_neg]; ring
  rw [cayleyInv, h1, h2, div_im]
  simp only [normSq_apply, sub_re, sub_im, one_re, one_im, add_re, add_im, mul_re, mul_im,
    ofReal_re, ofReal_im, I_re, I_im]
  ring

lemma cayleyInv_zero (θ : ℝ) : cayleyInv θ 0 = exp (π * θ * I) := by simp [cayleyInv]

lemma stripMap_zero {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) : stripMap θ 0 = θ := by
  obtain ⟨h0, h1⟩ := hθ
  have hI : -I * exp (π * θ * I) = exp (((π * (θ - 1 / 2) : ℝ) : ℂ) * I) := by
    rw [show ((π * (θ - 1 / 2) : ℝ) : ℂ) * I = π * θ * I + (-(π / 2 * I)) by push_cast; ring,
      Complex.exp_add, Complex.exp_neg, Complex.exp_pi_div_two_mul_I, inv_I]
    ring
  rw [stripMap, cayleyInv_zero, hI, Complex.log_exp]
  · push_cast
    field_simp
    ring_nf
    rw [I_sq]; ring
  · simp only [mul_im, ofReal_re, ofReal_im, I_re, I_im]
    nlinarith [Real.pi_pos]
  · simp only [mul_im, ofReal_re, ofReal_im, I_re, I_im]
    nlinarith [Real.pi_pos]

lemma neg_I_mul_re (z : ℂ) : (-I * z).re = z.im := by simp

lemma cayleyInv_im_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) {w : ℂ} (hw : ‖w‖ < 1) :
    0 < (cayleyInv θ w).im := by
  rw [cayleyInv_im]
  have hs : 0 < Real.sin (π * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos, hθ.1]) (by nlinarith [Real.pi_pos, hθ.2])
  have hw1 : 1 - w ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h, norm_one] at hw; exact lt_irrefl _ hw
  have hn : normSq w < 1 := by
    rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  have := normSq_pos.2 hw1
  have : 0 < 1 - normSq w := by linarith
  positivity

lemma re_neg_I_mul_cayleyInv_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) {w : ℂ} (hw : ‖w‖ < 1) :
    0 < (-I * cayleyInv θ w).re := by
  rw [neg_I_mul_re]; exact cayleyInv_im_pos hθ hw

lemma stripMap_mem_verticalStrip {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) {w : ℂ} (hw : ‖w‖ < 1) :
    stripMap θ w ∈ Complex.HadamardThreeLines.verticalStrip 0 1 := by
  have h := abs_arg_lt_pi_div_two_iff.2 (Or.inl (re_neg_I_mul_cayleyInv_pos hθ hw))
  rw [abs_lt] at h
  change 0 < (stripMap θ w).re ∧ (stripMap θ w).re < 1
  rw [stripMap_re]
  have hπ := Real.pi_pos
  constructor
  · have : -(1 / 2 : ℝ) < arg (-I * cayleyInv θ w) / π := by
      rw [lt_div_iff₀ hπ]; linarith
    linarith
  · have : arg (-I * cayleyInv θ w) / π < 1 / 2 := by
      rw [div_lt_iff₀ hπ]; linarith
    linarith

lemma analyticAt_stripMap {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) {w : ℂ} (hw : ‖w‖ < 1) :
    AnalyticAt ℂ (stripMap θ) w := by
  have hw1 : 1 - w ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h, norm_one] at hw; exact lt_irrefl _ hw
  have hc : AnalyticAt ℂ (cayleyInv θ) w := by
    unfold cayleyInv
    exact (analyticAt_const.sub (analyticAt_id.mul analyticAt_const)).div
      (analyticAt_const.sub analyticAt_id) hw1
  unfold stripMap
  refine analyticAt_const.sub ((analyticAt_const.mul ?_).div analyticAt_const
    (ofReal_ne_zero.2 Real.pi_ne_zero))
  exact (analyticAt_const.mul hc).clog
    (mem_slitPlane_iff.2 (Or.inl (re_neg_I_mul_cayleyInv_pos hθ hw)))

lemma exp_pi_theta_I (θ : ℝ) :
    exp (π * θ * I) = (Real.cos (π * θ) : ℂ) + Real.sin (π * θ) * I := by
  rw [show (π : ℂ) * θ * I = ((π * θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
  push_cast; ring

lemma exp_neg_pi_theta_I (θ : ℝ) :
    exp (-(π * θ * I)) = (Real.cos (π * θ) : ℂ) - Real.sin (π * θ) * I := by
  rw [show -((π : ℂ) * θ * I) = ((-(π * θ) : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
  push_cast; rw [Complex.cos_neg, Complex.sin_neg]; ring

lemma cayleyInv_circleMap_re (θ φ : ℝ) :
    (cayleyInv θ (circleMap 0 1 φ)).re =
      2 * (Real.cos (π * θ) - Real.cos (φ - π * θ)) / normSq (1 - circleMap 0 1 φ) := by
  rw [cayleyInv, exp_pi_theta_I, exp_neg_pi_theta_I, div_re, circleMap_zero, ofReal_one, one_mul,
    Complex.exp_mul_I]
  simp only [← ofReal_cos, ← ofReal_sin, normSq_apply, sub_re, sub_im, one_re, one_im, add_re,
    add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
  rw [Real.cos_sub, ← add_div]
  congr 1
  linear_combination Real.cos (π * θ) * Real.sin_sq_add_cos_sq φ

lemma normSq_circleMap (φ : ℝ) : normSq (circleMap 0 1 φ) = 1 := by
  rw [normSq_eq_norm_sq, norm_circleMap_zero, abs_one, one_pow]

lemma cayleyInv_circleMap_im (θ φ : ℝ) : (cayleyInv θ (circleMap 0 1 φ)).im = 0 := by
  rw [cayleyInv_im, normSq_circleMap, sub_self, mul_zero, zero_div]

lemma normSq_one_sub_circleMap_pos {φ : ℝ} (h0 : 0 < φ) (h1 : φ < 2 * π) :
    0 < normSq (1 - circleMap 0 1 φ) := by
  refine normSq_pos.2 fun h => ?_
  have h' : circleMap 0 1 φ = 1 := (sub_eq_zero.1 h).symm
  have hre : Real.cos φ = 1 := by
    have := congrArg Complex.re h'
    simpa [circleMap, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin] using this
  rw [Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) h1] at hre
  linarith

lemma cos_sub_cos_eq (θ φ : ℝ) :
    Real.cos (π * θ) - Real.cos (φ - π * θ) = 2 * Real.sin (φ / 2) * Real.sin (φ / 2 - π * θ) := by
  rw [Real.cos_sub_cos, show (π * θ - (φ - π * θ)) / 2 = -(φ / 2 - π * θ) by ring, Real.sin_neg,
    show (π * θ + (φ - π * θ)) / 2 = φ / 2 by ring]
  ring

lemma stripMap_re_of_cayleyInv_pos {θ : ℝ} {w : ℂ} (him : (cayleyInv θ w).im = 0)
    (hre : 0 < (cayleyInv θ w).re) : (stripMap θ w).re = 0 := by
  have hw : cayleyInv θ w = ((cayleyInv θ w).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [stripMap_re, hw, show -I * ((cayleyInv θ w).re : ℂ) = ((cayleyInv θ w).re : ℂ) * (-I) by
    ring, arg_real_mul _ hre, arg_neg_I]
  field_simp
  ring

lemma stripMap_re_of_cayleyInv_neg {θ : ℝ} {w : ℂ} (him : (cayleyInv θ w).im = 0)
    (hre : (cayleyInv θ w).re < 0) : (stripMap θ w).re = 1 := by
  have hw : cayleyInv θ w = ((cayleyInv θ w).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [stripMap_re, hw, show -I * ((cayleyInv θ w).re : ℂ) = ((-(cayleyInv θ w).re : ℝ) : ℂ) * I by
    push_cast; ring, arg_real_mul _ (by linarith), arg_I]
  field_simp
  ring

lemma cayleyInv_circleMap_re_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) {φ : ℝ}
    (hφ : φ ∈ Set.Ioo (2 * π * θ) (2 * π)) : 0 < (cayleyInv θ (circleMap 0 1 φ)).re := by
  obtain ⟨h0, h1⟩ := hφ
  have hπ := Real.pi_pos
  have hφ0 : 0 < φ := by nlinarith [hθ.1]
  rw [cayleyInv_circleMap_re, cos_sub_cos_eq]
  have := normSq_one_sub_circleMap_pos hφ0 h1
  have hs1 : 0 < Real.sin (φ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs2 : 0 < Real.sin (φ / 2 - π * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by nlinarith [hθ.1])
  positivity

lemma cayleyInv_circleMap_re_neg {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) {φ : ℝ}
    (hφ : φ ∈ Set.Ioo 0 (2 * π * θ)) : (cayleyInv θ (circleMap 0 1 φ)).re < 0 := by
  obtain ⟨h0, h1⟩ := hφ
  have hπ := Real.pi_pos
  have hφ1 : φ < 2 * π := by nlinarith [hθ.2]
  rw [cayleyInv_circleMap_re, cos_sub_cos_eq]
  have hn := normSq_one_sub_circleMap_pos h0 hφ1
  have hs1 : 0 < Real.sin (φ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs2 : Real.sin (φ / 2 - π * θ) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [show 2 * π * θ = 2 * (π * θ) by ring])
      (by nlinarith [hθ.1, hθ.2])
  have : 2 * (2 * Real.sin (φ / 2) * Real.sin (φ / 2 - π * θ)) < 0 := by
    have := mul_pos (two_pos (α := ℝ)) hs1
    nlinarith
  exact div_neg_of_neg_of_pos this hn

/-- The arc `2πθ < φ < 2π` of the unit circle is mapped to the line `re z = 0`. -/
lemma stripMap_circleMap_re_eq_zero {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) {φ : ℝ}
    (hφ : φ ∈ Set.Ioo (2 * π * θ) (2 * π)) : (stripMap θ (circleMap 0 1 φ)).re = 0 :=
  stripMap_re_of_cayleyInv_pos (cayleyInv_circleMap_im θ φ) (cayleyInv_circleMap_re_pos hθ hφ)

/-- The arc `0 < φ < 2πθ` of the unit circle is mapped to the line `re z = 1`. -/
lemma stripMap_circleMap_re_eq_one {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) {φ : ℝ}
    (hφ : φ ∈ Set.Ioo 0 (2 * π * θ)) : (stripMap θ (circleMap 0 1 φ)).re = 1 :=
  stripMap_re_of_cayleyInv_neg (cayleyInv_circleMap_im θ φ) (cayleyInv_circleMap_re_neg hθ hφ)

/-- `stripMap` is continuous at boundary points of the disc off the two arcs' endpoints. -/
lemma continuousAt_stripMap_circleMap {θ : ℝ} {φ : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 2 * π)
    (hre : (cayleyInv θ (circleMap 0 1 φ)).re ≠ 0) :
    ContinuousAt (stripMap θ) (circleMap 0 1 φ) := by
  have hw1 : 1 - circleMap 0 1 φ ≠ 0 := normSq_pos.1 (normSq_one_sub_circleMap_pos hφ0 hφ1)
  have hc : ContinuousAt (cayleyInv θ) (circleMap 0 1 φ) := by
    unfold cayleyInv
    exact (continuousAt_const.sub (continuousAt_id.mul continuousAt_const)).div
      (continuousAt_const.sub continuousAt_id) hw1
  have hslit : -I * cayleyInv θ (circleMap 0 1 φ) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; right; simpa using hre
  unfold stripMap
  exact continuousAt_const.sub (((continuousAt_const.mul
    ((continuousAt_const.mul hc).clog hslit))).div_const _)

/-! ## Jensen's inequality for `exp`, in the form `avg log u ≤ (1/a) log avg u^a` -/

lemma integral_log_le {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : 0 < μ.real Set.univ)
    {u : ℝ → ℝ} (hu0 : ∀ x, 0 ≤ u x) (hupos : ∀ᵐ x ∂μ, 0 < u x)
    (hlog : Integrable (fun x => Real.log (u x)) μ) {a : ℝ} (ha : 0 < a)
    (hua : Integrable (fun x => u x ^ a) μ) :
    ∫ x, Real.log (u x) ∂μ ≤
      μ.real Set.univ / a * Real.log ((μ.real Set.univ)⁻¹ * ∫ x, u x ^ a ∂μ) := by
  set L := μ.real Set.univ
  set c := L⁻¹ * ∫ x, u x ^ a ∂μ
  have hint : 0 < ∫ x, u x ^ a ∂μ := by
    rw [integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun x =>
      Real.rpow_nonneg (hu0 x) a) hua]
    have hU : μ Set.univ ≠ 0 := fun h => by simp [L, Measure.real, h] at hμ
    have hnull : μ {x | ¬ 0 < u x} = 0 := ae_iff.1 hupos
    have hsub : {x | 0 < u x} ⊆ Function.support fun x => u x ^ a :=
      fun x hx => (Real.rpow_pos_of_pos hx a).ne'
    refine pos_iff_ne_zero.2 fun h0 => hU ?_
    refine le_antisymm ?_ bot_le
    calc μ Set.univ ≤ μ {x | 0 < u x} + μ {x | 0 < u x}ᶜ := measure_univ_le_add_compl _
      _ = 0 := by rw [measure_mono_null hsub h0, zero_add]; exact hnull
  have hc : 0 < c := by positivity
  -- pointwise: `a log y ≤ log c + y^a / c - 1`
  have hpt : ∀ᵐ x ∂μ, a * Real.log (u x) ≤ Real.log c + u x ^ a / c - 1 := by
    filter_upwards [hupos] with x hx
    have h1 := Real.log_le_sub_one_of_pos (div_pos (Real.rpow_pos_of_pos hx a) hc)
    rw [Real.log_div (Real.rpow_pos_of_pos hx a).ne' hc.ne', Real.log_rpow hx] at h1
    linarith
  have hR : Integrable (fun x => Real.log c + u x ^ a / c - 1) μ :=
    ((integrable_const (Real.log c)).add (hua.div_const c)).sub (integrable_const 1)
  have hmono := integral_mono_ae (hlog.const_mul a) hR hpt
  have hI : ∫ x, (Real.log c + u x ^ a / c - 1) ∂μ =
      L * Real.log c - L + (∫ x, u x ^ a ∂μ) / c := by
    rw [integral_sub (by exact (integrable_const _).add (hua.div_const c) :
      Integrable (fun x => Real.log c + u x ^ a / c) μ) (integrable_const 1),
      integral_add (integrable_const _) (hua.div_const c), integral_div, integral_const,
      integral_const, smul_eq_mul, smul_eq_mul]
    ring
  have hLc : (∫ x, u x ^ a ∂μ) / c = L := by
    simp only [c]; field_simp
  rw [integral_const_mul, hI, hLc] at hmono
  have key : a * ∫ x, Real.log (u x) ∂μ ≤ L * Real.log c := by linarith
  calc ∫ x, Real.log (u x) ∂μ = (a * ∫ x, Real.log (u x) ∂μ) / a := by field_simp
    _ ≤ (L * Real.log c) / a := by gcongr
    _ = L / a * Real.log c := by ring

/-- Exponentiated form of `integral_log_le`. -/
lemma exp_avg_log_le {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : 0 < μ.real Set.univ)
    {u : ℝ → ℝ} (hu0 : ∀ x, 0 ≤ u x) (hupos : ∀ᵐ x ∂μ, 0 < u x)
    (hlog : Integrable (fun x => Real.log (u x)) μ) {a : ℝ} (ha : 0 < a)
    (hua : Integrable (fun x => u x ^ a) μ) :
    Real.exp (a * ((μ.real Set.univ)⁻¹ * ∫ x, Real.log (u x) ∂μ)) ≤
      (μ.real Set.univ)⁻¹ * ∫ x, u x ^ a ∂μ := by
  have h := integral_log_le hμ hu0 hupos hlog ha hua
  have hint : 0 < ∫ x, u x ^ a ∂μ := by
    have hU : μ Set.univ ≠ 0 := fun h => by simp [Measure.real, h] at hμ
    rw [integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun x =>
      Real.rpow_nonneg (hu0 x) a) hua]
    have hnull : μ {x | ¬ 0 < u x} = 0 := ae_iff.1 hupos
    have hsub : {x | 0 < u x} ⊆ Function.support fun x => u x ^ a :=
      fun x hx => (Real.rpow_pos_of_pos hx a).ne'
    refine pos_iff_ne_zero.2 fun h0 => hU ?_
    refine le_antisymm ?_ bot_le
    calc μ Set.univ ≤ μ {x | 0 < u x} + μ {x | 0 < u x}ᶜ := measure_univ_le_add_compl _
      _ = 0 := by rw [measure_mono_null hsub h0, zero_add]; exact hnull
  have hc : 0 < (μ.real Set.univ)⁻¹ * ∫ x, u x ^ a ∂μ := by positivity
  calc Real.exp (a * ((μ.real Set.univ)⁻¹ * ∫ x, Real.log (u x) ∂μ))
      ≤ Real.exp (Real.log ((μ.real Set.univ)⁻¹ * ∫ x, u x ^ a ∂μ)) := by
        gcongr
        rw [← mul_assoc, mul_comm a, mul_assoc]
        calc (μ.real Set.univ)⁻¹ * (a * ∫ x, Real.log (u x) ∂μ)
            ≤ (μ.real Set.univ)⁻¹ * (a * (μ.real Set.univ / a *
                Real.log ((μ.real Set.univ)⁻¹ * ∫ x, u x ^ a ∂μ))) := by gcongr
          _ = _ := by field_simp
    _ = _ := Real.exp_log hc

/-! ## Zeros of an analytic function on a circle are null -/

lemma ae_ne_zero_circleMap {H : ℂ → ℂ} (hH : AnalyticOnNhd ℂ H (ball 0 1)) (h0 : H 0 ≠ 0)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᵐ φ ∂(volume : Measure ℝ), H (circleMap 0 ρ φ) ≠ 0 := by
  have h1 : H ⁻¹' {0}ᶜ ∈ Filter.codiscreteWithin (ball (0 : ℂ) 1) :=
    hH.preimage_zero_mem_codiscreteWithin h0 (mem_ball_self one_pos) (Metric.isConnected_ball one_pos)
  have h2 : H ⁻¹' {0}ᶜ ∈ Filter.codiscreteWithin (sphere (0 : ℂ) |ρ|) := by
    refine Filter.codiscreteWithin_mono (fun z hz => ?_) h1
    rw [mem_sphere_zero_iff_norm, abs_of_pos hρ0] at hz
    rw [mem_ball_zero_iff]; linarith
  have h3 := circleMap_preimage_codiscrete (c := 0) hρ0.ne' h2
  have h4 := ae_restrict_le_codiscreteWithin (μ := (volume : Measure ℝ)) MeasurableSet.univ h3
  rw [Measure.restrict_univ] at h4
  exact h4

/-! ## The disc inequality at radius `ρ < 1`, split into two arcs -/

lemma real_restrict_Ioc {a b : ℝ} (hab : a ≤ b) :
    ((volume : Measure ℝ).restrict (Set.Ioc a b)).real Set.univ = b - a := by
  simp [Measure.real, Real.volume_Ioc, hab]

lemma arc_estimate {H : ℂ → ℂ} (hH : AnalyticOnNhd ℂ H (ball 0 1)) (h0 : H 0 ≠ 0)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 2 * π)
    {a : ℝ} (ha : 0 < a) :
    Real.exp (a * ((t - s)⁻¹ * ∫ φ in Set.Ioc s t, Real.log ‖H (circleMap 0 ρ φ)‖)) ≤
      (t - s)⁻¹ * ∫ φ in Set.Ioc s t, ‖H (circleMap 0 ρ φ)‖ ^ a := by
  have hsub : ∀ φ, circleMap 0 ρ φ ∈ ball (0 : ℂ) 1 := fun φ => by
    rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hρ0]; exact hρ1
  have hcont : Continuous fun φ => H (circleMap 0 ρ φ) :=
    hH.continuousOn.comp_continuous (continuous_circleMap 0 ρ) hsub
  have hLog : Integrable (fun φ => Real.log ‖H (circleMap 0 ρ φ)‖)
      ((volume : Measure ℝ).restrict (Set.Ioc s t)) := by
    have hci : CircleIntegrable (fun z => Real.log ‖H z‖) 0 ρ := by
      refine MeromorphicOn.circleIntegrable_log_norm ?_
      refine (hH.mono fun z hz => ?_).meromorphicOn
      rw [mem_sphere_zero_iff_norm, abs_of_pos hρ0] at hz
      rw [mem_ball_zero_iff]; linarith
    have h2π : (0 : ℝ) ≤ 2 * π := by positivity
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hst.le).1 (hci.mono_set ?_)
    rw [Set.uIcc_of_le hst.le, Set.uIcc_of_le h2π]
    exact Set.Icc_subset_Icc hs ht
  have h := exp_avg_log_le (μ := (volume : Measure ℝ).restrict (Set.Ioc s t))
    (u := fun φ => ‖H (circleMap 0 ρ φ)‖) (by rw [real_restrict_Ioc hst.le]; linarith)
    (fun _ => norm_nonneg _)
    (ae_restrict_of_ae ((ae_ne_zero_circleMap hH h0 hρ0 hρ1).mono fun φ hφ => norm_pos_iff.2 hφ))
    hLog ha ((hcont.norm.rpow_const fun _ => Or.inr ha.le).integrableOn_Ioc)
  rwa [real_restrict_Ioc hst.le] at h

/-- Jensen's inequality at radius `ρ < 1`, with the circle split into the arcs
`(0, 2πθ]` (weight `θ`, exponent `a₁`) and `(2πθ, 2π]` (weight `1-θ`, exponent `a₀`). -/
theorem norm_le_arcs {H : ℂ → ℂ} (hH : AnalyticOnNhd ℂ H (ball 0 1)) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀)
    (ha₁ : 0 < a₁) :
    ‖H 0‖ ≤ ((2 * π - 2 * π * θ)⁻¹ *
        ∫ φ in Set.Ioc (2 * π * θ) (2 * π), ‖H (circleMap 0 ρ φ)‖ ^ a₀) ^ ((1 - θ) / a₀) *
      ((2 * π * θ - 0)⁻¹ * ∫ φ in Set.Ioc 0 (2 * π * θ), ‖H (circleMap 0 ρ φ)‖ ^ a₁) ^ (θ / a₁) := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hπ := Real.pi_pos
  have hA : 0 < 2 * π * θ := by positivity
  have hB : 2 * π * θ < 2 * π := by nlinarith
  rcases eq_or_ne (H 0) 0 with hz | hz
  · rw [hz, norm_zero]
    refine mul_nonneg (Real.rpow_nonneg (mul_nonneg ?_ (integral_nonneg fun _ => by positivity)) _)
      (Real.rpow_nonneg (mul_nonneg ?_ (integral_nonneg fun _ => by positivity)) _)
    · rw [inv_nonneg]; linarith
    · rw [inv_nonneg]; linarith
  set f : ℝ → ℝ := fun φ => Real.log ‖H (circleMap 0 ρ φ)‖
  have hclosed : closedBall (0 : ℂ) |ρ| ⊆ ball 0 1 := fun z hz => by
    rw [mem_closedBall_zero_iff, abs_of_pos hρ0] at hz
    rw [mem_ball_zero_iff]; linarith
  have hJ := log_norm_le_circleAverage (c := 0) hρ0 (hH.mono hclosed) hz
  have hci : CircleIntegrable (fun z => Real.log ‖H z‖) 0 ρ :=
    MeromorphicOn.circleIntegrable_log_norm
      ((hH.mono (sphere_subset_closedBall.trans hclosed)).meromorphicOn)
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hI1 : IntervalIntegrable f volume 0 (2 * π * θ) := hci.mono_set (by
    rw [Set.uIcc_of_le hA.le, Set.uIcc_of_le h2π]; exact Set.Icc_subset_Icc le_rfl hB.le)
  have hI0 : IntervalIntegrable f volume (2 * π * θ) (2 * π) := hci.mono_set (by
    rw [Set.uIcc_of_le hB.le, Set.uIcc_of_le h2π]; exact Set.Icc_subset_Icc hA.le le_rfl)
  rw [circleAverage_def, smul_eq_mul, ← intervalIntegral.integral_add_adjacent_intervals hI1 hI0,
    intervalIntegral.integral_of_le hA.le, intervalIntegral.integral_of_le hB.le] at hJ
  set X₁ := ∫ φ in Set.Ioc 0 (2 * π * θ), f φ
  set X₀ := ∫ φ in Set.Ioc (2 * π * θ) (2 * π), f φ
  have E₀ := arc_estimate hH hz hρ0 hρ1 hA.le hB le_rfl ha₀
  have E₁ := arc_estimate hH hz hρ0 hρ1 le_rfl hA hB.le ha₁
  calc ‖H 0‖ = Real.exp (Real.log ‖H 0‖) := (Real.exp_log (norm_pos_iff.2 hz)).symm
    _ ≤ Real.exp ((2 * π)⁻¹ * (X₁ + X₀)) := Real.exp_le_exp.2 hJ
    _ = Real.exp (a₀ * ((2 * π - 2 * π * θ)⁻¹ * X₀)) ^ ((1 - θ) / a₀) *
        Real.exp (a₁ * ((2 * π * θ - 0)⁻¹ * X₁)) ^ (θ / a₁) := by
      rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
      congr 1
      have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
      field_simp
      ring
    _ ≤ _ := by gcongr

/-! ## Composition with a function on the strip and the limit `ρ → 1` -/

lemma isOpen_verticalStrip : IsOpen (HadamardThreeLines.verticalStrip 0 1) :=
  isOpen_Ioo.preimage continuous_re

lemma closure_verticalStrip :
    closure (HadamardThreeLines.verticalStrip 0 1) = HadamardThreeLines.verticalClosedStrip 0 1 := by
  rw [HadamardThreeLines.verticalStrip, closure_preimage_re, closure_Ioo zero_ne_one]
  rfl

lemma analyticOnNhd_comp_stripMap {G : ℂ → ℂ}
    (hG : DiffContOnCl ℂ G (HadamardThreeLines.verticalStrip 0 1)) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) : AnalyticOnNhd ℂ (fun w => G (stripMap θ w)) (ball 0 1) := by
  refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) isOpen_ball
  have hw' : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
  have hGd : DifferentiableAt ℂ G (stripMap θ w) :=
    hG.differentiableOn.differentiableAt
      (isOpen_verticalStrip.mem_nhds (stripMap_mem_verticalStrip hθ hw'))
  exact (hGd.comp w (analyticAt_stripMap hθ hw').differentiableAt).differentiableWithinAt

lemma circleMap_mem_ball {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (φ : ℝ) :
    circleMap 0 ρ φ ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hρ0]; exact hρ1

lemma tendsto_comp_stripMap {G : ℂ → ℂ}
    (hG : DiffContOnCl ℂ G (HadamardThreeLines.verticalStrip 0 1)) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) {φ : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 2 * π)
    (hre : (cayleyInv θ (circleMap 0 1 φ)).re ≠ 0) :
    Filter.Tendsto (fun ρ : ℝ => G (stripMap θ (circleMap 0 ρ φ))) (nhdsWithin 1 (Set.Iio 1))
      (nhds (G (stripMap θ (circleMap 0 1 φ)))) := by
  have hc : Filter.Tendsto (fun ρ : ℝ => circleMap 0 ρ φ) (nhdsWithin 1 (Set.Iio 1))
      (nhds (circleMap 0 1 φ)) := by
    have : Continuous fun ρ : ℝ => circleMap 0 ρ φ := by unfold circleMap; fun_prop
    exact this.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ρ in nhdsWithin (1 : ℝ) (Set.Iio 1),
      stripMap θ (circleMap 0 ρ φ) ∈ HadamardThreeLines.verticalStrip 0 1 := by
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with ρ hρ
    exact stripMap_mem_verticalStrip hθ (mem_ball_zero_iff.1 (circleMap_mem_ball hρ.1 hρ.2 φ))
  have hs := (continuousAt_stripMap_circleMap hφ0 hφ1 hre).tendsto.comp hc
  have hmem : stripMap θ (circleMap 0 1 φ) ∈ closure (HadamardThreeLines.verticalStrip 0 1) :=
    mem_closure_of_tendsto hs hev
  exact (hG.continuousOn _ hmem).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hs, hev.mono fun _ h => subset_closure h⟩)

lemma tendsto_arc_integral {G : ℂ → ℂ}
    (hG : DiffContOnCl ℂ G (HadamardThreeLines.verticalStrip 0 1)) {B : ℝ}
    (hB : ∀ z ∈ HadamardThreeLines.verticalClosedStrip 0 1, ‖G z‖ ≤ B) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ 2 * π)
    (hre : ∀ φ ∈ Set.Ioo s t, (cayleyInv θ (circleMap 0 1 φ)).re ≠ 0) {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (fun ρ : ℝ => ∫ φ in Set.Ioc s t, ‖G (stripMap θ (circleMap 0 ρ φ))‖ ^ a)
      (nhdsWithin 1 (Set.Iio 1))
      (nhds (∫ φ in Set.Ioc s t, ‖G (stripMap θ (circleMap 0 1 φ))‖ ^ a)) := by
  have hev := Ioo_mem_nhdsLT (zero_lt_one' ℝ)
  have hcl : HadamardThreeLines.verticalStrip 0 1 ⊆ HadamardThreeLines.verticalClosedStrip 0 1 :=
    fun z hz => ⟨hz.1.le, hz.2.le⟩
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => B ^ a) ?_ ?_
    (integrable_const _) ?_
  · filter_upwards [hev] with ρ hρ
    have hcont : Continuous fun φ => G (stripMap θ (circleMap 0 ρ φ)) :=
      (analyticOnNhd_comp_stripMap hG hθ).continuousOn.comp_continuous (continuous_circleMap 0 ρ)
        (circleMap_mem_ball hρ.1 hρ.2)
    exact (hcont.norm.rpow_const fun _ => Or.inr ha.le).aestronglyMeasurable
  · filter_upwards [hev] with ρ hρ
    refine Filter.Eventually.of_forall fun φ => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    exact Real.rpow_le_rpow (norm_nonneg _) (hB _ (hcl (stripMap_mem_verticalStrip hθ
      (mem_ball_zero_iff.1 (circleMap_mem_ball hρ.1 hρ.2 φ))))) ha.le
  · have hae : ∀ᵐ φ ∂(volume : Measure ℝ).restrict (Set.Ioc s t), φ ∈ Set.Ioo s t := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]; exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hae] with φ hφ
    have h0 : 0 < φ := lt_of_le_of_lt hs hφ.1
    have h1 : φ < 2 * π := lt_of_lt_of_le hφ.2 ht
    exact ((tendsto_comp_stripMap hG hθ h0 h1 (hre φ hφ)).norm.rpow_const (Or.inr ha.le))

/-- Jensen's inequality on the boundary arcs (`ρ = 1`), for bounded `G` continuous on the closed
strip and holomorphic inside. -/
theorem norm_le_boundary_arcs {G : ℂ → ℂ}
    (hG : DiffContOnCl ℂ G (HadamardThreeLines.verticalStrip 0 1)) {B : ℝ}
    (hB : ∀ z ∈ HadamardThreeLines.verticalClosedStrip 0 1, ‖G z‖ ≤ B) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) :
    ‖G θ‖ ≤ ((2 * π - 2 * π * θ)⁻¹ * ∫ φ in Set.Ioc (2 * π * θ) (2 * π),
        ‖G (stripMap θ (circleMap 0 1 φ))‖ ^ a₀) ^ ((1 - θ) / a₀) *
      ((2 * π * θ - 0)⁻¹ * ∫ φ in Set.Ioc 0 (2 * π * θ),
        ‖G (stripMap θ (circleMap 0 1 φ))‖ ^ a₁) ^ (θ / a₁) := by
  have hπ := Real.pi_pos
  have hA : 0 < 2 * π * θ := by have := hθ.1; positivity
  have hB' : 2 * π * θ < 2 * π := by nlinarith [hθ.2]
  have hT₀ := tendsto_arc_integral hG hB hθ hA.le le_rfl
    (fun φ hφ => (cayleyInv_circleMap_re_pos hθ hφ).ne') ha₀
  have hT₁ := tendsto_arc_integral hG hB hθ le_rfl hB'.le
    (fun φ hφ => (cayleyInv_circleMap_re_neg hθ hφ).ne) ha₁
  have hT := ((hT₀.const_mul (2 * π - 2 * π * θ)⁻¹).rpow_const
    (Or.inr (div_nonneg (sub_nonneg.2 hθ.2.le) ha₀.le))).mul
    ((hT₁.const_mul (2 * π * θ - 0)⁻¹).rpow_const (Or.inr (div_nonneg hθ.1.le ha₁.le)))
  refine ge_of_tendsto hT ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with ρ hρ
  have h := norm_le_arcs (analyticOnNhd_comp_stripMap hG hθ) hθ hρ.1 hρ.2 ha₀ ha₁
  rwa [stripMap_zero hθ] at h

/-! ## From arcs of the circle to measures on the boundary lines -/

lemma measurable_stripMap (θ : ℝ) : Measurable (stripMap θ) := by
  unfold stripMap cayleyInv
  fun_prop

lemma ofReal_setIntegral_le {f : ℝ → ℝ} {s t : ℝ} (hf0 : ∀ φ, 0 ≤ f φ) :
    ENNReal.ofReal (∫ φ in Set.Ioc s t, f φ) ≤ ∫⁻ φ in Set.Ioc s t, ENNReal.ofReal (f φ) := by
  by_cases hfi : Integrable f ((volume : Measure ℝ).restrict (Set.Ioc s t))
  · rw [ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0)]
  · rw [integral_undef hfi, ENNReal.ofReal_zero]; exact bot_le

lemma ofReal_avg_le_lintegral_map {T : ℝ → ℝ} (hT : Measurable T) {s t : ℝ} (hst : s < t)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) {f : ℝ → ℝ} (hf0 : ∀ φ, 0 ≤ f φ)
    (hfg : ∀ φ ∈ Set.Ioo s t, ENNReal.ofReal (f φ) = g (T φ)) :
    ENNReal.ofReal ((t - s)⁻¹ * ∫ φ in Set.Ioc s t, f φ) ≤
      ∫⁻ x, g x ∂((ENNReal.ofReal (t - s))⁻¹ •
        ((volume : Measure ℝ).restrict (Set.Ioc s t)).map T) := by
  rw [lintegral_smul_measure, lintegral_map hg hT,
    ENNReal.ofReal_mul (inv_nonneg.2 (sub_nonneg.2 hst.le)),
    ENNReal.ofReal_inv_of_pos (sub_pos.2 hst), smul_eq_mul]
  gcongr
  refine (ofReal_setIntegral_le hf0).trans_eq ?_
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
  exact setLIntegral_congr_fun measurableSet_Ioo hfg

lemma isProbabilityMeasure_arc {T : ℝ → ℝ} (hT : Measurable T) {s t : ℝ} (hst : s < t) :
    IsProbabilityMeasure ((ENNReal.ofReal (t - s))⁻¹ •
      ((volume : Measure ℝ).restrict (Set.Ioc s t)).map T) := by
  constructor
  rw [Measure.smul_apply, Measure.map_apply hT MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ, Real.volume_Ioc, smul_eq_mul,
    ENNReal.inv_mul_cancel (by simpa using hst) ENNReal.ofReal_ne_top]

/-- **(SJ)**, exponentiated form: the strip Poisson-Jensen inequality, with `ν₀, ν₁` the
normalized images of the two boundary arcs of the unit disc under the conformal map onto the
strip. -/
theorem exists_stripPoissonJensen {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ ν₀ ν₁ : Measure ℝ, IsProbabilityMeasure ν₀ ∧ IsProbabilityMeasure ν₁ ∧
      ∀ G : ℂ → ℂ, DiffContOnCl ℂ G (HadamardThreeLines.verticalStrip 0 1) →
        BddAbove ((fun z => ‖G z‖) '' HadamardThreeLines.verticalClosedStrip 0 1) →
        ∀ a₀ a₁ : ℝ, 0 < a₀ → 0 < a₁ →
          ‖G θ‖ₑ ≤ (∫⁻ t, ‖G (t * I)‖ₑ ^ a₀ ∂ν₀) ^ ((1 - θ) / a₀) *
            (∫⁻ t, ‖G (1 + t * I)‖ₑ ^ a₁ ∂ν₁) ^ (θ / a₁) := by
  have hπ := Real.pi_pos
  have hA : 0 < 2 * π * θ := by have := hθ.1; positivity
  have hB' : 2 * π * θ < 2 * π := by nlinarith [hθ.2]
  set T : ℝ → ℝ := fun φ => (stripMap θ (circleMap 0 1 φ)).im
  have hT : Measurable T :=
    measurable_im.comp ((measurable_stripMap θ).comp (continuous_circleMap 0 1).measurable)
  refine ⟨_, _, isProbabilityMeasure_arc hT hB', isProbabilityMeasure_arc hT hA, ?_⟩
  intro G hG hbdd a₀ a₁ ha₀ ha₁
  obtain ⟨B, hB⟩ := hbdd
  have hBs : ∀ z ∈ HadamardThreeLines.verticalClosedStrip 0 1, ‖G z‖ ≤ B :=
    fun z hz => hB ⟨z, hz, rfl⟩
  have h := norm_le_boundary_arcs hG hBs hθ ha₀ ha₁
  have hGc : ContinuousOn G (HadamardThreeLines.verticalClosedStrip 0 1) :=
    closure_verticalStrip ▸ hG.continuousOn
  have hc₀ : Continuous fun t : ℝ => G (t * I) :=
    hGc.comp_continuous (by fun_prop) fun t => by
      change 0 ≤ ((t : ℂ) * I).re ∧ ((t : ℂ) * I).re ≤ 1; simp
  have hc₁ : Continuous fun t : ℝ => G (1 + t * I) :=
    hGc.comp_continuous (by fun_prop) fun t => by
      change 0 ≤ (1 + (t : ℂ) * I).re ∧ (1 + (t : ℂ) * I).re ≤ 1; simp
  set f : ℝ → ℝ := fun φ => ‖G (stripMap θ (circleMap 0 1 φ))‖
  have he₀ : 0 ≤ (1 - θ) / a₀ := div_nonneg (sub_nonneg.2 hθ.2.le) ha₀.le
  have he₁ : 0 ≤ θ / a₁ := div_nonneg hθ.1.le ha₁.le
  have hR₀ : 0 ≤ (2 * π - 2 * π * θ)⁻¹ * ∫ φ in Set.Ioc (2 * π * θ) (2 * π), f φ ^ a₀ :=
    mul_nonneg (inv_nonneg.2 (by linarith)) (integral_nonneg fun _ => by positivity)
  have hR₁ : 0 ≤ (2 * π * θ - 0)⁻¹ * ∫ φ in Set.Ioc 0 (2 * π * θ), f φ ^ a₁ :=
    mul_nonneg (inv_nonneg.2 (by linarith)) (integral_nonneg fun _ => by positivity)
  calc ‖G θ‖ₑ = ENNReal.ofReal ‖G θ‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (((2 * π - 2 * π * θ)⁻¹ *
          ∫ φ in Set.Ioc (2 * π * θ) (2 * π), f φ ^ a₀) ^ ((1 - θ) / a₀) *
        ((2 * π * θ - 0)⁻¹ * ∫ φ in Set.Ioc 0 (2 * π * θ), f φ ^ a₁) ^ (θ / a₁)) :=
      ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal ((2 * π - 2 * π * θ)⁻¹ *
          ∫ φ in Set.Ioc (2 * π * θ) (2 * π), f φ ^ a₀) ^ ((1 - θ) / a₀) *
        ENNReal.ofReal ((2 * π * θ - 0)⁻¹ *
          ∫ φ in Set.Ioc 0 (2 * π * θ), f φ ^ a₁) ^ (θ / a₁) := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hR₀ _), ENNReal.ofReal_rpow_of_nonneg hR₀ he₀,
        ENNReal.ofReal_rpow_of_nonneg hR₁ he₁]
    _ ≤ _ := by
      gcongr
      · refine ofReal_avg_le_lintegral_map (f := fun φ => f φ ^ a₀) hT hB'
          (hc₀.measurable.enorm.pow_const a₀) (fun _ => by positivity) fun φ hφ => ?_
        have hz : stripMap θ (circleMap 0 1 φ) = (T φ : ℂ) * I := by
          apply Complex.ext <;> simp [T, stripMap_circleMap_re_eq_zero hθ hφ]
        simp only [f, hz]
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ha₀.le]
      · refine ofReal_avg_le_lintegral_map (f := fun φ => f φ ^ a₁) hT hA
          (hc₁.measurable.enorm.pow_const a₁) (fun _ => by positivity) fun φ hφ => ?_
        have hz : stripMap θ (circleMap 0 1 φ) = 1 + (T φ : ℂ) * I := by
          apply Complex.ext <;> simp [T, stripMap_circleMap_re_eq_one hθ hφ]
        simp only [f, hz]
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ha₁.le]

/-- **(SJ)** holds for every `θ ∈ (0,1)`. -/
theorem stripPoissonJensen {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) : StripPoissonJensen θ :=
  exists_stripPoissonJensen hθ

/-- **N60.** Bilinear complex interpolation with quasi-Banach targets: for `T` bilinear on
finitely supported sequences on `ℤ`, bounds `‖T f g‖_{r_i} ≤ M_i ‖f‖_{p_i} ‖g‖_{q_i}` (`i = 0,1`)
imply `‖T f g‖_{r_θ} ≤ M₀^{1-θ} M₁^θ ‖f‖_{p_θ} ‖g‖_{q_θ}`. (All exponents only need to be
positive; the blueprint's `1 ≤ pᵢ, qᵢ` and `Mᵢ > 0` are special cases.) -/
theorem interp_bilinear
    (T : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ))
    {p₀ p₁ q₀ q₁ r₀ r₁ M₀ M₁ θ p q r : ℝ}
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (h₀ : ∀ f g : ℤ →₀ ℂ, eLpNorm (T f g) (ENNReal.ofReal r₀) Measure.count ≤
      ENNReal.ofReal M₀ * eLpNorm f (ENNReal.ofReal p₀) Measure.count *
        eLpNorm g (ENNReal.ofReal q₀) Measure.count)
    (h₁ : ∀ f g : ℤ →₀ ℂ, eLpNorm (T f g) (ENNReal.ofReal r₁) Measure.count ≤
      ENNReal.ofReal M₁ * eLpNorm f (ENNReal.ofReal p₁) Measure.count *
        eLpNorm g (ENNReal.ofReal q₁) Measure.count)
    (hθ : θ ∈ Set.Ioo 0 1) (hp : 1 / p = (1 - θ) / p₀ + θ / p₁)
    (hq : 1 / q = (1 - θ) / q₀ + θ / q₁) (hr : 1 / r = (1 - θ) / r₀ + θ / r₁)
    (f g : ℤ →₀ ℂ) :
    eLpNorm (T f g) (ENNReal.ofReal r) Measure.count ≤
      ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f (ENNReal.ofReal p) Measure.count *
        eLpNorm g (ENNReal.ofReal q) Measure.count :=
  interp_bilinear_of_poissonJensen T hp₀ hp₁ hq₀ hq₁ hr₀ hr₁ hM₀ hM₁ h₀ h₁ hθ hp hq hr
    (stripPoissonJensen hθ) f g

/-- **N60, the case used in the paper**: `1/rᵢ = 1/pᵢ + 1/qᵢ`, `1 ≤ pᵢ, qᵢ`, and then
`1/r = 1/p + 1/q` at the interpolated point. -/
theorem interp_bilinear_holder
    (T : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ))
    {p₀ p₁ q₀ q₁ r₀ r₁ M₀ M₁ θ p q r : ℝ}
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁)
    (hr₀ : 1 / r₀ = 1 / p₀ + 1 / q₀) (hr₁ : 1 / r₁ = 1 / p₁ + 1 / q₁)
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (h₀ : ∀ f g : ℤ →₀ ℂ, eLpNorm (T f g) (ENNReal.ofReal r₀) Measure.count ≤
      ENNReal.ofReal M₀ * eLpNorm f (ENNReal.ofReal p₀) Measure.count *
        eLpNorm g (ENNReal.ofReal q₀) Measure.count)
    (h₁ : ∀ f g : ℤ →₀ ℂ, eLpNorm (T f g) (ENNReal.ofReal r₁) Measure.count ≤
      ENNReal.ofReal M₁ * eLpNorm f (ENNReal.ofReal p₁) Measure.count *
        eLpNorm g (ENNReal.ofReal q₁) Measure.count)
    (hθ : θ ∈ Set.Ioo 0 1) (hp : 1 / p = (1 - θ) / p₀ + θ / p₁)
    (hq : 1 / q = (1 - θ) / q₀ + θ / q₁) (hr : 1 / r = 1 / p + 1 / q) (f g : ℤ →₀ ℂ) :
    eLpNorm (T f g) (ENNReal.ofReal r) Measure.count ≤
      ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f (ENNReal.ofReal p) Measure.count *
        eLpNorm g (ENNReal.ofReal q) Measure.count :=
  interp_bilinear_holder_of_poissonJensen T hp₀ hp₁ hq₀ hq₁ hr₀ hr₁ hM₀ hM₁ h₀ h₁ hθ hp hq hr
    (stripPoissonJensen hθ) f g

end PrimeBHT.Interpolation
