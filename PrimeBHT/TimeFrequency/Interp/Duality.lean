module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# R6c, duality with simple test functions

The step `‖G‖_{L^r} ≤ sup_{h simple, ‖h‖_{r'} ≤ 1} |∫ G h|` used to turn the form bound R6c-II
into the operator bound for `r > 1` (blueprint `docs/x1-blueprint.md`, R6c-II, "In particular").

* `eLpNorm_le_of_forall_simpleFunc`: for `ν` σ-finite, `1 < r`, `G : β → ℂ` a.e. strongly
  measurable with `‖∫ G g‖ ≤ A ‖g‖_{r'}` for every simple `g` with `‖g‖_{r'} < ∞`,
  `‖G‖_{L^r} ≤ 2A` (the factor `2` comes from Mathlib's simple approximation
  `‖approxOn u‖ ≤ 2‖u‖`; it is harmless for the existence of a constant).
-/

@[expose] public section

namespace PrimeBHT.TimeFrequency.Interp

open MeasureTheory Filter Topology ComplexConjugate
open scoped ENNReal

local infixr:25 " →ₛ " => SimpleFunc

variable {β : Type*} [MeasurableSpace β] {ν : Measure β}

/-- The truncation sets `S_N = K_N ∩ {‖G‖ ≤ N}` (`K_N` the spanning sets of `ν`). -/
private noncomputable def truncSet (ν : Measure β) [SigmaFinite ν] (G : β → ℂ) (N : ℕ) : Set β :=
  spanningSets ν N ∩ {x | ‖G x‖ ≤ N}

private lemma measurableSet_truncSet [SigmaFinite ν] {G : β → ℂ} (hG : StronglyMeasurable G)
    (N : ℕ) : MeasurableSet (truncSet ν G N) :=
  (measurableSet_spanningSets ν N).inter
    (measurableSet_le hG.measurable.norm measurable_const)

private lemma truncSet_mono [SigmaFinite ν] (G : β → ℂ) : Monotone (truncSet ν G) := by
  intro N M h x hx
  refine ⟨monotone_spanningSets ν h hx.1, ?_⟩
  have : (N : ℝ) ≤ M := by exact_mod_cast h
  exact le_trans hx.2 this

private lemma exists_mem_truncSet [SigmaFinite ν] (G : β → ℂ) (x : β) :
    ∃ N, x ∈ truncSet ν G N := by
  obtain ⟨N₁, hN₁⟩ : ∃ N₁, x ∈ spanningSets ν N₁ := by
    have : x ∈ ⋃ i, spanningSets ν i := by rw [iUnion_spanningSets]; trivial
    exact Set.mem_iUnion.1 this
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge ‖G x‖
  refine ⟨max N₁ N₂, monotone_spanningSets ν (le_max_left _ _) hN₁, ?_⟩
  show ‖G x‖ ≤ ((max N₁ N₂ : ℕ) : ℝ)
  exact le_trans hN₂ (by exact_mod_cast le_max_right _ _)

/-- The key pointwise identity `G · (‖G‖^(r-2) conj G) = ‖G‖^r`. -/
private lemma mul_rpow_conj {r : ℝ} (hr : 0 < r) (z : ℂ) :
    z * (((‖z‖ ^ (r - 2) : ℝ) : ℂ) * conj z) = ((‖z‖ ^ r : ℝ) : ℂ) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Real.zero_rpow hr.ne']
  · have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
    have e : ‖z‖ ^ (r - 2) * ‖z‖ ^ 2 = ‖z‖ ^ r := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
      norm_num
    calc z * (((‖z‖ ^ (r - 2) : ℝ) : ℂ) * conj z)
        = ((‖z‖ ^ (r - 2) : ℝ) : ℂ) * (z * conj z) := by ring
      _ = ((‖z‖ ^ (r - 2) : ℝ) : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) := by
          rw [RCLike.mul_conj]; push_cast; rfl
      _ = ((‖z‖ ^ r : ℝ) : ℂ) := by rw [← Complex.ofReal_mul, e]

private lemma norm_rpow_conj {r : ℝ} (hr : 1 < r) (z : ℂ) :
    ‖((‖z‖ ^ (r - 2) : ℝ) : ℂ) * conj z‖ = ‖z‖ ^ (r - 1) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Real.zero_rpow (by linarith : r - 1 ≠ 0)]
  · have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc ‖z‖ ^ (r - 2) * ‖z‖ = ‖z‖ ^ (r - 2) * ‖z‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = ‖z‖ ^ (r - 1) := by rw [← Real.rpow_add hpos]; ring_nf

/-- Per truncation level: `∫_{S_N} ‖G‖^r ≤ (2A)^r`. -/
private lemma integral_truncSet_le [SigmaFinite ν] {r A : ℝ} (hr : 1 < r) (hA : 0 ≤ A)
    {G : β → ℂ} (hG : StronglyMeasurable G)
    (h : ∀ g : β →ₛ ℂ, eLpNorm g (ENNReal.ofReal (r / (r - 1))) ν < ∞ →
      ‖∫ x, G x * g x ∂ν‖ ≤ A * (eLpNorm g (ENNReal.ofReal (r / (r - 1))) ν).toReal)
    (N : ℕ) :
    ∫ x, (truncSet ν G N).indicator (fun x => ‖G x‖ ^ r) x ∂ν ≤ (2 * A) ^ r := by
  set S := truncSet ν G N
  have hS : MeasurableSet S := measurableSet_truncSet hG N
  have hSfin : ν S < ∞ :=
    (measure_mono Set.inter_subset_left).trans_lt (measure_spanningSets_lt_top ν N)
  have hr0 : 0 < r := by linarith
  set r' := r / (r - 1)
  have hr'0 : 0 < r' := div_pos hr0 (by linarith)
  have hrr' : (r - 1) * r' = r := by simp only [r']; field_simp
  have hinv : 1 / r + 1 / r' = 1 := by simp only [r']; field_simp; ring
  set φ : β → ℝ := S.indicator (fun x => ‖G x‖ ^ r)
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => Set.indicator_nonneg (fun _ _ => by positivity) x
  have hφmeas : StronglyMeasurable φ :=
    ((hG.norm.measurable.pow_const r).stronglyMeasurable).indicator hS
  have hφbd : ∀ x, ‖φ x‖ ≤ S.indicator (fun _ => (N : ℝ) ^ r) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      simp only [φ, Set.indicator_of_mem hx]
      rw [Real.norm_of_nonneg (by positivity)]
      exact Real.rpow_le_rpow (norm_nonneg _) hx.2 hr0.le
    · rw [Set.indicator_of_notMem hx]
      simp only [φ, Set.indicator_of_notMem hx, norm_zero, le_refl]
  have hφint : Integrable φ ν := by
    refine Integrable.mono' ?_ hφmeas.aestronglyMeasurable (ae_of_all _ hφbd)
    exact (integrable_indicator_iff hS).2 (integrableOn_const hSfin.ne)
  set I := ∫ x, φ x ∂ν
  have hI0 : 0 ≤ I := integral_nonneg hφ0
  -- the test function
  set u : β → ℂ := S.indicator (fun x => ((‖G x‖ ^ (r - 2) : ℝ) : ℂ) * conj (G x))
  have humeas : Measurable u := by
    refine Measurable.indicator ?_ hS
    have h1 : Measurable fun x => ((‖G x‖ ^ (r - 2) : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp (hG.measurable.norm.pow_const _)
    exact h1.mul (Complex.continuous_conj.measurable.comp hG.measurable)
  have hGu : ∀ x, G x * u x = ((φ x : ℝ) : ℂ) := by
    intro x
    by_cases hx : x ∈ S
    · simp only [u, φ, Set.indicator_of_mem hx]
      exact mul_rpow_conj hr0 (G x)
    · simp only [u, φ, Set.indicator_of_notMem hx, mul_zero, Complex.ofReal_zero]
  have hnormGu : ∀ x, ‖G x‖ * ‖u x‖ = φ x := by
    intro x
    rw [← norm_mul, hGu, Complex.norm_real, Real.norm_of_nonneg (hφ0 x)]
  have hnormu : ∀ x, ‖u x‖ ^ r' = φ x := by
    intro x
    by_cases hx : x ∈ S
    · simp only [u, φ, Set.indicator_of_mem hx]
      rw [norm_rpow_conj hr, ← Real.rpow_mul (norm_nonneg _), hrr']
    · simp only [u, φ, Set.indicator_of_notMem hx, norm_zero]
      exact Real.zero_rpow hr'0.ne'
  -- the `L^{r'}` norm of `u`
  have hu_norm : eLpNorm u (ENNReal.ofReal r') ν = ENNReal.ofReal (I ^ (1 / r')) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr'0) ENNReal.ofReal_ne_top
      humeas.aestronglyMeasurable, ENNReal.toReal_ofReal hr'0.le]
    have : ∫⁻ x, ‖u x‖ₑ ^ r' ∂ν = ENNReal.ofReal I := by
      rw [ofReal_integral_eq_lintegral_ofReal hφint (ae_of_all _ hφ0)]
      refine lintegral_congr fun x => ?_
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr'0.le, hnormu]
    rw [this, ENNReal.ofReal_rpow_of_nonneg hI0 (by positivity)]
  -- simple approximations of `u`
  set uj : ℕ → β →ₛ ℂ := fun j => SimpleFunc.approxOn u humeas Set.univ 0 (Set.mem_univ 0) j
  have huj : ∀ j x, ‖uj j x‖ ≤ 2 * ‖u x‖ := by
    intro j x
    have := SimpleFunc.norm_approxOn_zero_le humeas (Set.mem_univ 0) x j
    simp only [uj]
    linarith
  have hujlim : ∀ x, Tendsto (fun j => uj j x) atTop (𝓝 (u x)) := fun x =>
    SimpleFunc.tendsto_approxOn humeas (Set.mem_univ 0) (by simp)
  have hujnorm : ∀ j, eLpNorm (uj j) (ENNReal.ofReal r') ν ≤
      ENNReal.ofReal 2 * ENNReal.ofReal (I ^ (1 / r')) := by
    intro j
    rw [← hu_norm]
    exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul (uj j).aestronglyMeasurable
      (ae_of_all _ (huj j)) _
  have hbound : ∀ j, ‖∫ x, G x * uj j x ∂ν‖ ≤ A * (2 * I ^ (1 / r')) := by
    intro j
    have hfin : eLpNorm (uj j) (ENNReal.ofReal r') ν < ∞ :=
      (hujnorm j).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    refine (h (uj j) hfin).trans ?_
    gcongr
    calc (eLpNorm (uj j) (ENNReal.ofReal r') ν).toReal
        ≤ (ENNReal.ofReal 2 * ENNReal.ofReal (I ^ (1 / r'))).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            ENNReal.ofReal_lt_top).ne (hujnorm j)
      _ = 2 * I ^ (1 / r') := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num),
            ENNReal.toReal_ofReal (by positivity)]
  -- dominated convergence
  have hlim : Tendsto (fun j => ∫ x, G x * uj j x ∂ν) atTop (𝓝 (∫ x, G x * u x ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => 2 * φ x) (fun j => ?_)
      (hφint.const_mul 2) (fun j => ae_of_all _ fun x => ?_)
      (ae_of_all _ fun x => (hujlim x).const_mul (G x))
    · exact (hG.aestronglyMeasurable).mul (uj j).aestronglyMeasurable
    · rw [norm_mul, ← hnormGu]
      have := huj j x
      have := norm_nonneg (G x)
      nlinarith
  have hGuI : ∫ x, G x * u x ∂ν = (I : ℂ) := by
    simp_rw [hGu]
    exact integral_complex_ofReal
  have hmain : I ≤ A * (2 * I ^ (1 / r')) := by
    have := le_of_tendsto' (hlim.norm) hbound
    rwa [hGuI, Complex.norm_real, Real.norm_of_nonneg hI0] at this
  -- conclude
  rcases hI0.eq_or_lt with hI | hI
  · rw [← hI]; positivity
  · have hsplit : I = I ^ (1 / r) * I ^ (1 / r') := by
      rw [← Real.rpow_add hI, hinv, Real.rpow_one]
    have hpos : 0 < I ^ (1 / r') := by positivity
    have h1 : I ^ (1 / r) ≤ 2 * A := by
      have : I ^ (1 / r) * I ^ (1 / r') ≤ (2 * A) * I ^ (1 / r') := by
        rw [← hsplit]; linarith
      exact le_of_mul_le_mul_right this hpos
    calc I = (I ^ (1 / r)) ^ r := by
          rw [← Real.rpow_mul hI.le, one_div_mul_cancel hr0.ne', Real.rpow_one]
      _ ≤ (2 * A) ^ r := by gcongr

/-- **Duality with simple test functions.** For `ν` σ-finite and `1 < r`, if
`‖∫ G g dν‖ ≤ A ‖g‖_{r'}` for all simple `g` with `‖g‖_{r'} < ∞` (`r' = r/(r-1)`), then
`‖G‖_{L^r} ≤ 2A`. -/
theorem eLpNorm_le_of_forall_simpleFunc [SigmaFinite ν] {r A : ℝ} (hr : 1 < r) (hA : 0 ≤ A)
    {G : β → ℂ} (hG : AEStronglyMeasurable G ν)
    (h : ∀ g : β →ₛ ℂ, eLpNorm g (ENNReal.ofReal (r / (r - 1))) ν < ∞ →
      ‖∫ x, G x * g x ∂ν‖ ≤ A * (eLpNorm g (ENNReal.ofReal (r / (r - 1))) ν).toReal) :
    eLpNorm G (ENNReal.ofReal r) ν ≤ ENNReal.ofReal (2 * A) := by
  set G' := hG.mk G
  have hG' : StronglyMeasurable G' := hG.stronglyMeasurable_mk
  have hae : G =ᵐ[ν] G' := hG.ae_eq_mk
  have h' : ∀ g : β →ₛ ℂ, eLpNorm g (ENNReal.ofReal (r / (r - 1))) ν < ∞ →
      ‖∫ x, G' x * g x ∂ν‖ ≤ A * (eLpNorm g (ENNReal.ofReal (r / (r - 1))) ν).toReal := by
    intro g hg
    have : ∫ x, G' x * g x ∂ν = ∫ x, G x * g x ∂ν :=
      integral_congr_ae (hae.mono fun x hx => by simp only [hx])
    rw [this]
    exact h g hg
  rw [eLpNorm_congr_ae hae]
  have hr0 : 0 < r := by linarith
  set φ : ℕ → β → ℝ := fun N => (truncSet ν G' N).indicator (fun x => ‖G' x‖ ^ r)
  have hφ0 : ∀ N x, 0 ≤ φ N x := fun N x =>
    Set.indicator_nonneg (fun _ _ => by positivity) x
  have hφmeas : ∀ N, Measurable fun x => ENNReal.ofReal (φ N x) := fun N =>
    ENNReal.measurable_ofReal.comp
      ((hG'.norm.measurable.pow_const r).indicator (measurableSet_truncSet hG' N))
  have hmono : Monotone fun N x => ENNReal.ofReal (φ N x) := by
    intro N M hNM x
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hx : x ∈ truncSet ν G' N
    · simp only [φ, Set.indicator_of_mem hx, Set.indicator_of_mem (truncSet_mono G' hNM hx),
        le_refl]
    · simp only [φ, Set.indicator_of_notMem hx]
      exact hφ0 M x
  have hsup : ∀ x, ‖G' x‖ₑ ^ r = ⨆ N, ENNReal.ofReal (φ N x) := by
    intro x
    refine le_antisymm ?_ (iSup_le fun N => ?_)
    · obtain ⟨N, hN⟩ := exists_mem_truncSet (ν := ν) G' x
      refine le_trans (le_of_eq ?_) (le_iSup (fun N => ENNReal.ofReal (φ N x)) N)
      simp only [φ, Set.indicator_of_mem hN]
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le]
    · by_cases hx : x ∈ truncSet ν G' N
      · simp only [φ, Set.indicator_of_mem hx]
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le]
      · simp only [φ, Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
        exact zero_le
  have hlint : ∫⁻ x, ‖G' x‖ₑ ^ r ∂ν ≤ ENNReal.ofReal ((2 * A) ^ r) := by
    simp_rw [hsup]
    rw [lintegral_iSup hφmeas hmono]
    refine iSup_le fun N => ?_
    have hint : Integrable (φ N) ν := by
      refine Integrable.mono' (g := (truncSet ν G' N).indicator (fun _ => (N : ℝ) ^ r)) ?_
        ((hG'.norm.measurable.pow_const r).indicator
          (measurableSet_truncSet hG' N)).aestronglyMeasurable
        (ae_of_all _ fun x => ?_)
      · have hSfin : ν (truncSet ν G' N) < ∞ :=
          (measure_mono Set.inter_subset_left).trans_lt (measure_spanningSets_lt_top ν N)
        exact (integrable_indicator_iff (measurableSet_truncSet hG' N)).2
          (integrableOn_const (C := (N : ℝ) ^ r) hSfin.ne)
      · by_cases hx : x ∈ truncSet ν G' N
        · simp only [φ, Set.indicator_of_mem hx]
          rw [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ‖G' x‖ ^ r)]
          exact Real.rpow_le_rpow (norm_nonneg _) hx.2 hr0.le
        · simp only [φ, Set.indicator_of_notMem hx, norm_zero, le_refl]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (hφ0 N))]
    exact ENNReal.ofReal_le_ofReal (integral_truncSet_le hr hA hG' h' N)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr0) ENNReal.ofReal_ne_top
    hG'.aestronglyMeasurable, ENNReal.toReal_ofReal hr0.le]
  calc (∫⁻ x, ‖G' x‖ₑ ^ r ∂ν) ^ (1 / r) ≤ (ENNReal.ofReal ((2 * A) ^ r)) ^ (1 / r) := by
        gcongr
    _ = ENNReal.ofReal (2 * A) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          ← Real.rpow_mul (by positivity), mul_one_div_cancel hr0.ne', Real.rpow_one]

end PrimeBHT.TimeFrequency.Interp
