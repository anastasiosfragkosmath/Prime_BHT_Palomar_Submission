module

public import PrimeBHT.TimeFrequency.Tile.Gram.Pair
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Same-interval Bessel inequalities: (G4), (G5) of blueprint node C2 (`TT.gram`)

* (G4) `sum_norm_sq_pairing_le_weighted`: if `φ_i` is adapted (exponent `N ≥ 3`) to `(I, [a_i, b_i))`, the
  `[a_i, b_i)` pairwise disjoint, then for `g ∈ L²`
  `Σ_i |⟨g, φ_i⟩|² ≤ besselConst N · ∫ |g|² (1 + |x - c(I)|/|I|)^{-2}`, `besselConst N = 4/(2N-1) + 4/(2N-3)`;
  tri-tile form `sum_norm_sq_pairing_sameInterval_le_weighted` (sum over `t ∈ P` with `I_t = I_{t₀}`).
* (G5) `sum_norm_sq_pairing_le`, `sum_norm_sq_pairing_sameInterval_le`: the same with `‖g‖₂²`.

## Correction to the blueprint's proof of (G4)

The blueprint's proof (annuli `A_j`, bumps `η_j`, Gram matrix with `(1+|m|)^{-N'}` decay via Bernstein,
Schur, Minkowski) is correct but not needed. A shorter proof, used here, needs neither (G0) nor
`|I||ω| = 1` nor the lattice structure of the frequencies, only that the frequency intervals are disjoint:
with `γ_i = ⟨g, φ_i⟩`, `F = Σ γ_i φ_i`, `W = 1 + |x - c(I)|/|I|`,
`Σ|γ_i|² = ⟨g, F⟩ ≤ (A/2)∫|g|²W^{-2} + (1/2A)∫|F|²W²`, and
`∫|F|²W² ≤ 2∫|F|² + 2|I|^{-2}∫|(x - c(I))F|² ≤ A Σ|γ_i|²` because both families `φ_i` and
`(x - c(I))φ_i` are orthogonal: `𝓕[(x - c)φ_i]` is a combination of `𝓕φ_i` and its derivative
(`Real.hasDerivAt_fourier`), hence vanishes off `[a_i, b_i]`, and two such closed intervals meet in at most
one point. Then `|φ_i| ≤ |I|^{-1/2}W^{-N}` gives `∫|φ_i|² ≤ 2/(2N-1)`, `∫|(x-c)φ_i|² ≤ 2|I|²/(2N-3)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform

namespace PrimeBHT.TimeFrequency.Tile

open PrimeBHT.Statements

/-! ### The moment `x ↦ (x - c) φ(x)` has the same Fourier support -/

/-- `x ↦ (x - c) φ(x)`. -/
noncomputable def momentFn (c : ℝ) (φ : ℝ → ℂ) (x : ℝ) : ℂ := ((x - c : ℝ) : ℂ) * φ x

theorem norm_momentFn_le {N : ℕ} {I ω : Set ℝ} {φ : ℝ → ℂ} (hφ : IsAdapted N I ω φ)
    (hI : 0 < (volume I).toReal) (x : ℝ) :
    ‖momentFn (intervalCentre I) φ x‖ ≤ (volume I).toReal ^ (1 / 2 : ℝ) *
      (1 + |x - intervalCentre I| / (volume I).toReal) ^ (-((N : ℝ) - 1)) := by
  set L := (volume I).toReal
  set c := intervalCentre I
  set t := 1 + |x - c| / L
  have ht : 0 < t := by have : 0 ≤ |x - c| / L := div_nonneg (abs_nonneg _) hI.le; linarith
  have hxc : |x - c| ≤ L * t := by
    simp only [t]
    rw [mul_add, mul_one, mul_div_cancel₀ _ hI.ne']
    linarith [hI]
  unfold momentFn
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |x - c| * ‖φ x‖ ≤ (L * t) * (L ^ (-(1 / 2 : ℝ)) * t ^ (-(N : ℝ))) :=
        mul_le_mul hxc (IsAdapted.norm_le hφ x) (norm_nonneg _) (by positivity)
    _ = (L * L ^ (-(1 / 2 : ℝ))) * (t * t ^ (-(N : ℝ))) := by ring
    _ = L ^ (1 / 2 : ℝ) * t ^ (-((N : ℝ) - 1)) := by
        congr 1
        · have h := Real.rpow_add hI (1 : ℝ) (-(1 / 2 : ℝ))
          rw [Real.rpow_one] at h
          rw [← h]
          norm_num
        · have h := Real.rpow_add ht (1 : ℝ) (-(N : ℝ))
          rw [Real.rpow_one] at h
          rw [← h]
          congr 1
          ring

theorem integrable_momentFn {N : ℕ} (hN : 3 ≤ N) {I ω : Set ℝ} {φ : ℝ → ℂ}
    (hφ : IsAdapted N I ω φ) (hI : 0 < (volume I).toReal) :
    Integrable (momentFn (intervalCentre I) φ) := by
  have hN1 : (1 : ℝ) < (N : ℝ) - 1 := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  refine Integrable.mono' ((integrable_one_add_abs_sub_div_rpow hN1 (intervalCentre I) hI).const_mul
    ((volume I).toReal ^ (1 / 2 : ℝ))) ?_ (ae_of_all _ (norm_momentFn_le hφ hI))
  exact (Continuous.mul (by fun_prop) (IsAdapted.continuous hφ)).aestronglyMeasurable

theorem continuous_momentFn {N : ℕ} {I ω : Set ℝ} {φ : ℝ → ℂ} (hφ : IsAdapted N I ω φ) (c : ℝ) :
    Continuous (momentFn c φ) :=
  Continuous.mul (by fun_prop) (IsAdapted.continuous hφ)

/-- The Fourier transform of the moment `(x - c(I)) φ(x)` vanishes off `Icc a b` if `φ` is adapted to
`(I, Ico a b)` (it is a combination of `𝓕φ` and its derivative). -/
theorem fourier_momentFn_eq_zero {N : ℕ} (hN : 3 ≤ N) {I : Set ℝ} {a b : ℝ} {φ : ℝ → ℂ}
    (hφ : IsAdapted N I (Ico a b) φ) (hI : 0 < (volume I).toReal) {w : ℝ} (hw : w ∉ Icc a b) :
    𝓕 (momentFn (intervalCentre I) φ) w = 0 := by
  set c := intervalCentre I
  have hφi : Integrable φ := hφ.2.1
  have hm : Integrable (momentFn c φ) := integrable_momentFn hN hφ hI
  have hxφ : Integrable (fun x : ℝ => x • φ x) := by
    have : (fun x : ℝ => x • φ x) = fun x => momentFn c φ x + (c : ℂ) * φ x := by
      funext x
      simp only [momentFn, Complex.real_smul]
      push_cast
      ring
    rw [this]
    exact hm.add (hφi.const_mul _)
  have hzero : 𝓕 φ =ᶠ[𝓝 w] fun _ => 0 := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hw] with ξ hξ
    exact hφ.2.2.1 ξ (fun h => hξ (Ico_subset_Icc_self h))
  have hd : HasDerivAt (𝓕 φ) 0 w := (hasDerivAt_const w (0 : ℂ)).congr_of_eventuallyEq hzero
  have h0 := (Real.hasDerivAt_fourier hφi hxφ w).unique hd
  have hφw : 𝓕 φ w = 0 := hzero.self_of_nhds
  have hsplit : momentFn c φ = (-2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
      (fun x : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * x) • φ x) + (-(c : ℂ)) • φ := by
    funext x
    have hpi : (-2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    simp only [momentFn, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp
    ring
  have hint1 : Integrable (fun x : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * x) • φ x) := by
    have : (fun x : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * x) • φ x) =
        fun x => (-2 * (Real.pi : ℂ) * Complex.I) * (x • φ x) := by
      funext x
      simp only [smul_eq_mul, Complex.real_smul]
      ring
    rw [this]
    exact hxφ.const_mul _
  rw [hsplit]
  change VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) _ w = 0
  rw [VectorFourier.fourierIntegral_add Real.continuous_fourierChar continuous_inner
    (hint1.smul _) (hφi.smul _)]
  rw [Pi.add_apply, VectorFourier.fourierIntegral_const_smul, VectorFourier.fourierIntegral_const_smul]
  change (-2 * (Real.pi : ℂ) * Complex.I)⁻¹ • 𝓕 (fun x : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * x) • φ x) w +
    (-(c : ℂ)) • 𝓕 φ w = 0
  rw [h0, hφw]
  simp

/-! ### `L²` bookkeeping -/

theorem integrable_mul_conj {f g : ℝ → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) :
    Integrable (fun x => f x * (starRingEnd ℂ) (g x)) :=
  hf.integrable_mul hg.star

theorem ofReal_norm_sq_eq_mul_conj (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem pairing_self (u : ℝ → ℂ) : pairing u u = ((∫ x, ‖u x‖ ^ 2 : ℝ) : ℂ) := by
  unfold pairing
  rw [← integral_complex_ofReal]
  congr 1
  funext x
  rw [ofReal_norm_sq_eq_mul_conj]

/-- `∫ |Σ c_i u_i|² = Σ |c_i|² ∫ |u_i|²` for pairwise orthogonal `u_i ∈ L²`. -/
theorem integral_norm_sq_sum_of_orthogonal {ι : Type*} (T : Finset ι) (u : ι → ℝ → ℂ) (c : ι → ℂ)
    (hu : ∀ i ∈ T, MemLp (u i) 2)
    (horth : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → pairing (u i) (u j) = 0) :
    ∫ x, ‖∑ i ∈ T, c i * u i x‖ ^ 2 = ∑ i ∈ T, ‖c i‖ ^ 2 * ∫ x, ‖u i x‖ ^ 2 := by
  apply Complex.ofReal_injective
  have hint : ∀ i ∈ T, ∀ j ∈ T, Integrable (fun x => u i x * (starRingEnd ℂ) (u j x)) :=
    fun i hi j hj => integrable_mul_conj (hu i hi) (hu j hj)
  calc ((∫ x, ‖∑ i ∈ T, c i * u i x‖ ^ 2 : ℝ) : ℂ)
      = ∫ x, ∑ i ∈ T, ∑ j ∈ T,
          c i * (starRingEnd ℂ) (c j) * (u i x * (starRingEnd ℂ) (u j x)) := by
        rw [← integral_complex_ofReal]
        congr 1
        funext x
        rw [ofReal_norm_sq_eq_mul_conj, map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]
        ring
    _ = ∑ i ∈ T, ∑ j ∈ T, c i * (starRingEnd ℂ) (c j) * pairing (u i) (u j) := by
        rw [integral_finsetSum _ (fun i hi => integrable_finsetSum _
          (fun j hj => (hint i hi j hj).const_mul _))]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [integral_finsetSum _ (fun j hj => (hint i hi j hj).const_mul _)]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul]
        rfl
    _ = ∑ i ∈ T, c i * (starRingEnd ℂ) (c i) * pairing (u i) (u i) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.sum_eq_single_of_mem i hi
          (fun j hj hji => by rw [horth i hi j hj (Ne.symm hji), mul_zero])]
    _ = _ := by
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pairing_self, ← ofReal_norm_sq_eq_mul_conj]
        push_cast
        ring

/-- A function with `|f(x)| ≤ A (1 + |x - c|/L)^{-p}`, `2p > 1`, is in `L²` with
`∫ |f|² ≤ A² · 2L/(2p - 1)`. -/
theorem memLp_two_and_integral_sq_le {f : ℝ → ℂ} (hf : AEStronglyMeasurable f) {A p c L : ℝ}
    (hL : 0 < L) (hp : 1 < 2 * p)
    (hb : ∀ x, ‖f x‖ ≤ A * (1 + |x - c| / L) ^ (-p)) :
    MemLp f 2 ∧ ∫ x, ‖f x‖ ^ 2 ≤ A ^ 2 * (2 * L / (2 * p - 1)) := by
  have hb2 : ∀ x, ‖f x‖ ^ 2 ≤ A ^ 2 * (1 + |x - c| / L) ^ (-(2 * p)) := by
    intro x
    have ht : 0 ≤ 1 + |x - c| / L := by positivity
    calc ‖f x‖ ^ 2 ≤ (A * (1 + |x - c| / L) ^ (-p)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hb x) 2
      _ = A ^ 2 * (1 + |x - c| / L) ^ (-(2 * p)) := by
          rw [mul_pow, ← Real.rpow_natCast ((1 + |x - c| / L) ^ (-p)), ← Real.rpow_mul ht]
          congr 2
          push_cast
          ring
  have hmaj : Integrable (fun x => A ^ 2 * (1 + |x - c| / L) ^ (-(2 * p))) :=
    (integrable_one_add_abs_sub_div_rpow hp c hL).const_mul _
  have hint : Integrable (fun x => ‖f x‖ ^ 2) :=
    hmaj.mono' (hf.norm.pow 2) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hb2 x)
  refine ⟨(memLp_two_iff_integrable_sq_norm hf).2 hint, ?_⟩
  calc ∫ x, ‖f x‖ ^ 2 ≤ ∫ x, A ^ 2 * (1 + |x - c| / L) ^ (-(2 * p)) :=
        integral_mono hint hmaj hb2
    _ = _ := by rw [integral_const_mul, integral_one_add_abs_sub_div_rpow hp c hL]

theorem IsAdapted.memLp_two_and_integral_sq_le {N : ℕ} (hN : 1 ≤ N) {I ω : Set ℝ} {φ : ℝ → ℂ}
    (hφ : IsAdapted N I ω φ) (hI : 0 < (volume I).toReal) :
    MemLp φ 2 ∧ ∫ x, ‖φ x‖ ^ 2 ≤ 2 / (2 * (N : ℝ) - 1) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨h1, h2⟩ := PrimeBHT.TimeFrequency.Tile.memLp_two_and_integral_sq_le
    (IsAdapted.continuous hφ).aestronglyMeasurable hI (by linarith) (IsAdapted.norm_le hφ)
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  have hsq : ((volume I).toReal ^ (-(1 / 2 : ℝ))) ^ 2 = ((volume I).toReal)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hI.le]
    norm_num
    exact Real.rpow_neg_one _
  rw [hsq]
  have : 2 * (N : ℝ) - 1 ≠ 0 := by linarith
  field_simp

theorem memLp_two_and_integral_sq_momentFn_le {N : ℕ} (hN : 2 ≤ N) {I ω : Set ℝ} {φ : ℝ → ℂ}
    (hφ : IsAdapted N I ω φ) (hI : 0 < (volume I).toReal) :
    MemLp (momentFn (intervalCentre I) φ) 2 ∧
      ∫ x, ‖momentFn (intervalCentre I) φ x‖ ^ 2 ≤
        (volume I).toReal ^ 2 * (2 / (2 * (N : ℝ) - 3)) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨h1, h2⟩ := PrimeBHT.TimeFrequency.Tile.memLp_two_and_integral_sq_le
    (continuous_momentFn hφ _).aestronglyMeasurable hI (p := (N : ℝ) - 1) (by linarith)
    (norm_momentFn_le hφ hI)
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  have hsq : ((volume I).toReal ^ (1 / 2 : ℝ)) ^ 2 = (volume I).toReal := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hI.le]
    norm_num
  rw [hsq]
  have : 2 * (N : ℝ) - 3 ≠ 0 := by linarith
  have : 2 * ((N : ℝ) - 1) - 1 = 2 * (N : ℝ) - 3 := by ring
  rw [this]
  field_simp

/-! ### (G4) the weighted same-interval Bessel inequality, (G5) the unweighted one -/

/-- The constant of (G4): `4/(2N-1) + 4/(2N-3)` (`≤ 8/(2N-3)`, decreasing in `N`). -/
noncomputable def besselConst (N : ℕ) : ℝ := 4 / (2 * (N : ℝ) - 1) + 4 / (2 * (N : ℝ) - 3)

theorem besselConst_pos {N : ℕ} (hN : 2 ≤ N) : 0 < besselConst N := by
  have : (2 : ℝ) ≤ N := by exact_mod_cast hN
  unfold besselConst
  have h1 : 0 < 2 * (N : ℝ) - 1 := by linarith
  have h2 : 0 < 2 * (N : ℝ) - 3 := by linarith
  positivity

theorem mul_le_half_sq_add {a b A : ℝ} (hA : 0 < A) :
    a * b ≤ A / 2 * a ^ 2 + 1 / (2 * A) * b ^ 2 := by
  have : A / 2 * a ^ 2 + 1 / (2 * A) * b ^ 2 - a * b = (A * a - b) ^ 2 / (2 * A) := by
    field_simp
    ring
  have h2 : 0 ≤ (A * a - b) ^ 2 / (2 * A) := by positivity
  linarith

/-- **(G4)** Weighted Bessel inequality for packets with a common time interval: if `φ_i` is adapted
(exponent `N ≥ 3`) to `(I, [a_i, b_i))` with pairwise disjoint frequency intervals, then for `g ∈ L²`
`Σ_i |⟨g, φ_i⟩|² ≤ C_N ∫ |g|² (1 + |x - c(I)|/|I|)^{-2}`, `C_N = besselConst N`.

Proof (no Bernstein inequality needed): with `γ_i = ⟨g, φ_i⟩`, `F = Σ γ_i φ_i`, `W = 1 + |x - c(I)|/|I|`,
`Σ|γ_i|² = ⟨g, F⟩ ≤ ∫ |g| W^{-1} · |F| W`; the `φ_i` and the moments `(x - c(I)) φ_i` are both
orthogonal (their Fourier transforms live on the closed intervals `[a_i, b_i]`), so
`∫ |F|² W² ≤ 2∫|F|² + 2|I|^{-2}∫|(x - c(I))F|² ≤ C_N Σ|γ_i|²`. -/
theorem sum_norm_sq_pairing_le_weighted {ι : Type*} (T : Finset ι) {N : ℕ} (hN : 3 ≤ N)
    {I : Set ℝ} (hI : 0 < (volume I).toReal) (a b : ι → ℝ)
    (hdisj : (T : Set ι).PairwiseDisjoint fun i => Ico (a i) (b i)) (φ : ι → ℝ → ℂ)
    (hφ : ∀ i ∈ T, IsAdapted N I (Ico (a i) (b i)) (φ i)) {g : ℝ → ℂ} (hg : MemLp g 2) :
    ∑ i ∈ T, ‖pairing g (φ i)‖ ^ 2 ≤
      besselConst N * ∫ x, ‖g x‖ ^ 2 *
        (1 + |x - intervalCentre I| / (volume I).toReal) ^ (-2 : ℝ) := by
  set L := (volume I).toReal
  set c := intervalCentre I
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  set γ : ι → ℂ := fun i => pairing g (φ i)
  set S : ℝ := ∑ i ∈ T, ‖γ i‖ ^ 2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  set A := besselConst N
  have hA : 0 < A := besselConst_pos (by omega)
  set F : ℝ → ℂ := fun x => ∑ i ∈ T, γ i * φ i x
  set M : ℝ → ℂ := fun x => ∑ i ∈ T, γ i * momentFn c (φ i) x
  set W : ℝ → ℝ := fun x => 1 + |x - c| / L
  have hW : ∀ x, 0 < W x := fun x => by
    have : 0 ≤ |x - c| / L := by positivity
    simp only [W]
    linarith
  have hWc : Continuous W := by fun_prop
  have hφ2 := fun i hi => IsAdapted.memLp_two_and_integral_sq_le (by omega) (hφ i hi) hI
  have hm2 := fun i hi => memLp_two_and_integral_sq_momentFn_le (by omega) (hφ i hi) hI
  have hdisj' : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (Ico (a i) (b i)) (Ico (a j) (b j)) :=
    fun i hi j hj hij => hdisj (Finset.mem_coe.2 hi) (Finset.mem_coe.2 hj) hij
  have horthφ : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → pairing (φ i) (φ j) = 0 := fun i hi j hj hij =>
    pairing_eq_zero_of_disjoint (hφ i hi) (hφ j hj) (Metric.isBounded_Ico _ _) (hdisj' i hi j hj hij)
  have horthm : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      pairing (momentFn c (φ i)) (momentFn c (φ j)) = 0 := fun i hi j hj hij =>
    pairing_eq_zero_of_fourier_Icc (integrable_momentFn hN (hφ i hi) hI)
      (continuous_momentFn (hφ j hj) c) (integrable_momentFn hN (hφ j hj) hI)
      (fun _ hξ => fourier_momentFn_eq_zero hN (hφ i hi) hI hξ)
      (fun _ hξ => fourier_momentFn_eq_zero hN (hφ j hj) hI hξ) (hdisj' i hi j hj hij)
  -- the two orthogonal expansions
  have hF2 : ∫ x, ‖F x‖ ^ 2 ≤ S * (2 / (2 * (N : ℝ) - 1)) := by
    rw [integral_norm_sq_sum_of_orthogonal T φ γ (fun i hi => (hφ2 i hi).1) horthφ, Finset.sum_mul]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hφ2 i hi).2 (by positivity)
  have hM2 : ∫ x, ‖M x‖ ^ 2 ≤ S * (L ^ 2 * (2 / (2 * (N : ℝ) - 3))) := by
    rw [integral_norm_sq_sum_of_orthogonal T (fun i => momentFn c (φ i)) γ (fun i hi => (hm2 i hi).1)
      horthm, Finset.sum_mul]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hm2 i hi).2 (by positivity)
  have hFm : MemLp F 2 := memLp_finsetSum T fun i hi => (hφ2 i hi).1.const_mul (γ i)
  have hMm : MemLp M 2 := memLp_finsetSum T fun i hi => (hm2 i hi).1.const_mul (γ i)
  have hFi : Integrable (fun x => ‖F x‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hFm.aestronglyMeasurable).1 hFm
  have hMi : Integrable (fun x => ‖M x‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hMm.aestronglyMeasurable).1 hMm
  have hFc : Continuous F :=
    continuous_finsetSum _ fun i hi => continuous_const.mul (IsAdapted.continuous (hφ i hi))
  have hMF : ∀ x, ‖M x‖ = |x - c| * ‖F x‖ := by
    intro x
    have : M x = ((x - c : ℝ) : ℂ) * F x := by
      simp only [M, F, momentFn, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  -- the weighted bound for `F`
  have hFW : ∀ x, ‖F x‖ ^ 2 * W x ^ 2 ≤ 2 * ‖F x‖ ^ 2 + 2 / L ^ 2 * ‖M x‖ ^ 2 := by
    intro x
    set s := |x - c| / L
    have hs : |x - c| = L * s := by simp only [s]; field_simp
    have h1 : W x ^ 2 ≤ 2 + 2 * s ^ 2 := by
      have := sq_nonneg (1 - s)
      simp only [W]
      nlinarith
    have h2 : 2 / L ^ 2 * ‖M x‖ ^ 2 = 2 * s ^ 2 * ‖F x‖ ^ 2 := by
      rw [hMF, hs]
      field_simp
    rw [h2]
    have : 0 ≤ ‖F x‖ ^ 2 := by positivity
    nlinarith
  have hFWi : Integrable (fun x => ‖F x‖ ^ 2 * W x ^ 2) :=
    ((hFi.const_mul 2).add (hMi.const_mul (2 / L ^ 2))).mono'
      ((hFc.norm.pow 2).mul (hWc.pow 2)).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hFW x)
  have hFWle : ∫ x, ‖F x‖ ^ 2 * W x ^ 2 ≤ A * S := by
    calc ∫ x, ‖F x‖ ^ 2 * W x ^ 2 ≤ ∫ x, (2 * ‖F x‖ ^ 2 + 2 / L ^ 2 * ‖M x‖ ^ 2) :=
          integral_mono hFWi ((hFi.const_mul 2).add (hMi.const_mul (2 / L ^ 2))) hFW
      _ = 2 * (∫ x, ‖F x‖ ^ 2) + 2 / L ^ 2 * ∫ x, ‖M x‖ ^ 2 := by
          rw [integral_add (hFi.const_mul 2) (hMi.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ 2 * (S * (2 / (2 * (N : ℝ) - 1))) + 2 / L ^ 2 * (S * (L ^ 2 * (2 / (2 * (N : ℝ) - 3)))) := by
          gcongr
      _ = A * S := by
          simp only [A, besselConst]
          field_simp
          ring
  -- duality
  have hdual : ((S : ℝ) : ℂ) = ∫ x, g x * (starRingEnd ℂ) (F x) := by
    have hint : ∀ i ∈ T, Integrable (fun x => g x * (starRingEnd ℂ) (φ i x)) :=
      fun i hi => integrable_mul_conj hg (hφ2 i hi).1
    calc ((S : ℝ) : ℂ) = ∑ i ∈ T, (starRingEnd ℂ) (γ i) * ∫ x, g x * (starRingEnd ℂ) (φ i x) := by
          simp only [S]
          rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ofReal_norm_sq_eq_mul_conj, mul_comm]
          rfl
      _ = ∑ i ∈ T, ∫ x, (starRingEnd ℂ) (γ i) * (g x * (starRingEnd ℂ) (φ i x)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_const_mul]
      _ = ∫ x, ∑ i ∈ T, (starRingEnd ℂ) (γ i) * (g x * (starRingEnd ℂ) (φ i x)) := by
          rw [integral_finsetSum _ fun i hi => (hint i hi).const_mul _]
      _ = _ := by
          congr 1
          funext x
          simp only [F, map_sum, map_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
  have hgF : Integrable (fun x => ‖g x‖ * ‖F x‖) := by
    refine (integrable_mul_conj hg hFm).norm.congr (ae_of_all _ fun x => ?_)
    simp only [norm_mul, Complex.norm_conj]
  have hS_le : S ≤ ∫ x, ‖g x‖ * ‖F x‖ := by
    calc S = ‖((S : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0]
      _ = ‖∫ x, g x * (starRingEnd ℂ) (F x)‖ := by rw [hdual]
      _ ≤ ∫ x, ‖g x * (starRingEnd ℂ) (F x)‖ := norm_integral_le_integral_norm _
      _ = ∫ x, ‖g x‖ * ‖F x‖ := by simp only [norm_mul, Complex.norm_conj]
  -- the weight
  set V : ℝ → ℝ := fun x => W x ^ (-2 : ℝ)
  have hV : ∀ x, V x = (W x ^ 2)⁻¹ := fun x => by
    simp only [V]
    rw [Real.rpow_neg (hW x).le]
    norm_cast
  have hVc : Continuous V := hWc.rpow_const fun x => Or.inl (hW x).ne'
  have hgi : Integrable (fun x => ‖g x‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  have hgV : Integrable (fun x => ‖g x‖ ^ 2 * V x) := by
    refine hgi.mono' ((hg.aestronglyMeasurable.norm.pow 2).mul hVc.aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    have h1 : 1 ≤ W x ^ 2 := by
      have : 1 ≤ W x := by
        have : 0 ≤ |x - c| / L := by positivity
        simp only [W]
        linarith
      nlinarith
    have hV1 : V x ≤ 1 := by rw [hV]; exact inv_le_one_of_one_le₀ h1
    have hV0 : 0 ≤ V x := by rw [hV]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖g x‖ ^ 2 * V x ≤ ‖g x‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left hV1 (by positivity)
      _ = _ := mul_one _
  have hpt : ∀ x, ‖g x‖ * ‖F x‖ ≤ A / 2 * (‖g x‖ ^ 2 * V x) + 1 / (2 * A) * (‖F x‖ ^ 2 * W x ^ 2) := by
    intro x
    have hWx := hW x
    have h := mul_le_half_sq_add (a := ‖g x‖ * (W x)⁻¹) (b := ‖F x‖ * W x) hA
    have e1 : ‖g x‖ * (W x)⁻¹ * (‖F x‖ * W x) = ‖g x‖ * ‖F x‖ := by
      field_simp
    have e2 : (‖g x‖ * (W x)⁻¹) ^ 2 = ‖g x‖ ^ 2 * V x := by
      rw [hV, mul_pow, inv_pow]
    have e3 : (‖F x‖ * W x) ^ 2 = ‖F x‖ ^ 2 * W x ^ 2 := by ring
    rw [e1, e2, e3] at h
    exact h
  have hmain : S ≤ A / 2 * (∫ x, ‖g x‖ ^ 2 * V x) + 1 / (2 * A) * (A * S) := by
    calc S ≤ ∫ x, ‖g x‖ * ‖F x‖ := hS_le
      _ ≤ ∫ x, (A / 2 * (‖g x‖ ^ 2 * V x) + 1 / (2 * A) * (‖F x‖ ^ 2 * W x ^ 2)) :=
          integral_mono hgF ((hgV.const_mul _).add (hFWi.const_mul _)) hpt
      _ = A / 2 * (∫ x, ‖g x‖ ^ 2 * V x) + 1 / (2 * A) * ∫ x, ‖F x‖ ^ 2 * W x ^ 2 := by
          rw [integral_add (hgV.const_mul _) (hFWi.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ _ := by gcongr
  have hAS : 1 / (2 * A) * (A * S) = S / 2 := by field_simp
  rw [hAS] at hmain
  show S ≤ A * ∫ x, ‖g x‖ ^ 2 * V x
  linarith

/-! ### (G4), (G5) for tri-tile packets with a common time interval -/

theorem eq_of_timeInt_eq {t t' : ℤ × ℤ × ℤ} (h : timeInt t = timeInt t') :
    t.1 = t'.1 ∧ t.2.1 = t'.2.1 := by
  have h1 : (2 : ℝ) ^ t.1 = 2 ^ t'.1 := by rw [← volume_timeInt, ← volume_timeInt, h]
  have hs : t.1 = t'.1 := zpow_right_injective₀ (by norm_num) (by norm_num) h1
  refine ⟨hs, ?_⟩
  have h2 := intervalCentre_timeInt t
  rw [h, intervalCentre_timeInt, ← hs] at h2
  have hpos : (0 : ℝ) < 2 ^ t.1 := zpow_pos (by norm_num) _
  have h3 := mul_left_cancel₀ hpos.ne' h2
  have : (t.2.1 : ℝ) = t'.2.1 := by linarith
  exact_mod_cast this

/-- Distinct tri-tiles of one class `Idx_{s',α}` with the same time interval have disjoint frequency
intervals in every slot (C1 (c)). -/
theorem pairwiseDisjoint_freqInt_sameInterval {a b s' α : ℤ} (k : Fin 3)
    (P : Finset (ℤ × ℤ × ℤ)) (hP : ∀ t ∈ P, t ∈ triIdx s' α) (t₀ : ℤ × ℤ × ℤ) :
    ((P.filter fun t => timeInt t = timeInt t₀ : Finset _) : Set (ℤ × ℤ × ℤ)).PairwiseDisjoint
      fun t => freqInt a b k t := by
  intro t ht t' ht' hne
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ht ht'
  obtain ⟨hs, hv⟩ := eq_of_timeInt_eq (ht.2.trans ht'.2.symm)
  have hℓ : t.2.2 ≠ t'.2.2 := by
    intro hℓ
    exact hne (Prod.ext hs (Prod.ext hv hℓ))
  have hmod : t.2.2 ≡ t'.2.2 [ZMOD 3] := ((hP t ht.1).2).trans ((hP t' ht'.1).2).symm
  exact disjoint_freqInt_of_ne k hs hmod hℓ

/-- **(G4) for tri-tiles.** `Σ_{t ∈ P, I_t = I} |⟨g, φ_{t,k}⟩|² ≤ C_N ∫ |g|² (1 + |x - c(I)|/|I|)^{-2}`
for `I = I_{t₀}` and packets adapted to `(I_t, ω_{t,k})` with exponent `N ≥ 3`. -/
theorem sum_norm_sq_pairing_sameInterval_le_weighted {N : ℕ} (hN : 3 ≤ N) {a b s' α : ℤ}
    (k : Fin 3) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (P : Finset (ℤ × ℤ × ℤ))
    (hP : ∀ t ∈ P, t ∈ triIdx s' α)
    (hφ : ∀ t ∈ P, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) (t₀ : ℤ × ℤ × ℤ)
    {g : ℝ → ℂ} (hg : MemLp g 2) :
    ∑ t ∈ P with timeInt t = timeInt t₀, ‖pairing g (φ t k)‖ ^ 2 ≤
      besselConst N * ∫ x, ‖g x‖ ^ 2 * (1 + |x - intervalCentre (timeInt t₀)| /
        (volume (timeInt t₀)).toReal) ^ (-2 : ℝ) := by
  refine sum_norm_sq_pairing_le_weighted _ hN (by rw [volume_timeInt]; positivity)
    (fun t => (2 : ℝ) ^ (-t.1) * ((freqNum a b t k : ℝ) / 3))
    (fun t => (2 : ℝ) ^ (-t.1) * ((freqNum a b t k : ℝ) / 3 + 1))
    (pairwiseDisjoint_freqInt_sameInterval k P hP t₀) (fun t => φ t k) (fun t ht => ?_) hg
  rw [Finset.mem_filter] at ht
  rw [← ht.2]
  exact hφ t ht.1

end PrimeBHT.TimeFrequency.Tile
