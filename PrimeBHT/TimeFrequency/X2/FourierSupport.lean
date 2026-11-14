module

public import PrimeBHT.TimeFrequency.X2.Classes
public import PrimeBHT.TimeFrequency.X2.ClassKernel
public import PrimeBHT.TimeFrequency.X2.Ortho.Fourier
public import PrimeBHT.TimeFrequency.X2.Paraproduct.Tensor
public import PrimeBHT.TimeFrequency.Tile.Gram.Pair
public import PrimeBHT.TimeFrequency.Tile.Gram.Bernstein

/-!
# X2, V13 foundations: the Fourier-support toolbox FS-1, FS-2 (FS-3 not provided, see below)

`docs/audits/X2-V13-route-check.md` §2.1.  Everything is stated for the scalar multiplier
`tm m f = 𝓕⁻ m * f` of `X2/Ortho/Fourier.lean` (`tmult m F x y = tm m (F · y) x`, so the vector statements are
coordinatewise).

* **Band-limited functions** `IsBandLimited g S` (continuous, integrable, `𝓕 g` vanishes off the bounded set `S`):
  closed under sums and scalar multiples; the tile pieces `gfun ψ m f` are band-limited (`isBandLimited_gfun`, reuse of
  V10's `fourier_gfun_eq_zero`); `tm n g = g` if `n = 1` on `S`, `tm n g = 0` if `n = 0` on `S`
  (`tm_eq_fourierInv_of_integrable`: `T_n g = 𝓕⁻(n 𝓕 g)`); `∫ g conj h = 0` for disjoint supports.
* **FS-1 (triple-kernel identity)** `integral_mul_mul_eq_zero_of_zero_sum` (Parseval for three Schwartz functions with
  `α + β + γ ≠ 0` on the product of the supports; generalizes V14's `integral_mul_mul_conj_eq_zero`, reusing its
  `integrable_*`, `fourierInv_schwartz_apply`), `integral_kernel3_eq_zero`, and its Fubini consequence
  `tm_mul_eq_zero`: `T_s[(T_a f)(T_b g)] = 0` for bounded measurable `f, g` and smooth compactly supported symbols
  `s, a, b` with `s γ ≠ 0 → a α ≠ 0 → b β ≠ 0 → γ ≠ α + β`.
* **FS-2 (Bernstein)**: the multiplier `bernN c L` (`= 1` on `|ξ - c| ≤ 1/(2L)`, `0` for `|ξ - c| > 1/L`), the reproducing
  formula `IsBandLimited.bernstein_reproduce`, the kernel decay `exists_norm_fourierInv_bernN_le`
  (`‖𝓕⁻ n (w)‖ ≤ C L⁻¹ (1 + |w|/L)^{-k}`), and the vector pointwise bound `yNorm_le_integral_bernstein`
  (`‖G x‖_{L^s(Y)} ≤ ∫ |K(x - z)| ‖G z‖_{L^s(Y)} dz`).  The last step of the weighted `L^p → L^∞` inequality
  (Hölder against `R ⟨R(x - ·)⟩^{100 - k}`, `A_w ⟨R|x - z|⟩^{100}` weights) is NOT included.
* **FS-3** (Young for kernel operators in `L^p(L^s(Y))`) is not included: no consumer in the route (the single-scale
  bounds (S), L3 use D-2 domination and single-tile energies; `p = ∞` uses FS-2), and Mathlib has no Young's inequality.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate Real ContDiff
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-! ## The multiplier on the Fourier side -/

/-- `T_m f = 𝓕⁻(m · 𝓕 f)` for `f ∈ L¹` and `m` continuous with compact support. -/
theorem tm_eq_fourierInv_of_integrable {m f : ℝ → ℂ} (hm : Continuous m) {c r : ℝ}
    (hsupp : ∀ ξ, r < |ξ - c| → m ξ = 0) (hf : Integrable f) (x : ℝ) :
    tm m f x = 𝓕⁻ (fun η => m η * 𝓕 f η) x := by
  have hρ : Integrable (fun ξ => m (-ξ)) := (integrable_of_far hm hsupp).comp_neg
  have key := integral_fourier_mul_fourier_neg (ρ := fun ξ => m (-ξ)) hρ hf x
  have hFρ : 𝓕 (fun ξ => m (-ξ)) = 𝓕⁻ m := (Real.fourierInv_eq_fourier_comp_neg m).symm
  rw [hFρ] at key
  have hL : ∫ ξ, Complex.exp (↑(-2 * Real.pi * ξ * x) * Complex.I) * (m (-ξ) * 𝓕 f (-ξ)) =
      𝓕⁻ (fun η => m η * 𝓕 f η) x := by
    rw [Real.fourierInv_eq']
    rw [← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [smul_eq_mul, neg_neg]
    congr 2
    simp only [inner, RCLike.re_to_real, star_trivial]
    push_cast
    ring
  rw [← hL, key]
  unfold tm
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  ring

/-- `T_m f = 0` if `m · 𝓕 f ≡ 0`. -/
theorem tm_eq_zero_of_fourier {m f : ℝ → ℂ} (hm : Continuous m) {c r : ℝ}
    (hs : ∀ ξ, r < |ξ - c| → m ξ = 0) (hf : Integrable f) (h : ∀ ξ, m ξ * 𝓕 f ξ = 0) (x : ℝ) :
    tm m f x = 0 := by
  rw [tm_eq_fourierInv_of_integrable hm hs hf]
  have : (fun η => m η * 𝓕 f η) = fun _ => (0 : ℂ) := funext h
  rw [this]
  simp [Real.fourierInv_eq]

/-! ## Band-limited functions -/

/-- `g` is a band-limited function with Fourier support in the bounded set `S`: continuous, integrable, and `𝓕 g`
vanishes off `S`. -/
structure IsBandLimited (g : ℝ → ℂ) (S : Set ℝ) : Prop where
  continuous : Continuous g
  integrable : Integrable g
  bounded : Bornology.IsBounded S
  fourier_eq_zero : ∀ ξ, ξ ∉ S → 𝓕 g ξ = 0

namespace IsBandLimited

variable {g h : ℝ → ℂ} {S T : Set ℝ}

theorem mono (hg : IsBandLimited g S) (hST : S ⊆ T) (hT : Bornology.IsBounded T) : IsBandLimited g T :=
  ⟨hg.continuous, hg.integrable, hT, fun ξ hξ => hg.fourier_eq_zero ξ fun hS => hξ (hST hS)⟩

theorem fourier_integrable (hg : IsBandLimited g S) : Integrable (𝓕 g) :=
  integrable_of_continuous_of_eq_zero (continuous_fourier_of_integrable hg.integrable) hg.bounded
    hg.fourier_eq_zero

theorem add (hg : IsBandLimited g S) (hh : IsBandLimited h S) : IsBandLimited (fun x => g x + h x) S := by
  refine ⟨hg.continuous.add hh.continuous, hg.integrable.add hh.integrable, hg.bounded, fun ξ hξ => ?_⟩
  have := fourier_add' hg.integrable hh.integrable ξ
  rw [hg.fourier_eq_zero ξ hξ, hh.fourier_eq_zero ξ hξ, add_zero] at this
  exact this

theorem const_mul (hg : IsBandLimited g S) (c : ℂ) : IsBandLimited (fun x => c * g x) S := by
  refine ⟨continuous_const.mul hg.continuous, hg.integrable.const_mul c, hg.bounded, fun ξ hξ => ?_⟩
  rw [fourier_const_mul' c g ξ, hg.fourier_eq_zero ξ hξ, mul_zero]

theorem zero (hS : Bornology.IsBounded S) : IsBandLimited (fun _ => (0 : ℂ)) S :=
  ⟨continuous_const, integrable_zero _ _ _, hS, fun ξ _ => by
    rw [Real.fourier_real_eq_integral_exp_smul]; simp⟩

theorem sum {ι : Type*} (I : Finset ι) {g : ι → ℝ → ℂ} (hS : Bornology.IsBounded S)
    (hg : ∀ i ∈ I, IsBandLimited (g i) S) : IsBandLimited (fun x => ∑ i ∈ I, g i x) S := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsBandLimited.zero hS
  | insert i I hi ih =>
    have h1 := hg i (Finset.mem_insert_self _ _)
    have h2 := ih fun j hj => hg j (Finset.mem_insert_of_mem hj)
    simpa [Finset.sum_insert hi] using h1.add h2

/-- **FS-1 (multiplier action)**: a multiplier equal to `1` on the Fourier support is the identity. -/
theorem tm_eq_self (hg : IsBandLimited g S) {n : ℝ → ℂ} (hn : Continuous n) {c r : ℝ}
    (hs : ∀ ξ, r < |ξ - c| → n ξ = 0) (h1 : ∀ ξ ∈ S, n ξ = 1) : tm n g = g := by
  funext x
  rw [tm_eq_fourierInv_of_integrable hn hs hg.integrable]
  have : (fun η => n η * 𝓕 g η) = 𝓕 g := by
    funext η
    by_cases hη : η ∈ S
    · rw [h1 η hη, one_mul]
    · rw [hg.fourier_eq_zero η hη, mul_zero]
  rw [this]
  exact congrFun (Continuous.fourierInv_fourier_eq hg.continuous hg.integrable hg.fourier_integrable) x

/-- **FS-1 (multiplier action)**: a multiplier vanishing on the Fourier support kills the function. -/
theorem tm_eq_zero (hg : IsBandLimited g S) {n : ℝ → ℂ} (hn : Continuous n) {c r : ℝ}
    (hs : ∀ ξ, r < |ξ - c| → n ξ = 0) (h0 : ∀ ξ ∈ S, n ξ = 0) (x : ℝ) : tm n g x = 0 := by
  refine tm_eq_zero_of_fourier hn hs hg.integrable (fun ξ => ?_) x
  by_cases hξ : ξ ∈ S
  · rw [h0 ξ hξ, zero_mul]
  · rw [hg.fourier_eq_zero ξ hξ, mul_zero]

/-- `⟨g, h⟩ = ∫ g conj h = 0` for band-limited functions with disjoint Fourier supports. -/
theorem integral_mul_conj_eq_zero (hg : IsBandLimited g S) (hh : IsBandLimited h T) (hST : Disjoint S T) :
    ∫ x, g x * (starRingEnd ℂ) (h x) = 0 := by
  have := pairing_eq_zero_of_ae hg.integrable hh.continuous hh.integrable hh.fourier_integrable
    (ae_of_all _ fun ξ => ?_)
  · exact this
  · by_cases hξ : ξ ∈ S
    · have : ξ ∉ T := Set.disjoint_left.1 hST hξ
      rw [hh.fourier_eq_zero ξ this, mul_zero]
    · rw [hg.fourier_eq_zero ξ hξ, map_zero, zero_mul]

theorem sum_biUnion {ι : Type*} (I : Finset ι) {g : ι → ℝ → ℂ} {S : ι → Set ℝ}
    (hg : ∀ i ∈ I, IsBandLimited (g i) (S i)) :
    IsBandLimited (fun x => ∑ i ∈ I, g i x) (⋃ i ∈ I, S i) := by
  have hb : Bornology.IsBounded (⋃ i ∈ I, S i) :=
    (Bornology.isBounded_biUnion_finset I).2 fun i hi => (hg i hi).bounded
  exact IsBandLimited.sum I hb fun i hi => (hg i hi).mono (Set.subset_biUnion_of_mem hi) hb

/-- A band-limited function is bounded (`g = 𝓕⁻ (𝓕 g)`, `𝓕 g ∈ L¹`). -/
theorem exists_norm_le (hg : IsBandLimited g S) : ∃ M : ℝ, ∀ x, ‖g x‖ ≤ M := by
  refine ⟨∫ ξ, ‖𝓕 g ξ‖, fun x => ?_⟩
  have h := congrFun (Continuous.fourierInv_fourier_eq hg.continuous hg.integrable hg.fourier_integrable) x
  rw [← h, Real.fourierInv_eq_fourier_neg]
  exact Real.norm_fourier_le_integral_norm _ _

theorem integrable_mul_conj (hg : IsBandLimited g S) (hh : IsBandLimited h T) :
    Integrable (fun x => g x * (starRingEnd ℂ) (h x)) := by
  obtain ⟨M, hM⟩ := hh.exists_norm_le
  have := hg.integrable.bdd_mul (c := M) ((Complex.continuous_conj.comp hh.continuous).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => by
      show ‖(starRingEnd ℂ) (h x)‖ ≤ M
      rw [Complex.norm_conj]; exact hM x)
  exact this.congr (Filter.Eventually.of_forall fun x => mul_comm _ _)

theorem integrable_norm_sq (hg : IsBandLimited g S) : Integrable (fun x => ‖g x‖ ^ 2) := by
  obtain ⟨M, hM⟩ := hg.exists_norm_le
  refine (hg.integrable.norm.const_mul M).mono' (hg.continuous.norm.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have := hM x
  have h0 := norm_nonneg (g x)
  nlinarith

/-- **Orthogonality (L4)**: `∫ ‖Σ g_i‖² = Σ ∫ ‖g_i‖²` for band-limited `g_i` with pairwise disjoint Fourier supports. -/
theorem integral_norm_sq_sum {ι : Type*} (I : Finset ι) {g : ι → ℝ → ℂ} {S : ι → Set ℝ}
    (hg : ∀ i ∈ I, IsBandLimited (g i) (S i)) (hS : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j)) :
    ∫ x, ‖∑ i ∈ I, g i x‖ ^ 2 = ∑ i ∈ I, ∫ x, ‖g i x‖ ^ 2 := by
  classical
  have hsq : ∀ z : ℂ, (((‖z‖ ^ 2 : ℝ)) : ℂ) = z * (starRingEnd ℂ) z := fun z => by
    rw [Complex.mul_conj']; push_cast; ring
  have hint : ∀ i ∈ I, ∀ j ∈ I, Integrable (fun x => g i x * (starRingEnd ℂ) (g j x)) := fun i hi j hj =>
    (hg i hi).integrable_mul_conj (hg j hj)
  apply Complex.ofReal_injective
  have e1 : (((∫ x, ‖∑ i ∈ I, g i x‖ ^ 2 : ℝ)) : ℂ) =
      ∫ x, (∑ i ∈ I, g i x) * (starRingEnd ℂ) (∑ j ∈ I, g j x) := by
    rw [← integral_complex_ofReal (μ := volume) (f := fun x => ‖∑ i ∈ I, g i x‖ ^ 2)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact hsq _
  rw [e1, Complex.ofReal_sum]
  have e2 : ∀ x, (∑ i ∈ I, g i x) * (starRingEnd ℂ) (∑ j ∈ I, g j x) =
      ∑ i ∈ I, ∑ j ∈ I, g i x * (starRingEnd ℂ) (g j x) := fun x => by
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  simp_rw [e2]
  rw [integral_finsetSum _ (fun i hi => integrable_finsetSum _ fun j hj => hint i hi j hj)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_finsetSum _ (fun j hj => hint i hi j hj), Finset.sum_eq_single i]
  · rw [← integral_complex_ofReal (μ := volume) (f := fun x => ‖g i x‖ ^ 2)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact (hsq _).symm
  · intro j hj hne
    exact (hg i hi).integral_mul_conj_eq_zero (hg j hj) (hS i hi j hj hne.symm)
  · intro h; exact absurd hi h

end IsBandLimited

section Pieces

variable {𝔭 : Params} {s v : ℤ} {c : ℝ} {ψ m : ℝ → ℂ}

/-- The tile pieces `g = ψ · (𝓕⁻m * f)` are band-limited, with Fourier support in
`[c - (β/2 + δ) 2^{-s}, c + (β/2 + δ) 2^{-s}]` (V10's `fourier_gfun_eq_zero`). -/
theorem isBandLimited_gfun (hN : 2 ≤ 𝔭.N) (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ)
    (hm : InMult 𝔭 s c m) {f : ℝ → ℂ} (hf : Measurable f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) :
    IsBandLimited (gfun ψ m f)
      (Icc (c - (𝔭.β / 2 + 𝔭.δ) * (2 : ℝ) ^ (-s)) (c + (𝔭.β / 2 + 𝔭.δ) * (2 : ℝ) ^ (-s))) := by
  refine ⟨continuous_gfun hD hβ hψ hm hf hB, integrable_gfun hN hD hβ hψ hm hf hB,
    Metric.isBounded_Icc _ _, fun ξ hξ => ?_⟩
  refine fourier_gfun_eq_zero hN hD hβ hψ hm hf hB ξ ?_
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hξ
  rw [lt_abs]
  rcases hξ with h | h
  · right; linarith
  · left; linarith

end Pieces


/-! ## FS-1: the triple-kernel identity -/

/-! ### Schwartz kernels of smooth compactly supported symbols -/

section Kernels

variable {a : ℝ → ℂ}

/-- The Schwartz kernel `𝓕⁻ a` of a smooth compactly supported symbol `a`. -/
def kerS (a : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) : 𝓢(ℝ, ℂ) :=
  𝓕⁻ (hc.toSchwartzMap ha)

theorem kerS_apply (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) : ⇑(kerS a ha hc) = 𝓕⁻ a := by
  unfold kerS
  rw [SchwartzMap.fourierInv_coe]
  rfl

theorem fourier_kerS (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) (w : ℝ) :
    𝓕 (⇑(kerS a ha hc)) w = a w := by
  rw [← SchwartzMap.fourier_coe]
  unfold kerS
  rw [FourierTransform.fourier_fourierInv_eq]
  rfl

end Kernels

section KernelIdentity

variable {s a b : ℝ → ℂ}

end KernelIdentity

/-! ## FS-2: Bernstein (reproducing formula and kernel decay for band-limited functions) -/

section Bernstein

theorem fourierInv_eq_integral_exp (f : ℝ → ℂ) (w : ℝ) :
    𝓕⁻ f w = ∫ v, Complex.exp (↑(2 * π * v * w) * Complex.I) * f v := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]
  congr 3; ring_nf

/-- The Bernstein multiplier `n(ξ) = χ(L (ξ - c))`, `χ = bumpG0` (`= 1` on `[-1/2, 1/2]`, `= 0` off `[-1, 1]`):
`n = 1` on `|ξ - c| ≤ 1/(2L)`, `n = 0` for `|ξ - c| ≥ 1/L`. -/
def bernN (c L : ℝ) (ξ : ℝ) : ℂ := ((bumpG0 (L * (ξ - c)) : ℝ) : ℂ)

theorem contDiff_bernN (c L : ℝ) : ContDiff ℝ ∞ (bernN c L) :=
  Complex.ofRealCLM.contDiff.comp (bumpG0.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const)))

theorem bernN_eq_one {c L ξ : ℝ} (hL : 0 < L) (h : |ξ - c| ≤ 1 / (2 * L)) : bernN c L ξ = 1 := by
  unfold bernN
  rw [bumpG0_eq_one, Complex.ofReal_one]
  rw [abs_mul, abs_of_pos hL]
  calc L * |ξ - c| ≤ L * (1 / (2 * L)) := by gcongr
    _ = 1 / 2 := by field_simp

theorem bernN_eq_zero {c L ξ : ℝ} (hL : 0 < L) (h : 1 / L < |ξ - c|) : bernN c L ξ = 0 := by
  unfold bernN
  have : bumpG0 (L * (ξ - c)) = 0 := by
    refine bumpG0.zero_of_le_dist ?_
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos hL]
    show (1 : ℝ) ≤ L * |ξ - c|
    rw [div_lt_iff₀ hL] at h
    linarith
  rw [this, Complex.ofReal_zero]

/-- **Reproducing formula (FS-2)**: a band-limited `g` with `𝓕 g` supported in `[c - 1/(2L), c + 1/(2L)]`
reproduces: `g(x) = ∫ K(x - z) g(z) dz`, `K = 𝓕⁻ (bernN c L)`. -/
theorem IsBandLimited.bernstein_reproduce {g : ℝ → ℂ} {S : Set ℝ} (hg : IsBandLimited g S) {c L : ℝ} (hL : 0 < L)
    (hS : S ⊆ Icc (c - 1 / (2 * L)) (c + 1 / (2 * L))) (x : ℝ) :
    g x = ∫ z, 𝓕⁻ (bernN c L) (x - z) * g z := by
  have hn : Continuous (bernN c L) := (contDiff_bernN c L).continuous
  have h := congrFun (hg.tm_eq_self hn (c := c) (r := 1 / L) (fun ξ hξ => bernN_eq_zero hL hξ)
    (fun ξ hξ => bernN_eq_one hL (by
      have := hS hξ
      rw [abs_le]
      constructor <;> linarith [this.1, this.2]))) x
  exact h.symm

/-- The kernel of the Bernstein multiplier: `𝓕⁻ n (w) = e^{2πicw} L⁻¹ 𝓕⁻ χ (w/L)`. -/
theorem fourierInv_bernN (c L w : ℝ) (hL : 0 < L) :
    𝓕⁻ (bernN c L) w = Complex.exp (↑(2 * π * c * w) * Complex.I) * (((L⁻¹ : ℝ)) : ℂ) *
      𝓕⁻ (fun η : ℝ => ((bumpG0 η : ℝ) : ℂ)) (w / L) := by
  rw [fourierInv_eq_integral_exp, fourierInv_eq_integral_exp]
  set H : ℝ → ℂ := fun u => Complex.exp (↑(2 * π * (u / L + c) * w) * Complex.I) * ((bumpG0 u : ℝ) : ℂ) with hH
  have h1 : ∫ v : ℝ, Complex.exp (↑(2 * π * v * w) * Complex.I) * bernN c L v = ∫ v : ℝ, H (L * (v - c)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [hH, bernN]
    have : L * (v - c) / L + c = v := by field_simp; ring
    rw [this]
  rw [h1, integral_sub_right_eq_self (fun v => H (L * v)) c, Measure.integral_comp_mul_left H L,
    abs_of_pos (inv_pos.2 hL)]
  have h2 : ∀ u : ℝ, H u = Complex.exp (↑(2 * π * c * w) * Complex.I) *
      (Complex.exp (↑(2 * π * u * (w / L)) * Complex.I) * ((bumpG0 u : ℝ) : ℂ)) := by
    intro u
    simp only [hH]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  simp_rw [h2]
  rw [integral_const_mul, Complex.real_smul]
  ring

/-- Decay of the Bernstein kernel: `‖𝓕⁻ n (w)‖ ≤ C L⁻¹ (1 + |w|/L)^{-k}`, `C = C(k)` independent of `c, L`. -/
theorem exists_norm_fourierInv_bernN_le (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c L : ℝ, 0 < L → ∀ w : ℝ,
      ‖𝓕⁻ (bernN c L) w‖ ≤ C * L⁻¹ * (1 + |w| / L) ^ (-(k : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_kernelG0_le 0 k
  refine ⟨C, hC0, fun c L hL w => ?_⟩
  rw [fourierInv_bernN c L w hL, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (inv_pos.2 hL).le]
  have hk : 𝓕⁻ (fun η : ℝ => ((bumpG0 η : ℝ) : ℂ)) (w / L) = kernelG0 0 (-(w / L)) := by
    rw [Real.fourierInv_eq_fourier_neg]
    have e : (fun η : ℝ => ((bumpG0 η : ℝ) : ℂ)) = kappaG0 0 := by
      funext η; simp [kappaG0]
    rw [e]
    rfl
  rw [hk]
  have := hC (-(w / L))
  rw [abs_neg, abs_div, abs_of_pos hL] at this
  calc L⁻¹ * ‖kernelG0 0 (-(w / L))‖ ≤ L⁻¹ * (C * (1 + |w| / L) ^ (-(k : ℝ))) :=
        mul_le_mul_of_nonneg_left this (inv_pos.2 hL).le
    _ = _ := by ring

/-- **FS-2 (vector, pointwise kernel bound)**: if the coordinates `z ↦ G z y` of `G : ℝ → ZMod P → ℂ` are
band-limited with `𝓕 ⊆ [c - 1/(2L), c + 1/(2L)]`, then
`‖G(x)‖_{L^s(Y)} ≤ ∫ |K(x - z)| ‖G(z)‖_{L^s(Y)} dz`, `K = 𝓕⁻ (bernN c L)`
(the weighted `L^p → L^∞` Bernstein inequality follows by Hölder from the kernel decay
`exists_norm_fourierInv_bernN_le`). -/
theorem yNorm_le_integral_bernstein {P : ℕ} [NeZero P] {s : ℝ} (hs : 1 ≤ s) {G : ℝ → ZMod P → ℂ} {S : Set ℝ}
    (hG : ∀ y, IsBandLimited (fun x => G x y) S) {c L : ℝ} (hL : 0 < L)
    (hS : S ⊆ Icc (c - 1 / (2 * L)) (c + 1 / (2 * L))) (x : ℝ) :
    yNorm s (G x) ≤ ∫ z, ‖𝓕⁻ (bernN c L) (x - z)‖ * yNorm s (G z) := by
  have hKc : Continuous (𝓕⁻ (bernN c L)) :=
    continuous_fourierInv_of_integrable' (integrable_of_far (contDiff_bernN c L).continuous
      (fun ξ hξ => bernN_eq_zero hL (c := c) (ξ := ξ) (by simpa using hξ)) (c := c) (r := 1 / L))
  have hrep : G x = fun y => ∫ z, 𝓕⁻ (bernN c L) (x - z) * G z y := by
    funext y
    exact (hG y).bernstein_reproduce hL hS x
  have hV : ∀ y, Integrable (fun z => 𝓕⁻ (bernN c L) (x - z) * G z y) volume := by
    intro y
    obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ w, ‖𝓕⁻ (bernN c L) w‖ ≤ M :=
      ⟨∫ ξ, ‖bernN c L ξ‖, fun w => by
        rw [Real.fourierInv_eq_fourier_neg]; exact Real.norm_fourier_le_integral_norm _ _⟩
    exact (hG y).integrable.bdd_mul (c := M)
      ((hKc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => hM _)
  have hs0 : 0 < s := by linarith
  rw [hrep]
  refine (yNorm_integral_le_of_one_le hs (fun z y => 𝓕⁻ (bernN c L) (x - z) * G z y) hV).trans ?_
  refine le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_))
  exact yNorm_fun_const_mul hs0 _ _

end Bernstein

end PrimeBHT.TimeFrequency.X2
