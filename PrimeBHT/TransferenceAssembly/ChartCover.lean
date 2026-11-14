module

public import PrimeBHT.TransferenceAssembly.Chart
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# N41 / N42 / N43(a): the finite family of Fourier charts of the circle

A `ChartCover` is a finite family of smooth compactly supported charts `χ_ι : ℝ → ℂ`
(`ι = 1, …, n_ch`), each supported in an interval `[a_ι, b_ι]` of length `< 1/1000`, whose
periodisations form a partition of unity of the circle: `∑_ι ∑_j χ_ι(θ - j) = 1`.

* `exists_chartCover`: such a family exists (normalised shifted `ContDiffBump`s).
* `exists_alias_d`, `exists_alias_v`: the two alias-uniqueness facts of blueprint N42 steps 4-5
  (pure interval-length arguments), in the exact shape of the hypotheses `_hd`, `_hv` of
  `exists_norm_tsum_tsum_chartProj_le_of_x2`.
* `sum_chartProj`: `∑_ι P_{ι,N} h = h` (blueprint N41(a), second half), via Fourier inversion on the
  circle (`integral_seqFourier_mul_e`).
-/

@[expose] public noncomputable section

namespace PrimeBHT.TransferenceAssembly

open MeasureTheory PrimeCarleson
open scoped ContDiff Real

/-! ### Periodisation of a function with bounded support -/

section Periodise

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
/-- Terms of `∑_j φ(t - j)` outside `[-T, T]` vanish when `φ` is supported in `[-R, R]` and
`|t| + R < T`. -/
theorem eq_zero_of_notMem_Icc {φ : ℝ → F} {R : ℝ} (hφ : ∀ s, φ s ≠ 0 → |s| ≤ R) {t : ℝ} {T : ℕ}
    (hT : |t| + R < T) {j : ℤ} (hj : j ∉ Finset.Icc (-(T : ℤ)) T) : φ (t - j) = 0 := by
  by_contra hne
  have h1 := hφ _ hne
  have h2 : |(j : ℝ)| ≤ |t| + R := by
    calc |(j : ℝ)| = |t - (t - j)| := by rw [sub_sub_cancel]
      _ ≤ |t| + |t - j| := abs_sub _ _
      _ ≤ |t| + R := by linarith
  apply hj
  have h3 : |(j : ℝ)| < T := lt_of_le_of_lt h2 hT
  obtain ⟨h4, h5⟩ := abs_lt.1 h3
  rw [Finset.mem_Icc]
  exact ⟨by exact_mod_cast h4.le, by exact_mod_cast h5.le⟩

omit [NormedSpace ℝ F] in
theorem tsum_sub_intCast_eq_sum {φ : ℝ → F} {R : ℝ} (hφ : ∀ s, φ s ≠ 0 → |s| ≤ R) {t : ℝ}
    {T : ℕ} (hT : |t| + R < T) :
    ∑' j : ℤ, φ (t - j) = ∑ j ∈ Finset.Icc (-(T : ℤ)) T, φ (t - j) :=
  tsum_eq_sum fun _ hj => eq_zero_of_notMem_Icc hφ hT hj

omit [NormedSpace ℝ F] in
theorem summable_sub_intCast {φ : ℝ → F} {R : ℝ} (hφ : ∀ s, φ s ≠ 0 → |s| ≤ R) (t : ℝ) :
    Summable fun j : ℤ => φ (t - j) := by
  obtain ⟨T, hT⟩ := exists_nat_gt (|t| + R)
  exact summable_of_ne_finset_zero fun _ hj => eq_zero_of_notMem_Icc hφ hT hj

/-- The periodisation `t ↦ ∑_j φ(t - j)` of a smooth function with bounded support is smooth. -/
theorem contDiff_tsum_sub_intCast {φ : ℝ → F} (hφ : ContDiff ℝ ∞ φ) {R : ℝ}
    (hR : ∀ s, φ s ≠ 0 → |s| ≤ R) : ContDiff ℝ ∞ (fun t : ℝ => ∑' j : ℤ, φ (t - j)) := by
  rw [contDiff_iff_contDiffAt]
  intro t₀
  obtain ⟨T, hT⟩ := exists_nat_gt (|t₀| + 1 + R)
  have hev : (fun t : ℝ => ∑' j : ℤ, φ (t - j)) =ᶠ[nhds t₀]
      fun t => ∑ j ∈ Finset.Icc (-(T : ℤ)) T, φ (t - j) := by
    have hmem : Set.Ioo (t₀ - 1) (t₀ + 1) ∈ nhds t₀ := Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hmem] with t ht
    refine tsum_sub_intCast_eq_sum hR ?_
    have h1 : |t - t₀| < 1 := abs_lt.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h2 := abs_sub_abs_le_abs_sub t t₀
    linarith
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact (ContDiff.sum fun j _ => hφ.comp (by fun_prop)).contDiffAt

omit [NormedSpace ℝ F] in
/-- `1`-periodicity of the periodisation. -/
theorem tsum_sub_intCast_add_intCast (φ : ℝ → F) (t : ℝ) (m : ℤ) :
    ∑' j : ℤ, φ (t + m - j) = ∑' j : ℤ, φ (t - j) := by
  refine Eq.trans (tsum_congr fun j => ?_) ((Equiv.subRight m).tsum_eq (fun j : ℤ => φ (t - j)))
  simp only [Equiv.subRight_apply]
  congr 1
  push_cast
  ring

end Periodise

theorem contDiff_chartSymbol {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (N : ℕ) : ContDiff ℝ ∞ (chartSymbol χ N) := by
  obtain ⟨R, hR⟩ := exists_bound_of_hasCompactSupport hχc
  exact (contDiff_tsum_sub_intCast hχ hR).comp (contDiff_const.mul contDiff_id)

/-! ### The structure -/

/-- A finite family of Fourier charts of the circle (blueprint N41): smooth compactly supported
`χ_ι`, supported in `[a_ι, b_ι]` with `b_ι - a_ι < 1/1000`, with periodised partition of unity
`∑_ι ∑_j χ_ι(θ - j) = 1`. -/
structure ChartCover where
  /-- the number of charts -/
  n : ℕ
  hn : 0 < n
  /-- the charts -/
  χ : Fin n → ℝ → ℂ
  a : Fin n → ℝ
  b : Fin n → ℝ
  contDiff : ∀ ι, ContDiff ℝ ∞ (χ ι)
  hasCompactSupport : ∀ ι, HasCompactSupport (χ ι)
  mem_Icc_of_ne_zero : ∀ ι t, χ ι t ≠ 0 → t ∈ Set.Icc (a ι) (b ι)
  length_lt : ∀ ι, b ι - a ι < 1 / 1000
  sum_tsum_eq_one : ∀ θ : ℝ, ∑ ι, ∑' j : ℤ, χ ι (θ - j) = 1

/-! ### Alias uniqueness (N42 steps 4-5) -/

/-- **One kernel alias** (N42 step 4): at most one integer `d` can satisfy
`|s₁ - s₂ - d| ≤ 1/1000` for `s_i ∈ [a_{ι_i}, b_{ι_i}]`. -/
theorem exists_alias_d (c : ChartCover) (ι₁ ι₂ : Fin c.n) :
    ∃ d : ℤ, ∀ d' : ℤ, ∀ s₁ ∈ Set.Icc (c.a ι₁) (c.b ι₁), ∀ s₂ ∈ Set.Icc (c.a ι₂) (c.b ι₂),
      |s₁ - s₂ - d'| ≤ 1 / 1000 → d' = d := by
  by_cases hex : ∃ d' : ℤ, ∃ s₁ ∈ Set.Icc (c.a ι₁) (c.b ι₁), ∃ s₂ ∈ Set.Icc (c.a ι₂) (c.b ι₂),
      |s₁ - s₂ - d'| ≤ 1 / 1000
  · obtain ⟨d₀, t₁, ht₁, t₂, ht₂, hd₀⟩ := hex
    refine ⟨d₀, fun d' s₁ hs₁ s₂ hs₂ hd' => ?_⟩
    have h1 := c.length_lt ι₁
    have h2 := c.length_lt ι₂
    rw [abs_le] at hd' hd₀
    have hlt : |((d' - d₀ : ℤ) : ℝ)| < 1 := by
      rw [abs_lt]
      push_cast
      obtain ⟨hs₁a, hs₁b⟩ := hs₁
      obtain ⟨hs₂a, hs₂b⟩ := hs₂
      obtain ⟨ht₁a, ht₁b⟩ := ht₁
      obtain ⟨ht₂a, ht₂b⟩ := ht₂
      constructor <;> linarith [hd'.1, hd'.2, hd₀.1, hd₀.2]
    have hz : |d' - d₀| < 1 := by exact_mod_cast hlt
    have := Int.abs_lt_one_iff.1 hz
    omega
  · exact ⟨0, fun d' s₁ hs₁ s₂ hs₂ hd' => absurd ⟨d', s₁, hs₁, s₂, hs₂, hd'⟩ hex⟩

/-- **One output alias** (N42 step 5): at most one integer `v` can equal `s₁ + s₂ - s₃` for
`s_i ∈ [a_{ι_i}, b_{ι_i}]`. -/
theorem exists_alias_v (c : ChartCover) (ι₁ ι₂ ι₃ : Fin c.n) :
    ∃ v : ℤ, ∀ v' : ℤ, ∀ s₁ ∈ Set.Icc (c.a ι₁) (c.b ι₁), ∀ s₂ ∈ Set.Icc (c.a ι₂) (c.b ι₂),
      ∀ s₃ ∈ Set.Icc (c.a ι₃) (c.b ι₃), (v' : ℝ) = s₁ + s₂ - s₃ → v' = v := by
  by_cases hex : ∃ v' : ℤ, ∃ s₁ ∈ Set.Icc (c.a ι₁) (c.b ι₁), ∃ s₂ ∈ Set.Icc (c.a ι₂) (c.b ι₂),
      ∃ s₃ ∈ Set.Icc (c.a ι₃) (c.b ι₃), (v' : ℝ) = s₁ + s₂ - s₃
  · obtain ⟨v₀, t₁, ht₁, t₂, ht₂, t₃, ht₃, hv₀⟩ := hex
    refine ⟨v₀, fun v' s₁ hs₁ s₂ hs₂ s₃ hs₃ hv' => ?_⟩
    have h1 := c.length_lt ι₁
    have h2 := c.length_lt ι₂
    have h3 := c.length_lt ι₃
    have hlt : |((v' - v₀ : ℤ) : ℝ)| < 1 := by
      rw [abs_lt]
      push_cast
      obtain ⟨hs₁a, hs₁b⟩ := hs₁
      obtain ⟨hs₂a, hs₂b⟩ := hs₂
      obtain ⟨hs₃a, hs₃b⟩ := hs₃
      obtain ⟨ht₁a, ht₁b⟩ := ht₁
      obtain ⟨ht₂a, ht₂b⟩ := ht₂
      obtain ⟨ht₃a, ht₃b⟩ := ht₃
      constructor <;> linarith
    have hz : |v' - v₀| < 1 := by exact_mod_cast hlt
    have := Int.abs_lt_one_iff.1 hz
    omega
  · exact ⟨0, fun v' s₁ hs₁ s₂ hs₂ s₃ hs₃ hv' => absurd ⟨v', s₁, hs₁, s₂, hs₂, s₃, hs₃, hv'⟩ hex⟩

/-! ### Fourier inversion on the circle -/

theorem integral_e_intCast_mul (m : ℤ) :
    ∫ β in (0 : ℝ)..1, e (m * β) = if m = 0 then 1 else 0 := by
  split_ifs with hm
  · subst hm
    simp [e]
  · have hc : (2 * (π : ℂ) * Complex.I * (m : ℂ)) ≠ 0 := by
      simp [Complex.I_ne_zero, hm, Real.pi_ne_zero]
    have hpt : ∀ β : ℝ, e (m * β) = Complex.exp ((2 * π * Complex.I * m) * (β : ℂ)) := fun β => by
      unfold e
      push_cast
      ring_nf
    have h1 : Complex.exp ((2 * π * Complex.I * m) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [← hpt 1, mul_one]
      exact e_intCast m
    rw [intervalIntegral.integral_congr (g := fun β : ℝ => Complex.exp ((2 * π * Complex.I * m) *
      (β : ℂ))) fun β _ => hpt β, integral_exp_mul_complex hc, h1]
    simp

/-- Fourier inversion on the circle: `∫₀¹ ĥ(β) e(nβ) dβ = h(n)`. -/
theorem integral_seqFourier_mul_e (h : ℤ →₀ ℂ) (n : ℤ) :
    ∫ β in (0 : ℝ)..1, seqFourier h β * e (n * β) = h n := by
  have hterm : ∀ β : ℝ, seqFourier h β * e (n * β) =
      ∑ k ∈ h.support, h k * e (((n - k : ℤ) : ℝ) * β) := by
    intro β
    unfold seqFourier
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, ← e_add]
    congr 2
    push_cast
    ring
  rw [intervalIntegral.integral_congr (g := fun β : ℝ =>
    ∑ k ∈ h.support, h k * e (((n - k : ℤ) : ℝ) * β)) fun β _ => hterm β,
    intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, integral_e_intCast_mul]
    simp only [mul_ite, mul_one, mul_zero, sub_eq_zero]
    rw [Finset.sum_ite_eq]
    by_cases hn : n ∈ h.support
    · simp only [hn, ite_true]
    · simp only [hn, ite_false]
      exact (Finsupp.notMem_support_iff.1 hn).symm
  · intro k _
    exact (continuous_const.mul (contDiff_e.continuous.comp (by fun_prop))).intervalIntegrable _ _

/-! ### The partition identity at the sequence level -/

theorem sum_chartSymbol (c : ChartCover) (N : ℕ) (β : ℝ) :
    ∑ ι, chartSymbol (c.χ ι) N β = 1 :=
  c.sum_tsum_eq_one _

/-- **N41(a), second half.** `∑_ι P_{ι,N} h = h`. -/
theorem sum_chartProj (c : ChartCover) (N : ℕ) (h : ℤ →₀ ℂ) (n : ℤ) :
    ∑ ι, chartProj (c.χ ι) N h n = h n := by
  have hcont : Continuous fun β : ℝ => seqFourier h β * e (n * β) :=
    (contDiff_seqFourier h).continuous.mul (contDiff_e.continuous.comp (by fun_prop))
  unfold chartProj
  rw [← intervalIntegral.integral_finsetSum]
  · rw [← integral_seqFourier_mul_e h n]
    refine intervalIntegral.integral_congr fun β _ => ?_
    rw [← Finset.sum_mul, ← Finset.sum_mul, sum_chartSymbol, one_mul]
  · intro ι _
    exact (((contDiff_chartSymbol (c.contDiff ι) (c.hasCompactSupport ι) N).continuous.mul
      (contDiff_seqFourier h).continuous).mul
      (contDiff_e.continuous.comp (by fun_prop))).intervalIntegrable _ _

/-! ### Existence: normalised shifted bumps -/

/-- The centre `(ι + 1/2)/4000` of the `ι`-th bump. -/
def bumpCentre (ι : Fin 4000) : ℝ := (((ι : ℕ) : ℝ) + 1 / 2) / 4000

/-- The `ι`-th raw bump: `1` on the ball of radius `1/8000`, supported in the ball of radius
`1/4000` about `bumpCentre ι`. -/
def rawBump (ι : Fin 4000) : ContDiffBump (bumpCentre ι) where
  rIn := 1 / 8000
  rOut := 1 / 4000
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem bumpCentre_nonneg (ι : Fin 4000) : 0 ≤ bumpCentre ι := by
  unfold bumpCentre
  positivity

theorem bumpCentre_le_one (ι : Fin 4000) : bumpCentre ι ≤ 1 := by
  have hι : (ι : ℕ) ≤ 3999 := by have := ι.2; omega
  have : ((ι : ℕ) : ℝ) ≤ 3999 := by exact_mod_cast hι
  unfold bumpCentre
  rw [div_le_one (by norm_num)]
  linarith

theorem rawBump_ne_zero_mem (ι : Fin 4000) {s : ℝ} (hs : rawBump ι s ≠ 0) :
    s ∈ Set.Icc (bumpCentre ι - 1 / 4000) (bumpCentre ι + 1 / 4000) := by
  have h : s ∈ Function.support (rawBump ι) := hs
  rw [(rawBump ι).support_eq, Metric.mem_ball, Real.dist_eq, abs_lt] at h
  have h4 : (rawBump ι).rOut = 1 / 4000 := rfl
  rw [h4] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem abs_le_two_of_rawBump_ne_zero (ι : Fin 4000) (s : ℝ) (hs : rawBump ι s ≠ 0) :
    |s| ≤ 2 := by
  obtain ⟨h1, h2⟩ := rawBump_ne_zero_mem ι hs
  have := bumpCentre_nonneg ι
  have := bumpCentre_le_one ι
  rw [abs_le]
  constructor <;> linarith

/-- The periodised sum of the raw bumps. -/
def bumpSum (t : ℝ) : ℝ := ∑ ι : Fin 4000, ∑' j : ℤ, rawBump ι (t - j)

theorem contDiff_bumpSum : ContDiff ℝ ∞ bumpSum :=
  ContDiff.sum fun ι _ =>
    contDiff_tsum_sub_intCast (rawBump ι).contDiff (abs_le_two_of_rawBump_ne_zero ι)

theorem bumpSum_add_intCast (t : ℝ) (m : ℤ) : bumpSum (t + m) = bumpSum t := by
  unfold bumpSum
  exact Finset.sum_congr rfl fun ι _ => tsum_sub_intCast_add_intCast _ t m

theorem bumpSum_pos (t : ℝ) : 0 < bumpSum t := by
  have hs0 : 0 ≤ Int.fract t := Int.fract_nonneg t
  have hs1 : Int.fract t < 1 := Int.fract_lt_one t
  have hι : ⌊4000 * Int.fract t⌋₊ < 4000 := by
    rw [Nat.floor_lt (by positivity)]
    push_cast
    linarith
  have h1 : (⌊4000 * Int.fract t⌋₊ : ℝ) ≤ 4000 * Int.fract t := Nat.floor_le (by positivity)
  have h2 : 4000 * Int.fract t < ⌊4000 * Int.fract t⌋₊ + 1 := Nat.lt_floor_add_one _
  let ι : Fin 4000 := ⟨⌊4000 * Int.fract t⌋₊, hι⟩
  have hval : rawBump ι (t - (⌊t⌋ : ℤ)) = 1 := by
    apply (rawBump ι).one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    have h3 : t - (⌊t⌋ : ℝ) = Int.fract t := rfl
    have h4 : bumpCentre ι = (⌊4000 * Int.fract t⌋₊ + 1 / 2) / 4000 := rfl
    have h5 : (rawBump ι).rIn = 1 / 8000 := rfl
    rw [h5, h3, h4]
    constructor <;> linarith
  calc (0 : ℝ) < 1 := one_pos
    _ = rawBump ι (t - (⌊t⌋ : ℤ)) := hval.symm
    _ ≤ ∑' j : ℤ, rawBump ι (t - j) :=
        (summable_sub_intCast (abs_le_two_of_rawBump_ne_zero ι) t).le_tsum ⌊t⌋
          fun j _ => (rawBump ι).nonneg
    _ ≤ bumpSum t :=
        Finset.single_le_sum (f := fun ι : Fin 4000 => ∑' j : ℤ, rawBump ι (t - j))
          (fun ι _ => tsum_nonneg fun j => (rawBump ι).nonneg) (Finset.mem_univ ι)

/-- The normalised chart `χ_ι = ψ_ι / ∑_κ ∑_j ψ_κ(· - j)`. -/
def normBump (ι : Fin 4000) (t : ℝ) : ℂ := ((rawBump ι t / bumpSum t : ℝ) : ℂ)

theorem contDiff_normBump (ι : Fin 4000) : ContDiff ℝ ∞ (normBump ι) := by
  have h : ContDiff ℝ ∞ (fun t : ℝ => rawBump ι t / bumpSum t) :=
    (rawBump ι).contDiff.div contDiff_bumpSum fun t => (bumpSum_pos t).ne'
  exact Complex.ofRealCLM.contDiff.comp h

theorem hasCompactSupport_normBump (ι : Fin 4000) : HasCompactSupport (normBump ι) := by
  refine HasCompactSupport.intro (K := tsupport (rawBump ι)) (rawBump ι).hasCompactSupport
    fun x hx => ?_
  simp [normBump, image_eq_zero_of_notMem_tsupport hx]

theorem sum_tsum_normBump (θ : ℝ) : ∑ ι : Fin 4000, ∑' j : ℤ, normBump ι (θ - j) = 1 := by
  have hP : ∀ j : ℤ, bumpSum (θ - j) = bumpSum θ := fun j => by
    simpa [sub_eq_add_neg] using bumpSum_add_intCast θ (-j)
  have key : ∑ ι : Fin 4000, ∑' j : ℤ, rawBump ι (θ - j) / bumpSum (θ - j) = 1 := by
    simp_rw [hP, tsum_div_const]
    rw [← Finset.sum_div]
    exact div_self (bumpSum_pos θ).ne'
  have hcast : ∑ ι : Fin 4000, ∑' j : ℤ, normBump ι (θ - j) =
      ((∑ ι : Fin 4000, ∑' j : ℤ, rawBump ι (θ - j) / bumpSum (θ - j) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun ι _ => (Complex.ofReal_tsum _).symm
  rw [hcast, key]
  simp

/-- **Existence of the chart family** (N41, formalization notes): normalised shifted bumps. -/
theorem exists_chartCover : Nonempty ChartCover :=
  ⟨{ n := 4000
     hn := by norm_num
     χ := normBump
     a := fun ι => bumpCentre ι - 1 / 4000
     b := fun ι => bumpCentre ι + 1 / 4000
     contDiff := contDiff_normBump
     hasCompactSupport := hasCompactSupport_normBump
     mem_Icc_of_ne_zero := fun ι t ht => rawBump_ne_zero_mem ι fun h0 => ht (by simp [normBump, h0])
     length_lt := fun ι => by norm_num
     sum_tsum_eq_one := sum_tsum_normBump }⟩

end PrimeBHT.TransferenceAssembly
