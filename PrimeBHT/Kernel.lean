module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Dyadic kernels `ψ_k` and the smoothing error (blueprint nodes N01 and N25)

* `IsCutoff χ`: `χ` is smooth, even, with `tsupport χ ⊆ (-1, 1)` and `χ = 1` on `[-1/2, 1/2]`.
* `psi χ t = (χ t - χ (2 t)) / t` (with `psi χ 0 = 0` by the Lean convention `x / 0 = 0`),
  `psiK χ k t = 2⁻ᵏ ψ(t 2⁻ᵏ)`, `kernelI χ a b = ∑ k ∈ [a, b], ψ_k`.
* N01: oddness, support, telescoping identities.
* N25: pointwise smoothing bound and the `ℓ¹` consequence.
-/

@[expose] public section

open scoped ContDiff

namespace PrimeBHT.Kernel

/-- Abstract smooth cutoff: `χ ∈ C^∞`, even, `tsupport χ ⊆ (-1, 1)`, `χ = 1` on `[-1/2, 1/2]`.
(Note: `∞` is `C^∞` smoothness, not `ω` = analytic.) -/
structure IsCutoff (χ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ χ
  even : ∀ t, χ (-t) = χ t
  tsupport_subset : tsupport χ ⊆ Set.Ioo (-1) 1
  eq_one : ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), χ t = 1

/-- `ψ(t) = (χ(t) - χ(2t)) / t`, with `ψ(0) = 0`. -/
noncomputable def psi (χ : ℝ → ℝ) (t : ℝ) : ℝ := (χ t - χ (2 * t)) / t

/-- `ψ_k(t) = 2⁻ᵏ ψ(t 2⁻ᵏ)`. -/
noncomputable def psiK (χ : ℝ → ℝ) (k : ℕ) (t : ℝ) : ℝ := psi χ (t / 2 ^ k) / 2 ^ k

/-- `K_I = ∑_{k ∈ [a, b]} ψ_k` for the interval of scales `I = [a, b]`. -/
noncomputable def kernelI (χ : ℝ → ℝ) (a b : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc a b, psiK χ k t

section N01

variable {χ : ℝ → ℝ}

theorem psi_zero (χ : ℝ → ℝ) : psi χ 0 = 0 := by simp [psi]

theorem psiK_zero (χ : ℝ → ℝ) (k : ℕ) : psiK χ k 0 = 0 := by simp [psiK, psi_zero]

theorem kernelI_zero (χ : ℝ → ℝ) (a b : ℕ) : kernelI χ a b 0 = 0 := by
  simp [kernelI, psiK_zero]

/-- `ψ` is odd. -/
theorem IsCutoff.psi_neg (hχ : IsCutoff χ) (t : ℝ) : psi χ (-t) = -psi χ t := by
  have h2 : χ (2 * -t) = χ (2 * t) := by rw [mul_neg, hχ.even]
  simp only [psi, hχ.even, h2, div_neg]

/-- `ψ_k` is odd. -/
theorem IsCutoff.psiK_neg (hχ : IsCutoff χ) (k : ℕ) (t : ℝ) :
    psiK χ k (-t) = -psiK χ k t := by
  simp only [psiK, neg_div, hχ.psi_neg, neg_div]

theorem IsCutoff.eq_zero_of_one_le_abs (hχ : IsCutoff χ) {t : ℝ} (ht : 1 ≤ |t|) : χ t = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have := hχ.tsupport_subset h
  rcases this with ⟨h1, h2⟩
  rcases le_abs'.1 ht with h | h <;> linarith

theorem IsCutoff.eq_one_of_abs_le (hχ : IsCutoff χ) {t : ℝ} (ht : |t| ≤ 1 / 2) : χ t = 1 :=
  hχ.eq_one t (by rw [Set.mem_Icc]; constructor <;> linarith [abs_le.1 ht])

/-- `ψ` vanishes on `|t| ≤ 1/4`. -/
theorem IsCutoff.psi_eq_zero_of_abs_le (hχ : IsCutoff χ) {t : ℝ} (ht : |t| ≤ 1 / 4) :
    psi χ t = 0 := by
  have h1 : χ t = 1 := hχ.eq_one_of_abs_le (by linarith)
  have h2 : χ (2 * t) = 1 := by
    apply hχ.eq_one_of_abs_le
    rw [abs_mul, abs_two]; linarith
  simp [psi, h1, h2]

/-- `ψ` vanishes on `|t| ≥ 1`. -/
theorem IsCutoff.psi_eq_zero_of_one_le_abs (hχ : IsCutoff χ) {t : ℝ} (ht : 1 ≤ |t|) :
    psi χ t = 0 := by
  have h1 : χ t = 0 := hχ.eq_zero_of_one_le_abs ht
  have h2 : χ (2 * t) = 0 := by
    apply hχ.eq_zero_of_one_le_abs
    rw [abs_mul, abs_two]; linarith
  simp [psi, h1, h2]

/-- N01 (support of `ψ`): `supp ψ ⊆ {1/4 ≤ |t| < 1}`. -/
theorem IsCutoff.support_psi_subset (hχ : IsCutoff χ) :
    Function.support (psi χ) ⊆ {t | 1 / 4 ≤ |t| ∧ |t| < 1} := by
  intro t ht
  rw [Function.mem_support] at ht
  refine ⟨?_, ?_⟩
  · by_contra h
    exact ht (hχ.psi_eq_zero_of_abs_le (by linarith [not_le.1 h]))
  · by_contra h
    exact ht (hχ.psi_eq_zero_of_one_le_abs (not_lt.1 h))

/-- N01 (support of `ψ_k`): `ψ_k t ≠ 0 → 2^k ≤ 4 |t| ∧ |t| < 2^k`, i.e. `2^{k-2} ≤ |t| < 2^k`. -/
theorem IsCutoff.support_psiK_subset (hχ : IsCutoff χ) (k : ℕ) :
    Function.support (psiK χ k) ⊆ {t | (2 : ℝ) ^ k ≤ 4 * |t| ∧ |t| < 2 ^ k} := by
  intro t ht
  rw [Function.mem_support] at ht
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hne : psi χ (t / 2 ^ k) ≠ 0 := fun h => ht (by simp [psiK, h])
  have hmem : t / 2 ^ k ∈ Function.support (psi χ) := hne
  obtain ⟨h1, h2⟩ := hχ.support_psi_subset hmem
  rw [abs_div, abs_of_pos hpos] at h1 h2
  rw [le_div_iff₀ hpos] at h1
  rw [div_lt_one hpos] at h2
  exact ⟨by linarith, h2⟩

/-- Smoothness of `ψ`. -/
theorem IsCutoff.contDiff_psi (hχ : IsCutoff χ) : ContDiff ℝ ∞ (psi χ) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t = 0
  · subst ht
    have hev : psi χ =ᶠ[nhds 0] fun _ => (0 : ℝ) := by
      have hmem : Set.Ioo (-(1 / 4 : ℝ)) (1 / 4) ∈ nhds (0 : ℝ) :=
        Ioo_mem_nhds (by norm_num) (by norm_num)
      filter_upwards [hmem] with s hs
      exact hχ.psi_eq_zero_of_abs_le (abs_le.2 ⟨hs.1.le, hs.2.le⟩)
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have h1 : ContDiffAt ℝ ∞ χ t := hχ.contDiff.contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fun s : ℝ => χ (2 * s)) t :=
      (hχ.contDiff.comp (contDiff_const.mul contDiff_id)).contDiffAt
    exact (h1.sub h2).div contDiffAt_id ht

theorem IsCutoff.hasCompactSupport_psi (hχ : IsCutoff χ) : HasCompactSupport (psi χ) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro t ht
  apply hχ.psi_eq_zero_of_one_le_abs
  by_contra h
  rw [not_le, abs_lt] at h
  exact ht ⟨h.1.le, h.2.le⟩

/-- `ψ` is bounded: `c_ψ = ‖ψ‖_∞`. -/
theorem IsCutoff.exists_bound_psi (hχ : IsCutoff χ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |psi χ t| ≤ B := by
  obtain ⟨C, hC⟩ :=
    hχ.contDiff_psi.continuous.bounded_above_of_compact_support hχ.hasCompactSupport_psi
  exact ⟨max C 0, le_max_right _ _, fun t => (le_of_eq_of_le (Real.norm_eq_abs _).symm (hC t)).trans (le_max_left _ _)⟩

/-- `ψ` is Lipschitz. -/
theorem IsCutoff.exists_lipschitz_psi (hχ : IsCutoff χ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s t, |psi χ s - psi χ t| ≤ L * |s - t| := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hχ.hasCompactSupport_psi
    (hχ.contDiff_psi.of_le (by exact_mod_cast le_top)) one_ne_zero
  refine ⟨C, C.2, fun s t => ?_⟩
  have := hC.dist_le_mul s t
  simpa [Real.dist_eq] using this

/-- N01 (d): `|ψ_k t| ≤ c_ψ 2^{-k}` and `ψ_k t = 0` for `|t| ≥ 2^k`. -/
theorem abs_psiK_le {B : ℝ} (hB : ∀ t, |psi χ t| ≤ B) (k : ℕ)
    (t : ℝ) : |psiK χ k t| ≤ B / 2 ^ k := by
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  rw [psiK, abs_div, abs_of_pos hpos]
  exact div_le_div_of_nonneg_right (hB _) hpos.le

theorem IsCutoff.psiK_eq_zero_of_le_abs (hχ : IsCutoff χ) (k : ℕ) {t : ℝ} (ht : (2 : ℝ) ^ k ≤ |t|) :
    psiK χ k t = 0 := by
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have : 1 ≤ |t / 2 ^ k| := by
    rw [abs_div, abs_of_pos hpos, le_div_iff₀ hpos]; linarith
  simp [psiK, hχ.psi_eq_zero_of_one_le_abs this]

/-- The identity `s ψ(s) = χ(s) - χ(2 s)` for `s ≠ 0`. -/
theorem mul_psi (χ : ℝ → ℝ) {s : ℝ} (hs : s ≠ 0) : s * psi χ s = χ s - χ (2 * s) := by
  rw [psi, mul_div_cancel₀ _ hs]

/-- N01 (a): `ψ_k(t) = (χ(2⁻ᵏ t) - χ(2^{1-k} t)) / t` for `t ≠ 0` (here `2^{1-k} t = t / 2^(k-1)`,
valid for `k ≥ 1`). -/
theorem psiK_eq (χ : ℝ → ℝ) {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : t ≠ 0) :
    psiK χ k t = (χ (t / 2 ^ k) - χ (t / 2 ^ (k - 1))) / t := by
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hs : t / 2 ^ k ≠ 0 := div_ne_zero ht hpos.ne'
  have h2 : 2 * (t / 2 ^ k) = t / 2 ^ (k - 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]; field_simp
  have key := mul_psi χ hs
  rw [h2] at key
  rw [eq_div_iff ht, psiK]
  have : psi χ (t / 2 ^ k) / 2 ^ k * t = (t / 2 ^ k) * psi χ (t / 2 ^ k) := by ring
  rw [this, key]

/-- N01 (b), inductive form: for `1 ≤ a`, `t * ∑_{k=a}^{a+m} ψ_k(t) = χ(t/2^{a+m}) - χ(t/2^{a-1})`. -/
theorem mul_kernelI_add (χ : ℝ → ℝ) {a : ℕ} (ha : 1 ≤ a) (t : ℝ) (m : ℕ) :
    t * kernelI χ a (a + m) t = χ (t / 2 ^ (a + m)) - χ (t / 2 ^ (a - 1)) := by
  induction m with
  | zero =>
    have h1 : t * psiK χ a t = χ (t / 2 ^ a) - χ (t / 2 ^ (a - 1)) := by
      by_cases ht : t = 0
      · subst ht; simp [psiK_zero]
      · rw [psiK_eq χ ha ht]; field_simp
    simpa [kernelI] using h1
  | succ m ih =>
    have h1 : t * psiK χ (a + m + 1) t =
        χ (t / 2 ^ (a + m + 1)) - χ (t / 2 ^ (a + m)) := by
      by_cases ht : t = 0
      · subst ht; simp [psiK_zero]
      · rw [psiK_eq χ (by omega) ht, Nat.add_sub_cancel]; field_simp
    have hs : kernelI χ a (a + (m + 1)) t = kernelI χ a (a + m) t + psiK χ (a + m + 1) t := by
      rw [← add_assoc, kernelI, kernelI, Finset.sum_Icc_succ_top (by omega)]
    rw [hs, mul_add, ih, h1, ← add_assoc]
    ring

/-- N01 (b): for `1 ≤ a ≤ b`, `t K_I(t) = χ(2^{-b} t) - χ(2^{1-a} t)`. -/
theorem mul_kernelI (χ : ℝ → ℝ) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (t : ℝ) :
    t * kernelI χ a b t = χ (t / 2 ^ b) - χ (t / 2 ^ (a - 1)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hab
  exact mul_kernelI_add χ ha t m

/-- N01 (telescoping): `∑_{k=1}^J ψ_k(t) = (χ(t/2^J) - χ(t))/t` for `t ≠ 0` (all `J`). -/
theorem sum_psiK_eq (χ : ℝ → ℝ) (J : ℕ) {t : ℝ} (ht : t ≠ 0) :
    ∑ k ∈ Finset.Icc 1 J, psiK χ k t = (χ (t / 2 ^ J) - χ t) / t := by
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · simp
  · have h := mul_kernelI χ (le_refl 1) hJ t
    rw [eq_div_iff ht, mul_comm]
    simpa [kernelI] using h

/-- N01 (c) for real `t`: `∑_{k=1}^J ψ_k(t) = 1/t` for `|t| ≥ 1`, `2^J ≥ 2|t|`. -/
theorem IsCutoff.sum_psiK_eq_inv (hχ : IsCutoff χ) {J : ℕ} {t : ℝ} (ht : 1 ≤ |t|)
    (hJ : 2 * |t| ≤ 2 ^ J) : ∑ k ∈ Finset.Icc 1 J, psiK χ k t = 1 / t := by
  have ht0 : t ≠ 0 := abs_pos.1 (by linarith)
  have hpos : (0 : ℝ) < 2 ^ J := by positivity
  have h1 : χ (t / 2 ^ J) = 1 := by
    apply hχ.eq_one_of_abs_le
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]; linarith
  rw [sum_psiK_eq χ J ht0, h1, hχ.eq_zero_of_one_le_abs ht]
  simp

/-- N01 (c): `∑_{k=1}^J ψ_k(n) = 1/n` for every integer `n ≠ 0` and `2^J ≥ 2|n|`. -/
theorem IsCutoff.sum_psiK_int (hχ : IsCutoff χ) {J : ℕ} {n : ℤ} (hn : n ≠ 0)
    (hJ : 2 * |(n : ℝ)| ≤ 2 ^ J) : ∑ k ∈ Finset.Icc 1 J, psiK χ k (n : ℝ) = 1 / (n : ℝ) := by
  apply hχ.sum_psiK_eq_inv _ hJ
  have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
  have h2 : (1 : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast this
  simpa using h2

/-- Existence of an admissible cutoff (from Mathlib's `ContDiffBump`, `rIn = 1/2`,
`rOut = 3/4`). -/
theorem exists_isCutoff : ∃ χ : ℝ → ℝ, IsCutoff χ := by
  let f : ContDiffBump (0 : ℝ) := ⟨1 / 2, 3 / 4, by norm_num, by norm_num⟩
  refine ⟨f, ⟨f.contDiff, f.neg, ?_, ?_⟩⟩
  · intro t ht
    rw [f.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at ht
    show -1 < t ∧ t < 1
    have : f.rOut = 3 / 4 := rfl
    rw [this] at ht
    constructor <;> linarith [ht.1, ht.2]
  · intro t ht
    apply f.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
    have : f.rIn = 1 / 2 := rfl
    rw [this]
    constructor <;> linarith [ht.1, ht.2]

end N01

section Smoothing

open MeasureTheory
open scoped Convolution

/-- Dilation `φ_N(y) = N⁻¹ φ(y / N)`. -/
noncomputable def dilate (φ : ℝ → ℝ) (N : ℝ) (y : ℝ) : ℝ := N⁻¹ * φ (y / N)

/-- The convolution on `ℝ` `(φ_N * K)(x) = ∫ φ_N(y) K(x - y) dy`. -/
noncomputable def smooth (φ : ℝ → ℝ) (N : ℝ) (K : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, dilate φ N y * K (x - y)

variable (φ : SchwartzMap ℝ ℝ)

theorem integrable_abs_mul_abs_pow (m : ℕ) : Integrable (fun u : ℝ => |φ u| * |u| ^ m) := by
  have h := φ.integrable_pow_mul volume m
  refine h.congr (ae_of_all _ fun u => ?_)
  simp [Real.norm_eq_abs, mul_comm]

theorem integrable_dilate {N : ℝ} (hN : 0 < N) : Integrable (dilate φ N) := by
  have := (φ.integrable (μ := volume)).comp_div hN.ne'
  exact this.const_mul N⁻¹

theorem abs_dilate_mul_abs_pow {N : ℝ} (hN : 0 < N) (m : ℕ) (y : ℝ) :
    |dilate φ N y| * |y| ^ m = N ^ m * N⁻¹ * (|φ (y / N)| * |y / N| ^ m) := by
  rw [dilate, abs_mul, abs_inv, abs_of_pos hN, abs_div, abs_of_pos hN, div_pow]
  field_simp

theorem integrable_abs_dilate_mul_abs_pow {N : ℝ} (hN : 0 < N) (m : ℕ) :
    Integrable (fun y => |dilate φ N y| * |y| ^ m) := by
  have h := ((integrable_abs_mul_abs_pow φ m).const_mul (N ^ m * N⁻¹)).comp_div hN.ne'
  refine h.congr (ae_of_all _ fun y => ?_)
  simp only [abs_dilate_mul_abs_pow φ hN m y]

/-- Scaling: `∫ |φ_N(y)| |y|^m dy = N^m ∫ |φ(u)| |u|^m du`. -/
theorem integral_abs_dilate_mul_abs_pow {N : ℝ} (hN : 0 < N) (m : ℕ) :
    ∫ y, |dilate φ N y| * |y| ^ m = N ^ m * ∫ u, |φ u| * |u| ^ m := by
  have h : (fun y => |dilate φ N y| * |y| ^ m) =
      fun y => (fun u : ℝ => N ^ m * N⁻¹ * (|φ u| * |u| ^ m)) (y / N) := by
    funext y
    exact abs_dilate_mul_abs_pow φ hN m y
  rw [h]
  refine (Measure.integral_comp_div (fun u : ℝ => N ^ m * N⁻¹ * (|φ u| * |u| ^ m)) N).trans ?_
  rw [smul_eq_mul, abs_of_pos hN, integral_const_mul]
  field_simp

/-- `∫ φ_N = ∫ φ`. -/
theorem integral_dilate {N : ℝ} (hN : 0 < N) : ∫ y, dilate φ N y = ∫ u, φ u := by
  have h : (fun y => dilate φ N y) = fun y => (fun u : ℝ => N⁻¹ * φ u) (y / N) := rfl
  rw [h]
  refine (Measure.integral_comp_div (fun u : ℝ => N⁻¹ * φ u) N).trans ?_
  rw [smul_eq_mul, abs_of_pos hN, integral_const_mul]
  field_simp

/-- Lipschitz bound for `ψ_k` from the one for `ψ`. -/
theorem abs_psiK_sub_le {χ : ℝ → ℝ} {L : ℝ} (hL : ∀ s t, |psi χ s - psi χ t| ≤ L * |s - t|)
    (k : ℕ) (s t : ℝ) : |psiK χ k s - psiK χ k t| ≤ L / (2 ^ k * 2 ^ k) * |s - t| := by
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have h : psiK χ k s - psiK χ k t = (psi χ (s / 2 ^ k) - psi χ (t / 2 ^ k)) / 2 ^ k := by
    simp only [psiK]; ring
  calc |psiK χ k s - psiK χ k t|
      = |psi χ (s / 2 ^ k) - psi χ (t / 2 ^ k)| / 2 ^ k := by
        rw [h, abs_div, abs_of_pos hpos]
    _ ≤ (L * |s / 2 ^ k - t / 2 ^ k|) / 2 ^ k := by gcongr; exact hL _ _
    _ = L / (2 ^ k * 2 ^ k) * |s - t| := by
        rw [← sub_div, abs_div, abs_of_pos hpos]; field_simp

theorem continuous_psiK {χ : ℝ → ℝ} (hχ : IsCutoff χ) (k : ℕ) : Continuous (psiK χ k) := by
  unfold psiK
  exact (hχ.contDiff_psi.continuous.comp (continuous_id.div_const _)).div_const _

theorem integrable_dilate_mul {K : ℝ → ℝ} (hK : Continuous K) {b : ℝ} (hb : ∀ t, |K t| ≤ b)
    {N : ℝ} (hN : 0 < N) (x : ℝ) : Integrable (fun y => dilate φ N y * K (x - y)) := by
  refine ((integrable_dilate φ hN).norm.mul_const b).mono' ?_ (ae_of_all _ fun y => ?_)
  · exact (integrable_dilate φ hN).aestronglyMeasurable.mul
      (hK.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hb _) (norm_nonneg _)

theorem smooth_sub_eq {K : ℝ → ℝ} (hK : Continuous K) {b : ℝ} (hb : ∀ t, |K t| ≤ b)
    (hφ : ∫ u, φ u = 1) {N : ℝ} (hN : 0 < N) (x : ℝ) :
    smooth φ N K x - K x = ∫ y, dilate φ N y * (K (x - y) - K x) := by
  simp only [smooth, mul_sub]
  rw [integral_sub (integrable_dilate_mul φ hK hb hN x) ((integrable_dilate φ hN).mul_const _),
    integral_mul_const, integral_dilate φ hN, hφ, one_mul]

/-- Regime of small `|x|`: Lipschitz (mean value) estimate. -/
theorem abs_smooth_sub_le_of_lipschitz {K : ℝ → ℝ} (hK : Continuous K) {b : ℝ}
    (hb : ∀ t, |K t| ≤ b) {Λ : ℝ} (hΛ : ∀ s t, |K s - K t| ≤ Λ * |s - t|)
    (hφ : ∫ u, φ u = 1) {N : ℝ} (hN : 0 < N) (x : ℝ) :
    |smooth φ N K x - K x| ≤ Λ * (N ^ 1 * ∫ u, |φ u| * |u| ^ 1) := by
  rw [smooth_sub_eq φ hK hb hφ hN x]
  have hint : Integrable (fun y => Λ * (|dilate φ N y| * |y| ^ 1)) :=
    (integrable_abs_dilate_mul_abs_pow φ hN 1).const_mul Λ
  have h := norm_integral_le_of_norm_le hint (f := fun y => dilate φ N y * (K (x - y) - K x))
    (ae_of_all _ fun y => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |dilate φ N y| * |K (x - y) - K x|
          ≤ |dilate φ N y| * (Λ * |x - y - x|) := by
            gcongr; exact hΛ _ _
        _ = Λ * (|dilate φ N y| * |y| ^ 1) := by
            rw [show x - y - x = -y by ring, abs_neg, pow_one]; ring)
  rw [integral_const_mul, integral_abs_dilate_mul_abs_pow φ hN 1] at h
  simpa [Real.norm_eq_abs] using h

/-- Regime of large `|x|`: tail estimate. -/
theorem abs_smooth_sub_le_of_tail {K : ℝ → ℝ} (hK : Continuous K) {b : ℝ}
    (hb : ∀ t, |K t| ≤ b) (hφ : ∫ u, φ u = 1) {N : ℝ} (hN : 0 < N) {x : ℝ} (hx : 0 < |x|)
    (hKx : K x = 0) (hsupp : ∀ y, K (x - y) ≠ 0 → |x| ≤ 2 * |y|) :
    |smooth φ N K x - K x| ≤ b * ((2 / |x|) ^ 10 * (N ^ 10 * ∫ u, |φ u| * |u| ^ 10)) := by
  rw [smooth_sub_eq φ hK hb hφ hN x]
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hb 0)
  have hint : Integrable (fun y => b * (2 / |x|) ^ 10 * (|dilate φ N y| * |y| ^ 10)) :=
    (integrable_abs_dilate_mul_abs_pow φ hN 10).const_mul _
  have h := norm_integral_le_of_norm_le hint (f := fun y => dilate φ N y * (K (x - y) - K x))
    (ae_of_all _ fun y => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, hKx, sub_zero]
      by_cases hy : K (x - y) = 0
      · rw [hy, abs_zero, mul_zero]; positivity
      · have h2 : 1 ≤ (2 / |x|) ^ 10 * |y| ^ 10 := by
          rw [← mul_pow, one_le_pow_iff_of_nonneg (by positivity) (by norm_num),
            div_mul_eq_mul_div, le_div_iff₀ hx]
          linarith [hsupp y hy]
        calc |dilate φ N y| * |K (x - y)| ≤ |dilate φ N y| * b := by
              gcongr; exact hb _
          _ = b * (|dilate φ N y|) * 1 := by ring
          _ ≤ b * |dilate φ N y| * ((2 / |x|) ^ 10 * |y| ^ 10) := by
              gcongr
          _ = b * (2 / |x|) ^ 10 * (|dilate φ N y| * |y| ^ 10) := by ring)
  rw [integral_const_mul, integral_abs_dilate_mul_abs_pow φ hN 10] at h
  calc |∫ y, dilate φ N y * (K (x - y) - K x)| ≤ _ := by simpa [Real.norm_eq_abs] using h
    _ = _ := by ring

theorem alg_small {R a N L M C : ℝ} (hR : 0 < R) (ha0 : 0 ≤ a) (ha : a ≤ 2 * R) (hN : 0 < N)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hC : 3 ^ 10 * L * M ≤ C) :
    L / (R * R) * (N * M) ≤ C * (N / R) * (1 / R) * ((1 + a / R) ^ 10)⁻¹ := by
  have h2 : a / R ≤ 2 := by rw [div_le_iff₀ hR]; linarith
  have hS0 : 0 < 1 + a / R := by positivity
  have hpow : (1 + a / R) ^ 10 ≤ 3 ^ 10 := pow_le_pow_left₀ hS0.le (by linarith) 10
  have h1 : 1 ≤ 3 ^ 10 * ((1 + a / R) ^ 10)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; linarith
  calc L / (R * R) * (N * M)
      ≤ L / (R * R) * (N * M) * (3 ^ 10 * ((1 + a / R) ^ 10)⁻¹) :=
        le_mul_of_one_le_right (by positivity) h1
    _ = (3 ^ 10 * L * M) * (N / R) * (1 / R) * ((1 + a / R) ^ 10)⁻¹ := by field_simp
    _ ≤ C * (N / R) * (1 / R) * ((1 + a / R) ^ 10)⁻¹ := by gcongr

theorem alg_large {R a N B M C : ℝ} (hR : 0 < R) (ha : 2 * R < a) (hN : 0 < N) (hNR : N ≤ R)
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hC : 2 ^ 20 * B * M ≤ C) :
    B / R * ((2 / a) ^ 10 * (N ^ 10 * M)) ≤ C * (N / R) * (1 / R) * ((1 + a / R) ^ 10)⁻¹ := by
  have ha0 : 0 < a := by linarith
  have h2 : 2 ≤ a / R := by rw [le_div_iff₀ hR]; linarith
  have hS : 1 + a / R ≤ 2 * a / R := by
    rw [mul_div_assoc]; linarith
  have hS0 : 0 < 1 + a / R := by positivity
  have hinv : (R / (2 * a)) ^ 10 ≤ ((1 + a / R) ^ 10)⁻¹ := by
    have : (R / (2 * a)) ^ 10 = ((2 * a / R) ^ 10)⁻¹ := by
      rw [← inv_pow, inv_div]
    rw [this]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hS0.le hS 10)
  have hN9 : N ^ 9 ≤ R ^ 9 := pow_le_pow_left₀ hN.le hNR 9
  calc B / R * ((2 / a) ^ 10 * (N ^ 10 * M))
      = (B * M * 2 ^ 10 / (R * a ^ 10)) * N ^ 10 := by field_simp
    _ ≤ (B * M * 2 ^ 10 / (R * a ^ 10)) * (N * R ^ 9) := by
        gcongr
        calc N ^ 10 = N * N ^ 9 := by ring
          _ ≤ N * R ^ 9 := by gcongr
    _ = (2 ^ 20 * B * M) * (N / R) * (1 / R) * (R / (2 * a)) ^ 10 := by
        field_simp
    _ ≤ C * (N / R) * (1 / R) * (R / (2 * a)) ^ 10 := by gcongr
    _ ≤ C * (N / R) * (1 / R) * ((1 + a / R) ^ 10)⁻¹ := by
        have hC0 : 0 ≤ C := le_trans (by positivity) hC
        gcongr

/-- N25 (pointwise smoothing bound): for `0 < N ≤ 2^k`,
`|(φ_N * ψ_k)(x) - ψ_k(x)| ≤ C (N / 2^k) 2^{-k} (1 + |x| / 2^k)^{-10}`, with `C = C(φ, χ)`. -/
theorem IsCutoff.exists_smoothing_bound {χ : ℝ → ℝ} (hχ : IsCutoff χ) (hφ : ∫ u, φ u = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℝ) (k : ℕ) (x : ℝ), 0 < N → N ≤ 2 ^ k →
      |smooth φ N (psiK χ k) x - psiK χ k x| ≤
        C * (N / 2 ^ k) * (1 / 2 ^ k) * ((1 + |x| / 2 ^ k) ^ 10)⁻¹ := by
  obtain ⟨B, hB0, hB⟩ := hχ.exists_bound_psi
  obtain ⟨L, hL0, hL⟩ := hχ.exists_lipschitz_psi
  set M₁ : ℝ := ∫ u, |φ u| * |u| ^ 1 with hM₁
  set M₁₀ : ℝ := ∫ u, |φ u| * |u| ^ 10 with hM₁₀
  have hM₁0 : 0 ≤ M₁ := integral_nonneg fun u => by positivity
  have hM₁₀0 : 0 ≤ M₁₀ := integral_nonneg fun u => by positivity
  refine ⟨max (3 ^ 10 * L * M₁) (2 ^ 20 * B * M₁₀), le_max_of_le_left (by positivity),
    fun N k x hN hNk => ?_⟩
  have hR : (0 : ℝ) < 2 ^ k := by positivity
  have hKc := continuous_psiK hχ k
  have hKb : ∀ t, |psiK χ k t| ≤ B / 2 ^ k := fun t => abs_psiK_le hB k t
  by_cases hx : |x| ≤ 2 * 2 ^ k
  · have h := abs_smooth_sub_le_of_lipschitz φ hKc hKb (abs_psiK_sub_le hL k) hφ hN x
    rw [pow_one] at h
    exact h.trans (alg_small hR (abs_nonneg x) hx hN hL0 hM₁0 (le_max_left _ _))
  · rw [not_le] at hx
    have hx0 : 0 < |x| := by linarith
    have hKx : psiK χ k x = 0 := hχ.psiK_eq_zero_of_le_abs k (by linarith)
    have hsupp : ∀ y, psiK χ k (x - y) ≠ 0 → |x| ≤ 2 * |y| := by
      intro y hy
      have h1 := (hχ.support_psiK_subset k (Function.mem_support.2 hy)).2
      have h2 : |x| ≤ |x - y| + |y| := by
        calc |x| = |(x - y) + y| := by ring_nf
          _ ≤ |x - y| + |y| := abs_add_le _ _
      linarith
    have h := abs_smooth_sub_le_of_tail φ hKc hKb hφ hN hx0 hKx hsupp
    exact h.trans (alg_large hR hx hN hNk hB0 hM₁₀0 (le_max_right _ _))

end Smoothing

section L1

/-- `ℓ²(ℤ)` norm `(∑ₙ ‖f n‖²)^{1/2}` (for finitely supported `f` this is a finite sum). -/
noncomputable def l2norm (f : ℤ → ℂ) : ℝ := Real.sqrt (∑' n, ‖f n‖ ^ 2)

/-- The bilinear expression `B_a(f, g)(x) = ∑ₙ a(n) f(x - n) g(x + n)`
(a finite sum for finitely supported `f, g`). -/
noncomputable def bilin (a : ℤ → ℂ) (f g : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑' n, a n * f (x - n) * g (x + n)

theorem l2norm_nonneg (f : ℤ → ℂ) : 0 ≤ l2norm f := Real.sqrt_nonneg _

theorem summable_norm_sq_of_finite_support {f : ℤ → ℂ} (hf : (Function.support f).Finite) :
    Summable (fun x => ‖f x‖ ^ 2) := by
  refine summable_of_ne_finset_zero (s := hf.toFinset) fun x hx => ?_
  rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hx
  simp [hx]

/-- Cauchy-Schwarz in `x` for a fixed shift `n`. -/
theorem sum_norm_mul_le {f g : ℤ → ℂ} (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) (n : ℤ) (X : Finset ℤ) :
    ∑ x ∈ X, ‖f (x - n)‖ * ‖g (x + n)‖ ≤ l2norm f * l2norm g := by
  have hsf := summable_norm_sq_of_finite_support hf
  have hsg := summable_norm_sq_of_finite_support hg
  have hsf' : Summable (fun x => ‖f (x - n)‖ ^ 2) := hsf.comp_injective (sub_left_injective (b := n))
  have hsg' : Summable (fun x => ‖g (x + n)‖ ^ 2) := hsg.comp_injective (add_left_injective n)
  have htf : ∑' x, ‖f (x - n)‖ ^ 2 = ∑' x, ‖f x‖ ^ 2 :=
    (Equiv.subRight n).tsum_eq (fun x => ‖f x‖ ^ 2)
  have htg : ∑' x, ‖g (x + n)‖ ^ 2 = ∑' x, ‖g x‖ ^ 2 :=
    (Equiv.addRight n).tsum_eq (fun x => ‖g x‖ ^ 2)
  have h1 : ∑ x ∈ X, ‖f (x - n)‖ ^ 2 ≤ ∑' x, ‖f x‖ ^ 2 := by
    rw [← htf]; exact hsf'.sum_le_tsum X (fun _ _ => by positivity)
  have h2 : ∑ x ∈ X, ‖g (x + n)‖ ^ 2 ≤ ∑' x, ‖g x‖ ^ 2 := by
    rw [← htg]; exact hsg'.sum_le_tsum X (fun _ _ => by positivity)
  have hF : 0 ≤ ∑' x, ‖f x‖ ^ 2 := tsum_nonneg fun _ => by positivity
  have hG : 0 ≤ ∑' x, ‖g x‖ ^ 2 := tsum_nonneg fun _ => by positivity
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq X (fun x => ‖f (x - n)‖) (fun x => ‖g (x + n)‖)
  rw [l2norm, l2norm, ← Real.sqrt_mul hF]
  apply Real.le_sqrt_of_sq_le
  refine hcs.trans (mul_le_mul h1 h2 (Finset.sum_nonneg fun _ _ => by positivity) hF)

/-- The `ℓ¹` bound for the bilinear form, in terms of a bound on the finite partial sums of the
weight. -/
theorem l1_bilin_le {f g : ℤ → ℂ} (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) {a : ℤ → ℂ} {E : ℝ}
    (ha : ∀ s : Finset ℤ, ∑ n ∈ s, ‖a n‖ ≤ E) :
    Summable (fun x => ‖bilin a f g x‖) ∧
      ∑' x, ‖bilin a f g x‖ ≤ E * (l2norm f * l2norm g) := by
  classical
  set Sf := hf.toFinset
  set Sg := hg.toFinset
  set Nfin : Finset ℤ := (Sg ×ˢ Sf).image (fun p => (p.1 - p.2) / 2) with hNfin
  set Xfin : Finset ℤ := (Sg ×ˢ Sf).image (fun p => (p.1 + p.2) / 2) with hXfin
  have hmem : ∀ x n : ℤ, f (x - n) * g (x + n) ≠ 0 → n ∈ Nfin ∧ x ∈ Xfin := by
    intro x n h
    have h1 : f (x - n) ≠ 0 := left_ne_zero_of_mul h
    have h2 : g (x + n) ≠ 0 := right_ne_zero_of_mul h
    have hp : ((x + n, x - n) : ℤ × ℤ) ∈ Sg ×ˢ Sf := by
      simp [Sg, Sf, h1, h2]
    refine ⟨Finset.mem_image.2 ⟨_, hp, ?_⟩, Finset.mem_image.2 ⟨_, hp, ?_⟩⟩
    · show (x + n - (x - n)) / 2 = n
      omega
    · show (x + n + (x - n)) / 2 = x
      omega
  have hterm : ∀ x n, n ∉ Nfin → a n * f (x - n) * g (x + n) = 0 := by
    intro x n hn
    by_contra h
    apply hn
    refine (hmem x n ?_).1
    intro h0; apply h; rw [mul_assoc, h0, mul_zero]
  have hbil : ∀ x, bilin a f g x = ∑ n ∈ Nfin, a n * f (x - n) * g (x + n) := fun x =>
    tsum_eq_sum (fun n hn => hterm x n hn)
  have hzero : ∀ x, x ∉ Xfin → bilin a f g x = 0 := by
    intro x hx
    rw [hbil]
    apply Finset.sum_eq_zero
    intro n _
    by_contra h
    apply hx
    refine (hmem x n ?_).2
    intro h0; apply h; rw [mul_assoc, h0, mul_zero]
  have hz : ∀ x ∉ Xfin, ‖bilin a f g x‖ = 0 := fun x hx => by rw [hzero x hx, norm_zero]
  refine ⟨summable_of_ne_finset_zero hz, ?_⟩
  rw [tsum_eq_sum hz]
  calc ∑ x ∈ Xfin, ‖bilin a f g x‖
      ≤ ∑ x ∈ Xfin, ∑ n ∈ Nfin, ‖a n‖ * (‖f (x - n)‖ * ‖g (x + n)‖) := by
        apply Finset.sum_le_sum
        intro x _
        rw [hbil]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        rw [norm_mul, norm_mul, mul_assoc]
    _ = ∑ n ∈ Nfin, ‖a n‖ * ∑ x ∈ Xfin, ‖f (x - n)‖ * ‖g (x + n)‖ := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
    _ ≤ ∑ n ∈ Nfin, ‖a n‖ * (l2norm f * l2norm g) := by
        gcongr with n hn
        exact sum_norm_mul_le hf hg n Xfin
    _ = (∑ n ∈ Nfin, ‖a n‖) * (l2norm f * l2norm g) := by rw [Finset.sum_mul]
    _ ≤ E * (l2norm f * l2norm g) :=
        mul_le_mul_of_nonneg_right (ha Nfin) (mul_nonneg (l2norm_nonneg f) (l2norm_nonneg g))

end L1

section Tail

/-- Telescoping bound for `∑ R² / (R + m + 1)²`. -/
theorem sum_range_sq_le {R : ℝ} (hR : 0 < R) (M : ℕ) :
    ∑ m ∈ Finset.range M, R ^ 2 / (R + ((m + 1 : ℕ) : ℝ)) ^ 2 ≤ R - R ^ 2 / (R + M) := by
  induction M with
  | zero =>
    have : R ^ 2 / R = R := by field_simp
    simp [this]
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hu : 0 < R + M := by positivity
    have key : R ^ 2 / (R + ((M + 1 : ℕ) : ℝ)) ^ 2 ≤
        R ^ 2 / (R + M) - R ^ 2 / (R + ((M + 1 : ℕ) : ℝ)) := by
      push_cast
      have e : R ^ 2 / (R + M) - R ^ 2 / (R + (M + 1)) = R ^ 2 / ((R + M) * (R + (M + 1))) := by
        field_simp; ring
      rw [e]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    linarith

theorem hfun_le {R u : ℝ} (hR : 0 < R) (hu : 0 ≤ u) :
    ((1 + u / R) ^ 10)⁻¹ ≤ R ^ 2 / (R + u) ^ 2 := by
  have h0 : 0 ≤ u / R := by positivity
  have h1 : 1 ≤ 1 + u / R := by linarith
  have h2 : (1 + u / R) ^ 2 ≤ (1 + u / R) ^ 10 := pow_le_pow_right₀ h1 (by norm_num)
  calc ((1 + u / R) ^ 10)⁻¹ ≤ ((1 + u / R) ^ 2)⁻¹ := inv_anti₀ (by positivity) h2
    _ = R ^ 2 / (R + u) ^ 2 := by
        have : R + u ≠ 0 := by positivity
        field_simp

/-- The dominating function of the pointwise bound is uniformly summable: for `R ≥ 1`,
`∑_{n ∈ s} (1 + |n|/R)^{-10} ≤ 3 R` for every finite `s ⊆ ℤ`. -/
theorem sum_hfun_le {R : ℝ} (hR : 1 ≤ R) (s : Finset ℤ) :
    ∑ n ∈ s, ((1 + |(n : ℝ)| / R) ^ 10)⁻¹ ≤ 3 * R := by
  have hR0 : 0 < R := by linarith
  set h : ℤ → ℝ := fun n => ((1 + |(n : ℝ)| / R) ^ 10)⁻¹ with hh
  have hnn : ∀ n, 0 ≤ h n := fun n => by positivity
  have hpos_term : ∀ m : ℕ, h ((m + 1 : ℕ) : ℤ) ≤ R ^ 2 / (R + ((m + 1 : ℕ) : ℝ)) ^ 2 := by
    intro m
    have e1 : h ((m + 1 : ℕ) : ℤ) = ((1 + ((m + 1 : ℕ) : ℝ) / R) ^ 10)⁻¹ := by
      simp only [hh, Int.cast_natCast]
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
    rw [e1]
    exact hfun_le hR0 (by positivity)
  have hneg_term : ∀ m : ℕ, h (-((m : ℤ) + 1)) ≤ R ^ 2 / (R + ((m + 1 : ℕ) : ℝ)) ^ 2 := by
    intro m
    have e1 : h (-((m : ℤ) + 1)) = ((1 + ((m + 1 : ℕ) : ℝ) / R) ^ 10)⁻¹ := by
      simp only [hh]
      have : ((-((m : ℤ) + 1) : ℤ) : ℝ) = -((m + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [this, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
    rw [e1]
    exact hfun_le hR0 (by positivity)
  have htail : ∀ M : ℕ, ∑ m ∈ Finset.range M, R ^ 2 / (R + ((m + 1 : ℕ) : ℝ)) ^ 2 ≤ R := by
    intro M
    have h1 := sum_range_sq_le hR0 M
    have : 0 ≤ R ^ 2 / (R + M) := by positivity
    linarith
  have hposS : ∀ M : ℕ, ∑ m ∈ Finset.range M, h (m : ℤ) ≤ 1 + R := by
    intro M
    cases M with
    | zero => simp; linarith
    | succ M =>
      rw [Finset.sum_range_succ']
      have h0 : h ((0 : ℕ) : ℤ) = 1 := by simp [hh]
      have h1 : ∑ m ∈ Finset.range M, h (((m + 1 : ℕ) : ℤ)) ≤ R :=
        (Finset.sum_le_sum fun m _ => hpos_term m).trans (htail M)
      have h2 : ∑ m ∈ Finset.range M, h ((m + 1 : ℕ) : ℤ) =
          ∑ m ∈ Finset.range M, h (((m + 1 : ℕ) : ℤ)) := rfl
      rw [h0]
      push_cast at h1 ⊢
      linarith
  have hnegS : ∀ M : ℕ, ∑ m ∈ Finset.range M, h (-((m : ℤ) + 1)) ≤ R := fun M =>
    (Finset.sum_le_sum fun m _ => hneg_term m).trans (htail M)
  have hs1 : Summable (fun m : ℕ => h (m : ℤ)) :=
    summable_of_sum_range_le (fun m => hnn _) hposS
  have hs2 : Summable (fun m : ℕ => h (-((m : ℤ) + 1))) :=
    summable_of_sum_range_le (fun m => hnn _) hnegS
  have hs : Summable h := Summable.of_nat_of_neg_add_one hs1 hs2
  have htsum : ∑' n, h n = (∑' m : ℕ, h (m : ℤ)) + ∑' m : ℕ, h (-((m : ℤ) + 1)) :=
    tsum_of_nat_of_neg_add_one hs1 hs2
  have t1 : ∑' m : ℕ, h (m : ℤ) ≤ 1 + R := Real.tsum_le_of_sum_range_le (fun m => hnn _) hposS
  have t2 : ∑' m : ℕ, h (-((m : ℤ) + 1)) ≤ R :=
    Real.tsum_le_of_sum_range_le (fun m => hnn _) hnegS
  calc ∑ n ∈ s, h n ≤ ∑' n, h n := hs.sum_le_tsum s (fun n _ => hnn n)
    _ ≤ 3 * R := by linarith

theorem sum_Icc_half_pow_le (a J : ℕ) :
    ∑ k ∈ Finset.Icc a J, ((1 : ℝ) / 2) ^ k ≤ 2 * ((1 : ℝ) / 2) ^ a := by
  by_cases hJ : a ≤ J
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hJ
    have key : ∀ m : ℕ, ∑ k ∈ Finset.Icc a (a + m), ((1 : ℝ) / 2) ^ k ≤
        2 * ((1 : ℝ) / 2) ^ a - ((1 : ℝ) / 2) ^ (a + m) := by
      intro m
      induction m with
      | zero => simp; linarith
      | succ m ih =>
        rw [← add_assoc, Finset.sum_Icc_succ_top (by omega)]
        have : ((1 : ℝ) / 2) ^ (a + m) = 2 * ((1 : ℝ) / 2) ^ (a + m + 1) := by
          rw [pow_succ]; ring
        linarith
    have := key m
    have h2 : 0 ≤ ((1 : ℝ) / 2) ^ (a + m) := by positivity
    linarith
  · rw [Finset.Icc_eq_empty_of_lt (by omega)]
    simp only [Finset.sum_empty]
    positivity

end Tail

section L1Final

open MeasureTheory

variable (φ : SchwartzMap ℝ ℝ)

/-- Linearity of the smoothing in the scale sum. -/
theorem smooth_kernelI {χ : ℝ → ℝ} (hχ : IsCutoff χ) {N : ℝ} (hN : 0 < N) (a J : ℕ) (x : ℝ) :
    smooth φ N (kernelI χ a J) x = ∑ k ∈ Finset.Icc a J, smooth φ N (psiK χ k) x := by
  obtain ⟨B, hB0, hB⟩ := hχ.exists_bound_psi
  unfold smooth kernelI
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  intro k _
  exact integrable_dilate_mul φ (continuous_psiK hχ k) (fun t => abs_psiK_le hB k t) hN x

/-- N25 (a), `ℓ¹` form, for an interval `I = [a, J]` of scales (uniform in `J`): for every weight
`w` with `‖w n‖ ≤ W`, finitely supported `f, g` and `0 < N ≤ 2^a`,
`‖x ↦ ∑ₙ w(n) (K_I(n) - (φ_N * K_I)(n)) f(x-n) g(x+n)‖_{ℓ¹} ≤ C W (N / 2^a) ‖f‖₂ ‖g‖₂`. -/
theorem IsCutoff.l1_smoothing_error_le {χ : ℝ → ℝ} (hχ : IsCutoff χ) (hφ : ∫ u, φ u = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℝ) (a J : ℕ) (w : ℤ → ℂ) (W : ℝ) (f g : ℤ → ℂ),
      0 < N → N ≤ 2 ^ a → (∀ n, ‖w n‖ ≤ W) →
      (Function.support f).Finite → (Function.support g).Finite →
      Summable (fun x => ‖bilin (fun n => w n *
        ((kernelI χ a J n - smooth φ N (kernelI χ a J) n : ℝ) : ℂ)) f g x‖) ∧
      ∑' x, ‖bilin (fun n => w n *
        ((kernelI χ a J n - smooth φ N (kernelI χ a J) n : ℝ) : ℂ)) f g x‖ ≤
        C * W * (N / 2 ^ a) * (l2norm f * l2norm g) := by
  obtain ⟨Cp, hCp0, hCp⟩ := hχ.exists_smoothing_bound φ hφ
  refine ⟨6 * Cp, by positivity, fun N a J w W f g hN hNa hw hf hg => ?_⟩
  have hW : 0 ≤ W := (norm_nonneg _).trans (hw 0)
  have hpt : ∀ n : ℤ, ‖w n * ((kernelI χ a J n - smooth φ N (kernelI χ a J) n : ℝ) : ℂ)‖ ≤
      W * ∑ k ∈ Finset.Icc a J, Cp * (N / 2 ^ k) * (1 / 2 ^ k) *
        ((1 + |(n : ℝ)| / 2 ^ k) ^ 10)⁻¹ := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hE : kernelI χ a J n - smooth φ N (kernelI χ a J) n =
        ∑ k ∈ Finset.Icc a J, (psiK χ k n - smooth φ N (psiK χ k) n) := by
      rw [smooth_kernelI φ hχ hN, kernelI, Finset.sum_sub_distrib]
    rw [hE]
    calc ‖w n‖ * |∑ k ∈ Finset.Icc a J, (psiK χ k n - smooth φ N (psiK χ k) n)|
        ≤ W * ∑ k ∈ Finset.Icc a J, |psiK χ k n - smooth φ N (psiK χ k) n| :=
          mul_le_mul (hw n) (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _) hW
      _ ≤ W * ∑ k ∈ Finset.Icc a J, Cp * (N / 2 ^ k) * (1 / 2 ^ k) *
            ((1 + |(n : ℝ)| / 2 ^ k) ^ 10)⁻¹ := by
          gcongr with k hk
          rw [abs_sub_comm]
          exact hCp N k n hN
            (hNa.trans (pow_le_pow_right₀ (by norm_num) (Finset.mem_Icc.1 hk).1))
  apply l1_bilin_le hf hg
  intro s
  calc ∑ n ∈ s, ‖w n * ((kernelI χ a J n - smooth φ N (kernelI χ a J) n : ℝ) : ℂ)‖
      ≤ ∑ n ∈ s, W * ∑ k ∈ Finset.Icc a J, Cp * (N / 2 ^ k) * (1 / 2 ^ k) *
          ((1 + |(n : ℝ)| / 2 ^ k) ^ 10)⁻¹ := Finset.sum_le_sum fun n _ => hpt n
    _ = W * ∑ k ∈ Finset.Icc a J, Cp * (N / 2 ^ k) * (1 / 2 ^ k) *
          ∑ n ∈ s, ((1 + |(n : ℝ)| / 2 ^ k) ^ 10)⁻¹ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
    _ ≤ W * ∑ k ∈ Finset.Icc a J, Cp * (N / 2 ^ k) * (1 / 2 ^ k) * (3 * 2 ^ k) := by
        gcongr with k hk
        exact sum_hfun_le (one_le_pow₀ (by norm_num)) s
    _ = W * (3 * Cp * N * ∑ k ∈ Finset.Icc a J, ((1 : ℝ) / 2) ^ k) := by
        refine congrArg (W * ·) ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [one_div_pow]
        have : (0 : ℝ) < 2 ^ k := by positivity
        field_simp
    _ ≤ W * (3 * Cp * N * (2 * ((1 : ℝ) / 2) ^ a)) := by
        gcongr
        exact sum_Icc_half_pow_le a J
    _ = 6 * Cp * W * (N / 2 ^ a) := by
        rw [one_div_pow]
        field_simp
        ring

end L1Final

end PrimeBHT.Kernel
