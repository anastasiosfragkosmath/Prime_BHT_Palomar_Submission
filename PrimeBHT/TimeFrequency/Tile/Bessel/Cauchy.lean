module

public import PrimeBHT.Frozen.Pairing
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# A Bessel-type inequality from the Gram matrix (blueprint C4, step 2)

For finitely many `u_i ∈ L²` and `f ∈ L²` put `c_i = ⟨f, u_i⟩`. Then

`(∑ |c_i|²)² ≤ ‖f‖₂² · ∑_i ∑_j |c_i| |c_j| |⟨u_i, u_j⟩|`

(`sq_sum_norm_pairing_le`): `∑ |c_i|² = ⟨f, F⟩` for `F = ∑ c_i u_i`, Cauchy-Schwarz, and
`‖F‖₂² = ∑_i ∑_j c_i \bar c_j ⟨u_i, u_j⟩`. Self-contained (no tile definitions).
-/

public section

open MeasureTheory
open PrimeBHT.Statements

namespace PrimeBHT.TimeFrequency.Tile.Bessel

/-- Cauchy-Schwarz for real functions, by the discriminant of `∫ (g - s h)² ≥ 0`. -/
theorem integral_mul_sq_le {g h : ℝ → ℝ} (hg : Integrable (fun x => g x ^ 2))
    (hh : Integrable (fun x => h x ^ 2)) (hgh : Integrable (fun x => g x * h x)) :
    (∫ x, g x * h x) ^ 2 ≤ (∫ x, g x ^ 2) * (∫ x, h x ^ 2) := by
  have key : ∀ s : ℝ, 0 ≤ (∫ x, h x ^ 2) * (s * s) + (-2 * ∫ x, g x * h x) * s + ∫ x, g x ^ 2 := by
    intro s
    have h1 : ∫ x, (g x - s * h x) ^ 2 =
        (∫ x, g x ^ 2) - 2 * s * (∫ x, g x * h x) + s ^ 2 * (∫ x, h x ^ 2) := by
      have : ∀ x, (g x - s * h x) ^ 2 = g x ^ 2 - 2 * s * (g x * h x) + s ^ 2 * h x ^ 2 :=
        fun x => by ring
      have i1 : Integrable (fun x => 2 * s * (g x * h x)) := hgh.const_mul _
      have i2 : Integrable (fun x => s ^ 2 * h x ^ 2) := hh.const_mul _
      have i3 : Integrable (fun x => g x ^ 2 - 2 * s * (g x * h x)) := hg.sub i1
      simp_rw [this]
      rw [integral_add i3 i2, integral_sub hg i1, integral_const_mul (2 * s),
        integral_const_mul (s ^ 2)]
    have h2 : 0 ≤ ∫ x, (g x - s * h x) ^ 2 := integral_nonneg fun x => sq_nonneg _
    have h3 : (∫ x, h x ^ 2) * (s * s) + (-2 * ∫ x, g x * h x) * s + ∫ x, g x ^ 2 =
        ∫ x, (g x - s * h x) ^ 2 := by linarith [h1]
    rw [h3]
    exact h2
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

theorem integrable_mul_conj' {f g : ℝ → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) :
    Integrable (fun x => f x * (starRingEnd ℂ) (g x)) :=
  hf.integrable_mul hg.star

theorem ofReal_norm_sq_eq_mul_conj' (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- `⟨f, g⟩` is conjugate-symmetric in norm. -/
theorem norm_pairing_comm (f g : ℝ → ℂ) : ‖pairing f g‖ = ‖pairing g f‖ := by
  have h : pairing f g = (starRingEnd ℂ) (pairing g f) := by
    unfold pairing
    rw [← integral_conj]
    congr 1
    funext x
    simp [mul_comm]
  rw [h, Complex.norm_conj]

/-- `|⟨f, g⟩| ≤ ‖f‖₂ ‖g‖₂` squared. -/
theorem norm_pairing_sq_le {f g : ℝ → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) :
    ‖pairing f g‖ ^ 2 ≤ (∫ x, ‖f x‖ ^ 2) * ∫ x, ‖g x‖ ^ 2 := by
  have hf2 : Integrable (fun x => ‖f x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hg2 : Integrable (fun x => ‖g x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  have hfg : Integrable (fun x => ‖f x‖ * ‖g x‖) := hf.norm.integrable_mul hg.norm
  have h1 : ‖pairing f g‖ ≤ ∫ x, ‖f x‖ * ‖g x‖ := by
    unfold pairing
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext x
    rw [norm_mul, Complex.norm_conj]
  have h2 := integral_mul_sq_le hf2 hg2 hfg
  have h3 : ‖pairing f g‖ ^ 2 ≤ (∫ x, ‖f x‖ * ‖g x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  exact h3.trans h2

/-- `∫ ‖∑ c_i u_i‖² = ∑_i ∑_j c_i \bar c_j ⟨u_i, u_j⟩`. -/
theorem integral_norm_sq_sum_eq {ι : Type*} (T : Finset ι) (u : ι → ℝ → ℂ) (c : ι → ℂ)
    (hu : ∀ i ∈ T, MemLp (u i) 2) :
    ((∫ x, ‖∑ i ∈ T, c i * u i x‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ T, ∑ j ∈ T, c i * (starRingEnd ℂ) (c j) * pairing (u i) (u j) := by
  have hint : ∀ i ∈ T, ∀ j ∈ T, Integrable (fun x => u i x * (starRingEnd ℂ) (u j x)) :=
    fun i hi j hj => integrable_mul_conj' (hu i hi) (hu j hj)
  calc ((∫ x, ‖∑ i ∈ T, c i * u i x‖ ^ 2 : ℝ) : ℂ)
      = ∫ x, ∑ i ∈ T, ∑ j ∈ T,
          c i * (starRingEnd ℂ) (c j) * (u i x * (starRingEnd ℂ) (u j x)) := by
        rw [← integral_complex_ofReal]
        congr 1
        funext x
        rw [ofReal_norm_sq_eq_mul_conj', map_sum, Finset.sum_mul_sum]
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

/-- `⟨f, ∑ c_i u_i⟩ = ∑ \bar c_i ⟨f, u_i⟩`. -/
theorem pairing_sum_right {ι : Type*} (T : Finset ι) (u : ι → ℝ → ℂ) (c : ι → ℂ) {f : ℝ → ℂ}
    (hf : MemLp f 2) (hu : ∀ i ∈ T, MemLp (u i) 2) :
    pairing f (fun x => ∑ i ∈ T, c i * u i x) =
      ∑ i ∈ T, (starRingEnd ℂ) (c i) * pairing f (u i) := by
  unfold pairing
  have hint : ∀ i ∈ T, Integrable (fun x => f x * (starRingEnd ℂ) (u i x)) :=
    fun i hi => integrable_mul_conj' hf (hu i hi)
  calc ∫ x, f x * (starRingEnd ℂ) (∑ i ∈ T, c i * u i x)
      = ∫ x, ∑ i ∈ T, (starRingEnd ℂ) (c i) * (f x * (starRingEnd ℂ) (u i x)) := by
        congr 1
        funext x
        rw [map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        ring
    _ = ∑ i ∈ T, (starRingEnd ℂ) (c i) * ∫ x, f x * (starRingEnd ℂ) (u i x) := by
        rw [integral_finsetSum _ (fun i hi => (hint i hi).const_mul _)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_const_mul]

/-- **Bessel from the Gram matrix.** With `c_i = ⟨f, u_i⟩`:
`(∑ |c_i|²)² ≤ ‖f‖₂² ∑_i ∑_j |c_i| |c_j| |⟨u_i, u_j⟩|`. -/
theorem sq_sum_norm_pairing_le {ι : Type*} (T : Finset ι) (u : ι → ℝ → ℂ) {f : ℝ → ℂ}
    (hf : MemLp f 2) (hu : ∀ i ∈ T, MemLp (u i) 2) :
    (∑ i ∈ T, ‖pairing f (u i)‖ ^ 2) ^ 2 ≤ (∫ x, ‖f x‖ ^ 2) *
      ∑ i ∈ T, ∑ j ∈ T, ‖pairing f (u i)‖ * ‖pairing f (u j)‖ * ‖pairing (u i) (u j)‖ := by
  set c : ι → ℂ := fun i => pairing f (u i) with hc
  set F : ℝ → ℂ := fun x => ∑ i ∈ T, c i * u i x with hF
  have hFmem : MemLp F 2 :=
    memLp_finsetSum T (f := fun i x => c i * u i x) fun i hi => (hu i hi).const_mul (c i)
  -- `⟨f, F⟩ = ∑ |c_i|²`
  have hfF : pairing f F = ((∑ i ∈ T, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [hF, pairing_sum_right T u c hf hu, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ofReal_norm_sq_eq_mul_conj', mul_comm]
  have hS : ‖pairing f F‖ = ∑ i ∈ T, ‖c i‖ ^ 2 := by
    rw [hfF, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => by positivity)]
  -- `‖F‖₂²`
  have hFF : ∫ x, ‖F x‖ ^ 2 ≤
      ∑ i ∈ T, ∑ j ∈ T, ‖c i‖ * ‖c j‖ * ‖pairing (u i) (u j)‖ := by
    have h := integral_norm_sq_sum_eq T u c hu
    have h2 : ∫ x, ‖F x‖ ^ 2 =
        ‖∑ i ∈ T, ∑ j ∈ T, c i * (starRingEnd ℂ) (c j) * pairing (u i) (u j)‖ := by
      rw [← h, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun x => by positivity)]
    rw [h2]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_conj]
  have hcs := norm_pairing_sq_le hf hFmem
  rw [hS] at hcs
  calc (∑ i ∈ T, ‖pairing f (u i)‖ ^ 2) ^ 2 ≤ (∫ x, ‖f x‖ ^ 2) * ∫ x, ‖F x‖ ^ 2 := hcs
    _ ≤ _ := mul_le_mul_of_nonneg_left hFF (integral_nonneg fun x => by positivity)

end PrimeBHT.TimeFrequency.Tile.Bessel
