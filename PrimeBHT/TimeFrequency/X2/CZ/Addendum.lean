module

public import PrimeBHT.TimeFrequency.X2.CZ.CZExtend

/-!
# V08 ADDENDUM: Calderón-Zygmund operators with kernel `K(x, z)` on `L^q(ℝ; L^s(Y_P))`

The statement `VectorCZStatement` of `drafts/x2-interface/02b-V08-CZ-Addendum.lean.txt`, transcribed to the
namespace `PrimeBHT.TimeFrequency.X2.CZ` (definitions `IsCZKernel`, `kernelOp`, unchanged), and its proof
(`vectorCZStatement`, unconditional):

1. normalize `K̃ = K / A`; `IsCZKernel A K` and the scalar `L²` bound give a `CZPack K̃ 13 1`
   (`czPack_normalize`; the Hörmander integral condition from the pointwise bounds, `CZHormander.lean`);
2. strong `(q, s)` and weak `(1, 1)` on the class `𝒞` (`CZStrong.lean`: Marcinkiewicz, duality);
3. extension to bounded measurable `F` with finite `L^q(L^s)` norm (`CZExtend.lean`: Fatou along truncations).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology Real ComplexConjugate

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

open PrimeBHT.Statements

/-- A kernel with CZ constant `A`: size `|K(x,z)| ≤ A/|x - z|` and the two Hörmander-type smoothness bounds. -/
def IsCZKernel (A : ℝ) (K : ℝ → ℝ → ℂ) : Prop :=
  (∀ x z, x ≠ z → ‖K x z‖ ≤ A / |x - z|) ∧
    ∀ x x' z, 2 * |x - x'| ≤ |x - z| →
      ‖K x z - K x' z‖ + ‖K z x - K z x'‖ ≤ A * |x - x'| / |x - z| ^ 2

/-- The operator `F ↦ ∫ K(x,z) F(z) dz`, coordinatewise in `y`. -/
def kernelOp {P : ℕ} (K : ℝ → ℝ → ℂ) (F : ℝ → ZMod P → ℂ) : ℝ → ZMod P → ℂ :=
  fun x y => ∫ z, K x z * F z y

theorem IsCZKernel.nonneg {A : ℝ} {K : ℝ → ℝ → ℂ} (h : IsCZKernel A K) : 0 ≤ A := by
  have := h.1 1 0 one_ne_zero
  simp only [sub_zero, abs_one, div_one] at this
  exact (norm_nonneg _).trans this

theorem czBounds_normalize {A : ℝ} (hA : 0 < A) {K : ℝ → ℝ → ℂ} (hCZ : IsCZKernel A K) :
    CZBounds (fun x u => (A : ℂ)⁻¹ * K x u) ∧ CZBounds (adjKernel fun x u => (A : ℂ)⁻¹ * K x u) := by
  have hnormA : ‖(A : ℂ)⁻¹‖ = A⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
  have hsize : ∀ x u : ℝ, x ≠ u → ‖(A : ℂ)⁻¹ * K x u‖ ≤ 1 / |x - u| := by
    intro x u hxu
    rw [norm_mul, hnormA]
    have := hCZ.1 x u hxu
    calc A⁻¹ * ‖K x u‖ ≤ A⁻¹ * (A / |x - u|) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 1 / |x - u| := by field_simp
  -- the smoothness bounds in the two forms
  have hsm : ∀ x u c : ℝ, 2 * |u - c| ≤ |x - u| →
      ‖K u x - K c x‖ + ‖K x u - K x c‖ ≤ A * |u - c| / |x - u| ^ 2 := by
    intro x u c h
    have h' : 2 * |u - c| ≤ |u - x| := by rwa [abs_sub_comm u x]
    have := hCZ.2 u c x h'
    rwa [abs_sub_comm u x] at this
  refine ⟨⟨hsize, fun x u c h => ?_⟩, ⟨fun x u hxu => ?_, fun x u c h => ?_⟩⟩
  · have h1 := hsm x u c h
    rw [← mul_sub, norm_mul, hnormA]
    have h2 : ‖K x u - K x c‖ ≤ A * |u - c| / |x - u| ^ 2 :=
      (le_add_of_nonneg_left (norm_nonneg _)).trans h1
    calc A⁻¹ * ‖K x u - K x c‖ ≤ A⁻¹ * (A * |u - c| / |x - u| ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = |u - c| / |x - u| ^ 2 := by field_simp
  · simp only [adjKernel, Complex.norm_conj]
    have := hsize u x (Ne.symm hxu)
    rwa [abs_sub_comm u x] at this
  · have h1 := hsm x u c h
    simp only [adjKernel]
    rw [← map_sub, Complex.norm_conj, ← mul_sub, norm_mul, hnormA]
    have h2 : ‖K u x - K c x‖ ≤ A * |u - c| / |x - u| ^ 2 :=
      (le_add_of_nonneg_right (norm_nonneg _)).trans h1
    calc A⁻¹ * ‖K u x - K c x‖ ≤ A⁻¹ * (A * |u - c| / |x - u| ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = |u - c| / |x - u| ^ 2 := by field_simp

theorem kop_normalize {A : ℝ} {K : ℝ → ℝ → ℂ} (h : ℝ → ℂ) :
    kop (fun x u => (A : ℂ)⁻¹ * K x u) h = (A : ℂ)⁻¹ • fun x => ∫ z, K x z * h z := by
  ext x
  simp only [kop, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; ext u; ring

theorem kernelOp_eq_zero_of_zero {P : ℕ} {K : ℝ → ℝ → ℂ} (h : IsCZKernel 0 K) (F : ℝ → ZMod P → ℂ) :
    kernelOp K F = 0 := by
  ext x y
  unfold kernelOp
  refine integral_eq_zero_of_ae ?_
  have hne : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ x := by
    rw [ae_iff]; simp
  filter_upwards [hne] with z hz
  have := h.1 x z (Ne.symm hz)
  simp only [zero_div] at this
  have hK : K x z = 0 := norm_le_zero_iff.1 this
  simp [hK]

end PrimeBHT.TimeFrequency.X2.CZ
