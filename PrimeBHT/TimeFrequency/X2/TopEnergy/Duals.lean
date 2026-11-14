module

public import PrimeBHT.TimeFrequency.X2.TopEnergy.Bessel
public import PrimeBHT.TimeFrequency.X2.Ortho.DualsVec
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Fourier.Convolution

/-!
# X2, node V12-top (TB-5, Layer B): the dual vectors of top operators

The dual-vector machinery of V10 (`Ortho/Duals.lean`, `Ortho/DualsVec.lean`) is generic in the class `InPsi 𝔭 s v ψ`,
`InMult 𝔭 s c m`.  A (one-sided) top multiplier is a multiplier of the class with `β = 12` centred in the middle of its
shell; its Fourier support is an interval `[lo, hi]` (the shell).  Here:

* `fourier_dual_eq_zero'`, `dual_orthogonal'`, `vz_orth'`: orthogonality of the duals of two multipliers whose
  supports lie in intervals `[lo, hi]`, `[lo', hi']` with disjoint `Ico`'s (V10 has the case `3ω ∩ 3ω' = ∅`);
* `topDualFam`: the family `DualFam` (Layer A) of the dual vectors `z_i = vz ψ_i m_i F` of indices `i` with data
  `(W_i, ψ_i, m_i)`, lengths `ℓ_i = 2^{W_i.1}`, centres `c_{W_i}`, amplitudes `a_i = ‖ψ_i T_{m_i} F‖_{L²(ℝ;L²(Y))}`,
  and `Ov i j ↔ [lo_i, hi_i] ∩ [lo_j, hi_j] ≠ ∅`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform ComplexConjugate ContDiff Real
open PrimeBHT.TimeFrequency.Tile PrimeBHT.Statements

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

section Orth

variable {𝔭 : Params} {s v : ℤ} {c : ℝ} {ψ m f : ℝ → ℂ}

/-- The Fourier transform of the dual vanishes wherever the multiplier does. -/
theorem fourier_dual_eq_zero' (hN : 2 ≤ 𝔭.N) (hD : 2 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ)
    (hm : InMult 𝔭 s c m) (hf : Measurable f) {B : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) (ζ : ℝ) (hζ : m ζ = 0) :
    𝓕 (dual ψ m f) ζ = 0 := by
  rw [dual_eq_conv, Real.fourier_mul_convolution_eq (integrable_Kdag hD hβ hm)
    (integrable_uu hN hD hβ hψ hm hf hB), fourier_Kdag hD hβ hm, hζ]
  simp

/-- Orthogonality of two duals with supports in intervals with disjoint `Ico`'s. -/
theorem dual_orthogonal' {s' v' : ℤ} {c' : ℝ} {ψ' m' f' : ℝ → ℂ} (hN : 2 ≤ 𝔭.N) (hD : 2 ≤ 𝔭.D)
    (hβ : 0 ≤ 𝔭.β) (hψ : InPsi 𝔭 s v ψ) (hψ' : InPsi 𝔭 s' v' ψ')
    (hm : InMult 𝔭 s c m) (hm' : InMult 𝔭 s' c' m') (hf : Measurable f) (hf' : Measurable f')
    {B B' : ℝ} (hB : ∀ z, ‖f z‖ ≤ B) (hB' : ∀ z, ‖f' z‖ ≤ B') {lo hi lo' hi' : ℝ}
    (hsupp : ∀ ζ, ζ ∉ Icc lo hi → m ζ = 0) (hsupp' : ∀ ζ, ζ ∉ Icc lo' hi' → m' ζ = 0)
    (hdisj : Disjoint (Ico lo hi) (Ico lo' hi')) :
    ∫ x, dual ψ m f x * (starRingEnd ℂ) (dual ψ' m' f' x) = 0 :=
  pairing_eq_zero_of_fourier_Icc (u := dual ψ m f) (v := dual ψ' m' f')
    (integrable_dual hN hD hβ hψ hm hf hB) (continuous_dual hD hβ hψ' hm' hf' hB')
    (integrable_dual hN hD hβ hψ' hm' hf' hB') (a := lo) (b := hi) (a' := lo') (b' := hi')
    (fun ξ hξ => fourier_dual_eq_zero' hN hD hβ hψ hm hf hB ξ (hsupp ξ hξ))
    (fun ξ hξ => fourier_dual_eq_zero' hN hD hβ hψ' hm' hf' hB' ξ (hsupp' ξ hξ)) hdisj

variable {P : ℕ} [NeZero P] {F : ℝ → ZMod P → ℂ}

/-- Vector version of `dual_orthogonal'`. -/
theorem vz_orth' {s' v' : ℤ} {c' : ℝ} {ψ' m' : ℝ → ℂ} (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β)
    (hψ : InPsi 𝔭 s v ψ) (hψ' : InPsi 𝔭 s' v' ψ') (hm : InMult 𝔭 s c m) (hm' : InMult 𝔭 s' c' m')
    (hF : Measurable F) {B : ℝ} (hB : ∀ x, yNorm 2 (F x) ≤ B) {lo hi lo' hi' : ℝ}
    (hsupp : ∀ ζ, ζ ∉ Icc lo hi → m ζ = 0) (hsupp' : ∀ ζ, ζ ∉ Icc lo' hi' → m' ζ = 0)
    (hdisj : Disjoint (Ico lo hi) (Ico lo' hi')) :
    ∫ x, yInner (vz ψ m F x) (vz ψ' m' F x) = 0 := by
  have hint : ∀ y : ZMod P, Integrable (fun x => dual ψ m (fun z => F z y) x *
      (starRingEnd ℂ) (dual ψ' m' (fun z => F z y) x)) := by
    intro y
    have h1 := integrable_dual (by omega) (by omega) hβ hψ hm (measurable_coord hF y) (coord_bound hF hB y)
    obtain ⟨M, hM⟩ := dual_bdd hN hD hβ hψ' hm' (measurable_coord hF y) (coord_bound hF hB y)
    have hc' := continuous_dual (by omega) hβ hψ' hm' (measurable_coord hF y) (coord_bound hF hB y)
    have := h1.bdd_mul (f := fun x => (starRingEnd ℂ) (dual ψ' m' (fun z => F z y) x)) (c := M)
      (Complex.continuous_conj.measurable.comp hc'.measurable).aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Complex.norm_conj]; exact hM x)
    exact this.congr (Eventually.of_forall fun x => mul_comm _ _)
  have e1 : ∀ x, yInner (vz ψ m F x) (vz ψ' m' F x) =
      (P : ℂ)⁻¹ * ∑ y : ZMod P, dual ψ m (fun z => F z y) x *
        (starRingEnd ℂ) (dual ψ' m' (fun z => F z y) x) := by
    intro x; rfl
  simp_rw [e1]
  rw [integral_const_mul, integral_finsetSum _ fun y _ => hint y]
  have e2 : ∀ y : ZMod P, ∫ x, dual ψ m (fun z => F z y) x *
      (starRingEnd ℂ) (dual ψ' m' (fun z => F z y) x) = 0 := fun y =>
    dual_orthogonal' (by omega) (by omega) hβ hψ hψ' hm hm' (measurable_coord hF y)
      (measurable_coord hF y) (coord_bound hF hB y) (coord_bound hF hB y) hsupp hsupp' hdisj
  simp_rw [e2]
  simp

end Orth

section Fam

variable {P : ℕ} [NeZero P] {ι : Type*} {F : ℝ → ZMod P → ℂ}

/-- **The dual family of indices with data `(W_i, ψ_i, m_i)`**: `ℓ_i = 2^{W_i.1}`, centre `c_{W_i}`, `a_i = va ψ_i m_i F`,
`z_i = vz ψ_i m_i F`, overlap of the closed intervals `[lo_i, up_i]` (the Fourier supports of `m_i`). -/
theorem topDualFam {𝔭 : Params} (𝒮 : Finset ι) (W : ι → ℤ × ℤ) (c lo up : ι → ℝ) (ψ m : ι → ℝ → ℂ)
    (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) (hβ : 0 ≤ 𝔭.β)
    (hψ : ∀ i ∈ 𝒮, InPsi 𝔭 (W i).1 (W i).2 (ψ i)) (hm : ∀ i ∈ 𝒮, InMult 𝔭 (W i).1 (c i) (m i))
    (hsupp : ∀ i ∈ 𝒮, ∀ ζ, ζ ∉ Icc (lo i) (up i) → m i ζ = 0)
    (hF : Measurable F) {B : ℝ} (hB : ∀ x, yNorm 2 (F x) ≤ B) :
    DualFam F 𝒮 (2 ^ 13 * 𝔭.β * 𝔭.C * 𝔭.C) (fun i => (2 : ℝ) ^ (W i).1)
      (fun i => dyCentre (W i).1 (W i).2) (fun i => va (ψ i) (m i) F) (fun i => vz (ψ i) (m i) F)
      (fun i j => (Icc (lo i) (up i) ∩ Icc (lo j) (up j)).Nonempty) where
  pos := fun i _ => zpow_pos (by norm_num) _
  nonneg := fun i _ => va_nonneg _ _ _
  meas := fun i hi => measurable_vz (by omega) hβ (hψ i hi) (hm i hi) hF hB
  inner_F := fun i hi => vz_inner_F hN hD hβ (hψ i hi) (hm i hi) hF hB
  bound := fun i hi x => vz_bound hN hD hβ (hψ i hi) (hm i hi) hF hB x
  orth := fun i hi j hj hnc => by
    have hdis : Disjoint (Icc (lo i) (up i)) (Icc (lo j) (up j)) :=
      Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hnc)
    have hdis' : Disjoint (Ico (lo i) (up i)) (Ico (lo j) (up j)) :=
      Set.disjoint_of_subset Set.Ico_subset_Icc_self Set.Ico_subset_Icc_self hdis
    exact vz_orth' hN hD hβ (hψ i hi) (hψ j hj) (hm i hi) (hm j hj) hF hB (hsupp i hi) (hsupp j hj) hdis'

end Fam

end PrimeBHT.TimeFrequency.X2
