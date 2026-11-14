module

public import PrimeBHT.TimeFrequency.X2.Psp.LacunaryLinf
public import PrimeBHT.TimeFrequency.X2.Psp.TreeConv

/-!
# X2, V13 O2 (l): decay of the layer cutoff `χ̃_σ` away from the tile centres

`layerCut_decay_off`: if every tile centre of the layer `σ` is at distance `≥ δ` from `x`, then
`χ̃_σ(x) ≤ K (4 jbConst 2) (1 + δ/2^σ)^{-(N-2)}` (`χ̃_σ(x) ≤ K Σ_R ⟨(x - c_R)/2^σ⟩^{-N}` and the lattice sum of `⟨·⟩^{-2}`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

theorem layerCut_decay_off {𝔭 : Params} {η : ℝ → ℝ} (hη : IsEtaCut 𝔭 η) (h2 : 2 ≤ 𝔭.N) {TA : Finset TriTile}
    (hb : ∀ R ∈ TA, ∀ R' ∈ TA, R.box.scale = R'.box.scale → R.box = R'.box) (σ : ℤ) {x δ : ℝ} (hδ : 0 ≤ δ)
    (hx : ∀ R ∈ layer' TA σ, δ ≤ |x - dyCentre σ R.pos|) :
    layerCut η TA σ x ≤ cutK 𝔭 * (2 ^ 2 * jbConst 2) * (1 + δ / 2 ^ σ) ^ (-((𝔭.N : ℝ) - 2)) := by
  have hp := zpow_two_pos σ
  have hN2 : (2 : ℝ) ≤ 𝔭.N := by exact_mod_cast h2
  have hC : 0 ≤ 𝔭.C := by
    have h1 : 0 ≤ η 0 := hη.2.1 0
    have h3 := hη.2.2.2.1 0
    have h5 : 0 < jb 0 ^ (-(𝔭.N : ℝ)) := Real.rpow_pos_of_pos (jb_pos 0) _
    exact nonneg_of_mul_nonneg_left (h1.trans h3) h5
  have hK : 0 ≤ cutK 𝔭 := by unfold cutK; positivity
  have hlc := layerCut_le hη TA σ x
  set A : ℝ := 1 + δ / (2 : ℝ) ^ σ with hA
  have hA1 : 1 ≤ A := by have : 0 ≤ δ / (2 : ℝ) ^ σ := by positivity
                         linarith
  have hA0 : 0 < A := by linarith
  have hpt : ∀ R ∈ layer' TA σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-(𝔭.N : ℝ)) ≤
      jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-(2 : ℝ)) * A ^ (-((𝔭.N : ℝ) - 2)) := by
    intro R hR
    set j := jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) with hj
    have hj0 : 0 < j := jb_pos _
    have hjA : A ≤ j := by
      rw [hA, hj]; unfold jb
      rw [abs_div, abs_of_pos hp]
      have := div_le_div_of_nonneg_right (hx R hR) hp.le
      linarith
    have e : j ^ (-(𝔭.N : ℝ)) = j ^ (-(2 : ℝ)) * j ^ (-((𝔭.N : ℝ) - 2)) := by
      rw [← Real.rpow_add hj0]; congr 1; ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hj0.le _)
    exact Real.rpow_le_rpow_of_nonpos hA0 hjA (by linarith)
  have hsum : ∑ R ∈ layer' TA σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-(2 : ℝ)) ≤
      (2 : ℝ) ^ (2 : ℝ) * jbConst 2 := by
    have := sum_layer'_eq_sum_keys (Tr := TA) hb σ (fun v => jb ((x - dyCentre σ v) / (2 : ℝ) ^ σ) ^ (-(2 : ℝ)))
    rw [this]
    have e : ∀ v : ℤ, (x - dyCentre σ v) / (2 : ℝ) ^ σ = (x / (2 : ℝ) ^ σ - 1 / 2) - v := by
      intro v; unfold dyCentre; field_simp; ring
    simp_rw [e]
    exact sum_jb_le (by norm_num : (1 : ℝ) < 2) _ _
  have hr : (2 : ℝ) ^ (2 : ℝ) = 2 ^ 2 := by norm_num
  rw [hr] at hsum
  have hA' : 0 ≤ A ^ (-((𝔭.N : ℝ) - 2)) := Real.rpow_nonneg hA0.le _
  calc layerCut η TA σ x ≤ cutK 𝔭 * ∑ R ∈ layer' TA σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-(𝔭.N : ℝ)) := hlc
    _ ≤ cutK 𝔭 * ∑ R ∈ layer' TA σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-(2 : ℝ)) * A ^ (-((𝔭.N : ℝ) - 2)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) hK
    _ = cutK 𝔭 * ((∑ R ∈ layer' TA σ, jb ((x - dyCentre σ R.pos) / (2 : ℝ) ^ σ) ^ (-(2 : ℝ))) *
          A ^ (-((𝔭.N : ℝ) - 2))) := by rw [← Finset.sum_mul]
    _ ≤ cutK 𝔭 * ((2 ^ 2 * jbConst 2) * A ^ (-((𝔭.N : ℝ) - 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsum hA') hK
    _ = _ := by ring

end PrimeBHT.TimeFrequency.X2
