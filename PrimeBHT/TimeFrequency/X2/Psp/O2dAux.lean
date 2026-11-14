module

public import PrimeBHT.TimeFrequency.X2.Psp.O2Close

/-!
# X2, V13 O2 (m): three small lemmas for the outside regime (requested by V13)

* `kernel_decay_layer`: the kernel `𝓕⁻ m` of a layer multiplier `m ∈ M_ω(𝔭)` of an overlapping slot decays like `(1 + 2^{-σ}|w|)^{-D}`;
* `measurable_dout`: `D_out` is measurable;
* `exists_Etil_near_endpoint`: every endpoint of `Ẽ_σ` is within `2^σ/2` of a point of `Ẽ_σ`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

theorem kernel_decay_layer {𝔭 : Params} {σ : ℤ} {c θ : ℝ} {m : ℝ → ℂ} (hm : InMult 𝔭 σ c m) (hβ : 𝔭.β ≤ 11 / 4)
    (hθ : |θ - c| ≤ 13 / 8 * (2 : ℝ) ^ (-σ)) (w : ℝ) :
    ‖𝓕⁻ m w‖ ≤ (2 ^ (𝔭.D + 1) * (2 * (3 * (2 : ℝ) ^ (-σ))) * 𝔭.C) * ((1 + (2 : ℝ) ^ (-σ) * |w|)⁻¹) ^ 𝔭.D := by
  have hsym := sym0_of_inMult hm hβ hθ
  have h1 := hsym.norm_ker_le w
  have hk : 𝓕⁻ m w = ovPhase θ w * 𝓕⁻ (fun ξ => m (ξ + θ)) w := by
    have := fourierInv_shift (fun ξ => m (ξ + θ)) θ w
    have e : (fun ξ => (fun ξ => m (ξ + θ)) (ξ - θ)) = m := funext fun ξ => by simp
    rw [e] at this
    exact this
  rw [hk, norm_mul, norm_ovPhase, one_mul]
  exact h1

section Dout

variable {P : ℕ} [NeZero P]

theorem measurable_dout {J : ℕ} {s₀ lo : ℤ} (TA : Finset TriTile) (W : ℤ × ℤ) (θ : ℝ) {F : ℝ → ZMod P → ℂ}
    (cL cR : ℤ → ℝ → ZMod P → ℂ) (σ : ℤ) (hF : Measurable F) :
    Measurable (fun z => Dout J s₀ lo TA W θ F cL cR σ z) := by
  unfold Dout
  refine Measurable.add ?_ ?_
  · refine Measurable.indicator ?_ (measurableSet_eTil TA W σ).compl
    exact (measurable_tmult_lowSym θ σ hF).sub (measurable_overlapPi TA W _ θ hF)
  · have hb := measurable_overlapBumps TA W ((ovScales J s₀ lo W.1).filter (fun τ => σ ≤ τ)) θ cL cR
    have e : (fun z => ∑ τ ∈ (ovScales J s₀ lo W.1).filter (fun τ => σ ≤ τ), bumpAt TA W θ cL cR τ z) =
        overlapBumps TA W ((ovScales J s₀ lo W.1).filter (fun τ => σ ≤ τ)) θ cL cR :=
      funext fun z => (overlapBumps_eq_sum _ _ _ _ _ _ z).symm
    rw [e]; exact hb

end Dout

theorem exists_Etil_near_endpoint {TA : Finset TriTile} {W : ℤ × ℤ} {σ : ℤ} {z : ℝ} (hz : z ∈ bdryEnds TA W σ) :
    ∃ x' ∈ eTil TA W σ, |x' - z| ≤ (2 : ℝ) ^ σ / 2 := by
  have hp := zpow_two_pos σ
  have hmem : ∀ v : ℤ, v ∈ eTilKeys TA W σ → ∀ y ∈ dyadicInt σ v, y ∈ eTil TA W σ := fun v hv y hy => by
    unfold eTil; exact Set.mem_biUnion hv hy
  rcases Finset.mem_union.1 hz with h1 | h1
  · obtain ⟨v, hv, -, rfl⟩ := mem_leftEndsOf.1 h1
    exact ⟨(2 : ℝ) ^ σ * v, hmem v (mem_eTilKeysF.1 hv) _ (mem_dyadicInt_left σ v), by simp; positivity⟩
  · obtain ⟨v, hv, -, rfl⟩ := mem_rightEndsOf.1 h1
    refine ⟨(2 : ℝ) ^ σ * ((v : ℝ) + 1 / 2), hmem v (mem_eTilKeysF.1 hv) _ ⟨by nlinarith, by nlinarith⟩, ?_⟩
    rw [abs_le]; constructor <;> nlinarith

end PrimeBHT.TimeFrequency.X2
