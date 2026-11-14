module

public import PrimeBHT.TimeFrequency.X2.Ortho.TileEng
public import PrimeBHT.TimeFrequency.X2.Ortho.Families
public import PrimeBHT.TimeFrequency.X2.Ortho.Geometry
public import PrimeBHT.TimeFrequency.X2.Ortho.Kernel
public import PrimeBHT.TimeFrequency.X2.Ortho.TreeToTile
public import PrimeBHT.TimeFrequency.X2.Ortho.TileDualsProof
import PrimeBHT.TimeFrequency.X2.Ortho.Level
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# X2, node V10: Hilbert orthogonality for strongly disjoint families of trees (`pint` at `s = qX = 2`)

## What is proved here

The corrected V10 statement (`pint_two`, the endpoint `s = 2`, `qX = 2` of the draft's `pint`; UNCONDITIONAL, proved):

  `∑_T |I_T| · topNorm(F; T; 2)² ≤ C (‖F‖₂² + (B² ∑_T |I_T|)^{1-α} ‖F‖₂^{2α})`,  `B ≥ ‖F‖_∞`, `0 < α < 1`,

in `ℝ≥0∞`, uniformly in `P`, for `k`-strongly disjoint families of `k`-lacunary trees of boxes of a rank-1 box set.
Both analytic inputs of the first version are now PROVED: `OrthoTreeToTile` (DPLMV `l:ortho0`; `ortho_tree_to_tile`,
`orthoTreeToTile_of_admissible`) and `OrthoTileBasic` (HLC `HilbertBasicEst`, tile form; `orthoTileBasic_of_admissible`);
`pint_two_of_tileBasic` is the reduction, `pint_two` the final statement.  The HLC argument is formalized as follows:

* the level argument of HLC `HilbertTileType` (L770-846): `Ortho/Level.lean` (`level_lemma`: basic estimate for all
  sub-collections `⟹` the `(1-α)`-form, `C_α = 6 K² (3 + 1/((1-α) log 2))`);
* the bookkeeping of strongly disjoint families (`Ortho/Families.lean`): inheritance of strong disjointness by
  sub-families `T ∩ 𝒬` with the same tops, disjointness of the tile sets of a strongly disjoint family;
* the single-tile energy `tileEng` (the tree norm of the one-tile tree) and its bound `tileEng ≤ C ‖F‖_∞`
  (DPLMV (e:sscaleentv)) from `norm_singleTile_le` (`Ortho/TileEng.lean`), including measurability of `T_m F`;
* the combinatorics of the nested part `S_2` of the TT* argument (`Ortho/Geometry.lean`): for tiles `R'` with a
  larger-or-equal frequency interval `3`-close to `ω_{R₀}`, `I_{R'}` is disjoint from the top of the tree of `R₀`
  (`IsStronglyDisjoint.disjoint_top`) and has multiplicity `≤ 2` (`no_three_close`: HLC's multiplicity `1` becomes
  `2` because the frequency supports are `3ω`, not `ω`; a lacunary tree may carry `ω', ω''` on both sides of `ω_{R₀}`);
* kernel decay of every order `M ≤ D` of the class multipliers (`Ortho/Kernel.lean`:
  `‖𝓕⁻ m w‖ ≤ 2^{M+1} β C l (1 + l|w|)^{-M}`; `ClassKernel` has `M = 2` only, too weak for the Peetre factors);
* the translation of the ENNReal statements to the real-number level lemma and back (this file).

## The proved reduction `OrthoTreeToTile` and the remaining hypothesis

* `OrthoTreeToTile 𝔭` (DPLMV `l:ortho0`, operator form; PROVED in `Ortho/{Fourier,TreeScalar,TreeToTile}.lean`): for a `k`-lacunary tree `T` with top `t` of rank-1 boxes,
  `|I_t| topNorm 𝔭 (F; T; 2)² ≤ K ∑_{R∈T} |I_R| tileEng_{𝔭'}(R)²`, `𝔭' = 𝔭.decN 10` (the weights `u_R^{-1} = (1+t²)^5`
  cost 10 orders of decay).  Proof as implemented: `𝓕(ψ_R · 𝓕⁻m_R * f)` vanishes off `[c ± (β/2+δ) l]` (Fubini and the definition of `𝓕⁻ m`),
  so pieces with disjoint `3ω` are `L²`-orthogonal (X1's `pairing_eq_zero_of_fourier_Icc`); same-box cross terms use
  `|g_R||g_{R'}| = u_R u_{R'} |h_R||h_{R'}|`, `u = (1+t²)⁻¹`, `u_R u_{R'} ≤ 2(1+n²)⁻¹`, `h_R = ψ̃_R T_{m_R} f`,
  `ψ̃_R = (1+t²)ψ_R` (class `decN 2 ⊂ decN 10`).  **Needs `β + 2δ ≤ 3`** (stated `< 3`): otherwise the Fourier supports of
  `ψ_R T_{m_R}F` of different frequency intervals of a lacunary tree may overlap.  The constant is `2 ∑_n (1+n²)⁻¹`.
* `OrthoTileBasic 𝔭'` (PROVED, `orthoTileBasic_of_admissible`; HLC Proposition `HilbertBasicEst`, tile form): for a strongly disjoint family with
  single-tile energies `≤ μ`, `∑_R |I_R| tileEng(R)² ≤ K (‖F‖² + (μ² Λ)^{1/3} ‖F‖^{4/3})`, `Λ = ∑_T|I_T|` or `∑_R|I_R|`.
  Proof plan: choose near-optimal `(ψ_R, m_R)` per tile, `z_R = T_{m̄_R}(ψ̄_R ψ_R T_{m_R} F)`; `⟨z_R, F⟩ = |I_R| ĉ_R²`,
  `|z_R(x)|_Y ≤ K ĉ_R ⟨(x-c_R)/|I_R|⟩^{-M}` (Cauchy-Schwarz with the kernel `𝓕⁻ m_R`), `z_R ⊥ z_{R'}` if
  `3ω_R ∩ 3ω_{R'} = ∅`; same-frequency block by translation decay, nested block by strong disjointness; closing algebra.

## Corrections of the draft `pint` (all forced)

1. `α < 1` (not `0 < α ≤ 1`): at `α = 1` the statement is the Bessel inequality without loss, false for Fourier tiles
   (HLC Prop `HilbertTileType`: the constant is `∼ (1-α)^{-1/2}`).  V12 only needs `α = qX/q < 1`.
2. `β + 2δ < 3` is needed (see above), not implied by `Params.Admissible` (`β ≤ 3`).
3. The internal class is `𝔭.decN 10` (decay lowered by 10): `(𝔭.decN 10).Admissible` is a hypothesis.
4. `topNorm` over trees with the TOP FIXED (X2-I1), as in the draft.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- **Hypothesis (DPLMV `l:ortho0`, operator form)**: the squared norm of a tree operator with fixed top is bounded
by the sum of the squared single-tile energies (in the class with 10 fewer orders of decay).  Only claimed for
`β + 2 δ < 3` (see the module doc). -/
def OrthoTreeToTile (𝔭 : Params) : Prop :=
  𝔭.β + 2 * 𝔭.δ < 3 →
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (P : ℕ) [NeZero P] (Qs : Set Box), IsRankOne 𝔭.J Qs →
    ∀ (k : Fin 3) (T : Finset TriTile) (t : Top), IsTree T t → IsLacunary k T →
      (∀ R ∈ T, R.box ∈ Qs) → ∀ (F : ℝ → ZMod P → ℂ) (B : ℝ), Measurable F →
        (∀ x, yNorm 2 (F x) ≤ B) →
          ENNReal.ofReal ((2 : ℝ) ^ t.1.1) * topNorm 𝔭 2 k F T t 2 ^ (2 : ℝ) ≤
            ENNReal.ofReal K * ∑ R ∈ T, ENNReal.ofReal ((2 : ℝ) ^ R.box.scale) *
              tileEng (𝔭.decN 10) k F R ^ (2 : ℝ)

/-- `OrthoTreeToTile` is a THEOREM for admissible `𝔭` (`Ortho/TreeToTile.lean`). -/
theorem orthoTreeToTile_of_admissible {𝔭 : Params} (h𝔭 : 𝔭.Admissible) : OrthoTreeToTile 𝔭 :=
  fun hβ => ortho_tree_to_tile 𝔭 h𝔭 hβ

/-! ### ENNReal bookkeeping -/

theorem toReal_basic {S F2e Λ : ℝ≥0∞} {K μ : ℝ} (hK : 0 ≤ K) (hF : F2e ≠ ⊤) (hΛ : Λ ≠ ⊤)
    (h : S ≤ ENNReal.ofReal K * (F2e + (ENNReal.ofReal (μ ^ 2) * Λ) ^ ((1 : ℝ) / 3) *
      F2e ^ ((2 : ℝ) / 3))) :
    S.toReal ≤ K * (F2e.toReal + (μ ^ 2 * Λ.toReal) ^ ((1 : ℝ) / 3) * F2e.toReal ^ ((2 : ℝ) / 3)) := by
  have h1 : (ENNReal.ofReal (μ ^ 2) * Λ) ^ ((1 : ℝ) / 3) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΛ)
  have h2 : F2e ^ ((2 : ℝ) / 3) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hF
  have hfin : ENNReal.ofReal K * (F2e + (ENNReal.ofReal (μ ^ 2) * Λ) ^ ((1 : ℝ) / 3) *
      F2e ^ ((2 : ℝ) / 3)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨hF, ENNReal.mul_ne_top h1 h2⟩)
  refine (ENNReal.toReal_mono hfin h).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK, ENNReal.toReal_add hF (ENNReal.mul_ne_top h1 h2),
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg μ)]

theorem ofReal_mul_ofReal_rpow_two {ℓ c : ℝ} (hℓ : 0 ≤ ℓ) (hc : 0 ≤ c) :
    ENNReal.ofReal ℓ * ENNReal.ofReal c ^ (2 : ℝ) = ENNReal.ofReal (ℓ * c ^ 2) := by
  rw [ENNReal.ofReal_rpow_of_nonneg hc (by norm_num), Real.rpow_two, ← ENNReal.ofReal_mul hℓ]

theorem topSum_pos {𝒯 : List (Finset TriTile × Top)} (h : 𝒯 ≠ []) : 0 < topSum 𝒯 := by
  cases 𝒯 with
  | nil => exact absurd rfl h
  | cons T 𝒯 =>
    rw [topSum_cons]
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 (zpow_pos (by norm_num) _)) le_self_add

/-! ### The reduction -/

/-- `β + 2δ < 3` follows from admissibility (`β ≤ 11/4`, `δ ≤ 2^{-3J/2}`, `J ≥ 16`). -/
theorem Params.Admissible.beta_delta {𝔭 : Params} (h : 𝔭.Admissible) : 𝔭.β + 2 * 𝔭.δ < 3 := by
  obtain ⟨hJ, -, -, -, hδ, -, hβ, -⟩ := h
  have hJ16 : (16 : ℝ) ≤ 𝔭.J := by
    have : (16 : ℕ) ≤ 𝔭.J := by have : jFloor = 16 := rfl; omega
    exact_mod_cast this
  have h1 : (2 : ℝ) ^ (-(3 * (𝔭.J : ℝ) / 2)) ≤ (2 : ℝ) ^ (-(4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h2 : (2 : ℝ) ^ (-(4 : ℝ)) = 1 / 16 := by
    rw [Real.rpow_neg (by norm_num), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  linarith

end PrimeBHT.TimeFrequency.X2
