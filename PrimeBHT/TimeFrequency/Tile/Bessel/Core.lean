module

public import PrimeBHT.TimeFrequency.Tile.Bessel.Claim
public import PrimeBHT.TimeFrequency.Tile.Bessel.Algebra
public import PrimeBHT.TimeFrequency.Tile.Bessel.Cauchy
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The weak Bessel inequality with an energy upper bound (blueprint C4, steps 2-6)

Under the extra assumption `∑_{t ∈ T} |a_t|² ≤ 2 μ² |I_T|` (`a_t = ⟨f, φ_{t,k}⟩`) and the tile bound with
`μ`: `∑_T |I_T| ≤ coreConst N ‖f‖₂² / μ²` (`coreBound`).
-/

@[expose] public section

open MeasureTheory
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Tile

/-- The constant of `coreBound`: `4 (2 C₃ + 4 + 2 C₄)`, `C₃` the (G3) constant and `C₄` the claim
constant. -/
noncomputable def coreConst (N : ℕ) : ℝ := 4 * (2 * sameScaleConst N + 4 + 2 * claimConst N)

theorem sameScaleConst_nonneg {N : ℕ} (hN : 3 ≤ N) : 0 ≤ sameScaleConst N := by
  unfold sameScaleConst
  exact mul_nonneg (gramConst_nonneg (by omega)) (tsum_nonneg fun j => by positivity)

theorem claimConst_nonneg {N : ℕ} (hN : 3 ≤ N) : 0 ≤ claimConst N := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : 0 < 2 * ((N : ℝ) - 2) - 1 := by linarith
  have h2 : 0 < 2 * ((N : ℝ) - 2) := by linarith
  unfold claimConst
  positivity

theorem coreConst_nonneg {N : ℕ} (hN : 3 ≤ N) : 0 ≤ coreConst N := by
  have := sameScaleConst_nonneg hN
  have := claimConst_nonneg hN
  unfold coreConst
  positivity

section Core

variable {a b s' α : ℤ} {N : ℕ} {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {i k : Fin 3}
  {P : Finset (ℤ × ℤ × ℤ)} {𝒯 : Finset TreeData}

/-- **The weak Bessel inequality under the energy upper bound** `∑_{t∈T}|a_t|² ≤ 2μ²|I_T|`. -/
theorem coreBound (hν : TriValid a b s' α) (hN : 3 ≤ N) (hik : i ≠ k)
    (hP : (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    (hφ : ∀ t ∈ P, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k))
    (h𝒯 : ∀ T ∈ 𝒯, IsTree a b i P T)
    (hdisj : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → Disjoint T.tiles T'.tiles)
    (hSD : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → StronglyDisjoint a b k T T')
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) {mu : ℝ} (hmu : 0 < mu)
    (htile : ∀ T ∈ 𝒯, ∀ t ∈ T.tiles,
      ‖pairing f (φ t k)‖ ^ 2 ≤ 4 * mu ^ 2 * (volume (timeInt t)).toReal)
    (hlow : ∀ T ∈ 𝒯, mu ^ 2 / 2 * (volume T.topInt).toReal ≤ ∑ t ∈ T.tiles, ‖pairing f (φ t k)‖ ^ 2)
    (hup : ∀ T ∈ 𝒯, ∑ t ∈ T.tiles, ‖pairing f (φ t k)‖ ^ 2 ≤ 2 * mu ^ 2 * (volume T.topInt).toReal) :
    ∑ T ∈ 𝒯, (volume T.topInt).toReal ≤ coreConst N * (∫ x, ‖f x‖ ^ 2) / mu ^ 2 := by
  classical
  set U : Finset (ℤ × ℤ × ℤ) := 𝒯.biUnion TreeData.tiles with hU
  set A : ℤ × ℤ × ℤ → ℝ := fun t => ‖pairing f (φ t k)‖ with hA
  set G : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ → ℝ := fun t t' => ‖pairing (φ t k) (φ t' k)‖ with hG
  set X : ℝ := ∑ T ∈ 𝒯, (volume T.topInt).toReal with hX
  set S : ℝ := ∑ t ∈ U, A t ^ 2 with hS
  set nf : ℝ := ∫ x, ‖f x‖ ^ 2 with hnf
  have hnf0 : 0 ≤ nf := integral_nonneg fun x => by positivity
  have hC3 := sameScaleConst_nonneg hN
  have hC4 := claimConst_nonneg hN
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun T _ => by rw [T.toReal_volume_topInt]; positivity
  have hUP : U ⊆ P := by
    intro t ht
    obtain ⟨T, hT, h⟩ := Finset.mem_biUnion.1 ht
    exact (h𝒯 T hT).subset h
  have hUmem : ∀ t ∈ U, ∃ T ∈ 𝒯, t ∈ T.tiles := by
    intro t ht
    obtain ⟨T, hT, h⟩ := Finset.mem_biUnion.1 ht
    exact ⟨T, hT, h⟩
  have hpd : (↑𝒯 : Set TreeData).PairwiseDisjoint TreeData.tiles :=
    fun T hT T' hT' hne => hdisj T hT T' hT' hne
  have hsumU : ∀ g : ℤ × ℤ × ℤ → ℝ, ∑ t ∈ U, g t = ∑ T ∈ 𝒯, ∑ t ∈ T.tiles, g t :=
    fun g => Finset.sum_biUnion hpd
  -- (1) `S` is comparable to `X`
  have hSlo : mu ^ 2 / 2 * X ≤ S := by
    rw [hS, hsumU, hX, Finset.mul_sum]
    exact Finset.sum_le_sum fun T hT => hlow T hT
  have hShi : S ≤ 2 * mu ^ 2 * X := by
    rw [hS, hsumU, hX, Finset.mul_sum]
    exact Finset.sum_le_sum fun T hT => hup T hT
  -- (2) Bessel from the Gram matrix
  have hu : ∀ t ∈ U, MemLp (φ t k) 2 := fun t ht =>
    (IsAdapted.memLp_two_and_integral_sq_le (by omega) (hφ t (hUP ht))
      (toReal_volume_timeInt_pos t)).1
  have hcs := Bessel.sq_sum_norm_pairing_le U (fun t => φ t k) hf hu
  -- (3) split the double sum
  set F : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ → ℝ := fun t t' => A t * A t' * G t t' with hF
  have hGs : ∀ t t', G t t' = G t' t := fun t t' => Bessel.norm_pairing_comm _ _
  have hFs : ∀ t t', F t t' = F t' t := fun t t' => by
    simp only [hF, hGs t t']; ring
  have hsplit := Bessel.double_sum_split U F hFs
  -- (4) equal scales
  have heq : ∑ t ∈ U, ∑ t' ∈ U with t'.1 = t.1, F t t' ≤ sameScaleConst N * S :=
    Bessel.sum_sameScale_le hN k φ P (fun t ht => hP ht) hφ hUP A
  -- (5) smaller scales
  have hAle : ∀ t ∈ U, A t ≤ 2 * mu * (volume (timeInt t)).toReal ^ (1 / 2 : ℝ) := by
    intro t ht
    obtain ⟨T, hT, htT⟩ := hUmem t ht
    have hv : 0 ≤ (volume (timeInt t)).toReal := (toReal_volume_timeInt_pos t).le
    have h1 : A t ^ 2 ≤ (2 * mu * (volume (timeInt t)).toReal ^ (1 / 2 : ℝ)) ^ 2 := by
      rw [mul_pow, mul_pow, rpow_half_sq hv]
      have := htile T hT t htT
      simp only [hA]
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 h1
  set cs : ℤ × ℤ × ℤ → ℝ := fun t => contribSum φ k U t with hcsdef
  have hlt : ∀ t ∈ U, ∑ t' ∈ U with t'.1 < t.1, F t t' ≤ 2 * mu * (A t * cs t) := by
    intro t ht
    have : ∑ t' ∈ U with t'.1 < t.1, F t t' ≤
        ∑ t' ∈ U with t'.1 < t.1, A t * (2 * mu) * ((volume (timeInt t')).toReal ^ (1 / 2 : ℝ) *
          G t t') := by
      refine Finset.sum_le_sum fun t' ht' => ?_
      have ht'U : t' ∈ U := (Finset.mem_filter.1 ht').1
      have h1 := hAle t' ht'U
      have h0 : 0 ≤ A t * G t t' := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      simp only [hF]
      calc A t * A t' * G t t' = (A t * G t t') * A t' := by ring
        _ ≤ (A t * G t t') * (2 * mu * (volume (timeInt t')).toReal ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 h0
        _ = _ := by ring
    refine this.trans (le_of_eq ?_)
    rw [← Finset.mul_sum]
    simp only [hcsdef, contribSum, hG]
    ring
  -- (6) the claim, tree by tree
  have htree : ∀ T ∈ 𝒯, ∑ t ∈ T.tiles, A t * cs t ≤
      (2 + claimConst N) * mu / 2 * (volume T.topInt).toReal := by
    intro T hT
    have hclaim := sum_sq_contribSum_le hν hN hik hP hφ h𝒯 hSD hT
    have h1 : ∀ t ∈ T.tiles, 2 * mu * (A t * cs t) ≤ A t ^ 2 + mu ^ 2 * cs t ^ 2 := by
      intro t _
      nlinarith [sq_nonneg (A t - mu * cs t)]
    have h2 : 2 * mu * ∑ t ∈ T.tiles, A t * cs t ≤
        2 * mu ^ 2 * (volume T.topInt).toReal +
          mu ^ 2 * (claimConst N * (volume T.topInt).toReal) := by
      rw [Finset.mul_sum]
      refine (Finset.sum_le_sum h1).trans ?_
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      have := hup T hT
      have h3 : mu ^ 2 * ∑ t ∈ T.tiles, cs t ^ 2 ≤ mu ^ 2 * (claimConst N * (volume T.topInt).toReal) :=
        mul_le_mul_of_nonneg_left hclaim (by positivity)
      simp only [hA] at this ⊢
      linarith
    refine le_of_mul_le_mul_left (a := 2 * mu) ?_ (by positivity)
    calc 2 * mu * ∑ t ∈ T.tiles, A t * cs t
        ≤ _ := h2
      _ = 2 * mu * ((2 + claimConst N) * mu / 2 * (volume T.topInt).toReal) := by ring
  have hlt' : ∑ t ∈ U, ∑ t' ∈ U with t'.1 < t.1, F t t' ≤
      2 * mu * ((2 + claimConst N) * mu / 2 * X) := by
    calc ∑ t ∈ U, ∑ t' ∈ U with t'.1 < t.1, F t t'
        ≤ ∑ t ∈ U, 2 * mu * (A t * cs t) := Finset.sum_le_sum hlt
      _ = 2 * mu * ∑ t ∈ U, A t * cs t := by rw [Finset.mul_sum]
      _ = 2 * mu * ∑ T ∈ 𝒯, ∑ t ∈ T.tiles, A t * cs t := by rw [hsumU]
      _ ≤ 2 * mu * ∑ T ∈ 𝒯, (2 + claimConst N) * mu / 2 * (volume T.topInt).toReal :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum htree) (by positivity)
      _ = _ := by rw [← Finset.mul_sum]
  -- (7) assemble
  have hW : ∑ t ∈ U, ∑ t' ∈ U, F t t' ≤
      (4 + 2 * claimConst N + 2 * sameScaleConst N) * (mu ^ 2 * X) := by
    rw [hsplit]
    have h3 : sameScaleConst N * S ≤ sameScaleConst N * (2 * mu ^ 2 * X) :=
      mul_le_mul_of_nonneg_left hShi hC3
    nlinarith [hlt', heq, h3]
  have hfin : (mu ^ 2 / 2 * X) ^ 2 ≤ nf * ((4 + 2 * claimConst N + 2 * sameScaleConst N) *
      (mu ^ 2 * X)) := by
    have h1 : (mu ^ 2 / 2 * X) ^ 2 ≤ S ^ 2 :=
      pow_le_pow_left₀ (by positivity) hSlo 2
    refine h1.trans (hcs.trans ?_)
    exact mul_le_mul_of_nonneg_left hW hnf0
  have hK : 0 ≤ 4 + 2 * claimConst N + 2 * sameScaleConst N := by positivity
  rcases hX0.eq_or_lt with h0 | hpos
  · rw [← h0]
    have := coreConst_nonneg hN
    positivity
  · have hm2 : 0 < mu ^ 2 := by positivity
    rw [le_div_iff₀ hm2]
    have h4 : (mu ^ 2 * X / 4) * (mu ^ 2 * X) ≤
        (nf * (4 + 2 * claimConst N + 2 * sameScaleConst N)) * (mu ^ 2 * X) := by
      nlinarith [hfin]
    have h5 := le_of_mul_le_mul_right h4 (by positivity)
    unfold coreConst
    nlinarith [h5]

end Core

end PrimeBHT.TimeFrequency.Tile
