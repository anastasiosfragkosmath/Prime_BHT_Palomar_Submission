module

public import PrimeBHT.TimeFrequency.Tile.RefSize
public import PrimeBHT.TimeFrequency.Tile.Orth
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Node C9 for arbitrary slot roles: `RefSize.lean` with `0, 1, 2` replaced by `σ 0, σ 1, σ 2`

`RefSize.lean` (C9) fixes the roles of the slots: slot `0` carries the smallest set (the `L¹`-normalized
one), slot `1` the middle one, slot `2` the largest. The frozen `M1(ε)` quantifies over all permutations
`σ` of the slots with `|E (σ 0)| ≤ |E (σ 1)| ≤ |E (σ 2)|`, and the tile geometry (`freqInt a b k`,
the lacunarity ratio `lacRatio i k`) is not symmetric in the slots, so this file redoes C9 with the roles
`(small, mid, large) = (σ 0, σ 1, σ 2)`. Every generic input (C1-C5, C7, C8) is stated for arbitrary
`i k : Fin 3` and is reused unchanged; only the literal slot indices of C9 are replaced.

## Setting

`σ : Equiv.Perm (Fin 3)`, `E : Fin 3 → Set ℝ` (indexed by SLOT), `h : Fin 3 → ℝ → ℂ` with `h k`
measurable, `‖h k‖ ≤ 1_{E k}`, `E k` measurable, `0 < |E (σ 0)| ≤ |E (σ 1)| ≤ |E (σ 2)|`,
`1/2 < |E (σ 2)| ≤ 1`.

## Definitions

* `refExceptionalσ σ E = refExceptional (E (σ 0)) (E (σ 1))` (`abbrev`): the exceptional set `F` of C9,
  `{M 1_{E (σ 0)} > 100 |E (σ 0)|} ∪ {M 1_{E (σ 1)} > 100 |E (σ 1)|}`;
* `refScaleσ σ E k = |E k|⁻¹` if `k = σ 0`, else `|E k|^{-1/2}`; `refGσ σ E h k = refScaleσ σ E k · h k`
  (`g_{σ 0} = |E (σ 0)|⁻¹ h_{σ 0}` is `L¹`-normalized, `g_{σ 1}`, `g_{σ 2}` are `L²`-normalized);
* the `L²`-normalized functions `g'_k = |E k|^{-1/2} h k` are `refG' E h k` of `RefSize.lean` (this
  definition does not involve the roles, so no `σ`-version is needed): `refG' E h k = refGσ σ E h k` for
  `k ≠ σ 0` (`refGσ_of_ne`) and `refG' E h (σ 0) = |E (σ 0)|^{1/2} · refGσ σ E h (σ 0)`
  (`refG'_eq_mul_refGσ`).

## Final theorems (unconditional, constants depend on `N` only)

With `hν : TriValid a b s' α`, `4 ≤ N`, `hP' : ↑P' ⊆ triIdx s' α`, `hφ : ∀ t ∈ P', ∀ k,
IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)`, `hnot : ∀ t ∈ P', ¬ timeInt t ⊆ refExceptional
(E (σ 0)) (E (σ 1))` and the setting above (the explicit hypotheses are listed in each signature):

* `isOpen_and_volume_refExceptionalσ_lt`: `refExceptional (E (σ 0)) (E (σ 1))` is open, of measure `< 1/12`;
* `size_refGσ_le_orth`:
  `size a b φ i k (refGσ σ E h k) P' ≤ ofReal (refSizeConst (orthSizeConst N) (sameScaleConst N))`
  for all `i k : Fin 3`;
* `size_refG'_σ0_le_orth`:
  `size a b φ i (σ 0) (refG' E h (σ 0)) P' ≤
    ofReal (refSizeConst (orthSizeConst N) (sameScaleConst N) * |E (σ 0)|^{1/2})`;
* `size_refG'_ne_σ0_le_orth` (`k ≠ σ 0`):
  `size a b φ i k (refG' E h k) P' ≤ ofReal (refSizeConst (orthSizeConst N) (sameScaleConst N))`.

The same three size statements hold conditionally on `SizeOffMax CO N₀` and `TreeBessel B N₀`
(`size_refGσ_le`, `size_refG'_σ0_le`, `size_refG'_ne_σ0_le`), for any constants `CO, B` with
`0 ≤ CO N`, `0 ≤ B N`; `..._orth` discharges them with C8 exactly as `OrthGlue.lean` does.

## Proof notes

Identical to `RefSize.lean` with `0` replaced by `σ 0`: the `L¹`-slot off-diagonal size is C7 applied to
each `i`-tree with `ξ' = lacRatio i (σ 0) · ξ_T` (`sizeOff_L1_le_of_bessel`, slot `k` arbitrary); the
`L²`-slots are C8(b) with `M(|g|²)(x) ≤ C₀` (`σ 1`) and `|g| ≤ 3/2` (`σ 2`); the diagonal sizes are (M5).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PrimeBHT.Statements
open PrimeCarleson.Proof.Common (maximalHLR)
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Tile

/-! ### The exceptional set for the roles `σ` -/

/-- The exceptional set `F` of C9 for the slot roles `σ`: it is built from the smallest and the middle set,
`F = {M 1_{E (σ 0)} > 100 |E (σ 0)|} ∪ {M 1_{E (σ 1)} > 100 |E (σ 1)|}`. -/
abbrev refExceptionalσ (σ : Equiv.Perm (Fin 3)) (E : Fin 3 → Set ℝ) : Set ℝ :=
  refExceptional (E (σ 0)) (E (σ 1))

/-! ### The normalizations -/

/-- The scalars of the normalizations of C9 for the roles `σ`: `|E k|⁻¹` for the smallest set
(`k = σ 0`, `L¹`) and `|E k|^{-1/2}` for the others (`L²`). -/
def refScaleσ (σ : Equiv.Perm (Fin 3)) (E : Fin 3 → Set ℝ) (k : Fin 3) : ℝ :=
  if k = σ 0 then ((volume (E k)).toReal)⁻¹ else refScale' E k

/-- The functions `g_k` of C9 for the roles `σ`: `g_{σ 0} = |E (σ 0)|⁻¹ h_{σ 0}`,
`g_{σ 1} = |E (σ 1)|^{-1/2} h_{σ 1}`, `g_{σ 2} = |E (σ 2)|^{-1/2} h_{σ 2}`. -/
def refGσ (σ : Equiv.Perm (Fin 3)) (E : Fin 3 → Set ℝ) (h : Fin 3 → ℝ → ℂ) (k : Fin 3) : ℝ → ℂ :=
  fun x => ((refScaleσ σ E k : ℝ) : ℂ) * h k x

theorem refScaleσ_σ0 (σ : Equiv.Perm (Fin 3)) (E : Fin 3 → Set ℝ) :
    refScaleσ σ E (σ 0) = ((volume (E (σ 0))).toReal)⁻¹ := by
  simp [refScaleσ]

theorem refScaleσ_of_ne {σ : Equiv.Perm (Fin 3)} (E : Fin 3 → Set ℝ) {k : Fin 3} (hk : k ≠ σ 0) :
    refScaleσ σ E k = refScale' E k := by
  simp [refScaleσ, hk]

theorem refGσ_σ0 (σ : Equiv.Perm (Fin 3)) (E : Fin 3 → Set ℝ) (h : Fin 3 → ℝ → ℂ) :
    refGσ σ E h (σ 0) = fun x => ((((volume (E (σ 0))).toReal)⁻¹ : ℝ) : ℂ) * h (σ 0) x := by
  funext x
  simp only [refGσ, refScaleσ_σ0]

/-- For `k ≠ σ 0` the normalization is the `L²` one: `g_k = g'_k`. -/
theorem refGσ_of_ne {σ : Equiv.Perm (Fin 3)} (E : Fin 3 → Set ℝ) (h : Fin 3 → ℝ → ℂ) {k : Fin 3}
    (hk : k ≠ σ 0) : refGσ σ E h k = refG' E h k := by
  funext x
  simp only [refGσ, refG', refScaleσ_of_ne E hk]

/-- `g'_{σ 0} = |E (σ 0)|^{1/2} g_{σ 0}`. -/
theorem refG'_eq_mul_refGσ {σ : Equiv.Perm (Fin 3)} {E : Fin 3 → Set ℝ} (h : Fin 3 → ℝ → ℂ)
    (hpos : 0 < (volume (E (σ 0))).toReal) :
    refG' E h (σ 0) =
      fun x => (((volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * refGσ σ E h (σ 0) x := by
  funext x
  simp only [refG', refGσ, refScaleσ_σ0, refScale', ← mul_assoc]
  congr 1
  rw [← Complex.ofReal_mul]
  congr 1
  rw [← Real.rpow_neg_one, ← Real.rpow_add hpos]
  norm_num

/-! ### Pointwise bounds -/

theorem norm_refGσ_σ0_le_indicator {σ : Equiv.Perm (Fin 3)} {E : Fin 3 → Set ℝ}
    {h : Fin 3 → ℝ → ℂ} (hdom : ∀ x, ‖h (σ 0) x‖ ≤ (E (σ 0)).indicator (1 : ℝ → ℝ) x) (x : ℝ) :
    ‖refGσ σ E h (σ 0) x‖ ≤ ((volume (E (σ 0))).toReal)⁻¹ * (E (σ 0)).indicator (1 : ℝ → ℝ) x := by
  have := norm_ofReal_mul_le_indicator (inv_nonneg.2 (ENNReal.toReal_nonneg (a := volume (E (σ 0)))))
    hdom x
  rwa [refGσ_σ0]

theorem norm_refG'_le_mul_indicator {E : Fin 3 → Set ℝ} {h : Fin 3 → ℝ → ℂ} {k : Fin 3}
    (hdom : ∀ x, ‖h k x‖ ≤ (E k).indicator (1 : ℝ → ℝ) x) (x : ℝ) :
    ‖refG' E h k x‖ ≤ (volume (E k)).toReal ^ (-(1 : ℝ) / 2) * (E k).indicator (1 : ℝ → ℝ) x :=
  norm_ofReal_mul_le_indicator (refScale'_nonneg E k) hdom x

/-- `‖g'_k‖ ≤ 3/2` if `|E k| > 1/2`. -/
theorem norm_refG'_le_three_halves {E : Fin 3 → Set ℝ} {h : Fin 3 → ℝ → ℂ} {k : Fin 3}
    (hhalf : 1 / 2 < (volume (E k)).toReal)
    (hdom : ∀ x, ‖h k x‖ ≤ (E k).indicator (1 : ℝ → ℝ) x) (x : ℝ) : ‖refG' E h k x‖ ≤ 3 / 2 := by
  refine (norm_refG'_le_mul_indicator hdom x).trans ?_
  have hind : (E k).indicator (1 : ℝ → ℝ) x ≤ 1 := by
    by_cases hx : x ∈ E k <;> simp [hx]
  have h0 : 0 ≤ (volume (E k)).toReal ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hs : (volume (E k)).toReal ^ (-(1 : ℝ) / 2) ≤ 3 / 2 :=
    refScale_two_le (E := fun _ => E k) hhalf
  calc (volume (E k)).toReal ^ (-(1 : ℝ) / 2) * (E k).indicator (1 : ℝ → ℝ) x
      ≤ (volume (E k)).toReal ^ (-(1 : ℝ) / 2) * 1 := mul_le_mul_of_nonneg_left hind h0
    _ ≤ 3 / 2 := by rw [mul_one]; exact hs

/-- `M g (x) ≤ C₀` for `‖g‖ ≤ |E|^{-1/2} 1_E`, `|E| ≤ 1`, `x ∉ {M 1_E > C₀ |E|}`. -/
theorem maximalHLR_le_of_notMem_exceptionalSet_L2_of_le_one {E : Set ℝ} {C₀ : ℝ} {x : ℝ}
    (hx : x ∉ exceptionalSet E C₀) (hC : 0 ≤ C₀) (h0 : volume E ≠ 0) (htop : volume E ≠ ⊤)
    (hle : (volume E).toReal ≤ 1) {g : ℝ → ℂ}
    (hdom : ∀ y, ‖g y‖ ≤ (volume E).toReal ^ (-(1 : ℝ) / 2) * E.indicator (1 : ℝ → ℝ) y) :
    maximalHLR g x ≤ ENNReal.ofReal C₀ := by
  have hpos : 0 < (volume E).toReal := ENNReal.toReal_pos h0 htop
  refine (maximalHLR_le_of_notMem_exceptionalSet hx hC (Real.rpow_nonneg hpos.le _) htop
    hdom).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have e : (volume E).toReal ^ (-(1 : ℝ) / 2) * (volume E).toReal =
      (volume E).toReal ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_add_one hpos.ne']
    norm_num
  have h1 : (volume E).toReal ^ ((1 : ℝ) / 2) ≤ 1 := Real.rpow_le_one hpos.le hle (by norm_num)
  calc (volume E).toReal ^ (-(1 : ℝ) / 2) * C₀ * (volume E).toReal
      = C₀ * ((volume E).toReal ^ (-(1 : ℝ) / 2) * (volume E).toReal) := by ring
    _ ≤ C₀ * 1 := by rw [e]; exact mul_le_mul_of_nonneg_left h1 hC
    _ = C₀ := mul_one _

/-! ### The `L¹`-normalized slot, `i ≠ k`: C7 (slot `k` arbitrary) -/

/-- **C9 step 5 for an arbitrary slot `k`** (conditional on `TreeBessel B N₀`): for `i ≠ k`,
`size_{i,k}(|E₁|⁻¹ h₁, P') ≤ C₀ √(energyConst (B N))` if `I_t ⊄ {M 1_{E₁} > C₀ |E₁|}` for all `t ∈ P'`.
Each `i`-tree `T ⊆ P'` is handled by C7 with `ξ'_T = lacRatio i k · ξ_T ∈ 50 ω_{t,k}` (C1(e)), the
multiplicity bound `≤ 3` (C1) and the top `I_T`. -/
theorem sizeOff_L1_le_of_bessel {a b s' α : ℤ} (hν : TriValid a b s' α) {N N₀ : ℕ}
    (hN : 4 ≤ N) (hN₀ : N₀ ≤ N) {B : ℕ → ℝ} (hB : 0 ≤ B N) (hBes : TreeBessel B N₀)
    {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {P' : Finset (ℤ × ℤ × ℤ)}
    (hP' : (↑P' : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    (hφ : ∀ t ∈ P', ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k))
    {i k : Fin 3} (hik : i ≠ k) {E₁ : Set ℝ} {h₁ : ℝ → ℂ}
    (hEm : MeasurableSet E₁) (h0 : volume E₁ ≠ 0) (htop : volume E₁ ≠ ⊤)
    (hhm : Measurable h₁) (hdom : ∀ x, ‖h₁ x‖ ≤ E₁.indicator (1 : ℝ → ℝ) x)
    (hnot : ∀ t ∈ P', ¬ timeInt t ⊆ exceptionalSet E₁ refC0) :
    sizeOff a b φ i k (fun x => ((((volume E₁).toReal)⁻¹ : ℝ) : ℂ) * h₁ x) P' ≤
      ENNReal.ofReal (refC0 * Real.sqrt (energyConst (B N))) := by
  classical
  refine sizeOff_le fun T hT => ?_
  have hTP : T.tiles ⊆ P' := hT.subset
  have hmult : ∀ t ∈ T.tiles,
      (T.tiles.filter fun t' => (t'.1, t'.2.1) = (t.1, t.2.1)).card ≤ 3 := by
    intro t _
    have h3 := hT.card_filter_timeInt_le_three hP' (timeInt t)
    have e : (T.tiles.filter fun t' => (t'.1, t'.2.1) = (t.1, t.2.1)) =
        T.tiles.filter fun t' => timeInt t' = timeInt t := by
      refine Finset.filter_congr fun t' _ => ?_
      rw [timeInt_eq_iff, Prod.mk.injEq]
    rw [e]
    exact h3
  have key := sum_norm_sq_pairing_normalized_le_of_bessel (N := N) hN (a := a) (b := b) (k := k)
    (T := T.tiles) (φ := φ) (fun t ht => hφ t (hTP ht) k) (ξ' := lacRatio i k * T.ξ)
    (fun t ht => (hT.lacunary hν hik ht).1) (sT := T.top.1) (vT := T.top.2)
    (fun t ht => hT.timeInt_subset ht) hmult hB
    (hBes a b s' α hν N hN₀ φ P' hP' hφ i k hik T hT)
    hEm h0 htop hhm.aestronglyMeasurable hdom (C₀ := refC0) refC0_pos
    (F := exceptionalSet E₁ refC0) subset_rfl (fun t ht => hnot t (hTP ht))
  have hkey : treeEnergy φ k (fun x => ((((volume E₁).toReal)⁻¹ : ℝ) : ℂ) * h₁ x) T ≤
      energyConst (B N) * refC0 ^ 2 := key
  rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg refC0_pos.le (Real.sqrt_nonneg _))]
  refine Real.sqrt_le_iff.2 ⟨mul_nonneg refC0_pos.le (Real.sqrt_nonneg _), ?_⟩
  have hE : 0 ≤ energyConst (B N) := energyConst_nonneg hB
  calc treeEnergy φ k (fun x => ((((volume E₁).toReal)⁻¹ : ℝ) : ℂ) * h₁ x) T
      ≤ energyConst (B N) * refC0 ^ 2 := hkey
    _ = (refC0 * Real.sqrt (energyConst (B N))) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hE]; ring

/-! ### Part (ii) for the roles `σ`: the sizes outside the exceptional set -/

/-- **C9 (ii) for the roles `σ`**, conditional on `SizeOffMax CO N₀` and `TreeBessel B N₀` (C8): for
`P' ⊆ triIdx s' α` finite with `I_t ⊄ F` for all `t ∈ P'` (`F = refExceptional (E (σ 0)) (E (σ 1))`), packets
adapted with exponent `N ≥ max 4 N₀`, all `i, k`: `size_{i,k}(g_k, P') ≤ refSizeConst (CO N) (B N)`. -/
theorem size_refGσ_le {a b s' α : ℤ} (hν : TriValid a b s' α) {N N₀ : ℕ} (hN : 4 ≤ N)
    (hN₀ : N₀ ≤ N) {CO B : ℕ → ℝ} (hCO : 0 ≤ CO N) (hB : 0 ≤ B N) (hSO : SizeOffMax CO N₀)
    (hBes : TreeBessel B N₀)
    {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {P' : Finset (ℤ × ℤ × ℤ)}
    (hP' : (↑P' : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    (hφ : ∀ t ∈ P', ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k))
    (σ : Equiv.Perm (Fin 3)) {E : Fin 3 → Set ℝ} {h : Fin 3 → ℝ → ℂ}
    (hEm : ∀ k, MeasurableSet (E k))
    (h01 : volume (E (σ 0)) ≤ volume (E (σ 1))) (h12 : volume (E (σ 1)) ≤ volume (E (σ 2)))
    (hE0 : volume (E (σ 0)) ≠ 0) (hhalf : 1 / 2 < (volume (E (σ 2))).toReal)
    (hone : (volume (E (σ 2))).toReal ≤ 1)
    (hhm : ∀ k, Measurable (h k)) (hdom : ∀ k x, ‖h k x‖ ≤ (E k).indicator (1 : ℝ → ℝ) x)
    (hnot : ∀ t ∈ P', ¬ timeInt t ⊆ refExceptional (E (σ 0)) (E (σ 1))) (i k : Fin 3) :
    size a b φ i k (refGσ σ E h k) P' ≤ ENNReal.ofReal (refSizeConst (CO N) (B N)) := by
  obtain ⟨hnz, hnt⟩ := volume_ne_zero_ne_top_of_normalized (E := fun r => E (σ r)) h01 h12 hE0
    hhalf
  have hnz' : ∀ r : Fin 3, volume (E (σ r)) ≠ 0 := hnz
  have hnt' : ∀ r : Fin 3, volume (E (σ r)) ≠ ⊤ := hnt
  have hone1 : (volume (E (σ 1))).toReal ≤ 1 :=
    (ENNReal.toReal_mono (hnt' 2) h12).trans hone
  have hx : ∀ t ∈ P', ∃ x ∈ timeInt t,
      x ∉ exceptionalSet (E (σ 0)) refC0 ∧ x ∉ exceptionalSet (E (σ 1)) refC0 :=
    fun t ht => exists_mem_notMem_exceptionalSet_of_not_subset (hnot t ht)
  have hsqrt : 0 ≤ Real.sqrt (energyConst (B N)) := Real.sqrt_nonneg _
  have hC0 : refC0 = 100 := rfl
  have hle : ∀ x : ℝ, x ≤ refSizeConst (CO N) (B N) → ∀ {c : ℝ≥0∞}, c ≤ ENNReal.ofReal x →
      c ≤ ENNReal.ofReal (refSizeConst (CO N) (B N)) :=
    fun x hx c hc => hc.trans (ENNReal.ofReal_le_ofReal hx)
  -- the diagonal sizes, from (M5)
  have hdiag : ∀ (k : Fin 3) (f : ℝ → ℂ), Measurable f → ∀ μ : ℝ, 0 ≤ μ →
      (∀ t ∈ P', ∃ x ∈ timeInt t, maximalHLR f x ≤ ENNReal.ofReal μ) →
      sizeDiag φ k f P' ≤ ENNReal.ofReal (45 / 2 * μ) :=
    fun k f hf μ hμ hM => sizeDiag_le_of_exists_maximalHLR_le (by omega) hφ k hf hμ hM
  have hgm : ∀ k, Measurable (refG' E h k) := fun k => (hhm k).const_mul _
  by_cases hk0 : k = σ 0
  · subst hk0
    -- `g = |E (σ 0)|⁻¹ h`, the `L¹`-normalized slot
    have hgm0 : Measurable (refGσ σ E h (σ 0)) := by
      rw [refGσ_σ0]
      exact (hhm _).const_mul _
    by_cases hik : i = σ 0
    · subst hik
      rw [size_self]
      refine hle (45 / 2 * refC0) (by unfold refSizeConst; rw [hC0]; linarith)
        (hdiag (σ 0) _ hgm0 refC0 refC0_pos.le fun t ht => ?_)
      obtain ⟨x, hxt, hx0, -⟩ := hx t ht
      exact ⟨x, hxt, maximalHLR_le_of_notMem_exceptionalSet_L1 hx0 refC0_pos.le (hnz' 0) (hnt' 0)
        (norm_refGσ_σ0_le_indicator (hdom _)) ⟩
    · rw [size_of_ne hik, refGσ_σ0]
      refine hle (refC0 * Real.sqrt (energyConst (B N)))
        (by unfold refSizeConst; rw [hC0]; linarith) ?_
      exact sizeOff_L1_le_of_bessel hν hN hN₀ hB hBes hP' hφ hik (hEm _) (hnz' 0) (hnt' 0)
        (hhm _) (hdom _) fun t ht hsub => hnot t ht (hsub.trans Set.subset_union_left)
  · rw [refGσ_of_ne E h hk0]
    have hk12 : k = σ 1 ∨ k = σ 2 := by
      obtain ⟨r, rfl⟩ := σ.surjective k
      have hr : r ≠ 0 := fun h0 => hk0 (by rw [h0])
      have hr12 : ∀ r : Fin 3, r ≠ 0 → r = 1 ∨ r = 2 := by decide
      rcases hr12 r hr with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hk12 with rfl | rfl
    · -- `g = |E (σ 1)|^{-1/2} h`
      by_cases hik : i = σ 1
      · subst hik
        rw [size_self]
        refine hle (45 / 2 * refC0) (by unfold refSizeConst; rw [hC0]; linarith)
          (hdiag (σ 1) _ (hgm _) refC0 refC0_pos.le fun t ht => ?_)
        obtain ⟨x, hxt, -, hx1⟩ := hx t ht
        exact ⟨x, hxt, maximalHLR_le_of_notMem_exceptionalSet_L2_of_le_one hx1 refC0_pos.le
          (hnz' 1) (hnt' 1) hone1 (norm_refG'_le_mul_indicator (hdom _))⟩
      · refine hle (CO N * 10) (by unfold refSizeConst; linarith) ?_
        refine hSO a b s' α hν N hN₀ φ P' hP' hφ i (σ 1) hik (refG' E h (σ 1)) (hgm _) 10
          (by norm_num) ?_
        intro t ht
        obtain ⟨x, hxt, -, hx1⟩ := hx t ht
        refine ⟨x, hxt, (maximalHLR_enorm_sq_le_of_notMem_exceptionalSet_L2 hx1 refC0_pos.le
          (hnz' 1) (hnt' 1) (norm_refG'_le_mul_indicator (hdom _))).trans_eq ?_⟩
        congr 1
        norm_num [refC0]
    · -- `g = |E (σ 2)|^{-1/2} h`
      by_cases hik : i = σ 2
      · subst hik
        rw [size_self]
        refine hle (45 / 2 * (3 / 2)) (by unfold refSizeConst; linarith)
          (hdiag (σ 2) _ (hgm _) (3 / 2) (by norm_num) fun t ht => ?_)
        obtain ⟨x, hxt, -, -⟩ := hx t ht
        exact ⟨x, hxt, maximalHLR_le_of_norm_le (norm_refG'_le_three_halves hhalf (hdom _)) x⟩
      · refine hle (CO N * (3 / 2)) (by unfold refSizeConst; linarith) ?_
        refine hSO a b s' α hν N hN₀ φ P' hP' hφ i (σ 2) hik (refG' E h (σ 2)) (hgm _) (3 / 2)
          (by norm_num) ?_
        intro t ht
        obtain ⟨x, hxt, -, -⟩ := hx t ht
        exact ⟨x, hxt, maximalHLR_enorm_sq_le_of_norm_le (by norm_num)
          (norm_refG'_le_three_halves hhalf (hdom _)) x⟩

/-! ### The `L²`-normalized forms (input of C10a, step 1) -/

/-- **C9 (ii'), `L²`-normalized `g'_{σ 0}`**: `size_{i,σ 0}(g'_{σ 0}, P') ≤ C |E (σ 0)|^{1/2}`
(`g'_{σ 0} = |E (σ 0)|^{-1/2} h_{σ 0} = |E (σ 0)|^{1/2} g_{σ 0}`, sizes are homogeneous of degree one). -/
theorem size_refG'_σ0_le {a b s' α : ℤ} (hν : TriValid a b s' α) {N N₀ : ℕ} (hN : 4 ≤ N)
    (hN₀ : N₀ ≤ N) {CO B : ℕ → ℝ} (hCO : 0 ≤ CO N) (hB : 0 ≤ B N) (hSO : SizeOffMax CO N₀)
    (hBes : TreeBessel B N₀)
    {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {P' : Finset (ℤ × ℤ × ℤ)}
    (hP' : (↑P' : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    (hφ : ∀ t ∈ P', ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k))
    (σ : Equiv.Perm (Fin 3)) {E : Fin 3 → Set ℝ} {h : Fin 3 → ℝ → ℂ}
    (hEm : ∀ k, MeasurableSet (E k))
    (h01 : volume (E (σ 0)) ≤ volume (E (σ 1))) (h12 : volume (E (σ 1)) ≤ volume (E (σ 2)))
    (hE0 : volume (E (σ 0)) ≠ 0) (hhalf : 1 / 2 < (volume (E (σ 2))).toReal)
    (hone : (volume (E (σ 2))).toReal ≤ 1)
    (hhm : ∀ k, Measurable (h k)) (hdom : ∀ k x, ‖h k x‖ ≤ (E k).indicator (1 : ℝ → ℝ) x)
    (hnot : ∀ t ∈ P', ¬ timeInt t ⊆ refExceptional (E (σ 0)) (E (σ 1))) (i : Fin 3) :
    size a b φ i (σ 0) (refG' E h (σ 0)) P' ≤
      ENNReal.ofReal (refSizeConst (CO N) (B N) * (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2)) := by
  obtain ⟨hnz, hnt⟩ := volume_ne_zero_ne_top_of_normalized (E := fun r => E (σ r)) h01 h12 hE0
    hhalf
  have hpos : 0 < (volume (E (σ 0))).toReal := ENNReal.toReal_pos (hnz 0) (hnt 0)
  have hc : 0 ≤ (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hpos.le _
  rw [refG'_eq_mul_refGσ h hpos]
  refine (size_const_mul_le hc i (σ 0) (refGσ σ E h (σ 0))).trans ?_
  have h1 := size_refGσ_le hν hN hN₀ hCO hB hSO hBes hP' hφ σ hEm h01 h12 hE0 hhalf hone hhm hdom
    hnot i (σ 0)
  rw [mul_comm (refSizeConst (CO N) (B N)), ENNReal.ofReal_mul hc]
  exact mul_le_mul' le_rfl h1

/-- **C9 (ii')** for `k ≠ σ 0`: `g'_k = g_k`, so `size_{i,k}(g'_k, P') ≤ C`. -/
theorem size_refG'_ne_σ0_le {a b s' α : ℤ} (hν : TriValid a b s' α) {N N₀ : ℕ} (hN : 4 ≤ N)
    (hN₀ : N₀ ≤ N) {CO B : ℕ → ℝ} (hCO : 0 ≤ CO N) (hB : 0 ≤ B N) (hSO : SizeOffMax CO N₀)
    (hBes : TreeBessel B N₀)
    {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {P' : Finset (ℤ × ℤ × ℤ)}
    (hP' : (↑P' : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    (hφ : ∀ t ∈ P', ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k))
    (σ : Equiv.Perm (Fin 3)) {E : Fin 3 → Set ℝ} {h : Fin 3 → ℝ → ℂ}
    (hEm : ∀ k, MeasurableSet (E k))
    (h01 : volume (E (σ 0)) ≤ volume (E (σ 1))) (h12 : volume (E (σ 1)) ≤ volume (E (σ 2)))
    (hE0 : volume (E (σ 0)) ≠ 0) (hhalf : 1 / 2 < (volume (E (σ 2))).toReal)
    (hone : (volume (E (σ 2))).toReal ≤ 1)
    (hhm : ∀ k, Measurable (h k)) (hdom : ∀ k x, ‖h k x‖ ≤ (E k).indicator (1 : ℝ → ℝ) x)
    (hnot : ∀ t ∈ P', ¬ timeInt t ⊆ refExceptional (E (σ 0)) (E (σ 1))) (i : Fin 3) {k : Fin 3}
    (hk : k ≠ σ 0) :
    size a b φ i k (refG' E h k) P' ≤ ENNReal.ofReal (refSizeConst (CO N) (B N)) := by
  rw [← refGσ_of_ne E h hk]
  exact size_refGσ_le hν hN hN₀ hCO hB hSO hBes hP' hφ σ hEm h01 h12 hE0 hhalf hone hhm hdom hnot
    i k

/-! ### Unconditional versions (C8 discharges `SizeOffMax` and `TreeBessel`, as in `OrthGlue.lean`) -/

theorem orth_constants_nonneg {N : ℕ} (hN : 4 ≤ N) :
    0 ≤ orthSizeConst N ∧ 0 ≤ sameScaleConst N := by
  refine ⟨orthSizeConst_nonneg N, ?_⟩
  exact mul_nonneg (gramConst_nonneg (by omega)) (tsum_nonneg fun j => by positivity)

/-- **C9 (ii'), unconditional**: `size_{i,σ 0}(g'_{σ 0}, P') ≤ C |E (σ 0)|^{1/2}`. -/
theorem size_refG'_σ0_le_orth {a b s' α : ℤ} (hν : TriValid a b s' α) {N : ℕ} (hN : 4 ≤ N)
    {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {P' : Finset (ℤ × ℤ × ℤ)}
    (hP' : (↑P' : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    (hφ : ∀ t ∈ P', ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k))
    (σ : Equiv.Perm (Fin 3)) {E : Fin 3 → Set ℝ} {h : Fin 3 → ℝ → ℂ}
    (hEm : ∀ k, MeasurableSet (E k))
    (h01 : volume (E (σ 0)) ≤ volume (E (σ 1))) (h12 : volume (E (σ 1)) ≤ volume (E (σ 2)))
    (hE0 : volume (E (σ 0)) ≠ 0) (hhalf : 1 / 2 < (volume (E (σ 2))).toReal)
    (hone : (volume (E (σ 2))).toReal ≤ 1)
    (hhm : ∀ k, Measurable (h k)) (hdom : ∀ k x, ‖h k x‖ ≤ (E k).indicator (1 : ℝ → ℝ) x)
    (hnot : ∀ t ∈ P', ¬ timeInt t ⊆ refExceptional (E (σ 0)) (E (σ 1))) (i : Fin 3) :
    size a b φ i (σ 0) (refG' E h (σ 0)) P' ≤
      ENNReal.ofReal (refSizeConst (orthSizeConst N) (sameScaleConst N) *
        (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2)) :=
  size_refG'_σ0_le hν hN (by omega) (orth_constants_nonneg hN).1 (orth_constants_nonneg hN).2
    sizeOffMax_orthSizeConst treeBessel_sameScaleConst hP' hφ σ hEm h01 h12 hE0 hhalf hone hhm hdom
    hnot i

/-- **C9 (ii'), unconditional**, `k ≠ σ 0`: `size_{i,k}(g'_k, P') ≤ C`. -/
theorem size_refG'_ne_σ0_le_orth {a b s' α : ℤ} (hν : TriValid a b s' α) {N : ℕ} (hN : 4 ≤ N)
    {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {P' : Finset (ℤ × ℤ × ℤ)}
    (hP' : (↑P' : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    (hφ : ∀ t ∈ P', ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k))
    (σ : Equiv.Perm (Fin 3)) {E : Fin 3 → Set ℝ} {h : Fin 3 → ℝ → ℂ}
    (hEm : ∀ k, MeasurableSet (E k))
    (h01 : volume (E (σ 0)) ≤ volume (E (σ 1))) (h12 : volume (E (σ 1)) ≤ volume (E (σ 2)))
    (hE0 : volume (E (σ 0)) ≠ 0) (hhalf : 1 / 2 < (volume (E (σ 2))).toReal)
    (hone : (volume (E (σ 2))).toReal ≤ 1)
    (hhm : ∀ k, Measurable (h k)) (hdom : ∀ k x, ‖h k x‖ ≤ (E k).indicator (1 : ℝ → ℝ) x)
    (hnot : ∀ t ∈ P', ¬ timeInt t ⊆ refExceptional (E (σ 0)) (E (σ 1))) (i : Fin 3) {k : Fin 3}
    (hk : k ≠ σ 0) :
    size a b φ i k (refG' E h k) P' ≤
      ENNReal.ofReal (refSizeConst (orthSizeConst N) (sameScaleConst N)) :=
  size_refG'_ne_σ0_le hν hN (by omega) (orth_constants_nonneg hN).1 (orth_constants_nonneg hN).2
    sizeOffMax_orthSizeConst treeBessel_sameScaleConst hP' hφ σ hEm h01 h12 hE0 hhalf hone hhm hdom
    hnot i hk

end PrimeBHT.TimeFrequency.Tile
