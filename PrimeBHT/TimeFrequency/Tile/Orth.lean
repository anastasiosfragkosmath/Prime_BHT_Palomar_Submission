module

public import PrimeBHT.TimeFrequency.Tile.Gram.Pair
public import PrimeBHT.TimeFrequency.Tile.Gram.Bessel
public import PrimeBHT.TimeFrequency.Tile.Maximal
public import PrimeBHT.TimeFrequency.Tile.Lacunary
public import PrimeBHT.TimeFrequency.Tile.Trees
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Tree orthogonality and size bounds by maximal functions (blueprint node C8, `TT.orth`)

Imports `Gram/Pair`, `Gram/Bessel` (not `Gram.lean`, to avoid loading `Gram/Bernstein`, which at the
time of writing redeclares `intervalCentre_Ico` of `Grid` and cannot be imported together with it).
Everything is for the frozen `IsAdapted`/`timeInt`/`freqInt`/`pairing`, parameters `TriValid a b s' α`,
tiles in `triIdx s' α`, packets `φ t k` adapted with exponent `N ≥ 3` (the blueprint's `N ≥ 12` is not needed).

## Final statements

* **(a)** `sum_norm_sq_pairing_tree_le`: for `i ≠ k`, `IsTree a b i P T`, `↑P ⊆ triIdx s' α`,
  `∀ t ∈ T.tiles, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)`, `MemLp f 2`:
  `∑ t ∈ T.tiles, ‖pairing f (φ t k)‖ ^ 2 ≤ sameScaleConst N * ∫ x, ‖f x‖ ^ 2`.
* **(b, `i = k`)** `sizeDiag_le_of_maximalHLR_le` (`size_self_le_of_maximalHLR_le` for `size a b φ k k`):
  `Measurable f`, `0 ≤ μ`, `∀ t ∈ P', ∃ x ∈ timeInt t, maximalHLR f x ≤ ofReal μ`
  `⊢ sizeDiag φ k f P' ≤ ofReal (45 / 2 * μ)` (any `N ≥ 2`; no lattice hypothesis).
* **(b, `i ≠ k`)** `sizeOff_le_of_maximalHLR_sq_le` (`size_le_of_maximalHLR_sq_le` for `size a b φ i k`):
  `i ≠ k`, `↑P' ⊆ triIdx s' α`, `Measurable f`, `0 ≤ μ`,
  `∀ t ∈ P', ∃ x ∈ timeInt t, maximalHLR (fun y => ‖f y‖ₑ ^ 2) x ≤ ofReal (μ ^ 2)`
  `⊢ sizeOff a b φ i k f P' ≤ ofReal (orthSizeConst N * μ)`, `orthSizeConst N = √(16 sameScaleConst N + 720)`.
  No `L²` hypothesis on `f` is needed (local `L²` follows from the maximal-function hypothesis).
  The one-tree form is `sum_norm_sq_pairing_tree_le_of_maximalHLR_sq_le` (a single point `x₀ ∈ I_T`).
* The exact `∀`-statements of C9's local Props `TreeBessel sameScaleConst 3` and `SizeOffMax orthSizeConst 3`
  (`RefSize.lean`): `treeBessel_sameScaleConst`, `sizeOffMax_orthSizeConst`.

## Proofs (and checks of the blueprint)

(a): Schur test for the Gram matrix (`sum_norm_sq_pairing_le_of_row_sum_le`, duality + AM-GM, no Cauchy-Schwarz
in `L²` needed); the Gram matrix of an `i`-tree in slot `k ≠ i` is block diagonal in the scale
(C1(e), (G2)) and the same-scale row sums are `≤ sameScaleConst N` (G3).
(b, `i ≠ k`): `f = f 1_{8 I_T} + f 1_{(8 I_T)^c}` (`8 I_T` the closed interval of length `8|I_T|` centred at
`c(I_T)`); near part by (a) and `∫_{8I_T} |f|² ≤ 8 |I_T| M(|f|²)(x₀)`; far part by the weighted
Cauchy-Schwarz (`norm_pairing_sq_le_far`): `|⟨f 1_far, φ_t⟩|² ≤ B · 8 (|I_t|/|I_T|)²/(2N-3)` with
`B = (45/2)|I_T| μ²` from the `L²` weight lemma of `Maximal.lean`, then `∑_{t ∈ T} (|I_t|/|I_T|)² ≤ 6`
(`sum_sq_ratio_le_six`: at most `2^d` dyadic intervals of relative scale `d` times at most `3` tiles each).
Corrections to the blueprint: the exponents printed in step 3 (`2^{-(2N-5)d}` and `2^{-(2N-3)d}`) are
inconsistent, and not needed: the crude decay `(|I_t|/|I_T|)²` per tile already sums against the `3·2^d`
tiles of relative scale `d` (only `N ≥ 3` is used, and only through (G3)); `N ≥ 12` is not needed.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Tile

open PrimeBHT.Statements PrimeCarleson.Proof.Common

/-! ### Almost-orthogonality from row sums of the Gram matrix -/

theorem pairing_swap (f g : ℝ → ℂ) : pairing g f = (starRingEnd ℂ) (pairing f g) := by
  unfold pairing
  rw [← integral_conj]
  congr 1
  funext x
  simp [mul_comm]

theorem norm_pairing_swap (f g : ℝ → ℂ) : ‖pairing g f‖ = ‖pairing f g‖ := by
  rw [pairing_swap f g, Complex.norm_conj]

/-- `∫ |Σ c_i u_i|² = Σ_i Σ_j c_i conj(c_j) ⟨u_i, u_j⟩` for `u_i ∈ L²` (no orthogonality). -/
theorem integral_norm_sq_sum_eq {ι : Type*} (T : Finset ι) (u : ι → ℝ → ℂ) (c : ι → ℂ)
    (hu : ∀ i ∈ T, MemLp (u i) 2) :
    ((∫ x, ‖∑ i ∈ T, c i * u i x‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ T, ∑ j ∈ T, c i * (starRingEnd ℂ) (c j) * pairing (u i) (u j) := by
  have hint : ∀ i ∈ T, ∀ j ∈ T, Integrable (fun x => u i x * (starRingEnd ℂ) (u j x)) :=
    fun i hi j hj => integrable_mul_conj (hu i hi) (hu j hj)
  calc ((∫ x, ‖∑ i ∈ T, c i * u i x‖ ^ 2 : ℝ) : ℂ)
      = ∫ x, ∑ i ∈ T, ∑ j ∈ T,
          c i * (starRingEnd ℂ) (c j) * (u i x * (starRingEnd ℂ) (u j x)) := by
        rw [← integral_complex_ofReal]
        congr 1
        funext x
        rw [ofReal_norm_sq_eq_mul_conj, map_sum, Finset.sum_mul_sum]
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

/-- **Schur test for the Gram matrix.** If the rows of `(‖⟨u_i, u_j⟩‖)_{i,j ∈ T}` sum to at most `C`
(`C > 0`), then `Σ_i |⟨f, u_i⟩|² ≤ C ‖f‖₂²` for every `f ∈ L²`. -/
theorem sum_norm_sq_pairing_le_of_row_sum_le {ι : Type*} (T : Finset ι) (u : ι → ℝ → ℂ)
    (hu : ∀ i ∈ T, MemLp (u i) 2) {C : ℝ} (hC : 0 < C)
    (hrow : ∀ i ∈ T, ∑ j ∈ T, ‖pairing (u i) (u j)‖ ≤ C) {f : ℝ → ℂ} (hf : MemLp f 2) :
    ∑ i ∈ T, ‖pairing f (u i)‖ ^ 2 ≤ C * ∫ x, ‖f x‖ ^ 2 := by
  set γ : ι → ℂ := fun i => pairing f (u i) with hγ
  set S : ℝ := ∑ i ∈ T, ‖γ i‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  set F : ℝ → ℂ := fun x => ∑ i ∈ T, γ i * u i x with hF
  have hFm : MemLp F 2 := memLp_finsetSum T fun i hi => (hu i hi).const_mul (γ i)
  -- duality
  have hdual : ((S : ℝ) : ℂ) = ∫ x, f x * (starRingEnd ℂ) (F x) := by
    have hint : ∀ i ∈ T, Integrable (fun x => f x * (starRingEnd ℂ) (u i x)) :=
      fun i hi => integrable_mul_conj hf (hu i hi)
    calc ((S : ℝ) : ℂ) = ∑ i ∈ T, (starRingEnd ℂ) (γ i) * ∫ x, f x * (starRingEnd ℂ) (u i x) := by
          rw [hS, Complex.ofReal_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ofReal_norm_sq_eq_mul_conj, mul_comm]
          rfl
      _ = ∑ i ∈ T, ∫ x, (starRingEnd ℂ) (γ i) * (f x * (starRingEnd ℂ) (u i x)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_const_mul]
      _ = ∫ x, ∑ i ∈ T, (starRingEnd ℂ) (γ i) * (f x * (starRingEnd ℂ) (u i x)) := by
          rw [integral_finsetSum _ fun i hi => (hint i hi).const_mul _]
      _ = _ := by
          congr 1
          funext x
          simp only [hF, map_sum, map_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
  have hfF : Integrable (fun x => ‖f x‖ * ‖F x‖) := by
    refine (integrable_mul_conj hf hFm).norm.congr (ae_of_all _ fun x => ?_)
    simp only [norm_mul, Complex.norm_conj]
  have hS_le : S ≤ ∫ x, ‖f x‖ * ‖F x‖ := by
    calc S = ‖((S : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0]
      _ = ‖∫ x, f x * (starRingEnd ℂ) (F x)‖ := by rw [hdual]
      _ ≤ ∫ x, ‖f x * (starRingEnd ℂ) (F x)‖ := norm_integral_le_integral_norm _
      _ = ∫ x, ‖f x‖ * ‖F x‖ := by simp only [norm_mul, Complex.norm_conj]
  -- the Gram bound `‖F‖² ≤ C S`
  have hF2 : ∫ x, ‖F x‖ ^ 2 ≤ C * S := by
    have hexp := integral_norm_sq_sum_eq T u γ hu
    have hnn : 0 ≤ ∫ x, ‖F x‖ ^ 2 := integral_nonneg fun x => by positivity
    have h1 : ∫ x, ‖F x‖ ^ 2 ≤
        ∑ i ∈ T, ∑ j ∈ T, ‖γ i‖ * ‖γ j‖ * ‖pairing (u i) (u j)‖ := by
      calc ∫ x, ‖F x‖ ^ 2 = ‖((∫ x, ‖F x‖ ^ 2 : ℝ) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
        _ = ‖∑ i ∈ T, ∑ j ∈ T, γ i * (starRingEnd ℂ) (γ j) * pairing (u i) (u j)‖ := by
            rw [hexp]
        _ ≤ ∑ i ∈ T, ‖∑ j ∈ T, γ i * (starRingEnd ℂ) (γ j) * pairing (u i) (u j)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ i ∈ T, ∑ j ∈ T, ‖γ i * (starRingEnd ℂ) (γ j) * pairing (u i) (u j)‖ :=
            Finset.sum_le_sum fun i _ => norm_sum_le _ _
        _ = _ := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [norm_mul, norm_mul, Complex.norm_conj]
    have h2 : ∑ i ∈ T, ∑ j ∈ T, ‖γ i‖ * ‖γ j‖ * ‖pairing (u i) (u j)‖ ≤
        ∑ i ∈ T, ∑ j ∈ T, (‖γ i‖ ^ 2 / 2 + ‖γ j‖ ^ 2 / 2) * ‖pairing (u i) (u j)‖ := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      nlinarith [sq_nonneg (‖γ i‖ - ‖γ j‖)]
    have h3 : ∑ i ∈ T, ∑ j ∈ T, (‖γ i‖ ^ 2 / 2 + ‖γ j‖ ^ 2 / 2) * ‖pairing (u i) (u j)‖ =
        ∑ i ∈ T, ‖γ i‖ ^ 2 * ∑ j ∈ T, ‖pairing (u i) (u j)‖ := by
      simp only [add_mul, Finset.sum_add_distrib]
      have hsw : ∑ i ∈ T, ∑ j ∈ T, ‖γ j‖ ^ 2 / 2 * ‖pairing (u i) (u j)‖ =
          ∑ i ∈ T, ∑ j ∈ T, ‖γ i‖ ^ 2 / 2 * ‖pairing (u i) (u j)‖ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [norm_pairing_swap (u i) (u j)]
      rw [hsw, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [← Finset.mul_sum]
      ring
    have h4 : ∑ i ∈ T, ‖γ i‖ ^ 2 * ∑ j ∈ T, ‖pairing (u i) (u j)‖ ≤ ∑ i ∈ T, ‖γ i‖ ^ 2 * C :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hrow i hi) (by positivity)
    calc ∫ x, ‖F x‖ ^ 2 ≤ _ := h1
      _ ≤ _ := h2
      _ = _ := h3
      _ ≤ ∑ i ∈ T, ‖γ i‖ ^ 2 * C := h4
      _ = C * S := by rw [hS, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  -- AM-GM
  have hfi : Integrable (fun x => ‖f x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hFi : Integrable (fun x => ‖F x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hFm.aestronglyMeasurable).1 hFm
  have hpt : ∀ x, ‖f x‖ * ‖F x‖ ≤ C / 2 * ‖f x‖ ^ 2 + 1 / (2 * C) * ‖F x‖ ^ 2 :=
    fun x => mul_le_half_sq_add hC
  have hmain : S ≤ C / 2 * (∫ x, ‖f x‖ ^ 2) + 1 / (2 * C) * (C * S) := by
    calc S ≤ ∫ x, ‖f x‖ * ‖F x‖ := hS_le
      _ ≤ ∫ x, (C / 2 * ‖f x‖ ^ 2 + 1 / (2 * C) * ‖F x‖ ^ 2) :=
          integral_mono hfF ((hfi.const_mul _).add (hFi.const_mul _)) hpt
      _ = C / 2 * (∫ x, ‖f x‖ ^ 2) + 1 / (2 * C) * ∫ x, ‖F x‖ ^ 2 := by
          rw [integral_add (hfi.const_mul _) (hFi.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ _ := by gcongr
  have hAS : 1 / (2 * C) * (C * S) = S / 2 := by field_simp
  rw [hAS] at hmain
  show S ≤ C * ∫ x, ‖f x‖ ^ 2
  have : S ≤ C * ∫ x, ‖f x‖ ^ 2 := by linarith
  exact this

/-! ### (a) Orthogonality of an `i`-tree in the slot `k ≠ i` -/

theorem sameScaleConst_pos {N : ℕ} (hN : 3 ≤ N) : 0 < sameScaleConst N := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hf : Summable fun j : ℤ => (1 + |(j : ℝ)|) ^ (-((N : ℝ) - 1)) :=
    summable_one_add_abs_int_rpow_neg (by linarith)
  have h0 : 0 < ∑' j : ℤ, (1 + |(j : ℝ)|) ^ (-((N : ℝ) - 1)) := by
    refine lt_of_lt_of_le ?_ (hf.le_tsum 0 (fun j _ => by positivity))
    simp
  have hg : 0 < gramConst N := by
    unfold gramConst
    exact div_pos (by positivity) (by linarith)
  exact mul_pos hg h0

/-- **(a) Tree orthogonality** (blueprint C8 (a), BD26 `l:orhogonality`, unshifted). For an `i`-tree `T`
in a family `P ⊆ Idx_ν`, a slot `k ≠ i`, packets `φ_{t,k}` adapted with exponent `N ≥ 3` and `f ∈ L²`:
`∑_{t ∈ T} |⟨f, φ_{t,k}⟩|² ≤ C_N ‖f‖₂²` with `C_N = sameScaleConst N`. Proof: the Gram matrix of the
packets is block diagonal in the scale (C1 (e): different scales have disjoint `ω_{t,k}`, hence
`⟨φ_{t,k}, φ_{t',k}⟩ = 0` by (G2)), and the same-scale row sums are at most `C_N` by (G3). -/
theorem sum_norm_sq_pairing_tree_le {N : ℕ} (hN : 3 ≤ N) {a b s' α : ℤ} (hν : TriValid a b s' α)
    {i k : Fin 3} (hik : i ≠ k) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) {P : Finset (ℤ × ℤ × ℤ)}
    (hP : (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α) {T : TreeData} (hT : IsTree a b i P T)
    (hφ : ∀ t ∈ T.tiles, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) {f : ℝ → ℂ}
    (hf : MemLp f 2) :
    ∑ t ∈ T.tiles, ‖pairing f (φ t k)‖ ^ 2 ≤ sameScaleConst N * ∫ x, ‖f x‖ ^ 2 := by
  classical
  have hTP : ∀ t ∈ T.tiles, t ∈ triIdx s' α := fun t ht => hP (hT.subset ht)
  have hmem : ∀ t ∈ T.tiles, MemLp (φ t k) 2 := fun t ht =>
    (IsAdapted.memLp_two_and_integral_sq_le (by omega) (hφ t ht)
      (toReal_volume_timeInt_pos t)).1
  refine sum_norm_sq_pairing_le_of_row_sum_le T.tiles (fun t => φ t k) hmem
    (sameScaleConst_pos hN) (fun t ht => ?_) hf
  have hrow : ∑ t' ∈ T.tiles, ‖pairing (φ t k) (φ t' k)‖ =
      ∑ t' ∈ T.tiles with t'.1 = t.1, ‖pairing (φ t k) (φ t' k)‖ := by
    symm
    refine Finset.sum_filter_of_ne fun t' ht' hne => ?_
    by_contra hs
    apply hne
    have hdisj := hT.disjoint_freqInt_of_scale_ne hν hik hP ht ht' (fun h => hs h.symm)
    rw [pairing_eq_zero_of_disjoint (hφ t ht) (hφ t' ht') (isBounded_freqInt a b k t') hdisj,
      norm_zero]
  rw [hrow]
  exact sum_norm_pairing_sameScale_le hN k φ T.tiles hTP hφ ht

/-! ### (b), diagonal: `size_{k,k}` by the maximal function -/

/-! ### Counting the tiles of a tree by relative scale -/

/-- **Packing of a tree.** `∑_{t ∈ T} (|I_t|/|I_T|)² ≤ 6`: the tiles of relative scale `d = S - s(t) ≥ 0` have
time intervals among the `2^d` dyadic subintervals of `I_T` of that scale, at most `3` tiles share an
interval (`IsTree.card_filter_timeInt_le_three`), and `∑_d 2^d 4^{-d} ≤ 2`. -/
theorem sum_sq_ratio_le_six {a b s' α : ℤ} {i : Fin 3} {P : Finset (ℤ × ℤ × ℤ)}
    (hP : (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α) {T : TreeData} (hT : IsTree a b i P T) :
    ∑ t ∈ T.tiles, ((2 : ℝ) ^ t.1 / (2 : ℝ) ^ T.top.1) ^ 2 ≤ 6 := by
  classical
  set S : ℤ := T.top.1 with hS
  set V : ℤ := T.top.2 with hV
  have hsc : ∀ t ∈ T.tiles, t.1 ≤ S := fun t ht =>
    scale_le_of_dyadicInt_subset (hT.timeInt_subset ht)
  set dd : ℤ × ℤ × ℤ → ℕ := fun t => (S - t.1).toNat with hdd
  set mm : ℤ × ℤ × ℤ → ℕ := fun t => (t.2.1 - 2 ^ (dd t) * V).toNat with hmm
  set ψ : ℤ × ℤ × ℤ → ℕ × ℕ := fun t => (dd t, mm t) with hψ
  have hdd_eq : ∀ t ∈ T.tiles, ((dd t : ℕ) : ℤ) = S - t.1 := fun t ht =>
    Int.toNat_of_nonneg (by have := hsc t ht; omega)
  -- the index bound
  have hidx : ∀ t ∈ T.tiles, 0 ≤ t.2.1 - 2 ^ (dd t) * V ∧ t.2.1 - 2 ^ (dd t) * V < 2 ^ (dd t) := by
    intro t ht
    have hmem : (2 : ℝ) ^ t.1 * t.2.1 ∈ timeInt t :=
      ⟨le_rfl, by have := timeInt_lt t; exact this⟩
    have h := hT.timeInt_subset ht hmem
    obtain ⟨h1, h2⟩ := h
    have hp : (0 : ℝ) < (2 : ℝ) ^ t.1 := zpow_pos (by norm_num) _
    have hS' : (2 : ℝ) ^ S = (2 : ℝ) ^ t.1 * (2 : ℝ) ^ (dd t) := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num), hdd_eq t ht]; congr 1; ring
    rw [hS'] at h1 h2
    have h1' : (2 : ℝ) ^ (dd t) * V ≤ t.2.1 := by
      have : (2 : ℝ) ^ t.1 * ((2 : ℝ) ^ (dd t) * V) ≤ (2 : ℝ) ^ t.1 * t.2.1 := by
        calc _ = (2 : ℝ) ^ t.1 * (2 : ℝ) ^ (dd t) * V := by ring
          _ ≤ _ := h1
      exact le_of_mul_le_mul_left this hp
    have h2' : (t.2.1 : ℝ) < (2 : ℝ) ^ (dd t) * (V + 1) := by
      have : (2 : ℝ) ^ t.1 * (t.2.1 : ℝ) < (2 : ℝ) ^ t.1 * ((2 : ℝ) ^ (dd t) * (V + 1)) := by
        calc _ < _ := h2
          _ = _ := by ring
      exact lt_of_mul_lt_mul_left this hp.le
    have h1'' : (2 : ℤ) ^ (dd t) * V ≤ t.2.1 := by exact_mod_cast h1'
    have h2'' : t.2.1 < (2 : ℤ) ^ (dd t) * (V + 1) := by exact_mod_cast h2'
    constructor <;> nlinarith
  have hmm_lt : ∀ t ∈ T.tiles, mm t < 2 ^ dd t := by
    intro t ht
    obtain ⟨h0, h1⟩ := hidx t ht
    have : ((mm t : ℕ) : ℤ) = t.2.1 - 2 ^ (dd t) * V := Int.toNat_of_nonneg h0
    have h2 : ((mm t : ℕ) : ℤ) < ((2 ^ dd t : ℕ) : ℤ) := by push_cast; omega
    exact_mod_cast h2
  have hψinj : ∀ t ∈ T.tiles, ∀ t' ∈ T.tiles, ψ t = ψ t' → timeInt t = timeInt t' := by
    intro t ht t' ht' h
    have hd : dd t = dd t' := congrArg Prod.fst h
    have hm : mm t = mm t' := congrArg Prod.snd h
    rw [timeInt_eq_iff]
    have e1 := hdd_eq t ht
    have e2 := hdd_eq t' ht'
    have hs : t.1 = t'.1 := by rw [hd] at e1; omega
    refine ⟨hs, ?_⟩
    obtain ⟨h0, _⟩ := hidx t ht
    obtain ⟨h0', _⟩ := hidx t' ht'
    have a1 : ((mm t : ℕ) : ℤ) = t.2.1 - 2 ^ (dd t) * V := Int.toNat_of_nonneg h0
    have a2 : ((mm t' : ℕ) : ℤ) = t'.2.1 - 2 ^ (dd t') * V := Int.toNat_of_nonneg h0'
    rw [hm] at a1
    rw [hd] at a1
    omega
  -- weights
  set w : ℕ × ℕ → ℝ := fun p => (1 / 4 : ℝ) ^ p.1 with hw
  have hterm : ∀ t ∈ T.tiles, ((2 : ℝ) ^ t.1 / (2 : ℝ) ^ S) ^ 2 = w (ψ t) := by
    intro t ht
    simp only [hw, hψ]
    have h1 : (2 : ℝ) ^ t.1 / (2 : ℝ) ^ S = (1 / 2 : ℝ) ^ (dd t) := by
      rw [div_eq_iff (zpow_pos (by norm_num) _).ne', one_div, inv_pow, ← zpow_natCast,
        ← zpow_neg, ← zpow_add₀ (by norm_num), hdd_eq t ht]
      congr 1
      ring
    rw [h1, ← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [Finset.sum_congr rfl hterm]
  set Sf : Finset (ℕ × ℕ) := T.tiles.image ψ with hSf
  have hmaps : ∀ t ∈ T.tiles, ψ t ∈ Sf := fun t ht => Finset.mem_image_of_mem ψ ht
  have hcard : ∀ x ∈ Sf, (T.tiles.filter fun t => ψ t = x).card ≤ 3 := by
    intro x hx
    obtain ⟨t₁, ht₁, rfl⟩ := Finset.mem_image.1 hx
    refine le_trans (Finset.card_le_card ?_) (hT.card_filter_timeInt_le_three hP (timeInt t₁))
    intro t ht
    rw [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, hψinj t ht.1 t₁ ht₁ ht.2⟩
  have hw0 : ∀ x ∈ Sf, 0 ≤ w x := fun x _ => by simp only [hw]; positivity
  have h3 : ∑ t ∈ T.tiles, w (ψ t) ≤ 3 * ∑ x ∈ Sf, w x := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
    refine Finset.sum_le_sum fun x hx => ?_
    calc ∑ t ∈ T.tiles with ψ t = x, w (ψ t) = ∑ t ∈ T.tiles with ψ t = x, w x :=
          Finset.sum_congr rfl fun t ht => by rw [(Finset.mem_filter.1 ht).2]
      _ = (T.tiles.filter fun t => ψ t = x).card * w x := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 3 * w x := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard x hx) (hw0 x hx)
  -- sum over Sf
  set D : ℕ := Sf.sup Prod.fst + 1 with hD
  have hSf_maps : ∀ x ∈ Sf, x.1 ∈ Finset.range D := by
    intro x hx
    rw [Finset.mem_range]
    have : x.1 ≤ Sf.sup Prod.fst := Finset.le_sup (f := Prod.fst) hx
    omega
  have hSf_lt : ∀ x ∈ Sf, x.2 < 2 ^ x.1 := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
    exact hmm_lt t ht
  have h4 : ∑ x ∈ Sf, w x ≤ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to hSf_maps]
    have hfib : ∀ d ∈ Finset.range D, ∑ x ∈ Sf with x.1 = d, w x ≤ (1 / 2 : ℝ) ^ d := by
      intro d hd
      have hc : (Sf.filter fun x => x.1 = d).card ≤ 2 ^ d := by
        have := Finset.card_le_card_of_injOn (fun x : ℕ × ℕ => x.2) (s := Sf.filter fun x => x.1 = d)
          (t := Finset.range (2 ^ d)) (fun x hx => by
            rw [Finset.mem_coe, Finset.mem_filter] at hx
            rw [Finset.mem_coe, Finset.mem_range]
            have := hSf_lt x hx.1
            rw [hx.2] at this
            exact this) (fun x hx y hy hxy => by
            rw [Finset.mem_coe, Finset.mem_filter] at hx hy
            exact Prod.ext (hx.2.trans hy.2.symm) hxy)
        simpa using this
      calc ∑ x ∈ Sf with x.1 = d, w x = ∑ x ∈ Sf with x.1 = d, (1 / 4 : ℝ) ^ d :=
            Finset.sum_congr rfl fun x hx => by simp only [hw, (Finset.mem_filter.1 hx).2]
        _ = (Sf.filter fun x => x.1 = d).card * (1 / 4 : ℝ) ^ d := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 2 ^ d * (1 / 4 : ℝ) ^ d :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
        _ = (1 / 2 : ℝ) ^ d := by rw [← mul_pow]; norm_num
    exact (Finset.sum_le_sum hfib).trans (sum_geometric_two_le D)
  linarith


/-! ### (b), off-diagonal: the far part of the near/far split -/

/-- Cauchy-Schwarz for `ℝ≥0∞`-valued integrals. -/
theorem sq_lintegral_mul_le {u v : ℝ → ℝ≥0∞} (hu : Measurable u) (hv : Measurable v) :
    (∫⁻ y, u y * v y) ^ 2 ≤ (∫⁻ y, u y ^ 2) * ∫⁻ y, v y ^ 2 := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    hu.aemeasurable hv.aemeasurable
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  have h2 := pow_le_pow_left' h 2
  rw [mul_pow] at h2
  have e1 : ((∫⁻ y, u y ^ 2) ^ (1 / (2 : ℝ))) ^ 2 = ∫⁻ y, u y ^ 2 := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have e2 : ((∫⁻ y, v y ^ 2) ^ (1 / (2 : ℝ))) ^ 2 = ∫⁻ y, v y ^ 2 := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  rw [e1, e2] at h2
  exact h2

/-- `∫⁻ ‖g‖ₑ² ≤ ofReal B` gives the real bound `∫ ‖g‖² ≤ B`. -/
theorem integral_norm_sq_le_of_lintegral_le {g : ℝ → ℂ} (hg : Measurable g) {B : ℝ} (hB : 0 ≤ B)
    (h : ∫⁻ y, ‖g y‖ₑ ^ 2 ≤ ENNReal.ofReal B) : ∫ y, ‖g y‖ ^ 2 ≤ B := by
  have hnn : 0 ≤ᵐ[volume] fun y : ℝ => ‖g y‖ ^ 2 := Eventually.of_forall fun y => by positivity
  have hmeas : Measurable fun y : ℝ => ‖g y‖ ^ 2 := hg.norm.pow_const 2
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hB ?_
  refine le_trans (le_of_eq ?_) h
  refine lintegral_congr fun y => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The pointwise estimate behind the far part: for `y` with `|y - c_J| > 4 |J|`, `|c_I - c_J| ≤ |J|/2`
and `|φ(y)| ≤ |I|^{-1/2} (1 + |y - c_I|/|I|)^{-N}`,
`(|φ(y)| (1 + |y - c_J|/|J|))² ≤ 4 (|I|/|J|)² |I|^{-1} (1 + |y - c_I|/|I|)^{-(2N-2)}`. -/
theorem far_pointwise {N : ℕ} {L ℓ cI cJ y a : ℝ} (hL : 0 < L) (hℓ : 0 < ℓ) (ha : 0 ≤ a)
    (hc : |cI - cJ| ≤ L / 2) (hy : 4 * L < |y - cJ|)
    (hφ : a ≤ ℓ ^ (-(1 / 2 : ℝ)) * (1 + |y - cI| / ℓ) ^ (-(N : ℝ))) :
    (a * (1 + |y - cJ| / L)) ^ 2 ≤
      4 * (ℓ / L) ^ 2 * ℓ⁻¹ * (1 + |y - cI| / ℓ) ^ (-(2 * (N : ℝ) - 2)) := by
  set s := |y - cI| with hs
  set q := 1 + s / ℓ with hq
  have hs0 : 0 ≤ s := abs_nonneg _
  have hσ0 : 0 ≤ s / ℓ := by positivity
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  have h1 : |y - cJ| ≤ s + L / 2 := by
    calc |y - cJ| = |(y - cI) + (cI - cJ)| := by ring_nf
      _ ≤ |y - cI| + |cI - cJ| := abs_add_le _ _
      _ ≤ s + L / 2 := by rw [hs]; linarith
  have h2 : 7 / 2 * L < s := by linarith
  set ρ := ℓ / L with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρσ : s / L = ρ * (s / ℓ) := by rw [hρ]; field_simp
  have h3 : 7 / 2 < ρ * (s / ℓ) := by
    rw [← hρσ, lt_div_iff₀ hL]; linarith
  have hW : 1 + |y - cJ| / L ≤ 10 / 7 * (ρ * q) := by
    have e1 : |y - cJ| / L ≤ (s + L / 2) / L := div_le_div_of_nonneg_right h1 hL.le
    have e2 : (s + L / 2) / L = s / L + 1 / 2 := by field_simp
    have e3 : s / ℓ ≤ q := by rw [hq]; linarith
    have e4 : ρ * (s / ℓ) ≤ ρ * q := mul_le_mul_of_nonneg_left e3 hρ0.le
    linarith
  have hW0 : 0 ≤ 1 + |y - cJ| / L := by positivity
  have hq2 : (q ^ (-(N : ℝ))) ^ 2 * q ^ 2 = q ^ (-(2 * (N : ℝ) - 2)) := by
    rw [← Real.rpow_natCast (q ^ (-(N : ℝ))) 2, ← Real.rpow_mul hq0.le,
      ← Real.rpow_natCast q 2, ← Real.rpow_add hq0]
    congr 1
    push_cast
    ring
  have hl2 : (ℓ ^ (-(1 / 2 : ℝ))) ^ 2 = ℓ⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hℓ.le]
    norm_num
    exact Real.rpow_neg_one _
  have hφ2 : a ^ 2 ≤ ℓ⁻¹ * (q ^ (-(N : ℝ))) ^ 2 := by
    calc a ^ 2 ≤ (ℓ ^ (-(1 / 2 : ℝ)) * q ^ (-(N : ℝ))) ^ 2 := pow_le_pow_left₀ ha hφ 2
      _ = _ := by rw [mul_pow, hl2]
  have hW2 : (1 + |y - cJ| / L) ^ 2 ≤ 4 * ρ ^ 2 * q ^ 2 := by
    calc (1 + |y - cJ| / L) ^ 2 ≤ (10 / 7 * (ρ * q)) ^ 2 := pow_le_pow_left₀ hW0 hW 2
      _ = 100 / 49 * (ρ ^ 2 * q ^ 2) := by ring
      _ ≤ 4 * ρ ^ 2 * q ^ 2 := by nlinarith [mul_nonneg (sq_nonneg ρ) (sq_nonneg q)]
  have hq20 : 0 ≤ (q ^ (-(N : ℝ))) ^ 2 := sq_nonneg _
  calc (a * (1 + |y - cJ| / L)) ^ 2 = a ^ 2 * (1 + |y - cJ| / L) ^ 2 := by rw [mul_pow]
    _ ≤ (ℓ⁻¹ * (q ^ (-(N : ℝ))) ^ 2) * (4 * ρ ^ 2 * q ^ 2) :=
        mul_le_mul hφ2 hW2 (sq_nonneg _) (by positivity)
    _ = 4 * ρ ^ 2 * ℓ⁻¹ * ((q ^ (-(N : ℝ))) ^ 2 * q ^ 2) := by ring
    _ = _ := by rw [hq2]


/-- **The far part for one packet.** Let `φ` be adapted to `(I, ω)` with exponent `N ≥ 2`, `J` an interval
with `|c(I) - c(J)| ≤ |J|/2`, and `g` measurable vanishing on `{|y - c(J)| ≤ 4|J|}` (so `g` lives off
`8J`), with `∫ (1 + |y - c(J)|/|J|)^{-2} |g|² ≤ B`. Then
`|⟨g, φ⟩|² ≤ B · 8 (|I|/|J|)² / (2N - 3)`. (Cauchy-Schwarz with the weight `(1 + |y - c(J)|/|J|)^{±1}`;
the factor `(|I|/|J|)²` is the decay of the packet, as seen from `J`, off `8J`.) -/
theorem norm_pairing_sq_le_far {N : ℕ} (hN : 2 ≤ N) {I J ω : Set ℝ} {φ : ℝ → ℂ}
    (hφ : IsAdapted N I ω φ) (hIL : 0 < (volume I).toReal) (hJL : 0 < (volume J).toReal)
    (hc : |intervalCentre I - intervalCentre J| ≤ (volume J).toReal / 2)
    {g : ℝ → ℂ} (hg : Measurable g)
    (hg0 : ∀ y, |y - intervalCentre J| ≤ 4 * (volume J).toReal → g y = 0)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∫⁻ y, ENNReal.ofReal ((1 + |y - intervalCentre J| / (volume J).toReal) ^ (-2 : ℤ)) *
      ‖g y‖ₑ ^ 2 ≤ ENNReal.ofReal B) :
    Integrable (fun y => g y * (starRingEnd ℂ) (φ y)) ∧ ‖pairing g φ‖ ^ 2 ≤
      B * (8 * ((volume I).toReal / (volume J).toReal) ^ 2 / (2 * (N : ℝ) - 3)) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set L := (volume J).toReal with hLdef
  set ℓ := (volume I).toReal with hℓdef
  set cJ := intervalCentre J with hcJ
  set cI := intervalCentre I with hcI
  obtain ⟨Wr, hWr⟩ : ∃ Wr : ℝ → ℝ, ∀ y, Wr y = 1 + |y - cJ| / L := ⟨_, fun _ => rfl⟩
  have hWr1 : ∀ y, 1 ≤ Wr y := fun y => by
    rw [hWr]; have : 0 ≤ |y - cJ| / L := by positivity
    linarith
  have hWr0 : ∀ y, 0 < Wr y := fun y => lt_of_lt_of_le one_pos (hWr1 y)
  have hWrc : Continuous Wr := by
    have : Wr = fun y => 1 + |y - cJ| / L := funext hWr
    rw [this]; fun_prop
  obtain ⟨far, hfar⟩ : ∃ far : Set ℝ, far = {y | 4 * L < |y - cJ|} := ⟨_, rfl⟩
  have hfarm : MeasurableSet far := by
    rw [hfar]; exact measurableSet_lt measurable_const (by fun_prop)
  obtain ⟨u, hu⟩ : ∃ u : ℝ → ℝ≥0∞, u = fun y => ‖g y‖ₑ * ENNReal.ofReal (Wr y)⁻¹ := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ → ℝ≥0∞,
      v = far.indicator (fun y => ‖φ y‖ₑ * ENNReal.ofReal (Wr y)) := ⟨_, rfl⟩
  have hum : Measurable u := by
    rw [hu]; exact hg.enorm.mul (ENNReal.measurable_ofReal.comp hWrc.measurable.inv)
  have hvm : Measurable v := by
    rw [hv]
    exact ((IsAdapted.continuous hφ).measurable.enorm.mul
      (ENNReal.measurable_ofReal.comp hWrc.measurable)).indicator hfarm
  -- step A
  have hA : ‖pairing g φ‖ₑ ≤ ∫⁻ y, ‖g y‖ₑ * ‖φ y‖ₑ := by
    unfold pairing
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine lintegral_mono fun y => le_of_eq ?_
    rw [enorm_mul, RCLike.enorm_conj]
  have hpt : ∀ y, ‖g y‖ₑ * ‖φ y‖ₑ = u y * v y := by
    intro y
    by_cases hy : y ∈ far
    · rw [hu, hv, Set.indicator_of_mem hy]
      have : ENNReal.ofReal (Wr y)⁻¹ * ENNReal.ofReal (Wr y) = 1 := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 (hWr0 y).le), inv_mul_cancel₀ (hWr0 y).ne',
          ENNReal.ofReal_one]
      calc ‖g y‖ₑ * ‖φ y‖ₑ = ‖g y‖ₑ * ‖φ y‖ₑ * (ENNReal.ofReal (Wr y)⁻¹ * ENNReal.ofReal (Wr y)) := by
            rw [this, mul_one]
        _ = _ := by ring
    · have h0 : g y = 0 := hg0 y (by rw [hfar] at hy; exact not_lt.1 hy)
      rw [hu]
      simp [h0]
  -- step D
  have hD : ∫⁻ y, u y ^ 2 ≤ ENNReal.ofReal B := by
    refine le_trans (le_of_eq ?_) hB
    refine lintegral_congr fun y => ?_
    rw [hu]
    simp only
    rw [mul_pow, mul_comm, ← ENNReal.ofReal_pow (inv_nonneg.2 (hWr0 y).le)]
    congr 2
    rw [← hWr y, zpow_neg, inv_pow]
    norm_cast
  -- step E
  have hp : 1 < 2 * (N : ℝ) - 2 := by linarith
  have h3 : (2 * (N : ℝ) - 3) ≠ 0 := by intro h; linarith
  set K : ℝ := 8 * (ℓ / L) ^ 2 / (2 * (N : ℝ) - 3) with hK
  have hK0 : 0 ≤ K := div_nonneg (by positivity) (by linarith)
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℝ, h = fun y =>
      4 * (ℓ / L) ^ 2 * ℓ⁻¹ * (1 + |y - cI| / ℓ) ^ (-(2 * (N : ℝ) - 2)) := ⟨_, rfl⟩
  have hv2 : ∀ y, v y ^ 2 ≤ ENNReal.ofReal (h y) := by
    intro y
    by_cases hy : y ∈ far
    · rw [hv, Set.indicator_of_mem hy, hh]
      simp only
      rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
        ← ENNReal.ofReal_pow (mul_nonneg (norm_nonneg _) (hWr0 y).le)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hWr]
      exact far_pointwise hJL hIL (norm_nonneg _) hc (by rw [hfar] at hy; exact hy)
        (IsAdapted.norm_le hφ y)
    · rw [hv, Set.indicator_of_notMem hy]
      simp
  have hint : Integrable h := by
    rw [hh]
    exact (integrable_one_add_abs_sub_div_rpow hp cI hIL).const_mul _
  have hhnn : 0 ≤ᵐ[volume] h := ae_of_all _ fun y => by rw [hh]; positivity
  have hval : ∫ y, h y = K := by
    rw [hh]
    simp only
    rw [integral_const_mul, integral_one_add_abs_sub_div_rpow hp cI hIL, hK]
    have e : 2 * (N : ℝ) - 2 - 1 = 2 * (N : ℝ) - 3 := by ring
    rw [e]
    field_simp
    norm_num
  have hE : ∫⁻ y, v y ^ 2 ≤ ENNReal.ofReal K := by
    calc ∫⁻ y, v y ^ 2 ≤ ∫⁻ y, ENNReal.ofReal (h y) := lintegral_mono hv2
      _ = ENNReal.ofReal (∫ y, h y) := (ofReal_integral_eq_lintegral_ofReal hint hhnn).symm
      _ = ENNReal.ofReal K := by rw [hval]
  have hCS : (∫⁻ y, ‖g y‖ₑ * ‖φ y‖ₑ) ^ 2 ≤ ENNReal.ofReal B * ENNReal.ofReal K := by
    calc (∫⁻ y, ‖g y‖ₑ * ‖φ y‖ₑ) ^ 2 = (∫⁻ y, u y * v y) ^ 2 := by simp_rw [hpt]
      _ ≤ (∫⁻ y, u y ^ 2) * ∫⁻ y, v y ^ 2 := sq_lintegral_mul_le hum hvm
      _ ≤ ENNReal.ofReal B * ENNReal.ofReal K := mul_le_mul' hD hE
  refine ⟨?_, ?_⟩
  · have hfin : (∫⁻ y, ‖g y‖ₑ * ‖φ y‖ₑ) ^ 2 < ⊤ :=
      lt_of_le_of_lt hCS (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    have hfin' : ∫⁻ y, ‖g y‖ₑ * ‖φ y‖ₑ < ⊤ := by
      by_contra hcon
      rw [not_lt, top_le_iff] at hcon
      rw [hcon] at hfin
      simp at hfin
    refine ⟨(hg.mul (Complex.continuous_conj.measurable.comp
      (IsAdapted.continuous hφ).measurable)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt (le_of_eq ?_) hfin'
    refine lintegral_congr fun y => ?_
    rw [enorm_mul, RCLike.enorm_conj]
  · have hfin : ENNReal.ofReal (‖pairing g φ‖ ^ 2) ≤ ENNReal.ofReal (B * K) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.ofReal_mul hB0]
      calc ‖pairing g φ‖ₑ ^ 2 ≤ (∫⁻ y, ‖g y‖ₑ * ‖φ y‖ₑ) ^ 2 := by gcongr
        _ ≤ _ := hCS
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB0 hK0)).1 hfin


/-! ### (b), off-diagonal: the near/far split for a tree -/

/-- The constant of (b), `i ≠ k`: `√(16 C_N + 720)` with `C_N = sameScaleConst N`. -/
noncomputable def orthSizeConst (N : ℕ) : ℝ := Real.sqrt (16 * sameScaleConst N + 720)

theorem orthSizeConst_nonneg (N : ℕ) : 0 ≤ orthSizeConst N := Real.sqrt_nonneg _

/-- The centre of a tile's time interval lies in it, hence within `|I_T|/2` of the centre of `I_T`. -/
theorem abs_intervalCentre_timeInt_sub_le {a b : ℤ} {i : Fin 3} {P : Finset (ℤ × ℤ × ℤ)}
    {T : TreeData} (hT : IsTree a b i P T) {t : ℤ × ℤ × ℤ} (ht : t ∈ T.tiles) :
    |intervalCentre (timeInt t) - intervalCentre T.topInt| ≤ (volume T.topInt).toReal / 2 := by
  have hmem : intervalCentre (timeInt t) ∈ timeInt t := by
    rw [intervalCentre_timeInt]
    have hp : (0 : ℝ) < (2 : ℝ) ^ t.1 := zpow_pos (by norm_num) _
    constructor <;> nlinarith
  exact abs_sub_intervalCentre_le_of_mem Set.ordConnected_Ico T.toReal_volume_topInt_pos
    (hT.timeInt_subset ht hmem)

/-- **(b), `i ≠ k`, one tree.** Let `T` be an `i`-tree in `P ⊆ Idx_ν`, `k ≠ i`, packets adapted with
exponent `N ≥ 3`, `f ∈ L²` measurable, and `x₀ ∈ I_T` with `M(|f|²)(x₀) ≤ μ²`. Then
`∑_{t ∈ T} |⟨f, φ_{t,k}⟩|² ≤ (C μ)² |I_T|` (BD26 `l:jneqk`, blueprint C8 step 3: `f = f 1_{8 I_T} +
f 1_{(8 I_T)^c}`; near part by (a), far part by the weighted Cauchy-Schwarz bound and the count of
tiles by relative scale). -/
theorem sum_norm_sq_pairing_tree_le_of_maximalHLR_sq_le {N : ℕ} (hN : 3 ≤ N) {a b s' α : ℤ}
    (hν : TriValid a b s' α) {i k : Fin 3} (hik : i ≠ k)
    (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) {P : Finset (ℤ × ℤ × ℤ)}
    (hP : (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α) {T : TreeData} (hT : IsTree a b i P T)
    (hφ : ∀ t ∈ T.tiles, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) {f : ℝ → ℂ}
    (hf : Measurable f) {μ : ℝ} {x₀ : ℝ} (hx₀ : x₀ ∈ T.topInt)
    (hM : maximalHLR (fun y => ‖f y‖ₑ ^ 2) x₀ ≤ ENNReal.ofReal (μ ^ 2)) :
    ∑ t ∈ T.tiles, ‖pairing f (φ t k)‖ ^ 2 ≤
      (orthSizeConst N * μ) ^ 2 * (volume T.topInt).toReal := by
  classical
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  set L := (volume T.topInt).toReal with hL
  have hL0 : 0 < L := T.toReal_volume_topInt_pos
  have hJoc : T.topInt.OrdConnected := Set.ordConnected_Ico
  set cT := intervalCentre T.topInt with hcT
  obtain ⟨Nr, hNr⟩ : ∃ Nr : Set ℝ, Nr = Set.Icc (cT - 4 * L) (cT + 4 * L) := ⟨_, rfl⟩
  have hNrm : MeasurableSet Nr := by rw [hNr]; exact measurableSet_Icc
  obtain ⟨fn, hfn⟩ : ∃ fn : ℝ → ℂ, fn = Nr.indicator f := ⟨_, rfl⟩
  obtain ⟨ff, hff⟩ : ∃ ff : ℝ → ℂ, ff = Nrᶜ.indicator f := ⟨_, rfl⟩
  have hfnm : Measurable fn := by rw [hfn]; exact hf.indicator hNrm
  have hffm : Measurable ff := by rw [hff]; exact hf.indicator hNrm.compl
  have hsplit : ∀ y, f y = fn y + ff y := fun y => by
    rw [hfn, hff]; exact (congrFun (Set.indicator_self_add_compl Nr f) y).symm
  have hx0c : |x₀ - cT| ≤ L / 2 := abs_sub_intervalCentre_le_of_mem hJoc hL0 hx₀
  have hx0Nr : x₀ ∈ Nr := by
    rw [hNr]
    constructor <;> linarith [abs_le.1 hx0c]
  -- near part
  have hnear_l : ∫⁻ y, ‖fn y‖ₑ ^ 2 ≤ ENNReal.ofReal (8 * L * μ ^ 2) := by
    have e1 : ∫⁻ y, ‖fn y‖ₑ ^ 2 = ∫⁻ y in Nr, ‖f y‖ₑ ^ 2 := by
      rw [← lintegral_indicator hNrm]
      refine lintegral_congr fun y => ?_
      by_cases hy : y ∈ Nr <;> simp [hfn, hy]
    rw [e1, hNr]
    have hab : cT - 4 * L < cT + 4 * L := by linarith
    have h := lintegral_Icc_le_mul_maximalHLR (fun y => ‖f y‖ₑ ^ 2) hab (hNr ▸ hx0Nr)
    simp only [enorm_eq_self] at h
    refine h.trans ?_
    calc ENNReal.ofReal (cT + 4 * L - (cT - 4 * L)) * maximalHLR (fun y => ‖f y‖ₑ ^ 2) x₀
        ≤ ENNReal.ofReal (cT + 4 * L - (cT - 4 * L)) * ENNReal.ofReal (μ ^ 2) :=
          mul_le_mul' le_rfl hM
      _ = ENNReal.ofReal (8 * L * μ ^ 2) := by
          rw [← ENNReal.ofReal_mul (by linarith)]
          congr 1
          ring
  have hfn2 : MemLp fn 2 := by
    refine (memLp_two_iff_integrable_sq_norm hfnm.aestronglyMeasurable).2
      ⟨(hfnm.norm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt (le_of_eq ?_) (hnear_l.trans_lt ENNReal.ofReal_lt_top)
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hnear_i : ∫ y, ‖fn y‖ ^ 2 ≤ 8 * L * μ ^ 2 :=
    integral_norm_sq_le_of_lintegral_le hfnm (by positivity) hnear_l
  have hnear : ∑ t ∈ T.tiles, ‖pairing fn (φ t k)‖ ^ 2 ≤ sameScaleConst N * (8 * L * μ ^ 2) :=
    (sum_norm_sq_pairing_tree_le hN hν hik φ hP hT hφ hfn2).trans
      (mul_le_mul_of_nonneg_left hnear_i (sameScaleConst_pos hN).le)
  -- far part
  have hffle : ∀ y, ‖ff y‖ₑ ≤ ‖f y‖ₑ := fun y => by
    by_cases hy : y ∈ Nrᶜ <;> simp [hff, hy]
  have hff0 : ∀ y, |y - cT| ≤ 4 * L → ff y = 0 := by
    intro y hy
    have hyN : y ∈ Nr := by
      rw [hNr]
      constructor <;> linarith [abs_le.1 hy]
    rw [hff]
    exact Set.indicator_of_notMem (Set.notMem_compl_iff.2 hyN) f
  have hB : ∫⁻ y, ENNReal.ofReal ((1 + |y - cT| / L) ^ (-2 : ℤ)) * ‖ff y‖ₑ ^ 2 ≤
      ENNReal.ofReal (45 / 2 * L * μ ^ 2) := by
    calc ∫⁻ y, ENNReal.ofReal ((1 + |y - cT| / L) ^ (-2 : ℤ)) * ‖ff y‖ₑ ^ 2
        ≤ ∫⁻ y, ENNReal.ofReal ((1 + |y - cT| / L) ^ (-2 : ℤ)) * ‖f y‖ₑ ^ 2 :=
          lintegral_mono fun y => mul_le_mul' le_rfl (pow_le_pow_left' (hffle y) 2)
      _ ≤ ENNReal.ofReal (45 / 2 * L) * maximalHLR (fun y => ‖f y‖ₑ ^ 2) x₀ :=
          lintegral_weight_le_maximalHLR_of_mem hJoc hL0 hx₀ (hf.enorm.pow_const 2)
      _ ≤ ENNReal.ofReal (45 / 2 * L) * ENNReal.ofReal (μ ^ 2) := mul_le_mul' le_rfl hM
      _ = ENNReal.ofReal (45 / 2 * L * μ ^ 2) := by rw [← ENNReal.ofReal_mul (by positivity)]
  have hfar_t : ∀ t ∈ T.tiles, Integrable (fun y => ff y * (starRingEnd ℂ) (φ t k y)) ∧
      ‖pairing ff (φ t k)‖ ^ 2 ≤
      (45 / 2 * L * μ ^ 2) * (8 * ((2 : ℝ) ^ t.1 / (2 : ℝ) ^ T.top.1) ^ 2 / (2 * (N : ℝ) - 3)) := by
    intro t ht
    have h := norm_pairing_sq_le_far (by omega : 2 ≤ N) (hφ t ht) (toReal_volume_timeInt_pos t) hL0
      (abs_intervalCentre_timeInt_sub_le hT ht) hffm hff0 (B := 45 / 2 * L * μ ^ 2)
      (by positivity) hB
    have e : (2 : ℝ) ^ t.1 / L = (2 : ℝ) ^ t.1 / (2 : ℝ) ^ T.top.1 := by
      rw [hL, T.toReal_volume_topInt]
    rw [toReal_volume_timeInt, e] at h
    exact h
  have hcount := sum_sq_ratio_le_six hP hT
  have h2N : (3 : ℝ) ≤ 2 * (N : ℝ) - 3 := by linarith
  have hfar : ∑ t ∈ T.tiles, ‖pairing ff (φ t k)‖ ^ 2 ≤ 360 * L * μ ^ 2 := by
    calc ∑ t ∈ T.tiles, ‖pairing ff (φ t k)‖ ^ 2
        ≤ ∑ t ∈ T.tiles, (45 / 2 * L * μ ^ 2 * 8 / (2 * (N : ℝ) - 3)) *
            ((2 : ℝ) ^ t.1 / (2 : ℝ) ^ T.top.1) ^ 2 := by
          refine Finset.sum_le_sum fun t ht => (hfar_t t ht).2.trans (le_of_eq ?_)
          ring
      _ = (45 / 2 * L * μ ^ 2 * 8 / (2 * (N : ℝ) - 3)) *
            ∑ t ∈ T.tiles, ((2 : ℝ) ^ t.1 / (2 : ℝ) ^ T.top.1) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (45 / 2 * L * μ ^ 2 * 8 / (2 * (N : ℝ) - 3)) * 6 :=
          mul_le_mul_of_nonneg_left hcount (by positivity)
      _ ≤ 360 * L * μ ^ 2 := by
          have hLμ : 0 ≤ L * μ ^ 2 := by positivity
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith [mul_le_mul_of_nonneg_left h2N hLμ]
  -- assembly
  have hpair : ∀ t ∈ T.tiles, pairing f (φ t k) = pairing fn (φ t k) + pairing ff (φ t k) := by
    intro t ht
    have hm : MemLp (φ t k) 2 := (IsAdapted.memLp_two_and_integral_sq_le (by omega) (hφ t ht)
      (toReal_volume_timeInt_pos t)).1
    have h1 := integrable_mul_conj hfn2 hm
    have h2 := (hfar_t t ht).1
    unfold pairing
    rw [← integral_add h1 h2]
    congr 1
    funext y
    have := hsplit y
    rw [this]
    ring
  have hsq : ∀ x y : ℝ, (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := fun x y => by
    nlinarith [sq_nonneg (x - y)]
  calc ∑ t ∈ T.tiles, ‖pairing f (φ t k)‖ ^ 2
      ≤ ∑ t ∈ T.tiles, (2 * ‖pairing fn (φ t k)‖ ^ 2 + 2 * ‖pairing ff (φ t k)‖ ^ 2) := by
        refine Finset.sum_le_sum fun t ht => ?_
        rw [hpair t ht]
        exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans
          (hsq _ _)
    _ = 2 * ∑ t ∈ T.tiles, ‖pairing fn (φ t k)‖ ^ 2 + 2 * ∑ t ∈ T.tiles, ‖pairing ff (φ t k)‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (sameScaleConst N * (8 * L * μ ^ 2)) + 2 * (360 * L * μ ^ 2) := by gcongr
    _ = (orthSizeConst N * μ) ^ 2 * L := by
        rw [mul_pow, orthSizeConst, Real.sq_sqrt (by have := sameScaleConst_pos hN; positivity)]
        ring

/-- **(b), `i ≠ k`: `size_{i,k}` by the maximal function of `|f|²`.** If every tile `t ∈ P'` has a point
`x_t ∈ I_t` with `M(|f|²)(x_t) ≤ μ²` (i.e. `M²f(x_t) ≤ μ`), then `size_{i,k}(f, P') ≤ C_N μ` for
`i ≠ k`, packets adapted with exponent `N ≥ 3`, `P' ⊆ Idx_ν`, `f ∈ L²`. -/
theorem sizeOff_le_of_maximalHLR_sq_le {N : ℕ} (hN : 3 ≤ N) {a b s' α : ℤ}
    (hν : TriValid a b s' α) {i k : Fin 3} (hik : i ≠ k)
    (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) {P' : Finset (ℤ × ℤ × ℤ)}
    (hP' : (↑P' : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    (hφ : ∀ t ∈ P', IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) {f : ℝ → ℂ}
    (hf : Measurable f) {μ : ℝ} (hμ : 0 ≤ μ)
    (hx : ∀ t ∈ P', ∃ x ∈ timeInt t, maximalHLR (fun y => ‖f y‖ₑ ^ 2) x ≤ ENNReal.ofReal (μ ^ 2)) :
    sizeOff a b φ i k f P' ≤ ENNReal.ofReal (orthSizeConst N * μ) := by
  have hc : 0 ≤ orthSizeConst N * μ := mul_nonneg (orthSizeConst_nonneg N) hμ
  rw [sizeOff_le_ofReal_iff hc]
  intro T hT
  rcases T.tiles.eq_empty_or_nonempty with he | ⟨t₀, ht₀⟩
  · rw [he, Finset.sum_empty]
    have := T.toReal_volume_topInt_pos
    positivity
  · obtain ⟨x₀, hx₀, hM⟩ := hx t₀ (hT.subset ht₀)
    exact sum_norm_sq_pairing_tree_le_of_maximalHLR_sq_le hN hν hik φ hP' hT
      (fun t ht => hφ t (hT.subset ht)) hf (hT.timeInt_subset ht₀ hx₀) hM

theorem size_le_of_maximalHLR_sq_le {N : ℕ} (hN : 3 ≤ N) {a b s' α : ℤ}
    (hν : TriValid a b s' α) {i k : Fin 3} (hik : i ≠ k)
    (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) {P' : Finset (ℤ × ℤ × ℤ)}
    (hP' : (↑P' : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    (hφ : ∀ t ∈ P', IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) {f : ℝ → ℂ}
    (hf : Measurable f) {μ : ℝ} (hμ : 0 ≤ μ)
    (hx : ∀ t ∈ P', ∃ x ∈ timeInt t, maximalHLR (fun y => ‖f y‖ₑ ^ 2) x ≤ ENNReal.ofReal (μ ^ 2)) :
    size a b φ i k f P' ≤ ENNReal.ofReal (orthSizeConst N * μ) := by
  rw [size_of_ne hik]
  exact sizeOff_le_of_maximalHLR_sq_le hN hν hik φ hP' hφ hf hμ hx


/-! ### The two results in the exact shape consumed by C9 (`RefSize.lean`: `TreeBessel`, `SizeOffMax`) -/

/-- **C8(a) in the shape of C9's `TreeBessel sameScaleConst 3`** (all slots adapted; `i`-tree `T` in `P'`). -/
theorem treeBessel_sameScaleConst :
    ∀ (a b s' α : ℤ), TriValid a b s' α → ∀ (N : ℕ), 3 ≤ N →
      ∀ (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (P' : Finset (ℤ × ℤ × ℤ)),
        (↑P' : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α →
        (∀ t ∈ P', ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) →
        ∀ (i k : Fin 3), i ≠ k → ∀ T : TreeData, IsTree a b i P' T →
          ∀ g : ℝ → ℂ, MemLp g 2 volume →
            ∑ t ∈ T.tiles, ‖pairing g (φ t k)‖ ^ 2 ≤ sameScaleConst N * ∫ x, ‖g x‖ ^ 2 :=
  fun _ _ _ _ hν _ hN φ _ hP' hφ _ k hik _ hT _ hg =>
    sum_norm_sq_pairing_tree_le hN hν hik φ hP' hT (fun t ht => hφ t (hT.subset ht) k) hg

/-- **C8(b), `i ≠ k`, in the shape of C9's `SizeOffMax orthSizeConst 3`.** -/
theorem sizeOffMax_orthSizeConst :
    ∀ (a b s' α : ℤ), TriValid a b s' α → ∀ (N : ℕ), 3 ≤ N →
      ∀ (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (P' : Finset (ℤ × ℤ × ℤ)),
        (↑P' : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α →
        (∀ t ∈ P', ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) →
        ∀ (i k : Fin 3), i ≠ k → ∀ f : ℝ → ℂ, Measurable f → ∀ μ : ℝ, 0 ≤ μ →
          (∀ t ∈ P', ∃ x ∈ timeInt t,
            maximalHLR (fun y => ‖f y‖ₑ ^ 2) x ≤ ENNReal.ofReal (μ ^ 2)) →
          size a b φ i k f P' ≤ ENNReal.ofReal (orthSizeConst N * μ) :=
  fun _ _ _ _ hν _ hN φ _ hP' hφ _ k hik _ hf _ hμ hx =>
    size_le_of_maximalHLR_sq_le hN hν hik φ hP' (fun t ht => hφ t ht k) hf hμ hx

end PrimeBHT.TimeFrequency.Tile
