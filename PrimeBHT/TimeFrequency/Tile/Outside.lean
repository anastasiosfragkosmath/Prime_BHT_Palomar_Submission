module

public import PrimeBHT.TimeFrequency.Tile.Select
public import PrimeBHT.TimeFrequency.Tile.TreeSum
public import PrimeBHT.TimeFrequency.Tile.Exponents
public import PrimeBHT.TimeFrequency.Tile.RefSize
public import PrimeBHT.TimeFrequency.Tile.RefSizeSigma
public import PrimeBHT.Frozen.TriForm
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The estimate outside the exceptional set (blueprint node C10a)

Everything here is conditional on `hC4 : WeakBesselHyp a b s' α N C` (the weak Bessel inequality C4,
consumed by the selection lemma `exists_selection_of_hC4`).

## Structure

* `sum_eq_sum_rest_add_sum_trees`: the sum over `P'` of any function of the tile splits as the sum over
  the remainder plus the sums over the selected trees (the selection's tile sets are disjoint).
* `tree_sum_le` (C3 for the family `g`): `∑_{t ∈ T} |I_t|^{-1/2} ∏_k |⟨g_k, φ_{t,k}⟩| ≤ |I_T| ∏_k s_k`
  for an `i`-tree `T` in `R` when `size_{i,k}(g_k, R) ≤ s_k`.
* `exists_step_of_hC4`, `exists_level_of_hC4`: one application of C5 (slot `k`), and a level (C5 for the three
  slots in turn) with `size ≤ 2 lam` going to `size ≤ lam`.
* `exists_iterate_of_hC4`: the levels `lam_ℓ = K 2^{-ℓ-1}`; `triForm_le_of_sizes_of_hC4`: the abstract outside
  bound `Λ ≤ 96 C⁺ K x (log₂(1/x) + 3)` for any family `g` with `‖g_k‖₂² ≤ 1` whose sizes on `Q` are `≤ K x`
  in the slot `k₀` and `≤ K` in the other two slots (`0 < x ≤ 1`).
* `triForm_outside_le_log_of_hC4`, `triForm_outside_le_of_hC4`, `triForm_filter_outside_le_of_hC4`: the same for
  `g' = refG' E h` and `k₀ = σ 0` (`σ` an arbitrary permutation of the slots), the C9 size bounds being the
  hypotheses `hsizeσ0`, `hsizeσ`; with the `ε`-loss `Λ ≤ 96 C⁺ K (3 + 1/ε) |E (σ 0)|^{1/2-ε}`.
* `triForm_filter_outside_le_orth_of_hC4`: the final theorem, with the sizes supplied by
  `size_refG'_σ0_le_orth`, `size_refG'_ne_σ0_le_orth` (`RefSizeSigma.lean`, `N ≥ 4`); conditional only on `hC4`.

## Corrections to the blueprint (C10a), checked by hand

1. `‖g'_k‖₂² ≤ 1` (not `≤ 2`): `|h_k| ≤ 1_{E_k}` and `g'_k = |E_k|^{-1/2} h_k`.
2. Only `N ≥ 4` (C9) is needed outside the exceptional set; `N ≥ N_ε` belongs to the inside estimate C10b.
   The constant is `96 C⁺ K_N (3 + 1/ε)` with `K_N = refSizeConst (orthSizeConst N) (sameScaleConst N)` and `C`
   the weak Bessel constant at `N`; the slot-`σ 0` initial size is `K_N |E (σ 0)|^{1/2}`, the other two `K_N`.
3. Step 3 (termination): it is false that "some stage empties `P_out`" (a tile with all three pairings zero is
   never selected). Instead, after `n` levels all sizes are `≤ K_N 2^{-n}`, so the remainder `R_n` has
   `Λ_{R_n} ≤ (∑_{t ∈ P_out} |I_t|) (K_N 2^{-n})^3 → 0`; this is exactly what is used (`triForm_le_sum_volume_mul_prod`).
4. Level constants: `lam_n = K_N 2^{-n-1}`, `∑ trees |I_T| ≤ 3 · 8 C⁺ / lam_n²`, per-tree `|I_T| ∏_k s_k` with
   `s_{σ 0} = K_N min(x, 2^{-n})`, `s_k = K_N 2^{-n}`; the level contributes exactly `96 C⁺ K_N min(x, 2^{-n})`.
-/

public section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Tile

/-! ### Splitting the sum over the selected trees -/

/-- **Decomposition of a sum along a selection.** The selected trees (of all types) have pairwise disjoint
tile sets inside `P'` and `rest = P' ∖ ⋃ tiles`, so a sum over `P'` is the sum over `rest` plus the sums over
the trees. -/
theorem sum_eq_sum_rest_add_sum_trees {a b : ℤ} {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {k : Fin 3}
    {f : ℝ → ℂ} {lam B : ℝ} {P' : Finset (ℤ × ℤ × ℤ)} {out : SelectionOutput}
    (hout : IsSelection a b φ k f lam B P' out) (F : ℤ × ℤ × ℤ → ℝ) :
    ∑ t ∈ P', F t = ∑ t ∈ out.rest, F t + ∑ i, ∑ T ∈ out.trees i, ∑ t ∈ T.tiles, F t := by
  classical
  obtain ⟨hT, hdisj, hrest, -, -⟩ := hout
  set U : Finset (ℤ × ℤ × ℤ) :=
    Finset.univ.biUnion (fun i => (out.trees i).biUnion TreeData.tiles) with hU
  have hUsub : U ⊆ P' := by
    intro t ht
    obtain ⟨i, -, T, hTi, htT⟩ := by simpa only [hU, Finset.mem_biUnion] using ht
    exact (hT i T hTi).subset htT
  have h1 : ∑ t ∈ P' \ U, F t + ∑ t ∈ U, F t = ∑ t ∈ P', F t := Finset.sum_sdiff hUsub
  have h2 : ∑ t ∈ U, F t = ∑ i, ∑ T ∈ out.trees i, ∑ t ∈ T.tiles, F t := by
    rw [hU, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_biUnion]
      intro T hTi T' hT'i hne
      exact hdisj i T hTi i T' hT'i (Or.inr hne)
    · intro i _ j _ hij
      simp only [Function.onFun]
      rw [Finset.disjoint_biUnion_left]
      intro T hTi
      rw [Finset.disjoint_biUnion_right]
      intro T' hT'j
      exact hdisj i T hTi j T' hT'j (Or.inl hij)
  rw [hrest, ← h1, h2]

/-! ### C3 for a family of functions -/

/-- **C3 for the family `g`.** For an `i`-tree `T` in `R` and `size_{i,k}(g_k, R) ≤ s_k` (`k = 0, 1, 2`):
`∑_{t ∈ T} |I_t|^{-1/2} ∏_k |⟨g_k, φ_{t,k}⟩| ≤ |I_T| ∏_k s_k`. -/
theorem tree_sum_le {a b : ℤ} {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {g : Fin 3 → ℝ → ℂ}
    {R : Finset (ℤ × ℤ × ℤ)} {i : Fin 3} {T : TreeData} (hT : IsTree a b i R T) {s : Fin 3 → ℝ}
    (hs0 : ∀ k, 0 ≤ s k) (hs : ∀ k, size a b φ i k (g k) R ≤ ENNReal.ofReal (s k)) :
    ∑ t ∈ T.tiles, (volume (timeInt t)).toReal ^ (-(1 : ℝ) / 2) * ∏ k, ‖pairing (g k) (φ t k)‖ ≤
      (volume T.topInt).toReal * ∏ k, s k := by
  refine sum_weight_mul_prod_le T.tiles (fun t => (volume (timeInt t)).toReal ^ (-(1 : ℝ) / 2))
    (fun k t => ‖pairing (g k) (φ t k)‖) s i T.toReal_volume_topInt_pos.le hs0
    (fun k t _ => norm_nonneg _) ?_ ?_
  · intro t ht
    have h := hs i
    rw [size_self] at h
    have h1 := (le_sizeDiag (φ := φ) (k := i) (f := g i) (hT.subset ht)).trans h
    exact (ENNReal.ofReal_le_ofReal_iff (hs0 i)).1 h1
  · intro k hk
    have h := hs k
    rw [size_of_ne (Ne.symm hk), sizeOff_le_ofReal_iff (hs0 k)] at h
    exact h T hT

/-- The tail bound: for any `R` with `size_{i,k}(g_k, R) ≤ s_k` (all `i, k`),
`Λ_R(g) ≤ (∑_{t ∈ R} |I_t|) ∏_k s_k` (each tile is a one-tile tree). -/
theorem triForm_le_sum_volume_mul_prod {a b : ℤ} {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    {g : Fin 3 → ℝ → ℂ} {R : Finset (ℤ × ℤ × ℤ)} {s : Fin 3 → ℝ} (hs0 : ∀ k, 0 ≤ s k)
    (hs : ∀ i k, size a b φ i k (g k) R ≤ ENNReal.ofReal (s k)) :
    triForm R φ g ≤ (∑ t ∈ R, (volume (timeInt t)).toReal) * ∏ k, s k := by
  unfold triForm
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun t ht => ?_
  have h := tree_sum_le (isTree_singleton a b (0 : Fin 3) ht) hs0 (fun k => hs 0 k)
  rw [Finset.sum_singleton] at h
  refine h.trans (le_of_eq ?_)
  have e : (volume (TreeData.topInt ⟨{t}, (t.1, t.2.1), intervalCentre (freqInt a b 0 t)⟩)).toReal =
      (volume (timeInt t)).toReal := by
    simp only [TreeData.topInt, toReal_volume_dyadicInt, toReal_volume_timeInt]
  rw [e]


/-! ### One application of C5 and one level -/

/-- **One application of C5** (slot `k`, conditional on `hC4`). `Q ⊆ R`; the sizes of `R` are bounded by `s`
(`size_{i,k'}(g_{k'}, R) ≤ s_{k'}`); `size_{i,k}(g_k, Q) ≤ 2 lam` for all `i`; `‖g_k‖₂² ≤ 1`. Then there is
`Q' ⊆ Q` with `size_{i,k}(g_k, Q') ≤ lam` and `Λ_Q(g) ≤ (∏ s) 8 C⁺ / lam² + Λ_{Q'}(g)`. -/
theorem exists_step_of_hC4 {a b s' α : ℤ} (hν : TriValid a b s' α) {N : ℕ} {C : ℝ}
    (hC4 : WeakBesselHyp a b s' α N C) {R Q : Finset (ℤ × ℤ × ℤ)} (hQR : Q ⊆ R)
    (hR : (↑R : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α) {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hφ : ∀ t ∈ R, ∀ j, IsAdapted N (timeInt t) (freqInt a b j t) (φ t j))
    {g : Fin 3 → ℝ → ℂ} {s : Fin 3 → ℝ} (hs0 : ∀ k, 0 ≤ s k)
    (hs : ∀ i k, size a b φ i k (g k) R ≤ ENNReal.ofReal (s k)) (k : Fin 3)
    (hg : MemLp (g k) 2 volume) (hint : ∫ x, ‖g k x‖ ^ 2 ≤ 1) {lam : ℝ} (hlam : 0 < lam)
    (hsize : ∀ i, size a b φ i k (g k) Q ≤ ENNReal.ofReal (2 * lam)) :
    ∃ Q' : Finset (ℤ × ℤ × ℤ), Q' ⊆ Q ∧ (∀ i, size a b φ i k (g k) Q' ≤ ENNReal.ofReal lam) ∧
      triForm Q φ g ≤ (∏ j, s j) * (8 * max C 0 / lam ^ 2) + triForm Q' φ g := by
  have hQidx : (↑Q : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α := fun t ht => hR (hQR ht)
  obtain ⟨out, hout⟩ := exists_selection_of_hC4 hν hC4 hQidx (fun t ht j => hφ t (hQR ht) j) k hg
    hlam hsize
  have hdec := sum_eq_sum_rest_add_sum_trees hout (fun t =>
    (volume (timeInt t)).toReal ^ (-(1 : ℝ) / 2) * ∏ j, ‖pairing (g j) (φ t j)‖)
  obtain ⟨hT, -, hrest, hsz, hsum⟩ := hout
  have hrestsub : out.rest ⊆ Q := by
    rw [hrest]; exact Finset.sdiff_subset
  have hP0 : 0 ≤ ∏ j, s j := Finset.prod_nonneg fun j _ => hs0 j
  have hlam2 : 0 < lam ^ 2 := by positivity
  have hI0 : 0 ≤ ∫ x, ‖g k x‖ ^ 2 := integral_nonneg fun x => by positivity
  have hB : 8 * C * (∫ x, ‖g k x‖ ^ 2) / lam ^ 2 ≤ 8 * max C 0 / lam ^ 2 := by
    refine div_le_div_of_nonneg_right ?_ hlam2.le
    have h1 : C * (∫ x, ‖g k x‖ ^ 2) ≤ max C 0 * 1 :=
      mul_le_mul (le_max_left _ _) hint hI0 (le_max_right _ _)
    linarith
  have htree : ∑ i, ∑ T ∈ out.trees i, ∑ t ∈ T.tiles,
        (volume (timeInt t)).toReal ^ (-(1 : ℝ) / 2) * ∏ j, ‖pairing (g j) (φ t j)‖ ≤
      (∏ j, s j) * ∑ i, ∑ T ∈ out.trees i, (volume T.topInt).toReal := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun T hTi => ?_
    have := tree_sum_le ((hT i T hTi).mono hQR) hs0 (fun j => hs i j)
    rw [mul_comm] at this
    exact this
  refine ⟨out.rest, hrestsub, hsz, ?_⟩
  unfold triForm
  rw [hdec]
  have := mul_le_mul_of_nonneg_left (hsum.trans hB) hP0
  linarith


/-- **One level** (conditional on `hC4`): C5 applied successively for `k = 0, 1, 2` (sizes only decrease under
subcollections, so the outputs for `k = 0, 1` survive the later applications). From `size_{i,k}(g_k, R) ≤ 2 lam`
(all `i, k`) to `R' ⊆ R` with all sizes `≤ lam` and `Λ_R(g) ≤ (∏ s) 24 C⁺ / lam² + Λ_{R'}(g)`. -/
theorem exists_level_of_hC4 {a b s' α : ℤ} (hν : TriValid a b s' α) {N : ℕ} {C : ℝ}
    (hC4 : WeakBesselHyp a b s' α N C) {R : Finset (ℤ × ℤ × ℤ)}
    (hR : (↑R : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α) {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hφ : ∀ t ∈ R, ∀ j, IsAdapted N (timeInt t) (freqInt a b j t) (φ t j))
    {g : Fin 3 → ℝ → ℂ} (hg : ∀ k, MemLp (g k) 2 volume) (hint : ∀ k, ∫ x, ‖g k x‖ ^ 2 ≤ 1)
    {s : Fin 3 → ℝ} (hs0 : ∀ k, 0 ≤ s k)
    (hs : ∀ i k, size a b φ i k (g k) R ≤ ENNReal.ofReal (s k)) {lam : ℝ} (hlam : 0 < lam)
    (hsize : ∀ i k, size a b φ i k (g k) R ≤ ENNReal.ofReal (2 * lam)) :
    ∃ R' : Finset (ℤ × ℤ × ℤ), R' ⊆ R ∧ (∀ i k, size a b φ i k (g k) R' ≤ ENNReal.ofReal lam) ∧
      triForm R φ g ≤ (∏ j, s j) * (24 * max C 0 / lam ^ 2) + triForm R' φ g := by
  obtain ⟨Q₁, h1sub, h1sz, h1⟩ := exists_step_of_hC4 hν hC4 (Finset.Subset.refl R) hR hφ hs0 hs 0
    (hg 0) (hint 0) hlam (fun i => hsize i 0)
  have h1R : Q₁ ⊆ R := h1sub
  obtain ⟨Q₂, h2sub, h2sz, h2⟩ := exists_step_of_hC4 hν hC4 h1R hR hφ hs0 hs 1 (hg 1) (hint 1) hlam
    (fun i => (size_mono h1R).trans (hsize i 1))
  have h2R : Q₂ ⊆ R := h2sub.trans h1R
  obtain ⟨Q₃, h3sub, h3sz, h3⟩ := exists_step_of_hC4 hν hC4 h2R hR hφ hs0 hs 2 (hg 2) (hint 2) hlam
    (fun i => (size_mono h2R).trans (hsize i 2))
  have h3R : Q₃ ⊆ R := h3sub.trans h2R
  refine ⟨Q₃, h3R, ?_, ?_⟩
  · intro i k
    fin_cases k
    · exact (size_mono (h3sub.trans h2sub)).trans (h1sz i)
    · exact (size_mono h3sub).trans (h2sz i)
    · exact h3sz i
  · have e : (∏ j, s j) * (24 * max C 0 / lam ^ 2) =
        (∏ j, s j) * (8 * max C 0 / lam ^ 2) + (∏ j, s j) * (8 * max C 0 / lam ^ 2) +
          (∏ j, s j) * (8 * max C 0 / lam ^ 2) := by ring
    linarith


/-! ### The levels `lam_ℓ = K 2^{-ℓ-1}` -/

theorem prod_ite_slot (k₀ : Fin 3) (u v : ℝ) : ∏ k : Fin 3, (if k = k₀ then u else v) = u * v * v := by
  have h : k₀ = 0 ∨ k₀ = 1 ∨ k₀ = 2 := by fin_cases k₀ <;> simp
  rcases h with rfl | rfl | rfl <;>
    simp [Fin.prod_univ_three, mul_comm, mul_left_comm]

/-- **Levels** (conditional on `hC4`). Let `g` be a family with `‖g_k‖₂² ≤ 1`, `K, x > 0`, `x ≤ 1`, and a slot
`k₀` with `size_{i,k₀}(g_{k₀}, Q) ≤ K x` and `size_{i,k}(g_k, Q) ≤ K` (`k ≠ k₀`). After `n` levels there is
`R ⊆ Q` with all sizes `≤ K 2^{-n}` and
`Λ_Q(g) ≤ 96 C⁺ K ∑_{ℓ<n} min(x, 2^{-ℓ}) + Λ_R(g)`. -/
theorem exists_iterate_of_hC4 {a b s' α : ℤ} (hν : TriValid a b s' α) {N : ℕ} {C : ℝ}
    (hC4 : WeakBesselHyp a b s' α N C) {Q : Finset (ℤ × ℤ × ℤ)}
    (hQ : (↑Q : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α) {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hφ : ∀ t ∈ Q, ∀ j, IsAdapted N (timeInt t) (freqInt a b j t) (φ t j))
    {g : Fin 3 → ℝ → ℂ} (hg : ∀ k, MemLp (g k) 2 volume) (hint : ∀ k, ∫ x, ‖g k x‖ ^ 2 ≤ 1)
    {K x : ℝ} (hK : 0 < K) (hx0 : 0 < x) (hx1 : x ≤ 1) (k₀ : Fin 3)
    (hs0 : ∀ i, size a b φ i k₀ (g k₀) Q ≤ ENNReal.ofReal (K * x))
    (hs1 : ∀ i k, k ≠ k₀ → size a b φ i k (g k) Q ≤ ENNReal.ofReal K) (n : ℕ) :
    ∃ R : Finset (ℤ × ℤ × ℤ), R ⊆ Q ∧
      (∀ i k, size a b φ i k (g k) R ≤ ENNReal.ofReal (K * (1 / 2 : ℝ) ^ n)) ∧
      triForm Q φ g ≤
        96 * max C 0 * K * ∑ ℓ ∈ Finset.range n, min x ((1 / 2 : ℝ) ^ ℓ) + triForm R φ g := by
  induction n with
  | zero =>
    refine ⟨Q, Finset.Subset.refl Q, ?_, by simp⟩
    intro i k
    rw [pow_zero, mul_one]
    by_cases hk : k = k₀
    · subst hk
      exact (hs0 i).trans (ENNReal.ofReal_le_ofReal (by nlinarith))
    · exact hs1 i k hk
  | succ n ih =>
    obtain ⟨R, hRQ, hRsz, hR⟩ := ih
    set r : ℝ := (1 / 2 : ℝ) ^ n with hr
    have hr0 : 0 < r := by positivity
    set lam : ℝ := K * r / 2 with hlam
    have hlam0 : 0 < lam := by positivity
    set s : Fin 3 → ℝ := fun k => if k = k₀ then K * min x r else K * r with hs
    have hsnn : ∀ k, 0 ≤ s k := by
      intro k
      simp only [hs]
      split_ifs
      · exact mul_nonneg hK.le (le_min hx0.le hr0.le)
      · exact mul_nonneg hK.le hr0.le
    have hsR : ∀ i k, size a b φ i k (g k) R ≤ ENNReal.ofReal (s k) := by
      intro i k
      by_cases hk : k = k₀
      · subst hk
        simp only [hs, ↓reduceIte]
        rcases le_total x r with h | h
        · rw [min_eq_left h]
          exact (size_mono hRQ).trans (hs0 i)
        · rw [min_eq_right h]
          exact hRsz i k
      · simp only [hs, hk, ↓reduceIte]
        exact hRsz i k
    have hRidx : (↑R : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α := fun t ht => hQ (hRQ ht)
    obtain ⟨R', hR'R, hR'sz, hR'⟩ := exists_level_of_hC4 hν hC4 hRidx
      (fun t ht j => hφ t (hRQ ht) j) hg hint hsnn hsR hlam0
      (fun i k => (hRsz i k).trans (ENNReal.ofReal_le_ofReal (by rw [hlam]; linarith)))
    have hlam_eq : K * (1 / 2 : ℝ) ^ (n + 1) = lam := by rw [pow_succ, hlam]; ring
    refine ⟨R', hR'R.trans hRQ, ?_, ?_⟩
    · intro i k
      rw [hlam_eq]
      exact hR'sz i k
    · have hprod : (∏ j, s j) * (24 * max C 0 / lam ^ 2) = 96 * max C 0 * K * min x r := by
        simp only [hs]
        rw [prod_ite_slot, hlam]
        field_simp
        ring
      rw [Finset.sum_range_succ]
      have : (1 / 2 : ℝ) ^ n = r := hr.symm
      rw [this]
      linarith


/-- **The abstract outside bound** (conditional on `hC4`; the sizes are hypotheses). For a family `g` of
`L²` functions with `‖g_k‖₂² ≤ 1`, a finite `Q ⊆ Idx_ν` with adapted packets, `0 < x ≤ 1`, `K > 0`, and a slot
`k₀` with `size_{i,k₀}(g_{k₀}, Q) ≤ K x`, `size_{i,k}(g_k, Q) ≤ K` for `k ≠ k₀`:
`Λ_Q(g) ≤ 96 C⁺ K · x (log₂(1/x) + 3)`. -/
theorem triForm_le_of_sizes_of_hC4 {a b s' α : ℤ} (hν : TriValid a b s' α) {N : ℕ} {C : ℝ}
    (hC4 : WeakBesselHyp a b s' α N C) {Q : Finset (ℤ × ℤ × ℤ)}
    (hQ : (↑Q : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α) {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hφ : ∀ t ∈ Q, ∀ j, IsAdapted N (timeInt t) (freqInt a b j t) (φ t j))
    {g : Fin 3 → ℝ → ℂ} (hg : ∀ k, MemLp (g k) 2 volume) (hint : ∀ k, ∫ x, ‖g k x‖ ^ 2 ≤ 1)
    {K x : ℝ} (hK : 0 < K) (hx0 : 0 < x) (hx1 : x ≤ 1) (k₀ : Fin 3)
    (hs0 : ∀ i, size a b φ i k₀ (g k₀) Q ≤ ENNReal.ofReal (K * x))
    (hs1 : ∀ i k, k ≠ k₀ → size a b φ i k (g k) Q ≤ ENNReal.ofReal K) :
    triForm Q φ g ≤ 96 * max C 0 * K * (x * (Real.logb 2 (1 / x) + 3)) := by
  set S : ℝ := ∑ t ∈ Q, (volume (timeInt t)).toReal with hS
  set A : ℝ := 96 * max C 0 * K * (x * (Real.logb 2 (1 / x) + 3)) with hA
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun t _ => ENNReal.toReal_nonneg
  have hCm : 0 ≤ 96 * max C 0 * K := by positivity
  have hbound : ∀ n : ℕ, triForm Q φ g ≤ A + S * K ^ 3 * ((1 / 8 : ℝ) ^ n) := by
    intro n
    obtain ⟨R, hRQ, hRsz, hR⟩ := exists_iterate_of_hC4 hν hC4 hQ hφ hg hint hK hx0 hx1 k₀ hs0 hs1 n
    have hsum : ∑ ℓ ∈ Finset.range n, min x ((1 / 2 : ℝ) ^ ℓ) ≤ x * (Real.logb 2 (1 / x) + 3) :=
      sum_range_min_two_pow_le hx0 hx1 n
    have hr0 : 0 ≤ K * (1 / 2 : ℝ) ^ n := by positivity
    have htail := triForm_le_sum_volume_mul_prod (φ := φ) (g := g) (R := R)
      (s := fun _ => K * (1 / 2 : ℝ) ^ n) (fun _ => hr0) hRsz
    have hprod : ∏ _k : Fin 3, K * (1 / 2 : ℝ) ^ n = K ^ 3 * ((1 / 8 : ℝ) ^ n) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← pow_mul,
        mul_comm n 3, pow_mul]
      norm_num
    have hRS : ∑ t ∈ R, (volume (timeInt t)).toReal ≤ S :=
      Finset.sum_le_sum_of_subset_of_nonneg hRQ fun _ _ _ => ENNReal.toReal_nonneg
    have hK3 : 0 ≤ K ^ 3 * ((1 / 8 : ℝ) ^ n) := by positivity
    rw [hprod] at htail
    have h1 : (∑ t ∈ R, (volume (timeInt t)).toReal) * (K ^ 3 * ((1 / 8 : ℝ) ^ n)) ≤
        S * (K ^ 3 * ((1 / 8 : ℝ) ^ n)) := mul_le_mul_of_nonneg_right hRS hK3
    have h2 : 96 * max C 0 * K * ∑ ℓ ∈ Finset.range n, min x ((1 / 2 : ℝ) ^ ℓ) ≤ A :=
      mul_le_mul_of_nonneg_left hsum hCm
    calc triForm Q φ g
        ≤ 96 * max C 0 * K * ∑ ℓ ∈ Finset.range n, min x ((1 / 2 : ℝ) ^ ℓ) + triForm R φ g := hR
      _ ≤ A + S * (K ^ 3 * ((1 / 8 : ℝ) ^ n)) := by linarith
      _ = A + S * K ^ 3 * ((1 / 8 : ℝ) ^ n) := by ring
  have hlim : Filter.Tendsto (fun n : ℕ => A + S * K ^ 3 * ((1 / 8 : ℝ) ^ n)) Filter.atTop
      (nhds (A + S * K ^ 3 * 0)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul
      (S * K ^ 3)).const_add A
  have := ge_of_tendsto' hlim hbound
  simpa using this


/-! ### The `L²`-normalized functions `g'_k = |E_k|^{-1/2} h_k` -/

section Normalized

variable {E : Fin 3 → Set ℝ} {h : Fin 3 → ℝ → ℂ}

theorem refScale'_sq {k : Fin 3} (hpos : 0 < (volume (E k)).toReal) :
    refScale' E k ^ 2 = ((volume (E k)).toReal)⁻¹ := by
  rw [refScale', ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
  norm_num [Real.rpow_neg_one]

theorem norm_refG'_le_indicator_const {k : Fin 3}
    (hdom : ∀ x, ‖h k x‖ ≤ (E k).indicator (1 : ℝ → ℝ) x) (x : ℝ) :
    ‖refG' E h k x‖ ≤ (E k).indicator (fun _ => refScale' E k) x := by
  refine (norm_ofReal_mul_le_indicator (refScale'_nonneg E k) hdom x).trans (le_of_eq ?_)
  by_cases hx : x ∈ E k <;> simp [hx]

theorem memLp_two_refG' {k : Fin 3} (hEm : MeasurableSet (E k)) (hfin : volume (E k) < ⊤)
    (hhm : Measurable (h k)) (hdom : ∀ x, ‖h k x‖ ≤ (E k).indicator (1 : ℝ → ℝ) x) :
    MemLp (refG' E h k) 2 volume := by
  refine MemLp.mono' (g := (E k).indicator fun _ => refScale' E k)
    (memLp_indicator_const 2 hEm.nullMeasurableSet _ (Or.inr hfin.ne)) ?_
    (Filter.Eventually.of_forall (norm_refG'_le_indicator_const hdom))
  exact (hhm.const_mul _ : Measurable fun x => ((refScale' E k : ℝ) : ℂ) * h k x).aestronglyMeasurable

/-- **`‖g'_k‖₂² ≤ 1`** (the blueprint's `≤ 2` is not needed). -/
theorem integral_norm_sq_refG'_le {k : Fin 3} (hEm : MeasurableSet (E k)) (hpos : 0 < volume (E k))
    (hfin : volume (E k) < ⊤) (hdom : ∀ x, ‖h k x‖ ≤ (E k).indicator (1 : ℝ → ℝ) x) :
    ∫ x, ‖refG' E h k x‖ ^ 2 ≤ 1 := by
  have hv : 0 < (volume (E k)).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  have hint : Integrable ((E k).indicator fun _ => refScale' E k ^ 2) volume :=
    (integrable_indicator_iff hEm).2 (integrableOn_const hfin.ne)
  have hle : ∀ x, ‖refG' E h k x‖ ^ 2 ≤ (E k).indicator (fun _ => refScale' E k ^ 2) x := by
    intro x
    have h1 := norm_refG'_le_indicator_const hdom x
    have h0 : 0 ≤ ‖refG' E h k x‖ := norm_nonneg _
    calc ‖refG' E h k x‖ ^ 2 ≤ ((E k).indicator (fun _ => refScale' E k) x) ^ 2 :=
          pow_le_pow_left₀ h0 h1 2
      _ = (E k).indicator (fun _ => refScale' E k ^ 2) x := by
          by_cases hx : x ∈ E k <;> simp [hx]
  calc ∫ x, ‖refG' E h k x‖ ^ 2 ≤ ∫ x, (E k).indicator (fun _ => refScale' E k ^ 2) x :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hint
          (Filter.Eventually.of_forall hle)
    _ = 1 := by
        rw [integral_indicator_const _ hEm, measureReal_def, smul_eq_mul, refScale'_sq hv]
        field_simp

theorem pairing_const_mul_left (c : ℂ) (f φ : ℝ → ℂ) :
    pairing (fun x => c * f x) φ = c * pairing f φ := by
  unfold pairing
  simp_rw [mul_assoc]
  exact integral_const_mul c _

/-- `Λ_Q(g') = (∏_k |E k|^{-1/2}) Λ_Q(h)`: the `L²` normalization is a scalar in the form. -/
theorem triForm_refG' (Q : Finset (ℤ × ℤ × ℤ)) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) :
    triForm Q φ (refG' E h) = (∏ k, refScale' E k) * triForm Q φ h := by
  unfold triForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have e : ∀ k, ‖pairing (refG' E h k) (φ t k)‖ = refScale' E k * ‖pairing (h k) (φ t k)‖ := by
    intro k
    unfold refG'
    rw [pairing_const_mul_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (refScale'_nonneg E k)]
  simp only [e, Finset.prod_mul_distrib]
  ring

/-- The converse scaling: `Λ_Q(h) = (∏_k |E k|^{1/2}) Λ_Q(g')` (for `|E k| > 0`). -/
theorem triForm_eq_prod_mul_triForm_refG' (hpos : ∀ k, 0 < (volume (E k)).toReal)
    (Q : Finset (ℤ × ℤ × ℤ)) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) :
    triForm Q φ h = (∏ k, (volume (E k)).toReal ^ ((1 : ℝ) / 2)) * triForm Q φ (refG' E h) := by
  rw [triForm_refG', ← mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_eq_one, one_mul]
  intro k _
  rw [refScale', ← Real.rpow_add (hpos k)]
  norm_num

end Normalized


/-! ### The outside bound for arbitrary slot roles `(σ 0, σ 1, σ 2) = (small, mid, large)` -/

/-- **C10a, outside the exceptional set, for an arbitrary permutation `σ` of the slots** (conditional on `hC4`;
the C9 size bounds are the hypotheses `hsizeσ0`, `hsizeσ`, to be supplied by the `σ`-general C9).
`E k` (indexed by *slot*) are measurable of finite positive measure with `|E (σ 0)| ≤ 1`, `h k` measurable with
`‖h k‖ ≤ 1_{E k}`, `g'_k = |E k|^{-1/2} h k` (`refG'`, which does not depend on `σ`). If on the finite `Q ⊆ Idx_ν`
(packets adapted with exponent `N`) the sizes are `size_{i,σ 0}(g'_{σ 0}, Q) ≤ K |E (σ 0)|^{1/2}` and
`size_{i,k}(g'_k, Q) ≤ K` for `k ≠ σ 0` (`K > 0`; this is C9 (ii'), valid when no tile of `Q` lies in the
exceptional set `F_σ = refExceptional (E (σ 0)) (E (σ 1))`), then with `x = |E (σ 0)|^{1/2}`,
`Λ_Q(g') ≤ 96 C⁺ K x (log₂(1/x) + 3)`. -/
theorem triForm_outside_le_log_of_hC4 {a b s' α : ℤ} (hν : TriValid a b s' α) {N : ℕ} {C : ℝ}
    (hC4 : WeakBesselHyp a b s' α N C) (σ : Equiv.Perm (Fin 3)) {E : Fin 3 → Set ℝ}
    {h : Fin 3 → ℝ → ℂ} (hEm : ∀ k, MeasurableSet (E k))
    (hE : ∀ k, 0 < volume (E k) ∧ volume (E k) < ⊤) (hone : (volume (E (σ 0))).toReal ≤ 1)
    (hhm : ∀ k, Measurable (h k)) (hdom : ∀ k x, ‖h k x‖ ≤ (E k).indicator (1 : ℝ → ℝ) x)
    {Q : Finset (ℤ × ℤ × ℤ)} (hQ : (↑Q : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hφ : ∀ t ∈ Q, ∀ j, IsAdapted N (timeInt t) (freqInt a b j t) (φ t j)) {K : ℝ} (hK : 0 < K)
    (hsizeσ0 : ∀ i, size a b φ i (σ 0) (refG' E h (σ 0)) Q ≤
      ENNReal.ofReal (K * (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2)))
    (hsizeσ : ∀ i k, k ≠ σ 0 → size a b φ i k (refG' E h k) Q ≤ ENNReal.ofReal K) :
    triForm Q φ (refG' E h) ≤ 96 * max C 0 * K *
      ((volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2) *
        (Real.logb 2 (1 / (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2)) + 3)) := by
  have hv : 0 < (volume (E (σ 0))).toReal :=
    ENNReal.toReal_pos (hE (σ 0)).1.ne' (hE (σ 0)).2.ne
  have hx0 : 0 < (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hv _
  have hx1 : (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2) ≤ 1 :=
    Real.rpow_le_one hv.le hone (by norm_num)
  exact triForm_le_of_sizes_of_hC4 hν hC4 hQ hφ
    (fun k => memLp_two_refG' (hEm k) (hE k).2 (hhm k) (hdom k))
    (fun k => integral_norm_sq_refG'_le (hEm k) (hE k).1 (hE k).2 (hdom k)) hK hx0 hx1 (σ 0)
    hsizeσ0 hsizeσ

/-- **C10a with the `ε`-loss**: `Λ_Q(g') ≤ 96 C⁺ K (3 + 1/ε) |E (σ 0)|^{1/2-ε}` for every `ε > 0`. Same
hypotheses as `triForm_outside_le_log_of_hC4`. -/
theorem triForm_outside_le_of_hC4 {a b s' α : ℤ} (hν : TriValid a b s' α) {N : ℕ} {C : ℝ}
    (hC4 : WeakBesselHyp a b s' α N C) (σ : Equiv.Perm (Fin 3)) {E : Fin 3 → Set ℝ}
    {h : Fin 3 → ℝ → ℂ} (hEm : ∀ k, MeasurableSet (E k))
    (hE : ∀ k, 0 < volume (E k) ∧ volume (E k) < ⊤) (hone : (volume (E (σ 0))).toReal ≤ 1)
    (hhm : ∀ k, Measurable (h k)) (hdom : ∀ k x, ‖h k x‖ ≤ (E k).indicator (1 : ℝ → ℝ) x)
    {Q : Finset (ℤ × ℤ × ℤ)} (hQ : (↑Q : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hφ : ∀ t ∈ Q, ∀ j, IsAdapted N (timeInt t) (freqInt a b j t) (φ t j)) {K : ℝ} (hK : 0 < K)
    (hsizeσ0 : ∀ i, size a b φ i (σ 0) (refG' E h (σ 0)) Q ≤
      ENNReal.ofReal (K * (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2)))
    (hsizeσ : ∀ i k, k ≠ σ 0 → size a b φ i k (refG' E h k) Q ≤ ENNReal.ofReal K)
    {ε : ℝ} (hε : 0 < ε) :
    triForm Q φ (refG' E h) ≤
      96 * max C 0 * K * (3 + 1 / ε) * (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2 - ε) := by
  have hv : 0 < (volume (E (σ 0))).toReal :=
    ENNReal.toReal_pos (hE (σ 0)).1.ne' (hE (σ 0)).2.ne
  have hx0 : 0 < (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hv _
  have hx1 : (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2) ≤ 1 :=
    Real.rpow_le_one hv.le hone (by norm_num)
  have hCm : 0 ≤ 96 * max C 0 * K := by positivity
  refine (triForm_outside_le_log_of_hC4 hν hC4 σ hEm hE hone hhm hdom hQ hφ hK hsizeσ0
    hsizeσ).trans ?_
  calc 96 * max C 0 * K * ((volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2) *
        (Real.logb 2 (1 / (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2)) + 3))
      ≤ 96 * max C 0 * K * ((3 + 1 / ε) *
          ((volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2)) ^ (1 - 2 * ε)) :=
        mul_le_mul_of_nonneg_left (mul_logb_add_three_le hx0 hx1 hε) hCm
    _ = 96 * max C 0 * K * (3 + 1 / ε) * (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2 - ε) := by
        rw [sqrt_rpow_one_sub_two_mul hv]
        ring

/-- The same for `Q = P_out = {t ∈ P : I_t ⊄ F}` (`F` any set, e.g. the exceptional set `F_σ`): the hypotheses
are those on `P_out`. -/
theorem triForm_filter_outside_le_of_hC4 {a b s' α : ℤ} (hν : TriValid a b s' α) {N : ℕ} {C : ℝ}
    (hC4 : WeakBesselHyp a b s' α N C) (σ : Equiv.Perm (Fin 3)) {E : Fin 3 → Set ℝ}
    {h : Fin 3 → ℝ → ℂ} (hEm : ∀ k, MeasurableSet (E k))
    (hE : ∀ k, 0 < volume (E k) ∧ volume (E k) < ⊤) (hone : (volume (E (σ 0))).toReal ≤ 1)
    (hhm : ∀ k, Measurable (h k)) (hdom : ∀ k x, ‖h k x‖ ≤ (E k).indicator (1 : ℝ → ℝ) x)
    {P : Finset (ℤ × ℤ × ℤ)} (hP : (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α) (F : Set ℝ)
    [DecidablePred fun t : ℤ × ℤ × ℤ => ¬ timeInt t ⊆ F] {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hφ : ∀ t ∈ P, ∀ j, IsAdapted N (timeInt t) (freqInt a b j t) (φ t j)) {K : ℝ} (hK : 0 < K)
    (hsizeσ0 : ∀ i, size a b φ i (σ 0) (refG' E h (σ 0))
      (P.filter fun t => ¬ timeInt t ⊆ F) ≤
      ENNReal.ofReal (K * (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2)))
    (hsizeσ : ∀ i k, k ≠ σ 0 → size a b φ i k (refG' E h k)
      (P.filter fun t => ¬ timeInt t ⊆ F) ≤ ENNReal.ofReal K)
    {ε : ℝ} (hε : 0 < ε) :
    triForm (P.filter fun t => ¬ timeInt t ⊆ F) φ (refG' E h) ≤
      96 * max C 0 * K * (3 + 1 / ε) * (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2 - ε) :=
  triForm_outside_le_of_hC4 hν hC4 σ hEm hE hone hhm hdom
    (fun _ ht => hP (Finset.mem_filter.1 ht).1) (fun t ht j => hφ t (Finset.mem_filter.1 ht).1 j) hK
    hsizeσ0 hsizeσ hε

/-! ### The glue with C9 for arbitrary slot roles (`RefSizeSigma.lean`) -/

/-- **C10a, outside the exceptional set, for an arbitrary permutation `σ` of the slots (conditional only on
the weak Bessel inequality `hC4`).** Setting of C9 with the roles `(small, mid, large) = (σ 0, σ 1, σ 2)`:
`E k` (indexed by slot) measurable, `0 < |E (σ 0)| ≤ |E (σ 1)| ≤ |E (σ 2)|`, `1/2 < |E (σ 2)| ≤ 1`,
`h k` measurable with `‖h k‖ ≤ 1_{E k}`, `g'_k = |E k|^{-1/2} h k` (`refG'`); `P ⊆ Idx_ν` finite with packets
adapted with exponent `N ≥ 4`; `P_out = {t ∈ P : I_t ⊄ F_σ}`, `F_σ = refExceptional (E (σ 0)) (E (σ 1))`.
Then for every `ε > 0`, with `K_N = refSizeConst (orthSizeConst N) (sameScaleConst N)`,
`Λ_{P_out}(g') ≤ 96 C⁺ K_N (3 + 1/ε) |E (σ 0)|^{1/2-ε}`. -/
theorem triForm_filter_outside_le_orth_of_hC4 {a b s' α : ℤ} (hν : TriValid a b s' α) {N : ℕ}
    (hN : 4 ≤ N) {C : ℝ} (hC4 : WeakBesselHyp a b s' α N C) (σ : Equiv.Perm (Fin 3))
    {E : Fin 3 → Set ℝ} {h : Fin 3 → ℝ → ℂ} (hEm : ∀ k, MeasurableSet (E k))
    (h01 : volume (E (σ 0)) ≤ volume (E (σ 1))) (h12 : volume (E (σ 1)) ≤ volume (E (σ 2)))
    (hE0 : volume (E (σ 0)) ≠ 0) (hhalf : 1 / 2 < (volume (E (σ 2))).toReal)
    (hone : (volume (E (σ 2))).toReal ≤ 1) (hhm : ∀ k, Measurable (h k))
    (hdom : ∀ k x, ‖h k x‖ ≤ (E k).indicator (1 : ℝ → ℝ) x)
    {P : Finset (ℤ × ℤ × ℤ)} (hP : (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    [DecidablePred fun t : ℤ × ℤ × ℤ => ¬ timeInt t ⊆ refExceptional (E (σ 0)) (E (σ 1))]
    {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hφ : ∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) {ε : ℝ} (hε : 0 < ε) :
    triForm (P.filter fun t => ¬ timeInt t ⊆ refExceptional (E (σ 0)) (E (σ 1))) φ (refG' E h) ≤
      96 * max C 0 * refSizeConst (orthSizeConst N) (sameScaleConst N) * (3 + 1 / ε) *
        (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2 - ε) := by
  obtain ⟨hnz, hnt⟩ := volume_ne_zero_ne_top_of_normalized (E := fun r => E (σ r)) h01 h12 hE0 hhalf
  have hE : ∀ k, 0 < volume (E k) ∧ volume (E k) < ⊤ := by
    intro k
    obtain ⟨r, rfl⟩ := σ.surjective k
    exact ⟨pos_iff_ne_zero.2 (hnz r), lt_top_iff_ne_top.2 (hnt r)⟩
  have hone0 : (volume (E (σ 0))).toReal ≤ 1 :=
    ((ENNReal.toReal_mono (hnt 2) (h01.trans h12)).trans hone)
  have hKpos : 0 < refSizeConst (orthSizeConst N) (sameScaleConst N) := by
    have h2 := (orth_constants_nonneg hN).1
    have h1 : 0 ≤ Real.sqrt (energyConst (sameScaleConst N)) := Real.sqrt_nonneg _
    unfold refSizeConst
    linarith
  have hPF : ∀ t ∈ P.filter fun t => ¬ timeInt t ⊆ refExceptional (E (σ 0)) (E (σ 1)),
      ¬ timeInt t ⊆ refExceptional (E (σ 0)) (E (σ 1)) :=
    fun t ht => (Finset.mem_filter.1 ht).2
  refine triForm_filter_outside_le_of_hC4 hν hC4 σ hEm hE hone0 hhm hdom hP
    (refExceptional (E (σ 0)) (E (σ 1))) hφ hKpos ?_ ?_ hε
  · intro i
    exact size_refG'_σ0_le_orth hν hN (fun t ht => hP (Finset.mem_filter.1 ht).1)
      (fun t ht k => hφ t (Finset.mem_filter.1 ht).1 k) σ hEm h01 h12 hE0 hhalf hone hhm hdom hPF i
  · intro i k hk
    exact size_refG'_ne_σ0_le_orth hν hN (fun t ht => hP (Finset.mem_filter.1 ht).1)
      (fun t ht k => hφ t (Finset.mem_filter.1 ht).1 k) σ hEm h01 h12 hE0 hhalf hone hhm hdom hPF i hk

end PrimeBHT.TimeFrequency.Tile
