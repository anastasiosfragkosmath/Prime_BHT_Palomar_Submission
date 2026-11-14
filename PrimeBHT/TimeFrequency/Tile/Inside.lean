module

public import PrimeBHT.TimeFrequency.Tile.Grid
public import PrimeBHT.TimeFrequency.Tile.Maximal
public import PrimeBHT.TimeFrequency.Tile.Gram
public import PrimeBHT.TimeFrequency.Tile.TreeSum
public import PrimeBHT.TimeFrequency.Tile.Exponents
public import PrimeBHT.Frozen.TriForm
public import PrimeBHT.TimeFrequency.Tile.RefSize

/-!
# Node C10b of the X1 blueprint: the tri-tile form inside the exceptional set (repaired)

Normalized setting of C9 with arbitrary slot roles `σ` (`σ 0` small, `σ 1` middle, `σ 2` large):
`0 < |E_{σ0}| ≤ |E_{σ1}| ≤ |E_{σ2}|`, `1/2 < |E_{σ2}| ≤ 1`, `F = refExceptional (E_{σ0}) (E_{σ1})`
(`= refExceptionalσ σ E` of `RefSizeSigma.lean`, `C₀ = 100`), `ℐ` the maximal dyadic intervals in `F`
(`maxDyadicKeys F`: `J ⊆ F`, parent `Ĵ ⊄ F`), `F̃ = ⋃_{J ∈ ℐ} 3J` (`insideTildeF`),
`Ẽ = E_{σ2} ∖ F̃` (`insideMajorSet E σ`, a function of `E, σ` only).

## Main results

* `triForm_inside_le`: for finite `P ⊆ Idx_{s',α}` with all `I_t ⊆ F`, packets adapted with `N ≥ 3`,
  `‖g_k‖ ≤ |E_k|^{-1/2} 1_{E_k}` (`k ≠ σ2`), `‖g_{σ2}‖ ≤ |E_{σ2}|^{-1/2} 1_Ẽ`:
  `Λ_P(g) ≤ insideConst · |E_{σ0}|^{1/2 - 1/(2(N-1))}`, `insideConst = (270 C₀)²/3`, independent of `N`;
* `triForm_inside_le_eps` (`N ≥ ⌈1/(2ε)⌉ + 11`, bound `insideConst · |E_{σ0}|^{1/2-ε}`) and
  `triForm_refG'_inside_le_eps` (the same for `g = refG' E h`, `|h_k| ≤ 1_{E_k}`, `|h_{σ2}| ≤ 1_Ẽ`);
* `insideMajorSet_facts`: `|F̃| ≤ 3|F| ≤ 1/4`, `Ẽ ⊆ E_{σ2}` measurable, `|E_{σ2}| ≤ 2|Ẽ|`;
* `inside_bound`: the exponent bookkeeping of steps 3-4 in one lemma.

## Proof (blueprint C10b) and corrections

For a time interval `I = I_q ⊆ F` let `n` be its depth (`J = n`-th ancestor of `I` is in `ℐ`,
`exists_dyadicAnc_mem_maxDyadicKeys`; uses only `|F| < ∞`, not openness), `K = 2^n`, `x₀ ∈ Ĵ ∖ F`.
Step 1 (`sum_filter_key_le`): `S_{σ0} ≤ 90 K C₀ |E_{σ0}|^{1/2}`, `D_{σ0}, D_{σ1} ≤ 3·90 K C₀ |I|`
((G4) with `besselConst N ≤ 3`, and the C6 bounds with the weight widened to scale `K|I|`, so the
loss is `2^d`, not the `4^d` of a recentred scale-`|I|` weight); `S_{σ2} ≤ 2|E_{σ2}|^{-1/2}(1+K)^{1-N}/(N-1)`
and `D_{σ2} ≤ 3 · 2 · 2|I|/(1+K)` from `|y - c(I)| > |J|` on `Ẽ` (strict: `c(I)` is interior to `J`).
Step 2 (`sum_mul_prod_le_min`): arrangements A and B give `M²|I| min(K(1+K)^{1-N}, |E_{σ0}|^{1/2}K)`,
`M = 270 C₀`, and `K(1+K)^{1-N} ≤ 2^{-(N-2)n}`. Steps 3-4 (`inside_bound`): **correction:** no sum over
`J ∈ ℐ` is needed: distinct intervals of the same depth are disjoint (their maximal ancestors coincide or
are disjoint) and lie in `F`, so for each depth `Σ|I| ≤ |F| < 1/12`; then `sum_range_min_geom_le`.
The final exponent is exactly `1/2 - 1/(2(N-1))` (checked), `≥ 1/2 - ε` for `N ≥ ⌈1/(2ε)⌉ + 11`, and the
constant is uniform in `N` (`2/(N-1) ≤ 1`, `besselConst N ≤ 3`). The ordering `|E_{σ0}| ≤ |E_{σ1}|` is used
only for nondegeneracy, `|E_{σ0}| ≤ 1` for the geometric sum, `|E_{σ2}| > 1/2` only for
`|E_{σ2}|^{-1/2} ≤ √2`. The statement `F = ⊔ℐ` is not needed and not proved.
-/

@[expose] public noncomputable section

open MeasureTheory Set Finset
open PrimeBHT.Statements
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Tile

/-! ### Dyadic ancestors and the maximal dyadic intervals contained in a set -/

/-- The `k`-th dyadic ancestor of the key `p = (s, v)` of `dyadicInt s v`. -/
def dyadicAnc (p : ℤ × ℤ) (k : ℕ) : ℤ × ℤ := dyadicParent^[k] p

theorem dyadicAnc_zero (p : ℤ × ℤ) : dyadicAnc p 0 = p := rfl

theorem dyadicAnc_succ (p : ℤ × ℤ) (k : ℕ) :
    dyadicAnc p (k + 1) = dyadicParent (dyadicAnc p k) :=
  Function.iterate_succ_apply' _ _ _

theorem dyadicAnc_fst (p : ℤ × ℤ) (k : ℕ) : (dyadicAnc p k).1 = p.1 + k := by
  induction k with
  | zero => simp [dyadicAnc_zero]
  | succ k ih =>
    rw [dyadicAnc_succ]
    simp only [dyadicParent, ih]
    push_cast
    ring

theorem dyadicInt_subset_dyadicAnc (p : ℤ × ℤ) (k : ℕ) :
    dyadicInt p.1 p.2 ⊆ dyadicInt (dyadicAnc p k).1 (dyadicAnc p k).2 := by
  induction k with
  | zero => exact subset_rfl
  | succ k ih =>
    rw [dyadicAnc_succ]
    exact ih.trans (dyadicInt_subset_parent _ _)

theorem left_mem_dyadicInt (s v : ℤ) : (2 : ℝ) ^ s * v ∈ dyadicInt s v :=
  ⟨le_rfl, by have := timeInt_lt (s, v, 0); simpa using this⟩

theorem dyadicInt_nonempty (s v : ℤ) : (dyadicInt s v).Nonempty :=
  ⟨_, left_mem_dyadicInt s v⟩

/-- If `I_a ⊆ I_b` and the scale of `a` is strictly smaller, the parent of `I_a` lies in `I_b`. -/
theorem parent_subset_of_subset_of_lt {a b : ℤ × ℤ} (h : dyadicInt a.1 a.2 ⊆ dyadicInt b.1 b.2)
    (hlt : a.1 < b.1) :
    dyadicInt (dyadicParent a).1 (dyadicParent a).2 ⊆ dyadicInt b.1 b.2 := by
  have hpa : dyadicInt a.1 a.2 ⊆ dyadicInt (dyadicParent a).1 (dyadicParent a).2 :=
    dyadicInt_subset_parent a.1 a.2
  rcases dyadicInt_nested_or_disjoint (dyadicParent a).1 (dyadicParent a).2 b.1 b.2 with
    h1 | h1 | h1
  · exact h1
  · have h2 := scale_le_of_dyadicInt_subset h1
    have hs : b.1 = (dyadicParent a).1 := by
      simp only [dyadicParent] at h2 ⊢
      omega
    have hv := index_eq_of_dyadicInt_subset hs h1
    rw [hs, hv]
  · obtain ⟨x, hx⟩ := dyadicInt_nonempty a.1 a.2
    exact absurd (h hx) (Set.disjoint_left.1 h1 (hpa hx))

/-- Keys of the maximal dyadic intervals contained in `F`: `J ⊆ F` and the parent `Ĵ ⊄ F`
(the blueprint's `ℐ`). -/
def maxDyadicKeys (F : Set ℝ) : Set (ℤ × ℤ) :=
  {p | dyadicInt p.1 p.2 ⊆ F ∧ ¬ dyadicInt (dyadicParent p).1 (dyadicParent p).2 ⊆ F}

/-- Elements of `ℐ` are maximal: a dyadic interval `J' ⊇ J` contained in `F` equals `J`. -/
theorem eq_of_mem_maxDyadicKeys_of_subset {F : Set ℝ} {p p' : ℤ × ℤ} (hp : p ∈ maxDyadicKeys F)
    (h : dyadicInt p.1 p.2 ⊆ dyadicInt p'.1 p'.2) (hF : dyadicInt p'.1 p'.2 ⊆ F) : p = p' := by
  have hle := scale_le_of_dyadicInt_subset h
  rcases hle.lt_or_eq with hlt | heq
  · exact absurd ((parent_subset_of_subset_of_lt h hlt).trans hF) hp.2
  · exact Prod.ext heq (index_eq_of_dyadicInt_subset heq h)

/-- Two elements of `ℐ` are equal or disjoint. -/
theorem eq_of_mem_maxDyadicKeys_of_not_disjoint {F : Set ℝ} {p p' : ℤ × ℤ}
    (hp : p ∈ maxDyadicKeys F) (hp' : p' ∈ maxDyadicKeys F)
    (h : ¬ Disjoint (dyadicInt p.1 p.2) (dyadicInt p'.1 p'.2)) : p = p' := by
  rcases dyadicInt_nested_or_disjoint p.1 p.2 p'.1 p'.2 with h1 | h1 | h1
  · exact eq_of_mem_maxDyadicKeys_of_subset hp h1 hp'.1
  · exact (eq_of_mem_maxDyadicKeys_of_subset hp' h1 hp.1).symm
  · exact absurd h1 h

theorem pairwiseDisjoint_maxDyadicKeys (F : Set ℝ) :
    (maxDyadicKeys F).PairwiseDisjoint fun p => dyadicInt p.1 p.2 :=
  fun _ hp _ hp' hne => by
    by_contra h
    exact hne (eq_of_mem_maxDyadicKeys_of_not_disjoint hp hp' h)

/-- A dyadic interval inside a set `F` of finite measure has an ancestor that is not inside `F`. -/
theorem exists_dyadicAnc_not_subset {F : Set ℝ} (hF : volume F ≠ ⊤) (q : ℤ × ℤ) :
    ∃ n : ℕ, ¬ dyadicInt (dyadicAnc q (n + 1)).1 (dyadicAnc q (n + 1)).2 ⊆ F := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((volume F).toReal * (2 : ℝ) ^ (-q.1))
    (one_lt_two : (1 : ℝ) < 2)
  refine ⟨n, fun hsub => ?_⟩
  have h1 := ENNReal.toReal_mono hF (measure_mono (μ := volume) hsub)
  rw [toReal_volume_dyadicInt, dyadicAnc_fst] at h1
  have hq : (0 : ℝ) < (2 : ℝ) ^ q.1 := zpow_pos (by norm_num) _
  have h2 : (2 : ℝ) ^ (q.1 + ((n + 1 : ℕ) : ℤ)) = (2 : ℝ) ^ q.1 * ((2 : ℝ) ^ n * 2) := by
    rw [zpow_add₀ (by norm_num), zpow_natCast, pow_succ]
  have h3 : (volume F).toReal = (volume F).toReal * (2 : ℝ) ^ (-q.1) * (2 : ℝ) ^ q.1 := by
    rw [zpow_neg, mul_assoc, inv_mul_cancel₀ hq.ne', mul_one]
  have h4 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  rw [h2] at h1
  nlinarith

/-- Every dyadic interval contained in a set `F` of finite measure lies in an element of `ℐ`,
namely one of its ancestors. -/
theorem exists_dyadicAnc_mem_maxDyadicKeys {F : Set ℝ} (hF : volume F ≠ ⊤) {q : ℤ × ℤ}
    (hq : dyadicInt q.1 q.2 ⊆ F) : ∃ n : ℕ, dyadicAnc q n ∈ maxDyadicKeys F := by
  classical
  have hex := exists_dyadicAnc_not_subset hF q
  refine ⟨Nat.find hex, ?_, ?_⟩
  · rcases h : Nat.find hex with _ | m
    · exact hq
    · have hm : m < Nat.find hex := by omega
      have := Nat.find_min hex hm
      exact not_not.1 this
  · rw [← dyadicAnc_succ]
    exact Nat.find_spec hex

/-- Same-depth disjointness: two distinct dyadic intervals `I_q, I_{q'}` whose `n`-th ancestors are
in `ℐ` (the same `n`) are disjoint. -/
theorem disjoint_of_dyadicAnc_mem_maxDyadicKeys {F : Set ℝ} {q q' : ℤ × ℤ} {n : ℕ}
    (hq : dyadicAnc q n ∈ maxDyadicKeys F) (hq' : dyadicAnc q' n ∈ maxDyadicKeys F)
    (hne : q ≠ q') : Disjoint (dyadicInt q.1 q.2) (dyadicInt q'.1 q'.2) := by
  by_contra hnd
  obtain ⟨x, hx, hx'⟩ := Set.not_disjoint_iff.1 hnd
  have hJ : dyadicAnc q n = dyadicAnc q' n := by
    refine eq_of_mem_maxDyadicKeys_of_not_disjoint hq hq' ?_
    exact Set.not_disjoint_iff.2
      ⟨x, dyadicInt_subset_dyadicAnc q n hx, dyadicInt_subset_dyadicAnc q' n hx'⟩
  have hs : q.1 = q'.1 := by
    have := congrArg Prod.fst hJ
    rw [dyadicAnc_fst, dyadicAnc_fst] at this
    omega
  have hv : q.2 = q'.2 := by
    by_contra hv
    have hd : Disjoint (dyadicInt q.1 q.2) (dyadicInt q.1 q'.2) := disjoint_dyadicInt_of_ne hv
    rw [hs] at hd
    exact hnd (by rw [hs]; exact hd)
  exact hne (Prod.ext hs hv)

/-! ### `F̃ = ⋃_{J ∈ ℐ} 3J` and the major subset `Ẽ₃ = E₃ ∖ F̃` -/

/-- `F̃ := ⋃_{J ∈ ℐ} 3J` for the maximal dyadic intervals `ℐ` of `F`. -/
def insideTildeF (F : Set ℝ) : Set ℝ := ⋃ p ∈ maxDyadicKeys F, dilate 3 (dyadicInt p.1 p.2)

/-- `E ∖ F̃`. -/
def insideMajor (F E : Set ℝ) : Set ℝ := E \ insideTildeF F

/-- The major subset of C10 for the slot roles `σ` (`σ 0` small, `σ 1` middle, `σ 2` large):
`Ẽ := E_{σ 2} ∖ F̃` with `F = {M 1_{E_{σ 0}} > C₀|E_{σ 0}|} ∪ {M 1_{E_{σ 1}} > C₀|E_{σ 1}|}`.
It is a function of `E` and `σ` only. -/
def insideMajorSet (E : Fin 3 → Set ℝ) (σ : Equiv.Perm (Fin 3)) : Set ℝ :=
  insideMajor (refExceptional (E (σ 0)) (E (σ 1))) (E (σ 2))

theorem insideMajor_subset (F E : Set ℝ) : insideMajor F E ⊆ E := sdiff_subset

theorem measurableSet_insideTildeF (F : Set ℝ) : MeasurableSet (insideTildeF F) :=
  MeasurableSet.biUnion (Set.to_countable _) fun p _ => by
    rw [dilate_dyadicInt]; exact measurableSet_Ico

theorem measurableSet_insideMajor (F : Set ℝ) {E : Set ℝ} (hE : MeasurableSet E) :
    MeasurableSet (insideMajor F E) :=
  hE.diff (measurableSet_insideTildeF F)

theorem volume_dilate_three_dyadicInt (s v : ℤ) :
    volume (dilate 3 (dyadicInt s v)) = 3 * volume (dyadicInt s v) := by
  rw [dilate_dyadicInt, Real.volume_Ico, volume_dyadicInt,
    show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-- `|F̃| ≤ 3 |F|`. -/
theorem volume_insideTildeF_le (F : Set ℝ) : volume (insideTildeF F) ≤ 3 * volume F := by
  calc volume (insideTildeF F)
      ≤ ∑' p : maxDyadicKeys F, volume (dilate 3 (dyadicInt (p : ℤ × ℤ).1 (p : ℤ × ℤ).2)) :=
        measure_biUnion_le volume (Set.to_countable _)
          (fun p : ℤ × ℤ => dilate 3 (dyadicInt p.1 p.2))
    _ = ∑' p : maxDyadicKeys F, 3 * volume (dyadicInt (p : ℤ × ℤ).1 (p : ℤ × ℤ).2) :=
        tsum_congr fun p => volume_dilate_three_dyadicInt _ _
    _ = 3 * ∑' p : maxDyadicKeys F, volume (dyadicInt (p : ℤ × ℤ).1 (p : ℤ × ℤ).2) :=
        ENNReal.tsum_mul_left
    _ = 3 * volume (⋃ p ∈ maxDyadicKeys F, dyadicInt p.1 p.2) := by
        rw [measure_biUnion (Set.to_countable _) (pairwiseDisjoint_maxDyadicKeys F)
          (fun p _ => measurableSet_dyadicInt _ _)]
    _ ≤ 3 * volume F := by
        gcongr
        exact Set.iUnion₂_subset fun p hp => hp.1

/-- `|F̃| ≤ 3|F| ≤ 1/4` when `|F| < 1/12`. -/
theorem volume_insideTildeF_le_quarter {F : Set ℝ} (hF : volume F < ENNReal.ofReal (1 / 12)) :
    volume (insideTildeF F) ≤ ENNReal.ofReal (1 / 4) := by
  refine (volume_insideTildeF_le F).trans ?_
  calc 3 * volume F ≤ 3 * ENNReal.ofReal (1 / 12) := by gcongr
    _ = ENNReal.ofReal (1 / 4) := by
        rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
        norm_num

/-- `|E| ≤ 2 |E ∖ F̃|` when `|E| > 1/2` and `|F̃| ≤ 1/4`. -/
theorem volume_le_two_mul_insideMajor {F E : Set ℝ} (hEtop : volume E ≠ ⊤)
    (hhalf : 1 / 2 < (volume E).toReal) (hFt : volume (insideTildeF F) ≤ ENNReal.ofReal (1 / 4)) :
    volume E ≤ 2 * volume (insideMajor F E) := by
  have hMtop : volume (insideMajor F E) ≠ ⊤ :=
    ne_top_of_le_ne_top hEtop (measure_mono (insideMajor_subset F E))
  have hFttop : volume (insideTildeF F) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hFt
  have h1 : volume E ≤ volume (insideMajor F E) + volume (insideTildeF F) :=
    (measure_mono (Set.subset_sdiff_union E (insideTildeF F))).trans (measure_union_le _ _)
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hMtop, hFttop⟩) h1
  rw [ENNReal.toReal_add hMtop hFttop] at h2
  have h3 : (volume (insideTildeF F)).toReal ≤ 1 / 4 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hFt
    rwa [ENNReal.toReal_ofReal (by norm_num)] at this
  rw [← ENNReal.ofReal_toReal hEtop, ← ENNReal.ofReal_toReal hMtop,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- Points outside `3J` are far from the centre of every dyadic `I ⊆ J`: `|J| < |y - c(I)|`. -/
theorem lt_abs_sub_intervalCentre_of_notMem_dilate {s v : ℤ} {p : ℤ × ℤ}
    (hI : dyadicInt s v ⊆ dyadicInt p.1 p.2) {y : ℝ} (hy : y ∉ dilate 3 (dyadicInt p.1 p.2)) :
    (2 : ℝ) ^ p.1 < |y - intervalCentre (dyadicInt s v)| := by
  rw [intervalCentre_dyadicInt]
  rw [dilate_dyadicInt, Set.mem_Ico, not_and_or, not_le, not_lt] at hy
  have hsub := (Set.Ico_subset_Ico_iff (timeInt_lt (s, v, 0))).1 hI
  have hs : 0 < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  obtain ⟨h1, h2⟩ := hsub
  simp only at h1 h2
  rw [lt_abs]
  rcases hy with hy | hy
  · right; linarith
  · left; linarith

/-! ### Tail bounds for the large slot -/

/-- The `S`-tail bound: if `‖g‖ ≤ a 1_S` and `S` stays at distance `> r` from `c(I)`, then for a packet
adapted to `I` with exponent `N ≥ 2`:
`|I|^{-1/2} |⟨g, φ⟩| ≤ a · 2 (1 + r/|I|)^{1-N}/(N-1)`. -/
theorem norm_pairing_le_tail {N : ℕ} (hN : 2 ≤ N) {I ω : Set ℝ} {φ : ℝ → ℂ}
    (hφ : IsAdapted N I ω φ) (hL : 0 < (volume I).toReal) {S : Set ℝ} {a r : ℝ} (ha : 0 ≤ a)
    (hr : 0 ≤ r) (hS : ∀ y ∈ S, r < |y - intervalCentre I|) {g : ℝ → ℂ}
    (hdom : ∀ y, ‖g y‖ ≤ a * S.indicator (1 : ℝ → ℝ) y) :
    (volume I).toReal ^ (-(1 : ℝ) / 2) * ‖pairing g φ‖ ≤
      a * (2 * ((1 + r / (volume I).toReal) ^ (1 - (N : ℝ)) / ((N : ℝ) - 1))) := by
  set L := (volume I).toReal with hLdef
  set c := intervalCentre I with hcdef
  have hp : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  set W : ℝ → ℝ := fun y =>
    {x : ℝ | r < |x - c|}.indicator (fun x => (1 + |x - c| / L) ^ (-(N : ℝ))) y with hWdef
  have hWm : MeasurableSet {x : ℝ | r < |x - c|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hWint : Integrable W := (integrable_one_add_abs_sub_div_rpow hp c hL).indicator hWm
  have hW0 : ∀ y, 0 ≤ W y := fun y => Set.indicator_nonneg (fun _ _ => by positivity) y
  have hpt : ∀ y, ‖g y * (starRingEnd ℂ) (φ y)‖ ≤ a * L ^ (-(1 : ℝ) / 2) * W y := by
    intro y
    rw [norm_mul, RCLike.norm_conj]
    by_cases hy : y ∈ S
    · have h1 : ‖g y‖ ≤ a := by simpa [hy] using hdom y
      have h2 := norm_le_of_isAdapted hφ y
      have hW : W y = (1 + |y - c| / L) ^ (-(N : ℝ)) := by
        simp only [hWdef]
        rw [Set.indicator_of_mem (show y ∈ {x : ℝ | r < |x - c|} from hS y hy)]
      rw [hW]
      calc ‖g y‖ * ‖φ y‖ ≤ a * (L ^ (-(1 : ℝ) / 2) * (1 + |y - c| / L) ^ (-(N : ℝ))) :=
            mul_le_mul h1 h2 (norm_nonneg _) ha
        _ = _ := by ring
    · have h1 : ‖g y‖ = 0 := le_antisymm (by simpa [hy] using hdom y) (norm_nonneg _)
      rw [h1, zero_mul]
      exact mul_nonneg (mul_nonneg ha (by positivity)) (hW0 y)
  have hint : ‖pairing g φ‖ ≤ ∫ y, a * L ^ (-(1 : ℝ) / 2) * W y := by
    unfold pairing
    exact (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (ae_of_all _ fun y => norm_nonneg _) (hWint.const_mul _) (ae_of_all _ hpt))
  rw [integral_const_mul] at hint
  have hWval : ∫ y, W y = 2 * L * ((1 + r / L) ^ (1 - (N : ℝ)) / ((N : ℝ) - 1)) :=
    integral_indicator_one_add_abs_sub_div_rpow hp c hL hr
  rw [hWval] at hint
  have hLL : L ^ (-(1 : ℝ) / 2) * L ^ (-(1 : ℝ) / 2) * L = 1 := by
    rw [← Real.rpow_add hL]
    norm_num
    rw [Real.rpow_neg_one]
    field_simp
  calc L ^ (-(1 : ℝ) / 2) * ‖pairing g φ‖
      ≤ L ^ (-(1 : ℝ) / 2) * (a * L ^ (-(1 : ℝ) / 2) *
          (2 * L * ((1 + r / L) ^ (1 - (N : ℝ)) / ((N : ℝ) - 1)))) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = a * (2 * ((1 + r / L) ^ (1 - (N : ℝ)) / ((N : ℝ) - 1))) *
          (L ^ (-(1 : ℝ) / 2) * L ^ (-(1 : ℝ) / 2) * L) := by ring
    _ = _ := by rw [hLL, mul_one]

/-- The `L²` tail: `∫ ‖g‖² (1 + |x - c|/L)^{-2} ≤ a² · 2L (1 + r/L)^{-1}` when `‖g‖ ≤ a 1_S` and
`S` stays at distance `> r` from `c`. -/
theorem integral_norm_sq_weight_le_tail {L c : ℝ} (hL : 0 < L) {S : Set ℝ} {a r : ℝ}
    (hr : 0 ≤ r) (hS : ∀ y ∈ S, r < |y - c|) {g : ℝ → ℂ}
    (hdom : ∀ y, ‖g y‖ ≤ a * S.indicator (1 : ℝ → ℝ) y) :
    ∫ x, ‖g x‖ ^ 2 * (1 + |x - c| / L) ^ (-2 : ℝ) ≤
      a ^ 2 * (2 * L * ((1 + r / L) ^ (1 - (2 : ℝ)) / ((2 : ℝ) - 1))) := by
  have hp : (1 : ℝ) < 2 := by norm_num
  set W : ℝ → ℝ := fun y =>
    {x : ℝ | r < |x - c|}.indicator (fun x => (1 + |x - c| / L) ^ (-(2 : ℝ))) y with hWdef
  have hWm : MeasurableSet {x : ℝ | r < |x - c|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hWint : Integrable W := (integrable_one_add_abs_sub_div_rpow hp c hL).indicator hWm
  have hW0 : ∀ y, 0 ≤ W y := fun y => Set.indicator_nonneg (fun _ _ => by positivity) y
  have hpt : ∀ y, ‖g y‖ ^ 2 * (1 + |y - c| / L) ^ (-2 : ℝ) ≤ a ^ 2 * W y := by
    intro y
    by_cases hy : y ∈ S
    · have h1 : ‖g y‖ ≤ a := by simpa [hy] using hdom y
      have hW : W y = (1 + |y - c| / L) ^ (-(2 : ℝ)) := by
        simp only [hWdef]
        rw [Set.indicator_of_mem (show y ∈ {x : ℝ | r < |x - c|} from hS y hy)]
      rw [hW]
      have h2 : ‖g y‖ ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    · have h1 : ‖g y‖ = 0 := le_antisymm (by simpa [hy] using hdom y) (norm_nonneg _)
      rw [h1]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      exact mul_nonneg (sq_nonneg a) (hW0 y)
  calc ∫ x, ‖g x‖ ^ 2 * (1 + |x - c| / L) ^ (-2 : ℝ) ≤ ∫ x, a ^ 2 * W x :=
        integral_mono_of_nonneg (ae_of_all _ fun y => by positivity) (hWint.const_mul _)
          (ae_of_all _ hpt)
    _ = a ^ 2 * (2 * L * ((1 + r / L) ^ (1 - (2 : ℝ)) / ((2 : ℝ) - 1))) := by
        rw [integral_const_mul, integral_indicator_one_add_abs_sub_div_rpow hp c hL hr]

/-- A function dominated by `a 1_E` with `|E| < ∞` is in `L²`. -/
theorem memLp_two_of_norm_le_indicator {E : Set ℝ} (hE : MeasurableSet E) (htop : volume E ≠ ⊤)
    {a : ℝ} {g : ℝ → ℂ} (hg : Measurable g) (hdom : ∀ y, ‖g y‖ ≤ a * E.indicator (1 : ℝ → ℝ) y) :
    MemLp g 2 := by
  refine MemLp.mono' (g := E.indicator fun _ => a)
    (memLp_indicator_const 2 hE.nullMeasurableSet a (Or.inr htop)) hg.aestronglyMeasurable
    (ae_of_all _ fun y => (hdom y).trans (le_of_eq ?_))
  by_cases hy : y ∈ E <;> simp [hy]

theorem besselConst_le_three {N : ℕ} (hN : 3 ≤ N) : besselConst N ≤ 3 := by
  have h : (3 : ℝ) ≤ N := by exact_mod_cast hN
  unfold besselConst
  have h1 : 4 / (2 * (N : ℝ) - 1) ≤ 4 / 5 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have h2 : 4 / (2 * (N : ℝ) - 3) ≤ 4 / 3 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  linarith


/-! ### Arrangements A and B for one time interval -/

/-- **C10b, step 2** (abstract). For the tiles `T` sharing one time interval of length `L`, with slot
roles `σ` (`σ 0` small, `σ 1` middle, `σ 2` large), coefficients `A k t ≥ 0`, weight `w t`, and
`S_{σ0} ≤ M K x`, `S_{σ2} ≤ M τ`, `D_{σ0}, D_{σ1} ≤ M K L`, `D_{σ2} ≤ M L / K`:
`∑_t w t ∏_k A k t ≤ M² L min(K τ, x K)` (arrangement A: sup in the large slot; B: sup in the small
slot). -/
theorem sum_mul_prod_le_min {ι : Type*} (T : Finset ι) (w : ι → ℝ) (A : Fin 3 → ι → ℝ)
    (σ : Equiv.Perm (Fin 3)) {M K L x τ : ℝ} (hM : 0 ≤ M) (hK : 0 < K) (hL : 0 ≤ L)
    (hx : 0 ≤ x) (hτ : 0 ≤ τ) (hA : ∀ k, ∀ t ∈ T, 0 ≤ A k t)
    (hS0 : ∀ t ∈ T, w t * A (σ 0) t ≤ M * K * x)
    (hS2 : ∀ t ∈ T, w t * A (σ 2) t ≤ M * τ)
    (hD0 : ∑ t ∈ T, A (σ 0) t ^ 2 ≤ M * K * L) (hD1 : ∑ t ∈ T, A (σ 1) t ^ 2 ≤ M * K * L)
    (hD2 : ∑ t ∈ T, A (σ 2) t ^ 2 ≤ M * L / K) :
    ∑ t ∈ T, w t * ∏ k, A k t ≤ M ^ 2 * L * min (K * τ) (x * K) := by
  have hprod : ∀ t, ∏ k, A k t = A (σ 0) t * A (σ 1) t * A (σ 2) t := by
    intro t
    rw [← Equiv.prod_comp σ (fun k => A k t), Fin.prod_univ_three]
  rw [mul_min_of_nonneg _ _ (by positivity)]
  refine le_min ?_ ?_
  · calc ∑ t ∈ T, w t * ∏ k, A k t
        = ∑ t ∈ T, (w t * A (σ 2) t) * A (σ 0) t * A (σ 1) t :=
          sum_congr rfl fun t _ => by rw [hprod]; ring
      _ ≤ (M * τ) * (√(M * K * L) * √(M * K * L)) :=
          sum_mul_mul_le_sqrt_mul_sqrt T (by positivity) hS2 (hA _) (hA _) hD0 hD1
      _ = M ^ 2 * L * (K * τ) := by
          rw [Real.mul_self_sqrt (by positivity)]; ring
  · have hsq : √(M * K * L) * √(M * L / K) = M * L := by
      rw [← Real.sqrt_mul (by positivity)]
      have : M * K * L * (M * L / K) = (M * L) ^ 2 := by field_simp
      rw [this, Real.sqrt_sq (by positivity)]
    calc ∑ t ∈ T, w t * ∏ k, A k t
        = ∑ t ∈ T, (w t * A (σ 0) t) * A (σ 1) t * A (σ 2) t :=
          sum_congr rfl fun t _ => by rw [hprod]; ring
      _ ≤ (M * K * x) * (√(M * K * L) * √(M * L / K)) :=
          sum_mul_mul_le_sqrt_mul_sqrt T (by positivity) hS0 (hA _) (hA _) hD1 hD2
      _ = M ^ 2 * L * (x * K) := by rw [hsq]; ring

/-! ### The exponent bookkeeping (`inside_bound`) -/

/-- **`inside_bound`: the exponent bookkeeping of C10b, steps 3-4, in one lemma.** Let `Q` index the
time intervals of the tiles inside `F`, `ℓ q = |I_q|`, `n q = d` the depth (`|J| = 2^d |I_q|`),
`G q` the contribution of the tiles over `I_q`. If `G q ≤ A |I_q| min(2^{-(N-2)d}, E^{1/2} 2^d)`
and, for every depth `m`, the intervals of depth `m` have total length `≤ V` (they are disjoint and
contained in `F`), then `∑_q G q ≤ 4 A V E^{1/2 - 1/(2(N-1))}`. -/
theorem inside_bound {κ : Type*} (Q : Finset κ) (G ℓ : κ → ℝ) (n : κ → ℕ) {A V E N : ℝ}
    (hA : 0 ≤ A) (hV : 0 ≤ V) (hE0 : 0 < E) (hE1 : E ≤ 1) (hN : 3 ≤ N)
    (hG : ∀ q ∈ Q, G q ≤ A * ℓ q *
      min ((2 : ℝ) ^ (-(N - 2) * (n q : ℝ))) (E ^ (1 / 2 : ℝ) * 2 ^ (n q)))
    (hsum : ∀ m : ℕ, ∑ q ∈ Q with n q = m, ℓ q ≤ V) :
    ∑ q ∈ Q, G q ≤ 4 * A * V * E ^ (1 / 2 - 1 / (2 * (N - 1))) := by
  set m : ℕ → ℝ := fun d => min ((2 : ℝ) ^ (-(N - 2) * (d : ℝ))) (E ^ (1 / 2 : ℝ) * 2 ^ d)
    with hmdef
  have hm0 : ∀ d, 0 ≤ m d := fun d => le_min (by positivity) (by positivity)
  have hx0 : 0 < E ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hE0 _
  have hx1 : E ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hE0.le hE1 (by norm_num)
  set D := Q.sup n + 1
  have hmaps : ∀ q ∈ Q, n q ∈ range D := fun q hq =>
    mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := n) hq))
  calc ∑ q ∈ Q, G q ≤ ∑ q ∈ Q, A * ℓ q * m (n q) := sum_le_sum hG
    _ = ∑ d ∈ range D, ∑ q ∈ Q with n q = d, A * ℓ q * m (n q) :=
        (sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ d ∈ range D, (A * m d) * ∑ q ∈ Q with n q = d, ℓ q := by
        refine sum_congr rfl fun d _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun q hq => ?_
        rw [(mem_filter.1 hq).2]
        ring
    _ ≤ ∑ d ∈ range D, (A * m d) * V :=
        sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (hsum d) (mul_nonneg hA (hm0 d))
    _ = A * V * ∑ d ∈ range D, m d := by
        rw [mul_sum]
        refine sum_congr rfl fun d _ => ?_
        ring
    _ ≤ A * V * (4 * (E ^ (1 / 2 : ℝ)) ^ (1 - 1 / (N - 1))) :=
        mul_le_mul_of_nonneg_left (sum_range_min_geom_le hN hx0 hx1 D) (by positivity)
    _ = 4 * A * V * E ^ (1 / 2 - 1 / (2 * (N - 1))) := by
        rw [sqrt_rpow_one_sub_inv hE0]
        ring


/-! ### The bounds `D_k`, `S_k` for one time interval -/

/-- The constant `M = 270 C₀` of the per-interval bounds (`C₀ = 100`). -/
def insideM : ℝ := 270 * refC0

theorem insideM_pos : 0 < insideM := by norm_num [insideM, refC0]

/-- **C10b, step 1, `D_k` for the small and middle slots** ((G4) + (M5) with the widened weight):
`∑_{t ∈ P, I_t = I} |⟨g, φ_{t,k}⟩|² ≤ 270 C₀ K |I|` for `‖g‖ ≤ |E|^{-1/2} 1_E`, a point
`x₀ ∈ J ∖ {M 1_E > C₀|E|}` of an interval `J ⊇ I` with `|J| ≤ 2K|I|`. -/
theorem sum_sq_pairing_le_of_notMem {N : ℕ} (hN : 3 ≤ N) {a b s' α : ℤ} (k : Fin 3)
    (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (P : Finset (ℤ × ℤ × ℤ)) (hP : ∀ t ∈ P, t ∈ triIdx s' α)
    (hφ : ∀ t ∈ P, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) (t₀ : ℤ × ℤ × ℤ)
    {J : Set ℝ} (hJ : J.OrdConnected) (hJL : 0 < (volume J).toReal) (hIJ : timeInt t₀ ⊆ J)
    {E : Set ℝ} (hEm : MeasurableSet E) (h0 : volume E ≠ 0) (htop : volume E ≠ ⊤) {C₀ : ℝ}
    (hC : 0 ≤ C₀) {g : ℝ → ℂ} (hg : Measurable g)
    (hdom : ∀ y, ‖g y‖ ≤ (volume E).toReal ^ (-(1 : ℝ) / 2) * E.indicator (1 : ℝ → ℝ) y)
    {x₀ K : ℝ} (hK : 1 ≤ K) (hx₀ : x₀ ∈ J) (hxE : x₀ ∉ exceptionalSet E C₀)
    (hJK : (volume J).toReal ≤ 2 * (K * (volume (timeInt t₀)).toReal)) :
    ∑ t ∈ P with timeInt t = timeInt t₀, ‖pairing g (φ t k)‖ ^ 2 ≤
      270 * C₀ * K * (volume (timeInt t₀)).toReal := by
  have hG4 := sum_norm_sq_pairing_sameInterval_le_weighted hN k φ P hP hφ t₀
    (memLp_two_of_norm_le_indicator hEm htop hg hdom)
  have hM := integral_weight_norm_sq_le_of_notMem_exceptionalSet_of_subset
    (show (timeInt t₀).OrdConnected from Set.ordConnected_Ico) (toReal_volume_timeInt_pos t₀)
    hJ hJL hIJ h0 htop hC hg hdom hK hx₀ hxE hJK
  have heq : ∫ x, ‖g x‖ ^ 2 * (1 + |x - intervalCentre (timeInt t₀)| /
        (volume (timeInt t₀)).toReal) ^ (-2 : ℝ) =
      ∫ y, (1 + |y - intervalCentre (timeInt t₀)| / (volume (timeInt t₀)).toReal) ^ (-2 : ℤ) *
        ‖g y‖ ^ 2 := by
    congr 1
    funext x
    rw [mul_comm, ← Real.rpow_intCast]
    norm_num
  rw [heq] at hG4
  have hβ := besselConst_le_three hN
  have hβ0 := (besselConst_pos (by omega : 2 ≤ N)).le
  have hI0 := (toReal_volume_timeInt_pos t₀).le
  have hK0 : 0 ≤ K := by linarith
  calc _ ≤ besselConst N * (90 * K * (volume (timeInt t₀)).toReal * C₀) :=
        hG4.trans (mul_le_mul_of_nonneg_left hM hβ0)
    _ ≤ 3 * (90 * K * (volume (timeInt t₀)).toReal * C₀) :=
        mul_le_mul_of_nonneg_right hβ (by positivity)
    _ = _ := by ring

/-- `K (1 + K)^{1-N} ≤ 2^{-(N-2)d}` for `K = 2^d`, `N ≥ 1`. -/
theorem two_pow_mul_rpow_le (n : ℕ) {N : ℝ} (hN : 1 ≤ N) :
    (2 : ℝ) ^ n * (1 + (2 : ℝ) ^ n) ^ (1 - N) ≤ (2 : ℝ) ^ (-(N - 2) * (n : ℝ)) := by
  have hK0 : (0 : ℝ) < 2 ^ n := by positivity
  calc (2 : ℝ) ^ n * (1 + (2 : ℝ) ^ n) ^ (1 - N) ≤ (2 : ℝ) ^ n * ((2 : ℝ) ^ n) ^ (1 - N) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hK0 (by linarith) (by linarith))
          hK0.le
    _ = ((2 : ℝ) ^ n) ^ (1 + (1 - N)) := by
        rw [Real.rpow_add hK0, Real.rpow_one]
    _ = (2 : ℝ) ^ (-(N - 2) * (n : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1
        ring

/-- **C10b, steps 1-2, for one time interval `I = I_q`** with depth `n` (the `n`-th ancestor `J` of
`I` is a maximal dyadic interval of `F`): the tiles over `I` contribute at most
`M² |I| min(2^{-(N-2)n}, |E_{σ0}|^{1/2} 2^n)`. -/
theorem sum_filter_key_le {N : ℕ} (hN : 3 ≤ N) {a b s' α : ℤ} (σ : Equiv.Perm (Fin 3))
    {E : Fin 3 → Set ℝ} (hEm : ∀ i, MeasurableSet (E i)) (hnz : ∀ i, volume (E i) ≠ 0)
    (hnt : ∀ i, volume (E i) ≠ ⊤) (hhalf : 1 / 2 < (volume (E (σ 2))).toReal)
    (P : Finset (ℤ × ℤ × ℤ)) (hP : ∀ t ∈ P, t ∈ triIdx s' α)
    (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ)
    (hφ : ∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k))
    (g : Fin 3 → ℝ → ℂ) (hg : ∀ k, Measurable (g k))
    (hdom : ∀ k, k ≠ σ 2 → ∀ y,
      ‖g k y‖ ≤ (volume (E k)).toReal ^ (-(1 : ℝ) / 2) * (E k).indicator (1 : ℝ → ℝ) y)
    (hdom2 : ∀ y, ‖g (σ 2) y‖ ≤ (volume (E (σ 2))).toReal ^ (-(1 : ℝ) / 2) *
      (insideMajorSet E σ).indicator (1 : ℝ → ℝ) y)
    (q : ℤ × ℤ) (n : ℕ)
    (hJ : dyadicAnc q n ∈ maxDyadicKeys (refExceptional (E (σ 0)) (E (σ 1)))) :
    ∑ t ∈ P with (t.1, t.2.1) = q,
        (volume (timeInt t)).toReal ^ (-(1 : ℝ) / 2) * ∏ k, ‖pairing (g k) (φ t k)‖ ≤
      insideM ^ 2 * (2 : ℝ) ^ q.1 * min ((2 : ℝ) ^ (-((N : ℝ) - 2) * (n : ℝ)))
        ((volume (E (σ 0))).toReal ^ (1 / 2 : ℝ) * 2 ^ n) := by
  set F := refExceptional (E (σ 0)) (E (σ 1)) with hFdef
  set t₀ : ℤ × ℤ × ℤ := (q.1, q.2, 0) with ht₀
  set L : ℝ := (2 : ℝ) ^ q.1 with hLdef
  set K : ℝ := (2 : ℝ) ^ n with hKdef
  have hL0 : 0 < L := zpow_pos (by norm_num) _
  have hK0 : 0 < K := by positivity
  have hK1 : 1 ≤ K := one_le_pow₀ (by norm_num)
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hfilt : P.filter (fun t => (t.1, t.2.1) = q) = P.filter (fun t => timeInt t = timeInt t₀) :=
    Finset.filter_congr fun t _ => by
      rw [timeInt_eq_iff, Prod.ext_iff]
  rw [hfilt]
  set T := P.filter (fun t => timeInt t = timeInt t₀) with hTdef
  have hTI : ∀ t ∈ T, timeInt t = timeInt t₀ := fun t ht => (mem_filter.1 ht).2
  have hTP : ∀ t ∈ T, t ∈ P := fun t ht => (mem_filter.1 ht).1
  have hI₀ : (volume (timeInt t₀)).toReal = L := toReal_volume_timeInt t₀
  have hIt : ∀ t ∈ T, (volume (timeInt t)).toReal = L := fun t ht => by rw [hTI t ht, hI₀]
  -- the parent `Ĵ` of `J` and the point `x₀ ∈ Ĵ ∖ F`
  set Jh := dyadicAnc q (n + 1) with hJhdef
  have hJ2 := hJ.2
  rw [← dyadicAnc_succ] at hJ2
  obtain ⟨x₀, hx₀J, hx₀F⟩ := Set.not_subset.1 hJ2
  rw [hFdef, refExceptional, Set.mem_union, not_or] at hx₀F
  have hIJh : timeInt t₀ ⊆ dyadicInt Jh.1 Jh.2 := dyadicInt_subset_dyadicAnc q (n + 1)
  have hJhL : (volume (dyadicInt Jh.1 Jh.2)).toReal = 2 * (K * L) := by
    rw [toReal_volume_dyadicInt, hJhdef, dyadicAnc_fst, zpow_add₀ (by norm_num), zpow_natCast,
      pow_succ]
    ring
  have hJhpos : 0 < (volume (dyadicInt Jh.1 Jh.2)).toReal := by rw [hJhL]; positivity
  have hJhOC : (dyadicInt Jh.1 Jh.2).OrdConnected := Set.ordConnected_Ico
  have hJK : (volume (dyadicInt Jh.1 Jh.2)).toReal ≤ 2 * (K * (volume (timeInt t₀)).toReal) := by
    rw [hJhL, hI₀]
  have hσ02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have hσ12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  have hC0 : (0 : ℝ) ≤ refC0 := refC0_pos.le
  -- the large slot: `a = |E_{σ2}|^{-1/2} ≤ 2`, `a² ≤ 2`
  set a₂ : ℝ := (volume (E (σ 2))).toReal ^ (-(1 : ℝ) / 2) with ha₂def
  have hu : 0 < (volume (E (σ 2))).toReal := by linarith
  have ha₂0 : 0 ≤ a₂ := by positivity
  have ha₂sq : a₂ ^ 2 ≤ 2 := by
    have : a₂ ^ 2 = ((volume (E (σ 2))).toReal)⁻¹ := by
      rw [ha₂def, ← Real.rpow_natCast, ← Real.rpow_mul hu.le]
      norm_num [Real.rpow_neg_one]
    rw [this, inv_le_comm₀ hu (by norm_num)]
    linarith
  have ha₂2 : a₂ ≤ 2 := by nlinarith
  have hdom2' : ∀ y, ‖g (σ 2) y‖ ≤ a₂ * (E (σ 2)).indicator (1 : ℝ → ℝ) y := by
    intro y
    refine (hdom2 y).trans (mul_le_mul_of_nonneg_left ?_ ha₂0)
    by_cases hy : y ∈ insideMajorSet E σ
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (insideMajor_subset _ _ hy)]
    · rw [Set.indicator_of_notMem hy]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) y
  -- the large slot stays away from `I`: `|y - c(I)| > |J| = K L` on `Ẽ`
  have hfar : ∀ y ∈ insideMajorSet E σ, K * L < |y - intervalCentre (timeInt t₀)| := by
    intro y hy
    have hy' : y ∉ dilate 3 (dyadicInt (dyadicAnc q n).1 (dyadicAnc q n).2) := by
      intro hmem
      exact hy.2 (Set.mem_biUnion hJ hmem)
    have h := lt_abs_sub_intervalCentre_of_notMem_dilate (dyadicInt_subset_dyadicAnc q n) hy'
    rw [dyadicAnc_fst, zpow_add₀ (by norm_num), zpow_natCast] at h
    calc K * L = (2 : ℝ) ^ q.1 * 2 ^ n := by rw [hLdef, hKdef]; ring
      _ < _ := h
  set τ : ℝ := (1 + K) ^ (1 - (N : ℝ)) with hτdef
  have hτ0 : 0 ≤ τ := by positivity
  have hmain := sum_mul_prod_le_min T
    (fun t => (volume (timeInt t)).toReal ^ (-(1 : ℝ) / 2))
    (fun k t => ‖pairing (g k) (φ t k)‖) σ insideM_pos.le hK0 hL0.le
    (x := (volume (E (σ 0))).toReal ^ (1 / 2 : ℝ)) (τ := τ) (by positivity) hτ0
    (fun _ _ _ => norm_nonneg _) ?hS0 ?hS2 ?hD0 ?hD1 ?hD2
  case hS0 =>
    intro t ht
    have h := norm_pairing_le_of_notMem_exceptionalSet_of_subset (by omega)
      (hφ t (hTP t ht) (σ 0)) (show (timeInt t).OrdConnected from Set.ordConnected_Ico)
      (toReal_volume_timeInt_pos t) hJhOC hJhpos (by rw [hTI t ht]; exact hIJh) (hnz _) (hnt _)
      hC0 (hg _) (hdom _ hσ02) hK1 hx₀J hx₀F.1 (by rw [hTI t ht]; exact hJK)
    refine h.trans ?_
    have hx : 0 ≤ (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2) := by positivity
    calc 90 * K * refC0 * (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2)
        = (90 * refC0) * (K * (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2)) := by ring
      _ ≤ (270 * refC0) * (K * (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by rw [insideM]; ring
  case hS2 =>
    intro t ht
    have h := norm_pairing_le_tail (by omega) (hφ t (hTP t ht) (σ 2))
      (toReal_volume_timeInt_pos t) ha₂0 (by positivity) (r := K * L)
      (by rw [hTI t ht]; exact hfar) hdom2
    have hr : K * L / (volume (timeInt t)).toReal = K := by
      rw [hIt t ht, mul_div_assoc, div_self hL0.ne', mul_one]
    rw [hr] at h
    refine h.trans ?_
    have hτN : τ / ((N : ℝ) - 1) ≤ τ / 2 :=
      div_le_div_of_nonneg_left hτ0 (by norm_num) (by linarith)
    have hτN0 : 0 ≤ τ / ((N : ℝ) - 1) := div_nonneg hτ0 (by linarith)
    calc a₂ * (2 * (τ / ((N : ℝ) - 1))) ≤ 2 * (2 * (τ / 2)) := by
          gcongr
      _ = 2 * τ := by ring
      _ ≤ insideM * τ := mul_le_mul_of_nonneg_right (by norm_num [insideM, refC0]) hτ0
  case hD0 =>
    have h := sum_sq_pairing_le_of_notMem hN (σ 0) φ P hP (fun t ht => hφ t ht (σ 0)) t₀ hJhOC
      hJhpos hIJh (hEm _) (hnz _) (hnt _) hC0 (hg _) (hdom _ hσ02) hK1 hx₀J hx₀F.1 hJK
    rw [hI₀] at h
    exact h.trans_eq (by rw [insideM])
  case hD1 =>
    have h := sum_sq_pairing_le_of_notMem hN (σ 1) φ P hP (fun t ht => hφ t ht (σ 1)) t₀ hJhOC
      hJhpos hIJh (hEm _) (hnz _) (hnt _) hC0 (hg _) (hdom _ hσ12) hK1 hx₀J hx₀F.2 hJK
    rw [hI₀] at h
    exact h.trans_eq (by rw [insideM])
  case hD2 =>
    have hG4 := sum_norm_sq_pairing_sameInterval_le_weighted hN (σ 2) φ P hP
      (fun t ht => hφ t ht (σ 2)) t₀
      (memLp_two_of_norm_le_indicator (hEm _) (hnt _) (hg _) hdom2')
    have htail := integral_norm_sq_weight_le_tail (toReal_volume_timeInt_pos t₀)
      (c := intervalCentre (timeInt t₀)) (by positivity : (0 : ℝ) ≤ K * L) hfar hdom2
    rw [hI₀, mul_div_assoc, div_self hL0.ne', mul_one,
      show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one,
      show (2 : ℝ) - 1 = 1 by norm_num, div_one] at htail
    rw [hI₀] at hG4
    have hβ := besselConst_le_three hN
    have hβ0 := (besselConst_pos (by omega : 2 ≤ N)).le
    have hinv : (1 + K)⁻¹ ≤ K⁻¹ := inv_anti₀ hK0 (by linarith)
    calc ∑ t ∈ T, ‖pairing (g (σ 2)) (φ t (σ 2))‖ ^ 2
        ≤ besselConst N * (a₂ ^ 2 * (2 * L * (1 + K)⁻¹)) :=
          hG4.trans (mul_le_mul_of_nonneg_left htail hβ0)
      _ ≤ 3 * (2 * (2 * L * K⁻¹)) := by
          gcongr
      _ = 12 * L / K := by ring
      _ ≤ insideM * L / K := by
          gcongr
          norm_num [insideM, refC0]
  refine hmain.trans ?_
  rw [hLdef]
  gcongr
  rw [hKdef]
  exact two_pow_mul_rpow_le n (by linarith)


/-! ### The inside bound (C10b) -/

/-- The constant of the inside bound: `4 M² / 12` with `M = 270 C₀`, `C₀ = 100`. -/
def insideConst : ℝ := insideM ^ 2 / 3

theorem insideConst_pos : 0 < insideConst := by
  unfold insideConst; have := insideM_pos; positivity

/-- Nondegeneracy of all three sets from the normalized ordering for the slot roles `σ`. -/
theorem volume_ne_zero_ne_top_of_sigma {σ : Equiv.Perm (Fin 3)} {E : Fin 3 → Set ℝ}
    (hE0 : volume (E (σ 0)) ≠ 0) (h01 : volume (E (σ 0)) ≤ volume (E (σ 1)))
    (h12 : volume (E (σ 1)) ≤ volume (E (σ 2))) (hone : volume (E (σ 2)) ≤ 1) :
    (∀ i, volume (E i) ≠ 0) ∧ ∀ i, volume (E i) ≠ ⊤ := by
  have h2t : volume (E (σ 2)) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hone
  have key : ∀ j, volume (E (σ j)) ≠ 0 ∧ volume (E (σ j)) ≠ ⊤ := by
    intro j
    fin_cases j
    · exact ⟨hE0, ne_top_of_le_ne_top h2t (h01.trans h12)⟩
    · exact ⟨fun h => hE0 (le_antisymm (h ▸ h01) bot_le), ne_top_of_le_ne_top h2t h12⟩
    · exact ⟨fun h => hE0 (le_antisymm (h ▸ (h01.trans h12)) bot_le), h2t⟩
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := (key (σ.symm i)).1; rwa [Equiv.apply_symm_apply] at this
  · have := (key (σ.symm i)).2; rwa [Equiv.apply_symm_apply] at this

/-- **C10b: the tri-tile form inside the exceptional set (repaired), for arbitrary slot roles.**
Normalized setting of C9 with roles `σ` (`σ 0` small, `σ 1` middle, `σ 2` large):
`0 < |E_{σ0}| ≤ |E_{σ1}| ≤ |E_{σ2}|`, `1/2 < |E_{σ2}| ≤ 1`, `F = refExceptional (E_{σ0}) (E_{σ1})`.
For every finite `P ⊆ Idx_{s',α}` all of whose time intervals lie in `F`, packets adapted with
exponent `N ≥ 3`, and `L²`-normalized functions `‖g_k‖ ≤ |E_k|^{-1/2} 1_{E_k}` (`k ≠ σ 2`),
`‖g_{σ2}‖ ≤ |E_{σ2}|^{-1/2} 1_{Ẽ}` with `Ẽ = insideMajorSet E σ = E_{σ2} ∖ F̃`:
`Λ_P(g) ≤ insideConst · |E_{σ0}|^{1/2 - 1/(2(N-1))}`. -/
theorem triForm_inside_le {N : ℕ} (hN : 3 ≤ N) {a b s' α : ℤ} (σ : Equiv.Perm (Fin 3))
    {E : Fin 3 → Set ℝ} (hEm : ∀ i, MeasurableSet (E i)) (hE0 : volume (E (σ 0)) ≠ 0)
    (h01 : volume (E (σ 0)) ≤ volume (E (σ 1))) (h12 : volume (E (σ 1)) ≤ volume (E (σ 2)))
    (hhalf : 1 / 2 < (volume (E (σ 2))).toReal) (hone : volume (E (σ 2)) ≤ 1)
    (P : Finset (ℤ × ℤ × ℤ)) (hP : (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    (hin : ∀ t ∈ P, timeInt t ⊆ refExceptional (E (σ 0)) (E (σ 1)))
    (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ)
    (hφ : ∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k))
    (g : Fin 3 → ℝ → ℂ) (hg : ∀ k, Measurable (g k))
    (hdom : ∀ k, k ≠ σ 2 → ∀ y,
      ‖g k y‖ ≤ (volume (E k)).toReal ^ (-(1 : ℝ) / 2) * (E k).indicator (1 : ℝ → ℝ) y)
    (hdom2 : ∀ y, ‖g (σ 2) y‖ ≤ (volume (E (σ 2))).toReal ^ (-(1 : ℝ) / 2) *
      (insideMajorSet E σ).indicator (1 : ℝ → ℝ) y) :
    triForm P φ g ≤
      insideConst * (volume (E (σ 0))).toReal ^ (1 / 2 - 1 / (2 * ((N : ℝ) - 1))) := by
  obtain ⟨hnz, hnt⟩ := volume_ne_zero_ne_top_of_sigma hE0 h01 h12 hone
  set F := refExceptional (E (σ 0)) (E (σ 1)) with hFdef
  have hFlt : volume F < ENNReal.ofReal (1 / 12) :=
    volume_refExceptional_lt (hEm _) (hEm _) (hnz _) (hnz _) (hnt _) (hnt _)
  have hFtop : volume F ≠ ⊤ := ne_top_of_lt (hFlt.trans_le le_top)
  have hV12 : (volume F).toReal < 1 / 12 := ENNReal.toReal_lt_of_lt_ofReal hFlt
  have hP' : ∀ t ∈ P, t ∈ triIdx s' α := fun t ht => hP ht
  set key : ℤ × ℤ × ℤ → ℤ × ℤ := fun t => (t.1, t.2.1) with hkey
  set Q := P.image key with hQ
  have hQF : ∀ q ∈ Q, dyadicInt q.1 q.2 ⊆ F := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hq
    exact hin t ht
  have hex : ∀ q : ℤ × ℤ, ∃ n : ℕ, q ∈ Q → dyadicAnc q n ∈ maxDyadicKeys F := by
    intro q
    by_cases hq : q ∈ Q
    · obtain ⟨n, hn⟩ := exists_dyadicAnc_mem_maxDyadicKeys hFtop (hQF q hq)
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => absurd h hq⟩
  choose n hn using hex
  set f : ℤ × ℤ × ℤ → ℝ := fun t =>
    (volume (timeInt t)).toReal ^ (-(1 : ℝ) / 2) * ∏ k, ‖pairing (g k) (φ t k)‖ with hfdef
  have hsplit : triForm P φ g = ∑ q ∈ Q, ∑ t ∈ P with key t = q, f t :=
    (sum_fiberwise_of_maps_to (fun t ht => mem_image_of_mem key ht) f).symm
  have hE0' : 0 < (volume (E (σ 0))).toReal := ENNReal.toReal_pos (hnz _) (hnt _)
  have hE1' : (volume (E (σ 0))).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top ((h01.trans h12).trans hone)
    simpa using this
  have hbound := inside_bound Q (fun q => ∑ t ∈ P with key t = q, f t)
    (fun q => (2 : ℝ) ^ q.1) n (A := insideM ^ 2) (V := (volume F).toReal)
    (E := (volume (E (σ 0))).toReal) (N := (N : ℝ)) (by positivity) ENNReal.toReal_nonneg hE0'
    hE1' (by exact_mod_cast hN)
    (fun q hq => sum_filter_key_le hN σ hEm hnz hnt hhalf P hP' φ hφ g hg hdom hdom2 q (n q)
      (hn q hq))
    (fun m => ?_)
  · rw [hsplit]
    refine hbound.trans ?_
    have hEp : 0 ≤ (volume (E (σ 0))).toReal ^ (1 / 2 - 1 / (2 * ((N : ℝ) - 1))) := by positivity
    have hM2 : 0 ≤ insideM ^ 2 := by positivity
    calc 4 * insideM ^ 2 * (volume F).toReal *
          (volume (E (σ 0))).toReal ^ (1 / 2 - 1 / (2 * ((N : ℝ) - 1)))
        ≤ 4 * insideM ^ 2 * (1 / 12) *
          (volume (E (σ 0))).toReal ^ (1 / 2 - 1 / (2 * ((N : ℝ) - 1))) := by
          gcongr
      _ = _ := by unfold insideConst; ring
  · -- the intervals of depth `m` are disjoint and lie in `F`
    set S := Q.filter (fun q => n q = m) with hS
    have hdisj : (S : Set (ℤ × ℤ)).PairwiseDisjoint fun q => dyadicInt q.1 q.2 := by
      intro q hq q' hq' hne
      simp only [hS, coe_filter, Set.mem_ofPred_eq] at hq hq'
      have h1 := hn q hq.1
      have h2 := hn q' hq'.1
      rw [hq.2] at h1
      rw [hq'.2] at h2
      exact disjoint_of_dyadicAnc_mem_maxDyadicKeys h1 h2 hne
    have hfin : ∀ q ∈ S, volume (dyadicInt q.1 q.2) ≠ ⊤ := fun q _ => by
      rw [volume_dyadicInt]; exact ENNReal.ofReal_ne_top
    calc ∑ q ∈ S, (2 : ℝ) ^ q.1 = ∑ q ∈ S, (volume (dyadicInt q.1 q.2)).toReal :=
          sum_congr rfl fun q _ => (toReal_volume_dyadicInt _ _).symm
      _ = (∑ q ∈ S, volume (dyadicInt q.1 q.2)).toReal := (ENNReal.toReal_sum hfin).symm
      _ = (volume (⋃ q ∈ S, dyadicInt q.1 q.2)).toReal := by
          rw [measure_biUnion_finset hdisj (fun q _ => measurableSet_dyadicInt _ _)]
      _ ≤ (volume F).toReal := by
          refine ENNReal.toReal_mono hFtop (measure_mono ?_)
          exact Set.iUnion₂_subset fun q hq => hQF q (mem_filter.1 hq).1

/-- **C10b with the `ε`-loss.** For `ε > 0` and `N ≥ N_ε = ⌈1/(2ε)⌉ + 11`:
`Λ_{P_in}(g) ≤ insideConst · |E_{σ0}|^{1/2 - ε}` (the constant does not depend on `ε` or `N`). -/
theorem triForm_inside_le_eps {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : ⌈1 / (2 * ε)⌉₊ + 11 ≤ N)
    {a b s' α : ℤ} (σ : Equiv.Perm (Fin 3))
    {E : Fin 3 → Set ℝ} (hEm : ∀ i, MeasurableSet (E i)) (hE0 : volume (E (σ 0)) ≠ 0)
    (h01 : volume (E (σ 0)) ≤ volume (E (σ 1))) (h12 : volume (E (σ 1)) ≤ volume (E (σ 2)))
    (hhalf : 1 / 2 < (volume (E (σ 2))).toReal) (hone : volume (E (σ 2)) ≤ 1)
    (P : Finset (ℤ × ℤ × ℤ)) (hP : (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    (hin : ∀ t ∈ P, timeInt t ⊆ refExceptional (E (σ 0)) (E (σ 1)))
    (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ)
    (hφ : ∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k))
    (g : Fin 3 → ℝ → ℂ) (hg : ∀ k, Measurable (g k))
    (hdom : ∀ k, k ≠ σ 2 → ∀ y,
      ‖g k y‖ ≤ (volume (E k)).toReal ^ (-(1 : ℝ) / 2) * (E k).indicator (1 : ℝ → ℝ) y)
    (hdom2 : ∀ y, ‖g (σ 2) y‖ ≤ (volume (E (σ 2))).toReal ^ (-(1 : ℝ) / 2) *
      (insideMajorSet E σ).indicator (1 : ℝ → ℝ) y) :
    triForm P φ g ≤ insideConst * (volume (E (σ 0))).toReal ^ (1 / 2 - ε) := by
  obtain ⟨h1, h12'⟩ := natCeil_inv_le_sub_one hε hN
  have hN3 : 3 ≤ N := by exact_mod_cast (show (3 : ℝ) ≤ N by linarith)
  obtain ⟨hnz, hnt⟩ := volume_ne_zero_ne_top_of_sigma hE0 h01 h12 hone
  have hE0' : 0 < (volume (E (σ 0))).toReal := ENNReal.toReal_pos (hnz _) (hnt _)
  have hE1' : (volume (E (σ 0))).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top ((h01.trans h12).trans hone)
    simpa using this
  refine (triForm_inside_le hN3 σ hEm hE0 h01 h12 hhalf hone P hP hin φ hφ g hg hdom
    hdom2).trans (mul_le_mul_of_nonneg_left ?_ insideConst_pos.le)
  refine rpow_half_sub_le hE0' hE1' ?_
  have hN1 : 0 < (N : ℝ) - 1 := by linarith
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ (by positivity)] at h1
  nlinarith

/-- **C10b in terms of the `h_k`** (`g'_k = |E_k|^{-1/2} h_k`, the role-free `refG'` of C9):
for `|h_k| ≤ 1_{E_k}` (`k ≠ σ 2`) and `|h_{σ2}| ≤ 1_Ẽ`,
`Λ_{P_in}(g') ≤ insideConst · |E_{σ0}|^{1/2-ε}` for `N ≥ ⌈1/(2ε)⌉ + 11`. -/
theorem triForm_refG'_inside_le_eps {ε : ℝ} (hε : 0 < ε) {N : ℕ}
    (hN : ⌈1 / (2 * ε)⌉₊ + 11 ≤ N) {a b s' α : ℤ} (σ : Equiv.Perm (Fin 3))
    {E : Fin 3 → Set ℝ} (hEm : ∀ i, MeasurableSet (E i)) (hE0 : volume (E (σ 0)) ≠ 0)
    (h01 : volume (E (σ 0)) ≤ volume (E (σ 1))) (h12 : volume (E (σ 1)) ≤ volume (E (σ 2)))
    (hhalf : 1 / 2 < (volume (E (σ 2))).toReal) (hone : volume (E (σ 2)) ≤ 1)
    (P : Finset (ℤ × ℤ × ℤ)) (hP : (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    (hin : ∀ t ∈ P, timeInt t ⊆ refExceptional (E (σ 0)) (E (σ 1)))
    (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ)
    (hφ : ∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k))
    (h : Fin 3 → ℝ → ℂ) (hh : ∀ k, Measurable (h k))
    (hhdom : ∀ k, k ≠ σ 2 → ∀ y, ‖h k y‖ ≤ (E k).indicator (1 : ℝ → ℝ) y)
    (hhdom2 : ∀ y, ‖h (σ 2) y‖ ≤ (insideMajorSet E σ).indicator (1 : ℝ → ℝ) y) :
    triForm P φ (refG' E h) ≤ insideConst * (volume (E (σ 0))).toReal ^ (1 / 2 - ε) := by
  refine triForm_inside_le_eps hε hN σ hEm hE0 h01 h12 hhalf hone P hP hin φ hφ (refG' E h)
    (fun k => measurable_const.mul (hh k)) ?_ ?_
  · intro k hk y
    exact norm_ofReal_mul_le_indicator (refScale'_nonneg E k) (hhdom k hk) y
  · intro y
    exact norm_ofReal_mul_le_indicator (refScale'_nonneg E (σ 2)) hhdom2 y

/-! ### The side facts of C10 for the slot roles `σ` -/

/-- **C10, side facts** for the roles `σ`: with `F = refExceptional (E_{σ0}) (E_{σ1})`,
`|F̃| ≤ 3|F| ≤ 1/4`, `Ẽ ⊆ E_{σ2}` is measurable and `|E_{σ2}| ≤ 2|Ẽ|`. (`Ẽ = insideMajorSet E σ`
depends only on `E` and `σ`, by definition.) -/
theorem insideMajorSet_facts {σ : Equiv.Perm (Fin 3)} {E : Fin 3 → Set ℝ}
    (hEm : ∀ i, MeasurableSet (E i)) (hE0 : volume (E (σ 0)) ≠ 0)
    (h01 : volume (E (σ 0)) ≤ volume (E (σ 1))) (h12 : volume (E (σ 1)) ≤ volume (E (σ 2)))
    (hhalf : 1 / 2 < (volume (E (σ 2))).toReal) (hone : volume (E (σ 2)) ≤ 1) :
    volume (insideTildeF (refExceptional (E (σ 0)) (E (σ 1)))) ≤
        3 * volume (refExceptional (E (σ 0)) (E (σ 1))) ∧
      volume (insideTildeF (refExceptional (E (σ 0)) (E (σ 1)))) ≤ ENNReal.ofReal (1 / 4) ∧
      MeasurableSet (insideMajorSet E σ) ∧ insideMajorSet E σ ⊆ E (σ 2) ∧
      volume (E (σ 2)) ≤ 2 * volume (insideMajorSet E σ) := by
  obtain ⟨hnz, hnt⟩ := volume_ne_zero_ne_top_of_sigma hE0 h01 h12 hone
  have hFlt := volume_refExceptional_lt (hEm (σ 0)) (hEm (σ 1)) (hnz _) (hnz _) (hnt _) (hnt _)
  have hq := volume_insideTildeF_le_quarter hFlt
  exact ⟨volume_insideTildeF_le _, hq, measurableSet_insideMajor _ (hEm _),
    insideMajor_subset _ _, volume_le_two_mul_insideMajor (hnt _) hhalf hq⟩


/-! ### The interface for the assembly (`Assemble.lean`) -/

open Classical in
/-- The inside bound in the form consumed by the assembly of M1(ε): the major subset `Et` is chosen
after `σ, E` and before the parameters, tiles, packets and functions. -/
def InsideBound (ε : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin 3)) (E : Fin 3 → Set ℝ), (∀ k, MeasurableSet (E k)) →
    volume (E (σ 0)) ≤ volume (E (σ 1)) → volume (E (σ 1)) ≤ volume (E (σ 2)) →
    volume (E (σ 0)) ≠ 0 → 1 / 2 < (volume (E (σ 2))).toReal → (volume (E (σ 2))).toReal ≤ 1 →
    ∃ Et : Set ℝ, MeasurableSet Et ∧ Et ⊆ E (σ 2) ∧ volume (E (σ 2)) ≤ 2 * volume Et ∧
      ∀ (a b s' α : ℤ), TriValid a b s' α → ∀ (P : Finset (ℤ × ℤ × ℤ)), ↑P ⊆ triIdx s' α →
        ∀ φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ,
          (∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) →
          ∀ h : Fin 3 → ℝ → ℂ, (∀ k, Measurable (h k)) →
            (∀ k, k ≠ σ 2 → ∀ x, ‖h k x‖ ≤ (E k).indicator (1 : ℝ → ℝ) x) →
            (∀ x, ‖h (σ 2) x‖ ≤ Et.indicator (1 : ℝ → ℝ) x) →
            triForm (P.filter fun t => timeInt t ⊆ refExceptional (E (σ 0)) (E (σ 1))) φ
                (refG' E h) ≤
              C * (volume (E (σ 0))).toReal ^ ((1 : ℝ) / 2 - ε)

/-- **C10b for the assembly**: `InsideBound ε N insideConst` for every `ε > 0` and
`N ≥ ⌈1/(2ε)⌉ + 11`; the constant `insideConst` depends neither on `ε` nor on `N`, and
`Et = insideMajorSet E σ`. -/
theorem insideBound_of_le {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : ⌈1 / (2 * ε)⌉₊ + 11 ≤ N) :
    InsideBound ε N insideConst := by
  intro σ E hEm h01 h12 hE0 hhalf hone
  have htop : volume (E (σ 2)) ≠ ⊤ := by
    intro h; rw [h] at hhalf; norm_num at hhalf
  have hone' : volume (E (σ 2)) ≤ 1 := by
    rw [← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hone
  obtain ⟨-, -, hm, hsub, h2⟩ := insideMajorSet_facts hEm hE0 h01 h12 hhalf hone'
  refine ⟨insideMajorSet E σ, hm, hsub, h2, ?_⟩
  intro a b s' α _ P hP φ hφ h hh hhdom hhdom2
  classical
  refine triForm_refG'_inside_le_eps hε hN σ hEm hE0 h01 h12 hhalf hone'
    (P.filter fun t => timeInt t ⊆ refExceptional (E (σ 0)) (E (σ 1)))
    (fun t ht => hP (mem_filter.1 ht).1) (fun t ht => (mem_filter.1 ht).2) φ
    (fun t ht => hφ t (mem_filter.1 ht).1) h hh hhdom hhdom2 |>.trans_eq ?_
  norm_num

end PrimeBHT.TimeFrequency.Tile
