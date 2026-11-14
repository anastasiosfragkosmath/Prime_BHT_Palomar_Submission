module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# V16, node B7: the abstract main estimate (energy-halving iteration)

Pure combinatorics and `ℝ≥0∞` arithmetic; no time-frequency theory. The source is
`docs/audits/X2-V16B-route-check.md` (B6, B7) and `drafts/x2-interface/08-V16-Main.lean.txt`.

## Setting

Tiles `ι`, contributions `lam : ι → ℂ`, tile weights `wt`, admissible collections `Adm`, three monotone
energies `e v : Finset ι → ℝ≥0∞`. The step hypothesis `StepHyp` packages V12 (one energy-halving step in the
slot `v`, with the tree count `(∑ w_T) e^q ≤ A`) and V15 (the tree bound `‖Λ_T‖ ≤ K w_T ∏ e_w(T)` on every
removed tree); `hone` is V15 on one-tile trees.

## Main results

* `levelThr q A k = (2^(-k) A)^(1/q)`: the threshold of level `k`.
* `StepHyp`: the step hypothesis (a `Prop`, used only to keep the helper statements short).
* `step_slot`: one application of the step hypothesis in a slot (with the count `∑ w_T ≤ 2^k`).
* `level_step`: a level (the three slots in turn): energies `≤ levelThr (k - 1)` go to `≤ levelThr k`,
  at the cost `24 K 2^k ∏_v min (Λb v) (levelThr k)`.
* `exists_stage`: `n` levels from a start level `c` (the energies are `≤ levelThr c` at the start).
* `norm_sum_le_of_energy_le`: the remainder bound from the one-tile bound `hone`.
* `main_estimate` (`PrimeBHT.TimeFrequency.X2`): `‖Λ(Cs)‖ ≤ 24 K ∑_{k ∈ ℤ} 2^k ∏_v min (Λb v) (levelThr k)`.

## Remarks

* The remainder does not become empty after finitely many stages in general (X1 C10a, correction 3);
  the limit `n → ∞` uses `hone` (the one-tile bound) and `levelThr k → 0`.
* `Λb v < ⊤` is necessary (finding X2-I5); it is used to find the start level.
* `K = ⊤` is handled separately: either some `Λb v = 0` (then every tile of `Cs` has a zero energy factor, so
  `Λ(Cs) = 0`), or the right-hand side is `⊤`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open Filter Topology

namespace PrimeBHT.TimeFrequency.X2.V16

/-! ### Powers of two -/

theorem ennreal_two_zpow_pos (k : ℤ) : (0 : ℝ≥0∞) < 2 ^ k := by
  rw [← ENNReal.rpow_intCast]
  exact ENNReal.rpow_pos (by norm_num) (by simp)

theorem ennreal_two_zpow_ne_zero (k : ℤ) : (2 : ℝ≥0∞) ^ k ≠ 0 := (ennreal_two_zpow_pos k).ne'

theorem ennreal_two_zpow_ne_top (k : ℤ) : (2 : ℝ≥0∞) ^ k ≠ ⊤ := by
  rw [← ENNReal.rpow_intCast]
  exact ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by simp)

theorem ennreal_two_zpow_add (a b : ℤ) : (2 : ℝ≥0∞) ^ (a + b) = 2 ^ a * 2 ^ b := by
  rw [← ENNReal.rpow_intCast, ← ENNReal.rpow_intCast, ← ENNReal.rpow_intCast, Int.cast_add,
    ENNReal.rpow_add _ _ (by norm_num) (by simp)]

theorem ennreal_two_zpow_neg_mul (k : ℤ) : (2 : ℝ≥0∞) ^ (-k) * 2 ^ k = 1 := by
  rw [← ennreal_two_zpow_add, neg_add_cancel, zpow_zero]

theorem ennreal_two_zpow_neg_natCast (n : ℕ) : (2 : ℝ≥0∞) ^ (-(n : ℤ)) = (2⁻¹) ^ n := by
  rw [← ENNReal.rpow_intCast, Int.cast_neg, Int.cast_natCast, ENNReal.rpow_neg,
    ENNReal.rpow_natCast, ENNReal.inv_pow]

theorem ennreal_two_zpow_neg_sub_one (k : ℤ) : (2 : ℝ≥0∞) ^ (-(k - 1)) = 2 * 2 ^ (-k) := by
  have : -(k - 1) = 1 + -k := by ring
  rw [this, ennreal_two_zpow_add, zpow_one]

/-! ### The level thresholds -/

/-- The threshold `(2^(-k) A)^(1/q)` of level `k`. -/
noncomputable def levelThr (q : ℝ) (A : ℝ≥0∞) (k : ℤ) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞) ^ (-k) * A) ^ (1 / q)

theorem levelThr_rpow {q : ℝ} (hq : 0 < q) (A : ℝ≥0∞) (k : ℤ) :
    levelThr q A k ^ q = 2 ^ (-k) * A := by
  rw [levelThr, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq.ne', ENNReal.rpow_one]

theorem levelThr_pred_le {q : ℝ} (hq : 1 ≤ q) (A : ℝ≥0∞) (k : ℤ) :
    levelThr q A (k - 1) ≤ 2 * levelThr q A k := by
  have hq0 : 0 < q := by linarith
  have h1 : (2 : ℝ≥0∞) ^ (-(k - 1)) * A = 2 * (2 ^ (-k) * A) := by
    rw [ennreal_two_zpow_neg_sub_one, mul_assoc]
  rw [levelThr, levelThr, h1, ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / q)]
  refine mul_le_mul_left ?_ _
  calc (2 : ℝ≥0∞) ^ (1 / q) ≤ 2 ^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [div_le_one hq0]; exact hq)
    _ = 2 := ENNReal.rpow_one 2

theorem levelThr_pos {q : ℝ} {A : ℝ≥0∞} (hA0 : 0 < A) (hA : A < ⊤) (k : ℤ) :
    0 < levelThr q A k := by
  refine ENNReal.rpow_pos (ENNReal.mul_pos (ennreal_two_zpow_ne_zero _) hA0.ne') ?_
  exact ENNReal.mul_ne_top (ennreal_two_zpow_ne_top _) hA.ne

theorem levelThr_tendsto {q : ℝ} (hq : 0 < q) {A : ℝ≥0∞} (hA : A < ⊤) (c : ℤ) :
    Tendsto (fun n : ℕ => levelThr q A (c + n)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => ((2 : ℝ≥0∞)⁻¹) ^ n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have ha : (2 : ℝ≥0∞) ^ (-c) * A ≠ ⊤ := ENNReal.mul_ne_top (ennreal_two_zpow_ne_top _) hA.ne
  have h2 : Tendsto (fun n : ℕ => ((2 : ℝ≥0∞) ^ (-c) * A) * ((2 : ℝ≥0∞)⁻¹) ^ n) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul h1 (Or.inr ha)
  have h3 := ((ENNReal.continuous_rpow_const (y := 1 / q)).tendsto 0).comp h2
  rw [ENNReal.zero_rpow_of_pos (by positivity)] at h3
  refine h3.congr fun n => ?_
  simp only [Function.comp, levelThr]
  congr 1
  have : -(c + (n : ℤ)) = -c + -(n : ℤ) := by ring
  rw [this, ennreal_two_zpow_add, ennreal_two_zpow_neg_natCast, mul_assoc, mul_assoc, mul_comm A]

theorem exists_nat_le_levelThr {q : ℝ} (hq : 0 < q) {A Λ : ℝ≥0∞} (hA0 : 0 < A) (hΛ : Λ < ⊤) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → Λ ≤ levelThr q A (-(m : ℤ)) := by
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hA0.ne'
    (ENNReal.rpow_lt_top_of_nonneg hq.le hΛ.ne : Λ ^ q < ⊤).ne
  refine ⟨N, fun m hm => ?_⟩
  rw [levelThr, neg_neg, one_div, ENNReal.le_rpow_inv_iff hq]
  refine hN.le.trans ?_
  have h1 : (N : ℝ≥0∞) ≤ 2 ^ N := by exact_mod_cast (Nat.lt_two_pow_self).le
  calc (N : ℝ≥0∞) * A ≤ 2 ^ N * A := by gcongr
    _ ≤ 2 ^ m * A := by gcongr; norm_num
    _ = 2 ^ (m : ℤ) * A := by rw [zpow_natCast]

/-- A start level: all the bounds `Λb w < ⊤` lie below the thresholds of a single level `c`. This is where
`Λb w < ⊤` is used. -/
theorem exists_start_level {A Λb : Fin 3 → ℝ≥0∞} {q : Fin 3 → ℝ} (hq : ∀ w, 0 < q w)
    (hA0 : ∀ w, 0 < A w) (hΛ : ∀ w, Λb w < ⊤) :
    ∃ c : ℤ, ∀ w, Λb w ≤ levelThr (q w) (A w) c := by
  choose N hN using fun w => exists_nat_le_levelThr (hq w) (hA0 w) (hΛ w)
  refine ⟨-((∑ w, N w : ℕ) : ℤ), fun w => hN w _ ?_⟩
  exact Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)

/-! ### Sums over the removed trees -/

section Trees

variable {ι : Type} [DecidableEq ι]

theorem mem_foldr_union_iff (L : List (Finset ι × ℝ≥0∞)) (x : ι) :
    x ∈ (L.map Prod.fst).foldr (· ∪ ·) ∅ ↔ ∃ T ∈ L, x ∈ T.1 := by
  induction L with
  | nil => simp
  | cons T L ih => simp [ih]

/-- The sum over the union of pairwise disjoint tree sets is controlled by the sum over the trees. -/
theorem enorm_sum_foldr_union_le (lam : ι → ℂ) :
    ∀ L : List (Finset ι × ℝ≥0∞), L.Pairwise (fun T T' => Disjoint T.1 T'.1) →
      ‖∑ P ∈ (L.map Prod.fst).foldr (· ∪ ·) ∅, lam P‖ₑ ≤
        (L.map fun T => ‖∑ P ∈ T.1, lam P‖ₑ).sum
  | [], _ => by simp
  | T :: L, h => by
    rw [List.pairwise_cons] at h
    have hd : Disjoint T.1 ((L.map Prod.fst).foldr (· ∪ ·) ∅) := by
      rw [Finset.disjoint_left]
      intro x hxT hxU
      obtain ⟨T', hT'L, hxT'⟩ := (mem_foldr_union_iff L x).1 hxU
      exact Finset.disjoint_left.1 (h.1 T' hT'L) hxT hxT'
    simp only [List.map_cons, List.foldr_cons, List.sum_cons]
    rw [Finset.sum_union hd]
    exact (enorm_add_le _ _).trans (add_le_add le_rfl (enorm_sum_foldr_union_le lam L h.2))

omit [DecidableEq ι] in
theorem list_sum_map_snd_mul (c : ℝ≥0∞) :
    ∀ L : List (Finset ι × ℝ≥0∞), (L.map fun T => c * T.2).sum = c * (L.map Prod.snd).sum
  | [] => by simp
  | T :: L => by simp [list_sum_map_snd_mul c L, mul_add]

/-- The step hypothesis of `main_estimate`: from every admissible `S`, for every slot `v`, a list `𝒯` of
pairwise disjoint trees inside `S` whose removal leaves an admissible collection of energy `≤ e v S / 2` in
the slot `v`, with the count `(∑ w_T) (e v S)^{q v} ≤ A v` and the tree bound on every `T`. -/
def StepHyp (lam : ι → ℂ) (Adm : Finset ι → Prop) (e : Fin 3 → Finset ι → ℝ≥0∞) (q : Fin 3 → ℝ)
    (A : Fin 3 → ℝ≥0∞) (K : ℝ≥0∞) : Prop :=
  ∀ v (S : Finset ι), Adm S → ∃ 𝒯 : List (Finset ι × ℝ≥0∞),
    (∀ T ∈ 𝒯, T.1 ⊆ S) ∧ 𝒯.Pairwise (fun T T' => Disjoint T.1 T'.1) ∧
    Adm (S \ (𝒯.map Prod.fst).foldr (· ∪ ·) ∅) ∧
    e v (S \ (𝒯.map Prod.fst).foldr (· ∪ ·) ∅) ≤ e v S / 2 ∧
    (𝒯.map Prod.snd).sum * e v S ^ q v ≤ A v ∧
    ∀ T ∈ 𝒯, ‖∑ P ∈ T.1, lam P‖ₑ ≤ K * T.2 * ∏ w, e w T.1

/-- **One step in the slot `v`.** If `e v S ≤ 2 t` (`t = levelThr k`) and `e w S ≤ m w`, one application of the
step hypothesis gives `S' ⊆ S` with `e v S' ≤ t` and `‖Λ S‖ ≤ K 2^k ∏ m + ‖Λ S'‖` (the count of the removed
trees is `≤ 2^k`, because `e v S > t` or nothing is removed). -/
theorem step_slot {lam : ι → ℂ} {Adm : Finset ι → Prop} {e : Fin 3 → Finset ι → ℝ≥0∞}
    {q : Fin 3 → ℝ} {A : Fin 3 → ℝ≥0∞} {K : ℝ≥0∞} (hstep : StepHyp lam Adm e q A K)
    (hmono : ∀ v (S S' : Finset ι), S ⊆ S' → e v S ≤ e v S') {v : Fin 3} (hq : 1 ≤ q v)
    (hA0 : 0 < A v) (hA : A v < ⊤) (k : ℤ) {S : Finset ι} (hS : Adm S) (m : Fin 3 → ℝ≥0∞)
    (hm : ∀ w, e w S ≤ m w) (hv : e v S ≤ 2 * levelThr (q v) (A v) k) :
    ∃ S' : Finset ι, S' ⊆ S ∧ Adm S' ∧ e v S' ≤ levelThr (q v) (A v) k ∧
      ‖∑ P ∈ S, lam P‖ₑ ≤ K * 2 ^ k * ∏ w, m w + ‖∑ P ∈ S', lam P‖ₑ := by
  have hq0 : 0 < q v := by linarith
  by_cases hle : e v S ≤ levelThr (q v) (A v) k
  · exact ⟨S, Finset.Subset.refl S, hS, hle, le_add_self⟩
  rw [not_le] at hle
  obtain ⟨𝒯, hsub, hdisj, hAdm, hhalf, hcount, htree⟩ := hstep v S hS
  set U := (𝒯.map Prod.fst).foldr (· ∪ ·) ∅ with hU
  have hUS : U ⊆ S := by
    intro x hx
    obtain ⟨T, hT, hxT⟩ := (mem_foldr_union_iff 𝒯 x).1 hx
    exact hsub T hT hxT
  -- the count of the removed trees
  have hsnd : (𝒯.map Prod.snd).sum ≤ 2 ^ k := by
    set s := (𝒯.map Prod.snd).sum with hs
    have h1 : levelThr (q v) (A v) k ^ q v ≤ e v S ^ q v := ENNReal.rpow_le_rpow hle.le hq0.le
    rw [levelThr_rpow hq0] at h1
    have h2 : s * 2 ^ (-k) * A v ≤ 1 * A v := by
      rw [one_mul, mul_assoc]
      exact (mul_le_mul_right h1 s).trans hcount
    have h3 : s * 2 ^ (-k) ≤ 1 := (ENNReal.mul_le_mul_iff_left hA0.ne' hA.ne).1 h2
    calc s = s * 2 ^ (-k) * 2 ^ k := by rw [mul_assoc, ennreal_two_zpow_neg_mul, mul_one]
      _ ≤ 1 * 2 ^ k := by gcongr
      _ = 2 ^ k := one_mul _
  refine ⟨S \ U, Finset.sdiff_subset, hAdm, ?_, ?_⟩
  · calc e v (S \ U) ≤ e v S / 2 := hhalf
      _ ≤ 2 * levelThr (q v) (A v) k / 2 := ENNReal.div_le_div_right hv 2
      _ = levelThr (q v) (A v) k := by
          rw [mul_comm]; exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
  · have hsplit : ∑ P ∈ S, lam P = ∑ P ∈ S \ U, lam P + ∑ P ∈ U, lam P :=
      (Finset.sum_sdiff hUS).symm
    have hprod : ∀ T ∈ 𝒯, ‖∑ P ∈ T.1, lam P‖ₑ ≤ (K * ∏ w, m w) * T.2 := by
      intro T hT
      refine (htree T hT).trans ?_
      have : ∏ w, e w T.1 ≤ ∏ w, m w :=
        Finset.prod_le_prod fun w _ => (hmono w T.1 S (hsub T hT)).trans (hm w)
      calc K * T.2 * ∏ w, e w T.1 ≤ K * T.2 * ∏ w, m w := by gcongr
        _ = (K * ∏ w, m w) * T.2 := by ring
    have hlist : (𝒯.map fun T => ‖∑ P ∈ T.1, lam P‖ₑ).sum ≤
        (𝒯.map fun T => (K * ∏ w, m w) * T.2).sum :=
      List.sum_le_sum fun T hT => hprod T hT
    calc ‖∑ P ∈ S, lam P‖ₑ ≤ ‖∑ P ∈ S \ U, lam P‖ₑ + ‖∑ P ∈ U, lam P‖ₑ := by
          rw [hsplit]; exact enorm_add_le _ _
      _ ≤ ‖∑ P ∈ S \ U, lam P‖ₑ + (K * ∏ w, m w) * (𝒯.map Prod.snd).sum := by
          rw [← list_sum_map_snd_mul]
          exact add_le_add le_rfl ((enorm_sum_foldr_union_le lam 𝒯 hdisj).trans hlist)
      _ ≤ ‖∑ P ∈ S \ U, lam P‖ₑ + (K * ∏ w, m w) * 2 ^ k := by gcongr
      _ = K * 2 ^ k * ∏ w, m w + ‖∑ P ∈ S \ U, lam P‖ₑ := by ring

/-- **One level** (the three slots in turn). From `e w S ≤ levelThr (k - 1)` and `e w S ≤ Λb w` to
`S' ⊆ S` with `e w S' ≤ levelThr k`, at the cost `24 K 2^k ∏_w min (Λb w) (levelThr k)`: each of the three
steps costs `K 2^k ∏ m` with `m w = min (Λb w) (2 levelThr k)`, and `m w ≤ 2 min (Λb w) (levelThr k)`. -/
theorem level_step {lam : ι → ℂ} {Adm : Finset ι → Prop} {e : Fin 3 → Finset ι → ℝ≥0∞}
    {q : Fin 3 → ℝ} {A Λb : Fin 3 → ℝ≥0∞} {K : ℝ≥0∞} (hstep : StepHyp lam Adm e q A K)
    (hmono : ∀ v (S S' : Finset ι), S ⊆ S' → e v S ≤ e v S') (hq : ∀ v, 1 ≤ q v)
    (hA0 : ∀ v, 0 < A v) (hA : ∀ v, A v < ⊤) (k : ℤ) {S : Finset ι} (hS : Adm S)
    (hΛ : ∀ w, e w S ≤ Λb w) (hprev : ∀ w, e w S ≤ levelThr (q w) (A w) (k - 1)) :
    ∃ S' : Finset ι, S' ⊆ S ∧ Adm S' ∧ (∀ w, e w S' ≤ levelThr (q w) (A w) k) ∧
      ‖∑ P ∈ S, lam P‖ₑ ≤
        24 * K * (2 ^ k * ∏ w, min (Λb w) (levelThr (q w) (A w) k)) + ‖∑ P ∈ S', lam P‖ₑ := by
  set m : Fin 3 → ℝ≥0∞ := fun w => min (Λb w) (2 * levelThr (q w) (A w) k) with hm
  have hmS : ∀ w, e w S ≤ m w := fun w =>
    le_min (hΛ w) ((hprev w).trans (levelThr_pred_le (hq w) _ _))
  have hv : ∀ {S : Finset ι}, (∀ w, e w S ≤ m w) → ∀ w, e w S ≤ 2 * levelThr (q w) (A w) k :=
    fun h w => (h w).trans (min_le_right _ _)
  obtain ⟨S₁, h1S, hS1, he1, hn1⟩ :=
    step_slot hstep hmono (v := 0) (hq 0) (hA0 0) (hA 0) k hS m hmS (hv hmS 0)
  have hmS1 : ∀ w, e w S₁ ≤ m w := fun w => (hmono w S₁ S h1S).trans (hmS w)
  obtain ⟨S₂, h2S, hS2, he2, hn2⟩ :=
    step_slot hstep hmono (v := 1) (hq 1) (hA0 1) (hA 1) k hS1 m hmS1 (hv hmS1 1)
  have hmS2 : ∀ w, e w S₂ ≤ m w := fun w => (hmono w S₂ S₁ h2S).trans (hmS1 w)
  obtain ⟨S₃, h3S, hS3, he3, hn3⟩ :=
    step_slot hstep hmono (v := 2) (hq 2) (hA0 2) (hA 2) k hS2 m hmS2 (hv hmS2 2)
  refine ⟨S₃, h3S.trans (h2S.trans h1S), hS3, ?_, ?_⟩
  · intro w
    fin_cases w
    · exact (hmono 0 S₃ S₁ (h3S.trans h2S)).trans he1
    · exact (hmono 1 S₃ S₂ h3S).trans he2
    · exact he3
  · set P : ℝ≥0∞ := ∏ w, min (Λb w) (levelThr (q w) (A w) k) with hP
    have h2 : ∀ w, m w ≤ 2 * min (Λb w) (levelThr (q w) (A w) k) := by
      intro w
      rcases le_total (Λb w) (levelThr (q w) (A w) k) with h | h
      · calc m w ≤ Λb w := min_le_left _ _
          _ = min (Λb w) (levelThr (q w) (A w) k) := (min_eq_left h).symm
          _ ≤ 2 * min (Λb w) (levelThr (q w) (A w) k) :=
            le_mul_of_one_le_left zero_le (by norm_num)
      · calc m w ≤ 2 * levelThr (q w) (A w) k := min_le_right _ _
          _ = 2 * min (Λb w) (levelThr (q w) (A w) k) := by rw [min_eq_right h]
    have hprod : ∏ w, m w ≤ 8 * P := by
      rw [hP, Fin.prod_univ_three, Fin.prod_univ_three]
      calc m 0 * m 1 * m 2 ≤ (2 * min (Λb 0) (levelThr (q 0) (A 0) k)) *
            (2 * min (Λb 1) (levelThr (q 1) (A 1) k)) * (2 * min (Λb 2) (levelThr (q 2) (A 2) k)) := by
            gcongr
            · exact h2 0
            · exact h2 1
            · exact h2 2
        _ = 8 * (min (Λb 0) (levelThr (q 0) (A 0) k) * min (Λb 1) (levelThr (q 1) (A 1) k) *
            min (Λb 2) (levelThr (q 2) (A 2) k)) := by ring
    have hX : K * 2 ^ k * ∏ w, m w ≤ 8 * (K * (2 ^ k * P)) :=
      calc K * 2 ^ k * ∏ w, m w ≤ K * 2 ^ k * (8 * P) := by gcongr
        _ = 8 * (K * (2 ^ k * P)) := by ring
    calc ‖∑ x ∈ S, lam x‖ₑ ≤ K * 2 ^ k * ∏ w, m w + ‖∑ x ∈ S₁, lam x‖ₑ := hn1
      _ ≤ K * 2 ^ k * ∏ w, m w + (K * 2 ^ k * ∏ w, m w + ‖∑ x ∈ S₂, lam x‖ₑ) :=
          add_le_add le_rfl hn2
      _ ≤ K * 2 ^ k * ∏ w, m w + (K * 2 ^ k * ∏ w, m w +
            (K * 2 ^ k * ∏ w, m w + ‖∑ x ∈ S₃, lam x‖ₑ)) :=
          add_le_add le_rfl (add_le_add le_rfl hn3)
      _ ≤ 8 * (K * (2 ^ k * P)) + (8 * (K * (2 ^ k * P)) +
            (8 * (K * (2 ^ k * P)) + ‖∑ x ∈ S₃, lam x‖ₑ)) := by gcongr
      _ = 24 * K * (2 ^ k * P) + ‖∑ x ∈ S₃, lam x‖ₑ := by ring

/-- **`n` levels** from a start level `c` (`e w Cs ≤ Λb w ≤ levelThr c`). -/
theorem exists_stage {lam : ι → ℂ} {Adm : Finset ι → Prop} {e : Fin 3 → Finset ι → ℝ≥0∞}
    {q : Fin 3 → ℝ} {A Λb : Fin 3 → ℝ≥0∞} {K : ℝ≥0∞} (hstep : StepHyp lam Adm e q A K)
    (hmono : ∀ v (S S' : Finset ι), S ⊆ S' → e v S ≤ e v S') (hq : ∀ v, 1 ≤ q v)
    (hA0 : ∀ v, 0 < A v) (hA : ∀ v, A v < ⊤) (c : ℤ)
    (hc : ∀ w, Λb w ≤ levelThr (q w) (A w) c) {Cs : Finset ι} (hCs : Adm Cs)
    (hCsΛ : ∀ w, e w Cs ≤ Λb w) (n : ℕ) :
    ∃ S : Finset ι, S ⊆ Cs ∧ Adm S ∧ (∀ w, e w S ≤ levelThr (q w) (A w) (c + n)) ∧
      ‖∑ P ∈ Cs, lam P‖ₑ ≤
        24 * K * ∑ j ∈ Finset.range n, (2 ^ (c + j + 1) *
          ∏ w, min (Λb w) (levelThr (q w) (A w) (c + j + 1))) + ‖∑ P ∈ S, lam P‖ₑ := by
  induction n with
  | zero =>
    refine ⟨Cs, Finset.Subset.refl _, hCs, fun w => ?_, by simp⟩
    simpa using (hCsΛ w).trans (hc w)
  | succ n ih =>
    obtain ⟨S, hSC, hS, heS, hnS⟩ := ih
    have hΛ : ∀ w, e w S ≤ Λb w := fun w => (hmono w S Cs hSC).trans (hCsΛ w)
    obtain ⟨S', hS'S, hS', heS', hnS'⟩ := level_step hstep hmono hq hA0 hA (c + n + 1) hS hΛ
      (fun w => by rw [add_sub_cancel_right]; exact heS w)
    refine ⟨S', hS'S.trans hSC, hS', fun w => ?_, ?_⟩
    · have : c + ((n + 1 : ℕ) : ℤ) = c + n + 1 := by push_cast; ring
      rw [this]
      exact heS' w
    · rw [Finset.sum_range_succ]
      calc ‖∑ P ∈ Cs, lam P‖ₑ
          ≤ 24 * K * ∑ j ∈ Finset.range n, (2 ^ (c + j + 1) *
              ∏ w, min (Λb w) (levelThr (q w) (A w) (c + j + 1))) + ‖∑ P ∈ S, lam P‖ₑ := hnS
        _ ≤ 24 * K * ∑ j ∈ Finset.range n, (2 ^ (c + j + 1) *
              ∏ w, min (Λb w) (levelThr (q w) (A w) (c + j + 1))) +
            (24 * K * (2 ^ (c + n + 1) * ∏ w, min (Λb w) (levelThr (q w) (A w) (c + n + 1))) +
              ‖∑ P ∈ S', lam P‖ₑ) := add_le_add le_rfl hnS'
        _ = 24 * K * (∑ j ∈ Finset.range n, (2 ^ (c + j + 1) *
              ∏ w, min (Λb w) (levelThr (q w) (A w) (c + j + 1))) +
            2 ^ (c + n + 1) * ∏ w, min (Λb w) (levelThr (q w) (A w) (c + n + 1))) +
              ‖∑ P ∈ S', lam P‖ₑ := by ring

omit [DecidableEq ι] in
/-- **The remainder bound** from the one-tile bound: if `e w S ≤ r w` and `S ⊆ Cs`, then
`‖Λ S‖ ≤ K (∑_{Cs} wt) ∏ r`. -/
theorem norm_sum_le_of_energy_le {lam : ι → ℂ} {wt : ι → ℝ≥0∞} {e : Fin 3 → Finset ι → ℝ≥0∞}
    {K : ℝ≥0∞} (hmono : ∀ v (S S' : Finset ι), S ⊆ S' → e v S ≤ e v S')
    (hone : ∀ P, ‖lam P‖ₑ ≤ K * wt P * ∏ w, e w {P}) {Cs S : Finset ι} (hSC : S ⊆ Cs)
    {r : Fin 3 → ℝ≥0∞} (hr : ∀ w, e w S ≤ r w) :
    ‖∑ P ∈ S, lam P‖ₑ ≤ K * (∑ P ∈ Cs, wt P) * ∏ w, r w := by
  calc ‖∑ P ∈ S, lam P‖ₑ ≤ ∑ P ∈ S, ‖lam P‖ₑ := enorm_sum_le _ _
    _ ≤ ∑ P ∈ S, K * wt P * ∏ w, r w := by
        refine Finset.sum_le_sum fun P hP => (hone P).trans ?_
        have : ∏ w, e w {P} ≤ ∏ w, r w :=
          Finset.prod_le_prod fun w _ =>
            (hmono w {P} S (Finset.singleton_subset_iff.2 hP)).trans (hr w)
        gcongr
    _ = K * (∑ P ∈ S, wt P) * ∏ w, r w := by rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ K * (∑ P ∈ Cs, wt P) * ∏ w, r w := by
        have := Finset.sum_le_sum_of_subset (f := wt) hSC
        gcongr

end Trees

end PrimeBHT.TimeFrequency.X2.V16

namespace PrimeBHT.TimeFrequency.X2

open PrimeBHT.TimeFrequency.X2.V16

/-- **B7 (main estimate, abstract).** The constant is `C = 24`. -/
theorem main_estimate :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ {ι : Type} [DecidableEq ι] (lam : ι → ℂ) (wt : ι → ℝ≥0∞)
      (Adm : Finset ι → Prop) (e : Fin 3 → Finset ι → ℝ≥0∞) (q : Fin 3 → ℝ) (A Λb : Fin 3 → ℝ≥0∞)
      (K : ℝ≥0∞),
      (∀ v, 1 ≤ q v) → (∀ v, 0 < A v) → (∀ v, A v < ⊤) → (∀ v, Λb v < ⊤) → (∀ P, wt P < ⊤) →
      (∀ v (S S' : Finset ι), S ⊆ S' → e v S ≤ e v S') →
      (∀ v (S : Finset ι), Adm S → ∃ 𝒯 : List (Finset ι × ℝ≥0∞),
          (∀ T ∈ 𝒯, T.1 ⊆ S) ∧ 𝒯.Pairwise (fun T T' => Disjoint T.1 T'.1) ∧
          Adm (S \ (𝒯.map Prod.fst).foldr (· ∪ ·) ∅) ∧
          e v (S \ (𝒯.map Prod.fst).foldr (· ∪ ·) ∅) ≤ e v S / 2 ∧
          (𝒯.map Prod.snd).sum * e v S ^ q v ≤ A v ∧
          ∀ T ∈ 𝒯, ‖∑ P ∈ T.1, lam P‖ₑ ≤ K * T.2 * ∏ w, e w T.1) →
      (∀ P, ‖lam P‖ₑ ≤ K * wt P * ∏ w, e w {P}) →
      ∀ Cs : Finset ι, Adm Cs → (∀ v, e v Cs ≤ Λb v) →
        ‖∑ P ∈ Cs, lam P‖ₑ ≤
          C * K * ∑' k : ℤ, (2 : ℝ≥0∞) ^ k * ∏ v, min (Λb v) (((2 : ℝ≥0∞) ^ (-k) * A v) ^ (1 / q v)) := by
  refine ⟨24, by norm_num, ?_⟩
  intro ι _ lam wt Adm e q A Λb K hq hA0 hA hΛ hwt hmono hstep hone Cs hCs hCsΛ
  have hstep' : StepHyp lam Adm e q A K := hstep
  have hq0 : ∀ v, 0 < q v := fun v => lt_of_lt_of_le one_pos (hq v)
  change ‖∑ P ∈ Cs, lam P‖ₑ ≤
    24 * K * ∑' k : ℤ, (2 : ℝ≥0∞) ^ k * ∏ v, min (Λb v) (levelThr (q v) (A v) k)
  -- the case `Λb v = 0` for some `v`: every tile of `Cs` has a vanishing energy factor
  by_cases hz : ∃ v, Λb v = 0
  · obtain ⟨v, hv⟩ := hz
    refine (enorm_sum_le _ _).trans ?_
    have h0 : ∑ P ∈ Cs, ‖lam P‖ₑ = 0 := by
      refine Finset.sum_eq_zero fun P hP => ?_
      have h1 : e v {P} = 0 :=
        le_antisymm (((hmono v {P} Cs (Finset.singleton_subset_iff.2 hP)).trans (hCsΛ v)).trans
          hv.le) zero_le
      have h2 : ∏ w, e w {P} = 0 := Finset.prod_eq_zero (Finset.mem_univ v) h1
      have h3 := hone P
      rw [h2, mul_zero, nonpos_iff_eq_zero] at h3
      exact h3
    rw [h0]
    exact zero_le
  push Not at hz
  by_cases hKt : K = ⊤
  · -- `K = ⊤`: the right-hand side is `⊤` since the series is positive
    have hterm : (2 : ℝ≥0∞) ^ (0 : ℤ) * ∏ v, min (Λb v) (levelThr (q v) (A v) 0) ≠ 0 := by
      rw [zpow_zero, one_mul]
      exact Finset.prod_ne_zero_iff.2 fun v _ =>
        (lt_min (pos_iff_ne_zero.2 (hz v)) (levelThr_pos (hA0 v) (hA v) 0)).ne'
    have hS : ∑' k : ℤ, (2 : ℝ≥0∞) ^ k * ∏ v, min (Λb v) (levelThr (q v) (A v) k) ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 hterm)
        (ENNReal.le_tsum (f := fun k : ℤ => (2 : ℝ≥0∞) ^ k *
          ∏ v, min (Λb v) (levelThr (q v) (A v) k)) 0))
    rw [hKt, ENNReal.mul_top (by norm_num), ENNReal.top_mul hS]
    exact le_top
  -- the main case `K < ⊤`
  obtain ⟨c, hc⟩ := exists_start_level hq0 hA0 hΛ
  set F : ℤ → ℝ≥0∞ := fun k => 2 ^ k * ∏ v, min (Λb v) (levelThr (q v) (A v) k) with hF
  set T : ℝ≥0∞ := ∑' k, F k with hT
  set W : ℝ≥0∞ := ∑ P ∈ Cs, wt P with hW
  have hWt : W ≠ ⊤ := (ENNReal.sum_lt_top.2 fun P _ => hwt P).ne
  have hbound : ∀ n : ℕ, ‖∑ P ∈ Cs, lam P‖ₑ ≤
      24 * K * T + K * W * ∏ w, levelThr (q w) (A w) (c + n) := by
    intro n
    obtain ⟨S, hSC, hS, heS, hnS⟩ := exists_stage hstep' hmono hq hA0 hA c hc hCs hCsΛ n
    have hsum : ∑ j ∈ Finset.range n, F (c + j + 1) ≤ T := by
      have hinj : Function.Injective (fun j : ℕ => c + (j : ℤ) + 1) := by
        intro a b h
        simpa using h
      calc ∑ j ∈ Finset.range n, F (c + j + 1) ≤ ∑' j : ℕ, F (c + j + 1) :=
            ENNReal.sum_le_tsum _
        _ ≤ T := ENNReal.tsum_comp_le_tsum_of_injective hinj F
    calc ‖∑ P ∈ Cs, lam P‖ₑ
        ≤ 24 * K * ∑ j ∈ Finset.range n, F (c + j + 1) + ‖∑ P ∈ S, lam P‖ₑ := hnS
      _ ≤ 24 * K * T + K * W * ∏ w, levelThr (q w) (A w) (c + n) :=
          add_le_add (by gcongr) (norm_sum_le_of_energy_le hmono hone hSC heS)
  have hprod : Tendsto (fun n : ℕ => ∏ w, levelThr (q w) (A w) (c + n)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_finsetProd_of_ne_top (Finset.univ : Finset (Fin 3))
      (fun w _ => levelThr_tendsto (hq0 w) (hA w) c) (fun w _ => ENNReal.zero_ne_top)
    simpa using this
  have hlim : Tendsto (fun n : ℕ => 24 * K * T + K * W * ∏ w, levelThr (q w) (A w) (c + n))
      atTop (𝓝 (24 * K * T)) := by
    have h1 := ENNReal.Tendsto.const_mul hprod (Or.inr (ENNReal.mul_ne_top hKt hWt))
    have h2 := (tendsto_const_nhds (x := 24 * K * T)).add h1
    simpa using h2
  exact ge_of_tendsto' hlim hbound

end PrimeBHT.TimeFrequency.X2
