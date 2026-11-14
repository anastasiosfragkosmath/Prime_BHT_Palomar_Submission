module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Dyadic weight sums and a counting lemma (blueprint node C4, step 5 (v))

Two elementary facts used in the weak Bessel inequality (C4):

* **Dyadic geometry lemma.** For `I = [a, a + ℓ)` and `q > 1`,
  `∑_{J ∈ 𝒟_d(I)} |J| (1 + dist(J, I^c)/|J|)^{-q} ≤ C_q 2^{-d} |I|`, with the explicit constant
  `C_q = 2q/(q-1)` (`sum_icoWeight_subIco_le`), and, summed over all scales, the bound `4q/(q-1)·|I|`
  (`sum_sum_icoWeight_le`). Here `𝒟_d(I)` is the family `subIco a ℓ d m`, `m < 2^d`, of the `2^d`
  half-open dyadic subintervals of length `ℓ/2^d`, and `dist(J, I^c)` is the concrete
  `icoGap a b l r = min (l - a) (b - r)` for `J = [l, r) ⊆ I = [a, b)` (this is the distance from
  `J` to `I^c`). The weights of `J = [l, r)` are `icoWeight q a b l r = |J| (1 + dist/|J|)^{-q}`.
  `sum_icoWeight_le` is the form consumed by C4: a finite family of tiles whose time intervals
  are among the `subIco a ℓ d m` with fibre cardinality at most `n` has total weight at most
  `n · 4q/(q-1) · |I|`.
* **Counting lemma.** If `ω_m = [c_m - L/2, c_m + L/2)` are pairwise disjoint, then a real `ξ` lies in
  `3ω_m = [c_m - 3L/2, c_m + 3L/2)` for at most three indices (`card_filter_mem_dilate_three_le`).
  The half-open convention for `3ω` is what makes the bound `3`: with half-open `ω_m` and a *closed*
  `3ω_m = [c_m - 3L/2, c_m + 3L/2]` four indices are possible (`L = 1`, `c_m = m`, `ξ = 3/2`).

Further API: `card_filter_mem_Ico_dilate_three_le` (the counting lemma for intervals `[l m, r m)` of
common length, with `3ω` in the normal form `[(x+y)/2 - 3(y-x)/2, (x+y)/2 + 3(y-x)/2)` of the
project's `dilate`), `isGLB_icoGap` (`icoGap` is the infimum of the distances from `J` to `I^c`),
`biUnion_subIco`, `pairwise_disjoint_subIco`, `volume_subIco` (the `subIco a ℓ d m` are exactly
`𝒟_d(I)`), and `subIcoLeft_two_zpow`/`subIcoRight_two_zpow` (the dictionary from the integer
parametrisation `2^s [v, v+1)` of dyadic intervals).

All results are stated over `ℝ` with explicit constants, independently of any tile definition.
-/

public section

open Finset

namespace PrimeBHT.TimeFrequency.Tile

/-! ### Definitions -/

/-- Left endpoint of the `m`-th of the `2^d` dyadic subintervals of `[a, a + ℓ)`. -/
@[expose] noncomputable def subIcoLeft (a ℓ : ℝ) (d m : ℕ) : ℝ := a + m * (ℓ / 2 ^ d)

/-- Right endpoint of the `m`-th of the `2^d` dyadic subintervals of `[a, a + ℓ)`. -/
@[expose] noncomputable def subIcoRight (a ℓ : ℝ) (d m : ℕ) : ℝ := a + (m + 1) * (ℓ / 2 ^ d)

/-- `dist(J, I^c)` for `J = [l, r) ⊆ I = [a, b)`: `min (l - a) (b - r)`. -/
@[expose] noncomputable def icoGap (a b l r : ℝ) : ℝ := min (l - a) (b - r)

/-- The weight `|J| (1 + dist(J, I^c)/|J|)^{-q}` of `J = [l, r) ⊆ I = [a, b)`. -/
@[expose] noncomputable def icoWeight (q a b l r : ℝ) : ℝ :=
  (r - l) * (1 + icoGap a b l r / (r - l)) ^ (-q)

/-! ### Elementary facts about the subintervals -/

theorem subIcoRight_sub_subIcoLeft (a ℓ : ℝ) (d m : ℕ) :
    subIcoRight a ℓ d m - subIcoLeft a ℓ d m = ℓ / 2 ^ d := by
  unfold subIcoRight subIcoLeft
  ring

/-! ### The gap and the weight of the subintervals -/

theorem icoGap_subIco {a ℓ : ℝ} (hℓ : 0 < ℓ) {d m : ℕ} (hm : m < 2 ^ d) :
    icoGap a (a + ℓ) (subIcoLeft a ℓ d m) (subIcoRight a ℓ d m) =
      ((min m (2 ^ d - 1 - m) : ℕ) : ℝ) * (ℓ / 2 ^ d) := by
  have hh : 0 ≤ ℓ / 2 ^ d := by positivity
  have h2 : (2 : ℝ) ^ d ≠ 0 := by positivity
  have hcast : ((2 ^ d - 1 - m : ℕ) : ℝ) = (2 : ℝ) ^ d - 1 - m := by
    have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have h3 : m ≤ 2 ^ d - 1 := by omega
    rw [Nat.cast_sub h3, Nat.cast_sub h1]
    simp
  rw [Nat.cast_min, hcast, min_mul_of_nonneg _ _ hh]
  unfold icoGap subIcoLeft subIcoRight
  congr 1
  · ring
  · field_simp
    ring

theorem icoWeight_subIco {q a ℓ : ℝ} (hℓ : 0 < ℓ) {d m : ℕ} (hm : m < 2 ^ d) :
    icoWeight q a (a + ℓ) (subIcoLeft a ℓ d m) (subIcoRight a ℓ d m) =
      (ℓ / 2 ^ d) * (1 + ((min m (2 ^ d - 1 - m) : ℕ) : ℝ)) ^ (-q) := by
  have hh : ℓ / 2 ^ d ≠ 0 := by positivity
  unfold icoWeight
  rw [subIcoRight_sub_subIcoLeft, icoGap_subIco hℓ hm, mul_div_cancel_right₀ _ hh]

/-! ### Harmonic-type sums -/

/-- `∑_{k=1}^{n} k^{-q} ≤ q/(q-1)` for `q > 1`. -/
theorem sum_range_add_one_rpow_neg_le {q : ℝ} (hq : 1 < q) (n : ℕ) :
    ∑ k ∈ range n, ((k : ℝ) + 1) ^ (-q) ≤ q / (q - 1) := by
  have hq1 : 0 < q - 1 := sub_pos.mpr hq
  cases n with
  | zero =>
    simp only [range_zero, sum_empty]
    positivity
  | succ n =>
    rw [sum_range_succ']
    have hanti : AntitoneOn (fun x : ℝ => x ^ (-q)) (Set.Icc (1 : ℝ) (1 + n)) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
    have hint := hanti.sum_le_integral
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hI : ∫ x in (1 : ℝ)..1 + n, x ^ (-q) =
        ((1 + n) ^ (-q + 1) - 1 ^ (-q + 1)) / (-q + 1) := by
      refine integral_rpow (Or.inr ⟨by linarith, ?_⟩)
      intro h
      rcases Set.mem_uIcc.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have hI2 : ∫ x in (1 : ℝ)..1 + n, x ^ (-q) ≤ 1 / (q - 1) := by
      rw [hI, Real.one_rpow]
      have h4 : -q + 1 = -(q - 1) := by ring
      rw [h4, div_neg, ← neg_div, neg_sub]
      have h3 : 0 < (1 + (n : ℝ)) ^ (-(q - 1)) := by positivity
      exact div_le_div_of_nonneg_right (by linarith) hq1.le
    have hsum : ∑ i ∈ range n, (((i + 1 : ℕ) : ℝ) + 1) ^ (-q) =
        ∑ i ∈ range n, (fun x : ℝ => x ^ (-q)) (1 + ((i + 1 : ℕ) : ℝ)) := by
      refine sum_congr rfl fun i _ => ?_
      simp only [add_comm]
    rw [hsum]
    have h0 : (((0 : ℕ) : ℝ) + 1) ^ (-q) = 1 := by simp
    rw [h0]
    calc _ ≤ 1 / (q - 1) + 1 := by linarith
      _ = q / (q - 1) := by field_simp; ring

/-- The boundary-layer sum: `∑_{m < n} (1 + min(m, n-1-m))^{-q} ≤ 2q/(q-1)`. -/
theorem sum_range_one_add_min_rpow_neg_le {q : ℝ} (hq : 1 < q) (n : ℕ) :
    ∑ m ∈ range n, (1 + ((min m (n - 1 - m) : ℕ) : ℝ)) ^ (-q) ≤ 2 * (q / (q - 1)) := by
  have hf : ∀ k : ℕ, 0 ≤ ((k : ℝ) + 1) ^ (-q) := fun k => by positivity
  have hterm : ∀ m ∈ range n, (1 + ((min m (n - 1 - m) : ℕ) : ℝ)) ^ (-q) ≤
      ((m : ℝ) + 1) ^ (-q) + (((n - 1 - m : ℕ) : ℝ) + 1) ^ (-q) := by
    intro m _
    rcases min_cases m (n - 1 - m) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h, add_comm (1 : ℝ)]
      exact le_add_of_nonneg_right (hf _)
    · rw [h, add_comm (1 : ℝ)]
      exact le_add_of_nonneg_left (hf _)
  calc ∑ m ∈ range n, (1 + ((min m (n - 1 - m) : ℕ) : ℝ)) ^ (-q)
      ≤ ∑ m ∈ range n, (((m : ℝ) + 1) ^ (-q) + (((n - 1 - m : ℕ) : ℝ) + 1) ^ (-q)) :=
        sum_le_sum hterm
    _ = ∑ m ∈ range n, ((m : ℝ) + 1) ^ (-q) +
          ∑ m ∈ range n, (((n - 1 - m : ℕ) : ℝ) + 1) ^ (-q) := sum_add_distrib
    _ = ∑ m ∈ range n, ((m : ℝ) + 1) ^ (-q) + ∑ m ∈ range n, ((m : ℝ) + 1) ^ (-q) := by
        rw [sum_range_reflect (fun k : ℕ => ((k : ℝ) + 1) ^ (-q)) n]
    _ ≤ q / (q - 1) + q / (q - 1) :=
        add_le_add (sum_range_add_one_rpow_neg_le hq n) (sum_range_add_one_rpow_neg_le hq n)
    _ = 2 * (q / (q - 1)) := by ring

/-! ### The dyadic geometry lemma -/

/-- **Dyadic geometry lemma, one scale.** For `I = [a, a + ℓ)` and `q > 1`,
`∑_{J ∈ 𝒟_d(I)} |J| (1 + dist(J, I^c)/|J|)^{-q} ≤ (2q/(q-1)) 2^{-d} |I|`. -/
theorem sum_icoWeight_subIco_le {q : ℝ} (hq : 1 < q) {a ℓ : ℝ} (hℓ : 0 < ℓ) (d : ℕ) :
    ∑ m ∈ range (2 ^ d), icoWeight q a (a + ℓ) (subIcoLeft a ℓ d m) (subIcoRight a ℓ d m) ≤
      2 * (q / (q - 1)) * (ℓ / 2 ^ d) := by
  have hh : 0 < ℓ / 2 ^ d := by positivity
  calc ∑ m ∈ range (2 ^ d), icoWeight q a (a + ℓ) (subIcoLeft a ℓ d m) (subIcoRight a ℓ d m)
      = ∑ m ∈ range (2 ^ d),
          (ℓ / 2 ^ d) * (1 + ((min m (2 ^ d - 1 - m) : ℕ) : ℝ)) ^ (-q) :=
        sum_congr rfl fun m hm => icoWeight_subIco hℓ (mem_range.mp hm)
    _ = (ℓ / 2 ^ d) * ∑ m ∈ range (2 ^ d), (1 + ((min m (2 ^ d - 1 - m) : ℕ) : ℝ)) ^ (-q) :=
        (mul_sum ..).symm
    _ ≤ (ℓ / 2 ^ d) * (2 * (q / (q - 1))) :=
        mul_le_mul_of_nonneg_left (sum_range_one_add_min_rpow_neg_le hq _) hh.le
    _ = 2 * (q / (q - 1)) * (ℓ / 2 ^ d) := by ring

/-- **Dyadic geometry lemma, all scales `d < D`** (uniformly in `D`):
`∑_{d < D} ∑_{J ∈ 𝒟_d(I)} |J| (1 + dist(J, I^c)/|J|)^{-q} ≤ (4q/(q-1)) |I|`. -/
theorem sum_sum_icoWeight_le {q : ℝ} (hq : 1 < q) {a ℓ : ℝ} (hℓ : 0 < ℓ) (D : ℕ) :
    ∑ d ∈ range D, ∑ m ∈ range (2 ^ d),
        icoWeight q a (a + ℓ) (subIcoLeft a ℓ d m) (subIcoRight a ℓ d m) ≤
      4 * (q / (q - 1)) * ℓ := by
  have hgeom : ∑ d ∈ range D, ℓ / 2 ^ d ≤ 2 * ℓ := by
    have h := sum_geometric_two_le D
    calc ∑ d ∈ range D, ℓ / 2 ^ d = ℓ * ∑ d ∈ range D, (1 / 2 : ℝ) ^ d := by
          rw [mul_sum]
          refine sum_congr rfl fun d _ => ?_
          rw [one_div, inv_pow, div_eq_mul_inv]
      _ ≤ ℓ * 2 := mul_le_mul_of_nonneg_left h hℓ.le
      _ = 2 * ℓ := by ring
  have hC : 0 ≤ 2 * (q / (q - 1)) := by
    have : 0 < q - 1 := sub_pos.mpr hq
    positivity
  calc ∑ d ∈ range D, ∑ m ∈ range (2 ^ d),
        icoWeight q a (a + ℓ) (subIcoLeft a ℓ d m) (subIcoRight a ℓ d m)
      ≤ ∑ d ∈ range D, 2 * (q / (q - 1)) * (ℓ / 2 ^ d) :=
        sum_le_sum fun d _ => sum_icoWeight_subIco_le hq hℓ d
    _ = 2 * (q / (q - 1)) * ∑ d ∈ range D, ℓ / 2 ^ d := (mul_sum ..).symm
    _ ≤ 2 * (q / (q - 1)) * (2 * ℓ) := mul_le_mul_of_nonneg_left hgeom hC
    _ = 4 * (q / (q - 1)) * ℓ := by ring

/-! ### Summing over a finite family with bounded multiplicity -/

/-- If `f : T → S` has all fibres of cardinality at most `n` and `w ≥ 0` on `S`, then
`∑_{t ∈ T} w (f t) ≤ n ∑_{x ∈ S} w x`. -/
theorem sum_comp_le_mul_sum {ι κ : Type*} [DecidableEq κ] (T : Finset ι) (S : Finset κ)
    (f : ι → κ) (w : κ → ℝ) (n : ℕ) (hw : ∀ x ∈ S, 0 ≤ w x) (hf : ∀ t ∈ T, f t ∈ S)
    (hcard : ∀ x ∈ S, (T.filter fun t => f t = x).card ≤ n) :
    ∑ t ∈ T, w (f t) ≤ n * ∑ x ∈ S, w x := by
  rw [← sum_fiberwise_of_maps_to hf, mul_sum]
  refine sum_le_sum fun x hx => ?_
  calc ∑ t ∈ T with f t = x, w (f t) = ∑ t ∈ T with f t = x, w x :=
        sum_congr rfl fun t ht => by rw [(mem_filter.mp ht).2]
    _ = (T.filter fun t => f t = x).card * w x := by rw [sum_const, nsmul_eq_mul]
    _ ≤ n * w x := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard x hx) (hw x hx)

/-- **The form consumed by C4 step 5 (v).** Let `T` be a finite family (of tiles) whose time interval
`J_t = [l t, r t)` is the `m`-th subinterval of scale `d` of `I = [a, a + ℓ)`, where `(d, m) = dm t`,
and suppose each pair `(d, m)` occurs for at most `n` members of `T` (`n = 3` for tiles with the
same interval and `ξ_T ∈ 3ω_{t,i}`, by `card_filter_mem_dilate_three_le`). Then
`∑_{t ∈ T} |J_t| (1 + dist(J_t, I^c)/|J_t|)^{-q} ≤ n (4q/(q-1)) |I|`. -/
theorem sum_icoWeight_le {ι : Type*} {q : ℝ} (hq : 1 < q) {a ℓ : ℝ} (hℓ : 0 < ℓ) (T : Finset ι)
    (l r : ι → ℝ) (dm : ι → ℕ × ℕ) (n : ℕ) (hm : ∀ t ∈ T, (dm t).2 < 2 ^ (dm t).1)
    (hl : ∀ t ∈ T, l t = subIcoLeft a ℓ (dm t).1 (dm t).2)
    (hr : ∀ t ∈ T, r t = subIcoRight a ℓ (dm t).1 (dm t).2)
    (hcard : ∀ p : ℕ × ℕ, (T.filter fun t => dm t = p).card ≤ n) :
    ∑ t ∈ T, icoWeight q a (a + ℓ) (l t) (r t) ≤ n * (4 * (q / (q - 1)) * ℓ) := by
  classical
  have hq1 : 0 < q - 1 := sub_pos.mpr hq
  set w : ℕ × ℕ → ℝ := fun p =>
    icoWeight q a (a + ℓ) (subIcoLeft a ℓ p.1 p.2) (subIcoRight a ℓ p.1 p.2) with hw
  have hwnn : ∀ p : ℕ × ℕ, p.2 < 2 ^ p.1 → 0 ≤ w p := by
    intro p hp
    simp only [hw]
    rw [icoWeight_subIco hℓ hp]
    positivity
  set D : ℕ := (T.image dm).sup Prod.fst + 1 with hD
  set S : Finset (ℕ × ℕ) := (T.image dm).filter fun p => p.2 < 2 ^ p.1 with hS
  have hTS : ∀ t ∈ T, dm t ∈ S := fun t ht =>
    mem_filter.mpr ⟨mem_image_of_mem dm ht, hm t ht⟩
  have hsum : ∑ t ∈ T, icoWeight q a (a + ℓ) (l t) (r t) = ∑ t ∈ T, w (dm t) :=
    sum_congr rfl fun t ht => by rw [hl t ht, hr t ht]
  have hSbound : ∑ x ∈ S, w x ≤ 4 * (q / (q - 1)) * ℓ := by
    have hsub : ∑ x ∈ S, w x ≤ ∑ d ∈ range D, ∑ m ∈ range (2 ^ d), w (d, m) := by
      have h1 : ∑ d ∈ range D, ∑ m ∈ range (2 ^ d), w (d, m) =
          ∑ x ∈ (range D).sigma (fun d => range (2 ^ d)), w (x.1, x.2) :=
        sum_sigma' (range D) (fun d => range (2 ^ d)) (fun d m => w (d, m))
      rw [h1]
      have h2 : ∑ x ∈ S, w x = ∑ x ∈ S.image (fun p => (⟨p.1, p.2⟩ : Σ _ : ℕ, ℕ)), w (x.1, x.2) := by
        rw [sum_image]
        intro x _ y _ hxy
        have h1 := congrArg Sigma.fst hxy
        have h2 : x.2 = y.2 := by
          have := congrArg Sigma.snd hxy
          simpa using this
        exact Prod.ext h1 h2
      rw [h2]
      refine sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro x hx
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
        obtain ⟨hp1, hp2⟩ := mem_filter.mp hp
        refine mem_sigma.mpr ⟨mem_range.mpr ?_, mem_range.mpr hp2⟩
        have : p.1 ≤ (T.image dm).sup Prod.fst := le_sup (f := Prod.fst) hp1
        show p.1 < (T.image dm).sup Prod.fst + 1
        omega
      · intro x hx _
        exact hwnn (x.1, x.2) (mem_range.mp (mem_sigma.mp hx).2)
    exact hsub.trans (sum_sum_icoWeight_le hq hℓ D)
  rw [hsum]
  calc ∑ t ∈ T, w (dm t) ≤ n * ∑ x ∈ S, w x :=
        sum_comp_le_mul_sum T S dm w n
          (fun x hx => hwnn x (mem_filter.mp hx).2) hTS
          (fun x _ => hcard x)
    _ ≤ n * (4 * (q / (q - 1)) * ℓ) := by
        refine mul_le_mul_of_nonneg_left hSbound (Nat.cast_nonneg n)

/-! ### Counting lemma -/

/-! ### The gap is the distance to the complement -/

/-! ### From dyadic intervals `2^s [v, v+1)` to the `subIco` parametrisation -/

/-- If `I = [2^{s+d} v', 2^{s+d}(v'+1))` and `J = [2^s v, 2^s (v+1))` with `v = 2^d v' + m`,
then `J` is the `m`-th subinterval of scale `d` of `I` (left endpoint). -/
theorem subIcoLeft_two_zpow (s : ℤ) (d m : ℕ) (v v' : ℤ) (hm : (m : ℤ) = v - 2 ^ d * v') :
    subIcoLeft ((2 : ℝ) ^ (s + d) * v') ((2 : ℝ) ^ (s + d)) d m = (2 : ℝ) ^ s * v := by
  have h2 : (2 : ℝ) ^ (s + d) / 2 ^ d = 2 ^ s := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, mul_div_cancel_right₀ _ (by positivity)]
  have hm' : (m : ℝ) = v - 2 ^ d * v' := by exact_mod_cast hm
  unfold subIcoLeft
  rw [h2, hm', zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
  ring

/-- Right endpoint companion of `subIcoLeft_two_zpow`. -/
theorem subIcoRight_two_zpow (s : ℤ) (d m : ℕ) (v v' : ℤ) (hm : (m : ℤ) = v - 2 ^ d * v') :
    subIcoRight ((2 : ℝ) ^ (s + d) * v') ((2 : ℝ) ^ (s + d)) d m = (2 : ℝ) ^ s * (v + 1) := by
  have h2 : (2 : ℝ) ^ (s + d) / 2 ^ d = 2 ^ s := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, mul_div_cancel_right₀ _ (by positivity)]
  have hm' : (m : ℝ) = v - 2 ^ d * v' := by exact_mod_cast hm
  unfold subIcoRight
  rw [h2, hm', zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
  ring

end PrimeBHT.TimeFrequency.Tile
