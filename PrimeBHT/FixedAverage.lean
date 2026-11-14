module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finsupp.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# The fixed-scale bound for `B_L` (node N11, `e:fixed-average`)

For `L : ℕ` and `F G : ℤ → ℂ` put
`B_L(F,G)(x) = (2L+1)⁻¹ ∑_{|n| ≤ L} ‖F(x-n)‖ ‖G(x+n)‖`.
For `u, v ≥ 1` and `1/t = 1/u + 1/v` we prove `‖B_L(F,G)‖_{ℓ^t} ≤ 9 ‖F‖_{ℓ^u} ‖G‖_{ℓ^v}`,
uniformly in `L`.

The case `t < 1` follows the elementary argument of the blueprint (node N11, steps 2-7):
partition `ℤ` into intervals `I_j` of length `2L+1`, control `∑_{x ∈ I_j} B(x)^t` by the triple
interval `3 I_j`, and sum over `j` with Hölder and bounded overlap.
-/

@[expose] public section

namespace PrimeBHT.FixedAverage

open Finset

/-! ### Real-valued finite-sum lemmas -/

section RealLemmas

/-- Power mean inequality for finite sums: `∑ z ≤ n^{1-1/p} (∑ z^p)^{1/p}` for `p ≥ 1`. -/
lemma sum_le_card_rpow_mul {ι : Type*} (s : Finset ι) (z : ι → ℝ) (hz : ∀ i ∈ s, 0 ≤ z i)
    {p : ℝ} (hp : 1 ≤ p) :
    ∑ i ∈ s, z i ≤ (s.card : ℝ) ^ (1 - 1 / p) * (∑ i ∈ s, z i ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have h1 := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg s hp hz
  have h2 : 0 ≤ ∑ i ∈ s, z i := Finset.sum_nonneg hz
  have h3 : 0 ≤ ∑ i ∈ s, z i ^ p :=
    Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hz i hi) p
  have h4 := Real.rpow_le_rpow (Real.rpow_nonneg h2 p) h1 (inv_nonneg.2 hp0.le)
  rw [← Real.rpow_mul h2, mul_inv_cancel₀ hp0.ne', Real.rpow_one,
    Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) h3, ← Real.rpow_mul (Nat.cast_nonneg _)]
    at h4
  convert h4 using 3
  · field_simp
  · rw [one_div]

/-- Power mean inequality for `0 < t ≤ 1`: `∑ z^t ≤ n^{1-t} (∑ z)^t`. -/
lemma sum_rpow_le_card_rpow_mul {ι : Type*} (s : Finset ι) (z : ι → ℝ) (hz : ∀ i ∈ s, 0 ≤ z i)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∑ i ∈ s, z i ^ t ≤ (s.card : ℝ) ^ (1 - t) * (∑ i ∈ s, z i) ^ t := by
  have h := sum_le_card_rpow_mul s (fun i => z i ^ t) (fun i hi => Real.rpow_nonneg (hz i hi) t)
    (p := 1 / t) (by rw [le_div_iff₀ ht]; linarith)
  have e1 : ∀ i ∈ s, (z i ^ t) ^ (1 / t) = z i := fun i hi => by
    rw [← Real.rpow_mul (hz i hi), mul_one_div_cancel ht.ne', Real.rpow_one]
  rw [Finset.sum_congr rfl e1, one_div_one_div] at h
  exact h

/-- The map `(x, n) ↦ (x - n, x + n)` is injective, so the double sum over `I × [-L, L]` is
bounded by the product of the sums over the triple interval. -/
lemma sum_pairs_le {L : ℕ} {I T : Finset ℤ}
    (hIT : ∀ x ∈ I, ∀ n ∈ Finset.Icc (-(L : ℤ)) L, x - n ∈ T ∧ x + n ∈ T)
    {a b : ℤ → ℝ} (ha : ∀ y, 0 ≤ a y) (hb : ∀ y, 0 ≤ b y) :
    ∑ x ∈ I, ∑ n ∈ Finset.Icc (-(L : ℤ)) L, a (x - n) * b (x + n) ≤
      (∑ y ∈ T, a y) * (∑ z ∈ T, b z) := by
  rw [← Finset.sum_product']
  have hinj : Set.InjOn (fun p : ℤ × ℤ => (p.1 - p.2, p.1 + p.2))
      ((I ×ˢ Finset.Icc (-(L : ℤ)) L : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
    intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    ext <;> omega
  rw [← Finset.sum_image (f := fun q : ℤ × ℤ => a q.1 * b q.2) hinj, Finset.sum_mul_sum,
    ← Finset.sum_product']
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun q _ _ => mul_nonneg (ha _) (hb _))
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
  obtain ⟨hx, hn⟩ := Finset.mem_product.1 hp
  exact Finset.mem_product.2 (hIT _ hx _ hn)

/-- Algebra of the constants in the block estimate. -/
lemma block_alg {M A B u v t : ℝ} (hM : 0 < M) (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 < t)
    (huvt : 1 / t = 1 / u + 1 / v) :
    M ^ (1 - t) * (M⁻¹ * ((3 * M) ^ (1 - 1 / u) * A) * ((3 * M) ^ (1 - 1 / v) * B)) ^ t =
      3 ^ (2 * t - 1) * (A * B) ^ t := by
  have h3M : 0 < 3 * M := by positivity
  have e1 : (3 * M) ^ (1 - 1 / u) * (3 * M) ^ (1 - 1 / v) = (3 * M) ^ (2 - 1 / t) := by
    rw [← Real.rpow_add h3M, huvt]; ring_nf
  have e2 : M⁻¹ * ((3 * M) ^ (1 - 1 / u) * A) * ((3 * M) ^ (1 - 1 / v) * B) =
      M⁻¹ * (3 * M) ^ (2 - 1 / t) * (A * B) := by
    rw [← e1]; ring
  rw [e2, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
    Real.inv_rpow hM.le, ← Real.rpow_mul h3M.le, Real.mul_rpow (by norm_num) hM.le,
    ← Real.rpow_neg hM.le]
  have e3 : (2 - 1 / t) * t = 2 * t - 1 := by field_simp
  rw [e3]
  have e4 : M ^ (1 - t) * (M ^ (-t) * (3 ^ (2 * t - 1) * M ^ (2 * t - 1)) * (A * B) ^ t) =
      3 ^ (2 * t - 1) * (A * B) ^ t * (M ^ (1 - t) * M ^ (-t) * M ^ (2 * t - 1)) := by ring
  rw [e4, ← Real.rpow_add hM, ← Real.rpow_add hM]
  have e5 : 1 - t + -t + (2 * t - 1) = 0 := by ring
  rw [e5, Real.rpow_zero, mul_one]

/-- The block estimate: steps 3-5 of the blueprint proof of N11. -/
lemma block_bound {L : ℕ} {I T : Finset ℤ} (hI : (I.card : ℝ) = 2 * L + 1)
    (hT : (T.card : ℝ) = 3 * (2 * L + 1))
    (hIT : ∀ x ∈ I, ∀ n ∈ Finset.Icc (-(L : ℤ)) L, x - n ∈ T ∧ x + n ∈ T)
    {a b : ℤ → ℝ} (ha : ∀ y, 0 ≤ a y) (hb : ∀ y, 0 ≤ b y)
    {u v t : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v) (ht : 0 < t) (ht1 : t ≤ 1)
    (huvt : 1 / t = 1 / u + 1 / v) :
    ∑ x ∈ I, ((2 * L + 1 : ℝ)⁻¹ * ∑ n ∈ Finset.Icc (-(L : ℤ)) L, a (x - n) * b (x + n)) ^ t ≤
      3 ^ (2 * t - 1) * ((∑ y ∈ T, a y ^ u) ^ (t / u) * (∑ y ∈ T, b y ^ v) ^ (t / v)) := by
  have hM : (0 : ℝ) < 2 * L + 1 := by positivity
  have hs : ∀ x ∈ I, 0 ≤ (2 * L + 1 : ℝ)⁻¹ *
      ∑ n ∈ Finset.Icc (-(L : ℤ)) L, a (x - n) * b (x + n) := fun x _ =>
    mul_nonneg (inv_nonneg.2 hM.le)
      (Finset.sum_nonneg fun n _ => mul_nonneg (ha _) (hb _))
  have h1 := sum_rpow_le_card_rpow_mul I _ hs ht ht1
  rw [hI] at h1
  have h2 : ∑ x ∈ I, (2 * L + 1 : ℝ)⁻¹ *
      ∑ n ∈ Finset.Icc (-(L : ℤ)) L, a (x - n) * b (x + n) ≤
      (2 * L + 1 : ℝ)⁻¹ * ((∑ y ∈ T, a y) * (∑ z ∈ T, b z)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_pairs_le hIT ha hb) (inv_nonneg.2 hM.le)
  have h3 := sum_le_card_rpow_mul T a (fun y _ => ha y) hu
  have h4 := sum_le_card_rpow_mul T b (fun y _ => hb y) hv
  rw [hT] at h3 h4
  have hA : 0 ≤ (∑ y ∈ T, a y ^ u) ^ (1 / u) :=
    Real.rpow_nonneg (Finset.sum_nonneg fun y _ => Real.rpow_nonneg (ha y) u) _
  have hB : 0 ≤ (∑ y ∈ T, b y ^ v) ^ (1 / v) :=
    Real.rpow_nonneg (Finset.sum_nonneg fun y _ => Real.rpow_nonneg (hb y) v) _
  have h5 : ∑ x ∈ I, (2 * L + 1 : ℝ)⁻¹ *
      ∑ n ∈ Finset.Icc (-(L : ℤ)) L, a (x - n) * b (x + n) ≤
      (2 * L + 1 : ℝ)⁻¹ * ((3 * (2 * L + 1 : ℝ)) ^ (1 - 1 / u) * (∑ y ∈ T, a y ^ u) ^ (1 / u)) *
        ((3 * (2 * L + 1 : ℝ)) ^ (1 - 1 / v) * (∑ y ∈ T, b y ^ v) ^ (1 / v)) := by
    refine h2.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hM.le)
    exact mul_le_mul h3 h4 (Finset.sum_nonneg fun z _ => hb z)
      (mul_nonneg (Real.rpow_nonneg (by positivity) _) hA)
  have h6 := Real.rpow_le_rpow (Finset.sum_nonneg hs) h5 ht.le
  have h7 := mul_le_mul_of_nonneg_left h6 (Real.rpow_nonneg hM.le (1 - t))
  refine h1.trans (h7.trans_eq ?_)
  rw [block_alg hM hA hB ht huvt, Real.mul_rpow hA hB, ← Real.rpow_mul
    (Finset.sum_nonneg fun y _ => Real.rpow_nonneg (ha y) u), ← Real.rpow_mul
    (Finset.sum_nonneg fun y _ => Real.rpow_nonneg (hb y) v)]
  congr 3 <;> ring

end RealLemmas

/-! ### Block decomposition of `ℤ` -/

section Blocks

open scoped ENNReal

/-- The interval `I_j` of length `M`. -/
def blk (M : ℕ) (j : ℤ) : Finset ℤ := Finset.Ico (j * M) (j * M + M)

/-- The triple interval `3 I_j = I_{j-1} ∪ I_j ∪ I_{j+1}`. -/
def trip (M : ℕ) (j : ℤ) : Finset ℤ := Finset.Ico (j * M - M) (j * M + 2 * M)

lemma card_blk (M : ℕ) (j : ℤ) : (blk M j).card = M := by
  simp [blk]

lemma card_trip (M : ℕ) (j : ℤ) : (trip M j).card = 3 * M := by
  simp only [trip, Int.card_Ico]
  omega

/-- Partition of `ℤ` into the intervals `I_j`. -/
lemma tsum_eq_tsum_blk (M : ℕ) [NeZero M] (f : ℤ → ℝ≥0∞) :
    ∑' x, f x = ∑' j : ℤ, ∑ x ∈ blk M j, f x := by
  rw [← (Int.divModEquiv M).symm.tsum_eq]
  have : ∀ p : ℤ × Fin M, f ((Int.divModEquiv M).symm p) = f (p.1 * M + (p.2 : ℕ)) :=
    fun p => rfl
  simp_rw [this]
  rw [ENNReal.tsum_prod (f := fun (a : ℤ) (b : Fin M) => f (a * M + (b : ℕ)))]
  refine tsum_congr fun j => ?_
  rw [tsum_fintype]
  refine Finset.sum_bij (fun r _ => j * M + ((r : ℕ) : ℤ)) ?_ ?_ ?_ ?_
  · intro r _
    have := r.isLt
    simp only [blk, Finset.mem_Ico]
    omega
  · intro r _ s _ h
    have h' : ((r : ℕ) : ℤ) = ((s : ℕ) : ℤ) := by omega
    exact Fin.ext (by exact_mod_cast h')
  · intro x hx
    simp only [blk, Finset.mem_Ico] at hx
    refine ⟨⟨(x - j * M).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    simp only
    omega
  · intro r _
    rfl

lemma sum_trip (M : ℕ) (g : ℤ → ℝ≥0∞) (j : ℤ) :
    ∑ y ∈ trip M j, g y =
      ∑ y ∈ blk M (j - 1), g y + ∑ y ∈ blk M j, g y + ∑ y ∈ blk M (j + 1), g y := by
  have e0 : blk M (j - 1) = Finset.Ico (j * M - M) (j * M) := by
    unfold blk
    congr 1 <;> ring
  have e2 : blk M (j + 1) = Finset.Ico (j * M + M) (j * M + 2 * M) := by
    unfold blk
    congr 1 <;> ring
  have e1 : blk M j = Finset.Ico (j * M) (j * M + M) := rfl
  have hM : (0 : ℤ) ≤ M := Int.natCast_nonneg M
  rw [e0, e1, e2, trip, ← Finset.sum_union, ← Finset.sum_union,
    Finset.Ico_union_Ico_eq_Ico (by omega) (by omega),
    Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
  · exact Finset.disjoint_left.2 fun x hx hx' => by
      simp only [Finset.mem_Ico, Finset.mem_union] at hx hx'
      omega
  · exact Finset.disjoint_left.2 fun x hx hx' => by
      simp only [Finset.mem_Ico] at hx hx'
      omega

/-- Bounded overlap of the triple intervals. -/
lemma tsum_sum_trip (M : ℕ) [NeZero M] (g : ℤ → ℝ≥0∞) :
    ∑' j, ∑ y ∈ trip M j, g y = 3 * ∑' y, g y := by
  simp_rw [sum_trip]
  rw [ENNReal.tsum_add, ENNReal.tsum_add]
  have h1 : ∑' j, ∑ y ∈ blk M (j - 1), g y = ∑' j, ∑ y ∈ blk M j, g y :=
    (Equiv.subRight (1 : ℤ)).tsum_eq (fun j => ∑ y ∈ blk M j, g y)
  have h2 : ∑' j, ∑ y ∈ blk M (j + 1), g y = ∑' j, ∑ y ∈ blk M j, g y :=
    (Equiv.addRight (1 : ℤ)).tsum_eq (fun j => ∑ y ∈ blk M j, g y)
  rw [h1, h2, ← tsum_eq_tsum_blk]
  ring

/-- Hölder's inequality for sequences indexed by `ℤ`, with `ℝ≥0∞` values (Q3). -/
lemma tsum_mul_rpow_le {p q : ℝ} (hpq : p.HolderConjugate q) (α β : ℤ → ℝ≥0∞) :
    ∑' j, α j ^ (1 / p) * β j ^ (1 / q) ≤
      (∑' j, α j) ^ (1 / p) * (∑' j, β j) ^ (1 / q) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq MeasureTheory.Measure.count hpq
    (f := fun j => α j ^ (1 / p)) (g := fun j => β j ^ (1 / q))
    (Measurable.of_discrete.aemeasurable) (Measurable.of_discrete.aemeasurable)
  simp only [MeasureTheory.lintegral_count, Pi.mul_apply] at h
  have e1 : ∀ j, (α j ^ (1 / p)) ^ p = α j := fun j => by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hpq.ne_zero, ENNReal.rpow_one]
  have e2 : ∀ j, (β j ^ (1 / q)) ^ q = β j := fun j => by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hpq.symm.ne_zero, ENNReal.rpow_one]
  simpa only [e1, e2] using h

end Blocks

/-! ### The operator `B_L` -/

/-- The fixed-scale bilinear average
`B_L(F,G)(x) = (2L+1)⁻¹ ∑_{|n| ≤ L} ‖F(x-n)‖ ‖G(x+n)‖`. -/
noncomputable def B (L : ℕ) (F G : ℤ → ℂ) (x : ℤ) : ℝ :=
  (1 / (2 * (L : ℝ) + 1)) * ∑ n ∈ Finset.Icc (-(L : ℤ)) L, ‖F (x - n)‖ * ‖G (x + n)‖

lemma B_nonneg (L : ℕ) (F G : ℤ → ℂ) (x : ℤ) : 0 ≤ B L F G x :=
  mul_nonneg (by positivity)
    (Finset.sum_nonneg fun n _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))

section Quasi

open scoped ENNReal

lemma ofReal_sum_norm_rpow (T : Finset ℤ) (F : ℤ → ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ENNReal.ofReal (∑ y ∈ T, ‖F y‖ ^ u) = ∑ y ∈ T, ENNReal.ofReal ‖F y‖ ^ u := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun y _ => Real.rpow_nonneg (norm_nonneg _) _)]
  exact Finset.sum_congr rfl fun y _ => (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hu).symm

/-- The block estimate in `ℝ≥0∞` form. -/
lemma block_ennreal (L : ℕ) (F G : ℤ → ℂ) {u v t : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v) (ht : 0 < t)
    (ht1 : t ≤ 1) (huvt : 1 / t = 1 / u + 1 / v) (j : ℤ) :
    ∑ x ∈ blk (2 * L + 1) j, ENNReal.ofReal (B L F G x) ^ t ≤
      ENNReal.ofReal (3 ^ (2 * t - 1)) *
        ((∑ y ∈ trip (2 * L + 1) j, ENNReal.ofReal ‖F y‖ ^ u) ^ (t / u) *
         (∑ y ∈ trip (2 * L + 1) j, ENNReal.ofReal ‖G y‖ ^ v) ^ (t / v)) := by
  have hIT : ∀ x ∈ blk (2 * L + 1) j, ∀ n ∈ Finset.Icc (-(L : ℤ)) L,
      x - n ∈ trip (2 * L + 1) j ∧ x + n ∈ trip (2 * L + 1) j := by
    intro x hx n hn
    simp only [blk, trip, Finset.mem_Ico, Finset.mem_Icc] at hx hn ⊢
    push_cast at hx ⊢
    omega
  have hb := block_bound (L := L) (I := blk (2 * L + 1) j) (T := trip (2 * L + 1) j)
    (by rw [card_blk]; push_cast; ring) (by rw [card_trip]; push_cast; ring) hIT
    (a := fun y => ‖F y‖) (b := fun y => ‖G y‖) (fun y => norm_nonneg _)
    (fun y => norm_nonneg _) hu hv ht ht1 huvt
  have hb' : ∑ x ∈ blk (2 * L + 1) j, B L F G x ^ t ≤
      3 ^ (2 * t - 1) * ((∑ y ∈ trip (2 * L + 1) j, ‖F y‖ ^ u) ^ (t / u) *
        (∑ y ∈ trip (2 * L + 1) j, ‖G y‖ ^ v) ^ (t / v)) := by
    simpa only [B, one_div] using hb
  have hX : 0 ≤ ∑ y ∈ trip (2 * L + 1) j, ‖F y‖ ^ u :=
    Finset.sum_nonneg fun y _ => Real.rpow_nonneg (norm_nonneg _) _
  have hY : 0 ≤ ∑ y ∈ trip (2 * L + 1) j, ‖G y‖ ^ v :=
    Finset.sum_nonneg fun y _ => Real.rpow_nonneg (norm_nonneg _) _
  calc ∑ x ∈ blk (2 * L + 1) j, ENNReal.ofReal (B L F G x) ^ t
      = ENNReal.ofReal (∑ x ∈ blk (2 * L + 1) j, B L F G x ^ t) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => Real.rpow_nonneg (B_nonneg L F G x) t)]
        exact Finset.sum_congr rfl fun x _ =>
          ENNReal.ofReal_rpow_of_nonneg (B_nonneg L F G x) ht.le
    _ ≤ ENNReal.ofReal (3 ^ (2 * t - 1) * ((∑ y ∈ trip (2 * L + 1) j, ‖F y‖ ^ u) ^ (t / u) *
        (∑ y ∈ trip (2 * L + 1) j, ‖G y‖ ^ v) ^ (t / v))) := ENNReal.ofReal_le_ofReal hb'
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Real.rpow_nonneg hX _),
          ← ENNReal.ofReal_rpow_of_nonneg hX (div_nonneg ht.le (by linarith)),
          ← ENNReal.ofReal_rpow_of_nonneg hY (div_nonneg ht.le (by linarith)),
          ofReal_sum_norm_rpow _ _ (by linarith), ofReal_sum_norm_rpow _ _ (by linarith)]

/-- Steps 6-7 of the blueprint proof of N11: summation over the blocks. -/
lemma tsum_B_rpow_le (L : ℕ) (F G : ℤ → ℂ) {u v t : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v) (ht : 0 < t)
    (ht1 : t ≤ 1) (huvt : 1 / t = 1 / u + 1 / v) :
    ∑' x, ENNReal.ofReal (B L F G x) ^ t ≤
      ENNReal.ofReal (3 ^ (2 * t)) *
        ((∑' y, ENNReal.ofReal ‖F y‖ ^ u) ^ (t / u) *
          (∑' y, ENNReal.ofReal ‖G y‖ ^ v) ^ (t / v)) := by
  have : NeZero (2 * L + 1) := ⟨Nat.succ_ne_zero _⟩
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hs : t / u + t / v = 1 := by
    have e : t / u + t / v = t * (1 / u + 1 / v) := by ring
    rw [e, ← huvt]
    field_simp
  have hta : 0 < t / u := div_pos ht hu0
  have htb : 0 < t / v := div_pos ht hv0
  have hpq : ((t / u)⁻¹).HolderConjugate ((t / v)⁻¹) :=
    Real.HolderConjugate.inv_inv hta htb hs
  have hK : ENNReal.ofReal (3 ^ (2 * t)) = ENNReal.ofReal (3 ^ (2 * t - 1)) * 3 := by
    have : (3 : ℝ) ^ (2 * t) = 3 ^ (2 * t - 1) * 3 := by
      rw [Real.rpow_sub_one (by norm_num)]
      field_simp
    rw [this, ENNReal.ofReal_mul (by positivity)]
    simp
  have h3 : (3 : ℝ≥0∞) ^ (t / u) * 3 ^ (t / v) = 3 := by
    rw [← ENNReal.rpow_add _ _ (by norm_num) (by simp), hs, ENNReal.rpow_one]
  set α : ℤ → ℝ≥0∞ := fun j => ∑ y ∈ trip (2 * L + 1) j, ENNReal.ofReal ‖F y‖ ^ u with hα
  set β : ℤ → ℝ≥0∞ := fun j => ∑ y ∈ trip (2 * L + 1) j, ENNReal.ofReal ‖G y‖ ^ v with hβ
  rw [tsum_eq_tsum_blk (2 * L + 1)]
  calc ∑' j, ∑ x ∈ blk (2 * L + 1) j, ENNReal.ofReal (B L F G x) ^ t
      ≤ ∑' j, ENNReal.ofReal (3 ^ (2 * t - 1)) * (α j ^ (t / u) * β j ^ (t / v)) :=
        ENNReal.tsum_le_tsum fun j => block_ennreal L F G hu hv ht ht1 huvt j
    _ = ENNReal.ofReal (3 ^ (2 * t - 1)) *
          ∑' j, α j ^ (1 / (t / u)⁻¹) * β j ^ (1 / (t / v)⁻¹) := by
        rw [ENNReal.tsum_mul_left]
        simp only [one_div, inv_inv]
    _ ≤ ENNReal.ofReal (3 ^ (2 * t - 1)) *
          ((∑' j, α j) ^ (1 / (t / u)⁻¹) * (∑' j, β j) ^ (1 / (t / v)⁻¹)) := by
        gcongr
        exact tsum_mul_rpow_le hpq α β
    _ = ENNReal.ofReal (3 ^ (2 * t - 1)) *
          ((3 * ∑' y, ENNReal.ofReal ‖F y‖ ^ u) ^ (t / u) *
            (3 * ∑' y, ENNReal.ofReal ‖G y‖ ^ v) ^ (t / v)) := by
        simp only [one_div, inv_inv]
        rw [hα, hβ]
        simp only
        rw [tsum_sum_trip, tsum_sum_trip]
    _ = ENNReal.ofReal (3 ^ (2 * t)) *
        ((∑' y, ENNReal.ofReal ‖F y‖ ^ u) ^ (t / u) *
          (∑' y, ENNReal.ofReal ‖G y‖ ^ v) ^ (t / v)) := by
        rw [hK, ENNReal.mul_rpow_of_nonneg _ _ hta.le, ENNReal.mul_rpow_of_nonneg _ _ htb.le]
        calc _ = ENNReal.ofReal (3 ^ (2 * t - 1)) * (3 ^ (t / u) * 3 ^ (t / v)) *
              ((∑' y, ENNReal.ofReal ‖F y‖ ^ u) ^ (t / u) *
                (∑' y, ENNReal.ofReal ‖G y‖ ^ v) ^ (t / v)) := by ring
          _ = _ := by rw [h3]

/-- For counting measure on `ℤ` and `0 < p < ∞`, `eLpNorm` is the `ℓ^p` sum, in `ℝ≥0∞`. -/
lemma eLpNorm_count_eq {E : Type*} [NormedAddCommGroup E] (f : ℤ → E) {p : ℝ} (hp : 0 < p) :
    MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count =
      (∑' x, ENNReal.ofReal ‖f x‖ ^ p) ^ (1 / p) := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp).ne'
    ENNReal.ofReal_ne_top MeasureTheory.AEStronglyMeasurable.of_discrete,
    ENNReal.toReal_ofReal hp.le, MeasureTheory.lintegral_count]
  simp_rw [ofReal_norm]

/-- The case `0 < t ≤ 1` of N11, with real exponents. -/
theorem eLpNorm_B_le_of_le_one (L : ℕ) (F G : ℤ → ℂ) {u v t : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v)
    (ht : 0 < t) (ht1 : t ≤ 1) (huvt : 1 / t = 1 / u + 1 / v) :
    MeasureTheory.eLpNorm (B L F G) (ENNReal.ofReal t) MeasureTheory.Measure.count ≤
      9 * MeasureTheory.eLpNorm F (ENNReal.ofReal u) MeasureTheory.Measure.count *
        MeasureTheory.eLpNorm G (ENNReal.ofReal v) MeasureTheory.Measure.count := by
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  rw [eLpNorm_count_eq _ ht, eLpNorm_count_eq F hu0, eLpNorm_count_eq G hv0]
  have hn : ∀ x, ENNReal.ofReal ‖B L F G x‖ = ENNReal.ofReal (B L F G x) := fun x => by
    rw [Real.norm_of_nonneg (B_nonneg L F G x)]
  simp_rw [hn]
  have h9 : ENNReal.ofReal (3 ^ (2 * t)) ^ (1 / t) = 9 := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
      ← Real.rpow_mul (by norm_num)]
    have : 2 * t * (1 / t) = 2 := by field_simp
    rw [this, Real.rpow_two]
    norm_num
  calc (∑' x, ENNReal.ofReal (B L F G x) ^ t) ^ (1 / t)
      ≤ (ENNReal.ofReal (3 ^ (2 * t)) *
          ((∑' y, ENNReal.ofReal ‖F y‖ ^ u) ^ (t / u) *
            (∑' y, ENNReal.ofReal ‖G y‖ ^ v) ^ (t / v))) ^ (1 / t) :=
        ENNReal.rpow_le_rpow (tsum_B_rpow_le L F G hu hv ht ht1 huvt) (by positivity)
    _ = 9 * (∑' y, ENNReal.ofReal ‖F y‖ ^ u) ^ (1 / u) *
          (∑' y, ENNReal.ofReal ‖G y‖ ^ v) ^ (1 / v) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), h9, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        have e1 : t / u * (1 / t) = 1 / u := by field_simp
        have e2 : t / v * (1 / t) = 1 / v := by field_simp
        rw [e1, e2, mul_assoc]

/-- The case `t ≥ 1` of N11 (Minkowski in `x` for the average over `n`, then Hölder and shift
invariance), with arbitrary `ℝ≥0∞` exponents; constant `1`. -/
theorem eLpNorm_B_le_of_one_le (L : ℕ) (F G : ℤ → ℂ) {p q r : ℝ≥0∞}
    [ENNReal.HolderTriple p q r] (hr : 1 ≤ r) :
    MeasureTheory.eLpNorm (B L F G) r MeasureTheory.Measure.count ≤
      MeasureTheory.eLpNorm F p MeasureTheory.Measure.count *
        MeasureTheory.eLpNorm G q MeasureTheory.Measure.count := by
  have hB : B L F G = (1 / (2 * (L : ℝ) + 1)) •
      ∑ n ∈ Finset.Icc (-(L : ℤ)) L, (fun x : ℤ => ‖F (x - n)‖ * ‖G (x + n)‖) := by
    ext x
    simp [B, Finset.sum_apply]
  have hterm : ∀ n : ℤ, MeasureTheory.eLpNorm (fun x : ℤ => ‖F (x - n)‖ * ‖G (x + n)‖) r
      MeasureTheory.Measure.count ≤
        MeasureTheory.eLpNorm F p MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm G q MeasureTheory.Measure.count := fun n => by
    have h := MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm (p := p) (q := q) (r := r)
      (μ := MeasureTheory.Measure.count) (f := fun x : ℤ => ‖F (x - n)‖)
      (g := fun x : ℤ => ‖G (x + n)‖) (fun a b : ℝ => a * b) 1 continuous_mul
      MeasureTheory.AEStronglyMeasurable.of_discrete MeasureTheory.AEStronglyMeasurable.of_discrete
      (Filter.Eventually.of_forall fun x => by simp [nnnorm_mul])
    have e1 : MeasureTheory.eLpNorm (fun x : ℤ => ‖F (x - n)‖) p MeasureTheory.Measure.count =
        MeasureTheory.eLpNorm F p MeasureTheory.Measure.count := by
      rw [MeasureTheory.eLpNorm_norm (fun x : ℤ => F (x - n)) MeasureTheory.AEStronglyMeasurable.of_discrete]
      exact MeasureTheory.eLpNorm_comp_measurePreserving (g := F)
        MeasureTheory.AEStronglyMeasurable.of_discrete
        (MeasureTheory.measurePreserving_sub_right MeasureTheory.Measure.count n)
    have e2 : MeasureTheory.eLpNorm (fun x : ℤ => ‖G (x + n)‖) q MeasureTheory.Measure.count =
        MeasureTheory.eLpNorm G q MeasureTheory.Measure.count := by
      rw [MeasureTheory.eLpNorm_norm (fun x : ℤ => G (x + n)) MeasureTheory.AEStronglyMeasurable.of_discrete]
      exact MeasureTheory.eLpNorm_comp_measurePreserving (g := G)
        MeasureTheory.AEStronglyMeasurable.of_discrete
        (MeasureTheory.measurePreserving_add_right MeasureTheory.Measure.count n)
    rw [e1, e2] at h
    simpa using h
  have hcard : (Finset.Icc (-(L : ℤ)) L).card = 2 * L + 1 := by
    rw [Int.card_Icc]
    omega
  have hc : ‖(1 / (2 * (L : ℝ) + 1))‖ₑ = ((2 * L + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [Real.enorm_eq_ofReal (by positivity), one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
    congr 1
    rw [show (2 * (L : ℝ) + 1) = ((2 * L + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  have h0 : ((2 * L + 1 : ℕ) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [hB, MeasureTheory.eLpNorm_const_smul]
  calc ‖(1 / (2 * (L : ℝ) + 1))‖ₑ *
        MeasureTheory.eLpNorm (∑ n ∈ Finset.Icc (-(L : ℤ)) L,
          fun x : ℤ => ‖F (x - n)‖ * ‖G (x + n)‖) r MeasureTheory.Measure.count
      ≤ ‖(1 / (2 * (L : ℝ) + 1))‖ₑ * ∑ n ∈ Finset.Icc (-(L : ℤ)) L,
          MeasureTheory.eLpNorm (fun x : ℤ => ‖F (x - n)‖ * ‖G (x + n)‖) r
            MeasureTheory.Measure.count := by
        gcongr
        exact MeasureTheory.eLpNorm_sum_le hr
    _ ≤ ‖(1 / (2 * (L : ℝ) + 1))‖ₑ * ∑ n ∈ Finset.Icc (-(L : ℤ)) L,
          (MeasureTheory.eLpNorm F p MeasureTheory.Measure.count *
            MeasureTheory.eLpNorm G q MeasureTheory.Measure.count) := by
        gcongr with n _
        exact hterm n
    _ = _ := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul, ← mul_assoc, hc,
          ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top _), one_mul]

/-- **N11, `e:fixed-average`**, real exponents: for `u, v ≥ 1` and `1/t = 1/u + 1/v` (so `t ≥ 1/2`),
`‖B_L(F,G)‖_{ℓ^t} ≤ 9 ‖F‖_{ℓ^u} ‖G‖_{ℓ^v}`, uniformly in `L`. -/
theorem eLpNorm_B_le_real (L : ℕ) (F G : ℤ → ℂ) {u v t : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v)
    (huvt : 1 / t = 1 / u + 1 / v) :
    MeasureTheory.eLpNorm (B L F G) (ENNReal.ofReal t) MeasureTheory.Measure.count ≤
      9 * MeasureTheory.eLpNorm F (ENNReal.ofReal u) MeasureTheory.Measure.count *
        MeasureTheory.eLpNorm G (ENNReal.ofReal v) MeasureTheory.Measure.count := by
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have ht : 0 < t := by
    have : 0 < 1 / t := by rw [huvt]; positivity
    exact one_div_pos.1 this
  rcases le_total t 1 with h | h
  · exact eLpNorm_B_le_of_le_one L F G hu hv ht h huvt
  · have hT : ENNReal.HolderTriple (ENNReal.ofReal u) (ENNReal.ofReal v) (ENNReal.ofReal t) := by
      refine ⟨?_⟩
      rw [← ENNReal.ofReal_inv_of_pos hu0, ← ENNReal.ofReal_inv_of_pos hv0,
        ← ENNReal.ofReal_inv_of_pos ht, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      simpa only [one_div] using huvt.symm
    have hr : 1 ≤ ENNReal.ofReal t := by
      simpa using ENNReal.ofReal_le_ofReal h
    have h1 := eLpNorm_B_le_of_one_le L F G (p := ENNReal.ofReal u) (q := ENNReal.ofReal v)
      (r := ENNReal.ofReal t) hr
    refine h1.trans ?_
    rw [mul_assoc]
    exact le_mul_of_one_le_left zero_le (by norm_num)

end Quasi

end PrimeBHT.FixedAverage
