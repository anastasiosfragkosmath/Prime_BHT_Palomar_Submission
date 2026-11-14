module

public import PrimeBHT.TimeFrequency.X2.CZ.Dyadic1D
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# V08 phase 2: the Calderón-Zygmund covering lemma on `ℝ` (Gagliardo / Calderón)

For a nonnegative integrable `G : ℝ → ℝ` and a height `λ > 0` (`exists_cz_intervals`): there is a countable
family of pairwise disjoint half-open dyadic intervals `Q_i = [a_i, b_i)` with

* `λ |Q_i| < ∫_{Q_i} G ≤ 2 λ |Q_i|` (the average over `Q_i` lies in `(λ, 2λ]`),
* `G ≤ λ` almost everywhere outside `⋃ Q_i` (Lebesgue differentiation along dyadic intervals),
* `∑_i |Q_i| ≤ ‖G‖₁ / λ` (summable).

Used for `G = |f|_X = x ↦ yNorm s (F x)` (and, with the same proof, any norm of a Bochner-valued `f`), so
the interface is scalar: the vector-valued parts (good part, bad atoms with mean zero) are built from the
intervals in `WeakType.lean`.  The `X`-valued function itself is not needed here.

Proof: `Q` ranges over the *maximal* dyadic intervals whose average exceeds `λ`
(maximal exist since `∫_Q G ≤ ‖G‖₁` forces `|Q| < ‖G‖₁ / λ`); disjointness is the nesting property of dyadic
intervals; the upper bound `2λ` is the unselected parent; the `L¹` bound is disjointness plus `G ≥ 0`;
the pointwise bound outside is Lebesgue's differentiation theorem
(`IsUnifLocDoublingMeasure.ae_tendsto_average`) along the dyadic intervals containing `x`
(which are closed balls up to a null set).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

section Select

variable {G : ℝ → ℝ} {lam : ℝ}

/-- `Sel G lam k n`: the average of `G` over `dyI k n` exceeds `lam`. -/
def Sel (G : ℝ → ℝ) (lam : ℝ) (k n : ℤ) : Prop := lam * (2 : ℝ) ^ k < ∫ x in dyI k n, G x

/-- `dyI k n` is a *maximal* selected dyadic interval: selected, and no coarser dyadic interval
containing it is selected. -/
def IsMaxI (G : ℝ → ℝ) (lam : ℝ) (k n : ℤ) : Prop :=
  Sel G lam k n ∧ ∀ k' : ℤ, k < k' → ∀ x ∈ dyI k n, ¬ Sel G lam k' (dyIdx k' x)

theorem integral_dyI_le (hG0 : ∀ x, 0 ≤ G x) (hG : Integrable G) (k n : ℤ) :
    ∫ x in dyI k n, G x ≤ ∫ x, G x :=
  setIntegral_le_integral hG (Eventually.of_forall hG0)

theorem exists_level_bound (hG0 : ∀ x, 0 ≤ G x) (hG : Integrable G) (hlam : 0 < lam) :
    ∃ K : ℤ, ∀ k n : ℤ, Sel G lam k n → k < K := by
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt ((∫ x, G x) / lam) (by norm_num : (1 : ℝ) < 2)
  refine ⟨K, fun k n h => ?_⟩
  have h1 : lam * (2 : ℝ) ^ k < ∫ x, G x := h.trans_le (integral_dyI_le hG0 hG k n)
  have h2 : (2 : ℝ) ^ k < (2 : ℝ) ^ (K : ℤ) := by
    rw [zpow_natCast]
    have : (2 : ℝ) ^ k < (∫ x, G x) / lam := by
      rw [lt_div_iff₀ hlam]; linarith
    linarith
  exact (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h2

/-- Every point of a selected dyadic interval lies in a maximal selected one. -/
theorem exists_isMaxI (hG0 : ∀ x, 0 ≤ G x) (hG : Integrable G) (hlam : 0 < lam) {x : ℝ}
    (hx : ∃ k : ℤ, Sel G lam k (dyIdx k x)) : ∃ k n : ℤ, IsMaxI G lam k n ∧ x ∈ dyI k n := by
  obtain ⟨K, hK⟩ := exists_level_bound hG0 hG hlam
  obtain ⟨k₀, hk₀, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun k => Sel G lam k (dyIdx k x)) ⟨K, fun k hk => (hK k _ hk).le⟩ hx
  refine ⟨k₀, dyIdx k₀ x, ⟨hk₀, ?_⟩, mem_dyI_dyIdx k₀ x⟩
  intro k' hk' y hy hsel
  have hsub := dyI_subset_of_inter hk'.le ⟨x, mem_dyI_dyIdx k₀ x, mem_dyI_dyIdx k' x⟩
  have hy' : dyIdx k' y = dyIdx k' x := dyIdx_eq_of_mem (hsub hy)
  rw [hy'] at hsel
  exact absurd (hmax k' hsel) (not_le.2 hk')

theorem isMaxI_disjoint {k n k' n' : ℤ} (h : IsMaxI G lam k n) (h' : IsMaxI G lam k' n')
    (hne : (k, n) ≠ (k', n')) : Disjoint (dyI k n) (dyI k' n') := by
  by_contra hd
  rw [Set.not_disjoint_iff] at hd
  obtain ⟨z, hz, hz'⟩ := hd
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · exact h.2 k' hlt z hz (by rw [dyIdx_eq_of_mem hz']; exact h'.1)
  · subst heq
    have := dyI_eq_of_inter_same ⟨z, hz, hz'⟩
    exact hne (by rw [this])
  · exact h'.2 k hgt z hz' (by rw [dyIdx_eq_of_mem hz]; exact h.1)

/-- The average over a maximal interval is at most `2 λ` (the parent is not selected). -/
theorem integral_le_of_isMaxI (hG0 : ∀ x, 0 ≤ G x) (hG : Integrable G) {k n : ℤ}
    (h : IsMaxI G lam k n) : ∫ x in dyI k n, G x ≤ 2 * lam * (2 : ℝ) ^ k := by
  have hp := two_zpow_pos k
  have hx0 : (n : ℝ) * (2 : ℝ) ^ k ∈ dyI k n := by
    rw [mem_dyI]; constructor
    · exact le_rfl
    · nlinarith
  have hns := h.2 (k + 1) (by omega) _ hx0
  unfold Sel at hns
  rw [not_lt] at hns
  have hsub := dyI_subset_of_inter (by omega : k ≤ k + 1)
    ⟨_, hx0, mem_dyI_dyIdx (k + 1) ((n : ℝ) * (2 : ℝ) ^ k)⟩
  calc ∫ x in dyI k n, G x
      ≤ ∫ x in dyI (k + 1) (dyIdx (k + 1) ((n : ℝ) * (2 : ℝ) ^ k)), G x :=
        setIntegral_mono_set hG.integrableOn (Eventually.of_forall hG0)
          (Eventually.of_forall fun x hx => hsub hx)
    _ ≤ lam * (2 : ℝ) ^ (k + 1) := hns
    _ = 2 * lam * (2 : ℝ) ^ k := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]; ring

/-- Finite sums of the lengths of maximal intervals are at most `‖G‖₁ / λ`. -/
theorem sum_length_le (hG0 : ∀ x, 0 ≤ G x) (hG : Integrable G) (hlam : 0 < lam)
    (s : Finset (ℤ × ℤ)) (hs : ∀ p ∈ s, IsMaxI G lam p.1 p.2) :
    ∑ p ∈ s, (2 : ℝ) ^ p.1 ≤ (∫ x, G x) / lam := by
  rw [le_div_iff₀ hlam, Finset.sum_mul]
  have hdisj : Set.Pairwise (↑s : Set (ℤ × ℤ)) (Function.onFun Disjoint fun p => dyI p.1 p.2) := by
    intro p hp q hq hpq
    exact isMaxI_disjoint (hs p hp) (hs q hq) hpq
  calc ∑ p ∈ s, (2 : ℝ) ^ p.1 * lam = ∑ p ∈ s, lam * (2 : ℝ) ^ p.1 :=
        Finset.sum_congr rfl fun p _ => mul_comm _ _
    _ ≤ ∑ p ∈ s, ∫ x in dyI p.1 p.2, G x :=
        Finset.sum_le_sum fun p hp => (hs p hp).1.le
    _ = ∫ x in ⋃ p ∈ s, dyI p.1 p.2, G x :=
        (integral_biUnion_finset s (fun p _ => measurableSet_dyI _ _) hdisj
          (fun p _ => hG.integrableOn)).symm
    _ ≤ ∫ x, G x := setIntegral_le_integral hG (Eventually.of_forall hG0)

/-- **Lebesgue differentiation along dyadic intervals**: for a.e. `x`, if no dyadic interval containing
`x` has average `> λ`, then `G x ≤ λ`. -/
theorem ae_le_of_not_sel (hG : Integrable G) (lam : ℝ) :
    ∀ᵐ x ∂(volume : Measure ℝ), (∀ k : ℤ, ¬ Sel G lam k (dyIdx k x)) → G x ≤ lam := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average (μ := (volume : Measure ℝ))
    hG.locallyIntegrable 1] with x hx hns
  let k : ℕ → ℤ := fun j => -(j : ℤ)
  let n : ℕ → ℤ := fun j => dyIdx (k j) x
  have hδ : Tendsto (fun j : ℕ => (2 : ℝ) ^ (k j) / 2) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun j => ?_⟩
    · have h0 : Tendsto (fun j : ℕ => ((1 : ℝ) / 2) ^ j) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have := h0.div_const 2
      rw [zero_div] at this
      refine this.congr fun j => ?_
      simp only [k]
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    · exact div_pos (two_zpow_pos _) (by norm_num)
  have hmem : ∀ j : ℕ, x ∈ Metric.closedBall (((n j : ℝ) + 1 / 2) * (2 : ℝ) ^ (k j))
      (1 * ((2 : ℝ) ^ (k j) / 2)) := by
    intro j
    have hxm := mem_dyI.1 (mem_dyI_dyIdx (k j) x)
    have hp := two_zpow_pos (k j)
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> nlinarith [hxm.1, hxm.2]
  have hlim := hx (fun j => ((n j : ℝ) + 1 / 2) * (2 : ℝ) ^ (k j)) (fun j => (2 : ℝ) ^ (k j) / 2)
    hδ (Eventually.of_forall hmem)
  refine le_of_tendsto' hlim fun j => ?_
  have hp := two_zpow_pos (k j)
  have hball : Metric.closedBall (((n j : ℝ) + 1 / 2) * (2 : ℝ) ^ (k j)) ((2 : ℝ) ^ (k j) / 2) =
      Icc ((n j : ℝ) * (2 : ℝ) ^ (k j)) (((n j : ℝ) + 1) * (2 : ℝ) ^ (k j)) := by
    rw [Real.closedBall_eq_Icc]
    congr 1 <;> ring
  rw [hball, setAverage_eq]
  have hae : Ico ((n j : ℝ) * (2 : ℝ) ^ (k j)) (((n j : ℝ) + 1) * (2 : ℝ) ^ (k j)) =ᵐ[volume]
      Icc ((n j : ℝ) * (2 : ℝ) ^ (k j)) (((n j : ℝ) + 1) * (2 : ℝ) ^ (k j)) := Ico_ae_eq_Icc
  rw [← setIntegral_congr_set hae, Measure.real, Real.volume_Icc]
  have hnk := hns (k j)
  unfold Sel at hnk
  rw [not_lt] at hnk
  have hlen : ENNReal.ofReal (((n j : ℝ) + 1) * (2 : ℝ) ^ (k j) - (n j : ℝ) * (2 : ℝ) ^ (k j)) =
      ENNReal.ofReal ((2 : ℝ) ^ (k j)) := by congr 1; ring
  rw [hlen, ENNReal.toReal_ofReal hp.le, smul_eq_mul, inv_mul_le_iff₀ hp]
  calc ∫ y in Ico ((n j : ℝ) * (2 : ℝ) ^ (k j)) (((n j : ℝ) + 1) * (2 : ℝ) ^ (k j)), G y
      = ∫ y in dyI (k j) (dyIdx (k j) x), G y := rfl
    _ ≤ lam * (2 : ℝ) ^ (k j) := hnk
    _ = (2 : ℝ) ^ (k j) * lam := mul_comm _ _

/-- **The Calderón-Zygmund covering lemma on `ℝ`.**  For `G ≥ 0` integrable and `λ > 0` there are countably
many pairwise disjoint half-open dyadic intervals `Q_i = [a_i, b_i)` such that
`λ |Q_i| < ∫_{Q_i} G ≤ 2 λ |Q_i|`, `G ≤ λ` a.e. outside `⋃ Q_i`, and `∑ |Q_i| ≤ ‖G‖₁ / λ`. -/
theorem exists_cz_intervals (hG0 : ∀ x, 0 ≤ G x) (hG : Integrable G) (hlam : 0 < lam) :
    ∃ (ι : Type) (_ : Countable ι) (a b : ι → ℝ),
      (∀ i, a i < b i) ∧
      (Pairwise fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j))) ∧
      (∀ i, lam * (b i - a i) < ∫ x in Ico (a i) (b i), G x) ∧
      (∀ i, ∫ x in Ico (a i) (b i), G x ≤ 2 * lam * (b i - a i)) ∧
      (∀ᵐ x ∂(volume : Measure ℝ), x ∉ ⋃ i, Ico (a i) (b i) → G x ≤ lam) ∧
      Summable (fun i => b i - a i) ∧ ∑' i, (b i - a i) ≤ (∫ x, G x) / lam := by
  let ι : Type := {p : ℤ × ℤ // IsMaxI G lam p.1 p.2}
  have hlen : ∀ i : ι, (((i.1.2 : ℤ) : ℝ) + 1) * (2 : ℝ) ^ i.1.1 - ((i.1.2 : ℤ) : ℝ) * (2 : ℝ) ^ i.1.1
      = (2 : ℝ) ^ i.1.1 := fun i => by ring
  refine ⟨ι, inferInstance, fun i => ((i.1.2 : ℤ) : ℝ) * (2 : ℝ) ^ i.1.1,
    fun i => (((i.1.2 : ℤ) : ℝ) + 1) * (2 : ℝ) ^ i.1.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have := two_zpow_pos i.1.1
    nlinarith
  · intro i j hij
    exact isMaxI_disjoint i.2 j.2 (fun h => hij (Subtype.ext h))
  · intro i
    rw [hlen]
    exact i.2.1
  · intro i
    rw [hlen]
    exact integral_le_of_isMaxI hG0 hG i.2
  · filter_upwards [ae_le_of_not_sel hG lam] with x hx hxn
    apply hx
    intro k hk
    obtain ⟨k', n', hmax, hxm⟩ := exists_isMaxI hG0 hG hlam ⟨k, hk⟩
    exact hxn (Set.mem_iUnion.2 ⟨⟨(k', n'), hmax⟩, hxm⟩)
  · have hsum : ∀ s : Finset ι, ∑ i ∈ s, (((((i.1.2 : ℤ) : ℝ) + 1) * (2 : ℝ) ^ i.1.1 -
        ((i.1.2 : ℤ) : ℝ) * (2 : ℝ) ^ i.1.1)) ≤ (∫ x, G x) / lam := by
      intro s
      have h1 := sum_length_le hG0 hG hlam (s.image Subtype.val) (by
        intro p hp
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hp
        exact i.2)
      rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)] at h1
      simpa only [hlen] using h1
    have hnn : ∀ i : ι, 0 ≤ (((i.1.2 : ℤ) : ℝ) + 1) * (2 : ℝ) ^ i.1.1 -
        ((i.1.2 : ℤ) : ℝ) * (2 : ℝ) ^ i.1.1 := fun i => by rw [hlen]; exact (two_zpow_pos _).le
    exact ⟨summable_of_sum_le hnn hsum, Real.tsum_le_of_sum_le hnn hsum⟩

end Select

end PrimeBHT.TimeFrequency.X2.CZ
