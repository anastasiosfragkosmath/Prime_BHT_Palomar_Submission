module

public import PrimeBHT.TimeFrequency.X2.Ortho.Weights
public import PrimeBHT.TimeFrequency.X2.Classes

/-!
# X2, node V10: the dyadic tail sum

For a finite set of dyadic intervals `I_p = dyadicInt p.1 p.2 ⊆ I₀ = dyadicInt s₀ v₀` (distinct pairs),
`∑_p ∫_{ℝ ∖ I₀} wt 3 (c_p) |I_p| ≤ 4 Z |I₀|`, `Z = ∑_{j ≥ 0} (1 + j)^{-2}`.  This is the estimate
`∑_{I ⊆ I_T} ‖1_{ℝ∖I_T} u_I‖₁ ≲ |I_T|` of HLC L691-694 (DPLMV l:ortho2).

Tile bound: the `j`-th interval of length `ℓ` from the left in `I₀` (`I₀` has `N` of them), `i = min(j, N-1-j)`:
`∫_{ℝ∖I₀} wt 3 c ℓ ≤ ℓ (1 + i)^{-2}`, by the exact tail integral `integral_indicator_one_add_abs_sub_div_rpow`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- `∑_{j ∈ ℕ} (1 + j)^{-2}`. -/
def zetaTwo : ℝ := ∑' j : ℕ, (1 + (j : ℝ)) ^ (-2 : ℝ)

theorem summable_zetaTwo : Summable fun j : ℕ => (1 + (j : ℝ)) ^ (-2 : ℝ) := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by norm_num : (-2 : ℝ) < -1))
  refine h.congr fun j => ?_
  push_cast
  rw [add_comm]

theorem zetaTwo_nonneg : 0 ≤ zetaTwo := tsum_nonneg fun j => by positivity

/-- The tail of one tile. -/
theorem tail_tile {ℓ A : ℝ} (hℓ : 0 < ℓ) (N j i : ℕ) (hij : i ≤ j) (hiN : i + j + 1 ≤ N) :
    ∫ x in (Set.Ico A (A + ℓ * N))ᶜ, wt 3 (A + ℓ * (j + 1 / 2)) ℓ x ≤ ℓ * (1 + (i : ℝ)) ^ (-2 : ℝ) := by
  set c := A + ℓ * (j + 1 / 2) with hc
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hr : 0 ≤ ℓ * i := by positivity
  have hsub : ∀ x, x ∈ (Set.Ico A (A + ℓ * N))ᶜ → ℓ * i < |x - c| := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Ico, not_and_or, not_le, not_lt] at hx
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    have hiN' : (i : ℝ) + j + 1 ≤ N := by exact_mod_cast hiN
    rcases hx with h | h
    · rw [lt_abs]; right
      have : ℓ * i < ℓ * (j + 1 / 2) := by nlinarith
      linarith
    · rw [lt_abs]; left
      have : ℓ * i < ℓ * (N - j - 1 / 2) := by nlinarith
      nlinarith
  have hint : Integrable (wt 3 c ℓ) := integrable_wt (by norm_num) c hℓ
  have hmeas : MeasurableSet (Set.Ico A (A + ℓ * N))ᶜ := measurableSet_Ico.compl
  have hmeas2 : MeasurableSet {x : ℝ | ℓ * i < |x - c|} :=
    measurableSet_lt measurable_const (by fun_prop)
  rw [← integral_indicator hmeas]
  have hind := integral_indicator_one_add_abs_sub_div_rpow (p := 3) (by norm_num) c hℓ hr
  calc ∫ x, ((Set.Ico A (A + ℓ * N))ᶜ).indicator (wt 3 c ℓ) x
      ≤ ∫ x, {x : ℝ | ℓ * i < |x - c|}.indicator (fun x => (1 + |x - c| / ℓ) ^ (-(3 : ℝ))) x := by
        refine integral_mono (hint.indicator hmeas) ?_ fun x => ?_
        · have : Integrable (fun x => (1 + |x - c| / ℓ) ^ (-(3 : ℝ))) :=
            integrable_one_add_abs_sub_div_rpow (by norm_num) c hℓ
          exact this.indicator hmeas2
        · by_cases hx : x ∈ (Set.Ico A (A + ℓ * N))ᶜ
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ {x : ℝ | ℓ * (i : ℝ) < |x - c|} from hsub x hx)]; rfl
          · rw [Set.indicator_of_notMem hx]
            exact Set.indicator_nonneg (fun y _ => by positivity) x
    _ = ℓ * (1 + (i : ℝ)) ^ (-2 : ℝ) := by
        rw [hind, mul_div_cancel_left₀ _ hℓ.ne']
        have : (1 : ℝ) - 3 = -2 := by norm_num
        rw [this]; ring

theorem min_term_le {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (a b : ℕ) : f (min a b) ≤ f a + f b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]; linarith [hf b]
  · rw [min_eq_right h]; linarith [hf a]

/-- `∑_{j < N} f(min(j, N-1-j)) ≤ 2 ∑_{j<N} f j`. -/
theorem sum_min_le {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (N : ℕ) :
    ∑ j ∈ Finset.range N, f (min j (N - 1 - j)) ≤ 2 * ∑ j ∈ Finset.range N, f j := by
  calc ∑ j ∈ Finset.range N, f (min j (N - 1 - j)) ≤ ∑ j ∈ Finset.range N, (f j + f (N - 1 - j)) :=
        Finset.sum_le_sum fun j _ => min_term_le hf _ _
    _ = ∑ j ∈ Finset.range N, f j + ∑ j ∈ Finset.range N, f (N - 1 - j) := Finset.sum_add_distrib
    _ = 2 * ∑ j ∈ Finset.range N, f j := by
        rw [Finset.sum_range_reflect (fun j => f j) N]; ring

/-- **The dyadic tail sum.** -/
theorem tail_sum (s₀ v₀ : ℤ) (T : Finset (ℤ × ℤ))
    (hT : ∀ p ∈ T, dyadicInt p.1 p.2 ⊆ dyadicInt s₀ v₀) :
    ∑ p ∈ T, ∫ x in (dyadicInt s₀ v₀)ᶜ, wt 3 (dyCentre p.1 p.2) ((2 : ℝ) ^ p.1) x ≤
      4 * zetaTwo * (2 : ℝ) ^ s₀ := by
  classical
  set d : ℤ × ℤ → ℕ := fun p => (s₀ - p.1).toNat with hd
  set j : ℤ × ℤ → ℕ := fun p => (p.2 - (2 : ℤ) ^ (d p) * v₀).toNat with hj
  -- the arithmetic of one interval
  have hp : ∀ p ∈ T, s₀ = p.1 + d p ∧ p.2 = (2 : ℤ) ^ (d p) * v₀ + j p ∧ j p < 2 ^ (d p) := by
    intro p hpT
    have hsub := hT p hpT
    have hs : p.1 ≤ s₀ := scale_le_of_dyadicInt_subset hsub
    have hds : s₀ = p.1 + d p := by simp only [hd]; omega
    have h2 : ((2 : ℝ) ^ s₀) = (2 : ℝ) ^ p.1 * (2 : ℝ) ^ (d p) := by
      rw [hds, zpow_add₀ (by norm_num), zpow_natCast]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ p.1 := zpow_pos (by norm_num) _
    have hlt : (2 : ℝ) ^ p.1 * (p.2 : ℝ) < (2 : ℝ) ^ p.1 * ((p.2 : ℝ) + 1) := by nlinarith
    unfold dyadicInt at hsub
    rw [Set.Ico_subset_Ico_iff hlt] at hsub
    obtain ⟨h1, h3⟩ := hsub
    rw [h2] at h1 h3
    have e1 : (2 : ℝ) ^ (d p) * (v₀ : ℝ) ≤ (p.2 : ℝ) := by
      by_contra hc; push Not at hc
      nlinarith [mul_lt_mul_of_pos_left hc hpos]
    have e2 : (p.2 : ℝ) + 1 ≤ (2 : ℝ) ^ (d p) * ((v₀ : ℝ) + 1) := by
      by_contra hc; push Not at hc
      nlinarith [mul_lt_mul_of_pos_left hc hpos]
    have e1' : (2 : ℤ) ^ (d p) * v₀ ≤ p.2 := by exact_mod_cast e1
    have e2' : p.2 + 1 ≤ (2 : ℤ) ^ (d p) * (v₀ + 1) := by exact_mod_cast e2
    refine ⟨hds, ?_, ?_⟩
    · simp only [hj]; omega
    · have e3 : (2 : ℤ) ^ (d p) * (v₀ + 1) = 2 ^ (d p) * v₀ + 2 ^ (d p) := by ring
      have : (j p : ℤ) < 2 ^ (d p) := by simp only [hj]; omega
      exact_mod_cast this
  -- the bound for one interval
  set h : (Σ _ : ℕ, ℕ) → ℝ := fun x =>
    (2 : ℝ) ^ s₀ * (1 / 2) ^ x.1 * (1 + ((min x.2 (2 ^ x.1 - 1 - x.2) : ℕ) : ℝ)) ^ (-2 : ℝ) with hh
  have hbound : ∀ p ∈ T, ∫ x in (dyadicInt s₀ v₀)ᶜ, wt 3 (dyCentre p.1 p.2) ((2 : ℝ) ^ p.1) x ≤
      h ⟨d p, j p⟩ := by
    intro p hpT
    obtain ⟨hds, hv, hjN⟩ := hp p hpT
    have hpos : (0 : ℝ) < (2 : ℝ) ^ p.1 := zpow_pos (by norm_num) _
    have h2 : ((2 : ℝ) ^ s₀) = (2 : ℝ) ^ p.1 * (2 : ℝ) ^ (d p) := by
      rw [hds, zpow_add₀ (by norm_num), zpow_natCast]
    have hc : dyCentre p.1 p.2 = (2 : ℝ) ^ s₀ * (v₀ : ℝ) + (2 : ℝ) ^ p.1 * ((j p : ℝ) + 1 / 2) := by
      unfold dyCentre
      have : (p.2 : ℝ) = (2 : ℝ) ^ (d p) * (v₀ : ℝ) + (j p : ℝ) := by exact_mod_cast hv
      rw [this, h2]; ring
    have hI : dyadicInt s₀ v₀ = Set.Ico ((2 : ℝ) ^ s₀ * (v₀ : ℝ))
        ((2 : ℝ) ^ s₀ * (v₀ : ℝ) + (2 : ℝ) ^ p.1 * ((2 ^ (d p) : ℕ) : ℝ)) := by
      unfold dyadicInt
      congr 1
      push_cast
      rw [h2]; ring
    rw [hc, hI]
    have := tail_tile (A := (2 : ℝ) ^ s₀ * (v₀ : ℝ)) hpos (2 ^ (d p)) (j p)
      (min (j p) (2 ^ (d p) - 1 - j p)) (min_le_left _ _) (by
        have := min_le_right (j p) (2 ^ (d p) - 1 - j p)
        omega)
    refine this.trans (le_of_eq ?_)
    simp only [hh]
    have : (2 : ℝ) ^ p.1 = (2 : ℝ) ^ s₀ * (1 / 2) ^ (d p) := by
      rw [h2, one_div, inv_pow]; field_simp
    rw [this]
  -- sum over the intervals
  have hinj : Set.InjOn (fun p : ℤ × ℤ => (⟨d p, j p⟩ : Σ _ : ℕ, ℕ)) (T : Set (ℤ × ℤ)) := by
    intro p hpT q hqT hpq
    simp only [Sigma.mk.injEq, heq_eq_eq] at hpq
    obtain ⟨hd1, hj1⟩ := hpq
    obtain ⟨hds, hv, -⟩ := hp p hpT
    obtain ⟨hds', hv', -⟩ := hp q hqT
    have h1 : p.1 = q.1 := by omega
    have h2 : p.2 = q.2 := by rw [hv, hv', hd1, hj1]
    exact Prod.ext h1 h2
  set D : ℕ := T.sup d + 1 with hD
  have hsubset : T.image (fun p : ℤ × ℤ => (⟨d p, j p⟩ : Σ _ : ℕ, ℕ)) ⊆
      (Finset.range D).sigma (fun n => Finset.range (2 ^ n)) := by
    intro x hx
    obtain ⟨p, hpT, rfl⟩ := Finset.mem_image.1 hx
    simp only [Finset.mem_sigma, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Finset.le_sup (f := d) hpT), (hp p hpT).2.2⟩
  have hh0 : ∀ x, 0 ≤ h x := fun x => by simp only [hh]; positivity
  have hZ : ∀ n : ℕ, ∑ jj ∈ Finset.range n, (1 + (jj : ℝ)) ^ (-2 : ℝ) ≤ zetaTwo :=
    fun n => summable_zetaTwo.sum_le_tsum _ (fun i _ => by positivity)
  calc ∑ p ∈ T, ∫ x in (dyadicInt s₀ v₀)ᶜ, wt 3 (dyCentre p.1 p.2) ((2 : ℝ) ^ p.1) x
      ≤ ∑ p ∈ T, h ⟨d p, j p⟩ := Finset.sum_le_sum hbound
    _ = ∑ x ∈ T.image (fun p : ℤ × ℤ => (⟨d p, j p⟩ : Σ _ : ℕ, ℕ)), h x :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ x ∈ (Finset.range D).sigma (fun n => Finset.range (2 ^ n)), h x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset fun x _ _ => hh0 x
    _ = ∑ n ∈ Finset.range D, ∑ jj ∈ Finset.range (2 ^ n), h ⟨n, jj⟩ := Finset.sum_sigma _ _ _
    _ ≤ ∑ n ∈ Finset.range D, (2 : ℝ) ^ s₀ * (1 / 2) ^ n * (2 * zetaTwo) := by
        refine Finset.sum_le_sum fun n _ => ?_
        have hinner : ∑ jj ∈ Finset.range (2 ^ n), (1 + ((min jj (2 ^ n - 1 - jj) : ℕ) : ℝ)) ^ (-2 : ℝ) ≤
            2 * zetaTwo := by
          have := sum_min_le (f := fun m : ℕ => (1 + (m : ℝ)) ^ (-2 : ℝ)) (fun m => by positivity) (2 ^ n)
          have h2 := hZ (2 ^ n)
          linarith
        calc ∑ jj ∈ Finset.range (2 ^ n), h ⟨n, jj⟩
            = (2 : ℝ) ^ s₀ * (1 / 2) ^ n * ∑ jj ∈ Finset.range (2 ^ n),
              (1 + ((min jj (2 ^ n - 1 - jj) : ℕ) : ℝ)) ^ (-2 : ℝ) := by
              simp only [hh]; rw [Finset.mul_sum]
          _ ≤ _ := mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = (2 : ℝ) ^ s₀ * (2 * zetaTwo) * ∑ n ∈ Finset.range D, (1 / 2 : ℝ) ^ n := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => by ring
    _ ≤ (2 : ℝ) ^ s₀ * (2 * zetaTwo) * 2 :=
        mul_le_mul_of_nonneg_left (sum_geometric_two_le D) (by have := zetaTwo_nonneg; positivity)
    _ = 4 * zetaTwo * (2 : ℝ) ^ s₀ := by ring

end PrimeBHT.TimeFrequency.X2
