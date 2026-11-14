module

public import PrimeBHT.TimeFrequency.Tile.Bessel.Defs
public import PrimeBHT.TimeFrequency.Tile.Bessel.Core
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The weak Bessel inequality (blueprint node C4, `TT.bessel`; BD26 Lemma `l:bessel`, `m = 0`)

## Definitions (`Bessel/Defs.lean`)

```
def StronglyDisjoint (a b : ℤ) (k : Fin 3) (T T' : TreeData) : Prop :=
  ∀ t ∈ T.tiles, ∀ t' ∈ T'.tiles, freqInt a b k t ⊂ freqInt a b k t' → ¬ timeInt t' ⊆ T.topInt

def WeakBesselBound (a b s' α : ℤ) (N : ℕ) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (i k : Fin 3) (C : ℝ) : Prop :=
  i ≠ k → ∀ (P : Finset (ℤ × ℤ × ℤ)), ↑P ⊆ triIdx s' α →
    (∀ t ∈ P, ∀ k', IsAdapted N (timeInt t) (freqInt a b k' t) (φ t k')) →
    ∀ (𝒯 : Finset TreeData), (∀ T ∈ 𝒯, IsTree a b i P T) →
      (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → Disjoint T.tiles T'.tiles) →      -- added (see below)
      (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → StronglyDisjoint a b k T T') →
      ∀ (f : ℝ → ℂ) (lam : ℝ), 0 < lam → MemLp f 2 volume →
        (∀ T ∈ 𝒯, ∀ t ∈ T.tiles, ‖pairing f (φ t k)‖ ^ 2 ≤ 4 * lam ^ 2 * (volume (timeInt t)).toReal) →
        (∀ T ∈ 𝒯, lam ^ 2 / 2 * (volume T.topInt).toReal ≤ ∑ t ∈ T.tiles, ‖pairing f (φ t k)‖ ^ 2) →
        ∑ T ∈ 𝒯, (volume T.topInt).toReal ≤ C * (∫ x, ‖f x‖ ^ 2) / lam ^ 2
```

## Main results

* `weakBessel`: for `3 ≤ N` (in particular `N ≥ 12`) and `TriValid a b s' α`,
  `WeakBesselBound a b s' α N φ i k (weakBesselConst N)`, for all `φ`, `i`, `k`.
  The constant `weakBesselConst N = 2 · coreConst N` depends on `N` only.
* `weakBessel_exists`: `12 ≤ N → ∃ C, ∀ a b s' α, TriValid a b s' α → ∀ φ i k, WeakBesselBound … C`.

## Proof (files `Bessel/*.lean`)

`Cauchy` (`∑|c_i|² = ⟨f, F⟩`, Cauchy-Schwarz, `‖F‖² = ∑∑ c_i c̄_j ⟨u_i, u_j⟩`); `Algebra` (splitting
the double sum by scale, same scale by (G3)); `Contrib` (steps (i)-(iii) of the claim: lacunarity and
strong disjointness); `Weights` (Peetre, integral over the union of the disjoint intervals); `TopSum`
(step (v), dyadic geometry); `Claim` (the claim `∑_t (∑_{t'} …)² ≤ C |I_T|`); `Core` (the case
`∑_{t∈T}|a_t|² ≤ 2μ²|I_T|`); here: reduction by dyadic energy levels.

## Corrections of the blueprint

1. The statement needs the tile sets of the trees of `𝒯` pairwise disjoint (steps 2, 4 use
   `∑_T ∑_{t ∈ T} = ∑_{t ∈ ∪𝒯}`); without it, copies of one tree with different `ξ_T` break it.
2. (G1) has exponent `N - 1`, so step 5 (iv) reads `(1 + |c I_t - x|/|I_t|)^{-(N-1)}` and its result
   `|I_t|^{1/2} (1 + dist/|I_t|)^{-(N-2)}`; step 5 (v) uses `q = 2(N - 2)`.
3. (iv) needs `|I_{t'}| ≤ |I_t|` and Peetre `(1 + |c - c'|/L) ≥ (2/3)(1 + |c - x|/L)` on `I_{t'}`.
4. Only `N ≥ 3` is needed (`N ≥ 12` is not).
-/

@[expose] public section

open MeasureTheory
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Tile

/-- The constant of the weak Bessel inequality: `2 · coreConst N` (`coreConst` is `4 (2 C₃ + 4 + 2 C₄)`). -/
noncomputable def weakBesselConst (N : ℕ) : ℝ := 2 * coreConst N

/-- The energy level `n` with `4^n ≤ 2 r < 4^{n+1}` of a ratio `r ≥ 1/2`. -/
noncomputable def energyLevel (r : ℝ) : ℕ := Nat.log 4 ⌊2 * r⌋₊

theorem energyLevel_bounds {r : ℝ} (hr : 1 / 2 ≤ r) :
    (4 : ℝ) ^ energyLevel r ≤ 2 * r ∧ r < 2 * (4 : ℝ) ^ energyLevel r := by
  have hy : (1 : ℝ) ≤ 2 * r := by linarith
  have hpos : 0 < ⌊2 * r⌋₊ := Nat.floor_pos.2 hy
  unfold energyLevel
  set n := Nat.log 4 ⌊2 * r⌋₊ with hn
  have h1 : 4 ^ n ≤ ⌊2 * r⌋₊ := Nat.pow_log_le_self 4 hpos.ne'
  have h2 : ⌊2 * r⌋₊ < 4 ^ (n + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h1' : ((4 : ℝ) ^ n) ≤ ⌊2 * r⌋₊ := by exact_mod_cast h1
  have h2' : ((⌊2 * r⌋₊ : ℝ) + 1) ≤ (4 : ℝ) ^ (n + 1) := by exact_mod_cast h2
  have h3 : (⌊2 * r⌋₊ : ℝ) ≤ 2 * r := Nat.floor_le (by linarith)
  have h4 : 2 * r < (⌊2 * r⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨h1'.trans h3, ?_⟩
  rw [pow_succ] at h2'
  linarith

section Main

variable {a b s' α : ℤ} {N : ℕ}

/-- **The weak Bessel inequality** (BD26 Lemma `l:bessel`, `m = 0`; blueprint C4). -/
theorem weakBessel (hN : 3 ≤ N) (hν : TriValid a b s' α)
    (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (i k : Fin 3) :
    WeakBesselBound a b s' α N φ i k (weakBesselConst N) := by
  classical
  intro hik P hP hφall 𝒯 h𝒯 hdisj hSD f lam hlam hf htile hlow
  have hφ : ∀ t ∈ P, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k) := fun t ht => hφall t ht k
  set nf : ℝ := ∫ x, ‖f x‖ ^ 2 with hnf
  have hnf0 : 0 ≤ nf := integral_nonneg fun x => by positivity
  set vol : TreeData → ℝ := fun T => (volume T.topInt).toReal with hvol
  have hvolpos : ∀ T, 0 < vol T := fun T => T.toReal_volume_topInt_pos
  set E : TreeData → ℝ := fun T => ∑ t ∈ T.tiles, ‖pairing f (φ t k)‖ ^ 2 with hE
  set r : TreeData → ℝ := fun T => E T / (lam ^ 2 * vol T) with hr
  have hlam2 : 0 < lam ^ 2 := by positivity
  have hrlow : ∀ T ∈ 𝒯, 1 / 2 ≤ r T := by
    intro T hT
    have := hlow T hT
    have hd : 0 < lam ^ 2 * vol T := mul_pos hlam2 (hvolpos T)
    rw [hr]
    simp only
    rw [le_div_iff₀ hd]
    simp only [hE, hvol] at this ⊢
    linarith
  set lev : TreeData → ℕ := fun T => energyLevel (r T) with hlev
  set M : ℕ := 𝒯.sup lev + 1 with hM
  have hmaps : ∀ T ∈ 𝒯, lev T ∈ Finset.range M := fun T hT =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := lev) hT))
  have hsum : ∑ T ∈ 𝒯, vol T = ∑ n ∈ Finset.range M, ∑ T ∈ 𝒯 with lev T = n, vol T :=
    (Finset.sum_fiberwise_of_maps_to hmaps vol).symm
  -- the bound on each level
  have hlevel : ∀ n ∈ Finset.range M, ∑ T ∈ 𝒯 with lev T = n, vol T ≤
      coreConst N * nf / lam ^ 2 * (1 / 2) ^ n := by
    intro n _
    set mu : ℝ := lam * 2 ^ n with hmu
    have hmupos : 0 < mu := by positivity
    have hmu2 : mu ^ 2 = lam ^ 2 * 4 ^ n := by
      rw [hmu, mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
      norm_num
    have h4n : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    have hsub : ∀ T ∈ 𝒯.filter (fun T => lev T = n), T ∈ 𝒯 := fun T hT => (Finset.mem_filter.1 hT).1
    have hcore := coreBound (𝒯 := 𝒯.filter (fun T => lev T = n)) hν hN hik hP hφ
      (fun T hT => h𝒯 T (hsub T hT))
      (fun T hT T' hT' hne => hdisj T (hsub T hT) T' (hsub T' hT') hne)
      (fun T hT T' hT' hne => hSD T (hsub T hT) T' (hsub T' hT') hne) hf hmupos
      (fun T hT t ht => by
        have := htile T (hsub T hT) t ht
        rw [hmu2]
        have hv : 0 ≤ (volume (timeInt t)).toReal := (toReal_volume_timeInt_pos t).le
        nlinarith [mul_nonneg (mul_nonneg hlam2.le hv) (sub_nonneg.2 h4n)])
      (fun T hT => by
        have hT' := hsub T hT
        have hlv : lev T = n := (Finset.mem_filter.1 hT).2
        obtain ⟨h1, -⟩ := energyLevel_bounds (hrlow T hT')
        have h1' : (4 : ℝ) ^ n ≤ 2 * r T := by rw [← hlv]; exact h1
        have hd : 0 < lam ^ 2 * vol T := mul_pos hlam2 (hvolpos T)
        have hE' : E T = r T * (lam ^ 2 * vol T) := by
          rw [hr]; exact (div_mul_cancel₀ (E T) hd.ne').symm
        have : mu ^ 2 / 2 * vol T ≤ E T := by
          rw [hmu2, hE']
          nlinarith [mul_le_mul_of_nonneg_right h1' hd.le]
        exact this)
      (fun T hT => by
        have hT' := hsub T hT
        have hlv : lev T = n := (Finset.mem_filter.1 hT).2
        obtain ⟨-, h2⟩ := energyLevel_bounds (hrlow T hT')
        have h2' : r T < 2 * (4 : ℝ) ^ n := by rw [← hlv]; exact h2
        have hd : 0 < lam ^ 2 * vol T := mul_pos hlam2 (hvolpos T)
        have hE' : E T = r T * (lam ^ 2 * vol T) := by
          rw [hr]; exact (div_mul_cancel₀ (E T) hd.ne').symm
        have : E T ≤ 2 * mu ^ 2 * vol T := by
          rw [hmu2, hE']
          nlinarith [mul_le_mul_of_nonneg_right h2'.le hd.le]
        exact this)
    refine hcore.trans ?_
    rw [hmu2]
    have h4 : (1 : ℝ) / 4 ^ n ≤ (1 / 2) ^ n := by
      rw [one_div_pow, one_div_le_one_div (by positivity) (by positivity)]
      calc (2 : ℝ) ^ n = 2 ^ n := rfl
        _ ≤ 4 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
    have hC := coreConst_nonneg hN
    calc coreConst N * nf / (lam ^ 2 * 4 ^ n)
        = coreConst N * nf / lam ^ 2 * (1 / 4 ^ n) := by field_simp
      _ ≤ coreConst N * nf / lam ^ 2 * (1 / 2) ^ n :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
  calc ∑ T ∈ 𝒯, (volume T.topInt).toReal = ∑ T ∈ 𝒯, vol T := rfl
    _ = ∑ n ∈ Finset.range M, ∑ T ∈ 𝒯 with lev T = n, vol T := hsum
    _ ≤ ∑ n ∈ Finset.range M, coreConst N * nf / lam ^ 2 * (1 / 2) ^ n :=
        Finset.sum_le_sum hlevel
    _ = coreConst N * nf / lam ^ 2 * ∑ n ∈ Finset.range M, (1 / 2 : ℝ) ^ n := by
        rw [Finset.mul_sum]
    _ ≤ coreConst N * nf / lam ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left (sum_geometric_two_le M)
          (by have := coreConst_nonneg hN; positivity)
    _ = weakBesselConst N * nf / lam ^ 2 := by
        unfold weakBesselConst; ring

/-- **The weak Bessel inequality in the uncurried shape of `WeakBesselHyp` (`Select.lean`)**: all of
`φ, i, k, P, 𝒯, f, λ` quantified after the parameters `(a, b, s', α, N)`, strong disjointness written out,
constant `weakBesselConst N`. -/
theorem weakBessel_forall (hN : 3 ≤ N) :
    TriValid a b s' α → ∀ (i k : Fin 3), i ≠ k → ∀ (P : Finset (ℤ × ℤ × ℤ)),
      (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α →
      ∀ (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ),
        (∀ t ∈ P, ∀ j, IsAdapted N (timeInt t) (freqInt a b j t) (φ t j)) →
        ∀ 𝒯 : Finset TreeData, (∀ T ∈ 𝒯, IsTree a b i P T) →
          (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → Disjoint T.tiles T'.tiles) →
          (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → ∀ t ∈ T.tiles, ∀ t' ∈ T'.tiles,
            freqInt a b k t ⊂ freqInt a b k t' → ¬ timeInt t' ⊆ T.topInt) →
          ∀ (f : ℝ → ℂ) (lam : ℝ), 0 < lam → MemLp f 2 volume →
            (∀ T ∈ 𝒯, ∀ t ∈ T.tiles,
              ‖pairing f (φ t k)‖ ^ 2 ≤ 4 * lam ^ 2 * (volume (timeInt t)).toReal) →
            (∀ T ∈ 𝒯, lam ^ 2 / 2 * (volume T.topInt).toReal ≤
              ∑ t ∈ T.tiles, ‖pairing f (φ t k)‖ ^ 2) →
            ∑ T ∈ 𝒯, (volume T.topInt).toReal ≤ weakBesselConst N * (∫ x, ‖f x‖ ^ 2) / lam ^ 2 :=
  fun hν i k hik P hP φ hφ 𝒯 h𝒯 hdisj hSD f lam hlam hf ht hl =>
    weakBessel hN hν φ i k hik P hP hφ 𝒯 h𝒯 hdisj hSD f lam hlam hf ht hl

end Main

end PrimeBHT.TimeFrequency.Tile
