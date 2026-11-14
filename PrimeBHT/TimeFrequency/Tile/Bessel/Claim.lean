module

public import PrimeBHT.TimeFrequency.Tile.Gram.Pair
public import PrimeBHT.TimeFrequency.Tile.Gram.Bessel
public import PrimeBHT.TimeFrequency.Tile.Bessel.Defs
public import PrimeBHT.TimeFrequency.Tile.Bessel.Contrib
public import PrimeBHT.TimeFrequency.Tile.Bessel.Weights
public import PrimeBHT.TimeFrequency.Tile.Bessel.TopSum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The claim of the weak Bessel inequality (blueprint C4, step 5; BD26 Lemma `l:claim`, `m = 0`)

For a tree `T ∈ 𝒯` and `U = ∪𝒯`:
`∑_{t ∈ T} (∑_{t' ∈ U, s(t') < s(t)} |I_{t'}|^{1/2} |⟨φ_{t,k}, φ_{t',k}⟩|)² ≤ claimConst N · |I_T|`
(`sum_sq_contribSum_le`). The corrected exponents (G1 has `N - 1`): the integrand is
`(1 + |c - x|/|I_t|)^{-(N-1)}`, the inner sum is `≲ |I_t|^{1/2} (1 + dist/|I_t|)^{-(N-2)}`, and the
dyadic sum uses `q = 2(N - 2)`.
-/

@[expose] public section

open MeasureTheory
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Tile

/-- The inner sum of the claim: `∑_{t' ∈ U, s(t') < s(t)} |I_{t'}|^{1/2} |⟨φ_{t,k}, φ_{t',k}⟩|`. -/
noncomputable def contribSum (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (k : Fin 3)
    (U : Finset (ℤ × ℤ × ℤ)) (t : ℤ × ℤ × ℤ) : ℝ :=
  open Classical in
  ∑ t' ∈ U with t'.1 < t.1, (volume (timeInt t')).toReal ^ (1 / 2 : ℝ) *
    ‖pairing (φ t k) (φ t' k)‖

/-- `C_N (3/2)^{N-1} · 2/(N-2)`: the constant of the bound on `contribSum`. -/
noncomputable def besselK (N : ℕ) : ℝ :=
  gramConst N * (3 / 2) ^ ((N : ℝ) - 1) * (2 / ((N : ℝ) - 2))

/-- The constant of the claim: `K² · 3 · 4q/(q-1)` with `q = 2(N-2)`. -/
noncomputable def claimConst (N : ℕ) : ℝ :=
  besselK N ^ 2 * (3 * (4 * (2 * ((N : ℝ) - 2) / (2 * ((N : ℝ) - 2) - 1))))

theorem contribSum_nonneg (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (k : Fin 3) (U : Finset (ℤ × ℤ × ℤ))
    (t : ℤ × ℤ × ℤ) : 0 ≤ contribSum φ k U t := by
  unfold contribSum
  exact Finset.sum_nonneg fun t' _ => mul_nonneg (Real.rpow_nonneg (by
    rw [toReal_volume_timeInt]; exact (zpow_pos (by norm_num) _).le) _) (norm_nonneg _)

/-- A point outside `[A, B)` is farther from the midpoint of `[l, ρ) ⊆ [A, B)` than the gap. -/
theorem icoGap_lt_abs_sub_midpoint {A B l ρ x : ℝ} (hlρ : l < ρ) (hx : x ∉ Set.Ico A B) :
    icoGap A B l ρ < |x - (l + ρ) / 2| := by
  rw [Set.mem_Ico, not_and_or] at hx
  rcases hx with h | h
  · have h' : x < A := not_le.mp h
    refine lt_of_le_of_lt (min_le_left _ _) ?_
    rw [abs_sub_comm]
    refine lt_of_lt_of_le ?_ (le_abs_self _)
    linarith
  · have h' : B ≤ x := not_lt.mp h
    refine lt_of_lt_of_le (lt_of_le_of_lt (min_le_right _ _) ?_) (le_abs_self _)
    linarith

section Claim

variable {a b s' α : ℤ} {N : ℕ} {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {i k : Fin 3}
  {P : Finset (ℤ × ℤ × ℤ)} {𝒯 : Finset TreeData}

/-- **Step (iv) of the claim.** For `t ∈ T ∈ 𝒯` and `U = ∪𝒯`:
`∑_{t' ∈ U, s(t') < s(t)} |I_{t'}|^{1/2} |⟨φ_{t,k}, φ_{t',k}⟩| ≤ K |I_t|^{1/2} (1 + g/|I_t|)^{-(N-2)}`
with `g = dist(I_t, I_T^c)` (`icoGap`). -/
theorem contribSum_le (hν : TriValid a b s' α) (hN : 3 ≤ N) (hik : i ≠ k)
    (hP : (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    (hφ : ∀ t ∈ P, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k))
    (h𝒯 : ∀ T ∈ 𝒯, IsTree a b i P T)
    (hSD : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → StronglyDisjoint a b k T T')
    {T : TreeData} (hT : T ∈ 𝒯) {t : ℤ × ℤ × ℤ} (ht : t ∈ T.tiles) :
    contribSum φ k (𝒯.biUnion TreeData.tiles) t ≤
      besselK N * ((2 : ℝ) ^ t.1) ^ (1 / 2 : ℝ) *
        (1 + icoGap (topLeft T) (topRight T) (tileLeft t) (tileRight t) / (2 : ℝ) ^ t.1) ^
          (-((N : ℝ) - 2)) := by
  classical
  set U := 𝒯.biUnion TreeData.tiles with hU
  set L : ℝ := (2 : ℝ) ^ t.1 with hLdef
  have hL : 0 < L := zpow_pos (by norm_num) _
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  set p : ℝ := (N : ℝ) - 1 with hpdef
  have hp : 1 < p := by rw [hpdef]; linarith
  set g : ℝ := icoGap (topLeft T) (topRight T) (tileLeft t) (tileRight t) with hgdef
  have htI : t ∈ triIdx s' α := hP ((h𝒯 T hT).subset ht)
  have htsub : timeInt t ⊆ T.topInt := (h𝒯 T hT).timeInt_subset ht
  obtain ⟨hAl, hrB⟩ := topLeft_le_tileLeft htsub
  have hg0 : 0 ≤ g := le_min (by linarith) (by linarith)
  set c : ℝ := (tileLeft t + tileRight t) / 2 with hcdef
  have hcent : ∀ u : ℤ × ℤ × ℤ, intervalCentre (timeInt u) = (tileLeft u + tileRight u) / 2 := by
    intro u
    rw [intervalCentre_timeInt_eq]
    unfold tileLeft tileRight
    ring
  have hvol : ∀ u : ℤ × ℤ × ℤ, (volume (timeInt u)).toReal = tileRight u - tileLeft u := by
    intro u
    rw [toReal_volume_timeInt, tileRight_sub_tileLeft]
  -- the contributing set
  set Q : Finset (ℤ × ℤ × ℤ) :=
    (U.filter fun t' => t'.1 < t.1).filter
      (fun t' => ¬ Disjoint (freqInt a b k t) (freqInt a b k t')) with hQ
  have hQmem : ∀ t' ∈ Q, t' ∈ U ∧ t'.1 < t.1 ∧ ¬ Disjoint (freqInt a b k t) (freqInt a b k t') := by
    intro t' ht'
    simp only [hQ, Finset.mem_filter] at ht'
    exact ⟨ht'.1.1, ht'.1.2, ht'.2⟩
  have hUmem : ∀ t' ∈ U, ∃ T' ∈ 𝒯, t' ∈ T'.tiles := by
    intro t' ht'
    obtain ⟨T', hT', h⟩ := Finset.mem_biUnion.1 ht'
    exact ⟨T', hT', h⟩
  have hUP : ∀ t' ∈ U, t' ∈ P := by
    intro t' ht'
    obtain ⟨T', hT', h⟩ := hUmem t' ht'
    exact (h𝒯 T' hT').subset h
  -- step 1: the sum is supported on `Q` (Fourier supports)
  have hsupp : contribSum φ k U t =
      ∑ t' ∈ Q, (volume (timeInt t')).toReal ^ (1 / 2 : ℝ) * ‖pairing (φ t k) (φ t' k)‖ := by
    unfold contribSum
    rw [hQ]
    symm
    refine Finset.sum_filter_of_ne fun t' ht' hne => ?_
    by_contra hd
    have hU' : t' ∈ U := (Finset.mem_filter.1 ht').1
    apply hne
    have h0 : pairing (φ t k) (φ t' k) = 0 :=
      pairing_eq_zero_of_disjoint (hφ t ((h𝒯 T hT).subset ht))
        (hφ t' (hUP t' hU')) (isBounded_freqInt a b k t') hd
    rw [h0, norm_zero, mul_zero]
  -- step 2: (G1) termwise
  have hterm : ∀ t' ∈ Q, (volume (timeInt t')).toReal ^ (1 / 2 : ℝ) *
      ‖pairing (φ t k) (φ t' k)‖ ≤
      gramConst N * L ^ (-(1 / 2 : ℝ)) *
        ((tileRight t' - tileLeft t') * (1 + |c - (tileLeft t' + tileRight t') / 2| / L) ^ (-p)) := by
    intro t' ht'
    obtain ⟨hU', hs, -⟩ := hQmem t' ht'
    have hL' : 0 < (volume (timeInt t')).toReal := toReal_volume_timeInt_pos t'
    have hle : (volume (timeInt t')).toReal ≤ (volume (timeInt t)).toReal := by
      rw [toReal_volume_timeInt, toReal_volume_timeInt]
      exact zpow_le_zpow_right₀ (by norm_num) hs.le
    have hG := norm_pairing_le_of_isAdapted (by omega : 2 ≤ N) (hφ t ((h𝒯 T hT).subset ht))
      (hφ t' (hUP t' hU')) hL' hle
    rw [hcent t, hcent t', toReal_volume_timeInt t] at hG
    have hsq : (volume (timeInt t')).toReal ^ (1 / 2 : ℝ) * (volume (timeInt t')).toReal ^
        (1 / 2 : ℝ) = tileRight t' - tileLeft t' := by
      rw [← Real.rpow_add hL', hvol t'] at *
      rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]
    have hw : ((N : ℝ) - 1) = p := rfl
    rw [hw, ← hLdef] at hG
    calc (volume (timeInt t')).toReal ^ (1 / 2 : ℝ) * ‖pairing (φ t k) (φ t' k)‖
        ≤ (volume (timeInt t')).toReal ^ (1 / 2 : ℝ) * (gramConst N * L ^ (-(1 / 2 : ℝ)) *
          (volume (timeInt t')).toReal ^ (1 / 2 : ℝ) *
          (1 + |(tileLeft t + tileRight t) / 2 - (tileLeft t' + tileRight t') / 2| / L) ^ (-p)) :=
          mul_le_mul_of_nonneg_left hG (by positivity)
      _ = gramConst N * L ^ (-(1 / 2 : ℝ)) *
          ((volume (timeInt t')).toReal ^ (1 / 2 : ℝ) * (volume (timeInt t')).toReal ^ (1 / 2 : ℝ)) *
          (1 + |(tileLeft t + tileRight t) / 2 - (tileLeft t' + tileRight t') / 2| / L) ^ (-p) := by
          ring
      _ = _ := by rw [hsq]; ring
  -- step 3: the weighted sum over disjoint intervals
  have hsum := Bessel.sum_len_mul_weight_le Q tileLeft tileRight (c := c) (L := L) (r := g) (p := p) hL hp
    hg0 (fun u _ => tileLeft_lt_tileRight u)
    (fun u hu => by
      rw [tileRight_sub_tileLeft]
      exact zpow_le_zpow_right₀ (by norm_num) (hQmem u hu).2.1.le)
    (fun u hu v hv huv => by
      obtain ⟨hU1, hs1, hn1⟩ := hQmem u hu
      obtain ⟨hU2, hs2, hn2⟩ := hQmem v hv
      obtain ⟨T1, hT1, hu1⟩ := hUmem u hU1
      obtain ⟨T2, hT2, hv2⟩ := hUmem v hU2
      exact disjoint_timeInt_of_contrib hν hik hP h𝒯 hSD hT1 hT2 hu1 hv2
        (ssubset_of_contrib htI (hP ((h𝒯 T1 hT1).subset hu1)) hs1 hn1)
        (ssubset_of_contrib htI (hP ((h𝒯 T2 hT2).subset hv2)) hs2 hn2) huv)
    (fun u hu x hx => by
      obtain ⟨hU1, hs1, hn1⟩ := hQmem u hu
      obtain ⟨T1, hT1, hu1⟩ := hUmem u hU1
      have hd := disjoint_timeInt_topInt_of_contrib hν hik hP h𝒯 hSD hT hT1 ht hu1 hs1 hn1
      have hxT : x ∉ Set.Ico (topLeft T) (topRight T) := fun hx' =>
        Set.disjoint_left.1 hd hx hx'
      exact icoGap_lt_abs_sub_midpoint (tileLeft_lt_tileRight t) hxT)
  have hXL : L ^ (-(1 / 2 : ℝ)) * L = L ^ (1 / 2 : ℝ) := by
    have h := Real.rpow_add hL (-(1 / 2 : ℝ)) 1
    rw [Real.rpow_one] at h
    rw [← h]
    norm_num
  have he : 1 - p = -((N : ℝ) - 2) := by rw [hpdef]; ring
  have hb : besselK N = gramConst N * (3 / 2) ^ p * (2 / (p - 1)) := by
    unfold besselK
    rw [hpdef]
    have : (N : ℝ) - 1 - 1 = (N : ℝ) - 2 := by ring
    rw [this]
  have hG0 : 0 ≤ gramConst N := gramConst_nonneg (by omega)
  rw [he] at hsum
  calc contribSum φ k U t
      = ∑ t' ∈ Q, (volume (timeInt t')).toReal ^ (1 / 2 : ℝ) *
          ‖pairing (φ t k) (φ t' k)‖ := hsupp
    _ ≤ ∑ t' ∈ Q, gramConst N * L ^ (-(1 / 2 : ℝ)) *
        ((tileRight t' - tileLeft t') *
          (1 + |c - (tileLeft t' + tileRight t') / 2| / L) ^ (-p)) := Finset.sum_le_sum hterm
    _ = gramConst N * L ^ (-(1 / 2 : ℝ)) * ∑ t' ∈ Q, ((tileRight t' - tileLeft t') *
          (1 + |c - (tileLeft t' + tileRight t') / 2| / L) ^ (-p)) := by rw [Finset.mul_sum]
    _ ≤ gramConst N * L ^ (-(1 / 2 : ℝ)) *
        ((3 / 2) ^ p * (2 * L * ((1 + g / L) ^ (-((N : ℝ) - 2)) / (p - 1)))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = besselK N * L ^ (1 / 2 : ℝ) * (1 + g / L) ^ (-((N : ℝ) - 2)) := by
        rw [hb]
        linear_combination (gramConst N * (3 / 2) ^ p * 2 * (1 + g / L) ^ (-((N : ℝ) - 2)) /
          (p - 1)) * hXL

theorem rpow_half_sq {L : ℝ} (hL : 0 ≤ L) : (L ^ (1 / 2 : ℝ)) ^ 2 = L := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
  norm_num

theorem rpow_neg_sq {W : ℝ} (hW : 0 ≤ W) (m : ℝ) : (W ^ (-m)) ^ 2 = W ^ (-(2 * m)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hW]
  congr 1
  push_cast
  ring

/-- **The claim** (BD26 `l:claim`, `m = 0`): for `T ∈ 𝒯`,
`∑_{t ∈ T} (∑_{t' ∈ ∪𝒯, s(t') < s(t)} |I_{t'}|^{1/2} |⟨φ_{t,k}, φ_{t',k}⟩|)² ≤ C |I_T|`. -/
theorem sum_sq_contribSum_le (hν : TriValid a b s' α) (hN : 3 ≤ N) (hik : i ≠ k)
    (hP : (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α)
    (hφ : ∀ t ∈ P, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k))
    (h𝒯 : ∀ T ∈ 𝒯, IsTree a b i P T)
    (hSD : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → StronglyDisjoint a b k T T')
    {T : TreeData} (hT : T ∈ 𝒯) :
    ∑ t ∈ T.tiles, contribSum φ k (𝒯.biUnion TreeData.tiles) t ^ 2 ≤
      claimConst N * (volume T.topInt).toReal := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  set q : ℝ := 2 * ((N : ℝ) - 2) with hq
  have hq1 : 1 < q := by rw [hq]; linarith
  have hterm : ∀ t ∈ T.tiles, contribSum φ k (𝒯.biUnion TreeData.tiles) t ^ 2 ≤
      besselK N ^ 2 * icoWeight q (topLeft T) (topRight T) (tileLeft t) (tileRight t) := by
    intro t ht
    have h1 := contribSum_le hν hN hik hP hφ h𝒯 hSD hT ht
    have hL : 0 < (2 : ℝ) ^ t.1 := zpow_pos (by norm_num) _
    have hW : 0 < 1 + icoGap (topLeft T) (topRight T) (tileLeft t) (tileRight t) / (2 : ℝ) ^ t.1 := by
      have hg0 : 0 ≤ icoGap (topLeft T) (topRight T) (tileLeft t) (tileRight t) := by
        obtain ⟨hAl, hrB⟩ := topLeft_le_tileLeft ((h𝒯 T hT).timeInt_subset ht)
        exact le_min (by linarith) (by linarith)
      positivity
    have h2 := pow_le_pow_left₀ (contribSum_nonneg φ k _ t) h1 2
    refine h2.trans (le_of_eq ?_)
    unfold icoWeight
    rw [tileRight_sub_tileLeft, mul_pow, mul_pow, rpow_half_sq hL.le, rpow_neg_sq hW.le]
    have : (-(2 * ((N : ℝ) - 2))) = -q := by rw [hq]
    rw [this]
    ring
  calc ∑ t ∈ T.tiles, contribSum φ k (𝒯.biUnion TreeData.tiles) t ^ 2
      ≤ ∑ t ∈ T.tiles, besselK N ^ 2 *
          icoWeight q (topLeft T) (topRight T) (tileLeft t) (tileRight t) :=
        Finset.sum_le_sum hterm
    _ = besselK N ^ 2 * ∑ t ∈ T.tiles,
          icoWeight q (topLeft T) (topRight T) (tileLeft t) (tileRight t) := by
        rw [Finset.mul_sum]
    _ ≤ besselK N ^ 2 * (3 * (4 * (q / (q - 1)) * (2 : ℝ) ^ T.top.1)) :=
        mul_le_mul_of_nonneg_left (sum_icoWeight_tree_le hP (h𝒯 T hT) hq1) (by positivity)
    _ = claimConst N * (volume T.topInt).toReal := by
        rw [T.toReal_volume_topInt]
        unfold claimConst
        rw [hq]
        ring

end Claim

end PrimeBHT.TimeFrequency.Tile
