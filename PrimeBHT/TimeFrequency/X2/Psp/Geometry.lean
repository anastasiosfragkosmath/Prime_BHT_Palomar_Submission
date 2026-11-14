module

public import PrimeBHT.TimeFrequency.X2.Psp.Defs
public import PrimeBHT.TimeFrequency.X2.GoodTree
public import PrimeBHT.TimeFrequency.Tile.Gram.Pair
public import PrimeBHT.TimeFrequency.X2.ClassKernel

/-!
# X2, V13: the lattice geometry of MTT2 §4 (G-1 .. G-7)

`docs/audits/X2-V13-route-check.md` §2.3 on the lattice `s₀ + Jℤ`.

**Generic core** (keys `V σ ⊆ ℤ` of dyadic intervals of length `2^σ` inside a top `W`, nested across a finite set `S` of
scales): the bump intervals of the left/right endpoints are pairwise disjoint (`leftBump_pairwiseDisjoint`,
`rightBump_pairwiseDisjoint`), hence `Σ_σ 2^σ #∂ ≤ 6 |W|` (`sum_leftEndsOf_le`, `sum_rightEndsOf_le`).

* **G-1** (`sum_leftEndsE_le`, `sum_rightEndsE_le`): MTT2 Lemma 4.8 for the spatial sets `E_σ` of a good tree;
* **G-2** (`layerSet_subset_eTil`, `eTil_mono`, `dyadicInt_subset_eTil_or_disjoint`, `eTil_subset`): `Ẽ_σ` is a union of
  `σ`-intervals, increasing in `σ`, contains `E_σ`, and every `σ`-interval is inside it or disjoint from it;
* **G-3** (`exists_tile_near`, `exists_tile_at_scale_near`): `3I₀ ∩ Ẽ_σ ≠ ∅` gives a tile `R ∈ Tr` with `|I_R| ≤ |I₀|`,
  `I_R ⊆ 5 I₀` (MTT2: `10 I₀`), and (G-3') a tile of the same scale `σ` with `I_{R'} ⊆ 7 I₀` when `σ` is a tree scale;
* **G-4** (`sum_leftEnds_le`, `sum_rightEnds_le`, `sum_bdryEnds_le`; `leftBump_pairwiseDisjoint_eTil`,
  `leftBump_disjoint_eTil`, `leftBump_subset_dilate_three` and the right versions): the bump intervals are pairwise
  disjoint, lie outside `Ẽ_σ` and in `3 I_t`, and `Σ_σ 2^σ #∂Ẽ_σ ≤ 12 |I_t|`;
* **G-5** (`card_leftBumps_near_le`, `card_rightBumps_near_le`): at most `14` left (right) bumps of scales `≥ σ₀`
  meet `3 I₀`, `|I₀| = 2^{σ₀}`;
* **G-6** (`sum_integral_muW_le`, `sum_integral_muW_le_tree`): `Σ_σ ∫ μ_σ ≤ C |I_t|` (MTT2 (51), `C` independent of `J`);
* **G-7** `isGoodTree_filter_box` / `isGoodTree_treePart` (in `Psp/Split.lean`).
-/

@[expose] public noncomputable section

open MeasureTheory
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-! ## Powers of two -/

theorem zpow_two_pos (n : ℤ) : (0 : ℝ) < (2 : ℝ) ^ n := zpow_pos (by norm_num) n

theorem zpow_sub_one_eq (σ : ℤ) : (2 : ℝ) ^ (σ - 1) = (2 : ℝ) ^ (σ - 2) * 2 := by
  rw [show σ - 1 = (σ - 2) + 1 by ring, zpow_add_one₀ (by norm_num)]

theorem zpow_eq_four_mul (σ : ℤ) : (2 : ℝ) ^ σ = 4 * (2 : ℝ) ^ (σ - 2) := by
  rw [show σ = (σ - 2) + 2 by ring, zpow_add₀ (by norm_num)]
  simp only [sub_add_cancel]
  norm_num
  ring

theorem zpow_sub_one_le {σ σ' : ℤ} (h : σ < σ') : (2 : ℝ) ^ (σ - 1) ≤ (2 : ℝ) ^ (σ' - 2) :=
  zpow_le_zpow_right₀ (by norm_num) (by omega)

/-! ## Disjointness of the bump intervals -/

section Bumps

variable {V : ℤ → Finset ℤ}

theorem mem_dyadicInt_left (σ v : ℤ) : (2 : ℝ) ^ σ * v ∈ dyadicInt σ v :=
  ⟨le_rfl, by have := zpow_two_pos σ; nlinarith⟩

theorem dyadicInt_subset_iff' {σ v : ℤ} {W : ℤ × ℤ} (h : dyadicInt σ v ⊆ dyadicInt W.1 W.2) :
    (2 : ℝ) ^ W.1 * W.2 ≤ (2 : ℝ) ^ σ * v ∧ (2 : ℝ) ^ σ * ((v : ℝ) + 1) ≤ (2 : ℝ) ^ W.1 * ((W.2 : ℝ) + 1) := by
  have hp := zpow_two_pos σ
  exact (Set.Ico_subset_Ico_iff (by nlinarith)).1 h

/-- Bumps of left endpoints of different scales are disjoint (MTT2 Lemma 4.9/4.12). -/
theorem disjoint_leftBump_of_lt {σ σ' : ℤ} (hlt : σ < σ') {x x' : ℝ}
    (hx : x ∈ leftEndsOf σ (V σ)) (hx' : x' ∈ leftEndsOf σ' (V σ'))
    (hnest : ∀ v ∈ V σ, ∃ w ∈ V σ', dyadicInt σ v ⊆ dyadicInt σ' w) :
    Disjoint (leftBump σ x) (leftBump σ' x') := by
  obtain ⟨v, hv, hv1, rfl⟩ := mem_leftEndsOf.1 hx
  obtain ⟨v', hv', hv'1, rfl⟩ := mem_leftEndsOf.1 hx'
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨w, hw, hsub⟩ := hnest v hv
  have hxw : (2 : ℝ) ^ σ * v ∈ dyadicInt σ' w := hsub (mem_dyadicInt_left σ v)
  have hp := zpow_two_pos (σ - 2)
  have hp' := zpow_two_pos (σ' - 2)
  have h1 := zpow_sub_one_le hlt
  have e1 := zpow_sub_one_eq σ
  have e2 := zpow_sub_one_eq σ'
  have e3 := zpow_eq_four_mul σ
  have e4 := zpow_eq_four_mul σ'
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hz3, hz4⟩ := hz'
  have hxv' : (2 : ℝ) ^ σ * v ∈ dyadicInt σ' (v' - 1) := by
    constructor
    · push_cast
      nlinarith
    · push_cast
      nlinarith
  have : w = v' - 1 := by
    by_contra hne
    exact Set.disjoint_left.1 (disjoint_dyadicInt_of_ne hne) hxw hxv'
  exact hv'1 (this ▸ hw)

theorem disjoint_leftBump_of_eq {σ : ℤ} {x x' : ℝ} (hx : x ∈ leftEndsOf σ (V σ))
    (hx' : x' ∈ leftEndsOf σ (V σ)) (hne : x ≠ x') : Disjoint (leftBump σ x) (leftBump σ x') := by
  obtain ⟨v, hv, hv1, rfl⟩ := mem_leftEndsOf.1 hx
  obtain ⟨v', hv', hv'1, rfl⟩ := mem_leftEndsOf.1 hx'
  have hvne : v ≠ v' := fun h => hne (by rw [h])
  have hp := zpow_two_pos (σ - 2)
  have e1 := zpow_sub_one_eq σ
  have e3 := zpow_eq_four_mul σ
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hz3, hz4⟩ := hz'
  have hc : v + 1 ≤ v' ∨ v' + 1 ≤ v := by omega
  rcases hc with hc | hc
  · have : (v : ℝ) + 1 ≤ v' := by exact_mod_cast hc
    nlinarith
  · have : (v' : ℝ) + 1 ≤ v := by exact_mod_cast hc
    nlinarith

theorem leftBump_pairwiseDisjoint {S : Finset ℤ}
    (hnest : ∀ σ ∈ S, ∀ σ' ∈ S, σ < σ' → ∀ v ∈ V σ, ∃ w ∈ V σ', dyadicInt σ v ⊆ dyadicInt σ' w) :
    Set.PairwiseDisjoint (↑(S.sigma fun σ => leftEndsOf σ (V σ)) : Set (Σ _ : ℤ, ℝ))
      (fun p => leftBump p.1 p.2) := by
  rintro ⟨σ, x⟩ hp ⟨σ', x'⟩ hp' hne
  simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe] at hp hp'
  simp only [Function.onFun]
  rcases lt_trichotomy σ σ' with h | h | h
  · exact disjoint_leftBump_of_lt h hp.2 hp'.2 (hnest σ hp.1 σ' hp'.1 h)
  · subst h
    refine disjoint_leftBump_of_eq hp.2 hp'.2 fun hxx => hne ?_
    rw [hxx]
  · exact (disjoint_leftBump_of_lt h hp'.2 hp.2 (hnest σ' hp'.1 σ hp.1 h)).symm

/-- Bumps of right endpoints of different scales are disjoint. -/
theorem disjoint_rightBump_of_lt {σ σ' : ℤ} (hlt : σ < σ') {x x' : ℝ}
    (hx : x ∈ rightEndsOf σ (V σ)) (hx' : x' ∈ rightEndsOf σ' (V σ'))
    (hnest : ∀ v ∈ V σ, ∃ w ∈ V σ', dyadicInt σ v ⊆ dyadicInt σ' w) :
    Disjoint (rightBump σ x) (rightBump σ' x') := by
  obtain ⟨v, hv, hv1, rfl⟩ := mem_rightEndsOf.1 hx
  obtain ⟨v', hv', hv'1, rfl⟩ := mem_rightEndsOf.1 hx'
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨w, hw, hsub⟩ := hnest v hv
  have hp := zpow_two_pos (σ - 2)
  have hp' := zpow_two_pos (σ' - 2)
  have h1 := zpow_sub_one_le hlt
  have e1 := zpow_sub_one_eq σ
  have e2 := zpow_sub_one_eq σ'
  have e3 := zpow_eq_four_mul σ
  have e4 := zpow_eq_four_mul σ'
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hz3, hz4⟩ := hz'
  set X : ℝ := (2 : ℝ) ^ σ * ((v : ℝ) + 1) with hX
  set X' : ℝ := (2 : ℝ) ^ σ' * ((v' : ℝ) + 1) with hX'
  -- `X ∈ (X', X' + 2^σ')`
  have hX1 : X' < X := by nlinarith
  have hX2 : X < X' + (2 : ℝ) ^ σ' := by nlinarith
  -- a point `y` of the key `(σ, v)` in `(X', X' + 2^σ')`
  set y : ℝ := max (X - (2 : ℝ) ^ σ) ((X + X') / 2) with hy
  have hy1 : X - (2 : ℝ) ^ σ ≤ y := le_max_left _ _
  have hy2 : y < X := max_lt (by linarith [zpow_two_pos σ]) (by linarith)
  have hy3 : X' < y := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hyK : y ∈ dyadicInt σ v := by
    constructor
    · have : (2 : ℝ) ^ σ * v = X - (2 : ℝ) ^ σ := by rw [hX]; ring
      linarith
    · exact hy2
  have hyw : y ∈ dyadicInt σ' w := hsub hyK
  have hyv' : y ∈ dyadicInt σ' (v' + 1) := by
    constructor
    · push_cast
      linarith
    · push_cast
      have : (2 : ℝ) ^ σ' * ((v' : ℝ) + 1 + 1) = X' + (2 : ℝ) ^ σ' := by rw [hX']; ring
      linarith
  have : w = v' + 1 := by
    by_contra hne
    exact Set.disjoint_left.1 (disjoint_dyadicInt_of_ne hne) hyw hyv'
  exact hv'1 (this ▸ hw)

theorem disjoint_rightBump_of_eq {σ : ℤ} {x x' : ℝ} (hx : x ∈ rightEndsOf σ (V σ))
    (hx' : x' ∈ rightEndsOf σ (V σ)) (hne : x ≠ x') : Disjoint (rightBump σ x) (rightBump σ x') := by
  obtain ⟨v, hv, hv1, rfl⟩ := mem_rightEndsOf.1 hx
  obtain ⟨v', hv', hv'1, rfl⟩ := mem_rightEndsOf.1 hx'
  have hvne : v ≠ v' := fun h => hne (by rw [h])
  have hp := zpow_two_pos (σ - 2)
  have e1 := zpow_sub_one_eq σ
  have e3 := zpow_eq_four_mul σ
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hz3, hz4⟩ := hz'
  have hc : v + 1 ≤ v' ∨ v' + 1 ≤ v := by omega
  rcases hc with hc | hc
  · have : (v : ℝ) + 1 ≤ v' := by exact_mod_cast hc
    nlinarith
  · have : (v' : ℝ) + 1 ≤ v := by exact_mod_cast hc
    nlinarith

theorem rightBump_pairwiseDisjoint {S : Finset ℤ}
    (hnest : ∀ σ ∈ S, ∀ σ' ∈ S, σ < σ' → ∀ v ∈ V σ, ∃ w ∈ V σ', dyadicInt σ v ⊆ dyadicInt σ' w) :
    Set.PairwiseDisjoint (↑(S.sigma fun σ => rightEndsOf σ (V σ)) : Set (Σ _ : ℤ, ℝ))
      (fun p => rightBump p.1 p.2) := by
  rintro ⟨σ, x⟩ hp ⟨σ', x'⟩ hp' hne
  simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe] at hp hp'
  simp only [Function.onFun]
  rcases lt_trichotomy σ σ' with h | h | h
  · exact disjoint_rightBump_of_lt h hp.2 hp'.2 (hnest σ hp.1 σ' hp'.1 h)
  · subst h
    refine disjoint_rightBump_of_eq hp.2 hp'.2 fun hxx => hne ?_
    rw [hxx]
  · exact (disjoint_rightBump_of_lt h hp'.2 hp.2 (hnest σ' hp'.1 σ hp.1 h)).symm

/-! ### The counting bound -/

theorem volume_leftBump (σ : ℤ) (x : ℝ) : volume (leftBump σ x) = ENNReal.ofReal ((2 : ℝ) ^ (σ - 2)) := by
  unfold leftBump
  rw [Real.volume_Ioo]
  congr 1
  have := zpow_sub_one_eq σ
  linarith

theorem volume_rightBump (σ : ℤ) (x : ℝ) : volume (rightBump σ x) = ENNReal.ofReal ((2 : ℝ) ^ (σ - 2)) := by
  unfold rightBump
  rw [Real.volume_Ioo]
  congr 1
  have := zpow_sub_one_eq σ
  linarith

/-- **Counting (MTT2 Lemma 4.8 / 4.12, generic form)**: `Σ_σ 2^σ #(left endpoints of V σ) ≤ 6 · 2^{W.1}`
for keys inside `W`, nested across the scales of `S`. -/
theorem sum_leftEndsOf_le {W : ℤ × ℤ} {S : Finset ℤ}
    (hW : ∀ σ ∈ S, ∀ v ∈ V σ, dyadicInt σ v ⊆ dyadicInt W.1 W.2)
    (hnest : ∀ σ ∈ S, ∀ σ' ∈ S, σ < σ' → ∀ v ∈ V σ, ∃ w ∈ V σ', dyadicInt σ v ⊆ dyadicInt σ' w) :
    ∑ σ ∈ S, (2 : ℝ) ^ σ * ((leftEndsOf σ (V σ)).card : ℝ) ≤ 6 * (2 : ℝ) ^ W.1 := by
  set 𝓑 := S.sigma fun σ => leftEndsOf σ (V σ) with h𝓑
  have hdisj := leftBump_pairwiseDisjoint (V := V) hnest
  have hmeas : ∀ p ∈ 𝓑, MeasurableSet (leftBump p.1 p.2) := fun _ _ => measurableSet_Ioo
  have h1 := measure_biUnion_finset (μ := (volume : Measure ℝ)) hdisj hmeas
  set a : ℝ := (2 : ℝ) ^ W.1 * W.2 with ha
  set b : ℝ := (2 : ℝ) ^ W.1 * ((W.2 : ℝ) + 1) with hb
  have hsub : (⋃ p ∈ 𝓑, leftBump p.1 p.2) ⊆ Set.Ioo (a - (2 : ℝ) ^ (W.1 - 1)) b := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨⟨σ, x⟩, hp, hz⟩ := hz
    rw [h𝓑, Finset.mem_sigma] at hp
    obtain ⟨hpS, hpx⟩ := hp
    change σ ∈ S at hpS
    change x ∈ leftEndsOf σ (V σ) at hpx
    change z ∈ leftBump σ x at hz
    obtain ⟨v, hv, -, rfl⟩ := mem_leftEndsOf.1 hpx
    have hK := hW σ hpS v hv
    have hxW := hK (mem_dyadicInt_left σ v)
    have hσ := scale_le_of_dyadicInt_subset hK
    have h2 : (2 : ℝ) ^ (σ - 1) ≤ (2 : ℝ) ^ (W.1 - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h3 := zpow_two_pos (σ - 2)
    obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨hx1, hx2⟩ := hxW
    constructor <;> linarith
  have h3 : ∑ p ∈ 𝓑, volume (leftBump p.1 p.2) ≤ volume (Set.Ioo (a - (2 : ℝ) ^ (W.1 - 1)) b) := by
    rw [← h1]; exact measure_mono hsub
  rw [Real.volume_Ioo] at h3
  simp_rw [volume_leftBump] at h3
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => (zpow_two_pos _).le)] at h3
  have hb0 : 0 ≤ b - (a - (2 : ℝ) ^ (W.1 - 1)) := by
    have := zpow_two_pos (W.1 - 1)
    have := zpow_two_pos W.1
    rw [ha, hb]; nlinarith
  have h4 := (ENNReal.ofReal_le_ofReal_iff hb0).1 h3
  rw [h𝓑, Finset.sum_sigma] at h4
  have h5 : ∀ σ ∈ S, ∑ x ∈ leftEndsOf σ (V σ), (2 : ℝ) ^ (σ - 2) =
      ((leftEndsOf σ (V σ)).card : ℝ) * (2 : ℝ) ^ (σ - 2) := fun σ _ => by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl h5] at h4
  have hW1 : b - (a - (2 : ℝ) ^ (W.1 - 1)) = 3 / 2 * (2 : ℝ) ^ W.1 := by
    have := zpow_sub_one_eq W.1
    have := zpow_eq_four_mul W.1
    rw [ha, hb]; nlinarith
  rw [hW1] at h4
  calc ∑ σ ∈ S, (2 : ℝ) ^ σ * ((leftEndsOf σ (V σ)).card : ℝ)
      = 4 * ∑ σ ∈ S, ((leftEndsOf σ (V σ)).card : ℝ) * (2 : ℝ) ^ (σ - 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [zpow_eq_four_mul σ]; ring
    _ ≤ 4 * (3 / 2 * (2 : ℝ) ^ W.1) := by gcongr
    _ = _ := by ring

theorem sum_rightEndsOf_le {W : ℤ × ℤ} {S : Finset ℤ}
    (hW : ∀ σ ∈ S, ∀ v ∈ V σ, dyadicInt σ v ⊆ dyadicInt W.1 W.2)
    (hnest : ∀ σ ∈ S, ∀ σ' ∈ S, σ < σ' → ∀ v ∈ V σ, ∃ w ∈ V σ', dyadicInt σ v ⊆ dyadicInt σ' w) :
    ∑ σ ∈ S, (2 : ℝ) ^ σ * ((rightEndsOf σ (V σ)).card : ℝ) ≤ 6 * (2 : ℝ) ^ W.1 := by
  set 𝓑 := S.sigma fun σ => rightEndsOf σ (V σ) with h𝓑
  have hdisj := rightBump_pairwiseDisjoint (V := V) hnest
  have hmeas : ∀ p ∈ 𝓑, MeasurableSet (rightBump p.1 p.2) := fun _ _ => measurableSet_Ioo
  have h1 := measure_biUnion_finset (μ := (volume : Measure ℝ)) hdisj hmeas
  set a : ℝ := (2 : ℝ) ^ W.1 * W.2 with ha
  set b : ℝ := (2 : ℝ) ^ W.1 * ((W.2 : ℝ) + 1) with hb
  have hsub : (⋃ p ∈ 𝓑, rightBump p.1 p.2) ⊆ Set.Ioo a (b + (2 : ℝ) ^ (W.1 - 1)) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨⟨σ, x⟩, hp, hz⟩ := hz
    rw [h𝓑, Finset.mem_sigma] at hp
    obtain ⟨hpS, hpx⟩ := hp
    change σ ∈ S at hpS
    change x ∈ rightEndsOf σ (V σ) at hpx
    change z ∈ rightBump σ x at hz
    obtain ⟨v, hv, -, rfl⟩ := mem_rightEndsOf.1 hpx
    have hK := hW σ hpS v hv
    have hxW := hK (mem_dyadicInt_left σ v)
    have hσ := scale_le_of_dyadicInt_subset hK
    obtain ⟨hl, hr⟩ := dyadicInt_subset_iff' hK
    have h2 : (2 : ℝ) ^ (σ - 1) ≤ (2 : ℝ) ^ (W.1 - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h3 := zpow_two_pos (σ - 2)
    have e1 := zpow_sub_one_eq σ
    have e3 := zpow_eq_four_mul σ
    obtain ⟨hz1, hz2⟩ := hz
    constructor
    · nlinarith
    · nlinarith
  have h3 : ∑ p ∈ 𝓑, volume (rightBump p.1 p.2) ≤ volume (Set.Ioo a (b + (2 : ℝ) ^ (W.1 - 1))) := by
    rw [← h1]; exact measure_mono hsub
  rw [Real.volume_Ioo] at h3
  simp_rw [volume_rightBump] at h3
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => (zpow_two_pos _).le)] at h3
  have hb0 : 0 ≤ b + (2 : ℝ) ^ (W.1 - 1) - a := by
    have := zpow_two_pos (W.1 - 1)
    have := zpow_two_pos W.1
    rw [ha, hb]; nlinarith
  have h4 := (ENNReal.ofReal_le_ofReal_iff hb0).1 h3
  rw [h𝓑, Finset.sum_sigma] at h4
  have h5 : ∀ σ ∈ S, ∑ x ∈ rightEndsOf σ (V σ), (2 : ℝ) ^ (σ - 2) =
      ((rightEndsOf σ (V σ)).card : ℝ) * (2 : ℝ) ^ (σ - 2) := fun σ _ => by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl h5] at h4
  have hW1 : b + (2 : ℝ) ^ (W.1 - 1) - a = 3 / 2 * (2 : ℝ) ^ W.1 := by
    have := zpow_sub_one_eq W.1
    have := zpow_eq_four_mul W.1
    rw [ha, hb]; nlinarith
  rw [hW1] at h4
  calc ∑ σ ∈ S, (2 : ℝ) ^ σ * ((rightEndsOf σ (V σ)).card : ℝ)
      = 4 * ∑ σ ∈ S, ((rightEndsOf σ (V σ)).card : ℝ) * (2 : ℝ) ^ (σ - 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [zpow_eq_four_mul σ]; ring
    _ ≤ 4 * (3 / 2 * (2 : ℝ) ^ W.1) := by gcongr
    _ = _ := by ring

end Bumps

/-! ## Lattice bookkeeping -/

/-! ## G-1: the spatial sets `E_σ` of a good tree -/

theorem dyadicInt_eq_Ico (σ v : ℤ) :
    dyadicInt σ v = Set.Ico ((2 : ℝ) ^ σ * v) ((2 : ℝ) ^ σ * ((v : ℝ) + 1)) := rfl

theorem dilate_dyadicInt_mono {C : ℝ} (hC : 1 ≤ C) {σ v σ' w : ℤ} (h : dyadicInt σ v ⊆ dyadicInt σ' w) :
    dilate C (dyadicInt σ v) ⊆ dilate C (dyadicInt σ' w) :=
  dilate_Ico_mono_of_subset (timeInt_lt (σ, v, 0)) hC h

theorem layerKeys_subset {Tr : Finset TriTile} {t : Top} (hT : IsTree Tr t) {σ v : ℤ}
    (hv : v ∈ layerKeys Tr σ) : dyadicInt σ v ⊆ dyadicInt t.1.1 t.1.2 := by
  obtain ⟨R, hR, hs, hp⟩ := mem_layerKeys_iff.1 hv
  have := (hT R hR).1
  unfold TriTile.I at this
  rwa [hs, hp] at this

theorem layerKeys_nest {Tr : Finset TriTile} {t : Top} (hg : IsGoodTree Tr t) {σ σ' : ℤ}
    (hσ' : σ' ∈ treeScales Tr) (hlt : σ ≤ σ') :
    ∀ v ∈ layerKeys Tr σ, ∃ w ∈ layerKeys Tr σ', dyadicInt σ v ⊆ dyadicInt σ' w := by
  intro v hv
  obtain ⟨R, hR, hRs, hRp⟩ := mem_layerKeys_iff.1 hv
  obtain ⟨R', hR', hR's⟩ := mem_treeScales_iff.1 hσ'
  have hc := hg.2.2 R' hR' R hR (by omega)
  have hx : (2 : ℝ) ^ σ * v ∈ ⋃ R'' ∈ Tr.filter (fun R'' => R''.box = R.box), R''.I := by
    simp only [Set.mem_iUnion, Finset.mem_filter]
    refine ⟨R, ⟨hR, rfl⟩, ?_⟩
    unfold TriTile.I
    rw [hRs, hRp]
    exact mem_dyadicInt_left σ v
  have hx' := hc hx
  simp only [Set.mem_iUnion, Finset.mem_filter] at hx'
  obtain ⟨R'', ⟨hR'', hbox⟩, hxR''⟩ := hx'
  have hs'' : R''.box.scale = σ' := by rw [hbox, hR's]
  refine ⟨R''.pos, mem_layerKeys_iff.2 ⟨R'', hR'', hs'', rfl⟩, ?_⟩
  have hxR : (2 : ℝ) ^ σ * v ∈ dyadicInt σ v := mem_dyadicInt_left σ v
  unfold TriTile.I at hxR''
  rw [hs''] at hxR''
  exact dyadicInt_subset_of_meet (W := (σ', R''.pos)) hlt hxR hxR''

/-- **G-1 (MTT2 Lemma 4.8)**: for a good tree, `Σ_σ 2^σ #(left endpoints of E_σ) ≤ 6 |I_t|` over any set `S` of tree scales. -/
theorem sum_leftEndsE_le {Tr : Finset TriTile} {t : Top} (hg : IsGoodTree Tr t) {S : Finset ℤ}
    (hS : S ⊆ treeScales Tr) :
    ∑ σ ∈ S, (2 : ℝ) ^ σ * ((leftEndsE Tr σ).card : ℝ) ≤ 6 * (2 : ℝ) ^ t.1.1 := by
  refine sum_leftEndsOf_le (V := layerKeys Tr) (W := t.1) (S := S) ?_ ?_
  · intro σ _ v hv
    exact layerKeys_subset hg.1 hv
  · intro σ hσ σ' hσ' hlt v hv
    exact layerKeys_nest hg (hS hσ') hlt.le v hv

theorem sum_rightEndsE_le {Tr : Finset TriTile} {t : Top} (hg : IsGoodTree Tr t) {S : Finset ℤ}
    (hS : S ⊆ treeScales Tr) :
    ∑ σ ∈ S, (2 : ℝ) ^ σ * ((rightEndsE Tr σ).card : ℝ) ≤ 6 * (2 : ℝ) ^ t.1.1 := by
  refine sum_rightEndsOf_le (V := layerKeys Tr) (W := t.1) (S := S) ?_ ?_
  · intro σ _ v hv
    exact layerKeys_subset hg.1 hv
  · intro σ hσ σ' hσ' hlt v hv
    exact layerKeys_nest hg (hS hσ') hlt.le v hv

/-- `Σ_σ 2^σ #∂E_σ ≤ 12 |I_t|`. -/
theorem sum_bdryEndsE_le {Tr : Finset TriTile} {t : Top} (hg : IsGoodTree Tr t) {S : Finset ℤ}
    (hS : S ⊆ treeScales Tr) :
    ∑ σ ∈ S, (2 : ℝ) ^ σ * ((bdryEndsE Tr σ).card : ℝ) ≤ 12 * (2 : ℝ) ^ t.1.1 := by
  have h1 := sum_leftEndsE_le hg hS
  have h2 := sum_rightEndsE_le hg hS
  calc ∑ σ ∈ S, (2 : ℝ) ^ σ * ((bdryEndsE Tr σ).card : ℝ)
      ≤ ∑ σ ∈ S, ((2 : ℝ) ^ σ * ((leftEndsE Tr σ).card : ℝ) + (2 : ℝ) ^ σ * ((rightEndsE Tr σ).card : ℝ)) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        have : ((bdryEndsE Tr σ).card : ℝ) ≤ (leftEndsE Tr σ).card + (rightEndsE Tr σ).card := by
          exact_mod_cast Finset.card_union_le _ _
        have h := zpow_two_pos σ
        nlinarith
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := by linarith

/-! ## G-2: the sets `Ẽ_σ` -/

section ETil

variable {Tr : Finset TriTile} {W : ℤ × ℤ}

theorem mem_eTilKeys {σ v : ℤ} :
    v ∈ eTilKeys Tr W σ ↔ dyadicInt σ v ⊆ dyadicInt W.1 W.2 ∧ ∃ R ∈ Tr, R.I ⊆ dilate 3 (dyadicInt σ v) := by
  unfold eTilKeys freeKey
  simp only [Set.mem_ofPred_eq, not_forall, not_not, exists_prop]

theorem eTil_subset (σ : ℤ) : eTil Tr W σ ⊆ dyadicInt W.1 W.2 := by
  unfold eTil
  intro z hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨v, hv, hz⟩ := hz
  exact hv.1 hz

theorem eTilKeys_eq_empty {σ : ℤ} (h : W.1 < σ) : eTilKeys Tr W σ = ∅ := by
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hv
  have := scale_le_of_dyadicInt_subset hv.1
  omega

theorem leftEnds_eq_empty {σ : ℤ} (h : W.1 < σ) : leftEnds Tr W σ = ∅ := by
  unfold leftEnds leftEndsOf
  have : eTilKeysF Tr W σ = ∅ := by
    ext v; rw [mem_eTilKeysF, eTilKeys_eq_empty h]; simp
  rw [this]; simp

theorem rightEnds_eq_empty {σ : ℤ} (h : W.1 < σ) : rightEnds Tr W σ = ∅ := by
  unfold rightEnds rightEndsOf
  have : eTilKeysF Tr W σ = ∅ := by
    ext v; rw [mem_eTilKeysF, eTilKeys_eq_empty h]; simp
  rw [this]; simp

/-- **G-2 (monotone)**: the keys of `Ẽ_σ` are nested in `σ` (for `σ ≤ σ' ≤ W.1`). -/
theorem eTilKeys_nest {σ σ' : ℤ} (hle : σ ≤ σ') (hσ' : σ' ≤ W.1) :
    ∀ v ∈ eTilKeys Tr W σ, ∃ w ∈ eTilKeys Tr W σ', dyadicInt σ v ⊆ dyadicInt σ' w := by
  intro v hv
  obtain ⟨hvW, R, hR, hRsub⟩ := mem_eTilKeys.1 hv
  obtain ⟨w, hw⟩ := exists_dyadicInt_superset σ v hle
  have hxv : (2 : ℝ) ^ σ * v ∈ dyadicInt σ v := mem_dyadicInt_left σ v
  have hwW : dyadicInt σ' w ⊆ dyadicInt W.1 W.2 :=
    dyadicInt_subset_of_meet hσ' (hw hxv) (hvW hxv)
  exact ⟨w, mem_eTilKeys.2 ⟨hwW, R, hR, hRsub.trans (dilate_dyadicInt_mono (by norm_num) hw)⟩, hw⟩

theorem eTil_mono {σ σ' : ℤ} (hle : σ ≤ σ') (hσ' : σ' ≤ W.1) : eTil Tr W σ ⊆ eTil Tr W σ' := by
  unfold eTil
  intro z hz
  simp only [Set.mem_iUnion] at hz ⊢
  obtain ⟨v, hv, hz⟩ := hz
  obtain ⟨w, hw, hsub⟩ := eTilKeys_nest hle hσ' v hv
  exact ⟨w, hw, hsub hz⟩

theorem disjoint_dyadicInt_eTil_of_not_mem {σ u : ℤ} (hu : u ∉ eTilKeys Tr W σ) :
    Disjoint (dyadicInt σ u) (eTil Tr W σ) := by
  unfold eTil
  rw [Set.disjoint_iUnion₂_right]
  intro w hw
  have : w ≠ u := fun h => hu (h ▸ hw)
  exact (disjoint_dyadicInt_of_ne this).symm

/-! ## G-4: counting for `Ẽ_σ`, the bumps -/

/-- **G-4 (MTT2 Lemma 4.12)**: `Σ_σ 2^σ #(left endpoints of Ẽ_σ) ≤ 6 |W|` for every finite set `S` of scales. -/
theorem sum_leftEnds_le (S : Finset ℤ) :
    ∑ σ ∈ S, (2 : ℝ) ^ σ * ((leftEnds Tr W σ).card : ℝ) ≤ 6 * (2 : ℝ) ^ W.1 := by
  have h0 : ∑ σ ∈ S, (2 : ℝ) ^ σ * ((leftEnds Tr W σ).card : ℝ) =
      ∑ σ ∈ S.filter (fun σ => σ ≤ W.1), (2 : ℝ) ^ σ * ((leftEnds Tr W σ).card : ℝ) := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun σ hσ hσ' => ?_
    have : W.1 < σ := by
      by_contra h
      exact hσ' (Finset.mem_filter.2 ⟨hσ, not_lt.1 h⟩)
    rw [leftEnds_eq_empty this]; simp
  rw [h0]
  refine sum_leftEndsOf_le (V := eTilKeysF Tr W) (W := W) ?_ ?_
  · intro σ _ v hv
    exact (mem_eTilKeys.1 (mem_eTilKeysF.1 hv)).1
  · intro σ hσ σ' hσ' hlt v hv
    obtain ⟨w, hw, hsub⟩ := eTilKeys_nest hlt.le (Finset.mem_filter.1 hσ').2 v (mem_eTilKeysF.1 hv)
    exact ⟨w, mem_eTilKeysF.2 hw, hsub⟩

theorem sum_rightEnds_le (S : Finset ℤ) :
    ∑ σ ∈ S, (2 : ℝ) ^ σ * ((rightEnds Tr W σ).card : ℝ) ≤ 6 * (2 : ℝ) ^ W.1 := by
  have h0 : ∑ σ ∈ S, (2 : ℝ) ^ σ * ((rightEnds Tr W σ).card : ℝ) =
      ∑ σ ∈ S.filter (fun σ => σ ≤ W.1), (2 : ℝ) ^ σ * ((rightEnds Tr W σ).card : ℝ) := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun σ hσ hσ' => ?_
    have : W.1 < σ := by
      by_contra h
      exact hσ' (Finset.mem_filter.2 ⟨hσ, not_lt.1 h⟩)
    rw [rightEnds_eq_empty this]; simp
  rw [h0]
  refine sum_rightEndsOf_le (V := eTilKeysF Tr W) (W := W) ?_ ?_
  · intro σ _ v hv
    exact (mem_eTilKeys.1 (mem_eTilKeysF.1 hv)).1
  · intro σ hσ σ' hσ' hlt v hv
    obtain ⟨w, hw, hsub⟩ := eTilKeys_nest hlt.le (Finset.mem_filter.1 hσ').2 v (mem_eTilKeysF.1 hv)
    exact ⟨w, mem_eTilKeysF.2 hw, hsub⟩

/-- `Σ_σ 2^σ #∂Ẽ_σ ≤ 12 |W|`. -/
theorem sum_bdryEnds_le (S : Finset ℤ) :
    ∑ σ ∈ S, (2 : ℝ) ^ σ * ((bdryEnds Tr W σ).card : ℝ) ≤ 12 * (2 : ℝ) ^ W.1 := by
  have h1 := sum_leftEnds_le (Tr := Tr) (W := W) S
  have h2 := sum_rightEnds_le (Tr := Tr) (W := W) S
  calc ∑ σ ∈ S, (2 : ℝ) ^ σ * ((bdryEnds Tr W σ).card : ℝ)
      ≤ ∑ σ ∈ S, ((2 : ℝ) ^ σ * ((leftEnds Tr W σ).card : ℝ) + (2 : ℝ) ^ σ * ((rightEnds Tr W σ).card : ℝ)) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        have : ((bdryEnds Tr W σ).card : ℝ) ≤ (leftEnds Tr W σ).card + (rightEnds Tr W σ).card := by
          exact_mod_cast Finset.card_union_le _ _
        have h := zpow_two_pos σ
        nlinarith
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := by linarith

/-- The left bump intervals of `Ẽ_σ`, over all scales, are pairwise disjoint (`σ` ranging over any finite set). -/
theorem leftBump_pairwiseDisjoint_eTil (S : Finset ℤ) :
    Set.PairwiseDisjoint (↑(S.sigma fun σ => leftEnds Tr W σ) : Set (Σ _ : ℤ, ℝ))
      (fun p => leftBump p.1 p.2) := by
  rintro ⟨σ, x⟩ hp ⟨σ', x'⟩ hp' hne
  simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe] at hp hp'
  simp only [Function.onFun]
  have hnest : ∀ τ τ' : ℤ, τ < τ' → τ' ≤ W.1 → ∀ v ∈ eTilKeysF Tr W τ,
      ∃ w ∈ eTilKeysF Tr W τ', dyadicInt τ v ⊆ dyadicInt τ' w := by
    intro τ τ' hlt hτ' v hv
    obtain ⟨w, hw, hsub⟩ := eTilKeys_nest hlt.le hτ' v (mem_eTilKeysF.1 hv)
    exact ⟨w, mem_eTilKeysF.2 hw, hsub⟩
  rcases lt_trichotomy σ σ' with h | h | h
  · by_cases hσ' : σ' ≤ W.1
    · exact disjoint_leftBump_of_lt (V := eTilKeysF Tr W) h hp.2 hp'.2 (hnest σ σ' h hσ')
    · exfalso
      have := leftEnds_eq_empty (Tr := Tr) (not_le.1 hσ')
      rw [this] at hp'; exact absurd hp'.2 (Finset.notMem_empty _)
  · subst h
    refine disjoint_leftBump_of_eq (V := eTilKeysF Tr W) hp.2 hp'.2 fun hxx => hne ?_
    rw [hxx]
  · by_cases hσ : σ ≤ W.1
    · exact (disjoint_leftBump_of_lt (V := eTilKeysF Tr W) h hp'.2 hp.2 (hnest σ' σ h hσ)).symm
    · exfalso
      have := leftEnds_eq_empty (Tr := Tr) (not_le.1 hσ)
      rw [this] at hp; exact absurd hp.2 (Finset.notMem_empty _)

theorem rightBump_pairwiseDisjoint_eTil (S : Finset ℤ) :
    Set.PairwiseDisjoint (↑(S.sigma fun σ => rightEnds Tr W σ) : Set (Σ _ : ℤ, ℝ))
      (fun p => rightBump p.1 p.2) := by
  rintro ⟨σ, x⟩ hp ⟨σ', x'⟩ hp' hne
  simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe] at hp hp'
  simp only [Function.onFun]
  have hnest : ∀ τ τ' : ℤ, τ < τ' → τ' ≤ W.1 → ∀ v ∈ eTilKeysF Tr W τ,
      ∃ w ∈ eTilKeysF Tr W τ', dyadicInt τ v ⊆ dyadicInt τ' w := by
    intro τ τ' hlt hτ' v hv
    obtain ⟨w, hw, hsub⟩ := eTilKeys_nest hlt.le hτ' v (mem_eTilKeysF.1 hv)
    exact ⟨w, mem_eTilKeysF.2 hw, hsub⟩
  rcases lt_trichotomy σ σ' with h | h | h
  · by_cases hσ' : σ' ≤ W.1
    · exact disjoint_rightBump_of_lt (V := eTilKeysF Tr W) h hp.2 hp'.2 (hnest σ σ' h hσ')
    · exfalso
      have := rightEnds_eq_empty (Tr := Tr) (not_le.1 hσ')
      rw [this] at hp'; exact absurd hp'.2 (Finset.notMem_empty _)
  · subst h
    refine disjoint_rightBump_of_eq (V := eTilKeysF Tr W) hp.2 hp'.2 fun hxx => hne ?_
    rw [hxx]
  · by_cases hσ : σ ≤ W.1
    · exact (disjoint_rightBump_of_lt (V := eTilKeysF Tr W) h hp'.2 hp.2 (hnest σ' σ h hσ)).symm
    · exfalso
      have := rightEnds_eq_empty (Tr := Tr) (not_le.1 hσ)
      rw [this] at hp; exact absurd hp.2 (Finset.notMem_empty _)

/-- The left bump of a left endpoint of `Ẽ_σ` lies outside `Ẽ_σ`. -/
theorem leftBump_disjoint_eTil {σ : ℤ} {x : ℝ} (hx : x ∈ leftEnds Tr W σ) :
    Disjoint (leftBump σ x) (eTil Tr W σ) := by
  obtain ⟨v, hv, hv1, rfl⟩ := mem_leftEndsOf.1 hx
  have hu : v - 1 ∉ eTilKeys Tr W σ := fun h => hv1 (mem_eTilKeysF.2 h)
  refine Disjoint.mono_left ?_ (disjoint_dyadicInt_eTil_of_not_mem hu)
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  have e1 := zpow_sub_one_eq σ
  have e3 := zpow_eq_four_mul σ
  have hp := zpow_two_pos (σ - 2)
  constructor
  · push_cast
    nlinarith
  · push_cast
    nlinarith

theorem rightBump_disjoint_eTil {σ : ℤ} {x : ℝ} (hx : x ∈ rightEnds Tr W σ) :
    Disjoint (rightBump σ x) (eTil Tr W σ) := by
  obtain ⟨v, hv, hv1, rfl⟩ := mem_rightEndsOf.1 hx
  have hu : v + 1 ∉ eTilKeys Tr W σ := fun h => hv1 (mem_eTilKeysF.2 h)
  refine Disjoint.mono_left ?_ (disjoint_dyadicInt_eTil_of_not_mem hu)
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  have e1 := zpow_sub_one_eq σ
  have e3 := zpow_eq_four_mul σ
  have hp := zpow_two_pos (σ - 2)
  constructor
  · push_cast
    nlinarith
  · push_cast
    nlinarith

/-- The bumps lie in `3 I_t`. -/
theorem leftBump_subset_dilate_three {σ : ℤ} {x : ℝ} (hx : x ∈ leftEnds Tr W σ) :
    leftBump σ x ⊆ dilate 3 (dyadicInt W.1 W.2) := by
  obtain ⟨v, hv, -, rfl⟩ := mem_leftEndsOf.1 hx
  have hK := (mem_eTilKeys.1 (mem_eTilKeysF.1 hv)).1
  obtain ⟨hl, hr⟩ := dyadicInt_subset_iff' hK
  have hσ := scale_le_of_dyadicInt_subset hK
  have h2 : (2 : ℝ) ^ (σ - 1) ≤ (2 : ℝ) ^ (W.1 - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have e1 := zpow_sub_one_eq W.1
  have e3 := zpow_eq_four_mul W.1
  have hp := zpow_two_pos (σ - 2)
  have hp' := zpow_two_pos (W.1 - 2)
  have hp0 := zpow_two_pos σ
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  rw [dilate_dyadicInt]
  constructor <;> nlinarith

theorem rightBump_subset_dilate_three {σ : ℤ} {x : ℝ} (hx : x ∈ rightEnds Tr W σ) :
    rightBump σ x ⊆ dilate 3 (dyadicInt W.1 W.2) := by
  obtain ⟨v, hv, -, rfl⟩ := mem_rightEndsOf.1 hx
  have hK := (mem_eTilKeys.1 (mem_eTilKeysF.1 hv)).1
  obtain ⟨hl, hr⟩ := dyadicInt_subset_iff' hK
  have hσ := scale_le_of_dyadicInt_subset hK
  have h2 : (2 : ℝ) ^ (σ - 1) ≤ (2 : ℝ) ^ (W.1 - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have e1 := zpow_sub_one_eq W.1
  have e3 := zpow_eq_four_mul W.1
  have hp := zpow_two_pos (σ - 2)
  have hp' := zpow_two_pos (W.1 - 2)
  have hp0 := zpow_two_pos σ
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  rw [dilate_dyadicInt]
  constructor <;> nlinarith

/-! ## G-3: tiles near `Ẽ_σ` -/

theorem mem_dilate_dyadicInt_iff (C : ℝ) (σ v : ℤ) (z : ℝ) :
    z ∈ dilate C (dyadicInt σ v) ↔
      (2 : ℝ) ^ σ * ((v : ℝ) + 1 / 2 - C / 2) ≤ z ∧ z < (2 : ℝ) ^ σ * ((v : ℝ) + 1 / 2 + C / 2) := by
  rw [dilate_dyadicInt]; rfl

/-- A `σ`-interval meeting `3 I₀` is one of the three `σ`-intervals of `3 I₀`. -/
theorem key_near {σ u w : ℤ} {z : ℝ} (hz : z ∈ dyadicInt σ w) (hz' : z ∈ dilate 3 (dyadicInt σ u)) :
    u - 1 ≤ w ∧ w ≤ u + 1 := by
  have hp := zpow_two_pos σ
  rw [mem_dilate_dyadicInt_iff] at hz'
  obtain ⟨h1, h2⟩ := hz
  obtain ⟨h3, h4⟩ := hz'
  have a1 : (w : ℝ) < (u : ℝ) + 2 := by
    by_contra h
    push Not at h
    nlinarith
  have a2 : (u : ℝ) - 2 < (w : ℝ) := by
    by_contra h
    push Not at h
    nlinarith
  have b1 : w < u + 2 := by exact_mod_cast a1
  have b2 : u - 2 < w := by exact_mod_cast a2
  omega

theorem scale_le_of_subset_dilate_three {s p σ w : ℤ} (h : dyadicInt s p ⊆ dilate 3 (dyadicInt σ w)) :
    s ≤ σ + 1 := by
  have hp := zpow_two_pos s
  have hq := zpow_two_pos σ
  have hlt : (2 : ℝ) ^ s * p < (2 : ℝ) ^ s * ((p : ℝ) + 1) := by nlinarith
  rw [dilate_dyadicInt, dyadicInt_eq_Ico] at h
  have := (Set.Ico_subset_Ico_iff hlt).1 h
  obtain ⟨h1, h2⟩ := this
  by_contra hs
  have hs2 : σ + 2 ≤ s := by omega
  have : (2 : ℝ) ^ (σ + 2) ≤ (2 : ℝ) ^ s := zpow_le_zpow_right₀ (by norm_num) hs2
  have e : (2 : ℝ) ^ (σ + 2) = 4 * (2 : ℝ) ^ σ := by
    rw [zpow_add₀ (by norm_num)]; norm_num; ring
  nlinarith

/-- **G-3 (MTT2 Lemma 4.11, get-tile)**: if `3 I₀ ∩ Ẽ_σ ≠ ∅` for a `σ`-interval `I₀` (`σ` on the lattice of the tile
scales, `J ≥ 2`), there is a tile `R ∈ Tr` with `|I_R| ≤ |I₀|` and `I_R ⊆ 5 I₀` (MTT2: `10 I₀`). -/
theorem exists_tile_near {J : ℕ} (hJ : 2 ≤ J) {σ u : ℤ} (hlat : ∀ R ∈ Tr, (J : ℤ) ∣ R.box.scale - σ)
    (h : (dilate 3 (dyadicInt σ u) ∩ eTil Tr W σ).Nonempty) :
    ∃ R ∈ Tr, R.box.scale ≤ σ ∧ R.I ⊆ dilate 5 (dyadicInt σ u) := by
  obtain ⟨z, hz3, hzE⟩ := h
  unfold eTil at hzE
  simp only [Set.mem_iUnion] at hzE
  obtain ⟨w, hw, hzw⟩ := hzE
  obtain ⟨-, R, hR, hRsub⟩ := mem_eTilKeys.1 hw
  obtain ⟨hw1, hw2⟩ := key_near hzw hz3
  refine ⟨R, hR, ?_, ?_⟩
  · have hs := scale_le_of_subset_dilate_three (by unfold TriTile.I at hRsub; exact hRsub)
    by_contra hgt
    have hs1 : R.box.scale = σ + 1 := by omega
    have := hlat R hR
    rw [hs1] at this
    have h1 : ((J : ℤ)) ∣ 1 := by simpa using this
    have := Int.le_of_dvd one_pos h1
    omega
  · intro y hy
    have hy' := hRsub hy
    rw [mem_dilate_dyadicInt_iff] at hy' ⊢
    have hp := zpow_two_pos σ
    have c1 : (u : ℝ) - 1 ≤ w := by exact_mod_cast hw1
    have c2 : (w : ℝ) ≤ u + 1 := by exact_mod_cast hw2
    obtain ⟨h1, h2⟩ := hy'
    constructor <;> nlinarith

end ETil

/-! ## G-5: few bumps near an interval -/

/-! ## G-6: the weight `μ_σ` of MTT2 (51) -/

section Mu

/-- `r = 2^{-1/100}`. -/
def geomR : ℝ := (2 : ℝ) ^ (-(1 / 100 : ℝ))

theorem geomR_pos : 0 < geomR := Real.rpow_pos_of_pos (by norm_num) _

theorem geomR_lt_one : geomR < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- The geometric constant `Σ_{m ∈ ℤ} r^{|m|} ≤ 2/(1 - r)`. -/
def muConst : ℝ := 2 / (1 - geomR)

theorem muConst_pos : 0 < muConst := by
  unfold muConst
  have := geomR_lt_one
  exact div_pos (by norm_num) (by linarith)

theorem geomR_neg_succ (n : ℕ) : geomR ^ (-((n : ℤ) + 1)).natAbs = geomR * geomR ^ n := by
  rw [show (-((n : ℤ) + 1)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_neg, Int.natAbs_natCast, pow_succ']

theorem summable_geom_int : Summable (fun m : ℤ => geomR ^ m.natAbs) := by
  have h0 := geomR_pos
  have h1 := geomR_lt_one
  have hs : Summable (fun n : ℕ => geomR ^ n) := summable_geometric_of_lt_one h0.le h1
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa using hs
  · have := hs.mul_left geomR
    exact this.congr fun n => (geomR_neg_succ n).symm

theorem sum_geom_int_le (M : Finset ℤ) : ∑ m ∈ M, geomR ^ m.natAbs ≤ muConst := by
  have h0 := geomR_pos
  have h1 := geomR_lt_one
  have hs : Summable (fun n : ℕ => geomR ^ n) := summable_geometric_of_lt_one h0.le h1
  calc ∑ m ∈ M, geomR ^ m.natAbs ≤ ∑' m : ℤ, geomR ^ m.natAbs :=
        summable_geom_int.sum_le_tsum M (fun i _ => by positivity)
    _ = ∑' n : ℕ, geomR ^ n + ∑' n : ℕ, geomR * geomR ^ n := by
        rw [tsum_of_nat_of_neg_add_one]
        · simp only [Int.natAbs_natCast]
          simp_rw [geomR_neg_succ]
        · simpa using hs
        · have := hs.mul_left geomR
          exact this.congr fun n => (geomR_neg_succ n).symm
    _ = (1 - geomR)⁻¹ + geomR * (1 - geomR)⁻¹ := by
        rw [tsum_geometric_of_lt_one h0.le h1, tsum_mul_left, tsum_geometric_of_lt_one h0.le h1]
    _ ≤ muConst := by
        unfold muConst
        have : 0 < 1 - geomR := by linarith
        rw [div_eq_mul_inv]
        have : (1 - geomR)⁻¹ + geomR * (1 - geomR)⁻¹ = (1 + geomR) * (1 - geomR)⁻¹ := by ring
        rw [this]
        have hi : 0 < (1 - geomR)⁻¹ := inv_pos.2 (by linarith)
        nlinarith

/-- The lattice sum: for `S` on the lattice `s₀ + Jℤ` and any `σ'` on it,
`Σ_{σ ∈ S} 2^{-|σ - σ'|/(100 J)} ≤ muConst`. -/
theorem sum_lattice_weight_le {J : ℕ} (hJ : 0 < J) {s₀ : ℤ} {S : Finset ℤ} (hS : ∀ σ ∈ S, (J : ℤ) ∣ σ - s₀)
    {σ' : ℤ} (hσ' : (J : ℤ) ∣ σ' - s₀) :
    ∑ σ ∈ S, (2 : ℝ) ^ (-((|σ - σ'| : ℤ) : ℝ) / (100 * (J : ℝ))) ≤ muConst := by
  have hJ0 : (J : ℤ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hJr : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hd : ∀ σ ∈ S, (J : ℤ) ∣ σ - σ' := fun σ hσ => by
    have := dvd_sub (hS σ hσ) hσ'
    rwa [show σ - s₀ - (σ' - s₀) = σ - σ' by ring] at this
  set m : ℤ → ℤ := fun σ => (σ - σ') / J with hm
  have hmul : ∀ σ ∈ S, (σ - σ') = J * m σ := fun σ hσ => (Int.mul_ediv_cancel' (hd σ hσ)).symm
  have hinj : Set.InjOn m (↑S) := by
    intro a ha b hb hab
    have h1 := hmul a ha
    have h2 := hmul b hb
    have : (a - σ') = (b - σ') := by rw [h1, h2]; simp only [hm] at hab ⊢; rw [hab]
    omega
  have hterm : ∀ σ ∈ S, (2 : ℝ) ^ (-((|σ - σ'| : ℤ) : ℝ) / (100 * (J : ℝ))) = geomR ^ (m σ).natAbs := by
    intro σ hσ
    rw [hmul σ hσ, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ J)]
    unfold geomR
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    have hna : (((m σ).natAbs : ℕ) : ℝ) = ((|m σ| : ℤ) : ℝ) := by
      rw [← Int.natCast_natAbs]; simp
    rw [hna]
    push_cast
    field_simp
  calc ∑ σ ∈ S, (2 : ℝ) ^ (-((|σ - σ'| : ℤ) : ℝ) / (100 * (J : ℝ)))
      = ∑ σ ∈ S, geomR ^ (m σ).natAbs := Finset.sum_congr rfl hterm
    _ = ∑ k ∈ S.image m, geomR ^ k.natAbs := (Finset.sum_image (f := fun k : ℤ => geomR ^ k.natAbs) hinj).symm
    _ ≤ muConst := sum_geom_int_le _

theorem integral_jb_inv_pow (y : ℝ) {L : ℝ} (hL : 0 < L) :
    ∫ x, jb ((x - y) / L) ^ (-100 : ℝ) = 2 * L / 99 := by
  have h := integral_one_add_abs_sub_div_rpow (p := 100) (by norm_num) y hL
  have e : ∀ x : ℝ, jb ((x - y) / L) = 1 + |x - y| / L := fun x => by
    unfold jb; rw [abs_div, abs_of_pos hL]
  simp_rw [e]
  rw [h]; norm_num

theorem integrable_jb_inv_pow (y : ℝ) {L : ℝ} (hL : 0 < L) :
    Integrable (fun x : ℝ => jb ((x - y) / L) ^ (-100 : ℝ)) :=
  integrable_jb_rpow (c := y) hL (r := 100) (by norm_num)

theorem integral_muW (J : ℕ) (S : Finset ℤ) (ends : ℤ → Finset ℝ) (σ : ℤ) :
    ∫ x, muW J S ends σ x = ∑ σ' ∈ S, (2 : ℝ) ^ (-((|σ - σ'| : ℤ) : ℝ) / (100 * (J : ℝ))) *
      (((ends σ').card : ℝ) * (2 * (2 : ℝ) ^ σ' / 99)) := by
  unfold muW
  rw [integral_finsetSum _ (fun σ' _ => ((integrable_finsetSum _ (fun y _ =>
    integrable_jb_inv_pow y (zpow_two_pos σ'))).const_mul _))]
  refine Finset.sum_congr rfl fun σ' _ => ?_
  rw [integral_const_mul, integral_finsetSum _ (fun y _ => integrable_jb_inv_pow y (zpow_two_pos σ'))]
  simp_rw [integral_jb_inv_pow _ (zpow_two_pos σ')]
  rw [Finset.sum_const, nsmul_eq_mul]

/-- **G-6 (O4, abstract form)**: `Σ_σ ∫ μ_σ ≤ (2/99) muConst Σ_σ' 2^σ' #ends(σ')` for scales `S` on a lattice
`s₀ + Jℤ`. -/
theorem sum_integral_muW_le {J : ℕ} (hJ : 0 < J) {s₀ : ℤ} {S : Finset ℤ} (hS : ∀ σ ∈ S, (J : ℤ) ∣ σ - s₀)
    (ends : ℤ → Finset ℝ) :
    ∑ σ ∈ S, ∫ x, muW J S ends σ x ≤
      (2 / 99) * muConst * ∑ σ' ∈ S, (2 : ℝ) ^ σ' * ((ends σ').card : ℝ) := by
  simp_rw [integral_muW]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun σ' hσ' => ?_
  rw [← Finset.sum_mul]
  have h1 := sum_lattice_weight_le hJ hS (hS σ' hσ')
  have hc : 0 ≤ ((ends σ').card : ℝ) * (2 * (2 : ℝ) ^ σ' / 99) := by
    have := zpow_two_pos σ'; positivity
  calc (∑ σ ∈ S, (2 : ℝ) ^ (-((|σ - σ'| : ℤ) : ℝ) / (100 * (J : ℝ)))) *
        (((ends σ').card : ℝ) * (2 * (2 : ℝ) ^ σ' / 99))
      ≤ muConst * (((ends σ').card : ℝ) * (2 * (2 : ℝ) ^ σ' / 99)) := mul_le_mul_of_nonneg_right h1 hc
    _ = _ := by ring

/-- **G-6 (O4)**: for a tree with top `W` and lattice scales `S`: `Σ_σ ∫ μ_σ ≤ (24/99) muConst |W|`, with
`μ_σ` built from `∂Ẽ_{σ'}`. -/
theorem sum_integral_muW_le_tree {J : ℕ} (hJ : 0 < J) {s₀ : ℤ} {S : Finset ℤ} (hS : ∀ σ ∈ S, (J : ℤ) ∣ σ - s₀)
    (Tr : Finset TriTile) (W : ℤ × ℤ) :
    ∑ σ ∈ S, ∫ x, muW J S (bdryEnds Tr W) σ x ≤ (24 / 99) * muConst * (2 : ℝ) ^ W.1 := by
  refine (sum_integral_muW_le hJ hS (bdryEnds Tr W)).trans ?_
  have h := sum_bdryEnds_le (Tr := Tr) (W := W) S
  have := muConst_pos
  calc (2 / 99) * muConst * ∑ σ' ∈ S, (2 : ℝ) ^ σ' * ((bdryEnds Tr W σ').card : ℝ)
      ≤ (2 / 99) * muConst * (12 * (2 : ℝ) ^ W.1) := by gcongr
    _ = _ := by ring

end Mu

/-! ## The indicator of a union of `σ`-intervals as a difference of Heaviside sums -/

section Heaviside

/-- The Heaviside function `H = 1_{[0, ∞)}`. -/
def heav (t : ℝ) : ℝ := if 0 ≤ t then 1 else 0

theorem heav_sub_zpow_mul (σ a : ℤ) (y : ℝ) :
    heav (y - (2 : ℝ) ^ σ * (a : ℝ)) = if a ≤ ⌊y / (2 : ℝ) ^ σ⌋ then 1 else 0 := by
  have hp := zpow_two_pos σ
  unfold heav
  have : (0 : ℝ) ≤ y - (2 : ℝ) ^ σ * a ↔ a ≤ ⌊y / (2 : ℝ) ^ σ⌋ := by
    rw [Int.le_floor, le_div_iff₀ hp]
    constructor <;> intro h <;> nlinarith
  simp only [this]

theorem mem_dyadicInt_iff_floor {σ v : ℤ} {y : ℝ} : y ∈ dyadicInt σ v ↔ v = ⌊y / (2 : ℝ) ^ σ⌋ := by
  constructor
  · intro h
    by_contra hne
    exact Set.disjoint_left.1 (disjoint_dyadicInt_of_ne hne) h (mem_dyadicInt_floor σ y)
  · rintro rfl
    exact mem_dyadicInt_floor σ y

theorem cntL_succ (V : Finset ℤ) (n : ℤ) :
    ((V.filter (fun a => a - 1 ∉ V ∧ a ≤ n + 1)).card : ℤ) =
      ((V.filter (fun a => a - 1 ∉ V ∧ a ≤ n)).card : ℤ) + (if (n + 1 ∈ V ∧ n ∉ V) then 1 else 0) := by
  by_cases h : n + 1 ∈ V ∧ n ∉ V
  · rw [ite_eq_left h]
    have e : V.filter (fun a => a - 1 ∉ V ∧ a ≤ n + 1) =
        insert (n + 1) (V.filter (fun a => a - 1 ∉ V ∧ a ≤ n)) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨ha, h1, h2⟩
        by_cases hh : a = n + 1
        · exact Or.inl hh
        · exact Or.inr ⟨ha, h1, by omega⟩
      · rintro (rfl | ⟨ha, h1, h2⟩)
        · exact ⟨h.1, by simpa using h.2, le_rfl⟩
        · exact ⟨ha, h1, by omega⟩
    rw [e, Finset.card_insert_of_notMem (by simp)]
    push_cast; ring
  · rw [ite_eq_right h]
    have e : V.filter (fun a => a - 1 ∉ V ∧ a ≤ n + 1) = V.filter (fun a => a - 1 ∉ V ∧ a ≤ n) := by
      ext a
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨ha, h1, h2⟩
        refine ⟨ha, h1, ?_⟩
        by_contra hn
        have : a = n + 1 := by omega
        subst this
        exact h ⟨ha, by simpa using h1⟩
      · rintro ⟨ha, h1, h2⟩
        exact ⟨ha, h1, by omega⟩
    rw [e]; simp

theorem cntR_succ (V : Finset ℤ) (n : ℤ) :
    ((V.filter (fun v => v + 1 ∉ V ∧ v + 1 ≤ n + 1)).card : ℤ) =
      ((V.filter (fun v => v + 1 ∉ V ∧ v + 1 ≤ n)).card : ℤ) + (if (n ∈ V ∧ n + 1 ∉ V) then 1 else 0) := by
  by_cases h : n ∈ V ∧ n + 1 ∉ V
  · rw [ite_eq_left h]
    have e : V.filter (fun v => v + 1 ∉ V ∧ v + 1 ≤ n + 1) =
        insert n (V.filter (fun v => v + 1 ∉ V ∧ v + 1 ≤ n)) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨ha, h1, h2⟩
        by_cases hh : a = n
        · exact Or.inl hh
        · exact Or.inr ⟨ha, h1, by omega⟩
      · rintro (rfl | ⟨ha, h1, h2⟩)
        · exact ⟨h.1, h.2, le_rfl⟩
        · exact ⟨ha, h1, by omega⟩
    rw [e, Finset.card_insert_of_notMem (by simp)]
    push_cast; ring
  · rw [ite_eq_right h]
    have e : V.filter (fun v => v + 1 ∉ V ∧ v + 1 ≤ n + 1) = V.filter (fun v => v + 1 ∉ V ∧ v + 1 ≤ n) := by
      ext a
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨ha, h1, h2⟩
        refine ⟨ha, h1, ?_⟩
        by_contra hn
        have : a = n := by omega
        subst this
        exact h ⟨ha, h1⟩
      · rintro ⟨ha, h1, h2⟩
        exact ⟨ha, h1, by omega⟩
    rw [e]; simp

/-- The integer telescoping identity: the number of left ends `≤ n` minus the number of right ends `≤ n` is `1_V(n)`. -/
theorem cnt_left_sub_right (V : Finset ℤ) (n : ℤ) :
    ((V.filter (fun a => a - 1 ∉ V ∧ a ≤ n)).card : ℤ) - ((V.filter (fun v => v + 1 ∉ V ∧ v + 1 ≤ n)).card : ℤ) =
      if n ∈ V then 1 else 0 := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, ∀ v ∈ V, m ≤ v := by
    obtain ⟨m, hm⟩ := V.bddBelow
    exact ⟨m, fun v hv => hm hv⟩
  have hlow : ∀ n : ℤ, n < m → ((V.filter (fun a => a - 1 ∉ V ∧ a ≤ n)).card : ℤ) -
      ((V.filter (fun v => v + 1 ∉ V ∧ v + 1 ≤ n)).card : ℤ) = if n ∈ V then 1 else 0 := by
    intro n hn
    have h1 : V.filter (fun a => a - 1 ∉ V ∧ a ≤ n) = ∅ := by
      ext a; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨ha, -, h2⟩; have := hm a ha; omega
    have h2 : V.filter (fun v => v + 1 ∉ V ∧ v + 1 ≤ n) = ∅ := by
      ext a; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨ha, -, h2⟩; have := hm a ha; omega
    have h3 : n ∉ V := fun h => by have := hm n h; omega
    rw [h1, h2, ite_eq_right h3]; simp
  by_cases hn : n < m
  · exact hlow n hn
  · push Not at hn
    have hP : ∀ k : ℕ, ((V.filter (fun a => a - 1 ∉ V ∧ a ≤ m + k)).card : ℤ) -
        ((V.filter (fun v => v + 1 ∉ V ∧ v + 1 ≤ m + k)).card : ℤ) = if m + k ∈ V then 1 else 0 := by
      intro k
      induction k with
      | zero =>
        have h0 := hlow (m - 1) (by omega)
        have h1 := cntL_succ V (m - 1)
        have h2 := cntR_succ V (m - 1)
        simp only [sub_add_cancel] at h1 h2
        simp only [Nat.cast_zero, add_zero]
        rw [h1, h2]
        have h3 : m - 1 ∉ V := fun h => by have := hm _ h; omega
        by_cases hmV : m ∈ V <;> simp [hmV, h3] at h0 ⊢ <;> omega
      | succ k ih =>
        have e : m + ((k + 1 : ℕ) : ℤ) = (m + k) + 1 := by push_cast; ring
        rw [e, cntL_succ, cntR_succ]
        by_cases h1 : m + k ∈ V <;> by_cases h2 : m + k + 1 ∈ V <;> simp [h1, h2] at ih ⊢ <;> omega
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 hn)
    have hnk : n = m + k := by omega
    subst hnk
    exact hP k

theorem sum_heaviside_leftEndsOf (σ : ℤ) (V : Finset ℤ) (y : ℝ) :
    ∑ x ∈ leftEndsOf σ V, heav (y - x) =
      ((V.filter (fun a => a - 1 ∉ V ∧ a ≤ ⌊y / (2 : ℝ) ^ σ⌋)).card : ℝ) := by
  unfold leftEndsOf
  have hinj : Function.Injective (fun v : ℤ => (2 : ℝ) ^ σ * (v : ℝ)) := by
    intro a b h
    have hp := zpow_two_pos σ
    have := mul_left_cancel₀ hp.ne' h
    exact_mod_cast this
  rw [Finset.sum_image (fun a _ b _ h => hinj h)]
  simp_rw [heav_sub_zpow_mul]
  rw [← Finset.sum_filter, Finset.filter_filter]
  simp

theorem sum_heaviside_rightEndsOf (σ : ℤ) (V : Finset ℤ) (y : ℝ) :
    ∑ x ∈ rightEndsOf σ V, heav (y - x) =
      ((V.filter (fun v => v + 1 ∉ V ∧ v + 1 ≤ ⌊y / (2 : ℝ) ^ σ⌋)).card : ℝ) := by
  unfold rightEndsOf
  have hinj : Function.Injective (fun v : ℤ => (2 : ℝ) ^ σ * ((v : ℝ) + 1)) := by
    intro a b h
    have hp := zpow_two_pos σ
    have := mul_left_cancel₀ hp.ne' h
    have h2 : (a : ℝ) = b := by linarith
    exact_mod_cast h2
  rw [Finset.sum_image (fun a _ b _ h => hinj h)]
  have e : ∀ v : ℤ, heav (y - (2 : ℝ) ^ σ * ((v : ℝ) + 1)) =
      if v + 1 ≤ ⌊y / (2 : ℝ) ^ σ⌋ then 1 else 0 := by
    intro v
    have := heav_sub_zpow_mul σ (v + 1) y
    push_cast at this
    exact this
  simp_rw [e]
  rw [← Finset.sum_filter, Finset.filter_filter]
  simp

/-- **The indicator of a union of `σ`-intervals** `⋃_{v ∈ V} [2^σ v, 2^σ (v+1))` is `Σ_{left ends} H(y - x) - Σ_{right ends} H(y - x)`
(`H = 1_{[0,∞)}`): the endpoint sets determine the set. -/
theorem sum_heaviside_leftEndsOf_sub_rightEndsOf (σ : ℤ) (V : Finset ℤ) (y : ℝ) :
    ∑ x ∈ leftEndsOf σ V, heav (y - x) - ∑ x ∈ rightEndsOf σ V, heav (y - x) =
      if y ∈ ⋃ v ∈ V, dyadicInt σ v then 1 else 0 := by
  rw [sum_heaviside_leftEndsOf, sum_heaviside_rightEndsOf]
  have h := cnt_left_sub_right V ⌊y / (2 : ℝ) ^ σ⌋
  have hmem : (y ∈ ⋃ v ∈ V, dyadicInt σ v) ↔ ⌊y / (2 : ℝ) ^ σ⌋ ∈ V := by
    simp only [Set.mem_iUnion, mem_dyadicInt_iff_floor]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact hv
    · intro h; exact ⟨_, h, rfl⟩
  by_cases hy : y ∈ ⋃ v ∈ V, dyadicInt σ v
  · rw [ite_eq_left hy, ite_eq_left (hmem.1 hy)] at *
    exact_mod_cast h
  · rw [ite_eq_right hy]
    rw [ite_eq_right (fun hh => hy (hmem.2 hh))] at h
    exact_mod_cast h

/-- For `Ẽ_σ`: `1_{Ẽ_σ}(y) = Σ_{x ∈ leftEnds} H(y - x) - Σ_{x ∈ rightEnds} H(y - x)`. -/
theorem indicator_eTil_eq_heaviside (Tr : Finset TriTile) (W : ℤ × ℤ) (σ : ℤ) (y : ℝ) :
    (if y ∈ eTil Tr W σ then (1 : ℝ) else 0) =
      ∑ x ∈ leftEnds Tr W σ, heav (y - x) - ∑ x ∈ rightEnds Tr W σ, heav (y - x) := by
  unfold leftEnds rightEnds
  rw [sum_heaviside_leftEndsOf_sub_rightEndsOf]
  have : (⋃ v ∈ eTilKeysF Tr W σ, dyadicInt σ v) = eTil Tr W σ := by
    unfold eTil
    ext y; simp only [Set.mem_iUnion, mem_eTilKeysF]
  rw [this]

/-- For `E_σ`. -/
theorem indicator_layerSet_eq_heaviside (Tr : Finset TriTile) (σ : ℤ) (y : ℝ) :
    (if y ∈ layerSet Tr σ then (1 : ℝ) else 0) =
      ∑ x ∈ leftEndsE Tr σ, heav (y - x) - ∑ x ∈ rightEndsE Tr σ, heav (y - x) := by
  unfold leftEndsE rightEndsE
  rw [sum_heaviside_leftEndsOf_sub_rightEndsOf]
  have : (⋃ v ∈ layerKeys Tr σ, dyadicInt σ v) = layerSet Tr σ := by
    unfold layerSet
    ext y
    simp only [Set.mem_iUnion, mem_layerKeys_iff, mem_layer'_iff]
    constructor
    · rintro ⟨v, ⟨R, hR, hs, hp⟩, hy⟩
      exact ⟨R, ⟨hR, hs⟩, by unfold TriTile.I; rw [hs, hp]; exact hy⟩
    · rintro ⟨R, ⟨hR, hs⟩, hy⟩
      refine ⟨R.pos, ⟨R, hR, hs, rfl⟩, ?_⟩
      unfold TriTile.I at hy; rw [hs] at hy; exact hy
  rw [this]

end Heaviside

end PrimeBHT.TimeFrequency.X2
