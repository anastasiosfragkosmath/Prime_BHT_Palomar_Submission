module

public import PrimeBHT.TimeFrequency.X2.Ortho.Families
public import PrimeBHT.TimeFrequency.X2.Collections

/-!
# X2, node V10: the combinatorial lemma of the TT* argument (HLC Lemma `disjProp`, operator form)

In the Gram-matrix estimate of V10 (HLC `HilbertBasicEst`, nested part `S_2`), one needs, for a fixed tile `R₀`,
the set of tiles `R'` with a *larger-or-equal* frequency interval that is `3`-close to `ω_{R₀}`:
their time intervals `I_{R'}` must be (a) disjoint from the top `I_{T(R₀)}` of the tree of `R₀` and (b) of
multiplicity `≤ 2` (HLC have `1` because their frequency supports are exactly the dyadic `ω`'s; here the supports
are `3ω`, and a lacunary tree may contain two intervals `ω', ω''` on both sides of `ω_{R₀}`).

* `IsStronglyDisjoint.disjoint_top`: (a) for tiles of different trees (both orientations of the pair);
* `IsLacunary.not_three_close`: a `k`-lacunary tree has at most two distinct frequency intervals `ω ≥ ω₀` that are
  `3`-close to `ω₀` (pigeonhole: each `3ω` contains an endpoint of `3ω₀`);
* `no_three_close`: (b) no point lies in the time intervals of three distinct tiles `R_i` of a strongly disjoint
  family of trees of rank-1 boxes with `R_i.box.scale ≤ R₀.box.scale` and `3ω_{R_i} ∩ 3ω_{R₀} ≠ ∅`.
-/

@[expose] public noncomputable section

open MeasureTheory
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- `3ω_{R,k} ∩ 3ω_{R',k} ≠ ∅`. -/
def FreqClose (k : Fin 3) (R R' : TriTile) : Prop :=
  (dilate 3 (R.box.ω k) ∩ dilate 3 (R'.box.ω k)).Nonempty

theorem mem_dilate_omega (B : Box) (k : Fin 3) (C x : ℝ) :
    x ∈ dilate C (B.ω k) ↔
      B.centre k - C * (2 : ℝ) ^ (-B.scale) / 2 ≤ x ∧ x < B.centre k + C * (2 : ℝ) ^ (-B.scale) / 2 := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
  have hlt : B.centre k - (2 : ℝ) ^ (-B.scale) / 2 < B.centre k + (2 : ℝ) ^ (-B.scale) / 2 := by
    linarith
  unfold Box.ω
  rw [dilate_Ico hlt, Set.mem_Ico]
  have e1 : (B.centre k - (2 : ℝ) ^ (-B.scale) / 2 + (B.centre k + (2 : ℝ) ^ (-B.scale) / 2)) / 2 =
      B.centre k := by ring
  have e2 : (B.centre k + (2 : ℝ) ^ (-B.scale) / 2) - (B.centre k - (2 : ℝ) ^ (-B.scale) / 2) =
      (2 : ℝ) ^ (-B.scale) := by ring
  rw [e1, e2]

/-- An interval `[l, r)` of length `≥ |J|` meeting `J = [j₁, j₂)` contains `j₁` or `j₂`. -/
theorem contains_endpoint {l r j₁ j₂ : ℝ} (hlen : j₂ - j₁ ≤ r - l) (hmeet : ∃ a, a ∈ Set.Ico l r ∧ a ∈ Set.Ico j₁ j₂) :
    j₁ ∈ Set.Ico l r ∨ j₂ ∈ Set.Ico l r := by
  obtain ⟨a, ⟨hla, har⟩, ⟨hja, haj⟩⟩ := hmeet
  by_cases h : l ≤ j₁
  · left; exact ⟨h, by linarith⟩
  · right
    push Not at h
    exact ⟨by linarith, by linarith⟩

theorem IsLacunary.not_three_close {k : Fin 3} {T : Finset TriTile} (hT : IsLacunary k T) {R₀ R₁ R₂ R₃ : TriTile}
    (h₁ : R₁ ∈ T) (h₂ : R₂ ∈ T) (h₃ : R₃ ∈ T)
    (s₁ : R₁.box.scale ≤ R₀.box.scale) (s₂ : R₂.box.scale ≤ R₀.box.scale) (s₃ : R₃.box.scale ≤ R₀.box.scale)
    (c₁ : FreqClose k R₁ R₀) (c₂ : FreqClose k R₂ R₀) (c₃ : FreqClose k R₃ R₀)
    (d₁₂ : R₁.box.ω k ≠ R₂.box.ω k) (d₁₃ : R₁.box.ω k ≠ R₃.box.ω k) (d₂₃ : R₂.box.ω k ≠ R₃.box.ω k) :
    False := by
  -- the endpoints of `3 ω₀`
  set j₁ := R₀.box.centre k - 3 * (2 : ℝ) ^ (-R₀.box.scale) / 2 with hj₁
  set j₂ := R₀.box.centre k + 3 * (2 : ℝ) ^ (-R₀.box.scale) / 2 with hj₂
  have key : ∀ R : TriTile, R ∈ T → R.box.scale ≤ R₀.box.scale → FreqClose k R R₀ →
      j₁ ∈ dilate 3 (R.box.ω k) ∨ j₂ ∈ dilate 3 (R.box.ω k) := by
    intro R _ hs hc
    obtain ⟨a, ha1, ha2⟩ := hc
    rw [mem_dilate_omega] at ha1 ha2
    have hle : (2 : ℝ) ^ (-R₀.box.scale) ≤ (2 : ℝ) ^ (-R.box.scale) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have := contains_endpoint (l := R.box.centre k - 3 * (2 : ℝ) ^ (-R.box.scale) / 2)
      (r := R.box.centre k + 3 * (2 : ℝ) ^ (-R.box.scale) / 2) (j₁ := j₁) (j₂ := j₂)
      (by rw [hj₁, hj₂]; nlinarith) ⟨a, ⟨ha1.1, ha1.2⟩, ⟨ha2.1, ha2.2⟩⟩
    simpa only [mem_dilate_omega, Set.mem_Ico] using this
  have hdisj : ∀ {R R' : TriTile}, R ∈ T → R' ∈ T → R.box.ω k ≠ R'.box.ω k →
      Disjoint (dilate 3 (R.box.ω k)) (dilate 3 (R'.box.ω k)) := fun hR hR' hne => hT _ hR _ hR' hne
  have e₁ := key R₁ h₁ s₁ c₁
  have e₂ := key R₂ h₂ s₂ c₂
  have e₃ := key R₃ h₃ s₃ c₃
  have hno : ∀ {R R' : TriTile} (x : ℝ), R ∈ T → R' ∈ T → R.box.ω k ≠ R'.box.ω k →
      x ∈ dilate 3 (R.box.ω k) → x ∈ dilate 3 (R'.box.ω k) → False :=
    fun x hR hR' hne hx hx' => Set.disjoint_left.1 (hdisj hR hR' hne) hx hx'
  rcases e₁ with a₁ | a₁ <;> rcases e₂ with a₂ | a₂ <;> rcases e₃ with a₃ | a₃
  · exact hno _ h₁ h₂ d₁₂ a₁ a₂
  · exact hno _ h₁ h₂ d₁₂ a₁ a₂
  · exact hno _ h₁ h₃ d₁₃ a₁ a₃
  · exact hno _ h₂ h₃ d₂₃ a₂ a₃
  · exact hno _ h₂ h₃ d₂₃ a₂ a₃
  · exact hno _ h₁ h₃ d₁₃ a₁ a₃
  · exact hno _ h₁ h₂ d₁₂ a₁ a₂
  · exact hno _ h₁ h₂ d₁₂ a₁ a₂

/-- `3`-closeness implies `10`-closeness (the hypothesis form of strong disjointness). -/
theorem FreqClose.dilate_ten {k : Fin 3} {R R' : TriTile} (h : FreqClose k R R') :
    (dilate 10 (R.box.ω k) ∩ dilate 10 (R'.box.ω k)).Nonempty := by
  obtain ⟨x, hx1, hx2⟩ := h
  refine ⟨x, ?_, ?_⟩
  · rw [mem_dilate_omega] at hx1 ⊢
    have hp : (0 : ℝ) < (2 : ℝ) ^ (-R.box.scale) := zpow_pos (by norm_num) _
    constructor <;> linarith [hx1.1, hx1.2]
  · rw [mem_dilate_omega] at hx2 ⊢
    have hp : (0 : ℝ) < (2 : ℝ) ^ (-R'.box.scale) := zpow_pos (by norm_num) _
    constructor <;> linarith [hx2.1, hx2.2]

/-- Two frequency-close-to-`R₀` tiles of larger-or-equal frequency interval are `10`-close to each other. -/
theorem FreqClose.dilate_ten_of_both {k : Fin 3} {R₀ R R' : TriTile} (hR : FreqClose k R R₀)
    (hR' : FreqClose k R' R₀) (hs : R.box.scale ≤ R₀.box.scale) (hs' : R'.box.scale ≤ R₀.box.scale) :
    (dilate 10 (R.box.ω k) ∩ dilate 10 (R'.box.ω k)).Nonempty := by
  obtain ⟨p, hp1, hp2⟩ := hR
  obtain ⟨q, hq1, hq2⟩ := hR'
  rw [mem_dilate_omega] at hp1 hp2 hq1 hq2
  set ℓ := (2 : ℝ) ^ (-R.box.scale) with hℓ
  set ℓ' := (2 : ℝ) ^ (-R'.box.scale) with hℓ'
  set ℓ₀ := (2 : ℝ) ^ (-R₀.box.scale) with hℓ₀
  have hℓ0 : 0 < ℓ₀ := zpow_pos (by norm_num) _
  have h1 : ℓ₀ ≤ ℓ := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h2 : ℓ₀ ≤ ℓ' := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hℓp : 0 < ℓ := by linarith
  have hℓ'p : 0 < ℓ' := by linarith
  set c := R.box.centre k
  set c' := R'.box.centre k
  -- the weighted average of the centres
  refine ⟨(c * ℓ' + c' * ℓ) / (ℓ + ℓ'), ?_, ?_⟩
  · rw [mem_dilate_omega]
    have hsum : 0 < ℓ + ℓ' := by linarith
    have hd : |c - c'| < 3 * ℓ + 3 * ℓ' := by
      rw [abs_lt]; constructor <;> linarith [hp1.1, hp1.2, hp2.1, hp2.2, hq1.1, hq1.2, hq2.1, hq2.2]
    rw [abs_lt] at hd
    constructor
    · rw [le_div_iff₀ hsum]; nlinarith
    · rw [div_lt_iff₀ hsum]; nlinarith
  · rw [mem_dilate_omega]
    have hsum : 0 < ℓ + ℓ' := by linarith
    have hd : |c - c'| < 3 * ℓ + 3 * ℓ' := by
      rw [abs_lt]; constructor <;> linarith [hp1.1, hp1.2, hp2.1, hp2.2, hq1.1, hq1.2, hq2.1, hq2.2]
    rw [abs_lt] at hd
    constructor
    · rw [le_div_iff₀ hsum]; nlinarith
    · rw [div_lt_iff₀ hsum]; nlinarith

/-- Strong disjointness, both orientations (the symmetric form of the `Pairwise` hypothesis). -/
theorem IsStronglyDisjoint.disjoint_top {k : Fin 3} {𝒯 : List (Finset TriTile × Top)}
    (h : IsStronglyDisjoint k 𝒯) {T T' : Finset TriTile × Top} (hT : T ∈ 𝒯) (hT' : T' ∈ 𝒯)
    (hne : T ≠ T') {R R' : TriTile} (hR : R ∈ T.1) (hR' : R' ∈ T'.1)
    (hs : R'.box.scale ≤ R.box.scale)
    (hc : (dilate 10 (R'.box.ω k) ∩ dilate 10 (R.box.ω k)).Nonempty) :
    Disjoint R'.I (dyadicInt T.2.1.1 T.2.1.2) := by
  let rel : Finset TriTile × Top → Finset TriTile × Top → Prop := fun T T' =>
    (∀ R ∈ T.1, ∀ R' ∈ T'.1, R.box.scale ≤ R'.box.scale →
          (dilate 10 (R'.box.ω k) ∩ dilate 10 (R.box.ω k)).Nonempty →
          Disjoint R.I (dyadicInt T'.2.1.1 T'.2.1.2)) ∧
      (∀ R ∈ T.1, ∀ R' ∈ T'.1, R'.box.scale ≤ R.box.scale →
          (dilate 10 (R'.box.ω k) ∩ dilate 10 (R.box.ω k)).Nonempty →
          Disjoint R'.I (dyadicInt T.2.1.1 T.2.1.2))
  have : Std.Symm rel :=
    ⟨fun a b hab => ⟨fun R hR R' hR' hs hc => hab.2 R' hR' R hR hs (by rwa [Set.inter_comm]),
      fun R hR R' hR' hs hc => hab.1 R' hR' R hR hs (by rwa [Set.inter_comm])⟩⟩
  have hrel : rel T T' := h.2.forall hT hT' hne
  exact hrel.2 R hR R' hR' hs hc

/-- Equal frequency intervals in a rank-1 box set force equal boxes. -/
theorem box_eq_of_omega_eq {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {k : Fin 3} {B B' : Box}
    (hB : B ∈ Qs) (hB' : B' ∈ Qs) (hω : B.ω k = B'.ω k) : B = B' := by
  have hscale : B.scale = B'.scale := by
    have hlen := congrArg (fun S => (volume S).toReal) hω
    simp only [Box.ω, Real.volume_Ico] at hlen
    have e : ∀ B : Box, (B.centre k + (2 : ℝ) ^ (-B.scale) / 2 - (B.centre k - (2 : ℝ) ^ (-B.scale) / 2)) =
        (2 : ℝ) ^ (-B.scale) := fun B => by ring
    have hp : ∀ B : Box, 0 < (2 : ℝ) ^ (-B.scale) := fun B => zpow_pos (by norm_num) _
    rw [e, e, ENNReal.toReal_ofReal (hp B).le, ENNReal.toReal_ofReal (hp B').le] at hlen
    have := zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hlen
    omega
  by_contra hne
  have := hQ.2.2.1 B hB B' hB' hne hscale k
  obtain ⟨y, hy⟩ := omega_nonempty B k
  exact Set.disjoint_left.1 this hy (hω ▸ hy)

/-- Same frequency interval and intersecting time intervals force equal tiles (rank-1 boxes). -/
theorem eq_of_omega_eq_of_I_inter {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {k : Fin 3} {R R' : TriTile}
    (hR : R.box ∈ Qs) (hR' : R'.box ∈ Qs) (hω : R.box.ω k = R'.box.ω k) {x : ℝ} (hx : x ∈ R.I)
    (hx' : x ∈ R'.I) : R = R' := by
  have hbox : R.box = R'.box := box_eq_of_omega_eq hQ hR hR' hω
  have hpos : R.pos = R'.pos := by
    unfold TriTile.I at hx hx'
    rw [hbox] at hx
    rcases dyadicInt_nested_or_disjoint R'.box.scale R.pos R'.box.scale R'.pos with h1 | h1 | h1
    · exact index_eq_of_dyadicInt_subset rfl h1
    · exact (index_eq_of_dyadicInt_subset rfl h1).symm
    · exact absurd hx' (fun hx'' => Set.disjoint_left.1 h1 hx hx'')
  cases R; cases R'; simp_all

theorem dilate_three_omega (B : Box) (k : Fin 3) :
    dilate 3 (B.ω k) = Set.Ico (B.centre k - 3 * (2 : ℝ) ^ (-B.scale) / 2)
      (B.centre k + 3 * (2 : ℝ) ^ (-B.scale) / 2) := by
  ext x
  rw [mem_dilate_omega, Set.mem_Ico]

end PrimeBHT.TimeFrequency.X2
