module

public import PrimeBHT.TimeFrequency.X2.Collections
public import PrimeBHT.TimeFrequency.X2.Disc.TileCutoff

/-!
# X2, node V05-6: window-full collections and the limit `L → ∞`

* `windowTiles Q W`: all tiles `(B, v)`, `B ∈ Q`, `dyadicInt B.scale v ⊆ dyadicInt W.1 W.2` (a finite `Finset`);
  `isWindowFull_windowTiles : ↑Q ⊆ Qs → IsWindowFull Qs (windowTiles Q W)`.
* `tendsto_windows`: for a finite `Q`, a continuous profile `η` with `Σ_v χ_{s,v} = 1`, and integrable `h_B`,
  the sum of the two window forms (`dyadicInt L 0` and `dyadicInt L (-1)`) `Σ_P ∫ χ_P h_{P.box}` tends to
  `Σ_{B ∈ Q} ∫ h_B` as `L → ∞` (dominated convergence).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Disc

/-- Index range of the dyadic intervals of scale `s` inside `dyadicInt L w`. -/
def winRange (L w s : ℤ) : Finset ℤ :=
  if s ≤ L then Finset.Ico (w * 2 ^ (L - s).toNat) ((w + 1) * 2 ^ (L - s).toNat) else ∅

theorem two_zpow_eq {s L : ℤ} (h : s ≤ L) : (2 : ℝ) ^ L = 2 ^ s * (((2 : ℤ) ^ (L - s).toNat : ℤ) : ℝ) := by
  have : L = s + ((L - s).toNat : ℤ) := by omega
  conv_lhs => rw [this]
  rw [zpow_add₀ (by norm_num), zpow_natCast]
  push_cast
  ring

theorem dyadicInt_subset_iff {s v L w : ℤ} :
    dyadicInt s v ⊆ dyadicInt L w ↔
      s ≤ L ∧ w * 2 ^ (L - s).toNat ≤ v ∧ v < (w + 1) * 2 ^ (L - s).toNat := by
  have hs : (0 : ℝ) < 2 ^ s := zpow_pos (by norm_num) _
  constructor
  · intro h
    have hsL := scale_le_of_dyadicInt_subset h
    refine ⟨hsL, ?_⟩
    unfold dyadicInt at h
    have := (Set.Ico_subset_Ico_iff (by nlinarith : (2 : ℝ) ^ s * v < 2 ^ s * (v + 1))).1 h
    rw [two_zpow_eq hsL] at this
    set K : ℤ := 2 ^ (L - s).toNat with hK
    have h1 : ((w * K : ℤ) : ℝ) ≤ (v : ℝ) := by
      push_cast
      have := this.1
      nlinarith
    have h2 : (v : ℝ) + 1 ≤ (((w + 1) * K : ℤ) : ℝ) := by
      push_cast
      have := this.2
      nlinarith
    constructor
    · exact_mod_cast h1
    · have : v + 1 ≤ (w + 1) * K := by exact_mod_cast h2
      omega
  · rintro ⟨hsL, h1, h2⟩
    unfold dyadicInt
    rw [two_zpow_eq hsL]
    set K : ℤ := 2 ^ (L - s).toNat with hK
    have h1' : ((w * K : ℤ) : ℝ) ≤ v := by exact_mod_cast h1
    have h2' : (v : ℝ) + 1 ≤ (((w + 1) * K : ℤ) : ℝ) := by
      have : v + 1 ≤ (w + 1) * K := by omega
      exact_mod_cast this
    push_cast at h1' h2'
    apply Set.Ico_subset_Ico
    · nlinarith
    · nlinarith

/-- The finite set of tiles of the boxes in `Q` whose time interval lies in the window `W`. -/
def windowTiles (Q : Finset Box) (W : ℤ × ℤ) : Finset TriTile :=
  Q.biUnion fun B => (winRange W.1 W.2 B.scale).image fun v => (⟨B, v⟩ : TriTile)

theorem mem_windowTiles {Q : Finset Box} {W : ℤ × ℤ} {R : TriTile} :
    R ∈ windowTiles Q W ↔ R.box ∈ Q ∧ R.I ⊆ dyadicInt W.1 W.2 := by
  unfold windowTiles winRange TriTile.I
  rw [dyadicInt_subset_iff (s := R.box.scale)]
  simp only [Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨B, hB, v, hv, rfl⟩
    by_cases h : B.scale ≤ W.1
    · rw [ite_eq_left h, Finset.mem_Ico] at hv
      exact ⟨hB, h, hv.1, hv.2⟩
    · rw [ite_eq_right h] at hv; simp at hv
  · rintro ⟨hB, h, h1, h2⟩
    exact ⟨R.box, hB, R.pos, by rw [ite_eq_left h, Finset.mem_Ico]; exact ⟨h1, h2⟩, rfl⟩

theorem isWindowFull_windowTiles {Qs : Set Box} {Q : Finset Box} (hQ : (↑Q : Set Box) ⊆ Qs) (W : ℤ × ℤ) :
    IsWindowFull Qs (windowTiles Q W) :=
  ⟨Q, W, hQ, fun _R => mem_windowTiles⟩

theorem sum_windowTiles (Q : Finset Box) (W : ℤ × ℤ) (F : TriTile → ℂ) :
    ∑ P ∈ windowTiles Q W, F P = ∑ B ∈ Q, ∑ v ∈ winRange W.1 W.2 B.scale, F ⟨B, v⟩ := by
  unfold windowTiles
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun B _ => ?_
    rw [Finset.sum_image]
    intro a _ b _ h
    exact (TriTile.mk.inj h).2
  · intro B₁ _ B₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro P hP1 hP2
    simp only [Finset.mem_image] at hP1 hP2
    obtain ⟨v1, -, rfl⟩ := hP1
    obtain ⟨v2, -, h2⟩ := hP2
    exact hne (TriTile.mk.inj h2).1.symm

/-- Both windows `[0, 2^L)` and `[-2^L, 0)` together: the index range `[-2^{L-s}, 2^{L-s})`. -/
theorem winRange_union {L s : ℤ} (h : s ≤ L) :
    winRange L 0 s ∪ winRange L (-1) s = Finset.Ico (-(2 ^ (L - s).toNat : ℤ)) (2 ^ (L - s).toNat) := by
  unfold winRange
  rw [ite_eq_left h, ite_eq_left h]
  ext v
  simp only [Finset.mem_union, Finset.mem_Ico]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    by_cases hv : 0 ≤ v
    · left; constructor <;> nlinarith
    · right; constructor <;> nlinarith

theorem winRange_disjoint {L s : ℤ} : Disjoint (winRange L 0 s) (winRange L (-1) s) := by
  unfold winRange
  by_cases h : s ≤ L
  · rw [ite_eq_left h, ite_eq_left h, Finset.disjoint_left]
    intro v h1 h2
    simp only [Finset.mem_Ico] at h1 h2
    nlinarith [h1.1, h2.2]
  · rw [ite_eq_right h]; simp

theorem tileCutoff_nonneg {η : ℝ → ℝ} (hnn : ∀ x, 0 ≤ η x) (s v : ℤ) (x : ℝ) : 0 ≤ tileCutoff η s v x := by
  unfold tileCutoff
  apply setIntegral_nonneg measurableSet_Ico
  intro y _
  exact mul_nonneg (zpow_nonneg (by norm_num) _) (hnn _)

theorem sum_tileCutoff_le_one {η : ℝ → ℝ} (hη : Continuous η) (hint : Integrable η) (hnn : ∀ x, 0 ≤ η x)
    (h1 : ∫ x, η x = 1) (s : ℤ) (x : ℝ) (A : Finset ℤ) : ∑ v ∈ A, tileCutoff η s v x ≤ 1 :=
  sum_le_hasSum A (fun v _ => tileCutoff_nonneg hnn s v x) (hasSum_tileCutoff hη hint h1 s x)

theorem tendsto_winRange (s : ℤ) :
    Tendsto (fun L : ℕ => winRange (L : ℤ) 0 s ∪ winRange (L : ℤ) (-1) s) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro A
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ a ∈ A, -(N : ℤ) ≤ a ∧ a < N := by
    refine ⟨A.sup (fun a => a.natAbs) + 1, fun a ha => ?_⟩
    have := Finset.le_sup (f := fun a : ℤ => a.natAbs) ha
    omega
  filter_upwards [eventually_ge_atTop (N + s.toNat)] with L hL
  have hsL : s ≤ (L : ℤ) := by omega
  rw [winRange_union hsL]
  intro a ha
  obtain ⟨h1, h2⟩ := hN a ha
  have hK : (L : ℤ) - s ≤ ((2 : ℤ) ^ ((L : ℤ) - s).toNat : ℤ) := by
    have := Nat.lt_two_pow_self (n := ((L : ℤ) - s).toNat)
    have h3 : (((L : ℤ) - s).toNat : ℤ) = (L : ℤ) - s := Int.toNat_of_nonneg (by omega)
    have h4 : (((L : ℤ) - s).toNat : ℤ) < ((2 ^ ((L : ℤ) - s).toNat : ℕ) : ℤ) := by exact_mod_cast this
    push_cast at h4
    omega
  simp only [Finset.mem_Ico]
  constructor <;> omega

/-- **V05-6 (the limit).**  The sum of the two window forms `dyadicInt L 0`, `dyadicInt L (-1)` of the integrands
`χ_P h_{P.box}` tends to `Σ_B ∫ h_B` as `L → ∞` (partition of unity `Σ_v χ_{s,v} = 1` and dominated convergence). -/
theorem tendsto_windows {η : ℝ → ℝ} (hη : Continuous η) (hint : Integrable η) (hnn : ∀ x, 0 ≤ η x)
    (h1 : ∫ x, η x = 1) (Q : Finset Box) (h : Box → ℝ → ℂ) (hh : ∀ B ∈ Q, Integrable (h B)) :
    Tendsto (fun L : ℕ =>
      (∑ P ∈ windowTiles Q ((L : ℤ), 0), ∫ x, (tileCutoff η P.box.scale P.pos x : ℂ) * h P.box x) +
      (∑ P ∈ windowTiles Q ((L : ℤ), -1), ∫ x, (tileCutoff η P.box.scale P.pos x : ℂ) * h P.box x))
      atTop (𝓝 (∑ B ∈ Q, ∫ x, h B x)) := by
  have hbdd : ∀ s v : ℤ, ∀ x, ‖((tileCutoff η s v x : ℝ) : ℂ)‖ ≤ 1 := by
    intro s v x
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tileCutoff_nonneg hnn s v x)]
    simpa using sum_tileCutoff_le_one hη hint hnn h1 s x {v}
  have hint_v : ∀ B ∈ Q, ∀ v : ℤ, Integrable (fun x => ((tileCutoff η B.scale v x : ℝ) : ℂ) * h B x) := by
    intro B hB v
    exact (hh B hB).bdd_mul (c := 1)
      (Complex.continuous_ofReal.comp (disc_continuous_tileCutoff hη B.scale v)).aestronglyMeasurable
      (Filter.Eventually.of_forall (hbdd B.scale v))
  -- regroup
  have key : ∀ L : ℕ,
      (∑ P ∈ windowTiles Q ((L : ℤ), 0), ∫ x, (tileCutoff η P.box.scale P.pos x : ℂ) * h P.box x) +
      (∑ P ∈ windowTiles Q ((L : ℤ), -1), ∫ x, (tileCutoff η P.box.scale P.pos x : ℂ) * h P.box x) =
      ∑ B ∈ Q, ∫ x, (((∑ v ∈ winRange (L : ℤ) 0 B.scale ∪ winRange (L : ℤ) (-1) B.scale,
        tileCutoff η B.scale v x : ℝ)) : ℂ) * h B x := by
    intro L
    rw [sum_windowTiles, sum_windowTiles, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun B hB => ?_
    dsimp only
    rw [← Finset.sum_union winRange_disjoint]
    simp_rw [Complex.ofReal_sum, Finset.sum_mul]
    exact (integral_finset_sum _ (fun v _ => hint_v B hB v)).symm
  simp_rw [key]
  refine tendsto_finsetSum _ fun B hB => ?_
  have hmeas : ∀ L : ℕ, AEStronglyMeasurable (fun x => (((∑ v ∈ winRange (L : ℤ) 0 B.scale ∪
      winRange (L : ℤ) (-1) B.scale, tileCutoff η B.scale v x : ℝ)) : ℂ) * h B x) volume := by
    intro L
    have hc : Continuous fun x => (((∑ v ∈ winRange (L : ℤ) 0 B.scale ∪ winRange (L : ℤ) (-1) B.scale,
        tileCutoff η B.scale v x : ℝ)) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_finsetSum _ fun v _ => disc_continuous_tileCutoff hη B.scale v)
    exact hc.aestronglyMeasurable.mul (hh B hB).aestronglyMeasurable
  have hlim : ∀ x, Tendsto (fun L : ℕ => (((∑ v ∈ winRange (L : ℤ) 0 B.scale ∪
      winRange (L : ℤ) (-1) B.scale, tileCutoff η B.scale v x : ℝ)) : ℂ) * h B x) atTop (𝓝 (h B x)) := by
    intro x
    have h2 : Tendsto (fun L : ℕ => ∑ v ∈ winRange (L : ℤ) 0 B.scale ∪ winRange (L : ℤ) (-1) B.scale,
        tileCutoff η B.scale v x) atTop (𝓝 1) :=
      (hasSum_tileCutoff hη hint h1 B.scale x).comp (tendsto_winRange B.scale)
    have h3 := (Complex.continuous_ofReal.tendsto 1).comp h2
    have h4 := h3.mul_const (h B x)
    simpa using h4
  have := tendsto_integral_of_dominated_convergence (fun x => ‖h B x‖) hmeas (hh B hB).norm
    (fun L => Filter.Eventually.of_forall fun x => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h0 : 0 ≤ ∑ v ∈ winRange (L : ℤ) 0 B.scale ∪ winRange (L : ℤ) (-1) B.scale,
          tileCutoff η B.scale v x := Finset.sum_nonneg fun v _ => tileCutoff_nonneg hnn _ v x
      rw [abs_of_nonneg h0]
      exact mul_le_of_le_one_left (norm_nonneg _) (sum_tileCutoff_le_one hη hint hnn h1 _ x _))
    (Filter.Eventually.of_forall hlim)
  exact this

end PrimeBHT.TimeFrequency.X2.Disc
