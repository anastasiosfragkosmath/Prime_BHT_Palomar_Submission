module

public import PrimeBHT.TimeFrequency.X2.V16.Defs
public import PrimeBHT.TimeFrequency.X2.V16.Count
public import PrimeBHT.TimeFrequency.X2.V16.Main
public import PrimeBHT.TimeFrequency.X2.GoodTree
public import PrimeBHT.TimeFrequency.X2.Energy
public import PrimeBHT.TimeFrequency.X2.ClassLemmas
public import PrimeBHT.TimeFrequency.X2.EnergyTop
public import PrimeBHT.TimeFrequency.X2.Basic
public import PrimeBHT.Lift

/-!
# X2, node V16: the abstract hypotheses of B10, B11, B12, and the interface facts they need

The V16 assembly (`V16/Outside.lean` = B10, `V16/Inside.lean` = B11, `V16/HullBound.lean` = B12) is CONDITIONAL on the
three nodes B5 (tail-aware energy bound), V12 (energy lemma, halving step with global and localized count) and V15
(tree lemma).  Their CONCRETE shapes are under revision (V13 route check, repair R1: the energies get a top-term part
`engTop`, the tree class is `𝔭.tree`), so the assembly is developed GENERIC in an abstract energy family

  `e : EnergyFamily`,  `e P h v Cs : ℝ≥0∞`   (the energy of slot `v` of the test functions `h` on the collection `Cs`),

and the three hypotheses are abstract `Prop`s over `e`, exactly in the shape that `main_estimate` consumes:

* `EnergyMono e`: `e` is monotone in the collection;
* `EnergyTailBound e ints u 𝔭 M` (B5): `e h v Cs ≤ C sup_{W ∈ ints Cs} λ_M(‖h_v‖; W)` (`ints` = tile intervals, REV2: plus tops);
* `EnergyStep e u 𝔭` (V12): one halving step by removing maximal trees, with the global count and the localized count B6';
* `EnergyTree e u 𝔭` (V15): the tree bound `‖Λ_Tr‖ ≤ C CT |I_t| ∏_k e_k(Tr)` on good trees.

Instantiating them with the concrete energies of the final V09/V12/V15 statements (whatever their shape) gives B10-B12.

This file also contains the elementary interface facts about the BUILT definitions (`removeTrees`, `removedTrees`,
`maxTree`, `IsModelData`, `IsGoodTree`, `yNorm`, `locPoly`, the margins of `V16Params`) that the assembly (and the
instantiation) needs.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

theorem slotExp_pos {u : ℝ} (hu : 1 < u) (v : Fin 3) : 0 < slotExp u v := by
  unfold slotExp; split_ifs <;> linarith

/-! ## The energy exponents `(2, 2, R)` and the abstract energy family -/

/-- The energy exponents `q_X = (2, 2, R)` of the three slots (`= qv`). -/
abbrev qX (R : ℝ) (v : Fin 3) : ℝ := qv R v

/-- An energy family: for each `P` and test functions `h`, the energy `e P h v Cs` of the slot `v` on the collection `Cs`. -/
abbrev EnergyFamily : Type :=
  ∀ (P : ℕ) [NeZero P], (Fin 3 → ℝ → ZMod P → ℂ) → Fin 3 → Finset TriTile → ℝ≥0∞

/-- Energies are monotone in the collection (DPLMV: sup over sub-trees). -/
def EnergyMono (e : EnergyFamily) : Prop :=
  ∀ (P : ℕ) [NeZero P] (h : Fin 3 → ℝ → ZMod P → ℂ) (v : Fin 3) {S S' : Finset TriTile},
    S ⊆ S' → e P h v S ≤ e P h v S'

/-- A family of admissible dyadic intervals `ints Cs ⊆ ℤ × ℤ` (keys of `dyadicInt`) attached to a collection: the
intervals at which the tail masses of B5 are taken.  For the printed B5 (`eng`) these are the tile intervals
(`tileInts`); for the top-term energy of REV2 they also contain the top intervals `W`. -/
abbrev IntFamily : Type := Finset TriTile → Set (ℤ × ℤ)

/-- The tile intervals `I_R = dyadicInt R.box.scale R.pos`, `R ∈ Cs`. -/
def tileInts : IntFamily := fun Cs => {W | ∃ R ∈ Cs, W = (R.box.scale, R.pos)}

/-- Structural property used by B10: every admissible interval contains the interval of a tile of the collection. -/
def IntsContain (ints : IntFamily) : Prop :=
  ∀ (Cs : Finset TriTile) (W : ℤ × ℤ), W ∈ ints Cs → ∃ R ∈ Cs, R.I ⊆ dyadicInt W.1 W.2

/-- Structural property used by B11: for a collection of tiles of ONE scale, every admissible interval is a tile
interval.  REV3: used for B11 with the TILE family `tileInts` only (the sandwich-free top intervals `fullInts` do NOT satisfy
it: a top interval far above a layer sees the whole exceptional slot). -/
def IntsScale (ints : IntFamily) : Prop :=
  ∀ (L : Finset TriTile) (s₀ : ℤ), (∀ R ∈ L, R.box.scale = s₀) →
    ∀ W ∈ ints L, ∃ R ∈ L, W = (R.box.scale, R.pos)

theorem tileInts_scale : IntsScale tileInts := by
  rintro L s₀ - W ⟨R, hR, rfl⟩
  exact ⟨R, hR, rfl⟩

/-- **B5 (tail-aware energy bound)**, abstract form: `e_v(Cs) ≤ C sup_{W ∈ ints Cs} λ_M(yNorm_{s_v} ∘ h_v; W)` for
test functions with `yNorm_{s_v} (h_v) ≤ 1`, boxes of a rank-1 set. -/
def EnergyTailBound (e : EnergyFamily) (ints : IntFamily) (u : ℝ) (𝔭 : Params) (M : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (Qs : Set Box), IsRankOne 𝔭.J Qs →
    ∀ (Cs : Finset TriTile), (∀ R ∈ Cs, R.box ∈ Qs) → ∀ (h : Fin 3 → ℝ → ZMod P → ℂ),
      (∀ i, Measurable (h i)) → (∀ v x, yNorm (slotExp u v) (h v x) ≤ 1) → ∀ v : Fin 3,
        e P h v Cs ≤ ENNReal.ofReal C *
          ⨆ W ∈ ints Cs, ENNReal.ofReal
            (V16.tailMass M (fun y => yNorm (slotExp u v) (h v y)) (dyadicInt W.1 W.2))

/-- **V12 (energy lemma, global and localized)**, abstract form, at the count exponent `q⁺ = (1 + η) q_X`
(`qPlus`): in a residual `Cs` of a TC base, there are tops `ts` such that removing the maximal trees halves the
energy, and `(Σ|I_t|) e^{q⁺} ≤ C ‖h_v‖_{q_X}^{q_X}` (global) resp. `≤ C ‖h_v/p_W‖_{q_X}^{q_X}` (localized to every
dyadic `W ⊇ ⋃ I_R`). -/
def EnergyStep (e : EnergyFamily) (u : ℝ) (𝔭 : Params) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (Qs : Set Box), IsRankOne 𝔭.J Qs →
    ∀ (Cs₀ Cs : Finset TriTile), (∀ R ∈ Cs₀, R.box ∈ Qs) → HasTC Cs₀ → IsResidual Cs₀ Cs →
    ∀ (h : Fin 3 → ℝ → ZMod P → ℂ), (∀ i, Measurable (h i)) → (∀ v x, yNorm (slotExp u v) (h v x) ≤ 1) →
    ∀ v : Fin 3, ∃ ts : List Top,
      e P h v (removeTrees Cs ts) ≤ e P h v Cs / 2 ∧
      topSum (removedTrees Cs ts) * e P h v Cs ^ V16.qPlus (Rof u) v ≤
        ENNReal.ofReal C * mixedPow (qX (Rof u) v) (slotExp u v) (h v) ∧
      ∀ W : ℤ × ℤ, (∀ R ∈ Cs, R.I ⊆ dyadicInt W.1 W.2) →
        topSum (removedTrees Cs ts) * e P h v Cs ^ V16.qPlus (Rof u) v ≤
          ENNReal.ofReal C * mixedPow (qX (Rof u) v) (slotExp u v) (fun x => ((locPoly W x)⁻¹ : ℂ) • h v x)

/-- **V15 (tree lemma)**, abstract form, for the good trees satisfying the side condition `A` (REV3): on a GOOD tree `Tr`
with top `t` and `A Tr`, `‖Λ_Tr‖ ≤ C CT |I_t| ∏_k e_k(Tr)`.  `A = True` is the tree lemma V15 (outside part B10), `A =
SingleScale` the single-scale tree lemma V15s (inside layers B11). -/
def EnergyTreeA (A : Finset TriTile → Prop) (e : EnergyFamily) (u : ℝ) (𝔭 : Params) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (T : Form P) (CT : ℝ), FormBound u T CT →
    ∀ (Qs : Set Box), IsRankOne 𝔭.J Qs → ∀ (Tr : Finset TriTile) (t : Top), IsGoodTree Tr t → A Tr →
      (∀ R ∈ Tr, R.box ∈ Qs) → ∀ (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ),
        IsModelData 𝔭 Tr χ m → ∀ (h : Fin 3 → ℝ → ZMod P → ℂ), (∀ i, Measurable (h i)) →
          (∀ v x, yNorm (slotExp u v) (h v x) ≤ 1) →
            ‖modelForm T Tr χ m (h 0) (h 1) (h 2)‖ₑ ≤
              ENNReal.ofReal (C * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) * ∏ k, e P h k Tr

/-- **V15 (tree lemma)**, abstract form: on a GOOD tree `Tr` with top `t`, `‖Λ_Tr‖ ≤ C CT |I_t| ∏_k e_k(Tr)`. -/
def EnergyTree (e : EnergyFamily) (u : ℝ) (𝔭 : Params) : Prop :=
  EnergyTreeA (fun _ => True) e u 𝔭

/-- All tiles of `S` have the same scale (a single-scale collection: a layer, REV3). -/
def SingleScale (S : Finset TriTile) : Prop := ∃ s₀ : ℤ, ∀ R ∈ S, R.box.scale = s₀

theorem SingleScale.mono {S S' : Finset TriTile} (h : S' ⊆ S) (hS : SingleScale S) : SingleScale S' := by
  obtain ⟨s₀, hs⟩ := hS
  exact ⟨s₀, fun R hR => hs R (h hR)⟩

/-- **V15s (single-scale tree lemma)**, abstract form (REV3): the tree bound for GOOD trees of ONE scale (a single box). -/
def EnergyTreeSS (e : EnergyFamily) (u : ℝ) (𝔭 : Params) : Prop :=
  EnergyTreeA SingleScale e u 𝔭

/-! ## The concrete hypotheses (REV2) -/

/-- **V15 = tree lemma, REV2/REV3** (`docs/audits/X2-V13-route-check.md` §1.1/§1.3): `q = (2, 2, R)`, energies `engV`
in the class `𝔭.tree` (REV3: `engTop` is the energy of the FAT top data, `IsTopDatum`). -/
def TreeLemmaStatementRev2 : Prop :=
  ∀ (𝔭 : Params), 𝔭.Admissible → 𝔭.tree.Admissible → ProfileOK 𝔭 → ∀ {u R : ℝ}, 1 < u → 2 < R →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (T : Form P) (CT : ℝ), FormBound u T CT →
      ∀ (Qs : Set Box), IsRankOne 𝔭.J Qs → ∀ (Tr : Finset TriTile) (t : Top), IsGoodTree Tr t →
        (∀ R' ∈ Tr, R'.box ∈ Qs) → ∀ (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ),
          IsModelData 𝔭 Tr χ m → ∀ F : Fin 3 → ℝ → ZMod P → ℂ, (∀ k, Measurable (F k)) →
            (∀ k, ∃ B, ∀ x, yNorm 2 (F k x) ≤ B) →
              ‖modelForm T Tr χ m (F 0) (F 1) (F 2)‖ₑ ≤
                ENNReal.ofReal (C * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) * ∏ k, engV 𝔭 u R k (F k) Tr

/-! ## Removed trees -/

theorem maxTree_subset (S : Finset TriTile) (W : ℤ × ℤ) (ξ : ℝ) : maxTree S W ξ ⊆ S :=
  fun _ hR => (mem_maxTree.1 hR).1

/-- The residual after removing the maximal trees `removedTrees S ts` is `S` minus their union. -/
theorem removeTrees_eq_sdiff (S : Finset TriTile) (ts : List Top) :
    removeTrees S ts = S \ ((removedTrees S ts).map Prod.fst).foldr (· ∪ ·) ∅ := by
  induction ts generalizing S with
  | nil => simp [removeTrees, removedTrees]
  | cons t ts ih =>
    have h1 : removeTrees S (t :: ts) = removeTrees (S \ maxTree S t.1 t.2) ts := rfl
    rw [h1, ih, removedTrees]
    simp only [List.map_cons, List.foldr_cons]
    rw [sdiff_sdiff_left]
    rfl

/-- Each removed tree is a maximal tree of an intermediate residual. -/
theorem removedTrees_spec (S : Finset TriTile) (ts : List Top) :
    ∀ T ∈ removedTrees S ts, ∃ ts₀ : List Top, T.1 = maxTree (removeTrees S ts₀) T.2.1 T.2.2 := by
  induction ts generalizing S with
  | nil => intro T hT; simp [removedTrees] at hT
  | cons t ts ih =>
    intro T hT
    rw [removedTrees, List.mem_cons] at hT
    rcases hT with rfl | hT
    · exact ⟨[], rfl⟩
    · obtain ⟨ts₀, h⟩ := ih _ T hT
      exact ⟨t :: ts₀, h⟩

theorem removedTrees_subset (S : Finset TriTile) (ts : List Top) :
    ∀ T ∈ removedTrees S ts, T.1 ⊆ S := by
  intro T hT
  obtain ⟨ts₀, h⟩ := removedTrees_spec S ts T hT
  rw [h]
  exact (maxTree_subset _ _ _).trans (removeTrees_subset S ts₀)

theorem removedTrees_pairwise (S : Finset TriTile) (ts : List Top) :
    (removedTrees S ts).Pairwise (fun T T' => Disjoint T.1 T'.1) := by
  induction ts generalizing S with
  | nil => simp [removedTrees]
  | cons t ts ih =>
    rw [removedTrees, List.pairwise_cons]
    refine ⟨fun T' hT' => ?_, ih _⟩
    exact Finset.disjoint_of_subset_right (removedTrees_subset _ _ T' hT') Finset.disjoint_sdiff

/-- The residuals of a base are subsets of the base. -/
theorem IsResidual.subset {Cs₀ Cs : Finset TriTile} (h : IsResidual Cs₀ Cs) : Cs ⊆ Cs₀ := by
  obtain ⟨ts, rfl⟩ := h
  exact removeTrees_subset _ _

/-! ## Model data, one-tile trees -/

theorem IsModelData.mono {𝔭 : Params} {Ps Ps' : Finset TriTile} {χ : TriTile → ℝ → ℝ}
    {m : TriTile → Fin 3 → ℝ → ℂ} (h : IsModelData 𝔭 Ps χ m) (hsub : Ps' ⊆ Ps) :
    IsModelData 𝔭 Ps' χ m :=
  ⟨fun Q hQ => h.1 Q (hsub hQ), fun Q hQ Q' hQ' => h.2.1 Q (hsub hQ) Q' (hsub hQ'),
    let ⟨η, hη, hχ⟩ := h.2.2; ⟨η, hη, fun Q hQ => hχ Q (hsub hQ)⟩⟩

theorem Box.exists_mem_hull (B : Box) : ∃ ξ, ξ ∈ B.hull := by
  have hw : 0 < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
  have hD : 0 < hullDil := by unfold hullDil; norm_num
  refine ⟨(B.centre 0 - hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir 0, ?_, ?_⟩
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · refine le_trans ?_ ((le_max_left _ _).trans (le_max_left _ _))
    have : freqDir 0 = 1 := by simp [freqDir]
    rw [this]
    nlinarith

/-- A single tile is a good tree (with the top its own interval). -/
theorem isGoodTree_singleton (R : TriTile) :
    ∃ t : Top, t.1 = (R.box.scale, R.pos) ∧ IsGoodTree {R} t := by
  obtain ⟨ξ, hξ⟩ := Box.exists_mem_hull R.box
  refine ⟨((R.box.scale, R.pos), ξ), rfl, ?_, ?_, ?_⟩
  · intro R' hR'
    rw [Finset.mem_singleton] at hR'
    subst hR'
    exact ⟨Set.Subset.rfl, hξ⟩
  · intro R₁ h₁ R₂ h₂ _
    rw [Finset.mem_singleton] at h₁ h₂
    rw [h₁, h₂]
  · intro R₁ h₁ R₂ h₂ _
    rw [Finset.mem_singleton] at h₁ h₂
    rw [h₁, h₂]


/-! ## `yNorm` facts -/

theorem yNorm_nonneg' {P : ℕ} [NeZero P] (s : ℝ) (F : ZMod P → ℂ) : 0 ≤ yNorm s F :=
  PrimeBHT.Lift.yNorm_nonneg s F

theorem yNorm_smul {P : ℕ} [NeZero P] {s : ℝ} (hs : 0 < s) (c : ℂ) (F : ZMod P → ℂ) :
    yNorm s (c • F) = ‖c‖ * yNorm s F := by
  unfold yNorm
  have h1 : ∀ y, ‖(c • F) y‖ ^ s = ‖c‖ ^ s * ‖F y‖ ^ s := fun y => by
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  simp_rw [h1, ← Finset.mul_sum]
  rw [mul_left_comm, Real.mul_rpow (by positivity) (PrimeBHT.Lift.avg_rpow_nonneg s F),
    Real.rpow_rpow_inv (norm_nonneg _) hs.ne']

/-- A function with `yNorm u ≤ 1` has a bounded `yNorm 2` (the bound depends on `P` and `u`). -/
theorem exists_yNorm_two_le (P : ℕ) [NeZero P] {u : ℝ} (hu : 0 < u) :
    ∃ B : ℝ, ∀ F : ZMod P → ℂ, yNorm u F ≤ 1 → yNorm 2 F ≤ B := by
  have hPpos : (0 : ℝ) < P := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P)
  refine ⟨(P : ℝ) ^ u⁻¹, fun F hF => ?_⟩
  have hM : 0 ≤ (P : ℝ) ^ u⁻¹ := Real.rpow_nonneg hPpos.le _
  have h1 : ∀ y, ‖F y‖ ≤ (P : ℝ) ^ u⁻¹ := by
    intro y
    have h2 : ‖F y‖ ^ u ≤ ∑ z, ‖F z‖ ^ u :=
      Finset.single_le_sum (f := fun z => ‖F z‖ ^ u) (fun z _ => Real.rpow_nonneg (norm_nonneg _) _)
        (Finset.mem_univ y)
    have h3 : yNorm u F ^ u = (P : ℝ)⁻¹ * ∑ z, ‖F z‖ ^ u :=
      PrimeBHT.Lift.yNorm_rpow_self hu.ne' F
    have h4 : yNorm u F ^ u ≤ 1 := by
      calc yNorm u F ^ u ≤ 1 ^ u :=
            Real.rpow_le_rpow (PrimeBHT.Lift.yNorm_nonneg u F) hF hu.le
        _ = 1 := Real.one_rpow u
    have h5 : ∑ z, ‖F z‖ ^ u ≤ P := by
      rw [h3] at h4
      rw [inv_mul_le_iff₀ hPpos] at h4
      linarith
    calc ‖F y‖ = (‖F y‖ ^ u) ^ u⁻¹ := (Real.rpow_rpow_inv (norm_nonneg _) hu.ne').symm
      _ ≤ (P : ℝ) ^ u⁻¹ :=
          Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) (h2.trans h5) (inv_nonneg.2 hu.le)
  exact (PrimeBHT.Lift.yNorm_le_yNormInf (by norm_num) F).trans (PrimeBHT.Lift.yNormInf_le hM h1)

/-! ## The energy exponents `(2, 2, R)` -/

theorem qPlus_eq (R : ℝ) (v : Fin 3) : V16.qPlus R v = qX R v * (1 + V16.etaR R) := by
  unfold V16.qPlus
  simp only [qX, qv]
  split_ifs <;> ring

theorem two_le_qX {R : ℝ} (hR : 4 ≤ R) (v : Fin 3) : 2 ≤ qX R v := by
  unfold qX qv; split_ifs <;> linarith

theorem isEnergyExponent_slot {u : ℝ} (hu : 1 < u) (v : Fin 3) :
    IsEnergyExponent (slotExp u v) (qX (Rof u) v) := by
  fin_cases v
  · exact Or.inl ⟨by simp [slotExp], by simp [qX, qv]⟩
  · exact Or.inl ⟨by simp [slotExp], by simp [qX, qv]⟩
  · right
    have hu1 : 0 < u - 1 := by linarith
    have hu' : 0 < u / (u - 1) := by positivity
    have h1 : u ≤ max u (u / (u - 1)) := le_max_left _ _
    have h2 : u / (u - 1) ≤ max u (u / (u - 1)) := le_max_right _ _
    simp only [slotExp, qX, qv, Rof]
    simp only [Fin.reduceFinMk, ↓reduceIte]
    refine ⟨hu, by linarith, by linarith⟩

/-- `q⁺_v = (1 + η) q_X,v > q_X,v`. -/
theorem qX_lt_qPlus {R : ℝ} (hR : 4 ≤ R) (v : Fin 3) : qX R v < V16.qPlus R v := by
  rw [qPlus_eq]
  have h2 := two_le_qX hR v
  have hη : 0 < V16.etaR R := by unfold V16.etaR; positivity
  nlinarith

/-! ## The margins of `V16Params` (REV2: the energy class is `𝔭.tree`, `N/8`) -/

theorem V16Params.tree_loc_admissible {u : ℝ} {𝔭 : Params} (h : V16Params u 𝔭) :
    𝔭.tree.loc.Admissible ∧ 𝔭.tree.Admissible := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, hN, hD, -⟩ := h
  have hN8 : classFloor + 2 * locLoss ≤ 𝔭.N / 8 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    unfold v16Decay at hN; omega
  have hD' : classFloor + 2 * locLoss ≤ 𝔭.D := by
    unfold v16Decay at hD; omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    simp only [Params.loc_J, Params.loc_N, Params.loc_D, Params.loc_δ, Params.loc_β, Params.loc_C,
      Params.tree_J, Params.tree_N, Params.tree_D, Params.tree_δ, Params.tree_β, Params.tree_C] <;>
    first | assumption | omega

theorem V16Params.profileOK {u : ℝ} {𝔭 : Params} (h : V16Params u 𝔭) : ProfileOK 𝔭 := h.2.2.2

/-- B5 at the tail order `M = 33 R + 2` of B11 in the class `𝔭.tree`: `M + 100 ≤ (𝔭.tree).N`. -/
theorem V16Params.tail_decay {u : ℝ} {𝔭 : Params} (h : V16Params u 𝔭) :
    (33 * Rof u + 2) + 100 ≤ ((𝔭.tree.N : ℕ) : ℝ) := by
  obtain ⟨-, hN, -⟩ := h
  have hN8 : classFloor + 2 * locLoss + ⌈33 * Rof u⌉₊ + 2 ≤ 𝔭.N / 8 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]; unfold v16Decay at hN; omega
  have h1 : (33 * Rof u : ℝ) ≤ ⌈33 * Rof u⌉₊ := Nat.le_ceil _
  have h2 : ((classFloor + 2 * locLoss + ⌈33 * Rof u⌉₊ + 2 : ℕ) : ℝ) ≤ ((𝔭.N / 8 : ℕ) : ℝ) := by
    exact_mod_cast hN8
  simp only [Params.tree_N]
  push_cast at h2
  have h4 : (400 : ℝ) ≤ classFloor := by exact_mod_cast classFloor_ge
  have h5 : (locLoss : ℝ) = 100 := by simp [locLoss]
  linarith

/-! ## The single-scale tree lemma V15s (REV3) -/

/-- **V15s: the tree lemma for single-scale good trees with TILE energies only** (class `𝔭.tree`, exponents `(2, 2, R)`).
A single-scale good tree is a single box (`IsTree.box_eq_of_scale_eq`), so its form is `∫ (Σ_R χ_R) Π(T F₀, T F₁, T F₂)`;
the proof is Hölder in `(2, 2, ∞)` plus the single-scale `L^∞` bound (Bernstein) of V13 (S); no projections, no top operators
(`docs/audits/X2-REV3-fat-top.md` §3).  UNVERIFIED (about 0.3-0.5k lines). -/
def TreeLemmaSingleScaleStatement : Prop :=
  ∀ (𝔭 : Params), 𝔭.Admissible → 𝔭.tree.Admissible → ∀ {u R : ℝ}, 1 < u → 2 < R →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (T : Form P) (CT : ℝ), FormBound u T CT →
      ∀ (Qs : Set Box), IsRankOne 𝔭.J Qs → ∀ (Tr : Finset TriTile) (t : Top), IsGoodTree Tr t →
        SingleScale Tr → (∀ R' ∈ Tr, R'.box ∈ Qs) →
        ∀ (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ),
          IsModelData 𝔭 Tr χ m → ∀ F : Fin 3 → ℝ → ZMod P → ℂ, (∀ k, Measurable (F k)) →
            (∀ k, ∃ B, ∀ x, yNorm 2 (F k x) ≤ B) →
              ‖modelForm T Tr χ m (F 0) (F 1) (F 2)‖ₑ ≤
                ENNReal.ofReal (C * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) *
                  ∏ k, eng 𝔭.tree (slotExp u k) k (F k) Tr (qv R k)

end PrimeBHT.TimeFrequency.X2
