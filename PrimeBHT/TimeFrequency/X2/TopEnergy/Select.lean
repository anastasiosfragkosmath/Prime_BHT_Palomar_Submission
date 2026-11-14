module

public import PrimeBHT.TimeFrequency.X2.TopEnergy.Defs

/-!
# X2, node V12-top (TB-0): the greedy selection of top data, its reflection, bookkeeping

* `resH H C ts`: the residual after removing `maxTreeH H C W ζ` for the data of `ts` in turn;
* `exists_greedy`: for a candidate predicate with FINITELY many admissible candidates, a greedy selection (maximal `ξ` first,
  `IsGreedyTopH`) exists and runs until no admissible candidate is left;
* `IsGreedyTopH.nodup`: the selected data are pairwise distinct;
* the reflected hull `Hσ σ B = {x | σ x ∈ hull B}`: `σ = -1` runs the `−`-side selection as the `+`-side one for the
  reflected data `ξ' = σ ξ` (`maxTreeH_Hσ`, `isTopDatumH_Hσ`), so `top_separation_pair_H` applies to both sides;
* `removeTrees_map_toTop`, `topSum_removedTrees_map`: the translation to the removal tops `(W, σ ξ')` of the statement.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-- The residual after removing the maximal trees of the data of `ts`, in turn. -/
def resH (H : Box → Set ℝ) : Finset TriTile → List TopSel → Finset TriTile
  | C, [] => C
  | C, V :: ts => resH H (C \ maxTreeH H C V.W V.ζ) ts

theorem resH_subset (H : Box → Set ℝ) : ∀ (ts : List TopSel) (C : Finset TriTile), resH H C ts ⊆ C
  | [], _C => subset_rfl
  | _V :: ts, _C => (resH_subset H ts _).trans Finset.sdiff_subset

/-- A datum is swallowed by its own removal. -/
theorem isTopDatumH_mem_maxTreeH {H : Box → Set ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) {J : ℕ} {C : Finset TriTile}
    {W : ℤ × ℤ} {ξ : ℝ} (h : IsTopDatumH H ρ J C W ξ) : ∃ R ∈ C, R ∈ maxTreeH H C W ξ := by
  obtain ⟨-, R, hR, h1, -, h3⟩ := h
  have ha : (0 : ℝ) < (2 : ℝ) ^ (-W.1) := zpow_pos (by norm_num) _
  exact ⟨R, hR, mem_maxTreeH.2 ⟨hR, h1, h3 ⟨by nlinarith, by nlinarith⟩⟩⟩

/-- **Existence of the greedy selection** (TB-0): finitely many admissible candidates. -/
theorem exists_greedy (H : Box → Set ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (J : ℕ) (Cand : ℤ × ℤ → ℝ → Prop) :
    ∀ (n : ℕ) (C : Finset TriTile), C.card ≤ n →
      {p : (ℤ × ℤ) × ℝ | Cand p.1 p.2 ∧ IsTopDatumH H ρ J C p.1 p.2}.Finite →
      ∃ ts : List TopSel, IsGreedyTopH H (AdmH H ρ J) Cand C ts ∧
        ∀ W ξ, Cand W ξ → ¬ IsTopDatumH H ρ J (resH H C ts) W ξ := by
  intro n
  induction n with
  | zero =>
    intro C hC hfin
    have hC0 : C = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hC)
    refine ⟨[], IsGreedyTopH.nil C, fun W ξ _ hd => ?_⟩
    obtain ⟨-, R, hR, -⟩ := hd
    simp [resH, hC0] at hR
  | succ n ih =>
    intro C hC hfin
    by_cases hne : {p : (ℤ × ℤ) × ℝ | Cand p.1 p.2 ∧ IsTopDatumH H ρ J C p.1 p.2}.Nonempty
    · set A := {p : (ℤ × ℤ) × ℝ | Cand p.1 p.2 ∧ IsTopDatumH H ρ J C p.1 p.2} with hA
      obtain ⟨p₀, hp₀⟩ := hne
      obtain ⟨⟨W, ξ⟩, hpA, hmax⟩ := Finset.exists_max_image hfin.toFinset (fun p => p.2)
        ⟨p₀, hfin.mem_toFinset.2 hp₀⟩
      have hpA' : Cand W ξ ∧ IsTopDatumH H ρ J C W ξ := hfin.mem_toFinset.1 hpA
      obtain ⟨R, hRC, hRm⟩ := isTopDatumH_mem_maxTreeH hρ hpA'.2
      have hcard : (C \ maxTreeH H C W ξ).card ≤ n := by
        have h1 : (C \ maxTreeH H C W ξ).card < C.card :=
          Finset.card_lt_card (Finset.sdiff_ssubset (Finset.filter_subset _ _) ⟨R, hRm⟩)
        omega
      have hfin' : {p : (ℤ × ℤ) × ℝ | Cand p.1 p.2 ∧
          IsTopDatumH H ρ J (C \ maxTreeH H C W ξ) p.1 p.2}.Finite :=
        hfin.subset fun p hp => ⟨hp.1, hp.2.mono Finset.sdiff_subset⟩
      obtain ⟨ts, hts, hres⟩ := ih (C \ maxTreeH H C W ξ) hcard hfin'
      refine ⟨⟨W, ξ, ξ⟩ :: ts, IsGreedyTopH.cons (ζ := ξ) ⟨rfl, hpA'.2⟩ hpA'.1 ?_ hts, hres⟩
      intro W' ξ' ζ' hc' hadm
      exact hmax (W', ξ') (hfin.mem_toFinset.2 ⟨hc', hadm.2⟩)
    · refine ⟨[], IsGreedyTopH.nil C, fun W ξ hc hd => hne ⟨(W, ξ), hc, hd⟩⟩

/-- In a greedy selection (radius `ρ ≥ 0`) the selected data are pairwise distinct. -/
theorem IsGreedyTopH.nodup {H : Box → Set ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) {J : ℕ} {Cand : ℤ × ℤ → ℝ → Prop}
    {C : Finset TriTile} {ts : List TopSel} (h : IsGreedyTopH H (AdmH H ρ J) Cand C ts) : ts.Nodup := by
  have hmono : ∀ C C' W ξ ζ, C ⊆ C' → AdmH H ρ J C W ξ ζ → AdmH H ρ J C' W ξ ζ :=
    fun C C' W ξ ζ h hd => hd.mono h
  induction h with
  | nil C => exact List.nodup_nil
  | @cons C W ξ ζ ts hadm hcand hmax htail ih =>
    refine List.nodup_cons.2 ⟨fun hmem => ?_, ih⟩
    obtain ⟨h1, -⟩ := htail.adm_cand hmono _ hmem
    -- the head datum is not admissible after its own removal
    obtain ⟨h1a, h1b⟩ := hadm
    subst h1a
    simp only at h1
    exact not_adm_after (H := H) (ρ := ρ) (J := J) (C := C) (W := W) (W' := W) (ξ := ζ) (ξ' := ζ) (ζ' := ζ)
      subset_rfl (by simpa using mul_nonneg hρ (zpow_pos (by norm_num : (0 : ℝ) < 2) (-W.1)).le) h1

/-! ## The reflected hull -/

/-- The reflected tree hull `{x | σ x ∈ hull B}`. -/
def Hσ (σ : ℝ) (B : Box) : Set ℝ := {x | σ * x ∈ B.hull}

theorem Hσ_one : Hσ 1 = Box.hull := by
  funext B; ext x; simp [Hσ]

theorem maxTreeH_Hσ {σ : ℝ} (_hσ : σ = 1 ∨ σ = -1) (C : Finset TriTile) (W : ℤ × ℤ) (ξ' : ℝ) :
    maxTreeH (Hσ σ) C W ξ' = maxTree C W (σ * ξ') := by
  unfold maxTreeH maxTree Hσ
  rfl

theorem isTopDatumH_Hσ {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {ρ : ℝ} {J : ℕ} {C : Finset TriTile} {W : ℤ × ℤ}
    {ξ' : ℝ} : IsTopDatumH (Hσ σ) ρ J C W ξ' ↔ IsTopDatumH Box.hull ρ J C W (σ * ξ') := by
  rcases hσ with rfl | rfl
  · simp [Hσ_one]
  · unfold IsTopDatumH
    constructor
    · rintro ⟨⟨z, hz⟩, R, hR, h1, h2, h3⟩
      refine ⟨⟨-z, ?_⟩, R, hR, h1, h2, fun x hx => ?_⟩
      · rw [hz]; push_cast; ring
      · have hy : -x ∈ Set.Icc (ξ' - ρ * (2 : ℝ) ^ (-W.1)) (ξ' + ρ * (2 : ℝ) ^ (-W.1)) := by
          obtain ⟨hx1, hx2⟩ := hx
          constructor <;> linarith
        have := h3 hy
        simpa [Hσ] using this
    · rintro ⟨⟨z, hz⟩, R, hR, h1, h2, h3⟩
      refine ⟨⟨-z, ?_⟩, R, hR, h1, h2, fun x hx => ?_⟩
      · have : ξ' = -1 * (-1 * ξ') := by ring
        rw [this, hz]; push_cast; ring
      · have hy : -x ∈ Set.Icc (-1 * ξ' - ρ * (2 : ℝ) ^ (-W.1)) (-1 * ξ' + ρ * (2 : ℝ) ^ (-W.1)) := by
          obtain ⟨hx1, hx2⟩ := hx
          constructor <;> linarith
        have := h3 hy
        simpa [Hσ] using this

/-- Translation of a selected datum (reflected coordinates) to the removal top of the statement. -/
def toTop (σ : ℝ) (V : TopSel) : Top := (V.W, σ * V.ζ)

theorem removeTrees_map_toTop {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∀ (ts : List TopSel) (C : Finset TriTile), removeTrees C (ts.map (toTop σ)) = resH (Hσ σ) C ts
  | [], C => rfl
  | V :: ts, C => by
    simp only [List.map_cons, removeTrees, resH, toTop, maxTreeH_Hσ hσ]
    exact removeTrees_map_toTop hσ ts _

theorem removedTrees_map_toTop {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∀ (ts : List TopSel) (C : Finset TriTile),
      topSum (removedTrees C (ts.map (toTop σ))) = (ts.map fun V => ENNReal.ofReal ((2 : ℝ) ^ V.W.1)).sum
  | [], C => by simp [removedTrees]
  | V :: ts, C => by
    simp only [List.map_cons, removedTrees, toTop, topSum_cons, List.sum_cons]
    rw [removedTrees_map_toTop hσ ts _]

end PrimeBHT.TimeFrequency.X2
