module

public import PrimeBHT.TimeFrequency.X2.TopEnergy.Main
public import PrimeBHT.TimeFrequency.X2.EnergyTop
public import PrimeBHT.TimeFrequency.X2.EnergyLemma.Defs

/-!
# X2, node V12-top: the halving step of `engV` WITHOUT the localized count, and the glue to the other slot

`engV_stepG`: the global part of `engV_stepR` (halving of `engV = max (eng, engTop)` and the global count), from the repaired
V12 for `eng` (`EnergyLemmaStatementR`, global conjuncts only used) and the GLOBAL top statement.  The localized conjunct of
`engV_step` is FALSE for `engTop` (report), and B10 (`Outside.lean`) discards it, so the outside family needs
exactly this statement.

`EnergyLemmaTopGStatement := EnergyLemmaTopGStatementFor IsEnergyExponent` and `energyLemmaTopG_of_two`: the full
global top statement follows from the Hilbert case (`energyLemmaTopG_two`, proved) and the non-Hilbert case
`EnergyLemmaTopGStatementFor NonHilbertExp` (TB-4: `s ≠ 2`, slot 3).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- The global top statement for all energy exponents. -/
def EnergyLemmaTopGStatement : Prop := EnergyLemmaTopGStatementFor IsEnergyExponent

/-- The non-Hilbert energy exponents `1 < s < qX`, `s/(s-1) < qX` (TB-4). -/
def NonHilbertExp (s qX : ℝ) : Prop := 1 < s ∧ s < qX ∧ s / (s - 1) < qX

theorem EnergyLemmaTopGStatementFor.of_union {E₁ E₂ E : ℝ → ℝ → Prop} (h₁ : EnergyLemmaTopGStatementFor E₁)
    (h₂ : EnergyLemmaTopGStatementFor E₂) (hE : ∀ s qX, E s qX → E₁ s qX ∨ E₂ s qX) :
    EnergyLemmaTopGStatementFor E := by
  intro 𝔭 h𝔭 s qX q hX hq
  rcases hE s qX hX with h | h
  · exact h₁ 𝔭 h𝔭 h hq
  · exact h₂ 𝔭 h𝔭 h hq

/-- **The global top statement from the Hilbert case and TB-4.** -/
theorem energyLemmaTopG_of_two (h : EnergyLemmaTopGStatementFor NonHilbertExp) : EnergyLemmaTopGStatement :=
  EnergyLemmaTopGStatementFor.of_union energyLemmaTopG_two h fun s qX hX => by
    rcases hX with hX | hX
    · exact Or.inl hX
    · exact Or.inr hX

/-- **`engV_stepG`**: the halving step of `engV` with the GLOBAL count only. -/
theorem engV_stepG (hV12 : EnergyLemmaStatementR) (hV12t : EnergyLemmaTopGStatement) (𝔭 : Params)
    (h𝔭 : (𝔭.tree.loc.decN 10).Admissible) {u R : ℝ} (k : Fin 3)
    (hX : IsEnergyExponent (slotExp u k) (qv R k)) {q : ℝ} (hq : qv R k < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (Qs : Set Box), IsRankOne 𝔭.J Qs →
      ∀ (Cs₀ Cs : Finset TriTile), (∀ R' ∈ Cs₀, R'.box ∈ Qs) → HasTC Cs₀ → IsResidual Cs₀ Cs →
        ∀ (F : ℝ → ZMod P → ℂ), Measurable F → (∀ x, yNorm (slotExp u k) (F x) ≤ 1) →
          ∃ ts : List Top,
            engV 𝔭 u R k F (removeTrees Cs ts) ≤ engV 𝔭 u R k F Cs / 2 ∧
            topSum (removedTrees Cs ts) * engV 𝔭 u R k F Cs ^ q ≤
              ENNReal.ofReal C * mixedPow (qv R k) (slotExp u k) F := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := hV12 𝔭.tree h𝔭 hX hq
  obtain ⟨C₂, hC₂0, hC₂⟩ := hV12t 𝔭.tree (Params.Admissible.of_loc_decN h𝔭).1 hX hq
  have hqv0 : 0 < qv R k := by
    rcases hX with ⟨-, h2⟩ | ⟨h1, h2, -⟩
    · rw [h2]; norm_num
    · linarith
  have hq0 : 0 ≤ q := by linarith
  refine ⟨2 ^ q * (C₁ + C₂), mul_nonneg (by positivity) (by linarith), ?_⟩
  intro P _ Qs hQ Cs₀ Cs hbox hTC hres F hFm hbd
  let Cond : Unit → Finset TriTile → Prop := fun _ _ => True
  have hCond : ∀ i S S', S' ⊆ S → Cond i S → Cond i S' := fun _ _ _ _ _ => trivial
  have st₁ : ∀ S, IsResidual Cs₀ S → ∃ ts : List Top,
      eng 𝔭.tree (slotExp u k) k F (removeTrees S ts) (qv R k) ≤
        eng 𝔭.tree (slotExp u k) k F S (qv R k) / 2 ∧
      ∀ i, Cond i S → topSum (removedTrees S ts) * eng 𝔭.tree (slotExp u k) k F S (qv R k) ^ q ≤
        ENNReal.ofReal C₁ * mixedPow (qv R k) (slotExp u k) F := by
    intro S hS
    obtain ⟨ts, ha, hb, -⟩ := hC₁ P Qs hQ Cs₀ S hbox hTC hS k F hFm hbd
    exact ⟨ts, ha, fun _ _ => hb⟩
  have st₂ : ∀ S, IsResidual Cs₀ S → ∃ ts : List Top,
      engTop 𝔭.tree (slotExp u k) k F (removeTrees S ts) (qv R k) ≤
        engTop 𝔭.tree (slotExp u k) k F S (qv R k) / 2 ∧
      ∀ i, Cond i S → topSum (removedTrees S ts) * engTop 𝔭.tree (slotExp u k) k F S (qv R k) ^ q ≤
        ENNReal.ofReal C₂ * mixedPow (qv R k) (slotExp u k) F := by
    intro S hS
    obtain ⟨ts, ha, hb⟩ := hC₂ P Qs hQ Cs₀ S hbox hTC hS k F hFm hbd
    exact ⟨ts, ha, fun _ _ => hb⟩
  obtain ⟨ts, hh, hc⟩ := two_step (ι := Unit) Cond hCond (IsResidual Cs₀) (fun S ts hS => hS.removeTrees ts)
    (fun S => eng 𝔭.tree (slotExp u k) k F S (qv R k))
    (fun S => engTop 𝔭.tree (slotExp u k) k F S (qv R k))
    (fun S S' hSS => eng_mono _ _ _ _ hSS _) (fun S S' hSS => engTop_mono _ _ _ _ hSS _) hq0
    (fun _ => ENNReal.ofReal C₁ * mixedPow (qv R k) (slotExp u k) F)
    (fun _ => ENNReal.ofReal C₂ * mixedPow (qv R k) (slotExp u k) F) st₁ st₂ hres
  have hcoef : (2 : ℝ≥0∞) ^ q * (ENNReal.ofReal C₁ * mixedPow (qv R k) (slotExp u k) F +
      ENNReal.ofReal C₂ * mixedPow (qv R k) (slotExp u k) F) =
      ENNReal.ofReal (2 ^ q * (C₁ + C₂)) * mixedPow (qv R k) (slotExp u k) F := by
    have h2 : (2 : ℝ≥0∞) ^ q = ENNReal.ofReal ((2 : ℝ) ^ q) := by
      rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
    rw [h2, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add hC₁0 hC₂0]
    ring
  exact ⟨ts, hh, (hc () trivial).trans (le_of_eq hcoef)⟩

end PrimeBHT.TimeFrequency.X2
