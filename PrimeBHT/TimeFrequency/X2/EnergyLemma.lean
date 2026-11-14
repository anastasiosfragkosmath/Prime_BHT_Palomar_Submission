module

public import PrimeBHT.TimeFrequency.X2.EnergyLemma.Select
public import PrimeBHT.TimeFrequency.X2.EnergyLemma.Count

/-!
# X2, node V12: the energy lemma (global count B6 and localized count B6')

`energyLemma (hpint : PintStatement) (hB5 : EngBoundStatement) : EnergyLemmaStatementR`.

## What is proved

The greedy selection of `Select.lean` (three phases: tiles on the right / on the left of the top frequency, and the
single-box rest; maximal trees `maxTree` of the current residual removed one at a time, each round removes at least
one tile), the halving `eng ≤ θ + θ + θ = λ/2`, and the count by `pint` (DPLMV L1347-1366): global (class `𝔭`) and
localized (class `𝔭.loc`, applied to `g = F / p_W` through `treeOp_locPoly`, tops independent of `W`).

## Corrections of `EnergyLemmaStatement` (all forced; see the handoff report)

1. **`IsStronglyDisjoint` (V10, built) is not what a selection produces.**  It requires, for tiles `R ∈ T`, `R' ∈ T'`
   with `R.scale ≤ R'.scale` (EQUAL scales included) and `10`-close frequency intervals, `I_R ∩ I_{T'} = ∅`, in both
   orders.  For two trees with a tile of the SAME box and nested tops (the top of the later tree contains a tile of the
   earlier one) this fails for either order of the pair; the greedy selection can only avoid it by a time-ordering,
   which conflicts with the frequency ordering that the nested pairs need (DPLMV's `ℓ(ω_P) ≤ ℓ(ω_{P'})` should be `<`;
   HLC `eq:disjProp` and MTT2 use `ω_P ⊊ ω_{P'}`).  Moreover `10`-closeness without nesting is not controlled by
   the removal of a maximal tree.  `IsStronglyDisjointN` (`Defs.lean`) is the nested form (distinct boxes, `ω_k`
   strictly nested); `selection` produces it with NO extra hypothesis beyond `IsRankOne` fields (a), (b), (f), (h)
   and `J ≥ 16`.  `PintStatement` is stated for it.  The built `pint_two` is for the old predicate: `energyLemma_two`
   is conditional on its nested-form version `PintStatementFor HilbertExp`.
2. **The class margin** is `(𝔭.loc.decN 10).Admissible` instead of `𝔭.loc.Admissible`: the localized count applies
   `pint` in the class `𝔭.loc`, and `pint_two` costs `10` orders of decay (`EnergyLemmaStatementR`).
3. **B5 is an input** (`EngBoundStatement`, the consequence `eng ≲ ‖F‖_∞` of `EngLeTailMassStatement`, bridge
   `engBound_of_B5`): the count needs `λ ≲ 1` (DPLMV L1363-1366); it does not follow from `pint`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

theorem IsEnergyExponent.one_le_s {s qX : ℝ} (h : IsEnergyExponent s qX) : 1 ≤ s := by
  rcases h with ⟨h1, -⟩ | ⟨h1, -, -⟩
  · rw [h1]; norm_num
  · exact h1.le

theorem IsEnergyExponent.one_le_qX {s qX : ℝ} (h : IsEnergyExponent s qX) : 1 ≤ qX := by
  rcases h with ⟨-, h2⟩ | ⟨h1, h2, -⟩
  · rw [h2]; norm_num
  · linarith

end PrimeBHT.TimeFrequency.X2
