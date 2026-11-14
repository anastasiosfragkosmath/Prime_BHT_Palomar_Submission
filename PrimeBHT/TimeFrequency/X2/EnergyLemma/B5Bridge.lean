module

public import PrimeBHT.TimeFrequency.X2.EnergyLemma.Defs
public import PrimeBHT.TimeFrequency.X2.V16.Hyps

/-!
# X2, node V12: `EngBoundStatement` from B5

`engBound_of_B5`: the bound `eng ≲ 1` used by the energy lemma follows from the tail-aware bound B5
(`EngLeTailMassStatement`, at `q = qX`, `M = 3`) because `λ_M(‖F‖; I) ≤ C_M` for `‖F‖ ≤ 1`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

theorem IsEnergyExponent.one_lt_s' {s qX : ℝ} (h : IsEnergyExponent s qX) : 1 < s := by
  rcases h with ⟨h1, -⟩ | ⟨h1, -, -⟩
  · rw [h1]; norm_num
  · exact h1

theorem IsEnergyExponent.two_le_qX {s qX : ℝ} (h : IsEnergyExponent s qX) : 2 ≤ qX := by
  rcases h with ⟨-, h2⟩ | ⟨h1, h2, h3⟩
  · rw [h2]
  · rcases lt_or_ge s 2 with hs | hs
    · have : 2 < s / (s - 1) := by
        rw [lt_div_iff₀ (by linarith)]; linarith
      linarith
    · linarith

end PrimeBHT.TimeFrequency.X2
