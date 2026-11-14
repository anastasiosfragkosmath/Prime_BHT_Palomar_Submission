module

public import PrimeBHT.TimeFrequency.X2.Classes
public import PrimeBHT.TimeFrequency.X2.Collections
public import PrimeBHT.TimeFrequency.X2.Interp.FormV
public import PrimeBHT.TimeFrequency.X2.V16.Exceptional
public import PrimeBHT.Frozen.YNorm

/-!
# X2, node V16: the interface definitions and the statement `V16Statement`

Statements only (definitions and the `Prop` `V16Statement`; no theorem of this file is a node proof).
Promoted from `drafts/x2-interface/{06-V16-Defs,07-V16-Count-Exceptional,09-V16-HullBound}.lean.txt`
(design doc `docs/x2-interface-design.md` §3, "V16"):

* `Rof u = 2 max(u, u')` and `four_le_Rof` (`4 ≤ Rof u` for `u > 1`, so the region lemma of `V16/Count.lean`
  applies at `R = Rof u`);
* `slotExp u k` (the exponents `(2, 2, u)` of the three slots) and `slotNorms u k = yNorm (slotExp u k)`;
* `v16Decay`, `V16Params u 𝔭` (the parameter margin required by V16, design doc §2);
* `IsHullData u E τ h` (the data of B10/B11/B12: sets, a largest index, test functions);
* `V16Statement` (the deliverable of V16, route check §1.2): `HullBound` near the corner for the model form
  of every window-full collection of a rank-1 box set, uniformly in `P, Π, Ps, χ, m, β`.  The `HullBound`
  predicate is the one of the V17 chain, `Interp.VHullBound` (`X2/Interp/FormV.lean`), for the Lebesgue measure
  on `ℝ` and the carrier `ZMod P → ℂ`; the corner region is `Interp.InCornerNbhd`.

## Deviations from the drafts

* `VDominatedBy`, `VHullBound`, `InCornerNbhd` are those of `X2.Interp` (no own copies, no `μ`-free variants);
  `VHullBound` therefore takes the measure `volume` explicitly.
* the exceptional set and the major subset are those of the built `X2/V16/Exceptional.lean`
  (`V16.exceptionalMajor`, namespace `X2.V16`); `insidePart` is that of `X2/Collections.lean`.
* `four_le_Rof` is proved here (it was a sorried restatement in the draft 07).
* `slotExp` (draft 05) is defined here, because the model-bound chain (`ModelOp`, `V17`, `Assembly`) needs the slot
  norms and nothing else of the tree-lemma draft.
-/

@[expose] public noncomputable section

open MeasureTheory
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- `R(u) = 2 max(u, u')` with `u' = u/(u-1)` (any `R > max(u, u')` works; route check §1.2). -/
def Rof (u : ℝ) : ℝ := 2 * max u (u / (u - 1))

/-- `Rof u ≥ 4` for every `u > 1` (so the hypothesis `4 ≤ R` of the region lemma `tsum_levelTerm_le_region`
always holds). -/
theorem four_le_Rof {u : ℝ} (hu : 1 < u) : 4 ≤ Rof u := by
  unfold Rof
  have hu1 : 0 < u - 1 := by linarith
  by_cases h2 : 2 ≤ u
  · have : u ≤ max u (u / (u - 1)) := le_max_left _ _
    linarith
  · push Not at h2
    have h3 : 2 ≤ u / (u - 1) := by
      rw [le_div_iff₀ hu1]; linarith
    have : u / (u - 1) ≤ max u (u / (u - 1)) := le_max_right _ _
    linarith

theorem one_le_Rof {u : ℝ} (hu : 1 < u) : 1 ≤ Rof u := by linarith [four_le_Rof hu]

/-- The exponents of the three slots of the frozen form: `(2, 2, u)`. -/
def slotExp (u : ℝ) (k : Fin 3) : ℝ := if k = 2 then u else 2

@[simp] theorem slotExp_zero (u : ℝ) : slotExp u 0 = 2 := by simp [slotExp]
@[simp] theorem slotExp_one (u : ℝ) : slotExp u 1 = 2 := by simp [slotExp]
@[simp] theorem slotExp_two (u : ℝ) : slotExp u 2 = u := by simp [slotExp]

/-- The slot norms `(yNorm 2, yNorm 2, yNorm u)` on the carrier `ZMod P → ℂ`. -/
def slotNorms {P : ℕ} [NeZero P] (u : ℝ) (k : Fin 3) : (ZMod P → ℂ) → ℝ := yNorm (slotExp u k)

/-- The parameter margin required by V16 (design doc §2): `𝔭.loc.loc` admissible (B6' inside the tree-lemma
class `𝔭.loc`) and decay `≥ 33R + 2` left in the class `𝔭.loc` for B5 at `M = 33R + 2`. -/
def v16Decay (u : ℝ) : ℕ := 8 * (classFloor + 2 * locLoss + ⌈33 * Rof u⌉₊ + 2)

/-- **The class `𝔭` carries the tree profile and the margin `N/8 + 3 ≤ D`**: (`.1`) a second profile `η'` of the energy class `𝔭.tree`
(decay order `N/8`, same `δ`, `C`) exists (`IsEtaCut 𝔭.tree η'`); (`.2`) `𝔭.N/8 + 3 ≤ 𝔭.D`: the kernels of the multipliers (`D` derivatives) decay
faster than the polynomial growth `N' = N/8` of the low-pass operators (`X2/Psp/O2*`: the outside terms (d1)-(d4) of the overlapping projection).  The tree lemma V15 needs it (the cutoffs of the energy class are built from `η'`).  It is a property of
the parameters, supplied by the discretization (`discretization_params_good`); a sufficient condition is
`Even (N/8) ∧ 2 ≤ N/8 ∧ δ ≤ 1/4 ∧ N (3N/δ)^N ≤ C` (`exists_etaCut_tree`). -/
def ProfileOK (𝔭 : Params) : Prop := (∃ η' : ℝ → ℝ, IsEtaCut 𝔭.tree η') ∧ 𝔭.N / 8 + 3 ≤ 𝔭.D

/-- Parameters admitted by V16.  REV3: the derivative margin is `v16Decay u ≤ 𝔭.D` (the corrected B5 / B5-top need
`M + 100 ≤ 𝔭.D` at `M = 33 Rof u + 2`, `X2/EngTail/Top.lean`); it is free for the discretization (`∀ N D ∃ 𝔭`).  `ProfileOK 𝔭`: the class carries the tree profile (V15). -/
def V16Params (u : ℝ) (𝔭 : Params) : Prop :=
  𝔭.Admissible ∧ v16Decay u ≤ 𝔭.N ∧ v16Decay u ≤ 𝔭.D ∧ ProfileOK 𝔭

/-- Hypotheses shared by B10, B11, B12: sets `E`, a largest index `τ`, test functions dominated by `E_v`
(`v ≠ τ`) and by the major subset `exceptionalMajor 48 E τ` (slot `τ`). -/
def IsHullData {P : ℕ} [NeZero P] (u : ℝ) (E : Fin 3 → Set ℝ) (τ : Fin 3)
    (h : Fin 3 → ℝ → ZMod P → ℂ) : Prop :=
  (∀ i, MeasurableSet (E i)) ∧ (∀ i, 0 < volume (E i)) ∧ (∀ i, volume (E i) < ⊤) ∧
    (∀ i, volume (E i) ≤ volume (E τ)) ∧ (∀ i, Measurable (h i)) ∧
    (∀ i, i ≠ τ → Interp.VDominatedBy (slotNorms u i) (E i) (h i)) ∧
    Interp.VDominatedBy (slotNorms u τ) (V16.exceptionalMajor 48 E τ) (h τ)

/-- **V16 (the deliverable; route check §1.2).**  `HullBound` near the corner for the model form of every
window-full collection of a rank-1 box set, uniformly in `P, Π, Ps, χ, m, β`; the major subset is
`exceptionalMajor 48 E τ` (a function of `(E, τ)` only).  A hypothesis of the assembly (`Assembly.lean`);
the node proofs `B10`, `B11`, `B12` are not part of this file. -/
def V16Statement : Prop :=
  ∀ u : ℝ, 1 < u → ∀ 𝔭 : Params, V16Params u 𝔭 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (T : Form P) (CT : ℝ), FormBound u T CT →
      ∀ (Qs : Set Box), IsRankOne 𝔭.J Qs → ∀ (Ps : Finset TriTile), IsWindowFull Qs Ps →
      ∀ (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ), IsModelData 𝔭 Ps χ m →
      ∀ β : Fin 3 → ℝ, Interp.InCornerNbhd (Rof u) β →
        Interp.VHullBound (volume : Measure ℝ) (slotNorms u)
          (fun h => ‖modelForm T Ps χ m (h 0) (h 1) (h 2)‖) β (C * CT)

end PrimeBHT.TimeFrequency.X2
