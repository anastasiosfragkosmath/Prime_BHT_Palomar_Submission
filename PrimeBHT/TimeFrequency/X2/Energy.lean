module

public import PrimeBHT.TimeFrequency.X2.Classes
public import PrimeBHT.TimeFrequency.X2.Collections

/-!
# X2, node V09: tree norms and energies (definitions)

Definitions of `drafts/x2-interface/03-V09-Energy.lean.txt` and of the V10-V12 draft
`04-V10-V12-Orthogonality-EnergyLemma.lean.txt` (`mixedPow`, `topSum`, `IsEnergyExponent`), with the easy lemmas.

Energies are `ℝ≥0∞`-valued suprema (no `BddAbove` bookkeeping; `eng` is monotone in the collection by
definition).  Two tree quantities are distinguished (design doc §4, finding X2-I1):

* `topNorm`: the tree norm `‖F‖_{T,k,q}` with the top `t` FIXED, sup over tree operators of class `𝔭` only
  (DPLMV (e:size)); this is what the orthogonality / interpolation estimates V10 / V11 control;
* `eng`: DPLMV (e:engdef), sup over all `k`-lacunary sub-trees with THEIR OWN tops; this is what the energy lemma
  halves and what the tree lemma V15 uses.

`tailMass`/`tailWeight` of the draft are NOT restated here: they live in `X2/V16/Exceptional.lean`.
The B5 bound `eng_le_tailMass` is a separate node (`X2/EnergyBound.lean`).

## Deviations from the draft

None in the statements.  Added lemmas: `topNorm_le_eng`, `eng_le_of_forall`, `topNorm_le_of_forall`,
`le_topNorm`, `eng_empty`, `treeOpNorm_nonneg`-free facts, `topSum_nil/cons/append`, `mixedPow_mono`, ...
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

section

variable {P : ℕ} [NeZero P]

/-- `|I_t|^{-1/q} ‖T_Tr F‖_{L^q(ℝ; L^s(Y))}` for one choice of tree-operator data. -/
def treeOpNorm (s q : ℝ) (Tr : Finset TriTile) (t : Top) (ψ m : TriTile → ℝ → ℂ)
    (F : ℝ → ZMod P → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (-1 / q)) *
    eLpNorm (fun x => yNorm s (treeOp Tr ψ m F x)) (ENNReal.ofReal q) volume

/-- DPLMV (e:size) with the top fixed: sup over the type-`k` tree operators of class `𝔭`. -/
def topNorm (𝔭 : Params) (s : ℝ) (k : Fin 3) (F : ℝ → ZMod P → ℂ) (Tr : Finset TriTile) (t : Top)
    (q : ℝ) : ℝ≥0∞ :=
  ⨆ (ψ : TriTile → ℝ → ℂ) (m : TriTile → ℝ → ℂ) (_ : IsTreeOpData 𝔭 k Tr ψ m),
    treeOpNorm s q Tr t ψ m F

/-- DPLMV (e:engdef): sup over the `k`-lacunary trees `Tr ⊆ Cs` (any top) of `topNorm`. -/
def eng (𝔭 : Params) (s : ℝ) (k : Fin 3) (F : ℝ → ZMod P → ℂ) (Cs : Finset TriTile) (q : ℝ) :
    ℝ≥0∞ :=
  ⨆ (Tr : Finset TriTile) (_ : Tr ⊆ Cs) (t : Top) (_ : IsTree Tr t) (_ : IsLacunary k Tr),
    topNorm 𝔭 s k F Tr t q

/-! ### Elementary lemmas -/

theorem le_topNorm {𝔭 : Params} {s : ℝ} {k : Fin 3} {F : ℝ → ZMod P → ℂ} {Tr : Finset TriTile}
    {t : Top} {q : ℝ} {ψ m : TriTile → ℝ → ℂ} (h : IsTreeOpData 𝔭 k Tr ψ m) :
    treeOpNorm s q Tr t ψ m F ≤ topNorm 𝔭 s k F Tr t q :=
  le_iSup₂_of_le ψ m (le_iSup_of_le h le_rfl)

theorem topNorm_le_of_forall {𝔭 : Params} {s : ℝ} {k : Fin 3} {F : ℝ → ZMod P → ℂ}
    {Tr : Finset TriTile} {t : Top} {q : ℝ} {c : ℝ≥0∞}
    (h : ∀ ψ m : TriTile → ℝ → ℂ, IsTreeOpData 𝔭 k Tr ψ m → treeOpNorm s q Tr t ψ m F ≤ c) :
    topNorm 𝔭 s k F Tr t q ≤ c :=
  iSup₂_le fun ψ m => iSup_le fun hψm => h ψ m hψm

theorem topNorm_le_eng {𝔭 : Params} {s : ℝ} {k : Fin 3} {F : ℝ → ZMod P → ℂ} {Cs Tr : Finset TriTile}
    {t : Top} {q : ℝ} (hsub : Tr ⊆ Cs) (ht : IsTree Tr t) (hlac : IsLacunary k Tr) :
    topNorm 𝔭 s k F Tr t q ≤ eng 𝔭 s k F Cs q :=
  le_iSup_of_le Tr (le_iSup_of_le hsub (le_iSup_of_le t (le_iSup_of_le ht (le_iSup_of_le hlac le_rfl))))

theorem eng_le_of_forall {𝔭 : Params} {s : ℝ} {k : Fin 3} {F : ℝ → ZMod P → ℂ} {Cs : Finset TriTile}
    {q : ℝ} {c : ℝ≥0∞}
    (h : ∀ Tr : Finset TriTile, Tr ⊆ Cs → ∀ t : Top, IsTree Tr t → IsLacunary k Tr →
      topNorm 𝔭 s k F Tr t q ≤ c) :
    eng 𝔭 s k F Cs q ≤ c :=
  iSup_le fun Tr => iSup_le fun hsub => iSup_le fun t => iSup_le fun ht => iSup_le fun hlac =>
    h Tr hsub t ht hlac

theorem eng_mono (𝔭 : Params) (s : ℝ) (k : Fin 3) (F : ℝ → ZMod P → ℂ) {Cs Cs' : Finset TriTile}
    (h : Cs ⊆ Cs') (q : ℝ) : eng 𝔭 s k F Cs q ≤ eng 𝔭 s k F Cs' q :=
  eng_le_of_forall fun _ hTr _ ht hlac => topNorm_le_eng (hTr.trans h) ht hlac

/-- The empty collection has only the empty tree, whose tree operator is `0`. -/
theorem treeOpNorm_empty (s q : ℝ) (t : Top) (ψ m : TriTile → ℝ → ℂ) (F : ℝ → ZMod P → ℂ)
    (hs : 0 < s) : treeOpNorm s q ∅ t ψ m F = 0 := by
  have h0 : (fun x => yNorm s (treeOp (∅ : Finset TriTile) ψ m F x)) = fun _ => 0 := by
    funext x
    simp [treeOp, yNorm, Real.zero_rpow hs.ne', Real.zero_rpow (inv_ne_zero hs.ne')]
  rw [treeOpNorm, h0]
  simp

end

/-! ### The norms `mixedPow`, `topSum` and the energy exponents (draft 04) -/

section

variable {P : ℕ} [NeZero P]

/-- `‖F‖_{L^q(ℝ; L^s(Y))}^q` as an `ℝ≥0∞` integral. -/
def mixedPow (q s : ℝ) (F : ℝ → ZMod P → ℂ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (yNorm s (F x) ^ q)

end

/-- `Σ_{T ∈ 𝒯} |I_T|` for a list of trees with tops. -/
def topSum (𝒯 : List (Finset TriTile × Top)) : ℝ≥0∞ :=
  (𝒯.map (fun T => ENNReal.ofReal ((2 : ℝ) ^ T.2.1.1))).sum

@[simp] theorem topSum_nil : topSum [] = 0 := rfl

@[simp] theorem topSum_cons (T : Finset TriTile × Top) (𝒯 : List (Finset TriTile × Top)) :
    topSum (T :: 𝒯) = ENNReal.ofReal ((2 : ℝ) ^ T.2.1.1) + topSum 𝒯 := by
  simp [topSum]

theorem topSum_append (𝒯 𝒯' : List (Finset TriTile × Top)) :
    topSum (𝒯 ++ 𝒯') = topSum 𝒯 + topSum 𝒯' := by
  simp [topSum, List.sum_append]

theorem topSum_ne_top (𝒯 : List (Finset TriTile × Top)) : topSum 𝒯 ≠ ⊤ := by
  induction 𝒯 with
  | nil => simp
  | cons T 𝒯 ih => rw [topSum_cons]; exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ih⟩

/-- Energy exponents: `qX = 2` for the Hilbert slot `s = 2`; `qX > max(s, s')` for `L^s(Y)`
(`L^s(Y_P)` is `qX`-intermediate between `L^{s₀}(Y_P)` and `L²(Y_P)`, blueprint §0.1). -/
def IsEnergyExponent (s qX : ℝ) : Prop :=
  (s = 2 ∧ qX = 2) ∨ (1 < s ∧ s < qX ∧ s / (s - 1) < qX)

end PrimeBHT.TimeFrequency.X2
