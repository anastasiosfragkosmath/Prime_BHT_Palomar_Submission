module

public import PrimeBHT.TimeFrequency.X2.EnergyLemma.SelectableProof

/-!
# X2, node V12: kernels, semikernels (Neumann-Lara), and the quadrant game behind `OSelectable`

The selection lemma `OSelectable` follows from the existence of a KERNEL of the destruction relation `DT S` on every
finite family of candidates (`oSelectable_of_kernel`, `SelectableProof.lean`).  This file adds the two standard
reductions of kernel theory, in the abstract setting of `Absorb.lean`:

* `IsKernel D C K`: an independent (both directions) and absorbing subset;
* `IsSemikernel D C S` (Neumann-Lara): a nonempty independent subset such that every candidate destroying a member is
  destroyed by a member;
* `exists_kernel_of_semikernels`: if every nonempty subfamily has a semikernel, the family has a kernel (strong
  induction: a semikernel `S`, a kernel of the candidates not absorbed by `S`, and their union);
* `selectable_of_semikernels`, `oSelectable_of_semikernels`: the consequences for the game and for `OSelectable`.

A SOURCE of the strict relation (`selectable_of_sources`) is a singleton semikernel; semikernels of size two win the
strict `4`-cycles of the report (`{X1, X3}`).

## The quadrant game (the exact abstract form of the tile game)

`QCand W B` is `Absorb.Cand` WITHOUT the least-upper-bound condition: a nonempty finite footprint of abstract tiles
`(window, box)` and an upper bound `top` (`I ≤ W`, `b ≤ c`: boxes ordered by "descendant ≤ ancestor", windows by
inclusion).  `Dq Z X`: a tile of `X` lies in the quadrant `↓W_Z × ↑b_Z` of the top of `Z`.  This is EXACTLY the real
destruction relation `DT`: for a rank-1 box set, the boxes of `S` whose hull contains the top frequency `ξ` form a chain
(fields (e), (f)), so `maxTree S W ξ` is the set of tiles of `S` with `I_R ⊆ W` and box an ancestor-or-equal (hull
inclusion) of the DEEPEST box of `S` containing `ξ` (the effective top box, which is a descendant of every box of the
tree; it is the tree's own deepest box only when `ξ` avoids all deeper hulls).  Dropping `lub` is therefore necessary.

`QuadrantKernel W B`: **the open statement** (every finite family of `QCand` has a kernel).  Exact solvers on random and
adversarial instances (coupled or not, canonical or effective tops; scripts in the scratchpad `sel/`) never found a
family without a kernel; the strict relation has directed cycles, even ODD ones (so Richardson's theorem does not
apply), no scalar priority greedy produces kernels, and the chain/forest structure (`IsForest`) is essential.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2.Absorb

section Abstract

variable {α : Type*}

/-- A kernel of the destruction relation on `C`: a subset `K ⊆ C`, independent in both directions, that destroys every
candidate of `C`. -/
def IsKernel (D : α → α → Prop) (C K : Finset α) : Prop :=
  K ⊆ C ∧ (∀ Z ∈ K, ∀ Z' ∈ K, Z ≠ Z' → ¬ D Z Z') ∧ ∀ X ∈ C, ∃ Z ∈ K, D Z X

end Abstract

/-! ## The quadrant game -/

section Quadrant

variable (W B : Type*) [PartialOrder W] [PartialOrder B]

/-- A candidate of the quadrant game: a nonempty finite footprint of abstract tiles `(window, box)` with an UPPER BOUND
`top` for the tile order `(I, b) ≤ (Wt, c) ↔ I ≤ Wt ∧ c ≤ b` (no least-upper-bound condition: the effective top box of a
real tree is a descendant of its deepest box). -/
structure QCand where
  T : Finset (W × B)
  top : W × B
  nonempty : T.Nonempty
  upper : ∀ p ∈ T, p.1 ≤ top.1 ∧ top.2 ≤ p.2

variable {W B}

/-- `Dq Z X`: choosing `Z` destroys `X` (a tile of `X` lies in the quadrant below the top of `Z`). -/
def Dq (Z X : QCand W B) : Prop := ∃ p ∈ X.T, p.1 ≤ Z.top.1 ∧ Z.top.2 ≤ p.2

variable (W B) in
/-- **The open statement (quadrant kernel theorem).**  For a tree of windows and a forest of boxes, every finite family
of quadrant candidates has a kernel.  Exact solvers find no counterexample (random and adversarial instances, with and
without the window-depth coupling of real tiles, canonical and effective tops); the strict relation has odd directed
cycles, so this is not Richardson's theorem; the proof is OPEN. -/
def QuadrantKernel [IsForest W] [IsForest B] : Prop :=
  ∀ C : Finset (QCand W B), ∃ K, IsKernel Dq C K

end Quadrant

end PrimeBHT.TimeFrequency.X2.Absorb

namespace PrimeBHT.TimeFrequency.X2

open Absorb

end PrimeBHT.TimeFrequency.X2
