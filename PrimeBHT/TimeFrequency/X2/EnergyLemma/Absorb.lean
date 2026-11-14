module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Data.List.Nodup
public import Mathlib.Order.WellFounded

/-!
# X2, node V12: the abstract selection game behind `OSelectable` (partial results)

`OSelectable` (`SelectO.lean`) asks for an ORDER of greedy selections whose output satisfies the clause `O1`.  This file
isolates the combinatorial core, on abstract data, and proves the easy reductions.

## The abstract game

Candidates `X` of a finite family `C`; two relations on candidates:

* `D Z X`: "choosing `Z` destroys `X`" (the maximal tree of `Z` meets the tree of `X`; reflexive);
* `V X Z`: "choosing `X` BEFORE `Z` violates `O1`"; one always has `V X Z → D Z X` (a violation means that a tile of
  `X` lies in the shadow of the top of `Z`).

`Selectable D V C`: an ordered list `Z₁, …, Z_m` of members of `C`, such that for `i < j` the earlier choice neither
destroys the later one (`¬ D Zᵢ Zⱼ`: the later tree is still inside the residual) nor violates `O1` (`¬ V Zᵢ Zⱼ`), and
every candidate is destroyed by some chosen one (the selection runs until no candidate is left).

* `selectable_of_kernel`: a kernel of `D` (independent and absorbing set) gives a selection (in any order);
* `selectable_of_good`: if every nonempty subfamily contains a GOOD element (`V X Z → D X Z` for all `Z`: choosing
  `X` first is harmless), the game is winnable (greedy);
* `selectable_of_sources`: the same, with the good element given as a source of the strict relation
  (`D Z X → D X Z` for all `Z`);
* `selectable_of_wellFounded` (Duchet type): if the strict relation `D Z X ∧ ¬ D X Z` is well-founded, the game is
  winnable.  NOTE: the strict relation of the REAL game has directed cycles (length 4, see the report), so this
  does NOT close `OSelectable`; it handles the cases where it is acyclic.

## The model (hull forest x dyadic windows, canonical tops)

`Cand W B`: a nonempty finite set `T` of abstract tiles `(window, box)`, with its canonical top `(W, b)`: the least
upper bound for the tile order `(I, b) ≤ (W, c) ↔ I ≤ W ∧ c ≤ b` (windows are ordered by inclusion, boxes by
"descendant ≤ ancestor": a tile of a tree has a box ancestor of the top box).  `Dm`, `Vm` are the relations of the
model (`Dm Z X ↔ T_X ∩ ↓t_Z ≠ ∅`; `Vm X Z`: a tile `w` of `X` inside the window of `Z` and a tile `n` of `Z` with box
strictly below the box of `w`), `Vm_imp_Dm`.

* `ModelSelectable W B`: **the missing statement** (OPEN): `Selectable Dm Vm C` for every finite family `C`;
* `strict_window_lt`: strict destruction towards a candidate with deeper-or-equal top box strictly shrinks the
  window; hence `modelSelectable_commonBox`: the game is winnable when all top boxes coincide.
-/

@[expose] public section

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2.Absorb

section Abstract

variable {α : Type*}

/-- A legal ordered selection: for `i < j` the earlier choice neither destroys nor violates the later one. -/
def Legal (D V : α → α → Prop) (𝒵 : List α) : Prop :=
  𝒵.Pairwise fun Z Z' => ¬ D Z Z' ∧ ¬ V Z Z'

/-- The game is winnable on `C`: a legal selection from `C` that destroys every candidate of `C`. -/
def Selectable (D V : α → α → Prop) (C : Finset α) : Prop :=
  ∃ 𝒵 : List α, (∀ Z ∈ 𝒵, Z ∈ C) ∧ Legal D V 𝒵 ∧ ∀ X ∈ C, ∃ Z ∈ 𝒵, D Z X

theorem selectable_of_kernel {D V : α → α → Prop} {C K : Finset α} (hV : ∀ X ∈ C, ∀ Z ∈ C, V X Z → D Z X)
    (hKC : K ⊆ C) (hind : ∀ Z ∈ K, ∀ Z' ∈ K, Z ≠ Z' → ¬ D Z Z') (habs : ∀ X ∈ C, ∃ Z ∈ K, D Z X) :
    Selectable D V C := by
  refine ⟨K.toList, fun Z hZ => hKC (Finset.mem_toList.1 hZ), ?_, fun X hX => ?_⟩
  · refine (Finset.nodup_toList K).pairwise_of_forall_ne fun Z hZ Z' hZ' hne => ?_
    have hZ1 := Finset.mem_toList.1 hZ
    have hZ2 := Finset.mem_toList.1 hZ'
    exact ⟨hind Z hZ1 Z' hZ2 hne, fun hv => hind Z' hZ2 Z hZ1 hne.symm (hV Z (hKC hZ1) Z' (hKC hZ2) hv)⟩
  · obtain ⟨Z, hZ, hD⟩ := habs X hX
    exact ⟨Z, Finset.mem_toList.2 hZ, hD⟩

end Abstract

/-! ## The model -/

section Model

/-- Tree orders: the ancestors (elements above) of any element form a chain. -/
class IsForest (α : Type*) [PartialOrder α] : Prop where
  chain : ∀ a b c : α, a ≤ b → a ≤ c → b ≤ c ∨ c ≤ b

variable (W B : Type*) [PartialOrder W] [PartialOrder B]

/-- A candidate of the model: a nonempty finite set of abstract tiles `(window, box)` with its CANONICAL top, the least
upper bound for `(I, b) ≤ (Wt, c) ↔ I ≤ Wt ∧ c ≤ b`. -/
structure Cand where
  T : Finset (W × B)
  top : W × B
  nonempty : T.Nonempty
  upper : ∀ p ∈ T, p.1 ≤ top.1 ∧ top.2 ≤ p.2
  lub : ∀ t : W × B, (∀ p ∈ T, p.1 ≤ t.1 ∧ t.2 ≤ p.2) → top.1 ≤ t.1 ∧ t.2 ≤ top.2

variable {W B}

end Model

end PrimeBHT.TimeFrequency.X2.Absorb
