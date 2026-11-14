module

public import PrimeBHT.TimeFrequency.X2.EnergyLemma.Defs

/-!
# X2, node V12: the abstract greedy selection (termination)

`PhaseSeq V key S 𝒯` : the list `𝒯 = [(Tr₁, t₁), …]` is a greedy selection from the finite collection `S`: each `Tr_i`
is a candidate (`V Tr_i t_i`) inside the current residual `S_i`, with MAXIMAL `key` among all candidates inside `S_i`,
and `S_{i+1} = S_i ∖ maxTree S_i t_i`.  `phase_exists`: a selection exists that runs until no candidate is left
(each round removes the nonempty tree `Tr_i ⊆ maxTree S_i t_i`, so the collection strictly decreases).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

section Phase

variable {ι : Type*} [LinearOrder ι]

/-- A greedy selection sequence. -/
def PhaseSeq (V : Finset TriTile → Top → Prop) (key : Finset TriTile → ι) :
    Finset TriTile → List (Finset TriTile × Top) → Prop
  | _, [] => True
  | S, T :: 𝒯 => V T.1 T.2 ∧ T.1 ⊆ S ∧ (∀ Tr ⊆ S, (∃ t, V Tr t) → key Tr ≤ key T.1) ∧
      PhaseSeq V key (S \ maxTree S T.2.1 T.2.2) 𝒯

variable {V : Finset TriTile → Top → Prop} {key : Finset TriTile → ι}

theorem PhaseSeq.subset : ∀ {S : Finset TriTile} {𝒯 : List (Finset TriTile × Top)},
    PhaseSeq V key S 𝒯 → ∀ T ∈ 𝒯, T.1 ⊆ S
  | _, [], _, T, hT => absurd hT (List.not_mem_nil)
  | S, T₀ :: 𝒯, h, T, hT => by
    obtain ⟨-, h2, -, h4⟩ := h
    rcases List.mem_cons.1 hT with rfl | hT
    · exact h2
    · exact (PhaseSeq.subset h4 T hT).trans Finset.sdiff_subset

theorem PhaseSeq.valid : ∀ {S : Finset TriTile} {𝒯 : List (Finset TriTile × Top)},
    PhaseSeq V key S 𝒯 → ∀ T ∈ 𝒯, V T.1 T.2
  | _, [], _, T, hT => absurd hT (List.not_mem_nil)
  | S, T₀ :: 𝒯, h, T, hT => by
    obtain ⟨h1, -, -, h4⟩ := h
    rcases List.mem_cons.1 hT with rfl | hT
    · exact h1
    · exact PhaseSeq.valid h4 T hT

end Phase

/-- The tops of a family contribute `∑ |I_t|`, whether the trees are the maximal trees or sub-trees. -/
theorem topSum_removedTrees (𝒯 : List (Finset TriTile × Top)) :
    ∀ S : Finset TriTile, topSum (removedTrees S (𝒯.map Prod.snd)) = topSum 𝒯 := by
  induction 𝒯 with
  | nil => intro S; rfl
  | cons T 𝒯 ih =>
    intro S
    simp only [List.map_cons, removedTrees, topSum_cons]
    rw [ih]

end PrimeBHT.TimeFrequency.X2
