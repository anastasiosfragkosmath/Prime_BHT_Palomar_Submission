module

public import PrimeBHT.TimeFrequency.X2.Disc.Transfer

/-!
# X2, node V05 (R4, step 2): the indexed form of `class_form_bound`

For a finite index type `ι`, an injective `β : ι → Box` with values in a rank-1 set `Qs` and multipliers `m i k` with
`m i k ∈ M_{ω_k(β i)}(𝔭)`, the unlocalized forms satisfy
`‖Σ_i ∫ Π(T_{m i 0} F₁, T_{m i 1} F₂, T_{m i 2} F₃)‖ₑ ≤ 2 (ofReal (C₀ CT) ‖F₁‖₂ ‖F₂‖₂ ‖F₃‖_u)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate ContDiff
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Disc

theorem class_form_bound_indexed {u : ℝ} {𝔭 : Params} {C₀ : ℝ} (hM : ModelBoundAt u 𝔭 C₀)
    {P : ℕ} [NeZero P] {T : Form P} {CT : ℝ} (hT : FormBound u T CT)
    {Qs : Set Box} (hQs : IsRankOne 𝔭.J Qs) {ι : Type*} (s : Finset ι) (β : ι → Box)
    (hβ : Set.InjOn β ↑s) (hβQ : ∀ i ∈ s, β i ∈ Qs)
    (m : ι → Fin 3 → ℝ → ℂ) (hm : ∀ i ∈ s, ∀ k, InMult 𝔭 (β i).scale ((β i).centre k) (m i k))
    {η : ℝ → ℝ} (hη : IsEtaCut 𝔭 η) (hX : ∀ s v : ℤ, InX 𝔭 s v (tileCutoff η s v))
    {F₁ F₂ F₃ : ℝ → ZMod P → ℂ} (hc₁ : Continuous F₁) (hc₂ : Continuous F₂) (hc₃ : Continuous F₃)
    (hb₁ : IsBddV F₁) (hb₂ : IsBddV F₂) (hb₃ : IsBddV F₃)
    (hf₁ : eLpNorm (fun x => yNorm 2 (F₁ x)) 2 volume < ⊤)
    (hf₂ : eLpNorm (fun x => yNorm 2 (F₂ x)) 2 volume < ⊤)
    (hint : ∀ i ∈ s, Integrable (fun x => T (tmult (m i 0) F₁ x) (tmult (m i 1) F₂ x) (tmult (m i 2) F₃ x))) :
    ‖∑ i ∈ s, ∫ x, T (tmult (m i 0) F₁ x) (tmult (m i 1) F₂ x) (tmult (m i 2) F₃ x)‖ₑ ≤
      2 * (ENNReal.ofReal (C₀ * CT) * eLpNorm (fun x => yNorm 2 (F₁ x)) 2 volume *
        eLpNorm (fun x => yNorm 2 (F₂ x)) 2 volume * eLpNorm (fun x => yNorm u (F₃ x)) ⊤ volume) := by
  classical
  let Q : Finset Box := s.image β
  let m' : Box → Fin 3 → ℝ → ℂ := fun B => if h : ∃ i ∈ s, β i = B then m h.choose else fun _ _ => 0
  have hm' : ∀ i ∈ s, m' (β i) = m i := by
    intro i hi
    have h : ∃ j ∈ s, β j = β i := ⟨i, hi, rfl⟩
    simp only [m', dite_eq_left h]
    have := hβ h.choose_spec.1 hi h.choose_spec.2
    rw [this]
  have hQ : (↑Q : Set Box) ⊆ Qs := by
    intro B hB
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hB)
    exact hβQ i hi
  have hmQ : ∀ B ∈ Q, ∀ k, InMult 𝔭 B.scale (B.centre k) (m' B k) := by
    intro B hB k
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hB
    rw [hm' i hi]; exact hm i hi k
  have key := class_form_bound hM hT hQs Q hQ m' hmQ hη hX hc₁ hc₂ hc₃ hb₁ hb₂ hb₃ hf₁ hf₂ (by
    intro B hB
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hB
    rw [hm' i hi]; exact hint i hi)
  have hsum : ∑ B ∈ Q, ∫ x, T (tmult (m' B 0) F₁ x) (tmult (m' B 1) F₂ x) (tmult (m' B 2) F₃ x) =
      ∑ i ∈ s, ∫ x, T (tmult (m i 0) F₁ x) (tmult (m i 1) F₂ x) (tmult (m i 2) F₃ x) := by
    rw [Finset.sum_image hβ]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hm' i hi]
  rw [hsum] at key
  exact key

end PrimeBHT.TimeFrequency.X2.Disc
