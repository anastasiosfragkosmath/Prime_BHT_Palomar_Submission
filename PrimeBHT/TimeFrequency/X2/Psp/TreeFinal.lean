module

public import PrimeBHT.TimeFrequency.X2.Psp.TreeEasy

/-!
# X2, V15 (assembly), step 6: `TreeLemmaStatementRev2` from the hard parts

`treeLemmaRev2_of_hardParts`: V15 (`TreeLemmaStatementRev2`, `X2/V16/Hyps.lean`) follows from

* the second profile `η'` of the class `𝔭.tree` (`ProfileOK 𝔭.1`, a hypothesis of the statement),
* `HardPartStatement`: the estimate for the parts `T_A` with `A = {1, 2}` or `A = {0, 2}` (one of the two Hilbert slots overlapping),

by the split into the (at most four) parts with `#A ≥ 2` (`modelForm_eq_sum_big_parts`), the unconditional estimate `part_easy` for the
parts with `A ⊇ {0, 1}` (both Hilbert slots lacunary; `eng ≤ engV`), and the triangle inequality.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-- **The hard parts of the tree lemma (NOT PROVED here; the exact remaining statement of V15).**  For the parts `T_A` of a good tree
with `A = {1, 2}` (slot 0 overlapping) or `A = {0, 2}` (slot 1 overlapping), `‖Λ_{T_A}‖ ≤ C CT |I_t| ∏_k engV_k`.  Route:
`Λ = Σ_σ ∫ Π(χ̃a₀, χ̃a₁, χ̃a₂) + (conversion error, `conv_error`)`; split the overlapping slot `a = T_{m_σ} G + T_{m_σ}(F - G)` with the
`G` of `OverlapPsp` (O1, O2); the error `Σ_σ ∫ Π(χ̃ T_{m_σ}(F - G), ℓ₁σ, ℓ₂σ)` by Hölder on the `σ`-intervals `I₀` with
`(p₀, 2, R)`, `p₀ = 2R/(R-2)` (O2 interpolated between `p = q` and `p = ∞`; (S) in the other two slots; `Σ_σ ∫ μ_σ ≤ C |I_t|`);
the main term `Σ_σ ∫ Π(T_{m_σ} G, ℓ₁σ, ℓ₂σ)` by V14 (`paraproduct` / `paraproduct_swap`) after modulation by `θ_k`, the term
`Σ_σ ∫ Π((1 - χ̃_σ) T_{m_σ}G, ℓ₁σ, ℓ₂σ)` by `bLayer`, (O1), the sup bound (S) in the other slots. -/
def HardPartStatement : Prop :=
  ∀ (𝔭 : Params), 𝔭.Admissible → 𝔭.tree.Admissible → ProfileOK 𝔭 → ∀ {u R : ℝ}, 1 < u → 2 < R →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (T : Form P) (CT : ℝ), FormBound u T CT →
      ∀ (Qs : Set Box), IsRankOne 𝔭.J Qs → ∀ (Tr : Finset TriTile) (t : Top) (η η' : ℝ → ℝ) (χ : TriTile → ℝ → ℝ)
        (m : TriTile → Fin 3 → ℝ → ℂ) (A : Finset (Fin 3)), (A = {1, 2} ∨ A = {0, 2}) → (∀ Q ∈ Tr, Q.box ∈ Qs) →
        PartData 𝔭 η η' Tr (treePart Tr t A) t χ m → ∀ F : Fin 3 → ℝ → ZMod P → ℂ, (∀ k, Measurable (F k)) →
          (∀ k, ∃ B, ∀ x, yNorm 2 (F k x) ≤ B) →
            ‖modelForm T (treePart Tr t A) χ m (F 0) (F 1) (F 2)‖ₑ ≤
              ENNReal.ofReal (C * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) * ∏ k : Fin 3, engV 𝔭 u R k (F k) Tr

theorem eng_prod_le_engV {P : ℕ} [NeZero P] (𝔭 : Params) (u R : ℝ) (F : Fin 3 → ℝ → ZMod P → ℂ) (Tr : Finset TriTile) :
    ∏ k : Fin 3, eng 𝔭.tree (slotExp u k) k (F k) Tr (qv R k) ≤ ∏ k : Fin 3, engV 𝔭 u R k (F k) Tr :=
  Finset.prod_le_prod' fun _k _ => le_max_left _ _

theorem card_ge_two_cases : ∀ A : Finset (Fin 3), 2 ≤ A.card → ({0, 1} ⊆ A ∨ A = {1, 2} ∨ A = {0, 2}) := by decide

/-- **V15 from the hard parts**.  The second profile `η'` of the class `𝔭.tree` is the hypothesis `ProfileOK 𝔭` of the statement. -/
theorem treeLemmaRev2_of_hardParts (hHard : HardPartStatement) : TreeLemmaStatementRev2 := by
  intro 𝔭 h𝔭 h𝔭t hprof u R hu hR
  obtain ⟨η', hη'⟩ := hprof.1
  obtain ⟨Ch, hCh0, hCh⟩ := hHard 𝔭 h𝔭 h𝔭t hprof hu hR
  set Cp : ℝ := max (easyConst 𝔭 u R) 0 + Ch with hCp
  have hCp0 : 0 ≤ Cp := by have := le_max_right (easyConst 𝔭 u R) 0; positivity
  refine ⟨4 * Cp, by positivity, ?_⟩
  intro P _ T CT hT Qs hQ Tr t htree hbox χ m hdata F hF hFb
  have hCT : 0 ≤ CT := nonneg_of_formBound (by linarith) hT
  obtain ⟨hcls, hcons, η, hη, hcut⟩ := hdata
  have pdTr : PartData 𝔭 η η' Tr Tr t χ m := ⟨h𝔭, h𝔭t, hη, hη', subset_rfl, htree, hcons, hcut, hcls⟩
  rw [modelForm_eq_sum_big_parts hQ hbox t T χ m (F 0) (F 1) (F 2)]
  have hpart : ∀ A ∈ Finset.univ.filter (fun A : Finset (Fin 3) => 2 ≤ A.card),
      ‖modelForm T (treePart Tr t A) χ m (F 0) (F 1) (F 2)‖ₑ ≤
        ENNReal.ofReal (Cp * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) * ∏ k : Fin 3, engV 𝔭 u R k (F k) Tr := by
    intro A hA
    have hA2 := (Finset.mem_filter.1 hA).2
    have hpdA : PartData 𝔭 η η' Tr (treePart Tr t A) t χ m :=
      pdTr.mono (Finset.filter_subset _ _) (isGoodTree_treePart htree A)
    rcases card_ge_two_cases A hA2 with h01 | h12 | h02
    · have h0 : 0 ∈ A := h01 (by simp)
      have h1 : 1 ∈ A := h01 (by simp)
      have := part_easy hpdA hQ (fun R hR => hbox R (mem_treePart.1 hR).1)
        (fun R hR => not_isOvSlot_of_mem_treePart h0 hR) (fun R hR => not_isOvSlot_of_mem_treePart h1 hR)
        (isLacunary_treePart h𝔭.1 hQ htree.1 hbox h0) (isLacunary_treePart h𝔭.1 hQ htree.1 hbox h1) hu hR hT hF hFb
      refine this.trans ?_
      have hc : ENNReal.ofReal (easyConst 𝔭 u R * CT) ≤ ENNReal.ofReal (Cp * CT) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
          ((le_max_left _ _).trans (by rw [hCp]; linarith)) hCT)
      exact mul_le_mul' (mul_le_mul' hc le_rfl) (eng_prod_le_engV 𝔭 u R F Tr)
    · have := hCh P T CT hT Qs hQ Tr t η η' χ m A (Or.inl h12) hbox hpdA F hF hFb
      refine this.trans ?_
      have hc : ENNReal.ofReal (Ch * CT) ≤ ENNReal.ofReal (Cp * CT) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by rw [hCp]; linarith [le_max_right (easyConst 𝔭 u R) 0]) hCT)
      exact mul_le_mul' (mul_le_mul' hc le_rfl) le_rfl
    · have := hCh P T CT hT Qs hQ Tr t η η' χ m A (Or.inr h02) hbox hpdA F hF hFb
      refine this.trans ?_
      have hc : ENNReal.ofReal (Ch * CT) ≤ ENNReal.ofReal (Cp * CT) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by rw [hCp]; linarith [le_max_right (easyConst 𝔭 u R) 0]) hCT)
      exact mul_le_mul' (mul_le_mul' hc le_rfl) le_rfl
  calc ‖∑ A ∈ Finset.univ.filter (fun A : Finset (Fin 3) => 2 ≤ A.card), modelForm T (treePart Tr t A) χ m (F 0) (F 1) (F 2)‖ₑ
      ≤ ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin 3) => 2 ≤ A.card),
          ‖modelForm T (treePart Tr t A) χ m (F 0) (F 1) (F 2)‖ₑ := enorm_sum_le _ _
    _ ≤ ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin 3) => 2 ≤ A.card),
          ENNReal.ofReal (Cp * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) * ∏ k : Fin 3, engV 𝔭 u R k (F k) Tr :=
        Finset.sum_le_sum hpart
    _ = (4 : ℝ≥0∞) * (ENNReal.ofReal (Cp * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) * ∏ k : Fin 3, engV 𝔭 u R k (F k) Tr) := by
        rw [Finset.sum_const, card_bigParts, nsmul_eq_mul]; norm_num
    _ = ENNReal.ofReal (4 * Cp * CT) * ENNReal.ofReal ((2 : ℝ) ^ t.1.1) * ∏ k : Fin 3, engV 𝔭 u R k (F k) Tr := by
        have : ENNReal.ofReal (4 * Cp * CT) = 4 * ENNReal.ofReal (Cp * CT) := by
          rw [show 4 * Cp * CT = 4 * (Cp * CT) by ring, ENNReal.ofReal_mul (by norm_num)]
          norm_num
        rw [this]; ring

end PrimeBHT.TimeFrequency.X2
