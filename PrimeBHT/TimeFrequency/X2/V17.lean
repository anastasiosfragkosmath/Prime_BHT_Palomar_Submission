module

public import PrimeBHT.TimeFrequency.X2.V16.Defs
public import PrimeBHT.TimeFrequency.X2.YVec
public import PrimeBHT.TimeFrequency.X2.ModelOp
public import PrimeBHT.TimeFrequency.X2.Interp.StrongV
import PrimeBHT.TimeFrequency.X2.ModelOpTools
import PrimeBHT.TimeFrequency.X2.ClassKernel

/-!
# X2, node V17: the statement `V17Statement` and its proof from the abstract chain

`V17Statement` (draft `80-V17-Interp`): `HullBound` with constant `K` on the corner region `𝒩_{R(u)}` (plus the
qualitative structure) implies the strong bound at `(2, 2, ∞)`:
`|∫ ⟨B(F₁,F₂), F₃⟩_Y| ≤ C₁ K ‖F₁‖_{L²(H)} ‖F₂‖_{L²(H)} ‖F₃‖_{L^∞(X_u)}`, `C₁ = C₁(u)` LINEAR in `K`.

It is PROVED here by instantiating the abstract theorem `Interp.v17_abstract` (`X2/Interp/StrongV.lean`) at
`W := YVec P 2` (the Hilbert slots, with `‖w‖ = yNorm 2 w`), `E := YVec P u'` (the output space `X_{u'}`,
`u' = u/(u-1)`), `pr e v := yPair e v` (`isDualPairing_yPair`), `ν = slotNorms u`, `R = Rof u`:

* the ℝ-bilinearity hypotheses of the abstract theorem follow from the ℂ-bilinearity in `IsBilinOpV`
  (`c • v = (c : ℂ) • v` in the real structure of the complex normed space `YVec P s`);
* the continuity hypothesis `hcont` (simple-function form) is the field `cont` of `IsBilinOpV` applied to the
  coercions of the simple functions (bounded, measurable); the topologies of `YVec P s` and `ZMod P → ℂ` agree
  (`YVec.continuous_val`, `YVec.continuous_mk`);
* boundedness classes: `slotNorms`-bounded measurable functions are the `yNorm 2`-bounded ones (`isBddV_iff`).

## Deviations from the draft

* the predicates `IsSubadditiveV`, `IsSmallV`, `VHullBound`, `InCornerNbhd` are those of the V17 chain (namespace
  `X2.Interp`, with the measure `volume` explicit), as ruled for the drafts 80/06/09; `IsBddV`, `IsDominatedV`,
  `IsBilinOpV` (X2-side, `yNorm 2`-boundedness) are in `X2/ModelOp.lean`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- **V17 (the deliverable).**  `HullBound` with constant `K` on the corner region `𝒩_{R(u)}` implies
`|∫ ⟨B(F₁,F₂), F₃⟩_Y| ≤ C₁ K ‖F₁‖_{L²(H)} ‖F₂‖_{L²(H)} ‖F₃‖_{L^∞(X_u)}`, `C₁ = C₁(u)` linear in `K`. -/
def V17Statement : Prop :=
  ∀ u : ℝ, 1 < u → ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (P : ℕ) [NeZero P] (Λ : (Fin 3 → ℝ → ZMod P → ℂ) → ℝ)
    (B : (ℝ → ZMod P → ℂ) → (ℝ → ZMod P → ℂ) → ℝ → ZMod P → ℂ) (K : ℝ), 0 ≤ K →
    Interp.IsSubadditiveV (slotNorms u) Λ → Interp.IsSmallV (volume : Measure ℝ) (slotNorms u) Λ →
    IsBilinOpV B → IsDominatedV B Λ →
    (∀ β, Interp.InCornerNbhd (Rof u) β → Interp.VHullBound (volume : Measure ℝ) (slotNorms u) Λ β K) →
    ∀ F₁ F₂ F₃ : ℝ → ZMod P → ℂ, Continuous F₁ → Continuous F₂ → Continuous F₃ →
      IsBddV F₁ → IsBddV F₂ → IsBddV F₃ →
      eLpNorm (fun x => yNorm 2 (F₁ x)) 2 volume < ⊤ → eLpNorm (fun x => yNorm 2 (F₂ x)) 2 volume < ⊤ →
        ‖∫ x, yPair (B F₁ F₂ x) (F₃ x)‖ₑ ≤ ENNReal.ofReal (C₁ * K) *
          eLpNorm (fun x => yNorm 2 (F₁ x)) 2 volume * eLpNorm (fun x => yNorm 2 (F₂ x)) 2 volume *
          eLpNorm (fun x => yNorm u (F₃ x)) ⊤ volume

section Instantiation

variable {P : ℕ} [NeZero P]

theorem eLpNorm_yvec_eq {s : ℝ} [Fact (1 ≤ ENNReal.ofReal s)] (hs : 1 ≤ s) {F : ℝ → YVec P s}
    (hF : Measurable F) (p : ℝ≥0∞) :
    eLpNorm F p volume = eLpNorm (fun x => yNorm s (F x).val) p volume :=
  eLpNorm_congr_norm_ae hF.aestronglyMeasurable
    ((measurable_yNorm_fun s).comp hF).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [YVec.norm_eq hs, Real.norm_of_nonneg (yNorm_nonneg' _ _)])

end Instantiation

/-- **V17.**  Proof from the abstract chain (`Interp.v17_abstract`) at `YVec`. -/
theorem v17 : V17Statement := by
  intro u hu
  have hR : 1 ≤ Rof u := one_le_Rof hu
  refine ⟨4 * Interp.cornerConst (Rof u), mul_nonneg (by norm_num) (Interp.cornerConst_nonneg hR), ?_⟩
  intro P _ Λ B K hK hsub hsmall hbil hdom hhull F₁ F₂ F₃ _ _ _ hb₁ hb₂ hb₃ hf₁ hf₂
  have hH : u.HolderConjugate u.conjExponent := Real.HolderConjugate.conjExponent hu
  have hfact : Fact (1 ≤ ENNReal.ofReal u.conjExponent) :=
    YVec.fact_of_le (le_of_lt hH.symm.lt)
  have conv : ∀ (i : Fin 3) (f : ℝ → ZMod P → ℂ), Interp.IsBddV (slotNorms u i) f → IsBddV f :=
    fun i f hf => isBddV_iff_isBddC.2 ((isBddV_iff (slotExp_pos hu i)).1 hf)
  have hν0 : ∀ w : YVec P 2, slotNorms u 0 w.val = ‖w‖ := fun w => by
    show yNorm (slotExp u 0) w.val = ‖w‖
    rw [slotExp_zero]
    exact (YVec.norm_eq (by norm_num) w).symm
  have hν1 : ∀ w : YVec P 2, slotNorms u 1 w.val = ‖w‖ := fun w => by
    show yNorm (slotExp u 1) w.val = ‖w‖
    rw [slotExp_one]
    exact (YVec.norm_eq (by norm_num) w).symm
  have hν2 : Interp.IsSlotNorm (slotNorms u 2 : (ZMod P → ℂ) → ℝ) :=
    isSlotNorm_yNorm (slotExp_pos hu 2)
  have hpr : Interp.IsDualPairing (E := YVec P u.conjExponent) (W := YVec P 2) (slotNorms u 2)
      (fun e v => yPair e.val v.val) := by
    show Interp.IsDualPairing (E := YVec P u.conjExponent) (W := ZMod P → ℂ) (yNorm (slotExp u 2))
      (fun e v => yPair e.val v)
    rw [slotExp_two]
    exact isDualPairing_yPair hH
  have simple_bdd : ∀ f : SimpleFunc ℝ (YVec P 2), IsBddV (⇑f : ℝ → ZMod P → ℂ) := fun f => by
    obtain ⟨M, hM⟩ := f.exists_forall_norm_le
    exact ⟨f.measurable, M, fun x => by
      have := hM x
      rwa [YVec.norm_eq (by norm_num)] at this⟩
  have hsub' : Interp.IsSubadditiveV (α := ℝ) (W := YVec P 2) (slotNorms u) Λ := hsub
  have hsmall' : Interp.IsSmallV (W := YVec P 2) (volume : Measure ℝ) (slotNorms u) Λ := hsmall
  have hhull' : ∀ β, Interp.InCornerNbhd (Rof u) β →
      Interp.VHullBound (W := YVec P 2) (volume : Measure ℝ) (slotNorms u) Λ β K := hhull
  have hm₁ : Measurable (F₁ : ℝ → YVec P 2) := hb₁.1
  have hm₂ : Measurable (F₂ : ℝ → YVec P 2) := hb₂.1
  have hm₃ : Measurable (fun x => slotNorms u 2 (F₃ x)) :=
    (measurable_yNorm_fun (slotExp u 2)).comp hb₃.1
  have key := @Interp.v17_abstract ℝ (YVec P 2) (YVec P u.conjExponent) _ _ _
    (instMeasurableSpaceYVec P 2) _ _ _ (instMeasurableSpaceYVec P u.conjExponent) _ _ volume _ _
    (slotNorms u) Λ K (Rof u) (fun e v => yPair e.val v.val) B hν0 hν1 hν2 hR hK hsub' hsmall' hpr hhull'
    (fun f₁ f₂ h hf₁ hf₂ hh => hdom f₁ f₂ h (conv 0 _ hf₁) (conv 1 _ hf₂) (conv 2 _ hh))
    (fun f₁ f₂ h₁ h₂ => hbil.meas f₁ f₂ (conv 0 _ h₁) (conv 1 _ h₂))
    (fun f f' g h₁ h₁' h₂ => hbil.add₁ f f' g (conv 0 _ h₁) (conv 0 _ h₁') (conv 1 _ h₂))
    (fun c f g h₁ h₂ => hbil.smul₁ (c : ℂ) f g (conv 0 _ h₁) (conv 1 _ h₂))
    (fun f g g' h₁ h₂ h₂' => hbil.add₂ f g g' (conv 0 _ h₁) (conv 1 _ h₂) (conv 1 _ h₂'))
    (fun c f g h₁ h₂ => hbil.smul₂ (c : ℂ) f g (conv 0 _ h₁) (conv 1 _ h₂))
    F₁ F₂ F₃ hm₁ hm₂
    (by rw [eLpNorm_yvec_eq (by norm_num) hm₁]; exact hf₁)
    (by rw [eLpNorm_yvec_eq (by norm_num) hm₂]; exact hf₂)
    hm₃.aestronglyMeasurable
    (fun s₁ s₂ hbd₁ hbd₂ hl₁ hl₂ => by
      have h := hbil.cont F₁ F₂ (fun j => ⇑(s₁ j)) (fun j => ⇑(s₂ j)) hb₁ hb₂
        (fun n => simple_bdd (s₁ n)) (fun n => simple_bdd (s₂ n))
        (fun n x => by
          calc yNorm 2 ((s₁ n x).val) = ‖s₁ n x‖ := (YVec.norm_eq (by norm_num) _).symm
            _ ≤ 2 * ‖YVec.mk 2 (F₁ x)‖ := hbd₁ n x
            _ = 2 * yNorm 2 (F₁ x) := by rw [YVec.norm_eq (by norm_num) (YVec.mk 2 (F₁ x))])
        (fun n x => by
          calc yNorm 2 ((s₂ n x).val) = ‖s₂ n x‖ := (YVec.norm_eq (by norm_num) _).symm
            _ ≤ 2 * ‖YVec.mk 2 (F₂ x)‖ := hbd₂ n x
            _ = 2 * yNorm 2 (F₂ x) := by rw [YVec.norm_eq (by norm_num) (YVec.mk 2 (F₂ x))])
        (fun x => (YVec.continuous_val.tendsto _).comp (hl₁ x))
        (fun x => (YVec.continuous_val.tendsto _).comp (hl₂ x))
      exact h.mono fun x hx => (YVec.continuous_mk.tendsto _).comp hx)
  rw [eLpNorm_yvec_eq (by norm_num) hm₁, eLpNorm_yvec_eq (by norm_num) hm₂] at key
  exact key

end PrimeBHT.TimeFrequency.X2
