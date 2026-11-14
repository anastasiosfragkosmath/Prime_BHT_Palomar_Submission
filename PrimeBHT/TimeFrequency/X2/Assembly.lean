module

public import PrimeBHT.TimeFrequency.X2.Classes
public import PrimeBHT.TimeFrequency.X2.Collections
public import PrimeBHT.TimeFrequency.X2.V16.Defs
public import PrimeBHT.TimeFrequency.X2.ModelOp
public import PrimeBHT.TimeFrequency.X2.V17
public import PrimeBHT.TimeFrequency.X2.BandLimited
import PrimeBHT.Interface.X2Checks

/-!
# X2, node V18: the type-level assembly (V16 + V17 + V05 + V03 ⇒ the frozen statement)

Promoted from `drafts/x2-interface/{85-V05-V18,90-Assembly}.lean.txt`.  Hypotheses (Prop definitions, NOT proved
here): `V16Statement` (`X2/V16/Defs.lean`) and `DiscretizationStatement` (V05, below).  Proved: `V17Statement`
(`X2/V17.lean`), the structural lemmas of the model operator (`X2/ModelOp.lean`), the band-limited reduction V03
(`X2/BandLimited.lean`).

## Final statements (namespace `PrimeBHT.TimeFrequency.X2`)

* `ModelBoundStatement`: the uniform bound of the model forms of window-full collections of rank-1 box sets on
  continuous bounded `L² × L² × L^∞` functions;
* `DiscretizationStatement` (V04 + V05, transfer form): a uniform model bound gives the band-limited X2 bound with
  constant `C_d(A) · C₀`;
* `modelBound_of_v16_v17 : V16Statement → V17Statement → ModelBoundStatement`;
* `bandLimited_of_modelBound : ModelBoundStatement → DiscretizationStatement → X2BandLimited`;
* `x2Statement_of_chain : V16Statement → V17Statement → DiscretizationStatement → (X2BandLimited → X2Statement) →
  X2Statement`;
* `x2Statement_of_v16_discretization : V16Statement → DiscretizationStatement → X2Statement`
  (with the proved `v17` and `x2Statement_of_bandLimited`).

`PrimeBHT.TransferenceAssembly.X2Statement` is the type of the frozen `PrimeBHT.Statements.t_finiteBV` (checked by
`scripts/interface_check.sh`; this file does not import the frozen module).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate ContDiff
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

theorem FormBound.nonneg {P : ℕ} [NeZero P] {u : ℝ} (hu : 1 < u) {T : Form P} {CT : ℝ}
    (h : FormBound u T CT) : 0 ≤ CT :=
  PrimeBHT.Interface.X2.nonneg_of_bound T (by linarith) h

/-- The bound on the model forms that V16 + V17 deliver (consumed by V05's transfer). -/
def ModelBoundStatement : Prop :=
  ∀ u : ℝ, 1 < u → ∀ 𝔭 : Params, V16Params u 𝔭 → ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ (P : ℕ) [NeZero P] (T : Form P) (CT : ℝ), FormBound u T CT →
    ∀ (Qs : Set Box), IsRankOne 𝔭.J Qs → ∀ (Ps : Finset TriTile), IsWindowFull Qs Ps →
    ∀ (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ), IsModelData 𝔭 Ps χ m →
    ∀ F₁ F₂ F₃ : ℝ → ZMod P → ℂ, Continuous F₁ → Continuous F₂ → Continuous F₃ →
      IsBddV F₁ → IsBddV F₂ → IsBddV F₃ →
      eLpNorm (fun x => yNorm 2 (F₁ x)) 2 volume < ⊤ → eLpNorm (fun x => yNorm 2 (F₂ x)) 2 volume < ⊤ →
        ‖modelForm T Ps χ m F₁ F₂ F₃‖ₑ ≤ ENNReal.ofReal (C₀ * CT) *
          eLpNorm (fun x => yNorm 2 (F₁ x)) 2 volume * eLpNorm (fun x => yNorm 2 (F₂ x)) 2 volume *
          eLpNorm (fun x => yNorm u (F₃ x)) ⊤ volume

/-- **V04 + V05 (discretization), in transfer form.**  For every decay/derivative order there is an
admissible class `𝔭` that carries the tree profile (`ProfileOK 𝔭`, needed by the tree lemma V15) such that, for every `u` and every symbol bound sequence `A`, a uniform bound `C₀` on the
model forms of window-full collections of rank-1 box sets with data in `𝔭` (on continuous bounded
`L² × L² × L^∞` functions) gives the band-limited X2 bound with constant `C_d(A) · C₀`.  A hypothesis (V05 is not
proved in this file). -/
def DiscretizationStatement : Prop :=
  ∀ N D : ℕ, ∃ 𝔭 : Params, 𝔭.Admissible ∧ N ≤ 𝔭.N ∧ D ≤ 𝔭.D ∧ ProfileOK 𝔭 ∧
    ∀ u : ℝ, 1 < u → ∀ A : ℕ → ℝ, ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ C₀ : ℝ, 0 ≤ C₀ →
      (∀ (P : ℕ) [NeZero P] (T : Form P) (CT : ℝ), FormBound u T CT →
        ∀ (Qs : Set Box), IsRankOne 𝔭.J Qs → ∀ (Ps : Finset TriTile), IsWindowFull Qs Ps →
        ∀ (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ), IsModelData 𝔭 Ps χ m →
        ∀ F₁ F₂ F₃ : ℝ → ZMod P → ℂ, Continuous F₁ → Continuous F₂ → Continuous F₃ →
          IsBddV F₁ → IsBddV F₂ → IsBddV F₃ →
          eLpNorm (fun x => yNorm 2 (F₁ x)) 2 volume < ⊤ →
          eLpNorm (fun x => yNorm 2 (F₂ x)) 2 volume < ⊤ →
            ‖modelForm T Ps χ m F₁ F₂ F₃‖ₑ ≤ ENNReal.ofReal (C₀ * CT) *
              eLpNorm (fun x => yNorm 2 (F₁ x)) 2 volume *
              eLpNorm (fun x => yNorm 2 (F₂ x)) 2 volume *
              eLpNorm (fun x => yNorm u (F₃ x)) ⊤ volume) →
      ∀ (P : ℕ) [NeZero P] (T : Form P) (m : ℝ → ℂ), ContDiffOn ℝ ∞ m {0}ᶜ →
        (∀ j : ℕ, ∀ t : ℝ, t ≠ 0 → |t| ^ j * ‖iteratedDeriv j m t‖ ≤ A j) →
        ∀ CT : ℝ, FormBound u T CT → ∀ f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ),
          (∀ a, HasCompactSupport (𝓕 (⇑(f₁ a)))) → (∀ a, HasCompactSupport (𝓕 (⇑(f₂ a)))) →
          (∀ a, HasCompactSupport (𝓕 (⇑(f₃ a)))) →
            ‖multiplierForm m T f₁ f₂ f₃‖ₑ ≤ ENNReal.ofReal (Cd * C₀ * CT) *
              eLpNorm (fun x : ℝ => yNorm 2 (tensorFun f₁ x)) 2 volume *
              eLpNorm (fun x : ℝ => yNorm 2 (tensorFun f₂ x)) 2 volume *
              eLpNorm (fun x : ℝ => yNorm u (tensorFun f₃ x)) ⊤ volume

/-- **(a)** `V16 ∧ V17 ⇒ ModelBound` (with the structural facts of the model operator). -/
theorem modelBound_of_v16_v17 (h16 : V16Statement) (h17 : V17Statement) : ModelBoundStatement := by
  intro u hu 𝔭 h𝔭
  obtain ⟨C, hC0, hC⟩ := h16 u hu 𝔭 h𝔭
  obtain ⟨C₁, hC₁0, hV⟩ := h17 u hu
  refine ⟨C₁ * C, mul_nonneg hC₁0 hC0, ?_⟩
  intro P _ T CT hT Qs hQ Ps hPs χ m hd F₁ F₂ F₃ hc₁ hc₂ hc₃ hb₁ hb₂ hb₃ hf₁ hf₂
  have hCT : 0 ≤ CT := FormBound.nonneg hu hT
  have key := hV P (fun h => ‖modelForm T Ps χ m (h 0) (h 1) (h 2)‖) (modelOp T Ps χ m) (C * CT)
    (mul_nonneg hC0 hCT) (isSubadditiveV_modelForm hu 𝔭 h𝔭.1 T Ps χ m hd)
    (isSmallV_modelForm hu 𝔭 h𝔭.1 T Ps χ m hd) (isBilinOpV_modelOp 𝔭 h𝔭.1 T Ps χ m hd)
    (isDominatedV_modelOp 𝔭 h𝔭.1 T Ps χ m hd)
    (fun β hβ => hC P T CT hT Qs hQ Ps hPs χ m hd β hβ) F₁ F₂ F₃ hc₁ hc₂ hc₃ hb₁ hb₂ hb₃ hf₁ hf₂
  rw [modelForm_eq_integral_yPair 𝔭 h𝔭.1 T Ps χ m hd F₁ F₂ F₃ hb₁ hb₂ hb₃]
  calc ‖∫ x, yPair (modelOp T Ps χ m F₁ F₂ x) (F₃ x)‖ₑ ≤ _ := key
    _ = _ := by rw [mul_assoc C₁ C CT]

/-- **(b), first half**: `ModelBound ∧ V05 ⇒ X2BandLimited`. -/
theorem bandLimited_of_modelBound (hM : ModelBoundStatement) (hD : DiscretizationStatement) :
    X2BandLimited := by
  intro u hu A
  obtain ⟨𝔭, h𝔭, hN, hDD, hprof, hrest⟩ := hD (v16Decay u) (v16Decay u)
  obtain ⟨C₀, hC₀0, hC₀⟩ := hM u hu 𝔭 ⟨h𝔭, hN, hDD, hprof⟩
  obtain ⟨Cd, hCd0, htrans⟩ := hrest u hu A
  refine ⟨Cd * C₀, mul_nonneg hCd0 hC₀0, ?_⟩
  intro P _ T m hm hA CT hT f₁ f₂ f₃ hs₁ hs₂ hs₃
  exact htrans C₀ hC₀0 (fun P _ T CT hT Qs hQ Ps hPs χ m hd F₁ F₂ F₃ hc₁ hc₂ hc₃ hb₁ hb₂ hb₃ hf₁ hf₂ =>
    hC₀ P T CT hT Qs hQ Ps hPs χ m hd F₁ F₂ F₃ hc₁ hc₂ hc₃ hb₁ hb₂ hb₃ hf₁ hf₂) P T m hm hA CT hT
    f₁ f₂ f₃ hs₁ hs₂ hs₃

/-- **(b)**: the chain closes on the type of the frozen statement. -/
theorem x2Statement_of_chain (h16 : V16Statement) (h17 : V17Statement)
    (hD : DiscretizationStatement) (h03 : X2BandLimited → PrimeBHT.TransferenceAssembly.X2Statement) :
    PrimeBHT.TransferenceAssembly.X2Statement :=
  h03 (bandLimited_of_modelBound (modelBound_of_v16_v17 h16 h17) hD)

/-- **The assembly.**  `V16 ∧ V05 ⇒ X2Statement` (= the type of the frozen `t_finiteBV`), with the PROVED `V17`
(`v17`) and the proved band-limited reduction V03 (`x2Statement_of_bandLimited`). -/
theorem x2Statement_of_v16_discretization (h16 : V16Statement) (hD : DiscretizationStatement) :
    PrimeBHT.TransferenceAssembly.X2Statement :=
  x2Statement_of_chain h16 v17 hD x2Statement_of_bandLimited

end PrimeBHT.TimeFrequency.X2
