module

public import PrimeBHT.TimeFrequency.X2.Assembly
public import PrimeBHT.TimeFrequency.X2.Disc.Windows

/-!
# X2, node V05-6 (transfer): the model bound gives a bound on the UNLOCALIZED form of a finite set of boxes

`class_form_bound`: if the uniform model bound (the antecedent of `DiscretizationStatement`) holds with constant `C₀`
for the class `𝔭`, then for a finite set `Q` of boxes of a rank-1 set `Qs`, multipliers `m B k ∈ M_{ω_k(B)}(𝔭)` and
`η` with `IsEtaCut` and `tileCutoff ∈ X_I(𝔭)`,
`‖Σ_{B ∈ Q} ∫ Π(T_{m_{B,1}}F₁, T_{m_{B,2}}F₂, T_{m_{B,3}}F₃)(x) dx‖ ≤ 2 C₀ CT ‖F₁‖₂ ‖F₂‖₂ ‖F₃‖_u`
(provided the integrands are integrable).  Proof: the two window forms are model forms of window-full collections
(`isWindowFull_windowTiles`), and their sum tends to the unlocalized form (`tendsto_windows`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate ContDiff
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Disc

/-- The uniform model bound with constant `C₀` (the hypothesis of `DiscretizationStatement`, for fixed `u, 𝔭`). -/
def ModelBoundAt (u : ℝ) (𝔭 : Params) (C₀ : ℝ) : Prop :=
  ∀ (P : ℕ) [NeZero P] (T : Form P) (CT : ℝ), FormBound u T CT →
    ∀ (Qs : Set Box), IsRankOne 𝔭.J Qs → ∀ (Ps : Finset TriTile), IsWindowFull Qs Ps →
    ∀ (χ : TriTile → ℝ → ℝ) (m : TriTile → Fin 3 → ℝ → ℂ), IsModelData 𝔭 Ps χ m →
    ∀ F₁ F₂ F₃ : ℝ → ZMod P → ℂ, Continuous F₁ → Continuous F₂ → Continuous F₃ →
      IsBddV F₁ → IsBddV F₂ → IsBddV F₃ →
      eLpNorm (fun x => yNorm 2 (F₁ x)) 2 volume < ⊤ → eLpNorm (fun x => yNorm 2 (F₂ x)) 2 volume < ⊤ →
        ‖modelForm T Ps χ m F₁ F₂ F₃‖ₑ ≤ ENNReal.ofReal (C₀ * CT) *
          eLpNorm (fun x => yNorm 2 (F₁ x)) 2 volume * eLpNorm (fun x => yNorm 2 (F₂ x)) 2 volume *
          eLpNorm (fun x => yNorm u (F₃ x)) ⊤ volume

theorem isModelData_windowTiles {𝔭 : Params} {η : ℝ → ℝ} (hη : IsEtaCut 𝔭 η)
    (hX : ∀ s v : ℤ, InX 𝔭 s v (tileCutoff η s v)) (Q : Finset Box) (m : Box → Fin 3 → ℝ → ℂ)
    (hm : ∀ B ∈ Q, ∀ k, InMult 𝔭 B.scale (B.centre k) (m B k)) (W : ℤ × ℤ) :
    IsModelData 𝔭 (windowTiles Q W) (fun P => tileCutoff η P.box.scale P.pos) (fun P k => m P.box k) := by
  refine ⟨fun R hR => ⟨hX _ _, fun k => hm R.box (mem_windowTiles.1 hR).1 k⟩, ?_, η, hη, fun R _ => rfl⟩
  intro R _ R' _ h
  funext k
  show m R.box k = m R'.box k
  rw [h]

theorem class_form_bound {u : ℝ} {𝔭 : Params} {C₀ : ℝ} (hM : ModelBoundAt u 𝔭 C₀)
    {P : ℕ} [NeZero P] {T : Form P} {CT : ℝ} (hT : FormBound u T CT)
    {Qs : Set Box} (hQs : IsRankOne 𝔭.J Qs) (Q : Finset Box) (hQ : (↑Q : Set Box) ⊆ Qs)
    (m : Box → Fin 3 → ℝ → ℂ) (hm : ∀ B ∈ Q, ∀ k, InMult 𝔭 B.scale (B.centre k) (m B k))
    {η : ℝ → ℝ} (hη : IsEtaCut 𝔭 η) (hX : ∀ s v : ℤ, InX 𝔭 s v (tileCutoff η s v))
    {F₁ F₂ F₃ : ℝ → ZMod P → ℂ} (hc₁ : Continuous F₁) (hc₂ : Continuous F₂) (hc₃ : Continuous F₃)
    (hb₁ : IsBddV F₁) (hb₂ : IsBddV F₂) (hb₃ : IsBddV F₃)
    (hf₁ : eLpNorm (fun x => yNorm 2 (F₁ x)) 2 volume < ⊤)
    (hf₂ : eLpNorm (fun x => yNorm 2 (F₂ x)) 2 volume < ⊤)
    (hint : ∀ B ∈ Q, Integrable (fun x => T (tmult (m B 0) F₁ x) (tmult (m B 1) F₂ x) (tmult (m B 2) F₃ x))) :
    ‖∑ B ∈ Q, ∫ x, T (tmult (m B 0) F₁ x) (tmult (m B 1) F₂ x) (tmult (m B 2) F₃ x)‖ₑ ≤
      2 * (ENNReal.ofReal (C₀ * CT) * eLpNorm (fun x => yNorm 2 (F₁ x)) 2 volume *
        eLpNorm (fun x => yNorm 2 (F₂ x)) 2 volume * eLpNorm (fun x => yNorm u (F₃ x)) ⊤ volume) := by
  have hcont := hη.1
  have hnn := hη.2.1
  have hint1 := hη.2.2.1
  have hηint : Integrable η := by
    by_contra h
    rw [integral_undef h] at hint1
    exact zero_ne_one hint1
  set R := ENNReal.ofReal (C₀ * CT) * eLpNorm (fun x => yNorm 2 (F₁ x)) 2 volume *
    eLpNorm (fun x => yNorm 2 (F₂ x)) 2 volume * eLpNorm (fun x => yNorm u (F₃ x)) ⊤ volume with hR
  have hlim := tendsto_windows hcont hηint hnn hint1 Q
    (fun B x => T (tmult (m B 0) F₁ x) (tmult (m B 1) F₂ x) (tmult (m B 2) F₃ x)) hint
  have hbound : ∀ L : ℕ,
      ‖(∑ P' ∈ windowTiles Q ((L : ℤ), 0), ∫ x, (tileCutoff η P'.box.scale P'.pos x : ℂ) *
          T (tmult (m P'.box 0) F₁ x) (tmult (m P'.box 1) F₂ x) (tmult (m P'.box 2) F₃ x)) +
        (∑ P' ∈ windowTiles Q ((L : ℤ), -1), ∫ x, (tileCutoff η P'.box.scale P'.pos x : ℂ) *
          T (tmult (m P'.box 0) F₁ x) (tmult (m P'.box 1) F₂ x) (tmult (m P'.box 2) F₃ x))‖ₑ ≤ 2 * R := by
    intro L
    have hW : ∀ W : ℤ × ℤ, ‖∑ P' ∈ windowTiles Q W, ∫ x, (tileCutoff η P'.box.scale P'.pos x : ℂ) *
          T (tmult (m P'.box 0) F₁ x) (tmult (m P'.box 1) F₂ x) (tmult (m P'.box 2) F₃ x)‖ₑ ≤ R := by
      intro W
      exact hM P T CT hT Qs hQs (windowTiles Q W) (isWindowFull_windowTiles hQ W) _ _
        (isModelData_windowTiles hη hX Q m hm W) F₁ F₂ F₃ hc₁ hc₂ hc₃ hb₁ hb₂ hb₃
        hf₁ hf₂
    calc _ ≤ ‖∑ P' ∈ windowTiles Q ((L : ℤ), 0), _‖ₑ + ‖∑ P' ∈ windowTiles Q ((L : ℤ), -1), _‖ₑ :=
          enorm_add_le _ _
      _ ≤ R + R := add_le_add (hW _) (hW _)
      _ = 2 * R := (two_mul R).symm
  exact le_of_tendsto' hlim.enorm hbound

end PrimeBHT.TimeFrequency.X2.Disc
