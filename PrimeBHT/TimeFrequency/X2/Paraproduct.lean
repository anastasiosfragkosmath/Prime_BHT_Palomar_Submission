module

public import PrimeBHT.TimeFrequency.X2.Paraproduct.General

/-!
# X2, node V14: the paraproduct with an arbitrary trilinear form `Π` (decoupling route)

The inequality (PI) of `docs/audits/X2-V14-route-check.md`, fully proved (no placeholder, no new axiom) in
`X2/Paraproduct/{Symbols,Tensor,MaxBound,Estimates,Schwartz,General}.lean`:

* `paraproduct` (`General.lean`): the draft theorem of `drafts/x2-interface/05-V13-V15-Tree.lean.txt`, with the
  symbols anchored at a real `A > 0` (V13 route check §4 step 4; constant uniform in `A`), `IsLowSymbol A J a₀ j` in
  slot 1, `IsLPSymbol A J a₀ j` in slots 2 and 3, the draft's data class (measurable, `yNorm 2` bounded and
  integrable) and the right side as a product of mixed norms `mixedENorm q s F = ‖yNorm s ∘ F‖_{L^q}`;
* `paraproduct_draft`: the same with the right side `∏ k, eLpNorm (fun x => yNorm (s k) (g k x)) (ofReal (p k))`
  for any exponent function `s` with `s 0 = s 1 = 2`, `s 2 = u` (instantiate with `slotExp u`);
* `paraproduct_swap`: overlapping slot 2 (the two Hilbert slots exchanged);
* `paraproduct_schwartz`, `paraproduct_schwartz_swap` (`Schwartz.lean`): the same for tensor Schwartz data;
* the elementary cases `B = ∅, {3}` are the error estimate `enorm_sum_triL_le` (`Estimates.lean`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.X2.CZ

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- **V14 in the form of the draft**: the right side is `∏ k, eLpNorm (yNorm (s k) ∘ g k) (p k)` for an exponent
function `s` with `s 0 = s 1 = 2`, `s 2 = u` (the draft's `slotExp u`). -/
theorem paraproduct_draft (J a₀ : ℕ) (hJ : 1 ≤ J) (ha₀ : 3 ≤ a₀) {u : ℝ} (hu : 1 < u) (s : Fin 3 → ℝ)
    (hs0 : s 0 = 2) (hs1 : s 1 = 2) (hs2 : s 2 = u) {p : Fin 3 → ℝ} (hp : ∀ k, 1 < p k)
    (hpsum : ∑ k, 1 / p k = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 < A → ∀ (P : ℕ) [NeZero P] (T : Form P) (CT : ℝ), FormBound u T CT →
      ∀ (js : Finset ℤ) (ε : ℤ → ℂ), (∀ j, ‖ε j‖ ≤ 1) →
      ∀ (σ₁ σ₂ σ₃ : ℤ → ℝ → ℂ), (∀ j, IsLowSymbol A J a₀ j (σ₁ j)) → (∀ j, IsLPSymbol A J a₀ j (σ₂ j)) →
        (∀ j, IsLPSymbol A J a₀ j (σ₃ j)) →
      ∀ g : Fin 3 → ℝ → ZMod P → ℂ, (∀ k, Measurable (g k)) →
        (∀ k, ∃ B, ∀ x, yNorm 2 (g k x) ≤ B) → (∀ k, Integrable (fun x => yNorm 2 (g k x))) →
          ‖∑ j ∈ js, ε j * ∫ x, T (tmult (σ₁ j) (g 0) x) (tmult (σ₂ j) (g 1) x) (tmult (σ₃ j) (g 2) x)‖ₑ ≤
            ENNReal.ofReal (C * CT) *
              ∏ k, eLpNorm (fun x => yNorm (s k) (g k x)) (ENNReal.ofReal (p k)) volume := by
  obtain ⟨C, hC0, hC⟩ := paraproduct J a₀ hJ ha₀ hu hp hpsum
  refine ⟨C, hC0, fun A hA P _ T CT hT js ε hε σ₁ σ₂ σ₃ h1 h2 h3 g hm hb hi => ?_⟩
  have := hC A hA P T CT hT js ε hε σ₁ σ₂ σ₃ h1 h2 h3 g hm hb hi
  rw [Fin.prod_univ_three, hs0, hs1, hs2]
  exact this

end PrimeBHT.TimeFrequency.X2
