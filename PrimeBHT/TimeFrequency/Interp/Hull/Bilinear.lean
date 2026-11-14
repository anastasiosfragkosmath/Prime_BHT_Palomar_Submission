module

public import PrimeBHT.TimeFrequency.Interp.Hull.ModelForm
import Mathlib.MeasureTheory.Function.SimpleFunc

/-!
# Homogeneity of `Λ_P` and bilinearity of `Π_P` (hypotheses of R6c)

The hypotheses of `PrimeBHT.TimeFrequency.Interp.Strong` that are not consequences of the abstract
hypotheses of `Restricted/*` (see the docstring of `Operator.lean`: "Homogeneity (`hhom`) and
bilinearity of `T` on simple functions (`hadd`, `hsmul`) are *not* consequences of the hypotheses
here and stay hypotheses of the consumer"), proved here for `Λ_P = triForm P φ` and
`Π_P = modelOp P φ`:

* `triForm_smul_first/second/third`: `Λ_P(c • f, g, h) = c Λ_P(f, g, h)` for `c ≥ 0` (all functions;
  no integrability needed since only norms of pairings enter), the `hhom₁/₂/₃` of R6c-II (for simple
  functions use `SimpleFunc.coe_smul`);
* `modelOp_add_first/second`, `modelOp_smul_first/second`: `Π_P(f + f', g) = Π_P(f, g) + Π_P(f', g)`
  and `Π_P(c • f, g) = c • Π_P(f, g)` (for `c : ℝ`), likewise in the second slot, for bounded
  measurable inputs and integrable packets (additivity of the Bochner integral needs
  integrability), and the same facts for `SimpleFunc`s in the exact shape of the hypotheses
  `hadd₁ hsmul₁ hadd₂ hsmul₂` of `eLpNorm_le_of_restrictedStrong`.
-/

@[expose] public section

namespace PrimeBHT.TimeFrequency.Interp.Hull

open MeasureTheory Function Finset
open PrimeBHT.Statements
open PrimeBHT.TimeFrequency.Interp.Restricted

lemma pairing_smul (c : ℝ) (f φ : ℝ → ℂ) : pairing (c • f) φ = (c : ℂ) * pairing f φ := by
  unfold pairing
  have : (fun x => (c • f) x * (starRingEnd ℂ) (φ x)) =
      fun x => c • (f x * (starRingEnd ℂ) (φ x)) := by
    funext x
    simp only [Pi.smul_apply, smul_mul_assoc]
  rw [this, integral_smul, Complex.real_smul]

/-- Positive homogeneity of `Λ_P` in the slot `j` (with `update`). -/
lemma triForm_update_smul (P : Finset (ℤ × ℤ × ℤ)) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ)
    (h : Fin 3 → ℝ → ℂ) (j : Fin 3) {c : ℝ} (hc : 0 ≤ c) (f : ℝ → ℂ) :
    triForm P φ (update h j (c • f)) = c * triForm P φ (update h j f) := by
  simp only [triForm_eq]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [prod_norm_pairing_update, prod_norm_pairing_update, pairing_smul, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hc]
  ring

lemma triForm_smul_first (P : Finset (ℤ × ℤ × ℤ)) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) {c : ℝ}
    (hc : 0 ≤ c) (f g h : ℝ → ℂ) :
    triForm P φ ![c • f, g, h] = c * triForm P φ ![f, g, h] := by
  have := triForm_update_smul P φ ![f, g, h] 0 hc f
  rwa [update_vec3_zero, update_vec3_zero] at this

lemma triForm_smul_second (P : Finset (ℤ × ℤ × ℤ)) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) {c : ℝ}
    (hc : 0 ≤ c) (f g h : ℝ → ℂ) :
    triForm P φ ![f, c • g, h] = c * triForm P φ ![f, g, h] := by
  have := triForm_update_smul P φ ![f, g, h] 1 hc g
  rwa [update_vec3_one, update_vec3_one] at this

lemma triForm_smul_third (P : Finset (ℤ × ℤ × ℤ)) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) {c : ℝ}
    (hc : 0 ≤ c) (f g h : ℝ → ℂ) :
    triForm P φ ![f, g, c • h] = c * triForm P φ ![f, g, h] := by
  have := triForm_update_smul P φ ![f, g, h] 2 hc h
  rwa [update_vec3_two, update_vec3_two] at this

/-! ### Bilinearity of `Π_P` -/

lemma modelOp_add_first {P : Finset (ℤ × ℤ × ℤ)} {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hint : ∀ t ∈ P, ∀ k, Integrable (φ t k)) {f f' : ℝ → ℂ} (hf : IsBdd f) (hf' : IsBdd f')
    (g : ℝ → ℂ) : modelOp P φ (f + f') g = modelOp P φ f g + modelOp P φ f' g := by
  funext x
  simp only [modelOp, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [pairing_add (hint t ht 0) hf hf']
  ring

lemma modelOp_add_second {P : Finset (ℤ × ℤ × ℤ)} {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hint : ∀ t ∈ P, ∀ k, Integrable (φ t k)) (f : ℝ → ℂ) {g g' : ℝ → ℂ} (hg : IsBdd g)
    (hg' : IsBdd g') : modelOp P φ f (g + g') = modelOp P φ f g + modelOp P φ f g' := by
  funext x
  simp only [modelOp, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [pairing_add (hint t ht 1) hg hg']
  ring

lemma modelOp_smul_first (P : Finset (ℤ × ℤ × ℤ)) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (c : ℝ)
    (f g : ℝ → ℂ) : modelOp P φ (c • f) g = c • modelOp P φ f g := by
  funext x
  simp only [modelOp, Pi.smul_apply, Complex.real_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [pairing_smul]
  ring

lemma modelOp_smul_second (P : Finset (ℤ × ℤ × ℤ)) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (c : ℝ)
    (f g : ℝ → ℂ) : modelOp P φ f (c • g) = c • modelOp P φ f g := by
  funext x
  simp only [modelOp, Pi.smul_apply, Complex.real_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [pairing_smul]
  ring

/-! ### The shapes of `eLpNorm_le_of_restrictedStrong` (simple functions) -/

lemma modelOp_hadd₁ {P : Finset (ℤ × ℤ × ℤ)} {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hint : ∀ t ∈ P, ∀ k, Integrable (φ t k)) (f f' g : SimpleFunc ℝ ℂ) :
    modelOp P φ ⇑(f + f') ⇑g = modelOp P φ ⇑f ⇑g + modelOp P φ ⇑f' ⇑g :=
  modelOp_add_first hint (IsBdd.of_simpleFunc f) (IsBdd.of_simpleFunc f') _

lemma modelOp_hadd₂ {P : Finset (ℤ × ℤ × ℤ)} {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hint : ∀ t ∈ P, ∀ k, Integrable (φ t k)) (f g g' : SimpleFunc ℝ ℂ) :
    modelOp P φ ⇑f ⇑(g + g') = modelOp P φ ⇑f ⇑g + modelOp P φ ⇑f ⇑g' :=
  modelOp_add_second hint _ (IsBdd.of_simpleFunc g) (IsBdd.of_simpleFunc g')

lemma modelOp_hsmul₁ (P : Finset (ℤ × ℤ × ℤ)) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (c : ℝ)
    (f g : SimpleFunc ℝ ℂ) : modelOp P φ ⇑(c • f) ⇑g = c • modelOp P φ ⇑f ⇑g := by
  rw [SimpleFunc.coe_smul]
  exact modelOp_smul_first P φ c _ _

lemma modelOp_hsmul₂ (P : Finset (ℤ × ℤ × ℤ)) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (c : ℝ)
    (f g : SimpleFunc ℝ ℂ) : modelOp P φ ⇑f ⇑(c • g) = c • modelOp P φ ⇑f ⇑g := by
  rw [SimpleFunc.coe_smul]
  exact modelOp_smul_second P φ c _ _

end PrimeBHT.TimeFrequency.Interp.Hull
