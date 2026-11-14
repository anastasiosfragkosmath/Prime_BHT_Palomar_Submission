module

public import PrimeBHT.Frozen.TriValid
public import PrimeBHT.Frozen.TriIdx
public import PrimeBHT.Frozen.TimeInt
public import PrimeBHT.Frozen.FreqNum
public import PrimeBHT.Frozen.FreqInt
public import PrimeBHT.Frozen.IntervalCentre
public import PrimeBHT.Frozen.IsAdapted
public import PrimeBHT.Frozen.Pairing
public import PrimeBHT.Frozen.TriForm
public import PrimeBHT.TimeFrequency.Interp.Restricted.Operator
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# The model form `Λ_P` and the model operator `Π_P` against the abstract hypotheses of R6a/R6b

Blueprint `docs/x1-blueprint.md`, the notation block of R6 and the plug-in of the abstract chain
(`PrimeBHT.TimeFrequency.Interp.Restricted.{Form, Operator}`) into the concrete form of the frozen
statement M1(ε): `Λ_P = PrimeBHT.Statements.triForm P φ` on `(ℝ, volume)` and
`Π_P(f₁, f₂) = Σ_{t ∈ P} |I_t|^{-1/2} ⟨f₁, φ_{t,1}⟩ ⟨f₂, φ_{t,2}⟩ φ_{t,3}` (slots `0, 1, 2` here).

None of this uses M1(ε): the hypotheses are those of the abstract chain, proved for `triForm` from
integrability of the packets (hence from `IsAdapted`).

## Results

* `isSubadditive_triForm` / `_of_adapted`: `IsSubadditive (triForm P φ)` (needs `Integrable (φ t k)`,
  so that `pairing` is additive on bounded measurable inputs; without integrability the Bochner
  integral is `0` and additivity can fail).
* `isSmall_triForm` / `_of_adapted`: `IsSmall volume (triForm P φ)` with
  `A = Σ_{t ∈ P} |I_t|^{-1/2} B_t³` where `‖φ t k‖_∞ ≤ B_t`; for adapted packets `B_t = |I_t|^{-1/2}`
  (`IsAdapted.norm_le`, case `n = 0`), so `A = Σ_t |I_t|^{-2}` (`|I_t| = 2^{s}`).
* `isDominatedConj_modelOp` / `_of_adapted`: for bounded measurable `f₁ f₂ h`,
  `‖∫ Π_P(f₁,f₂) · conj h‖ ≤ Λ_P(f₁, f₂, h)`, the hypothesis `IsDominatedConj` of `Operator.lean`
  (conjugate pairing, the blueprint's `⟨Π, h⟩` with `⟨h, φ⟩ = ∫ h conj φ`).  The bilinear pairing
  `IsDominated volume Π_P (conjForm Λ_P)` follows (`isDominated_modelOp`), and `conjForm Λ_P` has
  the same `IsSubadditive`, `IsSmall`, `HullBound` hypotheses by `Operator.lean`'s `.conjForm` lemmas.
* `measurable_modelOp`: `hmeas` of `Operator.lean` (the packets are continuous).
-/

@[expose] public section

namespace PrimeBHT.TimeFrequency.Interp.Hull

open MeasureTheory Function Finset
open PrimeBHT.Statements
open PrimeBHT.TimeFrequency.Interp.Restricted
open scoped ComplexConjugate

/-! ### Tiles: the weight `|I_t|^{-1/2}` and the model operator -/

/-- The weight `|I_t|^{-1/2}` of the tri-tile `t`. -/
noncomputable def tileWeight (t : ℤ × ℤ × ℤ) : ℝ := (volume (timeInt t)).toReal ^ (-(1 : ℝ) / 2)

lemma triForm_eq (P : Finset (ℤ × ℤ × ℤ)) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ)
    (h : Fin 3 → ℝ → ℂ) :
    triForm P φ h = ∑ t ∈ P, tileWeight t * ∏ k, ‖pairing (h k) (φ t k)‖ := rfl

/-- The model operator `Π_P(f₁, f₂) = Σ_{t ∈ P} |I_t|^{-1/2} ⟨f₁, φ_{t,0}⟩ ⟨f₂, φ_{t,1}⟩ φ_{t,2}`. -/
noncomputable def modelOp (P : Finset (ℤ × ℤ × ℤ)) (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ)
    (f₁ f₂ : ℝ → ℂ) : ℝ → ℂ :=
  fun x => ∑ t ∈ P, ((tileWeight t : ℝ) : ℂ) * (pairing f₁ (φ t 0) * pairing f₂ (φ t 1)) *
    φ t 2 x

lemma volume_timeInt (t : ℤ × ℤ × ℤ) : volume (timeInt t) = ENNReal.ofReal ((2 : ℝ) ^ t.1) := by
  unfold timeInt
  rw [Real.volume_Ico]
  congr 1
  ring

lemma toReal_volume_timeInt (t : ℤ × ℤ × ℤ) : (volume (timeInt t)).toReal = (2 : ℝ) ^ t.1 := by
  rw [volume_timeInt, ENNReal.toReal_ofReal (by positivity)]

lemma tileWeight_nonneg (t : ℤ × ℤ × ℤ) : 0 ≤ tileWeight t :=
  Real.rpow_nonneg ENNReal.toReal_nonneg _

/-! ### Adapted packets are integrable, continuous and bounded by `|I|^{-1/2}` -/

lemma integrable_of_isAdapted {N : ℕ} {I ω : Set ℝ} {φ : ℝ → ℂ} (h : IsAdapted N I ω φ) :
    Integrable φ := h.2.1

lemma continuous_of_isAdapted {N : ℕ} {I ω : Set ℝ} {φ : ℝ → ℂ} (h : IsAdapted N I ω φ) :
    Continuous φ := h.1.continuous

lemma measurable_of_isAdapted {N : ℕ} {I ω : Set ℝ} {φ : ℝ → ℂ} (h : IsAdapted N I ω φ) :
    Measurable φ := (continuous_of_isAdapted h).measurable

/-- An adapted packet is bounded by `|I|^{-1/2}` (the case `n = 0` of the definition, the
demodulation having modulus one). -/
lemma norm_le_of_isAdapted {N : ℕ} {I ω : Set ℝ} {φ : ℝ → ℂ} (h : IsAdapted N I ω φ) (x : ℝ) :
    ‖φ x‖ ≤ (volume I).toReal ^ (-(1 : ℝ) / 2) := by
  have h0 := h.2.2.2 0 (by norm_num) x
  rw [iteratedDeriv_zero, norm_mul] at h0
  have hn : ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (intervalCentre ω : ℂ) * (x : ℂ)))‖ =
      1 := by
    rw [Complex.norm_exp]
    simp
  rw [hn, one_mul] at h0
  refine h0.trans ?_
  have hbase : (1 : ℝ) ≤ 1 + |x - intervalCentre I| / (volume I).toReal :=
    le_add_of_nonneg_right (div_nonneg (abs_nonneg _) ENNReal.toReal_nonneg)
  have hle : (1 + |x - intervalCentre I| / (volume I).toReal) ^ (-(N : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase (by simp)
  have hnn : 0 ≤ (volume I).toReal ^ (-((0 : ℕ) : ℝ) - 1 / 2) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  have heq : (volume I).toReal ^ (-((0 : ℕ) : ℝ) - 1 / 2) = (volume I).toReal ^ (-(1 : ℝ) / 2) := by
    congr 1
    push_cast
    ring
  rw [heq] at hnn ⊢
  calc (volume I).toReal ^ (-(1 : ℝ) / 2) *
        (1 + |x - intervalCentre I| / (volume I).toReal) ^ (-(N : ℝ))
      ≤ (volume I).toReal ^ (-(1 : ℝ) / 2) * 1 := mul_le_mul_of_nonneg_left hle hnn
    _ = _ := mul_one _

lemma norm_le_tileWeight_of_isAdapted {N : ℕ} {a b : ℤ} {k : Fin 3} {t : ℤ × ℤ × ℤ}
    {φ : ℝ → ℂ} (h : IsAdapted N (timeInt t) (freqInt a b k t) φ) (x : ℝ) :
    ‖φ x‖ ≤ tileWeight t :=
  norm_le_of_isAdapted h x

/-! ### The pairing -/

lemma integrable_mul_conj {φ f : ℝ → ℂ} (hφ : Integrable φ) (hf : IsBdd f) :
    Integrable (fun x => f x * (starRingEnd ℂ) (φ x)) := by
  obtain ⟨hm, M, hM⟩ := hf
  have hφ' : Integrable (fun x => (starRingEnd ℂ) (φ x)) :=
    Integrable.mono' hφ.norm
      (Complex.continuous_conj.comp_aestronglyMeasurable hφ.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by simp)
  exact hφ'.bdd_mul hm.aestronglyMeasurable (Filter.Eventually.of_forall hM)

lemma integrable_conj_mul {φ h : ℝ → ℂ} (hφ : Integrable φ) (hh : IsBdd h) :
    Integrable (fun x => φ x * (starRingEnd ℂ) (h x)) := by
  obtain ⟨hm, M, hM⟩ := hh
  exact hφ.mul_bdd (Complex.continuous_conj.comp_aestronglyMeasurable hm.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => by simpa using hM x)

lemma pairing_add {φ f g : ℝ → ℂ} (hφ : Integrable φ) (hf : IsBdd f) (hg : IsBdd g) :
    pairing (f + g) φ = pairing f φ + pairing g φ := by
  unfold pairing
  have : (fun x => (f + g) x * (starRingEnd ℂ) (φ x)) =
      fun x => f x * (starRingEnd ℂ) (φ x) + g x * (starRingEnd ℂ) (φ x) := by
    funext x
    simp only [Pi.add_apply, add_mul]
  rw [this]
  exact integral_add (integrable_mul_conj hφ hf) (integrable_mul_conj hφ hg)

lemma norm_pairing_le {φ h : ℝ → ℂ} {B : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ B) {S : Set ℝ}
    (hS : MeasurableSet S) (hSf : volume S < ⊤) (hh : DominatedBy S h) :
    ‖pairing h φ‖ ≤ B * (volume S).toReal := by
  unfold pairing
  have hint : Integrable (S.indicator fun _ : ℝ => B) :=
    (integrable_indicator_iff hS).2 (integrableOn_const hSf.ne)
  have hle := norm_integral_le_of_norm_le hint
    (f := fun x => h x * (starRingEnd ℂ) (φ x))
    (Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx, norm_mul, Complex.norm_conj]
        have h1 : ‖h x‖ ≤ 1 := by simpa [Set.indicator_of_mem hx] using hh x
        have hB : 0 ≤ B := (norm_nonneg _).trans (hφ x)
        calc ‖h x‖ * ‖φ x‖ ≤ 1 * B := mul_le_mul h1 (hφ x) (norm_nonneg _) zero_le_one
          _ = B := one_mul _
      · rw [Set.indicator_of_notMem hx, hh.eq_zero_of_notMem hx]
        simp)
  refine hle.trans (le_of_eq ?_)
  rw [integral_indicator_const _ hS, smul_eq_mul, mul_comm]
  rfl

lemma norm_pairing_swap {φ h : ℝ → ℂ} : ‖∫ x, φ x * (starRingEnd ℂ) (h x)‖ = ‖pairing h φ‖ := by
  unfold pairing
  have : (fun x => φ x * (starRingEnd ℂ) (h x)) =
      fun x => (starRingEnd ℂ) (h x * (starRingEnd ℂ) (φ x)) := by
    funext x
    simp only [map_mul, Complex.conj_conj]
    ring
  rw [this, integral_conj, Complex.norm_conj]

/-! ### `IsSubadditive` -/

lemma prod_norm_pairing_update (ψ : Fin 3 → ℝ → ℂ) (h : Fin 3 → ℝ → ℂ) (j : Fin 3)
    (u : ℝ → ℂ) :
    ∏ k, ‖pairing (update h j u k) (ψ k)‖ =
      ‖pairing u (ψ j)‖ * ∏ k ∈ univ.erase j, ‖pairing (h k) (ψ k)‖ := by
  rw [← Finset.mul_prod_erase univ (fun k => ‖pairing (update h j u k) (ψ k)‖) (mem_univ j)]
  congr 1
  · simp
  · exact Finset.prod_congr rfl fun k hk => by rw [update_of_ne (Finset.ne_of_mem_erase hk)]

theorem isSubadditive_triForm {P : Finset (ℤ × ℤ × ℤ)} {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hint : ∀ t ∈ P, ∀ k, Integrable (φ t k)) : IsSubadditive (triForm P φ) := by
  intro h j f g hh hf hg
  simp only [triForm_eq]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun t ht => ?_
  rw [prod_norm_pairing_update, prod_norm_pairing_update, prod_norm_pairing_update,
    pairing_add (hint t ht j) hf hg]
  have hw := tileWeight_nonneg t
  have hR : 0 ≤ ∏ k ∈ univ.erase j, ‖pairing (h k) (φ t k)‖ :=
    Finset.prod_nonneg fun _ _ => norm_nonneg _
  have key := norm_add_le (pairing f (φ t j)) (pairing g (φ t j))
  calc tileWeight t * (‖pairing f (φ t j) + pairing g (φ t j)‖ *
        ∏ k ∈ univ.erase j, ‖pairing (h k) (φ t k)‖)
      ≤ tileWeight t * ((‖pairing f (φ t j)‖ + ‖pairing g (φ t j)‖) *
        ∏ k ∈ univ.erase j, ‖pairing (h k) (φ t k)‖) := by gcongr
    _ = _ := by ring

theorem isSubadditive_triForm_of_adapted {P : Finset (ℤ × ℤ × ℤ)}
    {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {N : ℕ} {a b : ℤ}
    (hφ : ∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) :
    IsSubadditive (triForm P φ) :=
  isSubadditive_triForm fun t ht k => integrable_of_isAdapted (hφ t ht k)

/-! ### `IsSmall` -/

theorem isSmall_triForm {P : Finset (ℤ × ℤ × ℤ)} {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    {B : ℤ × ℤ × ℤ → ℝ} (hbd : ∀ t ∈ P, ∀ k x, ‖φ t k x‖ ≤ B t) :
    IsSmall volume (triForm P φ) := by
  refine ⟨∑ t ∈ P, tileWeight t * B t ^ 3, ?_, ?_⟩
  · exact Finset.sum_nonneg fun t ht => mul_nonneg (tileWeight_nonneg t)
      (pow_nonneg ((norm_nonneg _).trans (hbd t ht 0 0)) 3)
  · intro h S hSm hSf hhm hhd
    simp only [triForm_eq]
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun t ht => ?_
    have hB : 0 ≤ B t := (norm_nonneg _).trans (hbd t ht 0 0)
    have hw := tileWeight_nonneg t
    have hprod : ∏ k, ‖pairing (h k) (φ t k)‖ ≤ B t ^ 3 * ∏ k, (volume (S k)).toReal := by
      calc ∏ k, ‖pairing (h k) (φ t k)‖ ≤ ∏ k, (B t * (volume (S k)).toReal) :=
            Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) (fun k _ =>
              norm_pairing_le (hbd t ht k) (hSm k) (hSf k) (hhd k))
        _ = B t ^ 3 * ∏ k, (volume (S k)).toReal := by
            rw [Finset.prod_mul_distrib]
            simp
    calc tileWeight t * ∏ k, ‖pairing (h k) (φ t k)‖
        ≤ tileWeight t * (B t ^ 3 * ∏ k, (volume (S k)).toReal) := by gcongr
      _ = _ := by ring

theorem isSmall_triForm_of_adapted {P : Finset (ℤ × ℤ × ℤ)}
    {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {N : ℕ} {a b : ℤ}
    (hφ : ∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) :
    IsSmall volume (triForm P φ) :=
  isSmall_triForm (B := tileWeight) fun t ht k x => norm_le_tileWeight_of_isAdapted (hφ t ht k) x

/-! ### Domination of the model operator -/

theorem isDominatedConj_modelOp {P : Finset (ℤ × ℤ × ℤ)} {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hint : ∀ t ∈ P, ∀ k, Integrable (φ t k)) :
    IsDominatedConj volume (modelOp P φ) (triForm P φ) := by
  intro f₁ f₂ h hf₁ hf₂ hh
  set c : ℤ × ℤ × ℤ → ℂ := fun t =>
    ((tileWeight t : ℝ) : ℂ) * (pairing f₁ (φ t 0) * pairing f₂ (φ t 1)) with hc
  have hexp : (fun x => modelOp P φ f₁ f₂ x * (starRingEnd ℂ) (h x)) =
      fun x => ∑ t ∈ P, c t * (φ t 2 x * (starRingEnd ℂ) (h x)) := by
    funext x
    unfold modelOp
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun t _ => by simp only [hc]; ring
  have hint2 : ∀ t ∈ P, Integrable (fun x => c t * (φ t 2 x * (starRingEnd ℂ) (h x))) :=
    fun t ht => (integrable_conj_mul (hint t ht 2) hh).const_mul _
  rw [hexp, integral_finsetSum _ hint2]
  refine (norm_sum_le _ _).trans ?_
  simp only [triForm_eq]
  refine Finset.sum_le_sum fun t ht => ?_
  rw [integral_const_mul, norm_mul, norm_pairing_swap, Fin.prod_univ_three]
  simp only [hc, norm_mul, Complex.norm_real, Real.norm_of_nonneg (tileWeight_nonneg t)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  have e : Matrix.vecHead (Matrix.vecTail ![f₂, h]) = h := rfl
  rw [e]
  exact le_of_eq (by ring)

/-- The bilinear pairing `‖∫ Π_P(f₁, f₂) · h‖ ≤ Λ_P(f₁, f₂, conj h)` (the hypothesis `IsDominated` of
`Operator.lean`, for the form `conjForm Λ_P` with the third slot conjugated). -/
theorem isDominated_modelOp {P : Finset (ℤ × ℤ × ℤ)} {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hint : ∀ t ∈ P, ∀ k, Integrable (φ t k)) :
    IsDominated volume (modelOp P φ) (conjForm (triForm P φ)) :=
  (isDominatedConj_modelOp hint).conjForm

theorem isDominated_modelOp_of_adapted {P : Finset (ℤ × ℤ × ℤ)}
    {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {N : ℕ} {a b : ℤ}
    (hφ : ∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) :
    IsDominated volume (modelOp P φ) (conjForm (triForm P φ)) :=
  isDominated_modelOp fun t ht k => integrable_of_isAdapted (hφ t ht k)

/-! ### Measurability of the model operator -/

theorem measurable_modelOp {P : Finset (ℤ × ℤ × ℤ)} {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hmeas : ∀ t ∈ P, Measurable (φ t 2)) (f₁ f₂ : ℝ → ℂ) : Measurable (modelOp P φ f₁ f₂) := by
  unfold modelOp
  exact Finset.measurable_sum _ fun t ht => (hmeas t ht).const_mul _

theorem measurable_modelOp_of_adapted {P : Finset (ℤ × ℤ × ℤ)}
    {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ} {N : ℕ} {a b : ℤ}
    (hφ : ∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) (f₁ f₂ : ℝ → ℂ) :
    Measurable (modelOp P φ f₁ f₂) :=
  measurable_modelOp (fun t ht => measurable_of_isAdapted (hφ t ht 2)) f₁ f₂

end PrimeBHT.TimeFrequency.Interp.Hull
