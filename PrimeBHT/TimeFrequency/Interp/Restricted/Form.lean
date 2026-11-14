module

public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# R6a: Banach-range restricted type for an abstract trilinear-type form

Blueprint `docs/x1-blueprint.md`, node R6a (`RL.rt_form`), on top of the hull corollary M1-hull
(node C11).  The setting is abstract and independent of tiles: `α` is a measurable space with a
measure `μ` (for X1: `α = ℝ`, `μ = volume`), and `Λ : (Fin 3 → α → ℂ) → ℝ` is a "form" on triples
of complex functions (for X1: `Λ_P`, `Λ_P(h) = Σ_t |I_t|^{-1/2} Π_k |⟨h_k, φ_{t,k}⟩|`).

## Hypotheses (all named predicates)

* `IsBdd f`: `f` is measurable and bounded (the class of test functions).
* `DominatedBy E f`: `‖f x‖ ≤ 1_E x` for all `x`.
* `IsSubadditive Λ`: in each slot `j`, `Λ(h[j := f + g]) ≤ Λ(h[j := f]) + Λ(h[j := g])` for
  bounded measurable functions.  (Positive homogeneity is not needed for R6a, R6b.)
* `IsSmall μ Λ` (blueprint `Λ_small`): there is `A ≥ 0` with `Λ(h) ≤ A Π_i μ(S_i)` whenever
  `|h_i| ≤ 1_{S_i}`.  Satisfied by `Λ_P` for finite `P` and packets bounded by `B`, with
  `A = Σ_t |I_t|^{-1/2} Π_k ‖φ_{t,k}‖_∞` (as `|⟨h_k, φ⟩| ≤ ‖φ‖_∞ μ(S_k)`).  It is used only
  qualitatively (the final constant does not depend on `A`): to kill the remainder of the
  iteration and to treat null sets.
* `HullBound μ Λ a C` (M1-hull in the generalized restricted-type form at the exponent `a`): for all
  measurable `E_i` of finite positive measure and every index `j` of a largest set there is a
  measurable major subset `Ẽ ⊆ E_j`, `μ E_j ≤ 2 μ Ẽ` (depending on the sets only) such that
  `Λ(h) ≤ C Π_i μ(E_i)^{a_i}` for measurable `h` with `|h_i| ≤ 1_{E_i}` (`i ≠ j`),
  `|h_j| ≤ 1_{Ẽ}`.  Measures enter through `(μ E).toReal`.

## Main result

`restrictedType_of_hullBound` (R6a): for `a_i ≥ m > 0`, `Σ a_i = 1`, `0 ≤ C`, `IsSubadditive Λ`,
`IsSmall μ Λ`, `HullBound μ Λ a C`, for all measurable `E_i` of finite measure and measurable `h_i`
with `|h_i| ≤ 1_{E_i}`: `Λ(h) ≤ C / (1 - 2^{-m}) Π_i μ(E_i)^{a_i}` (so `m = min a_i` gives the
blueprint's `C'_a = C_a/(1 - 2^{-min a_i})`).

Proof (blueprint step 1-4, simplified): the iteration on the major subsets is run for `K` steps
as an induction on `K` over *all* states `(S, h)`, with the bound
`Λ(h) ≤ C Q(S) Σ_{k<K} q^k + A ((5/6)^K L(S))^3`, `q = 2^{-m}`, `Q(S) = Π μ(S_i)^{a_i}`,
`L(S) = Σ μ(S_i)`.  This replaces the blueprint's counting of halvings by two one-step facts:
`Q(S') ≤ q Q(S)` (the halved slot has `a_j ≥ m`) and `L(S') ≤ (5/6) L(S)` (the largest of three
sets has `μ ≥ L/3` and loses at least half of it).  The latter replaces the blueprint's step 3
(`M_{k+3} ≤ M_k/2`) and gives the explicit remainder `A (5/6)^{3K} L^3 → 0` from `IsSmall`.
If some `S_i` is null, `IsSmall` gives `Λ(h) ≤ 0` directly, so M1-hull (stated for positive
measures) is never invoked on null sets; this is the only place where the abstract setting needs
more than the blueprint (the blueprint does not treat null `S_i^{(k)}`).
-/

@[expose] public section

namespace PrimeBHT.TimeFrequency.Interp.Restricted

open MeasureTheory Function Finset
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- `‖f x‖ ≤ 1_E x` for all `x`. -/
def DominatedBy (E : Set α) (f : α → ℂ) : Prop :=
  ∀ x, ‖f x‖ ≤ E.indicator (fun _ => (1 : ℝ)) x

/-- The class of test functions: measurable and bounded. -/
def IsBdd (f : α → ℂ) : Prop :=
  Measurable f ∧ ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M

/-- `Λ` is subadditive in each slot, on bounded measurable functions. -/
def IsSubadditive (Λ : (Fin 3 → α → ℂ) → ℝ) : Prop :=
  ∀ (h : Fin 3 → α → ℂ) (j : Fin 3) (f g : α → ℂ), (∀ i, IsBdd (h i)) → IsBdd f → IsBdd g →
    Λ (update h j (f + g)) ≤ Λ (update h j f) + Λ (update h j g)

/-- Blueprint `Λ_small`: `Λ(h) ≤ A Π_i μ(S_i)` for `|h_i| ≤ 1_{S_i}`. -/
def IsSmall (μ : Measure α) (Λ : (Fin 3 → α → ℂ) → ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ (h : Fin 3 → α → ℂ) (S : Fin 3 → Set α), (∀ i, MeasurableSet (S i)) →
    (∀ i, μ (S i) < ∞) → (∀ i, Measurable (h i)) → (∀ i, DominatedBy (S i) (h i)) →
    Λ h ≤ A * ∏ i, (μ (S i)).toReal

/-- M1-hull at the exponent `a` with constant `C` (generalized restricted type, major subset in
a largest set). -/
def HullBound (μ : Measure α) (Λ : (Fin 3 → α → ℂ) → ℝ) (a : Fin 3 → ℝ) (C : ℝ) : Prop :=
  ∀ E : Fin 3 → Set α, (∀ i, MeasurableSet (E i)) → (∀ i, 0 < μ (E i)) → (∀ i, μ (E i) < ∞) →
    ∀ j : Fin 3, (∀ i, μ (E i) ≤ μ (E j)) →
      ∃ Et : Set α, MeasurableSet Et ∧ Et ⊆ E j ∧ μ (E j) ≤ 2 * μ Et ∧
        ∀ h : Fin 3 → α → ℂ, (∀ i, Measurable (h i)) → (∀ i, i ≠ j → DominatedBy (E i) (h i)) →
          DominatedBy Et (h j) → Λ h ≤ C * ∏ i, (μ (E i)).toReal ^ a i

/-- `Q(S) = Π_i μ(S_i)^{a_i}`. -/
noncomputable def measProd (μ : Measure α) (a : Fin 3 → ℝ) (S : Fin 3 → Set α) : ℝ :=
  ∏ i, (μ (S i)).toReal ^ a i

/-- `L(S) = Σ_i μ(S_i)`. -/
def measSum (μ : Measure α) (S : Fin 3 → Set α) : ℝ :=
  ∑ i, (μ (S i)).toReal

lemma measProd_nonneg (μ : Measure α) (a : Fin 3 → ℝ) (S : Fin 3 → Set α) :
    0 ≤ measProd μ a S :=
  Finset.prod_nonneg fun _ _ => Real.rpow_nonneg ENNReal.toReal_nonneg _

lemma measSum_nonneg (μ : Measure α) (S : Fin 3 → Set α) : 0 ≤ measSum μ S :=
  Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg

omit [MeasurableSpace α] in
lemma DominatedBy.measurable_indicator_of_subset {E F : Set α} {f : α → ℂ}
    (hf : DominatedBy E f) (hF : F ⊆ E) : DominatedBy F (F.indicator f) := by
  intro x
  by_cases hx : x ∈ F
  · have := hf x
    simpa [Set.indicator_of_mem hx, Set.indicator_of_mem (hF hx)] using this
  · simp [Set.indicator_of_notMem hx]

omit [MeasurableSpace α] in
lemma DominatedBy.eq_zero_of_notMem {E : Set α} {f : α → ℂ} (hf : DominatedBy E f) {x : α}
    (hx : x ∉ E) : f x = 0 := by
  have := hf x
  rw [Set.indicator_of_notMem hx] at this
  exact norm_le_zero_iff.1 this

lemma DominatedBy.isBdd {E : Set α} {f : α → ℂ} (hf : DominatedBy E f) (hm : Measurable f) :
    IsBdd f :=
  ⟨hm, 1, fun x => (hf x).trans (Set.indicator_le_self' (fun _ _ => zero_le_one) x)⟩

lemma IsBdd.indicator {f : α → ℂ} (hf : IsBdd f) {F : Set α} (hF : MeasurableSet F) :
    IsBdd (F.indicator f) := by
  obtain ⟨hm, M, hM⟩ := hf
  refine ⟨hm.indicator hF, M, fun x => ?_⟩
  by_cases hx : x ∈ F
  · simpa [Set.indicator_of_mem hx] using hM x
  · simp only [Set.indicator_of_notMem hx, norm_zero]
    exact (norm_nonneg _).trans (hM x)

lemma measurable_update_fin {h : Fin 3 → α → ℂ} (hh : ∀ i, Measurable (h i)) (j : Fin 3)
    {f : α → ℂ} (hf : Measurable f) : ∀ i, Measurable (update h j f i) := by
  intro i
  by_cases hi : i = j
  · subst hi; simpa using hf
  · simpa [update_of_ne hi] using hh i

omit [MeasurableSpace α] in
lemma eq_indicator_add_indicator_diff {E F : Set α} {f : α → ℂ} (hf : DominatedBy E f) :
    f = F.indicator f + (E \ F).indicator f := by
  funext x
  by_cases hxF : x ∈ F
  · have : x ∉ E \ F := fun h => h.2 hxF
    simp [Set.indicator_of_mem hxF, Set.indicator_of_notMem this]
  · by_cases hxE : x ∈ E
    · simp [Set.indicator_of_notMem hxF, Set.indicator_of_mem (show x ∈ E \ F from ⟨hxE, hxF⟩)]
    · have : x ∉ E \ F := fun h => hxE h.1
      simp [Set.indicator_of_notMem hxF, Set.indicator_of_notMem this,
        hf.eq_zero_of_notMem hxE]

/-- Replacing the `j`-th factor: `Π_i G i = G j * Π_{i ≠ j} G i`. -/
lemma prod_fin_three_eq (G : Fin 3 → ℝ) (j : Fin 3) :
    ∏ i, G i = G j * ∏ i ∈ Finset.univ.erase j, G i :=
  (Finset.mul_prod_erase Finset.univ G (Finset.mem_univ j)).symm

lemma sum_fin_three_eq (G : Fin 3 → ℝ) (j : Fin 3) :
    ∑ i, G i = G j + ∑ i ∈ Finset.univ.erase j, G i :=
  (Finset.add_sum_erase Finset.univ G (Finset.mem_univ j)).symm

/-- One step of the iteration on a state `(S, h)` all of whose sets have positive measure. -/
theorem exists_step {μ : Measure α} {Λ : (Fin 3 → α → ℂ) → ℝ} {a : Fin 3 → ℝ} {C m : ℝ}
    (ha : ∀ i, m ≤ a i) (hm : 0 ≤ m) (hsub : IsSubadditive Λ) (hhull : HullBound μ Λ a C)
    {S : Fin 3 → Set α} {h : Fin 3 → α → ℂ} (hSm : ∀ i, MeasurableSet (S i))
    (hSf : ∀ i, μ (S i) < ∞) (hpos : ∀ i, 0 < μ (S i)) (hhm : ∀ i, Measurable (h i))
    (hhd : ∀ i, DominatedBy (S i) (h i)) :
    ∃ (S' : Fin 3 → Set α) (h' : Fin 3 → α → ℂ), (∀ i, MeasurableSet (S' i)) ∧
      (∀ i, μ (S' i) < ∞) ∧ (∀ i, Measurable (h' i)) ∧ (∀ i, DominatedBy (S' i) (h' i)) ∧
      Λ h ≤ C * measProd μ a S + Λ h' ∧
      measProd μ a S' ≤ (2 : ℝ) ^ (-m) * measProd μ a S ∧
      measSum μ S' ≤ 5 / 6 * measSum μ S := by
  classical
  obtain ⟨j, -, hjmax⟩ := Finset.exists_max_image Finset.univ (fun i => μ (S i))
    Finset.univ_nonempty
  have hjmax' : ∀ i, μ (S i) ≤ μ (S j) := fun i => hjmax i (Finset.mem_univ i)
  obtain ⟨Et, hEtm, hEtsub, hEt2, hEtbd⟩ := hhull S hSm hpos hSf j hjmax'
  set S' : Fin 3 → Set α := update S j (S j \ Et) with hS'
  set g : α → ℂ := (S j \ Et).indicator (h j) with hg
  set h' : Fin 3 → α → ℂ := update h j g with hh'
  set f : α → ℂ := Et.indicator (h j) with hf
  have hSjd : MeasurableSet (S j \ Et) := (hSm j).diff hEtm
  have hS'm : ∀ i, MeasurableSet (S' i) := by
    intro i
    by_cases hi : i = j
    · subst hi; simpa [hS'] using hSjd
    · simpa [hS', update_of_ne hi] using hSm i
  have hS'j : S' j = S j \ Et := by simp [hS']
  have hS'ne : ∀ i, i ≠ j → S' i = S i := fun i hi => by simp [hS', update_of_ne hi]
  have hfd : DominatedBy Et f := (hhd j).measurable_indicator_of_subset hEtsub
  have hgd : DominatedBy (S j \ Et) g :=
    (hhd j).measurable_indicator_of_subset Set.sdiff_subset
  have hfm : Measurable f := (hhm j).indicator hEtm
  have hgm : Measurable g := (hhm j).indicator hSjd
  -- measure bookkeeping
  have hsplit : μ Et + μ (S j \ Et) = μ (S j) := by
    have := measure_inter_add_sdiff (μ := μ) (S j) hEtm
    rwa [Set.inter_eq_right.2 hEtsub] at this
  have hEtfin : μ Et < ∞ := (measure_mono hEtsub).trans_lt (hSf j)
  have hdfin : μ (S j \ Et) < ∞ := (measure_mono Set.sdiff_subset).trans_lt (hSf j)
  have hS'f : ∀ i, μ (S' i) < ∞ := by
    intro i
    by_cases hi : i = j
    · subst hi; simpa [hS'j] using hdfin
    · rw [hS'ne i hi]; exact hSf i
  have hsplitR : (μ Et).toReal + (μ (S j \ Et)).toReal = (μ (S j)).toReal := by
    rw [← ENNReal.toReal_add hEtfin.ne hdfin.ne, hsplit]
  have h2R : (μ (S j)).toReal ≤ 2 * (μ Et).toReal := by
    have := ENNReal.toReal_mono (by simpa using (ENNReal.mul_lt_top (by simp) hEtfin).ne) hEt2
    simpa [ENNReal.toReal_mul] using this
  have hmaxR : ∀ i, (μ (S i)).toReal ≤ (μ (S j)).toReal := fun i =>
    ENNReal.toReal_mono (hSf j).ne (hjmax' i)
  have hEtR : 0 ≤ (μ Et).toReal := ENNReal.toReal_nonneg
  have hdR : 0 ≤ (μ (S j \ Et)).toReal := ENNReal.toReal_nonneg
  have hd_le : (μ (S j \ Et)).toReal ≤ (μ (S j)).toReal / 2 := by linarith
  refine ⟨S', h', hS'm, hS'f, measurable_update_fin hhm j hgm, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = j
    · subst hi; simpa [hh', hS'j] using hgd
    · simpa [hh', hS'ne i hi, update_of_ne hi] using hhd i
  · -- Λ h ≤ C Q(S) + Λ h'
    have hdecomp : h j = f + g := eq_indicator_add_indicator_diff (hhd j)
    have hbdd : ∀ i, IsBdd (h i) := fun i => (hhd i).isBdd (hhm i)
    have h1 : Λ h ≤ Λ (update h j f) + Λ h' := by
      have := hsub h j f g hbdd (hfd.isBdd hfm) (hgd.isBdd hgm)
      rwa [← hdecomp, update_eq_self] at this
    have h2 : Λ (update h j f) ≤ C * ∏ i, (μ (S i)).toReal ^ a i := by
      refine hEtbd _ (measurable_update_fin hhm j hfm) ?_ (by simpa using hfd)
      intro i hi
      simpa [update_of_ne hi] using hhd i
    unfold measProd
    linarith
  · -- Q(S') ≤ q Q(S)
    unfold measProd
    rw [prod_fin_three_eq (fun i => (μ (S' i)).toReal ^ a i) j,
      prod_fin_three_eq (fun i => (μ (S i)).toReal ^ a i) j]
    have hrest : ∏ i ∈ Finset.univ.erase j, (μ (S' i)).toReal ^ a i =
        ∏ i ∈ Finset.univ.erase j, (μ (S i)).toReal ^ a i :=
      Finset.prod_congr rfl fun i hi => by rw [hS'ne i (Finset.ne_of_mem_erase hi)]
    rw [hrest]
    have hR : 0 ≤ ∏ i ∈ Finset.univ.erase j, (μ (S i)).toReal ^ a i :=
      Finset.prod_nonneg fun _ _ => Real.rpow_nonneg ENNReal.toReal_nonneg _
    have haj : 0 ≤ a j := hm.trans (ha j)
    have hq : (μ (S' j)).toReal ^ a j ≤ (2 : ℝ) ^ (-m) * (μ (S j)).toReal ^ a j := by
      rw [hS'j]
      calc (μ (S j \ Et)).toReal ^ a j ≤ ((μ (S j)).toReal / 2) ^ a j :=
            Real.rpow_le_rpow hdR hd_le haj
        _ = (μ (S j)).toReal ^ a j / (2 : ℝ) ^ a j :=
            Real.div_rpow ENNReal.toReal_nonneg (by norm_num) _
        _ ≤ (μ (S j)).toReal ^ a j / (2 : ℝ) ^ m :=
            div_le_div_of_nonneg_left (Real.rpow_nonneg ENNReal.toReal_nonneg _)
              (Real.rpow_pos_of_pos (by norm_num) _)
              (Real.rpow_le_rpow_of_exponent_le (by norm_num) (ha j))
        _ = (2 : ℝ) ^ (-m) * (μ (S j)).toReal ^ a j := by
            rw [Real.rpow_neg (by norm_num)]; ring
    calc (μ (S' j)).toReal ^ a j * ∏ i ∈ Finset.univ.erase j, (μ (S i)).toReal ^ a i
        ≤ ((2 : ℝ) ^ (-m) * (μ (S j)).toReal ^ a j) *
          ∏ i ∈ Finset.univ.erase j, (μ (S i)).toReal ^ a i := by gcongr
      _ = _ := by ring
  · -- L(S') ≤ 5/6 L(S)
    unfold measSum
    rw [sum_fin_three_eq (fun i => (μ (S' i)).toReal) j,
      sum_fin_three_eq (fun i => (μ (S i)).toReal) j]
    have hrest : ∑ i ∈ Finset.univ.erase j, (μ (S' i)).toReal =
        ∑ i ∈ Finset.univ.erase j, (μ (S i)).toReal :=
      Finset.sum_congr rfl fun i hi => by rw [hS'ne i (Finset.ne_of_mem_erase hi)]
    rw [hrest, hS'j]
    have hL : ∑ i, (μ (S i)).toReal ≤ 3 * (μ (S j)).toReal := by
      calc ∑ i, (μ (S i)).toReal ≤ ∑ _i : Fin 3, (μ (S j)).toReal :=
            Finset.sum_le_sum fun i _ => hmaxR i
        _ = 3 * (μ (S j)).toReal := by simp
    rw [sum_fin_three_eq (fun i => (μ (S i)).toReal) j] at hL
    linarith

lemma geom_sum_succ_aux (q : ℝ) (K : ℕ) :
    ∑ k ∈ range (K + 1), q ^ k = 1 + q * ∑ k ∈ range K, q ^ k := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_succ, pow_zero]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The `K`-step bound of R6a: after `K` steps of the iteration the remainder is
`A ((5/6)^K L(S))^3`. -/
theorem form_le_iterate {μ : Measure α} {Λ : (Fin 3 → α → ℂ) → ℝ} {a : Fin 3 → ℝ} {C m A : ℝ}
    (ha : ∀ i, m ≤ a i) (hm : 0 ≤ m) (hC : 0 ≤ C) (hA : 0 ≤ A) (hsub : IsSubadditive Λ)
    (hsmall : ∀ (h : Fin 3 → α → ℂ) (S : Fin 3 → Set α), (∀ i, MeasurableSet (S i)) →
      (∀ i, μ (S i) < ∞) → (∀ i, Measurable (h i)) → (∀ i, DominatedBy (S i) (h i)) →
      Λ h ≤ A * ∏ i, (μ (S i)).toReal)
    (hhull : HullBound μ Λ a C) (K : ℕ) :
    ∀ (S : Fin 3 → Set α) (h : Fin 3 → α → ℂ), (∀ i, MeasurableSet (S i)) →
      (∀ i, μ (S i) < ∞) → (∀ i, Measurable (h i)) → (∀ i, DominatedBy (S i) (h i)) →
      Λ h ≤ C * measProd μ a S * ∑ k ∈ range K, ((2 : ℝ) ^ (-m)) ^ k +
        A * ((5 / 6 : ℝ) ^ K * measSum μ S) ^ 3 := by
  have hq0 : 0 ≤ (2 : ℝ) ^ (-m) := Real.rpow_nonneg (by norm_num) _
  induction K with
  | zero =>
    intro S h hSm hSf hhm hhd
    have h0 := hsmall h S hSm hSf hhm hhd
    have hprod : ∏ i, (μ (S i)).toReal ≤ (measSum μ S) ^ 3 := by
      have hle : ∀ i, (μ (S i)).toReal ≤ measSum μ S := by
        intro i
        unfold measSum
        exact Finset.single_le_sum (f := fun i => (μ (S i)).toReal)
          (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ i)
      rw [Fin.prod_univ_three, pow_three]
      have h0' := fun i => (ENNReal.toReal_nonneg : 0 ≤ (μ (S i)).toReal)
      calc (μ (S 0)).toReal * (μ (S 1)).toReal * (μ (S 2)).toReal
          ≤ measSum μ S * measSum μ S * measSum μ S :=
            mul_le_mul (mul_le_mul (hle 0) (hle 1) (h0' 1) (measSum_nonneg μ S)) (hle 2)
              (h0' 2) (mul_nonneg (measSum_nonneg μ S) (measSum_nonneg μ S))
        _ = _ := by ring
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, pow_zero, one_mul, zero_add]
    exact h0.trans (by gcongr)
  | succ K ih =>
    intro S h hSm hSf hhm hhd
    have hRHS_nonneg : 0 ≤ C * measProd μ a S * ∑ k ∈ range (K + 1), ((2 : ℝ) ^ (-m)) ^ k +
        A * ((5 / 6 : ℝ) ^ (K + 1) * measSum μ S) ^ 3 := by
      have := measProd_nonneg μ a S
      have := measSum_nonneg μ S
      have : 0 ≤ ∑ k ∈ range (K + 1), ((2 : ℝ) ^ (-m)) ^ k :=
        Finset.sum_nonneg fun k _ => pow_nonneg hq0 k
      positivity
    by_cases hpos : ∀ i, 0 < μ (S i)
    · obtain ⟨S', h', hS'm, hS'f, hh'm, hh'd, hstep, hQ, hL⟩ :=
        exists_step ha hm hsub hhull hSm hSf hpos hhm hhd
      have hih := ih S' h' hS'm hS'f hh'm hh'd
      have hsum0 : 0 ≤ ∑ k ∈ range K, ((2 : ℝ) ^ (-m)) ^ k :=
        Finset.sum_nonneg fun k _ => pow_nonneg hq0 k
      have hQ' : C * measProd μ a S' * ∑ k ∈ range K, ((2 : ℝ) ^ (-m)) ^ k ≤
          C * (((2 : ℝ) ^ (-m)) * measProd μ a S) * ∑ k ∈ range K, ((2 : ℝ) ^ (-m)) ^ k := by
        gcongr
      have hL' : A * ((5 / 6 : ℝ) ^ K * measSum μ S') ^ 3 ≤
          A * ((5 / 6 : ℝ) ^ (K + 1) * measSum μ S) ^ 3 := by
        have h56 : (0 : ℝ) ≤ (5 / 6 : ℝ) ^ K := by positivity
        have := measSum_nonneg μ S'
        have h1 : (5 / 6 : ℝ) ^ K * measSum μ S' ≤ (5 / 6 : ℝ) ^ (K + 1) * measSum μ S := by
          rw [pow_succ]
          calc (5 / 6 : ℝ) ^ K * measSum μ S' ≤ (5 / 6 : ℝ) ^ K * (5 / 6 * measSum μ S) :=
                mul_le_mul_of_nonneg_left hL h56
            _ = _ := by ring
        have h2 : 0 ≤ (5 / 6 : ℝ) ^ K * measSum μ S' := mul_nonneg h56 this
        gcongr
      calc Λ h ≤ C * measProd μ a S + Λ h' := hstep
        _ ≤ C * measProd μ a S + (C * measProd μ a S' * ∑ k ∈ range K, ((2 : ℝ) ^ (-m)) ^ k +
            A * ((5 / 6 : ℝ) ^ K * measSum μ S') ^ 3) := by gcongr
        _ ≤ C * measProd μ a S + (C * (((2 : ℝ) ^ (-m)) * measProd μ a S) *
            ∑ k ∈ range K, ((2 : ℝ) ^ (-m)) ^ k +
            A * ((5 / 6 : ℝ) ^ (K + 1) * measSum μ S) ^ 3) := by gcongr
        _ = _ := by rw [geom_sum_succ_aux]; ring
    · -- some set is null: `Λ h ≤ 0`
      push Not at hpos
      obtain ⟨i, hi⟩ := hpos
      have hi0 : μ (S i) = 0 := nonpos_iff_eq_zero.1 hi
      have h0 := hsmall h S hSm hSf hhm hhd
      have hprod : ∏ i, (μ (S i)).toReal = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi0])
      rw [hprod, mul_zero] at h0
      exact h0.trans hRHS_nonneg

/-- **R6a** (restricted type for the form, no exceptional set): `Λ(h) ≤ C/(1 - 2^{-m}) Π μ(E_i)^{a_i}`
for measurable `h_i` with `|h_i| ≤ 1_{E_i}`, `E_i` measurable of finite measure, `a_i ≥ m > 0`,
`Σ a_i = 1`. With `m = min a_i` this is the blueprint's `C'_a = C_a/(1 - 2^{-min a_i})`. -/
theorem restrictedType_of_hullBound {μ : Measure α} {Λ : (Fin 3 → α → ℂ) → ℝ}
    {a : Fin 3 → ℝ} {C m : ℝ} (ha : ∀ i, m ≤ a i) (hm : 0 < m) (hC : 0 ≤ C)
    (hsub : IsSubadditive Λ) (hsmall : IsSmall μ Λ) (hhull : HullBound μ Λ a C)
    {E : Fin 3 → Set α} (hEm : ∀ i, MeasurableSet (E i)) (hEf : ∀ i, μ (E i) < ∞)
    {h : Fin 3 → α → ℂ} (hhm : ∀ i, Measurable (h i)) (hhd : ∀ i, DominatedBy (E i) (h i)) :
    Λ h ≤ C / (1 - (2 : ℝ) ^ (-m)) * ∏ i, (μ (E i)).toReal ^ a i := by
  obtain ⟨A, hA, hsm⟩ := hsmall
  have hq0 : 0 ≤ (2 : ℝ) ^ (-m) := Real.rpow_nonneg (by norm_num) _
  have hq1 : (2 : ℝ) ^ (-m) < 1 := by
    rw [Real.rpow_neg (by norm_num)]
    have : (1 : ℝ) < (2 : ℝ) ^ m := Real.one_lt_rpow (by norm_num) hm
    exact inv_lt_one_of_one_lt₀ this
  have hgap : 0 < 1 - (2 : ℝ) ^ (-m) := by linarith
  have hQ : 0 ≤ measProd μ a E := measProd_nonneg μ a E
  -- the bound for each `K`
  have hK : ∀ K : ℕ, Λ h ≤ C * measProd μ a E / (1 - (2 : ℝ) ^ (-m)) +
      A * ((5 / 6 : ℝ) ^ K * measSum μ E) ^ 3 := by
    intro K
    have h1 := form_le_iterate ha hm.le hC hA hsub hsm hhull K E h hEm hEf hhm hhd
    have hgs := geom_sum_mul_neg ((2 : ℝ) ^ (-m)) K
    have hpow : 0 ≤ ((2 : ℝ) ^ (-m)) ^ K := pow_nonneg hq0 K
    have hsumle : ∑ k ∈ range K, ((2 : ℝ) ^ (-m)) ^ k ≤ 1 / (1 - (2 : ℝ) ^ (-m)) := by
      rw [le_div_iff₀ hgap]
      linarith
    calc Λ h ≤ C * measProd μ a E * ∑ k ∈ range K, ((2 : ℝ) ^ (-m)) ^ k +
          A * ((5 / 6 : ℝ) ^ K * measSum μ E) ^ 3 := h1
      _ ≤ C * measProd μ a E * (1 / (1 - (2 : ℝ) ^ (-m))) +
          A * ((5 / 6 : ℝ) ^ K * measSum μ E) ^ 3 := by
          gcongr
      _ = _ := by ring
  have hlim : Filter.Tendsto
      (fun K : ℕ => C * measProd μ a E / (1 - (2 : ℝ) ^ (-m)) +
        A * ((5 / 6 : ℝ) ^ K * measSum μ E) ^ 3) Filter.atTop
      (nhds (C * measProd μ a E / (1 - (2 : ℝ) ^ (-m)) + A * ((0 : ℝ) * measSum μ E) ^ 3)) := by
    refine tendsto_const_nhds.add (Filter.Tendsto.const_mul A ?_)
    refine Filter.Tendsto.pow (Filter.Tendsto.mul_const _ ?_) 3
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have := ge_of_tendsto hlim (Filter.Eventually.of_forall hK)
  simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    add_zero] at this
  calc Λ h ≤ C * measProd μ a E / (1 - (2 : ℝ) ^ (-m)) := this
    _ = _ := by unfold measProd; ring

end PrimeBHT.TimeFrequency.Interp.Restricted
