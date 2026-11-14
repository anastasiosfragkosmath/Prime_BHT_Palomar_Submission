module

public import PrimeBHT.TimeFrequency.Interp.Restricted.Operator
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# X2, node V17 (I1): R6a for forms with one norm per slot

Vector-valued generalization of the verified X1 file `PrimeBHT/TimeFrequency/Interp/Restricted/Form.lean`
(R6a, `restrictedType_of_hullBound`), by COPY-ADAPT (the X1 file is untouched).  Source of the
mathematics: `docs/audits/X2-V16B-route-check.md` §1.1, §1.2, §2.3 (I1-I4).

## Setting

`α` is a measurable space with a measure `μ` (X2: `α = ℝ`, `μ = volume`).  The slots of the trilinear form
`Λ : (Fin 3 → α → W) → ℝ` take values in ONE carrier `W` (X2: `W = ZMod P → ℂ`, i.e. `ℂ^P`), and the
slot `i` carries its own *norm function* `ν i : W → ℝ` (X2: `ν = (yNorm 2, yNorm 2, yNorm u)`).  This is the
shape of the interface drafted for V16 (`drafts/x2-interface/06-V16-Defs.lean.txt`, `VHullBound`): the V16
output `VHullBound (slotNorms u) (fun h => ‖modelForm …‖) β K` is literally an instance of `VHullBound`
below (with `μ = volume`).  (The brief's `Π i, α → V i` with one normed type per slot is the special case
where the three types are type synonyms of one carrier; keeping one carrier avoids dependent types in
`update h j f` and `![f₁, f₂, h]`, and nothing in the argument uses more than the slot norm functions.)

## Predicates (copies of X1's `DominatedBy`, `IsBdd`, `IsSubadditive`, `IsSmall`, `HullBound`)

* `IsSlotNorm ν`: `ν w ≤ 0 ↔ w = 0` (`ν` is definite and `ν 0 ≤ 0`).  This is the only property of the
  slot norms used by R6a (zero is dominated by anything; a function dominated by `1_E` vanishes off `E`);
  it holds for every norm and for `yNorm s` (`s > 0`, `P ≥ 1`).  It is the one hypothesis on the slot
  norms that is not printed in the audit.
* `VDominatedBy ν E f`: `ν (f x) ≤ 1_E x` for all `x`.
* `IsBddV ν f`: `f` is measurable and `ν ∘ f` is bounded above.
* `IsSubadditiveV ν Λ`: in each slot `j`, `Λ(h[j := f + g]) ≤ Λ(h[j := f]) + Λ(h[j := g])` for `ν`-bounded
  measurable functions (slot-wise boundedness).
* `IsSmallV μ ν Λ`: `Λ(h) ≤ A Π_i μ(S_i)` whenever `ν_i ∘ h_i ≤ 1_{S_i}` (qualitative; used only to kill the
  remainder of the iteration and to treat null sets).
* `VHullBound μ ν Λ a C`: the vector `HullBound` (route check §1.2) at the exponent `a` with constant `C`:
  for all measurable `E_i` of finite positive measure and every index `j` of a largest set there is a measurable
  major subset `Ẽ ⊆ E_j`, `μ E_j ≤ 2 μ Ẽ` (depending on the sets only) such that `Λ(h) ≤ C Π_i μ(E_i)^{a_i}`
  for measurable `h` with `ν_i ∘ h_i ≤ 1_{E_i}` (`i ≠ j`), `ν_j ∘ h_j ≤ 1_Ẽ`.

## Main result

`restrictedType_of_hullBound` (**R6a, I1**): for `a_i ≥ m > 0`, `0 ≤ C`, `IsSubadditiveV`, `IsSmallV`,
`VHullBound μ ν Λ a C`, all measurable `E_i` of finite measure and measurable `h_i` with `ν_i ∘ h_i ≤ 1_{E_i}`:
`Λ(h) ≤ C / (1 - 2^{-m}) Π μ(E_i)^{a_i}`.  (`Σ a_i = 1` is not needed: the proof never uses it.)

The proof is X1's: the iteration on the major subsets is run for `K` steps as an induction on `K` over all
states `(S, h)`, with the bound `Λ(h) ≤ C Q(S) Σ_{k<K} q^k + A ((5/6)^K L(S))^3`, `q = 2^{-m}`,
`Q(S) = Π μ(S_i)^{a_i}`, `L(S) = Σ μ(S_i)`.  Nothing in it uses the scalar structure of the slots: only
the slot-wise norm bounds, additivity of the slot values and measurability of the indicators.

## Corrections to the printed statement

None needed for R6a itself.  (`Σ a_i = 1` is dropped from the hypotheses: it is not used; the audit lists
it only because the application has it.)
-/

@[expose] public section

namespace PrimeBHT.TimeFrequency.X2.Interp

open MeasureTheory Function Finset
open scoped ENNReal
open PrimeBHT.TimeFrequency.Interp.Restricted (measProd measSum measProd_nonneg measSum_nonneg
  prod_fin_three_eq sum_fin_three_eq geom_sum_succ_aux)

variable {α W : Type*} [MeasurableSpace α] [MeasurableSpace W] [AddCommMonoid W]

/-- The only property of a slot norm used by R6a: `ν w ≤ 0 ↔ w = 0`. -/
def IsSlotNorm (ν : W → ℝ) : Prop := ∀ w, ν w ≤ 0 ↔ w = 0

/-- `ν (f x) ≤ 1_E x` for all `x`. -/
def VDominatedBy (ν : W → ℝ) (E : Set α) (f : α → W) : Prop :=
  ∀ x, ν (f x) ≤ E.indicator (fun _ => (1 : ℝ)) x

/-- The class of test functions: measurable and `ν`-bounded. -/
def IsBddV (ν : W → ℝ) (f : α → W) : Prop :=
  Measurable f ∧ ∃ M : ℝ, ∀ x, ν (f x) ≤ M

/-- `Λ` is subadditive in each slot, on slot-wise bounded measurable functions. -/
def IsSubadditiveV (ν : Fin 3 → W → ℝ) (Λ : (Fin 3 → α → W) → ℝ) : Prop :=
  ∀ (h : Fin 3 → α → W) (j : Fin 3) (f g : α → W), (∀ i, IsBddV (ν i) (h i)) →
    IsBddV (ν j) f → IsBddV (ν j) g →
    Λ (update h j (f + g)) ≤ Λ (update h j f) + Λ (update h j g)

/-- `Λ(h) ≤ A Π_i μ(S_i)` for `ν_i ∘ h_i ≤ 1_{S_i}` (qualitative smallness). -/
def IsSmallV (μ : Measure α) (ν : Fin 3 → W → ℝ) (Λ : (Fin 3 → α → W) → ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ (h : Fin 3 → α → W) (S : Fin 3 → Set α), (∀ i, MeasurableSet (S i)) →
    (∀ i, μ (S i) < ∞) → (∀ i, Measurable (h i)) → (∀ i, VDominatedBy (ν i) (S i) (h i)) →
    Λ h ≤ A * ∏ i, (μ (S i)).toReal

/-- The vector `HullBound` (route check §1.2) at the exponent `a` with constant `C`: generalized
restricted type with the major subset in a largest set, one norm per slot. -/
def VHullBound (μ : Measure α) (ν : Fin 3 → W → ℝ) (Λ : (Fin 3 → α → W) → ℝ) (a : Fin 3 → ℝ)
    (C : ℝ) : Prop :=
  ∀ E : Fin 3 → Set α, (∀ i, MeasurableSet (E i)) → (∀ i, 0 < μ (E i)) → (∀ i, μ (E i) < ∞) →
    ∀ j : Fin 3, (∀ i, μ (E i) ≤ μ (E j)) →
      ∃ Et : Set α, MeasurableSet Et ∧ Et ⊆ E j ∧ μ (E j) ≤ 2 * μ Et ∧
        ∀ h : Fin 3 → α → W, (∀ i, Measurable (h i)) →
          (∀ i, i ≠ j → VDominatedBy (ν i) (E i) (h i)) → VDominatedBy (ν j) Et (h j) →
            Λ h ≤ C * ∏ i, (μ (E i)).toReal ^ a i

/-- The corner region `𝒩_R = {β : Σβ = 1, |β₁ - 1/2| ≤ 1/(8R), |β₂ - 1/2| ≤ 1/(8R)}` (route check §1.2).
(Defined here, not in `StrongV.lean`, so that V16 can state its `VHullBound` on it without importing
the interpolation chain.) -/
def InCornerNbhd (R : ℝ) (β : Fin 3 → ℝ) : Prop :=
  β 0 + β 1 + β 2 = 1 ∧ |β 0 - 1 / 2| ≤ 1 / (8 * R) ∧ |β 1 - 1 / 2| ≤ 1 / (8 * R)

omit [AddCommMonoid W] in
/-- A larger constant is also a hull constant. -/
lemma VHullBound.mono {μ : Measure α} {ν : Fin 3 → W → ℝ} {Λ : (Fin 3 → α → W) → ℝ}
    {a : Fin 3 → ℝ} {C C' : ℝ} (h : VHullBound μ ν Λ a C) (hC : C ≤ C') :
    VHullBound μ ν Λ a C' := by
  intro E hEm hEpos hEf j hj
  obtain ⟨Et, hEtm, hEtsub, hEt2, hbd⟩ := h E hEm hEpos hEf j hj
  refine ⟨Et, hEtm, hEtsub, hEt2, fun h hhm hhd hhj => (hbd h hhm hhd hhj).trans ?_⟩
  have : 0 ≤ ∏ i, (μ (E i)).toReal ^ a i :=
    Finset.prod_nonneg fun _ _ => Real.rpow_nonneg ENNReal.toReal_nonneg _
  exact mul_le_mul_of_nonneg_right hC this

/-! ### Elementary facts on domination -/

omit [MeasurableSpace α] [MeasurableSpace W] in
lemma VDominatedBy.indicator_of_subset {ν : W → ℝ} (hν : IsSlotNorm ν) {E F : Set α} {f : α → W}
    (hf : VDominatedBy ν E f) (hF : F ⊆ E) : VDominatedBy ν F (F.indicator f) := by
  intro x
  by_cases hx : x ∈ F
  · have := hf x
    simpa [Set.indicator_of_mem hx, Set.indicator_of_mem (hF hx)] using this
  · simp only [Set.indicator_of_notMem hx]
    exact (hν 0).2 rfl

omit [MeasurableSpace α] [MeasurableSpace W] in
lemma VDominatedBy.eq_zero_of_notMem {ν : W → ℝ} (hν : IsSlotNorm ν) {E : Set α} {f : α → W}
    (hf : VDominatedBy ν E f) {x : α} (hx : x ∉ E) : f x = 0 := by
  have := hf x
  rw [Set.indicator_of_notMem hx] at this
  exact (hν _).1 this

omit [AddCommMonoid W] in
lemma VDominatedBy.isBddV {ν : W → ℝ} {E : Set α} {f : α → W} (hf : VDominatedBy ν E f)
    (hm : Measurable f) : IsBddV ν f :=
  ⟨hm, 1, fun x => (hf x).trans (Set.indicator_le_self' (fun _ _ => zero_le_one) x)⟩

omit [MeasurableSpace α] [MeasurableSpace W] [AddCommMonoid W] in
lemma VDominatedBy.mono_set {ν : W → ℝ} {E F : Set α} {f : α → W} (hf : VDominatedBy ν E f)
    (hEF : E ⊆ F) : VDominatedBy ν F f := fun x =>
  (hf x).trans (Set.indicator_le_indicator_of_subset hEF (fun _ => zero_le_one) x)

lemma IsBddV.indicator {ν : W → ℝ} (hν : IsSlotNorm ν) {f : α → W} (hf : IsBddV ν f) {F : Set α}
    (hF : MeasurableSet F) : IsBddV ν (F.indicator f) := by
  obtain ⟨hm, M, hM⟩ := hf
  refine ⟨hm.indicator hF, max M 0, fun x => ?_⟩
  by_cases hx : x ∈ F
  · simpa [Set.indicator_of_mem hx] using (hM x).trans (le_max_left _ _)
  · simp only [Set.indicator_of_notMem hx]
    exact ((hν 0).2 rfl).trans (le_max_right _ _)

omit [AddCommMonoid W] in
lemma measurable_update_fin {h : Fin 3 → α → W} (hh : ∀ i, Measurable (h i)) (j : Fin 3)
    {f : α → W} (hf : Measurable f) : ∀ i, Measurable (update h j f i) := by
  intro i
  by_cases hi : i = j
  · subst hi; simpa using hf
  · simpa [update_of_ne hi] using hh i

omit [MeasurableSpace α] [MeasurableSpace W] in
lemma eq_indicator_add_indicator_diff {ν : W → ℝ} (hν : IsSlotNorm ν) {E F : Set α} {f : α → W}
    (hf : VDominatedBy ν E f) : f = F.indicator f + (E \ F).indicator f := by
  funext x
  by_cases hxF : x ∈ F
  · have : x ∉ E \ F := fun h => h.2 hxF
    simp [Set.indicator_of_mem hxF, Set.indicator_of_notMem this]
  · by_cases hxE : x ∈ E
    · simp [Set.indicator_of_notMem hxF, Set.indicator_of_mem (show x ∈ E \ F from ⟨hxE, hxF⟩)]
    · have : x ∉ E \ F := fun h => hxE h.1
      simp [Set.indicator_of_notMem hxF, Set.indicator_of_notMem this,
        hf.eq_zero_of_notMem hν hxE]

/-! ### One step of the iteration -/

/-- One step of the iteration on a state `(S, h)` all of whose sets have positive measure. -/
theorem exists_step {μ : Measure α} {ν : Fin 3 → W → ℝ} {Λ : (Fin 3 → α → W) → ℝ}
    {a : Fin 3 → ℝ} {C m : ℝ} (hν : ∀ i, IsSlotNorm (ν i))
    (ha : ∀ i, m ≤ a i) (hm : 0 ≤ m) (hsub : IsSubadditiveV ν Λ) (hhull : VHullBound μ ν Λ a C)
    {S : Fin 3 → Set α} {h : Fin 3 → α → W} (hSm : ∀ i, MeasurableSet (S i))
    (hSf : ∀ i, μ (S i) < ∞) (hpos : ∀ i, 0 < μ (S i)) (hhm : ∀ i, Measurable (h i))
    (hhd : ∀ i, VDominatedBy (ν i) (S i) (h i)) :
    ∃ (S' : Fin 3 → Set α) (h' : Fin 3 → α → W), (∀ i, MeasurableSet (S' i)) ∧
      (∀ i, μ (S' i) < ∞) ∧ (∀ i, Measurable (h' i)) ∧ (∀ i, VDominatedBy (ν i) (S' i) (h' i)) ∧
      Λ h ≤ C * measProd μ a S + Λ h' ∧
      measProd μ a S' ≤ (2 : ℝ) ^ (-m) * measProd μ a S ∧
      measSum μ S' ≤ 5 / 6 * measSum μ S := by
  classical
  obtain ⟨j, -, hjmax⟩ := Finset.exists_max_image Finset.univ (fun i => μ (S i))
    Finset.univ_nonempty
  have hjmax' : ∀ i, μ (S i) ≤ μ (S j) := fun i => hjmax i (Finset.mem_univ i)
  obtain ⟨Et, hEtm, hEtsub, hEt2, hEtbd⟩ := hhull S hSm hpos hSf j hjmax'
  set S' : Fin 3 → Set α := update S j (S j \ Et) with hS'
  set g : α → W := (S j \ Et).indicator (h j) with hg
  set h' : Fin 3 → α → W := update h j g with hh'
  set f : α → W := Et.indicator (h j) with hf
  have hSjd : MeasurableSet (S j \ Et) := (hSm j).diff hEtm
  have hS'm : ∀ i, MeasurableSet (S' i) := by
    intro i
    by_cases hi : i = j
    · subst hi; simpa [hS'] using hSjd
    · simpa [hS', update_of_ne hi] using hSm i
  have hS'j : S' j = S j \ Et := by simp [hS']
  have hS'ne : ∀ i, i ≠ j → S' i = S i := fun i hi => by simp [hS', update_of_ne hi]
  have hfd : VDominatedBy (ν j) Et f := (hhd j).indicator_of_subset (hν j) hEtsub
  have hgd : VDominatedBy (ν j) (S j \ Et) g :=
    (hhd j).indicator_of_subset (hν j) Set.sdiff_subset
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
    have hdecomp : h j = f + g := eq_indicator_add_indicator_diff (hν j) (hhd j)
    have hbdd : ∀ i, IsBddV (ν i) (h i) := fun i => (hhd i).isBddV (hhm i)
    have h1 : Λ h ≤ Λ (update h j f) + Λ h' := by
      have := hsub h j f g hbdd (hfd.isBddV hfm) (hgd.isBddV hgm)
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

/-- The `K`-step bound of R6a: after `K` steps of the iteration the remainder is
`A ((5/6)^K L(S))^3`. -/
theorem form_le_iterate {μ : Measure α} {ν : Fin 3 → W → ℝ} {Λ : (Fin 3 → α → W) → ℝ}
    {a : Fin 3 → ℝ} {C m A : ℝ} (hν : ∀ i, IsSlotNorm (ν i))
    (ha : ∀ i, m ≤ a i) (hm : 0 ≤ m) (hC : 0 ≤ C) (hA : 0 ≤ A) (hsub : IsSubadditiveV ν Λ)
    (hsmall : ∀ (h : Fin 3 → α → W) (S : Fin 3 → Set α), (∀ i, MeasurableSet (S i)) →
      (∀ i, μ (S i) < ∞) → (∀ i, Measurable (h i)) → (∀ i, VDominatedBy (ν i) (S i) (h i)) →
      Λ h ≤ A * ∏ i, (μ (S i)).toReal)
    (hhull : VHullBound μ ν Λ a C) (K : ℕ) :
    ∀ (S : Fin 3 → Set α) (h : Fin 3 → α → W), (∀ i, MeasurableSet (S i)) →
      (∀ i, μ (S i) < ∞) → (∀ i, Measurable (h i)) → (∀ i, VDominatedBy (ν i) (S i) (h i)) →
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
        exists_step hν ha hm hsub hhull hSm hSf hpos hhm hhd
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

/-- **R6a (I1)** (restricted type for the form, no exceptional set), one norm per slot:
`Λ(h) ≤ C/(1 - 2^{-m}) Π μ(E_i)^{a_i}` for measurable `h_i` with `ν_i ∘ h_i ≤ 1_{E_i}`, `E_i` measurable
of finite measure, `a_i ≥ m > 0`. -/
theorem restrictedType_of_hullBound {μ : Measure α} {ν : Fin 3 → W → ℝ}
    {Λ : (Fin 3 → α → W) → ℝ} {a : Fin 3 → ℝ} {C m : ℝ} (hν : ∀ i, IsSlotNorm (ν i))
    (ha : ∀ i, m ≤ a i) (hm : 0 < m) (hC : 0 ≤ C)
    (hsub : IsSubadditiveV ν Λ) (hsmall : IsSmallV μ ν Λ) (hhull : VHullBound μ ν Λ a C)
    {E : Fin 3 → Set α} (hEm : ∀ i, MeasurableSet (E i)) (hEf : ∀ i, μ (E i) < ∞)
    {h : Fin 3 → α → W} (hhm : ∀ i, Measurable (h i)) (hhd : ∀ i, VDominatedBy (ν i) (E i) (h i)) :
    Λ h ≤ C / (1 - (2 : ℝ) ^ (-m)) * ∏ i, (μ (E i)).toReal ^ a i := by
  obtain ⟨A, hA, hsm⟩ := hsmall
  have hq0 : 0 ≤ (2 : ℝ) ^ (-m) := Real.rpow_nonneg (by norm_num) _
  have hq1 : (2 : ℝ) ^ (-m) < 1 := by
    rw [Real.rpow_neg (by norm_num)]
    have : (1 : ℝ) < (2 : ℝ) ^ m := Real.one_lt_rpow (by norm_num) hm
    exact inv_lt_one_of_one_lt₀ this
  have hgap : 0 < 1 - (2 : ℝ) ^ (-m) := by linarith
  have hQ : 0 ≤ measProd μ a E := measProd_nonneg μ a E
  have hK : ∀ K : ℕ, Λ h ≤ C * measProd μ a E / (1 - (2 : ℝ) ^ (-m)) +
      A * ((5 / 6 : ℝ) ^ K * measSum μ E) ^ 3 := by
    intro K
    have h1 := form_le_iterate hν ha hm.le hC hA hsub hsm hhull K E h hEm hEf hhm hhd
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

end PrimeBHT.TimeFrequency.X2.Interp
