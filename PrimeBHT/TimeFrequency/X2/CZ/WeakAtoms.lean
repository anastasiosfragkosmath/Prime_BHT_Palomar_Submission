module

public import PrimeBHT.TimeFrequency.X2.CZ.Minkowski
public import PrimeBHT.TimeFrequency.X2.CZ.CZDecomp

/-!
# V08 phase 2: atoms and good part of the vector-valued Calderón-Zygmund decomposition

Given pairwise disjoint intervals `Q_i = [a_i, b_i)` (from `exists_cz_intervals`) and a function
`F : ℝ → ZMod P → ℂ` (a family of scalar functions `F(·, y)`, `y ∈ Y_P`), set

* `meanVal i y = |Q_i|⁻¹ ∫_{Q_i} F(u, y) du` (the vector mean `m_i ∈ X = L^s(Y)`),
* `atom i u y = 1_{Q_i}(u) (F(u, y) - m_i(y))` (a bad atom, mean zero in `u`),
* `badPart = ∑_i atom_i` and `goodPart = F - badPart` (`= m_i` on `Q_i`, `= F` off `⋃ Q_i`).

The `X`-norm bounds `‖m_i‖_X ≤ |Q_i|⁻¹ ∫_{Q_i} ‖F‖_X` come from Minkowski's inequality
(`Minkowski.lean`), so nothing here uses Bochner integrals in `X`: every statement is coordinatewise
in `y` plus the norm `yNorm s` (uniform in `P`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology Real ComplexConjugate

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

open PrimeBHT.Statements

/-- A pointwise `HasSum` of measurable functions over a countable index set is measurable. -/
theorem measurable_of_hasSum {ι : Type*} [Countable ι] {f : ι → ℝ → ℂ} (hf : ∀ i, Measurable (f i))
    {g : ℝ → ℂ} (hg : ∀ u, HasSum (fun i => f i u) (g u)) : Measurable g := by
  classical
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset ι))
    (f := fun S : Finset ι => fun u => ∑ i ∈ S, f i u)
    (fun S => Finset.measurable_sum _ fun i _ => hf i) ?_
  rw [tendsto_pi_nhds]
  intro u
  exact hg u


section YN
variable {P : ℕ} [NeZero P]

theorem yNorm_const_mul {s : ℝ} (hs : 0 < s) (c : ℂ) (v : ZMod P → ℂ) :
    yNorm s (fun y => c * v y) = ‖c‖ * yNorm s v := by
  rw [yNorm_eq_mul hs, yNorm_eq_mul hs]
  simp_rw [norm_mul, Real.mul_rpow (norm_nonneg c) (norm_nonneg _)]
  rw [← Finset.mul_sum, Real.mul_rpow (Real.rpow_nonneg (norm_nonneg _) _)
    (Finset.sum_nonneg fun y _ => Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg c), mul_inv_cancel₀ hs.ne', Real.rpow_one]
  ring

theorem yNorm_sub_le {s : ℝ} (hs : 1 ≤ s) (u v : ZMod P → ℂ) :
    yNorm s (u - v) ≤ yNorm s u + yNorm s v := by
  have h := yNorm_add_le hs u (fun y => (-1 : ℂ) * v y)
  have e : (u + fun y => (-1 : ℂ) * v y) = u - v := by ext y; simp [sub_eq_add_neg]
  rw [e, yNorm_const_mul (by linarith)] at h
  simpa using h

theorem yNorm_zero' {s : ℝ} (hs : 0 < s) : yNorm s (0 : ZMod P → ℂ) = 0 := by
  simp [yNorm, Real.zero_rpow hs.ne', Real.zero_rpow (inv_ne_zero hs.ne')]

/-- **Averages**: `‖ℓ⁻¹ ∫_Q F‖_{L^s(Y)} ≤ ℓ⁻¹ ∫_Q ‖F‖_{L^s(Y)}`. -/
theorem yNorm_average_le {s : ℝ} (hs : 1 < s) {Q : Set ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (F : ℝ → ZMod P → ℂ) (hFi : ∀ y, IntegrableOn (fun u => F u y) Q)
    (hG : IntegrableOn (fun u => yNorm s (F u)) Q) :
    yNorm s (fun y => (ℓ : ℂ)⁻¹ * ∫ u in Q, F u y) ≤ ℓ⁻¹ * ∫ u in Q, yNorm s (F u) := by
  have h := yNorm_integral_le (P := P) hs (μ := volume.restrict Q)
    (fun u y => (ℓ : ℂ)⁻¹ * F u y) (fun y => (hFi y).const_mul _) (by
      have : (fun u => yNorm s (fun y => (ℓ : ℂ)⁻¹ * F u y)) =
          fun u => ℓ⁻¹ * yNorm s (F u) := by
        ext u
        rw [yNorm_const_mul (by linarith), norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hℓ]
      rw [this]; exact hG.const_mul _)
  simp_rw [integral_const_mul] at h
  have e : (fun u => yNorm s (fun y => (ℓ : ℂ)⁻¹ * F u y)) = fun u => ℓ⁻¹ * yNorm s (F u) := by
    ext u
    rw [yNorm_const_mul (by linarith), norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hℓ]
  rw [e, integral_const_mul] at h
  exact h

end YN

section Atoms

variable {P : ℕ} [NeZero P] {ι : Type}

/-- The mean of `F(·, y)` over `Q_i = [a_i, b_i)`. -/
noncomputable def meanVal (a b : ι → ℝ) (F : ℝ → ZMod P → ℂ) (i : ι) (y : ZMod P) : ℂ :=
  ((b i - a i : ℝ) : ℂ)⁻¹ * ∫ u in Ico (a i) (b i), F u y

/-- The bad atom `1_{Q_i} (F - m_i)`. -/
noncomputable def atom (a b : ι → ℝ) (F : ℝ → ZMod P → ℂ) (i : ι) (u : ℝ) (y : ZMod P) : ℂ :=
  (Ico (a i) (b i)).indicator (fun u => F u y - meanVal a b F i y) u

/-- The bad part `∑_i atom_i` (at most one nonzero term for disjoint `Q_i`). -/
noncomputable def badPart (a b : ι → ℝ) (F : ℝ → ZMod P → ℂ) (u : ℝ) (y : ZMod P) : ℂ :=
  ∑' i, atom a b F i u y

/-- The good part `F - badPart`. -/
noncomputable def goodPart (a b : ι → ℝ) (F : ℝ → ZMod P → ℂ) (u : ℝ) (y : ZMod P) : ℂ :=
  F u y - badPart a b F u y

variable {a b : ι → ℝ} {F : ℝ → ZMod P → ℂ}

omit [NeZero P] in
theorem atom_eq_zero_of_notMem {i : ι} {u : ℝ} (h : u ∉ Ico (a i) (b i)) (y : ZMod P) :
    atom a b F i u y = 0 := by
  unfold atom; rw [indicator_of_notMem h]

omit [NeZero P] in
theorem atom_of_mem {i : ι} {u : ℝ} (h : u ∈ Ico (a i) (b i)) (y : ZMod P) :
    atom a b F i u y = F u y - meanVal a b F i y := by
  unfold atom; rw [indicator_of_mem h]

theorem hasSum_atom (hd : Pairwise fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j)))
    (u : ℝ) (y : ZMod P) : HasSum (fun i => atom a b F i u y) (badPart a b F u y) := by
  by_cases h : ∃ j, u ∈ Ico (a j) (b j)
  · obtain ⟨j, hj⟩ := h
    have hz : ∀ i, i ≠ j → atom a b F i u y = 0 := fun i hij =>
      atom_eq_zero_of_notMem (fun hu => (Set.disjoint_left.1 (hd hij)) hu hj) y
    have h1 : HasSum (fun i => atom a b F i u y) (atom a b F j u y) := hasSum_single j hz
    have h2 : badPart a b F u y = atom a b F j u y := h1.tsum_eq
    rw [h2]; exact h1
  · push Not at h
    have hz : ∀ i, atom a b F i u y = 0 := fun i => atom_eq_zero_of_notMem (h i) y
    have : badPart a b F u y = 0 := by unfold badPart; simp [hz]
    rw [this]
    simpa [hz] using hasSum_zero

theorem badPart_of_mem (hd : Pairwise fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j)))
    {j : ι} {u : ℝ} (hu : u ∈ Ico (a j) (b j)) (y : ZMod P) :
    badPart a b F u y = F u y - meanVal a b F j y := by
  have hz : ∀ i, i ≠ j → atom a b F i u y = 0 := fun i hij =>
    atom_eq_zero_of_notMem (fun h => (Set.disjoint_left.1 (hd hij)) h hu) y
  unfold badPart
  rw [tsum_eq_single j hz, atom_of_mem hu]

theorem badPart_of_notMem {u : ℝ} (h : ∀ j, u ∉ Ico (a j) (b j)) (y : ZMod P) :
    badPart a b F u y = 0 := by
  unfold badPart; simp [fun i => atom_eq_zero_of_notMem (F := F) (h i) y]

theorem goodPart_of_mem (hd : Pairwise fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j)))
    {j : ι} {u : ℝ} (hu : u ∈ Ico (a j) (b j)) (y : ZMod P) :
    goodPart a b F u y = meanVal a b F j y := by
  unfold goodPart; rw [badPart_of_mem hd hu]; ring

theorem goodPart_of_notMem {u : ℝ} (h : ∀ j, u ∉ Ico (a j) (b j)) (y : ZMod P) :
    goodPart a b F u y = F u y := by
  unfold goodPart; rw [badPart_of_notMem h]; ring

end Atoms

section AtomsAnalysis

variable {P : ℕ} [NeZero P] {ι : Type} [Countable ι] {a b : ι → ℝ} {F : ℝ → ZMod P → ℂ}

omit [NeZero P] [Countable ι] in
theorem measurable_atom (hFm : ∀ y, Measurable fun u => F u y) (i : ι) (y : ZMod P) :
    Measurable fun u => atom a b F i u y := by
  unfold atom
  exact (hFm y |>.sub measurable_const).indicator measurableSet_Ico

omit [NeZero P] [Countable ι] in
theorem integrable_atom (hFi : ∀ y, Integrable fun u => F u y) (_hFm : ∀ y, Measurable fun u => F u y)
    (i : ι) (y : ZMod P) : Integrable fun u => atom a b F i u y := by
  unfold atom
  exact (integrable_indicator_iff measurableSet_Ico).2
    ((hFi y).integrableOn.sub (integrableOn_const (by simp)))

omit [NeZero P] [Countable ι] in
theorem integral_atom_eq_zero (hab : ∀ i, a i < b i) (hFi : ∀ y, Integrable fun u => F u y)
    (i : ι) (y : ZMod P) : ∫ u, atom a b F i u y = 0 := by
  unfold atom
  rw [integral_indicator measurableSet_Ico, integral_sub (hFi y).integrableOn
    (integrableOn_const (by simp)), setIntegral_const]
  have hl : (0 : ℝ) < b i - a i := sub_pos.2 (hab i)
  unfold meanVal
  have : volume.real (Ico (a i) (b i)) = b i - a i := by
    rw [Real.volume_real_Ico_of_le (hab i).le]
  rw [this, Complex.real_smul]
  have hne : ((b i - a i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  field_simp
  ring

omit [NeZero P] [Countable ι] in
theorem norm_meanVal_le (hab : ∀ i, a i < b i) (_hFi : ∀ y, Integrable fun u => F u y)
    (i : ι) (y : ZMod P) :
    ‖meanVal a b F i y‖ * (b i - a i) ≤ ∫ u in Ico (a i) (b i), ‖F u y‖ := by
  have hl : (0 : ℝ) < b i - a i := sub_pos.2 (hab i)
  unfold meanVal
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl]
  calc (b i - a i)⁻¹ * ‖∫ u in Ico (a i) (b i), F u y‖ * (b i - a i)
      = ‖∫ u in Ico (a i) (b i), F u y‖ := by field_simp
    _ ≤ ∫ u in Ico (a i) (b i), ‖F u y‖ := norm_integral_le_integral_norm _

theorem integral_norm_atom_le (hab : ∀ i, a i < b i) (hFi : ∀ y, Integrable fun u => F u y)
    (i : ι) (y : ZMod P) :
    ∫ u, ‖atom a b F i u y‖ ≤ 2 * ∫ u in Ico (a i) (b i), ‖F u y‖ := by
  have hl : (0 : ℝ) < b i - a i := sub_pos.2 (hab i)
  have hint : IntegrableOn (fun u => ‖F u y‖) (Ico (a i) (b i)) := (hFi y).norm.integrableOn
  have hm := norm_meanVal_le hab hFi i y
  have : ∫ u, ‖atom a b F i u y‖ = ∫ u in Ico (a i) (b i), ‖F u y - meanVal a b F i y‖ := by
    unfold atom
    rw [← integral_indicator measurableSet_Ico]
    congr 1; ext u
    by_cases hu : u ∈ Ico (a i) (b i) <;> simp [hu]
  rw [this]
  calc ∫ u in Ico (a i) (b i), ‖F u y - meanVal a b F i y‖
      ≤ ∫ u in Ico (a i) (b i), (‖F u y‖ + ‖meanVal a b F i y‖) := by
        refine setIntegral_mono_on ?_ (hint.add (integrableOn_const (by simp))) measurableSet_Ico
          (fun u _ => norm_sub_le _ _)
        exact ((hFi y).integrableOn.sub (integrableOn_const (by simp))).norm
    _ = (∫ u in Ico (a i) (b i), ‖F u y‖) + ‖meanVal a b F i y‖ * (b i - a i) := by
        rw [integral_add hint (integrableOn_const (by simp)), setIntegral_const,
          Real.volume_real_Ico_of_le (hab i).le, smul_eq_mul, mul_comm]
    _ ≤ 2 * ∫ u in Ico (a i) (b i), ‖F u y‖ := by linarith

theorem summable_integral_norm_atom (hab : ∀ i, a i < b i)
    (hd : Pairwise fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j)))
    (hFi : ∀ y, Integrable fun u => F u y) (y : ZMod P) :
    Summable fun i => ∫ u, ‖atom a b F i u y‖ := by
  have h1 : HasSum (fun i => ∫ u in Ico (a i) (b i), ‖F u y‖)
      (∫ u in ⋃ i, Ico (a i) (b i), ‖F u y‖) :=
    hasSum_integral_iUnion (fun i => measurableSet_Ico) hd (hFi y).norm.integrableOn
  refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun u => norm_nonneg _)
    (fun i => integral_norm_atom_le hab hFi i y) (h1.summable.mul_left 2)

theorem integrable_badPart (hab : ∀ i, a i < b i)
    (hd : Pairwise fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j)))
    (hFm : ∀ y, Measurable fun u => F u y) (hFi : ∀ y, Integrable fun u => F u y) (y : ZMod P) :
    Integrable fun u => badPart a b F u y := by
  have hms : Measurable fun u => badPart a b F u y :=
    measurable_of_hasSum (fun i => measurable_atom hFm i y) (fun u => hasSum_atom hd u y)
  refine ⟨hms.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have h1 : ∀ u, ‖badPart a b F u y‖ₑ ≤ ∑' i, ‖atom a b F i u y‖ₑ := by
    intro u
    by_cases h : ∃ j, u ∈ Ico (a j) (b j)
    · obtain ⟨j, hj⟩ := h
      have hz : ∀ i, i ≠ j → ‖atom a b F i u y‖ₑ = 0 := fun i hij => by
        rw [atom_eq_zero_of_notMem (fun hu => (Set.disjoint_left.1 (hd hij)) hu hj) y]; simp
      rw [tsum_eq_single j hz, badPart_of_mem hd hj, atom_of_mem hj]
    · push Not at h
      rw [badPart_of_notMem h]; simp
  calc ∫⁻ u, ‖badPart a b F u y‖ₑ ≤ ∫⁻ u, ∑' i, ‖atom a b F i u y‖ₑ := lintegral_mono h1
    _ = ∑' i, ∫⁻ u, ‖atom a b F i u y‖ₑ := lintegral_tsum fun i =>
        (measurable_atom hFm i y).enorm.aemeasurable
    _ < ⊤ := by
        have hs := summable_integral_norm_atom hab hd hFi y
        have : ∀ i, ∫⁻ u, ‖atom a b F i u y‖ₑ = ENNReal.ofReal (∫ u, ‖atom a b F i u y‖) := fun i => by
          rw [ofReal_integral_eq_lintegral_ofReal (integrable_atom hFi hFm i y).norm
            (Eventually.of_forall fun _ => norm_nonneg _)]
          simp [ofReal_norm]
        simp_rw [this]
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun u => norm_nonneg _) hs]
        exact ENNReal.ofReal_lt_top

theorem integrable_goodPart (hab : ∀ i, a i < b i)
    (hd : Pairwise fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j)))
    (hFm : ∀ y, Measurable fun u => F u y) (hFi : ∀ y, Integrable fun u => F u y) (y : ZMod P) :
    Integrable fun u => goodPart a b F u y :=
  (hFi y).sub (integrable_badPart hab hd hFm hFi y)

theorem measurable_goodPart (hd : Pairwise fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j)))
    (hFm : ∀ y, Measurable fun u => F u y) (y : ZMod P) :
    Measurable fun u => goodPart a b F u y :=
  (hFm y).sub (measurable_of_hasSum (fun i => measurable_atom hFm i y) (fun u => hasSum_atom hd u y))

theorem norm_goodPart_le (hab : ∀ i, a i < b i)
    (hd : Pairwise fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j)))
    (hFi : ∀ y, Integrable fun u => F u y) {C : ℝ} (y : ZMod P) (hC : ∀ u, ‖F u y‖ ≤ C) (u : ℝ) :
    ‖goodPart a b F u y‖ ≤ C := by
  by_cases h : ∃ j, u ∈ Ico (a j) (b j)
  · obtain ⟨j, hj⟩ := h
    rw [goodPart_of_mem hd hj]
    have hl : (0 : ℝ) < b j - a j := sub_pos.2 (hab j)
    have hm := norm_meanVal_le hab hFi j y
    have h2 : ∫ u in Ico (a j) (b j), ‖F u y‖ ≤ C * (b j - a j) := by
      calc ∫ u in Ico (a j) (b j), ‖F u y‖ ≤ ∫ u in Ico (a j) (b j), C :=
            setIntegral_mono_on (hFi y).norm.integrableOn (integrableOn_const (by simp))
              measurableSet_Ico (fun u _ => hC u)
        _ = C * (b j - a j) := by
            rw [setIntegral_const, Real.volume_real_Ico_of_le (hab j).le, smul_eq_mul, mul_comm]
    nlinarith
  · push Not at h
    rw [goodPart_of_notMem h]; exact hC u

end AtomsAnalysis

end PrimeBHT.TimeFrequency.X2.CZ
