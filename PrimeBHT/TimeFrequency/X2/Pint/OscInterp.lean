module

public import PrimeBHT.TimeFrequency.X2.Pint.TheoremIMeas

/-!
# X2, V11 (Theorem II), part 1: interpolation of the mean oscillation on one interval

`osc_interp`: for `U_z(x) = ∑_k d_k(x) • famF (v k) z` (`d_k` bounded measurable) and an interval `[a, b)`, if the
`L^{s₀}(Y)`-mean of `U_{it}` over `[a, b)` is at most `Cb` for every `t`, then
`(⨍ ‖U_θ‖_s)^{qX} ≤ 2^{qX} Cb^{qX-2} ∫ (⨍ ‖U_{1+it}‖_2)² dν(t)` (`θ = 2/qX`, `ν` the Poisson-Jensen measure).

Proof: a finite norming net `G_j` of the dual unit ball (`exists_norming_net`, compactness; constant `2`), a measurable
partition `A_j` of `ℝ` choosing for every `x` the first `j` that norms `U_θ(x)` up to the factor `2`, and the holomorphic
function `Φ(z) = ⨍ ∑_j 1_{A_j} bil (U_z) (famG (G j) z)` (a finite sum of constants times entire functions).
-/

@[expose] public noncomputable section

open MeasureTheory Set Complex Complex.HadamardThreeLines
open scoped ENNReal ComplexConjugate
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Pint

variable {P : ℕ} [NeZero P]

theorem bil_smul_left (c : ℂ) (a b : ZMod P → ℂ) : bil (c • a) b = c * bil a b := by
  simp only [bil, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem bil_sum_left {κ : Type*} (S : Finset κ) (w : κ → ZMod P → ℂ) (b : ZMod P → ℂ) :
    bil (∑ k ∈ S, w k) b = ∑ k ∈ S, bil (w k) b := by
  simp only [bil, Finset.sum_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem continuous_bil_left (b : ZMod P → ℂ) : Continuous fun a : ZMod P → ℂ => bil a b :=
  continuous_const.mul (continuous_finsetSum _ fun y _ => (continuous_apply y).mul continuous_const)

theorem yNorm_one_const {s : ℝ} (_hs : 0 < s) : yNorm s (fun _ : ZMod P => (1 : ℂ)) = 1 := by
  have hP : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
  unfold yNorm
  simp [Finset.card_univ, ZMod.card, inv_mul_cancel₀ hP.ne']

/-- **A finite norming net** of the dual unit ball, with constant `2`. -/
theorem exists_norming_net {s : ℝ} (hs : 1 < s) (h : (sC s).HolderConjugate s) :
    ∃ (N : ℕ) (G : Fin N → ZMod P → ℂ), (∀ j, yNorm (sC s) (G j) ≤ 1) ∧
      ∀ u : ZMod P → ℂ, ∃ j, yNorm s u ≤ 2 * (bil u (G j)).re := by
  classical
  have hs0 : 0 < s := by linarith
  choose v hv1 hv2 using fun e : ZMod P → ℂ => exists_norming h e
  set g : (ZMod P → ℂ) → ZMod P → ℂ := fun e y => conj (v e y) with hg
  have hbg : ∀ u e, bil u (g e) = yPair u (v e) := fun u e => by
    rw [bil_eq_yPair]; simp [hg]
  set S : Set (ZMod P → ℂ) := {u | yNorm s u = 1} with hS
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_eq (continuous_yNorm hs0) continuous_const) ?_
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨(P : ℝ) ^ s⁻¹, fun u hu => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun y => ?_
    have := norm_apply_le_yNorm hs0 u y
    rwa [show yNorm s u = 1 from hu, mul_one] at this
  set U : (ZMod P → ℂ) → Set (ZMod P → ℂ) := fun e => {u | 1 / 2 < (bil u (g e)).re} with hU
  have hUo : ∀ e, IsOpen (U e) := fun e =>
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_bil_left (g e)))
  have hcov : S ⊆ ⋃ e, U e := by
    intro u hu
    refine mem_iUnion.2 ⟨u, ?_⟩
    show 1 / 2 < (bil u (g u)).re
    have := hv2 u
    rw [show yNorm s u = 1 from hu, ← hbg] at this
    linarith
  obtain ⟨t, ht⟩ := hSc.elim_finite_subcover U hUo hcov
  refine ⟨t.card, fun j => g (t.equivFin.symm j), fun j => by rw [hg, yNorm_conj]; exact hv1 _, fun u => ?_⟩
  by_cases hu0 : yNorm s u = 0
  · have hone : (fun _ => (1 : ℂ)) ∈ S := yNorm_one_const hs0
    obtain ⟨e, he, -⟩ := mem_iUnion₂.1 (ht hone)
    refine ⟨t.equivFin ⟨e, he⟩, ?_⟩
    rw [hu0, (yNorm_eq_zero_iff_of_pos hs0 u).1 hu0]
    simp [bil]
  · set r := yNorm s u with hr
    have hr0 : 0 < r := lt_of_le_of_ne (yNorm_nonneg _ _) (Ne.symm hu0)
    have hw : ((r⁻¹ : ℝ) : ℂ) • u ∈ S := by
      show yNorm s _ = 1
      rw [yNorm_smul' hs0, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hr0.le), ← hr,
        inv_mul_cancel₀ hr0.ne']
    obtain ⟨e, he, hwe⟩ := mem_iUnion₂.1 (ht hw)
    refine ⟨t.equivFin ⟨e, he⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    have hwe' : 1 / 2 < (bil (((r⁻¹ : ℝ) : ℂ) • u) (g e)).re := hwe
    rw [bil_smul_left, Complex.re_ofReal_mul] at hwe'
    have h3 : r * (1 / 2) < (bil u (g e)).re := by rwa [lt_inv_mul_iff₀ hr0] at hwe'
    linarith

/-- Integrability of a bounded a.e.-strongly measurable function on `[a, b)`. -/
theorem integrableOn_Ico_of_bound {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : AEStronglyMeasurable f volume) {C a b : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) : IntegrableOn f (Ico a b) := by
  refine Integrable.mono' ((continuous_const (y := C)).integrableOn_Icc.mono_set Ico_subset_Icc_self)
    hf.restrict (ae_of_all _ hb)

section Osc

variable {s qX : ℝ} (hE : 1 < s ∧ s < qX ∧ s / (s - 1) < qX)
include hE

/-- `U_z(x) = ∑_k d_k(x) • famF (v k) z`. -/
def oscU (s qX : ℝ) {κ : Type*} [Fintype κ] (d : κ → ℝ → ℂ) (v : κ → ZMod P → ℂ) (z : ℂ) (x : ℝ) : ZMod P → ℂ :=
  ∑ k, d k x • famF s qX (v k) z

theorem measurable_oscU {κ : Type*} [Fintype κ] {d : κ → ℝ → ℂ} (hdm : ∀ k, Measurable (d k))
    (v : κ → ZMod P → ℂ) (z : ℂ) : Measurable (oscU (P := P) s qX d v z) :=
  Finset.measurable_sum _ fun k _ => (hdm k).smul_const _

theorem yNorm_oscU_le {κ : Type*} [Fintype κ] {d : κ → ℝ → ℂ} {Cd : ℝ} (hdb : ∀ k x, ‖d k x‖ ≤ Cd)
    (v : κ → ZMod P → ℂ) (z : ℂ) {p : ℝ} (hp : 1 ≤ p) (x : ℝ) :
    yNorm p (oscU (P := P) s qX d v z x) ≤ ∑ k, Cd * yNorm p (famF s qX (v k) z) := by
  refine (yNorm_sum_le hp _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [yNorm_smul' (by linarith)]
  exact mul_le_mul_of_nonneg_right (hdb k x) (yNorm_nonneg _ _)

theorem integrableOn_yNorm_oscU {κ : Type*} [Fintype κ] {d : κ → ℝ → ℂ} (hdm : ∀ k, Measurable (d k)) {Cd : ℝ}
    (hdb : ∀ k x, ‖d k x‖ ≤ Cd) (v : κ → ZMod P → ℂ) (z : ℂ) {p : ℝ} (hp : 1 ≤ p) (a b : ℝ) :
    IntegrableOn (fun x => yNorm p (oscU (P := P) s qX d v z x)) (Ico a b) := by
  refine integrableOn_Ico_of_bound ((measurable_yNorm_fun p).comp (measurable_oscU hE hdm v z)).aestronglyMeasurable
    (C := ∑ k, Cd * yNorm p (famF s qX (v k) z)) fun x => ?_
  simp only [Function.comp_apply]
  rw [Real.norm_of_nonneg (yNorm_nonneg _ _)]
  exact yNorm_oscU_le hE hdb v z hp x

/-- **Interpolation of the mean oscillation on one interval.** -/
theorem osc_interp {ν : Measure ℝ} (hν : PJProp (2 / qX) ν) {κ : Type*} [Fintype κ] (d : κ → ℝ → ℂ)
    (hdm : ∀ k, Measurable (d k)) {Cd : ℝ} (hdb : ∀ k x, ‖d k x‖ ≤ Cd) (v : κ → ZMod P → ℂ) {a b Cb : ℝ}
    (hab : a < b) (hCb : 0 ≤ Cb)
    (h0 : ∀ t : ℝ, ∫⁻ x in Ico a b, ENNReal.ofReal (yNorm (s / rF s qX) (oscU s qX d v (t * I) x)) ≤
      ENNReal.ofReal (Cb * (b - a))) :
    ENNReal.ofReal (((b - a)⁻¹ * ∫ x in Ico a b, yNorm s (oscU s qX d v ((2 / qX : ℝ) : ℂ) x)) ^ qX) ≤
      ENNReal.ofReal (2 ^ qX * Cb ^ (qX - 2)) *
        ∫⁻ t, ENNReal.ofReal (((b - a)⁻¹ * ∫ x in Ico a b, yNorm 2 (oscU s qX d v (1 + t * I) x)) ^ 2) ∂ν := by
  classical
  have hq2 := two_lt_qX hE
  have hs : 0 < s := by linarith [hE.1]
  have hs1 : 1 ≤ s := hE.1.le
  have hrF := rF_pos hE
  have hrG := rG_pos hE
  have hsC := sC_pos hE
  have hba : 0 < b - a := sub_pos.2 hab
  have hp0 : 1 ≤ s / rF s qX := by rw [le_div_iff₀ hrF]; linarith [rF_lt hE]
  set U := oscU (P := P) s qX d v with hUdef
  set θc : ℂ := ((2 / qX : ℝ) : ℂ) with hθc
  obtain ⟨N, G, hG1, hGn⟩ := exists_norming_net (P := P) hE.1 (holder_s hE)
  -- the partition
  set cond : Fin N → ℝ → Prop := fun j x => yNorm s (U θc x) ≤ 2 * (bil (U θc x) (G j)).re with hcond
  set A : Fin N → Set ℝ := fun j => {x | cond j x} ∩ ⋂ i, ⋂ (_ : i < j), {x | ¬ cond i x} with hA
  have hcm : ∀ j, MeasurableSet {x | cond j x} := fun j =>
    measurableSet_le ((measurable_yNorm_fun s).comp (measurable_oscU hE hdm v θc))
      (measurable_const.mul (Complex.measurable_re.comp
        ((continuous_bil_left (G j)).measurable.comp (measurable_oscU hE hdm v θc))))
  have hAm : ∀ j, MeasurableSet (A j) := fun j =>
    (hcm j).inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => (hcm i).compl)
  have hAx : ∀ x, ∃ j0, (∀ j, x ∈ A j ↔ j = j0) ∧ cond j0 x := by
    intro x
    set S : Finset (Fin N) := Finset.univ.filter (fun j : Fin N => cond j x)
    have hne : S.Nonempty := by
      obtain ⟨j, hj⟩ := hGn (U θc x)
      exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩⟩
    refine ⟨S.min' hne, fun j => ⟨fun hj => ?_, fun hj => ?_⟩, (Finset.mem_filter.1 (S.min'_mem hne)).2⟩
    · obtain ⟨hj1, hj2⟩ := hj
      have hjS : j ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hj1⟩
      rcases lt_or_eq_of_le (S.min'_le j hjS) with hlt | heq
      · exact absurd (Finset.mem_filter.1 (S.min'_mem hne)).2
          (mem_iInter₂.1 hj2 (S.min' hne) hlt)
      · exact heq.symm
    · subst hj
      refine ⟨(Finset.mem_filter.1 (S.min'_mem hne)).2, mem_iInter₂.2 fun i hi hci => ?_⟩
      exact absurd (S.min'_le i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hci⟩)) (not_le.2 hi)
  set e : Fin N → ℝ → ℂ := fun j => (A j).indicator fun _ => (1 : ℂ) with he
  have hsum1 : ∀ x (f : Fin N → ℂ), ∃ j0, cond j0 x ∧ ∑ j, e j x * f j = f j0 := by
    intro x f
    obtain ⟨j0, hj0, hc⟩ := hAx x
    refine ⟨j0, hc, ?_⟩
    rw [Finset.sum_eq_single j0]
    · simp [he, (hj0 j0).2 rfl]
    · intro j _ hj
      simp [he, show x ∉ A j from fun h => hj ((hj0 j).1 h)]
    · simp
  -- the coefficients and the identity
  set c : Fin N → κ → ℂ := fun j k => ∫ x in Ico a b, (A j).indicator (d k) x with hc
  have hFid : ∀ z x, ∑ j, e j x * bil (U z x) (famG s qX (G j) z) =
      ∑ j, ∑ k, (A j).indicator (d k) x * bil (famF s qX (v k) z) (famG s qX (G j) z) := by
    intro z x
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hUdef, oscU, bil_sum_left, bil_smul_left, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hx : x ∈ A j <;> simp [he, hx]
  have hint : ∀ j k, IntegrableOn ((A j).indicator (d k)) (Ico a b) := fun j k =>
    integrableOn_Ico_of_bound ((hdm k).indicator (hAm j)).aestronglyMeasurable (C := Cd) fun x => by
      by_cases hx : x ∈ A j
      · simp [hx, hdb k x]
      · simp only [hx, not_false_eq_true, indicator_of_notMem, norm_zero]
        exact (norm_nonneg _).trans (hdb k x)
  have hFint : ∀ z, IntegrableOn (fun x => ∑ j, e j x * bil (U z x) (famG s qX (G j) z)) (Ico a b) := by
    intro z
    simp_rw [hFid z]
    exact integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ => (hint j k).mul_const _
  set Φ : ℂ → ℂ := fun z => ((b - a : ℝ) : ℂ)⁻¹ *
    ∑ j, ∑ k, c j k * bil (famF s qX (v k) z) (famG s qX (G j) z) with hΦ
  have hΦint : ∀ z, Φ z = ((b - a : ℝ) : ℂ)⁻¹ * ∫ x in Ico a b, ∑ j, e j x * bil (U z x) (famG s qX (G j) z) := by
    intro z
    rw [hΦ]
    simp_rw [hFid z]
    rw [integral_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ => (hint j k).mul_const _]
    congr 1
    refine Finset.sum_congr rfl (fun (j : Fin N) _ => ?_)
    rw [integral_finset_sum _ fun k _ => (hint j k).mul_const _]
    exact Finset.sum_congr rfl (fun (k : κ) _ => (integral_mul_const _ _).symm)
  -- holomorphy and boundedness
  have hdF : ∀ k y, Differentiable ℂ (fun z => famF s qX (v k) z y) :=
    fun k y => differentiable_famVec _ _ _ _ _ _ y
  have hdG : ∀ j y, Differentiable ℂ (fun z => famG s qX (G j) z y) :=
    fun j y => differentiable_famVec _ _ _ _ _ _ y
  have hdiff : Differentiable ℂ Φ := by
    simp only [hΦ, bil]
    fun_prop
  have habF : 0 < rF s qX + (s / 2 - rF s qX) := by linarith
  have habG : 0 < rG s qX + (sC s / 2 - rG s qX) := by linarith
  have hF := fun k y {z : ℂ} (hz : z.re ∈ Set.Icc (0 : ℝ) 1) =>
    norm_famVec_le (a' := -rF s qX) (b' := (qX - s) / 2 + rF s qX) hs hrF habF (v k) y hz
  have hG := fun j y {z : ℂ} (hz : z.re ∈ Set.Icc (0 : ℝ) 1) =>
    norm_famVec_le (a' := 0) (b' := 0) hsC hrG habG (G j) y hz
  have hbd : BddAbove ((fun z => ‖Φ z‖) '' verticalClosedStrip 0 1) := by
    refine ⟨‖((b - a : ℝ) : ℂ)⁻¹‖ * ∑ j, ∑ k, ‖c j k‖ * (‖(P : ℂ)⁻¹‖ * ∑ y,
      ((‖v k y‖ ^ rF s qX + ‖v k y‖ ^ (rF s qX + (s / 2 - rF s qX))) *
        (yNorm s (v k) ^ (-rF s qX) + yNorm s (v k) ^ (-rF s qX + ((qX - s) / 2 + rF s qX)))) *
      ((‖G j y‖ ^ rG s qX + ‖G j y‖ ^ (rG s qX + (sC s / 2 - rG s qX))) *
        (yNorm (sC s) (G j) ^ (0 : ℝ) + yNorm (sC s) (G j) ^ ((0 : ℝ) + 0)))), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z.re ∈ Set.Icc (0 : ℝ) 1 := hz
    show ‖Φ z‖ ≤ _
    simp only [hΦ, norm_mul]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_))) (norm_nonneg _)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    simp only [bil, norm_mul]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)) (norm_nonneg _)
    rw [norm_mul]
    exact mul_le_mul (hF k y hz') (hG j y hz') (norm_nonneg _)
      ((norm_nonneg _).trans (hF k y hz'))
  -- the endpoint bounds
  have hbinv : ‖((b - a : ℝ) : ℂ)⁻¹‖ = (b - a)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hba.le]
  have hend : ∀ (z : ℂ) (p p' : ℝ), p.HolderConjugate p' → 1 ≤ p' → (∀ j, yNorm p (famG s qX (G j) z) ≤ 1) →
      ‖Φ z‖ ≤ (b - a)⁻¹ * ∫ x in Ico a b, yNorm p' (U z x) := by
    intro z p p' hpp hp' hGz
    rw [hΦint, norm_mul, hbinv]
    refine mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le
      (integrableOn_yNorm_oscU hE hdm hdb v z hp' a b) (ae_of_all _ fun x => ?_)) (by positivity)
    obtain ⟨j0, -, hj0⟩ := hsum1 x (fun j => bil (U z x) (famG s qX (G j) z))
    rw [hj0]
    exact (norm_bil_le hpp _ _).trans (mul_le_of_le_one_right (yNorm_nonneg _ _) (hGz j0))
  have hit : ∀ t : ℝ, ‖Φ (t * I)‖ ≤ Cb := by
    intro t
    refine (hend _ _ _ (holder_0 hE) hp0 fun j => yNorm_famG_zero hE (hG1 j) t).trans ?_
    have hI := integrableOn_yNorm_oscU hE hdm hdb v (t * I) hp0 a b
    have h1 : ∫ x in Ico a b, yNorm (s / rF s qX) (U (t * I) x) ≤ Cb * (b - a) := by
      have := h0 t
      rw [← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun x => yNorm_nonneg _ _)] at this
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
    calc (b - a)⁻¹ * ∫ x in Ico a b, yNorm (s / rF s qX) (U (t * I) x) ≤ (b - a)⁻¹ * (Cb * (b - a)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Cb := by field_simp
  have h1t : ∀ t : ℝ, ‖Φ (1 + t * I)‖ ≤ (b - a)⁻¹ * ∫ x in Ico a b, yNorm 2 (U (1 + t * I) x) :=
    fun t => hend _ _ _ holder_two (by norm_num) fun j => yNorm_famG_one hE (hG1 j) t
  have hGθ : ∀ j, famG s qX (G j) θc = G j := fun j => famG_theta hE (G j)
  have hθ : (b - a)⁻¹ * ∫ x in Ico a b, yNorm s (U θc x) ≤ 2 * ‖Φ θc‖ := by
    have hre : (Φ θc).re = (b - a)⁻¹ * ∫ x in Ico a b, (∑ j, e j x * bil (U θc x) (G j)).re := by
      rw [hΦint]
      simp only [hGθ]
      rw [← Complex.ofReal_inv, Complex.re_ofReal_mul]
      congr 1
      have := integral_re (μ := volume.restrict (Ico a b)) (hFint θc)
      simp only [hGθ] at this
      exact this.symm
    have hle : ∫ x in Ico a b, yNorm s (U θc x) ≤ ∫ x in Ico a b, 2 * (∑ j, e j x * bil (U θc x) (G j)).re := by
      refine integral_mono (integrableOn_yNorm_oscU hE hdm hdb v θc hs1 a b) ?_ fun x => ?_
      · have := (hFint θc).re.const_mul 2
        simp only [hGθ] at this
        exact this
      · obtain ⟨j0, hc0, hj0⟩ := hsum1 x (fun j => bil (U θc x) (G j))
        show yNorm s (U θc x) ≤ 2 * (∑ j, e j x * bil (U θc x) (G j)).re
        rw [hj0]
        exact hc0
    rw [integral_const_mul] at hle
    calc (b - a)⁻¹ * ∫ x in Ico a b, yNorm s (U θc x) ≤ (b - a)⁻¹ *
          (2 * ∫ x in Ico a b, (∑ j, e j x * bil (U θc x) (G j)).re) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 2 * (Φ θc).re := by rw [hre]; ring
      _ ≤ 2 * ‖Φ θc‖ := by gcongr; exact Complex.re_le_norm _
  -- Poisson-Jensen
  have hPJ := hν Φ hdiff.diffContOnCl hbd hCb hit
  have hqq : 2 / (2 / qX) = qX := by field_simp
  rw [hqq] at hPJ
  have hq0 : (0 : ℝ) ≤ qX := by linarith
  have hA0 : 0 ≤ (b - a)⁻¹ * ∫ x in Ico a b, yNorm s (U θc x) :=
    mul_nonneg (by positivity) (integral_nonneg fun x => yNorm_nonneg _ _)
  calc ENNReal.ofReal (((b - a)⁻¹ * ∫ x in Ico a b, yNorm s (U θc x)) ^ qX)
      ≤ ENNReal.ofReal ((2 * ‖Φ θc‖) ^ qX) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hA0 hθ hq0)
    _ = ENNReal.ofReal (2 ^ qX) * ‖Φ θc‖ₑ ^ qX := by
        rw [Real.mul_rpow (by norm_num) (norm_nonneg _), ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0, ofReal_norm]
    _ ≤ ENNReal.ofReal (2 ^ qX) * (ENNReal.ofReal (Cb ^ (qX - 2)) *
          ∫⁻ t, ‖Φ (1 + t * I)‖ₑ ^ (2 : ℝ) ∂ν) := by gcongr
    _ ≤ ENNReal.ofReal (2 ^ qX) * (ENNReal.ofReal (Cb ^ (qX - 2)) *
          ∫⁻ t, ENNReal.ofReal (((b - a)⁻¹ * ∫ x in Ico a b, yNorm 2 (U (1 + t * I) x)) ^ 2) ∂ν) := by
        gcongr with t
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two, Real.rpow_two]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (h1t t) 2)
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

end Osc

end PrimeBHT.TimeFrequency.X2.Pint
