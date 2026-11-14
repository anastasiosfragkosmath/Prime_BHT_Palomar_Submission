module

public import PrimeBHT.TimeFrequency.X2.CZ.WeakType
public import PrimeBHT.TimeFrequency.X2.CZ.Marcinkiewicz

/-!
# V08 phase 3: strong type `(q, s)` for `1 < q < s` from weak `(1,1)` and strong `(s,s)`

For a kernel `K : ℝ → ℝ → ℂ` (bounded measurable) satisfying the Hörmander condition `hH` and the
strong `(s, s)` bound `hGood` (`‖K * g‖_{L^s(ℝ; L^s(Y))} ≤ A ‖g‖_{L^s(ℝ; L^s(Y))}` on the class `𝒞` of
`g` with measurable, integrable, bounded fibres), `marcinkiewicz_kernel` proves
`‖K * F‖_{L^q(ℝ; L^s(Y))} ≲ ‖F‖_{L^q(ℝ; L^s(Y))}` for `1 < q < s`, uniformly in `P`.

The interpolation is applied to `U = ‖K * F‖_X` and `G = ‖F‖_X` (`X = L^s(Y)`) through the decomposition
`F = F 1_{G > λ} + F 1_{G ≤ λ}` *by the norm of `F`*: the weak `(1,1)` theorem `weak11_of_kernel` for the
first part, `hGood` for the second.  Nothing uses a normed-space structure on `ZMod P → ℂ`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology Real

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

open PrimeBHT.Statements

section Trunc

variable {P : ℕ} [NeZero P] {s : ℝ}

/-- The part of `F` where `‖F(x)‖_X > λ`. -/
def truncAbove (s lam : ℝ) (F : ℝ → ZMod P → ℂ) : ℝ → ZMod P → ℂ :=
  fun x y => if lam < yNorm s (F x) then F x y else 0

/-- The part of `F` where `‖F(x)‖_X ≤ λ`. -/
def truncBelow (s lam : ℝ) (F : ℝ → ZMod P → ℂ) : ℝ → ZMod P → ℂ :=
  fun x y => if yNorm s (F x) ≤ lam then F x y else 0

theorem truncAbove_add_truncBelow (s lam : ℝ) (F : ℝ → ZMod P → ℂ) (x : ℝ) (y : ZMod P) :
    truncAbove s lam F x y + truncBelow s lam F x y = F x y := by
  unfold truncAbove truncBelow
  by_cases h : lam < yNorm s (F x)
  · simp [h, not_le.2 h]
  · simp [h, not_lt.1 h]

theorem yNorm_truncAbove (hs : 0 < s) (lam : ℝ) (F : ℝ → ZMod P → ℂ) (x : ℝ) :
    yNorm s (truncAbove s lam F x) = if lam < yNorm s (F x) then yNorm s (F x) else 0 := by
  unfold truncAbove
  by_cases h : lam < yNorm s (F x)
  · simp [h]
  · have : (fun y => if lam < yNorm s (F x) then F x y else 0) = 0 := by ext y; simp [h]
    rw [this]; simp [h, yNorm_zero' hs]

theorem yNorm_truncBelow (hs : 0 < s) (lam : ℝ) (F : ℝ → ZMod P → ℂ) (x : ℝ) :
    yNorm s (truncBelow s lam F x) = if yNorm s (F x) ≤ lam then yNorm s (F x) else 0 := by
  unfold truncBelow
  by_cases h : yNorm s (F x) ≤ lam
  · simp [h]
  · have : (fun y => if yNorm s (F x) ≤ lam then F x y else 0) = 0 := by ext y; simp [h]
    rw [this]; simp [h, yNorm_zero' hs]

/-- The class `𝒞` of functions with measurable, integrable, bounded fibres is closed under the two
truncations. -/
theorem truncAbove_facts (_hs : 0 < s) (lam : ℝ) {F : ℝ → ZMod P → ℂ}
    (hFm : ∀ y, Measurable fun u => F u y) (hFi : ∀ y, Integrable fun u => F u y)
    (hFb : ∀ y, ∃ C, ∀ u, ‖F u y‖ ≤ C) :
    (∀ y, Measurable fun u => truncAbove s lam F u y) ∧
      (∀ y, Integrable fun u => truncAbove s lam F u y) ∧
      (∀ y, ∃ C, ∀ u, ‖truncAbove s lam F u y‖ ≤ C) := by
  have hG : Measurable fun x => yNorm s (F x) := measurable_yNorm s hFm
  have hm : ∀ y, Measurable fun u => truncAbove s lam F u y := fun y =>
    Measurable.ite (measurableSet_lt measurable_const hG) (hFm y) measurable_const
  refine ⟨hm, fun y => ?_, fun y => ?_⟩
  · refine Integrable.mono' (hFi y).norm (hm y).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    unfold truncAbove
    by_cases h : lam < yNorm s (F u) <;> simp [h]
  · obtain ⟨C, hC⟩ := hFb y
    refine ⟨C, fun u => ?_⟩
    unfold truncAbove
    by_cases h : lam < yNorm s (F u)
    · simp only [h, ite_true]; exact hC u
    · simp only [h, ite_false, norm_zero]; exact (norm_nonneg _).trans (hC u)

theorem truncBelow_facts (_hs : 0 < s) (lam : ℝ) {F : ℝ → ZMod P → ℂ}
    (hFm : ∀ y, Measurable fun u => F u y) (hFi : ∀ y, Integrable fun u => F u y)
    (hFb : ∀ y, ∃ C, ∀ u, ‖F u y‖ ≤ C) :
    (∀ y, Measurable fun u => truncBelow s lam F u y) ∧
      (∀ y, Integrable fun u => truncBelow s lam F u y) ∧
      (∀ y, ∃ C, ∀ u, ‖truncBelow s lam F u y‖ ≤ C) := by
  have hG : Measurable fun x => yNorm s (F x) := measurable_yNorm s hFm
  have hm : ∀ y, Measurable fun u => truncBelow s lam F u y := fun y =>
    Measurable.ite (measurableSet_le hG measurable_const) (hFm y) measurable_const
  refine ⟨hm, fun y => ?_, fun y => ?_⟩
  · refine Integrable.mono' (hFi y).norm (hm y).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    unfold truncBelow
    by_cases h : yNorm s (F u) ≤ lam <;> simp [h]
  · obtain ⟨C, hC⟩ := hFb y
    refine ⟨C, fun u => ?_⟩
    unfold truncBelow
    by_cases h : yNorm s (F u) ≤ lam
    · simp only [h, ite_true]; exact hC u
    · simp only [h, ite_false, norm_zero]; exact (norm_nonneg _).trans (hC u)

end Trunc

section Main

variable {P : ℕ} [NeZero P] {s : ℝ}

/-- **Strong type `(q, s)`, `1 < q < s`, from weak `(1,1)` and strong `(s,s)`** (Marcinkiewicz, applied to
`‖K * F‖_X` and `‖F‖_X`; `X = L^s(Y_P)`).  Constants independent of `P`. -/
theorem marcinkiewicz_kernel (hs : 1 < s) {K : ℝ → ℝ → ℂ} {M : ℝ}
    (hKm : Measurable (Function.uncurry K)) (hKb : ∀ x z, ‖K x z‖ ≤ M) {cH A : ℝ} (hA0 : 0 ≤ A)
    (hcH : 0 ≤ cH)
    (hH : ∀ c u ℓ : ℝ, |u - c| ≤ ℓ / 2 →
      ∫⁻ x in {x : ℝ | ℓ < |x - c|}, ‖K x u - K x c‖ₑ ≤ ENNReal.ofReal cH)
    (hGood : ∀ g : ℝ → ZMod P → ℂ, (∀ y, Measurable fun u => g u y) →
      (∀ y, Integrable fun u => g u y) → (∀ y, ∃ C, ∀ u, ‖g u y‖ ≤ C) →
      ∫⁻ x, ENNReal.ofReal (yNorm s (fun y => kop K (fun u => g u y) x)) ^ s ≤
        ENNReal.ofReal A ^ s * ∫⁻ u, ENNReal.ofReal (yNorm s (g u)) ^ s)
    {q : ℝ} (hq : 1 < q) (hqs : q < s)
    (F : ℝ → ZMod P → ℂ) (hFm : ∀ y, Measurable fun u => F u y)
    (hFi : ∀ y, Integrable fun u => F u y) (hFb : ∀ y, ∃ C, ∀ u, ‖F u y‖ ≤ C) :
    ∫⁻ x, ENNReal.ofReal (yNorm s (fun y => kop K (fun u => F u y) x)) ^ q ≤
      ENNReal.ofReal (q * 2 ^ q * ((2 + 2 ^ (2 * s - 1) * A ^ s + 4 * cH) / (q - 1) +
        A ^ s / (s - q))) * ∫⁻ x, ENNReal.ofReal (yNorm s (F x)) ^ q := by
  have hs0 : 0 < s := by linarith
  have hC₀ : 0 ≤ 2 + 2 ^ (2 * s - 1) * A ^ s + 4 * cH := by positivity
  have hGm : Measurable fun x => yNorm s (F x) := measurable_yNorm s hFm
  have hUm : Measurable fun x => yNorm s (fun y => kop K (fun u => F u y) x) :=
    measurable_yNorm s (fun y => measurable_kop hKm (hFm y))
  refine marcinkiewicz_aux (G := fun x => yNorm s (F x)) hUm hGm (fun x => yNorm_nonneg s _)
    (fun x => yNorm_nonneg s _) hq hqs hC₀ hA0 ?_
  intro lam hlam
  obtain ⟨hAm, hAi, hAb⟩ := truncAbove_facts hs0 lam hFm hFi hFb
  obtain ⟨hBm, hBi, hBb⟩ := truncBelow_facts hs0 lam hFm hFi hFb
  set Fa := truncAbove s lam F with hFa
  set Fb := truncBelow s lam F with hFb'
  -- linearity and the triangle inequality
  have hlin : ∀ x y, kop K (fun u => F u y) x = kop K (fun u => Fa u y) x + kop K (fun u => Fb u y) x := by
    intro x y
    unfold kop
    rw [← integral_add (integrable_kernel_mul hKm hKb (hAi y) x)
      (integrable_kernel_mul hKm hKb (hBi y) x)]
    congr 1; ext u
    rw [← mul_add, hFa, hFb', truncAbove_add_truncBelow]
  have htri : ∀ x, yNorm s (fun y => kop K (fun u => F u y) x) ≤
      yNorm s (fun y => kop K (fun u => Fa u y) x) + yNorm s (fun y => kop K (fun u => Fb u y) x) := by
    intro x
    have : (fun y => kop K (fun u => F u y) x) =
        (fun y => kop K (fun u => Fa u y) x) + (fun y => kop K (fun u => Fb u y) x) := by
      ext y; exact hlin x y
    rw [this]; exact yNorm_add_le hs.le _ _
  have hsub : {x : ℝ | 2 * lam < yNorm s (fun y => kop K (fun u => F u y) x)} ⊆
      {x : ℝ | lam < yNorm s (fun y => kop K (fun u => Fa u y) x)} ∪
        {x : ℝ | lam < yNorm s (fun y => kop K (fun u => Fb u y) x)} := by
    intro x hx
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hcon hx
    linarith [htri x, hcon.1, hcon.2]
  -- the weak (1,1) part
  have hweak := weak11_of_kernel hs hKm hKb hA0 hcH hH hGood Fa hAm hAi hAb hlam
  have hA1 : ∫⁻ u, ENNReal.ofReal (yNorm s (Fa u)) =
      ∫⁻ x in {x | lam < yNorm s (F x)}, ENNReal.ofReal (yNorm s (F x)) := by
    rw [← lintegral_indicator (measurableSet_lt measurable_const hGm)]
    refine lintegral_congr fun x => ?_
    rw [hFa, yNorm_truncAbove hs0]
    by_cases h : lam < yNorm s (F x) <;> simp [h, indicator]
  -- the strong (s,s) part, via Chebyshev
  have hBmeas : Measurable fun x => yNorm s (fun y => kop K (fun u => Fb u y) x) :=
    measurable_yNorm s (fun y => measurable_kop hKm (hBm y))
  set ε : ℝ≥0∞ := ENNReal.ofReal (lam ^ s) with hε
  have hcheb := mul_meas_ge_le_lintegral₀ (μ := volume)
    (f := fun x => ENNReal.ofReal (yNorm s (fun y => kop K (fun u => Fb u y) x)) ^ s)
    (hBmeas.ennreal_ofReal.pow_const s).aemeasurable ε
  have hsetB : {x : ℝ | lam < yNorm s (fun y => kop K (fun u => Fb u y) x)} ⊆
      {x : ℝ | ε ≤ ENNReal.ofReal (yNorm s (fun y => kop K (fun u => Fb u y) x)) ^ s} := by
    intro x hx
    simp only [mem_ofPred_eq, hε] at hx ⊢
    rw [ENNReal.ofReal_rpow_of_nonneg (yNorm_nonneg s _) hs0.le]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hlam.le hx.le hs0.le)
  have hB1 : ∫⁻ u, ENNReal.ofReal (yNorm s (Fb u)) ^ s =
      ∫⁻ x in {x | yNorm s (F x) ≤ lam}, ENNReal.ofReal (yNorm s (F x)) ^ s := by
    rw [← lintegral_indicator (measurableSet_le hGm measurable_const)]
    refine lintegral_congr fun x => ?_
    rw [hFb', yNorm_truncBelow hs0]
    by_cases h : yNorm s (F x) ≤ lam
    · simp [h, indicator]
    · simp [h, indicator, ENNReal.zero_rpow_of_pos hs0]
  have hposε : ε ≠ 0 := by
    simp only [hε, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.rpow_pos_of_pos hlam s
  have hgoodB := hGood Fb hBm hBi hBb
  have h4 := meas_le_of_mul_le hposε ENNReal.ofReal_ne_top
    (hcheb.trans (hgoodB.trans (le_of_eq (by rw [hB1]))))
  have h5 : ε⁻¹ * (ENNReal.ofReal A ^ s *
      ∫⁻ x in {x | yNorm s (F x) ≤ lam}, ENNReal.ofReal (yNorm s (F x)) ^ s) =
      ENNReal.ofReal ((A / lam) ^ s) * ∫⁻ x in {x | yNorm s (F x) ≤ lam}, ENNReal.ofReal (yNorm s (F x)) ^ s := by
    rw [hε, ← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hlam s),
      ENNReal.ofReal_rpow_of_nonneg hA0 hs0.le, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [Real.div_rpow hA0 hlam.le]; ring
  calc volume {x : ℝ | 2 * lam < yNorm s (fun y => kop K (fun u => F u y) x)}
      ≤ volume ({x : ℝ | lam < yNorm s (fun y => kop K (fun u => Fa u y) x)} ∪
        {x : ℝ | lam < yNorm s (fun y => kop K (fun u => Fb u y) x)}) := measure_mono hsub
    _ ≤ volume {x : ℝ | lam < yNorm s (fun y => kop K (fun u => Fa u y) x)} +
        volume {x : ℝ | lam < yNorm s (fun y => kop K (fun u => Fb u y) x)} := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((2 + 2 ^ (2 * s - 1) * A ^ s + 4 * cH) / lam) *
          (∫⁻ x in {x | lam < yNorm s (F x)}, ENNReal.ofReal (yNorm s (F x))) +
        ENNReal.ofReal ((A / lam) ^ s) *
          (∫⁻ x in {x | yNorm s (F x) ≤ lam}, ENNReal.ofReal (yNorm s (F x)) ^ s) := by
        refine add_le_add ?_ ?_
        · rw [← hA1]; exact hweak
        · exact (measure_mono hsetB).trans (h4.trans (le_of_eq h5))

end Main

end PrimeBHT.TimeFrequency.X2.CZ
