module

public import PrimeBHT.TimeFrequency.X2.EngTail.Ops

/-!
# X2, node B5: the tail estimate

For the tiles `T ⊆ S` and the maximal tiles `Lm`, a measurable `F'` with `‖F'‖_X ≤ 1` whose tile densities are at most `λ`,
and `W ⊇ ⋃_{L ∈ Lm} 3 I_L`: the operator `K_T` applied to `F' 1_{W^c}` satisfies pointwise
`‖K_T (F' 1_{W^c})(x)‖_X ≤ ∑_{L ∈ Lm} C λ (1 + |x - c_L|/|I_L|)^{-2}` (`tail_op_le`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- The constant of the tail bound. -/
def tailConstK (N M Cφ Cκ : ℝ) : ℝ := 16 * (Cφ * Cκ) * (5 / 2) ^ M * latConst (N - M - 2)

theorem tailConstK_nonneg {N M Cφ Cκ : ℝ} (hN : M + 4 ≤ N) (hCφ : 0 ≤ Cφ) (hCκ : 0 ≤ Cκ) :
    0 ≤ tailConstK N M Cφ Cκ := by
  unfold tailConstK
  have := latConst_nonneg (by linarith : (1 : ℝ) < N - M - 2)
  positivity

/-- `z ↦ |I|⁻¹ (1 + |z - c|/|I|)^{-M} u(z)` is integrable for bounded measurable `u`. -/
theorem integrable_density {M c L : ℝ} (hM : 1 < M) (hL : 0 < L) {u : ℝ → ℝ} (hum : Measurable u)
    (hu0 : ∀ z, 0 ≤ u z) (hu1 : ∀ z, u z ≤ 1) :
    Integrable (fun z => L⁻¹ * (1 + |z - c| / L) ^ (-M) * u z) := by
  have hint : Integrable (fun z : ℝ => L⁻¹ * (1 + |z - c| / L) ^ (-M)) :=
    (integrable_one_add_abs_sub_div_rpow hM c hL).const_mul _
  refine hint.mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact ((measurable_const.mul ((measurable_const.add
      ((continuous_abs.measurable.comp (measurable_id.sub_const c)).div_const L)).pow_const _)).mul hum).aestronglyMeasurable
  · have h0 : 0 ≤ L⁻¹ * (1 + |z - c| / L) ^ (-M) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (hu0 z))]
    calc _ ≤ L⁻¹ * (1 + |z - c| / L) ^ (-M) * 1 := mul_le_mul_of_nonneg_left (hu1 z) h0
      _ = _ := mul_one _

section Tail

variable {ι : Type*} [DecidableEq ι]

/-- **Tail, pointwise in `(x, z)`**: the tiles `T`, each contained in a maximal interval `I_{Lf i}`, see a point `z` outside all
`3 I_L` with total size `∑_L C |I_L|⁻¹ (1 + |z - c_L|/|I_L|)^{-M} (1 + |x - c_L|/|I_L|)^{-2}`. -/
theorem tail_abs_le {N M Cφ Cκ : ℝ} (hM : 3 ≤ M) (hN : M + 4 ≤ N) (hCφ : 0 ≤ Cφ) (hCκ : 0 ≤ Cκ)
    (T Lm : Finset ι) (j v : ι → ℤ) (φ κ : ι → ℝ → ℂ)
    (hb : ∀ i ∈ T, TileBound N M Cφ Cκ (j i) (v i) (φ i) (κ i))
    (hinj : Set.InjOn (fun i => (j i, v i)) (T : Set ι)) (Lf : ι → ι)
    (hLf : ∀ i ∈ T, Lf i ∈ Lm ∧ dyadicInt (j i) (v i) ⊆ dyadicInt (j (Lf i)) (v (Lf i))) {x z : ℝ}
    (hz : ∀ L ∈ Lm, 3 * (2 : ℝ) ^ (j L) / 2 ≤ |z - (2 : ℝ) ^ (j L) * ((v L : ℝ) + 1 / 2)|) :
    ∑ i ∈ T, ‖φ i x * κ i (x - z)‖ ≤ ∑ L ∈ Lm, tailConstK N M Cφ Cκ *
      (((2 : ℝ) ^ (j L))⁻¹ * ((1 + |z - (2 : ℝ) ^ (j L) * ((v L : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j L)) ^ (-M) *
        (1 + |x - (2 : ℝ) ^ (j L) * ((v L : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j L)) ^ (-(2 : ℝ)))) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Lf) (t := Lm) (fun i hi => (hLf i hi).1)]
  refine Finset.sum_le_sum fun L hL => ?_
  have hsub : (T.filter (fun i => Lf i = L) : Set ι) ⊆ (T : Set ι) := fun i hi =>
    (Finset.mem_filter.1 hi).1
  have := sum_tail_le hM hN hCφ hCκ (T.filter (fun i => Lf i = L)) j v φ κ
    (fun i hi => hb i (Finset.mem_filter.1 hi).1) (hinj.mono hsub) (jL := j L) (vL := v L)
    (fun i hi => by
      obtain ⟨hiT, hiL⟩ := Finset.mem_filter.1 hi
      have hsubI := (hLf i hiT).2
      rw [hiL] at hsubI
      obtain ⟨h1, h2⟩ := dyadicInt_subset_geom hsubI
      refine ⟨h1, h2.trans ?_⟩
      have := two_zpow_pos' (j i)
      linarith) (hz L hL) x
  refine this.trans (le_of_eq ?_)
  unfold tailConstK
  ring

/-- **Tail, operator form**. -/
theorem tail_op_le {P : ℕ} [NeZero P] {N M Cφ Cκ s lam : ℝ} (hs : 1 < s) (hM : 3 ≤ M) (hN : M + 4 ≤ N)
    (hCφ : 0 ≤ Cφ) (hCκ : 0 ≤ Cκ) (T Lm : Finset ι) (j v : ι → ℤ) (φ κ : ι → ℝ → ℂ)
    (hb : ∀ i ∈ T, TileBound N M Cφ Cκ (j i) (v i) (φ i) (κ i))
    (hinj : Set.InjOn (fun i => (j i, v i)) (T : Set ι)) (Lf : ι → ι)
    (hLf : ∀ i ∈ T, Lf i ∈ Lm ∧ dyadicInt (j i) (v i) ⊆ dyadicInt (j (Lf i)) (v (Lf i)))
    {F' : ℝ → ZMod P → ℂ} (hF'm : Measurable F') {W : Set ℝ} (hWm : MeasurableSet W)
    (hW : ∀ L ∈ Lm, dil3 j v L ⊆ W) (hu1 : ∀ z, yNorm s (F' z) ≤ 1)
    (hdens : ∀ L ∈ Lm, ∫ z, ((2 : ℝ) ^ (j L))⁻¹ *
      (1 + |z - (2 : ℝ) ^ (j L) * ((v L : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j L)) ^ (-M) * yNorm s (F' z) ≤ lam)
    (x : ℝ) :
    yNorm s (fun y => ∫ z, tileKernel T φ κ x z * (Wᶜ).indicator (fun z => F' z y) z) ≤
      ∑ L ∈ Lm, tailConstK N M Cφ Cκ * lam *
        (1 + |x - (2 : ℝ) ^ (j L) * ((v L : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j L)) ^ (-(2 : ℝ)) := by
  have hs0 : 0 < s := by linarith
  have hM1 : 1 < M := by linarith
  set u : ℝ → ℝ := fun z => yNorm s (F' z) with hu
  have hF'y : ∀ y, Measurable fun z => F' z y := fun y => (measurable_pi_apply y).comp hF'm
  have hum : Measurable u := CZ.measurable_yNorm s hF'y
  have hu0 : ∀ z, 0 ≤ u z := fun z => CZ.yNorm_nonneg s _
  set G : ℝ → ZMod P → ℂ := fun z y => (Wᶜ).indicator (fun z => F' z y) z with hG
  have hGm : ∀ y, Measurable fun z => G z y := fun y => (hF'y y).indicator hWm.compl
  have hGy : ∀ z, yNorm s (G z) = (Wᶜ).indicator u z := by
    intro z
    by_cases hz : z ∈ Wᶜ
    · simp only [hG, hu, indicator_of_mem hz]
    · have : G z = 0 := by funext y; simp only [hG, indicator_of_notMem hz]; rfl
      rw [this, indicator_of_notMem hz]
      exact CZ.yNorm_zero' hs0
  have hKm : Measurable (Function.uncurry (tileKernel T φ κ)) :=
    (continuous_tileKernel T φ κ (fun i hi => (hb i hi).φ_diff.continuous)
      (fun i hi => (hb i hi).κ_diff.continuous)).measurable
  have hLpos : ∀ L ∈ Lm, (0 : ℝ) < (2 : ℝ) ^ (j L) := fun L _ => two_zpow_pos' _
  set TC : ℝ := tailConstK N M Cφ Cκ with hTC
  have hTC0 : 0 ≤ TC := tailConstK_nonneg hN hCφ hCκ
  set fk : ι → ℝ := fun L => (1 + |x - (2 : ℝ) ^ (j L) * ((v L : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j L)) ^ (-(2 : ℝ)) with hfk
  have hfk0 : ∀ L, 0 ≤ fk L := fun L => by simp only [hfk]; positivity
  set dens : ι → ℝ → ℝ := fun L z => ((2 : ℝ) ^ (j L))⁻¹ *
    (1 + |z - (2 : ℝ) ^ (j L) * ((v L : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j L)) ^ (-M) * u z with hdens'
  have hdens0 : ∀ L z, 0 ≤ dens L z := fun L z => by
    have := two_zpow_pos' (j L)
    simp only [hdens']; have := hu0 z; positivity
  have hdensi : ∀ L ∈ Lm, Integrable (dens L) := fun L hL =>
    integrable_density hM1 (hLpos L hL) hum hu0 hu1
  set w : ℝ → ℝ := fun z => ∑ L ∈ Lm, (TC * fk L) * dens L z with hw
  have hwi : Integrable w := integrable_finsetSum _ fun L hL => (hdensi L hL).const_mul _
  have hw0 : ∀ z, 0 ≤ w z := fun z => Finset.sum_nonneg fun L _ => mul_nonneg (mul_nonneg hTC0 (hfk0 L)) (hdens0 L z)
  have hle : ∀ z, ‖tileKernel T φ κ x z‖ * yNorm s (G z) ≤ w z := by
    intro z
    by_cases hz : z ∈ W
    · have : yNorm s (G z) = 0 := by rw [hGy, indicator_of_notMem (by simpa using hz)]
      rw [this, mul_zero]; exact hw0 z
    · have hzc : z ∈ Wᶜ := hz
      rw [hGy, indicator_of_mem hzc]
      have hzL : ∀ L ∈ Lm, 3 * (2 : ℝ) ^ (j L) / 2 ≤ |z - (2 : ℝ) ^ (j L) * ((v L : ℝ) + 1 / 2)| := by
        intro L hL
        have hnot : z ∉ dil3 j v L := fun h => hz (hW L hL h)
        have hl := hLpos L hL
        simp only [dil3, mem_Ico, not_and_or, not_le, not_lt] at hnot
        rcases hnot with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_nonneg (by linarith)]; linarith
      have h1 := tail_abs_le hM hN hCφ hCκ T Lm j v φ κ hb hinj Lf hLf (x := x) hzL
      have h2 : ‖tileKernel T φ κ x z‖ ≤ ∑ i ∈ T, ‖φ i x * κ i (x - z)‖ := norm_sum_le _ _
      have h3 := h2.trans h1
      calc ‖tileKernel T φ κ x z‖ * u z ≤ (∑ L ∈ Lm, TC * (((2 : ℝ) ^ (j L))⁻¹ *
          ((1 + |z - (2 : ℝ) ^ (j L) * ((v L : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j L)) ^ (-M) *
            (1 + |x - (2 : ℝ) ^ (j L) * ((v L : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j L)) ^ (-(2 : ℝ))))) * u z :=
            mul_le_mul_of_nonneg_right h3 (hu0 z)
        _ = w z := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun L _ => ?_
            simp only [hdens', hfk]; ring
  have hkey := yNorm_kernelOp_le hs hKm hGm hwi x hle
  refine hkey.trans ?_
  calc ∫ z, w z = ∑ L ∈ Lm, (TC * fk L) * ∫ z, dens L z := by
        simp only [hw]
        rw [integral_finsetSum _ fun L hL => (hdensi L hL).const_mul _]
        refine Finset.sum_congr rfl fun L _ => ?_
        rw [integral_const_mul]
    _ ≤ ∑ L ∈ Lm, (TC * fk L) * lam := by
        refine Finset.sum_le_sum fun L hL => ?_
        exact mul_le_mul_of_nonneg_left (hdens L hL) (mul_nonneg hTC0 (hfk0 L))
    _ = ∑ L ∈ Lm, TC * lam * fk L := by
        refine Finset.sum_congr rfl fun L _ => ?_; ring

end Tail

end PrimeBHT.TimeFrequency.X2
