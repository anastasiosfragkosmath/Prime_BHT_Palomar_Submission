module

public import PrimeBHT.TimeFrequency.X2.EngTail.Gen

/-!
# X2, node B5: one step of the induction on the number of tiles

`step_bound`: for a finite family `S` of tiles (with `TileBound`, a strong-type hypothesis for sub-families, a function `F'` with
`‖F'‖_X ≤ 1` and tile densities `≤ λ`), if the estimate
`‖yNorm ∘ K_T F'‖_q ≤ C λ |W(T)|^{1/q}` holds for every proper subfamily `T ⊂ S` then it holds for `S`
(Calderón-Zygmund decomposition of `F' 1_{W(S)}` at height `A λ`, `A = 7 (5/2)^M 2^q`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- The height `A = 7 (5/2)^M 2^q` of the Calderón-Zygmund decomposition. -/
def czHeight (M q : ℝ) : ℝ := 7 * (5 / 2) ^ M * 2 ^ q

theorem czHeight_pos (M q : ℝ) : 0 < czHeight M q := by unfold czHeight; positivity

/-- The constant of the good, atom and tail parts. -/
def stepConstG (N M Cφ Cκ C₀ q : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal C₀ * ENNReal.ofReal ((2 * czHeight M q) ^ (q - 1) * (5 / 2) ^ M) ^ (1 / q) +
    famConst q * ENNReal.ofReal (4 * czHeight M q * atomConst N M Cφ Cκ) *
      ENNReal.ofReal ((5 / 2) ^ M / czHeight M q) ^ (1 / q) +
    famConst q * ENNReal.ofReal (tailConstK N M Cφ Cκ)

/-- The constant of the induction. -/
def stepConst (N M Cφ Cκ C₀ q : ℝ) : ℝ≥0∞ := 2 * stepConstG N M Cφ Cκ C₀ q

/-- Algebra of the good part. -/
theorem good_alg {q A CM lam V : ℝ} (hq : 0 < q) (hA : 0 < A) (hCM : 0 ≤ CM) (hlam : 0 < lam) (_hV : 0 ≤ V) :
    (ENNReal.ofReal ((2 * (A * lam)) ^ (q - 1)) * ENNReal.ofReal (CM * lam * V)) ^ (1 / q) =
      ENNReal.ofReal ((2 * A) ^ (q - 1) * CM) ^ (1 / q) * ENNReal.ofReal lam * ENNReal.ofReal V ^ (1 / q) := by
  have e1 : (2 * (A * lam)) ^ (q - 1) = (2 * A) ^ (q - 1) * lam ^ (q - 1) := by
    rw [← mul_assoc, Real.mul_rpow (by positivity) hlam.le]
  have e2 : lam ^ (q - 1) * lam = lam ^ q := by
    rw [← Real.rpow_add_one hlam.ne']; congr 1; ring
  have e3 : ENNReal.ofReal ((2 * (A * lam)) ^ (q - 1)) * ENNReal.ofReal (CM * lam * V) =
      ENNReal.ofReal ((2 * A) ^ (q - 1) * CM) * ENNReal.ofReal lam ^ q * ENNReal.ofReal V := by
    rw [e1, ENNReal.ofReal_rpow_of_nonneg hlam.le hq.le, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1; rw [← e2]; ring
  rw [e3, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]

theorem half_rpow {q : ℝ} (hq : 0 < q) : (((2 : ℝ) ^ q)⁻¹) ^ (1 / q) = 1 / 2 := by
  rw [Real.inv_rpow (by positivity), ← Real.rpow_mul (by norm_num), mul_one_div_cancel hq.ne', Real.rpow_one]
  norm_num

theorem ofReal_half : ENNReal.ofReal (1 / 2) = 2⁻¹ := by
  rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

section Step

variable {ι : Type} [DecidableEq ι] {P : ℕ} [NeZero P]

/-- **One step of the induction**. -/
theorem step_bound {N M Cφ Cκ C₀ q s : ℝ}
    (hq : 1 < q) (hs : 1 < s) (hM : 3 ≤ M) (hN : M + 4 ≤ N) (hCφ : 0 ≤ Cφ) (hCκ : 0 ≤ Cκ) (_hC₀ : 0 ≤ C₀)
    (S : Finset ι) (j v : ι → ℤ) (φ κ : ι → ℝ → ℂ)
    (hb : ∀ i ∈ S, TileBound N M Cφ Cκ (j i) (v i) (φ i) (κ i))
    (hinj : Set.InjOn (fun i => (j i, v i)) (S : Set ι))
    (hStrong : ∀ T ⊆ S, ∀ G : ℝ → ZMod P → ℂ, Measurable G → (∃ B, ∀ x, yNorm s (G x) ≤ B) →
      Lq q (fun x => ENNReal.ofReal (yNorm s (CZ.kernelOp (tileKernel T φ κ) G x))) ≤
        ENNReal.ofReal C₀ * Lq q (fun x => ENNReal.ofReal (yNorm s (G x))))
    {F' : ℝ → ZMod P → ℂ} (hF'm : Measurable F') (hF'1 : ∀ x, yNorm s (F' x) ≤ 1) {lam : ℝ} (hlam : 0 < lam)
    (hdens : ∀ i ∈ S, ∫ z, ((2 : ℝ) ^ (j i))⁻¹ *
      (1 + |z - (2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j i)) ^ (-M) * yNorm s (F' z) ≤ lam)
    (hS : S.Nonempty)
    (hIH : ∀ T ⊂ S, Lq q (fun x => ENNReal.ofReal (yNorm s (CZ.kernelOp (tileKernel T φ κ) F' x))) ≤
      stepConst N M Cφ Cκ C₀ q * ENNReal.ofReal lam * ENNReal.ofReal (volume (Wset T j v)).toReal ^ (1 / q)) :
    Lq q (fun x => ENNReal.ofReal (yNorm s (CZ.kernelOp (tileKernel S φ κ) F' x))) ≤
      stepConst N M Cφ Cκ C₀ q * ENNReal.ofReal lam * ENNReal.ofReal (volume (Wset S j v)).toReal ^ (1 / q) := by
  classical
  have hs0 : 0 < s := by linarith
  have hq0 : 0 < q := by linarith
  have hM1 : 1 < M := by linarith
  have hN3 : 3 < N := by linarith
  set u : ℝ → ℝ := fun z => yNorm s (F' z) with hu
  have hF'y : ∀ y, Measurable fun z => F' z y := fun y => (measurable_pi_apply y).comp hF'm
  have hum : Measurable u := CZ.measurable_yNorm s hF'y
  have hu0 : ∀ z, 0 ≤ u z := fun z => CZ.yNorm_nonneg s _
  have hu1 : ∀ z, u z ≤ 1 := hF'1
  set W : Set ℝ := Wset S j v with hW
  have hWm : MeasurableSet W := measurableSet_Wset S j v
  have hWfin : volume W ≠ ⊤ := (volume_Wset_lt_top S j v).ne
  set V : ℝ := (volume W).toReal with hV
  have hVpos : 0 < V := ENNReal.toReal_pos (volume_Wset_pos j v hS).ne' hWfin
  set A : ℝ := czHeight M q with hA
  have hApos : 0 < A := czHeight_pos M q
  set CM : ℝ := (5 / 2 : ℝ) ^ M with hCM
  have hCMpos : 0 < CM := by positivity
  -- the mass of `u` on `W`
  set G : ℝ → ℝ := W.indicator u with hGdef
  have hG0 : ∀ z, 0 ≤ G z := fun z => indicator_nonneg (fun z _ => hu0 z) z
  have hG1 : ∀ z, G z ≤ 1 := fun z => by
    by_cases hz : z ∈ W
    · simp only [hGdef, indicator_of_mem hz]; exact hu1 z
    · simp only [hGdef, indicator_of_notMem hz]; norm_num
  have hGi : Integrable G := by
    refine (integrable_indicator_iff hWm).2 ?_
    exact Measure.integrableOn_of_bounded (M := 1) hWfin hum.aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hu0 z)]; exact hu1 z)
  have hGint : ∫ z, G z ≤ CM * lam * V := by
    have := integral_Wset_le hM1 hlam.le S j v hinj hum hu0 hu1 hdens
    rw [hGdef, integral_indicator hWm]; exact this
  have hAlam : 0 < A * lam := mul_pos hApos hlam
  -- the Calderón-Zygmund intervals at height `A λ`
  obtain ⟨ι', hcnt, a, b, hab, hd, -, hup, hout, hsum, htsum⟩ := CZ.exists_cz_intervals (G := G) hG0 hGi hAlam
  have : Countable ι' := hcnt
  -- the truncated functions
  set FW : ℝ → ZMod P → ℂ := fun z y => W.indicator (fun z => F' z y) z with hFW
  set FC : ℝ → ZMod P → ℂ := fun z y => (Wᶜ).indicator (fun z => F' z y) z with hFC
  have hFWm : ∀ y, Measurable fun z => FW z y := fun y => (hF'y y).indicator hWm
  have hFCm : ∀ y, Measurable fun z => FC z y := fun y => (hF'y y).indicator hWm.compl
  have hP0 : (0 : ℝ) ≤ (P : ℝ) ^ s⁻¹ := by positivity
  have hF'b : ∀ z y, ‖F' z y‖ ≤ (P : ℝ) ^ s⁻¹ := fun z y =>
    (norm_apply_le_rpow_mul_yNorm hs0 (F' z) y).trans (by
      calc (P : ℝ) ^ s⁻¹ * yNorm s (F' z) ≤ (P : ℝ) ^ s⁻¹ * 1 := mul_le_mul_of_nonneg_left (hu1 z) hP0
        _ = _ := mul_one _)
  have hFWb : ∀ z y, ‖FW z y‖ ≤ (P : ℝ) ^ s⁻¹ := fun z y => by
    by_cases hz : z ∈ W
    · simp only [hFW, indicator_of_mem hz]; exact hF'b z y
    · simp only [hFW, indicator_of_notMem hz, norm_zero]; exact hP0
  have hFCb : ∀ z y, ‖FC z y‖ ≤ (P : ℝ) ^ s⁻¹ := fun z y => by
    by_cases hz : z ∈ Wᶜ
    · simp only [hFC, indicator_of_mem hz]; exact hF'b z y
    · simp only [hFC, indicator_of_notMem hz, norm_zero]; exact hP0
  have hFWFC : ∀ z y, F' z y = FW z y + FC z y := fun z y =>
    (indicator_self_add_compl_apply W (fun z => F' z y) z).symm
  have hFWy : ∀ z, yNorm s (FW z) = G z := by
    intro z
    by_cases hz : z ∈ W
    · have : FW z = F' z := by funext y; simp only [hFW, indicator_of_mem hz]
      rw [this, hGdef]; simp only [indicator_of_mem hz]; rfl
    · have : FW z = 0 := by funext y; simp only [hFW, indicator_of_notMem hz]; rfl
      rw [this, hGdef]; simp only [indicator_of_notMem hz]; exact CZ.yNorm_zero' hs0
  have hFWi : ∀ y, Integrable fun z => FW z y := by
    intro y
    refine Integrable.mono' (g := W.indicator (fun _ => (P : ℝ) ^ s⁻¹))
      ((integrable_indicator_iff hWm).2 (integrableOn_const hWfin)) (hFWm y).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    by_cases hz : z ∈ W
    · simp only [hFW, indicator_of_mem hz]; exact hF'b z y
    · simp only [hFW, indicator_of_notMem hz, norm_zero]; exact le_rfl
  have hGW : Integrable (fun z => yNorm s (FW z)) := by
    have : (fun z => yNorm s (FW z)) = G := funext hFWy
    rw [this]; exact hGi
  have hFW1 : ∀ z, yNorm s (FW z) ≤ 1 := fun z => by rw [hFWy]; exact hG1 z
  -- near and outer tiles
  set Snear : Finset ι := S.filter (fun i => IsNear a b j v i) with hSnear
  set Sout : Finset ι := S.filter (fun i => ¬ IsNear a b j v i) with hSout
  have hunion : Snear ∪ Sout = S := Finset.filter_union_filter_not_eq _ _
  have hdisjS : Disjoint Snear Sout := Finset.disjoint_filter_filter_not _ _ _
  have hSnearS : Snear ⊆ S := Finset.filter_subset _ _
  have hSoutS : Sout ⊆ S := Finset.filter_subset _ _
  have hsumd : ∑' i, (b i - a i) ≤ CM * V / A := by
    calc _ ≤ (∫ x, G x) / (A * lam) := htsum
      _ ≤ (CM * lam * V) / (A * lam) := div_le_div_of_nonneg_right hGint hAlam.le
      _ = CM * V / A := by field_simp
  have hVnear : (volume (Wset Snear j v)).toReal ≤ ((2 : ℝ) ^ q)⁻¹ * V := by
    have h1 := volume_Wset_near_le hab hsum Snear j v (fun i hi => (Finset.mem_filter.1 hi).2)
    calc _ ≤ 7 * ∑' i, (b i - a i) := h1
      _ ≤ 7 * (CM * V / A) := by gcongr
      _ = ((2 : ℝ) ^ q)⁻¹ * V := by
          rw [hA, hCM]; unfold czHeight; field_simp
  have hsub : Snear ⊂ S := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨hSnearS, fun h => ?_⟩
    have h2 : (volume (Wset Snear j v)).toReal = V := by rw [h]
    rw [h2] at hVnear
    have h3 : (1 : ℝ) < (2 : ℝ) ^ q := Real.one_lt_rpow (by norm_num) hq0
    have h4 : ((2 : ℝ) ^ q)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h3
    nlinarith
  -- the kernels
  have hKm : ∀ T ⊆ S, Measurable (Function.uncurry (tileKernel T φ κ)) := fun T hT =>
    (continuous_tileKernel T φ κ (fun i hi => (hb i (hT hi)).φ_diff.continuous)
      (fun i hi => (hb i (hT hi)).κ_diff.continuous)).measurable
  have hKbd : ∀ T ⊆ S, ∃ B, ∀ x z, ‖tileKernel T φ κ x z‖ ≤ B := fun T hT =>
    bounded_tileKernel (by linarith) (by linarith) T j v φ κ (fun i hi => hb i (hT hi))
  have hKsplit : ∀ x z, tileKernel S φ κ x z = tileKernel Snear φ κ x z + tileKernel Sout φ κ x z := by
    intro x z
    have : tileKernel S φ κ x z = tileKernel (Snear ∪ Sout) φ κ x z := by rw [hunion]
    rw [this]
    unfold tileKernel
    exact Finset.sum_union hdisjS
  have hint : ∀ T ⊆ S, ∀ (g : ℝ → ZMod P → ℂ), (∀ y, Measurable fun z => g z y) →
      (∀ z y, ‖g z y‖ ≤ (P : ℝ) ^ s⁻¹) → ∀ (x : ℝ) (y : ZMod P),
      Integrable (fun z => tileKernel T φ κ x z * g z y) := fun T hT g hg hgb x y =>
    integrable_tileKernel_mul hM1 T j v φ κ (fun i hi => hb i (hT hi)) (hg y) (fun z => hgb z y) x
  have hdec : ∀ x y, CZ.kernelOp (tileKernel S φ κ) F' x y =
      CZ.kernelOp (tileKernel Snear φ κ) F' x y + CZ.kop (tileKernel Sout φ κ) (fun z => FW z y) x +
        ∫ z, tileKernel Sout φ κ x z * FC z y := by
    intro x y
    have i1 := hint Snear hSnearS F' hF'y hF'b x y
    have i2 := hint Sout hSoutS FW hFWm hFWb x y
    have i3 := hint Sout hSoutS FC hFCm hFCb x y
    simp only [CZ.kernelOp, CZ.kop]
    have i12 : Integrable (fun z => tileKernel Snear φ κ x z * F' z y + tileKernel Sout φ κ x z * FW z y) :=
      i1.add i2
    rw [← integral_add i1 i2, ← integral_add i12 i3]
    congr 1; ext z
    rw [hKsplit x z, hFWFC z y]; ring
  have htri : ∀ x, yNorm s (CZ.kernelOp (tileKernel S φ κ) F' x) ≤
      yNorm s (CZ.kernelOp (tileKernel Snear φ κ) F' x) +
        yNorm s (fun y => CZ.kop (tileKernel Sout φ κ) (fun z => FW z y) x) +
        yNorm s (fun y => ∫ z, tileKernel Sout φ κ x z * FC z y) := by
    intro x
    have e : CZ.kernelOp (tileKernel S φ κ) F' x =
        (CZ.kernelOp (tileKernel Snear φ κ) F' x + fun y => CZ.kop (tileKernel Sout φ κ) (fun z => FW z y) x) +
          fun y => ∫ z, tileKernel Sout φ κ x z * FC z y := by
      funext y; exact hdec x y
    rw [e]
    have h1 := CZ.yNorm_add_le hs.le (CZ.kernelOp (tileKernel Snear φ κ) F' x +
      fun y => CZ.kop (tileKernel Sout φ κ) (fun z => FW z y) x) (fun y => ∫ z, tileKernel Sout φ κ x z * FC z y)
    have h2 := CZ.yNorm_add_le hs.le (CZ.kernelOp (tileKernel Snear φ κ) F' x)
      (fun y => CZ.kop (tileKernel Sout φ κ) (fun z => FW z y) x)
    linarith
  -- the atom kernel bound for the outer tiles
  have hsm : ∀ i x, ∀ u ∈ Ico (a i) (b i), ‖tileKernel Sout φ κ x u - tileKernel Sout φ κ x (CZ.ctr a b i)‖ ≤
      atomConst N M Cφ Cκ * ((b i - a i)⁻¹ * (1 + |x - CZ.ctr a b i| / (b i - a i)) ^ (-(2 : ℝ))) := by
    intro i x u hu
    have hδ : 0 < b i - a i := sub_pos.2 (hab i)
    refine kernel_atom_le hN3 hM hCφ hCκ Sout j v φ κ (fun i' hi' => hb i' (hSoutS hi'))
      (hinj.mono (Finset.coe_subset.2 hSoutS)) hδ
      (fun i' hi' => sep_of_not_near (Finset.mem_filter.1 hi').2 i) ?_ x
    simp only [CZ.ctr]
    rw [abs_le]; obtain ⟨h1, h2⟩ := hu; constructor <;> linarith
  have hQ : ∀ i, ∫ u in Ico (a i) (b i), yNorm s (FW u) ≤ 2 * (A * lam) * (b i - a i) := by
    intro i
    have : (fun u => yNorm s (FW u)) = G := funext hFWy
    rw [this]; exact hup i
  have hout' : ∀ᵐ u ∂(volume : Measure ℝ), u ∉ ⋃ i, Ico (a i) (b i) → yNorm s (FW u) ≤ A * lam := by
    filter_upwards [hout] with u hu hnu
    rw [hFWy]; exact hu hnu
  have hczs : ∀ x, ENNReal.ofReal (yNorm s (fun y => CZ.kop (tileKernel Sout φ κ) (fun z => FW z y) x)) ≤
      ENNReal.ofReal (yNorm s (fun y => CZ.kop (tileKernel Sout φ κ) (fun u => CZ.goodPart a b FW u y) x)) +
        famPhiT (CZ.ctr a b) (fun i => b i - a i) (fun _ => 4 * (A * lam) * atomConst N M Cφ Cκ) x := by
    intro x
    obtain ⟨Bo, hBo⟩ := hKbd Sout hSoutS
    exact cz_step hs (hKm Sout hSoutS) hBo hab hd hFWm hFWi hGW (atomConst_nonneg hN3 hCφ hCκ) hQ hsm x
  -- the tail
  obtain ⟨Lm, hLmS, hcov, hLdisj⟩ := exists_maximal S j v hinj
  have hcov' : ∀ i, ∃ L, i ∈ S → L ∈ Lm ∧ dyadicInt (j i) (v i) ⊆ dyadicInt (j L) (v L) := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨L, hL, h⟩ := hcov i hi; exact ⟨L, fun _ => ⟨hL, h⟩⟩
    · exact ⟨i, fun h => absurd h hi⟩
  choose Lf hLf using hcov'
  have htail : ∀ x, ENNReal.ofReal (yNorm s (fun y => ∫ z, tileKernel Sout φ κ x z * FC z y)) ≤
      famPhi (fun L => (2 : ℝ) ^ (j L) * ((v L : ℝ) + 1 / 2)) (fun L => (2 : ℝ) ^ (j L))
        (fun _ => tailConstK N M Cφ Cκ * lam) Lm x := by
    intro x
    have h := tail_op_le hs hM hN hCφ hCκ Sout Lm j v φ κ (fun i hi => hb i (hSoutS hi))
      (hinj.mono (Finset.coe_subset.2 hSoutS)) Lf (fun i hi => hLf i (hSoutS hi)) hF'm hWm
      (fun L hL => dil3_subset_Wset (hLmS hL)) hF'1 (fun L hL => hdens L (hLmS hL)) x
    have hTC0 : 0 ≤ tailConstK N M Cφ Cκ := tailConstK_nonneg hN hCφ hCκ
    calc _ ≤ ENNReal.ofReal (∑ L ∈ Lm, tailConstK N M Cφ Cκ * lam *
          (1 + |x - (2 : ℝ) ^ (j L) * ((v L : ℝ) + 1 / 2)| / (2 : ℝ) ^ (j L)) ^ (-(2 : ℝ))) :=
          ENNReal.ofReal_le_ofReal h
      _ = _ := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun L _ => by positivity)]
          rfl
  -- the four terms
  set g : ℝ → ZMod P → ℂ := CZ.goodPart a b FW with hg
  have hgm : ∀ y, Measurable fun z => g z y := fun y => CZ.measurable_goodPart hd hFWm y
  set a1 : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (yNorm s (CZ.kernelOp (tileKernel Snear φ κ) F' x)) with ha1
  set a2 : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (yNorm s (CZ.kernelOp (tileKernel Sout φ κ) g x)) with ha2
  set a3 : ℝ → ℝ≥0∞ := famPhiT (CZ.ctr a b) (fun i => b i - a i)
    (fun _ => 4 * (A * lam) * atomConst N M Cφ Cκ) with ha3
  set a4 : ℝ → ℝ≥0∞ := famPhi (fun L => (2 : ℝ) ^ (j L) * ((v L : ℝ) + 1 / 2)) (fun L => (2 : ℝ) ^ (j L))
    (fun _ => tailConstK N M Cφ Cκ * lam) Lm with ha4
  have hpt : ∀ x, ENNReal.ofReal (yNorm s (CZ.kernelOp (tileKernel S φ κ) F' x)) ≤
      a1 x + a2 x + a3 x + a4 x := by
    intro x
    have h1 := htri x
    have hn1 := CZ.yNorm_nonneg s (CZ.kernelOp (tileKernel Snear φ κ) F' x)
    have hn2 := CZ.yNorm_nonneg s (fun y => CZ.kop (tileKernel Sout φ κ) (fun z => FW z y) x)
    have hn3 := CZ.yNorm_nonneg s (fun y => ∫ z, tileKernel Sout φ κ x z * FC z y)
    calc ENNReal.ofReal (yNorm s (CZ.kernelOp (tileKernel S φ κ) F' x))
        ≤ ENNReal.ofReal (yNorm s (CZ.kernelOp (tileKernel Snear φ κ) F' x) +
            yNorm s (fun y => CZ.kop (tileKernel Sout φ κ) (fun z => FW z y) x) +
            yNorm s (fun y => ∫ z, tileKernel Sout φ κ x z * FC z y)) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (yNorm s (CZ.kernelOp (tileKernel Snear φ κ) F' x)) +
            ENNReal.ofReal (yNorm s (fun y => CZ.kop (tileKernel Sout φ κ) (fun z => FW z y) x)) +
            ENNReal.ofReal (yNorm s (fun y => ∫ z, tileKernel Sout φ κ x z * FC z y)) := by
          rw [ENNReal.ofReal_add (add_nonneg hn1 hn2) hn3, ENNReal.ofReal_add hn1 hn2]
      _ ≤ a1 x + (a2 x + a3 x) + a4 x := add_le_add (add_le_add le_rfl (hczs x)) (htail x)
      _ = a1 x + a2 x + a3 x + a4 x := by ring
  have hℓ' : ∀ i, 0 < b i - a i := fun i => sub_pos.2 (hab i)
  have hm1 : Measurable a1 :=
    (CZ.measurable_yNorm s (fun y => CZ.measurable_kop (hKm Snear hSnearS) (hF'y y))).ennreal_ofReal
  have hm2 : Measurable a2 :=
    (CZ.measurable_yNorm s (fun y => CZ.measurable_kop (hKm Sout hSoutS) (hgm y))).ennreal_ofReal
  have hm3 : Measurable a3 := by
    rw [ha3]; unfold famPhiT
    exact Measurable.ennreal_tsum fun i => ENNReal.measurable_ofReal.comp
      (measurable_const.mul (measurable_famK (hℓ' i)))
  have hm4 : Measurable a4 := measurable_famPhi (fun L => two_zpow_pos' (j L)) Lm
  have hLq : Lq q (fun x => ENNReal.ofReal (yNorm s (CZ.kernelOp (tileKernel S φ κ) F' x))) ≤
      Lq q a1 + Lq q a2 + Lq q a3 + Lq q a4 := by
    calc _ ≤ Lq q (fun x => a1 x + a2 x + a3 x + a4 x) := Lq_mono hq0 hpt
      _ ≤ Lq q (fun x => a1 x + a2 x + a3 x) + Lq q a4 := Lq_add_le hq.le ((hm1.add hm2).add hm3) hm4
      _ ≤ (Lq q (fun x => a1 x + a2 x) + Lq q a3) + Lq q a4 :=
          add_le_add (Lq_add_le hq.le (hm1.add hm2) hm3) le_rfl
      _ ≤ ((Lq q a1 + Lq q a2) + Lq q a3) + Lq q a4 :=
          add_le_add (add_le_add (Lq_add_le hq.le hm1 hm2) le_rfl) le_rfl
  -- constants
  set c2 : ℝ≥0∞ := ENNReal.ofReal C₀ * ENNReal.ofReal ((2 * A) ^ (q - 1) * CM) ^ (1 / q) with hc2
  set c3 : ℝ≥0∞ := famConst q * ENNReal.ofReal (4 * A * atomConst N M Cφ Cκ) *
    ENNReal.ofReal (CM / A) ^ (1 / q) with hc3
  set c4 : ℝ≥0∞ := famConst q * ENNReal.ofReal (tailConstK N M Cφ Cκ) with hc4
  have hconst : stepConst N M Cφ Cκ C₀ q = 2 * (c2 + c3 + c4) := rfl
  set X : ℝ≥0∞ := ENNReal.ofReal lam * ENNReal.ofReal V ^ (1 / q) with hX
  -- (1) the near tiles
  have hL1 : Lq q a1 ≤ stepConst N M Cφ Cκ C₀ q * ENNReal.ofReal lam * (2⁻¹ * ENNReal.ofReal V ^ (1 / q)) := by
    refine (hIH Snear hsub).trans ?_
    have h1 : ENNReal.ofReal (volume (Wset Snear j v)).toReal ^ (1 / q) ≤ 2⁻¹ * ENNReal.ofReal V ^ (1 / q) := by
      calc _ ≤ (ENNReal.ofReal (((2 : ℝ) ^ q)⁻¹) * ENNReal.ofReal V) ^ (1 / q) := by
            refine ENNReal.rpow_le_rpow ?_ (by positivity)
            rw [← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal hVnear
        _ = 2⁻¹ * ENNReal.ofReal V ^ (1 / q) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
              ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), half_rpow hq0, ofReal_half]
    exact mul_le_mul' le_rfl h1
  -- (2) the good part
  have hL2 : Lq q a2 ≤ c2 * X := by
    have hgbd : ∃ B, ∀ x, yNorm s (g x) ≤ B := ⟨1, fun x => yNorm_goodPart_le_one hs hab hd hFWi hGW hFW1 x⟩
    have hs2 := hStrong Sout hSoutS g (measurable_pi_iff.2 hgm) hgbd
    refine hs2.trans ?_
    have hgl := lintegral_good_rpow_le hs hq hab hd hFWi hGW hAlam hQ hout'
    have h3 : Lq q (fun x => ENNReal.ofReal (yNorm s (g x))) ≤
        (ENNReal.ofReal ((2 * (A * lam)) ^ (q - 1)) * ENNReal.ofReal (CM * lam * V)) ^ (1 / q) := by
      unfold Lq
      refine ENNReal.rpow_le_rpow ?_ (by positivity)
      refine hgl.trans (mul_le_mul' le_rfl ?_)
      refine ENNReal.ofReal_le_ofReal ?_
      have : ∫ u, yNorm s (FW u) = ∫ u, G u := by congr 1; funext u; exact hFWy u
      rw [this]; exact hGint
    rw [good_alg hq0 hApos hCMpos.le hlam hVpos.le] at h3
    calc ENNReal.ofReal C₀ * Lq q (fun x => ENNReal.ofReal (yNorm s (g x)))
        ≤ ENNReal.ofReal C₀ * (ENNReal.ofReal ((2 * A) ^ (q - 1) * CM) ^ (1 / q) * ENNReal.ofReal lam *
            ENNReal.ofReal V ^ (1 / q)) := mul_le_mul' le_rfl h3
      _ = c2 * X := by rw [hc2, hX]; ring
  -- (3) the atoms
  have hL3 : Lq q a3 ≤ c3 * X := by
    have hdisj3 : Pairwise fun i j => Disjoint (Ico (CZ.ctr a b i - (b i - a i) / 2) (CZ.ctr a b i + (b i - a i) / 2))
        (Ico (CZ.ctr a b j - (b j - a j) / 2) (CZ.ctr a b j + (b j - a j) / 2)) := by
      have e : ∀ i, Ico (CZ.ctr a b i - (b i - a i) / 2) (CZ.ctr a b i + (b i - a i) / 2) = Ico (a i) (b i) :=
        fun i => by simp only [CZ.ctr]; congr 1 <;> ring
      intro i j hij; rw [e, e]; exact hd hij
    have hAC := atomConst_nonneg (M := M) hN3 hCφ hCκ
    have h1 := Lq_famPhiT_le hq (CZ.ctr a b) (fun i => b i - a i)
      (α := 4 * (A * lam) * atomConst N M Cφ Cκ) (by positivity) hℓ' hsum hdisj3
    refine h1.trans ?_
    have h2 : ENNReal.ofReal (∑' i, (b i - a i)) ^ (1 / q) ≤
        ENNReal.ofReal (CM / A) ^ (1 / q) * ENNReal.ofReal V ^ (1 / q) := by
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) (by positivity)
      calc _ ≤ CM * V / A := hsumd
        _ = CM / A * V := by ring
    calc famConst q * ENNReal.ofReal (4 * (A * lam) * atomConst N M Cφ Cκ) *
          ENNReal.ofReal (∑' i, (b i - a i)) ^ (1 / q)
        ≤ famConst q * ENNReal.ofReal (4 * (A * lam) * atomConst N M Cφ Cκ) *
          (ENNReal.ofReal (CM / A) ^ (1 / q) * ENNReal.ofReal V ^ (1 / q)) := mul_le_mul' le_rfl h2
      _ = c3 * X := by
          rw [show 4 * (A * lam) * atomConst N M Cφ Cκ = (4 * A * atomConst N M Cφ Cκ) * lam by ring,
            ENNReal.ofReal_mul (by positivity), hc3, hX]
          ring
  -- (4) the tail
  have hL4 : Lq q a4 ≤ c4 * X := by
    have hdisjL : ∀ i ∈ Lm, ∀ i' ∈ Lm, i ≠ i' →
        Disjoint (Ico ((2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2) - (2 : ℝ) ^ (j i) / 2)
            ((2 : ℝ) ^ (j i) * ((v i : ℝ) + 1 / 2) + (2 : ℝ) ^ (j i) / 2))
          (Ico ((2 : ℝ) ^ (j i') * ((v i' : ℝ) + 1 / 2) - (2 : ℝ) ^ (j i') / 2)
            ((2 : ℝ) ^ (j i') * ((v i' : ℝ) + 1 / 2) + (2 : ℝ) ^ (j i') / 2)) := by
      intro i hi i' hi' hne
      have := hLdisj i hi i' hi' hne
      rw [dyadicInt_eq_Ico', dyadicInt_eq_Ico'] at this
      exact this
    have hTC := tailConstK_nonneg hN hCφ hCκ
    have h1 := Lq_famPhi_le hq Lm (fun L => (2 : ℝ) ^ (j L) * ((v L : ℝ) + 1 / 2)) (fun L => (2 : ℝ) ^ (j L))
      (α := tailConstK N M Cφ Cκ * lam) (mul_nonneg hTC hlam.le) (fun L => two_zpow_pos' (j L)) hdisjL
    refine h1.trans ?_
    have h2 : ENNReal.ofReal (∑ L ∈ Lm, (2 : ℝ) ^ (j L)) ^ (1 / q) ≤ ENNReal.ofReal V ^ (1 / q) :=
      ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (sum_len_le_volume hLmS hLdisj)) (by positivity)
    calc famConst q * ENNReal.ofReal (tailConstK N M Cφ Cκ * lam) *
          ENNReal.ofReal (∑ L ∈ Lm, (2 : ℝ) ^ (j L)) ^ (1 / q)
        ≤ famConst q * ENNReal.ofReal (tailConstK N M Cφ Cκ * lam) * ENNReal.ofReal V ^ (1 / q) :=
          mul_le_mul' le_rfl h2
      _ = c4 * X := by
          rw [ENNReal.ofReal_mul hTC, hc4, hX]; ring
  -- the total
  have h2inv : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  calc _ ≤ Lq q a1 + Lq q a2 + Lq q a3 + Lq q a4 := hLq
    _ ≤ stepConst N M Cφ Cκ C₀ q * ENNReal.ofReal lam * (2⁻¹ * ENNReal.ofReal V ^ (1 / q)) +
          c2 * X + c3 * X + c4 * X :=
        add_le_add (add_le_add (add_le_add hL1 hL2) hL3) hL4
    _ = stepConst N M Cφ Cκ C₀ q * ENNReal.ofReal lam * ENNReal.ofReal V ^ (1 / q) := by
        rw [hconst]
        have e : 2 * (c2 + c3 + c4) * ENNReal.ofReal lam * (2⁻¹ * ENNReal.ofReal V ^ (1 / q)) =
            (2 * 2⁻¹) * ((c2 + c3 + c4) * X) := by rw [hX]; ring
        rw [e, h2inv, one_mul]
        rw [hX]; ring

end Step

end PrimeBHT.TimeFrequency.X2
