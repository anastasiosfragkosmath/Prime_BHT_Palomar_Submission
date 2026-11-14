module

public import PrimeBHT.TimeFrequency.X2.EngTail.Induct
public import PrimeBHT.TimeFrequency.X2.EngTail.TreeStrong
public import PrimeBHT.TimeFrequency.X2.EngTail.Eng

/-!
# X2, node B5: `TreeLqBound` and the unconditional corrected statement

* `treeLqBound`: for `M + 1 ≤ 𝔭.D`, `M + 4 ≤ 𝔭.N`, `M ≥ 3`, `1 < q, s`,
  `|I_t|^{-1/q} ‖T_Tr F‖_{L^q(L^s)} ≤ C sup_{R ∈ Tr} λ_M(‖F‖; I_R)` for every `k`-lacunary tree (DPLMV `e:engbd1`).
* `engLeTailMass : EngLeTailMassStatementD`: B5 with the derivative margin `M + 100 ≤ 𝔭.D` (unconditional).

The proof demodulates by `θ = t.2 · freqDir k`, applies the abstract tile estimate `tile_bound_main` (Calderón-Zygmund induction on
the number of tiles) to the kernel `∑_R ψ_R(x) κ'_R(x - z)` with the strong-type input `tileKernelOp_strong` for all sub-trees.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform ComplexConjugate ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

theorem eLpNorm_eq_Lq {q : ℝ} (hq : 0 < q) {f : ℝ → ℝ} (hf : AEStronglyMeasurable f volume)
    (hf0 : ∀ x, 0 ≤ f x) :
    eLpNorm f (ENNReal.ofReal q) volume = Lq q (fun x => ENNReal.ofReal (f x)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq).ne' ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hq.le]
  unfold Lq
  simp only [Real.enorm_eq_ofReal (hf0 _)]

/-- `3 I_R ⊆ 3 I_t` for `I_R ⊆ I_t` (dyadic intervals). -/
theorem dil3_subset_dil3 {s v s' v' : ℤ} (h : dyadicInt s v ⊆ dyadicInt s' v') :
    Ico ((2 : ℝ) ^ s * ((v : ℝ) + 1 / 2) - 3 * (2 : ℝ) ^ s / 2) ((2 : ℝ) ^ s * ((v : ℝ) + 1 / 2) + 3 * (2 : ℝ) ^ s / 2) ⊆
      Ico ((2 : ℝ) ^ s' * ((v' : ℝ) + 1 / 2) - 3 * (2 : ℝ) ^ s' / 2)
        ((2 : ℝ) ^ s' * ((v' : ℝ) + 1 / 2) + 3 * (2 : ℝ) ^ s' / 2) := by
  obtain ⟨-, hg⟩ := dyadicInt_subset_geom h
  have hs : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  rw [abs_le] at hg
  refine Ico_subset_Ico ?_ ?_ <;> nlinarith [hg.1, hg.2, abs_nonneg ((2 : ℝ) ^ s * ((v : ℝ) + 1 / 2) -
    (2 : ℝ) ^ s' * ((v' : ℝ) + 1 / 2))]

/-- The volume of `W(Tr)` is at most `3 |I_t|`. -/
theorem volume_Wset_tree_le {Tr : Finset TriTile} {t : Top} (ht : IsTree Tr t) :
    (volume (Wset Tr (fun R => R.box.scale) (fun R => R.pos))).toReal ≤ 3 * (2 : ℝ) ^ t.1.1 := by
  have hsub : Wset Tr (fun R => R.box.scale) (fun R => R.pos) ⊆
      Ico ((2 : ℝ) ^ t.1.1 * ((t.1.2 : ℝ) + 1 / 2) - 3 * (2 : ℝ) ^ t.1.1 / 2)
        ((2 : ℝ) ^ t.1.1 * ((t.1.2 : ℝ) + 1 / 2) + 3 * (2 : ℝ) ^ t.1.1 / 2) := by
    intro z hz
    obtain ⟨R, hR, hz⟩ := mem_iUnion₂.1 hz
    exact dil3_subset_dil3 (ht R hR).1 hz
  have h1 : volume (Wset Tr (fun R => R.box.scale) (fun R => R.pos)) ≤ ENNReal.ofReal (3 * (2 : ℝ) ^ t.1.1) := by
    refine (measure_mono hsub).trans (le_of_eq ?_)
    rw [Real.volume_Ico]; congr 1; ring
  exact ENNReal.toReal_le_of_le_ofReal (by have := two_zpow_pos' t.1.1; positivity) h1

/-- The tile density is bounded by the tail mass `λ_M`. -/
theorem density_le_tailMass {M : ℝ} (hM : 1 < M) (s v : ℤ) {u : ℝ → ℝ} (hum : Measurable u)
    (hu0 : ∀ z, 0 ≤ u z) (hu1 : ∀ z, u z ≤ 1) :
    ∫ z, ((2 : ℝ) ^ s)⁻¹ * (1 + |z - (2 : ℝ) ^ s * ((v : ℝ) + 1 / 2)| / (2 : ℝ) ^ s) ^ (-M) * u z ≤
      V16.tailMass M u (dyadicInt s v) := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ s := two_zpow_pos' s
  unfold V16.tailMass
  rw [toReal_volume_dyadicInt, intervalCentre_dyadicInt]
  set c : ℝ := (2 : ℝ) ^ s * ((v : ℝ) + 1 / 2) with hc
  set L : ℝ := (2 : ℝ) ^ s with hLdef
  have hint : Integrable (fun z : ℝ => ‖u z‖ * V16.tailWeight M ((z - c) / L)) := by
    refine (V16.integrable_tailWeight hM c hL).mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact (hum.norm.mul ((V16.measurable_tailWeight M).comp
        ((measurable_id.sub_const c).div_const L))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (V16.tailWeight_nonneg _ _))]
      rw [Real.norm_eq_abs, abs_of_nonneg (hu0 z)]
      exact mul_le_of_le_one_left (V16.tailWeight_nonneg _ _) (hu1 z)
  rw [← integral_const_mul]
  refine integral_mono (integrable_density hM hL hum hu0 hu1) (hint.const_mul _) fun z => ?_
  have h1 : (1 + |z - c| / L) ^ (-M) ≤ V16.tailWeight M ((z - c) / L) := by
    have := rpow_le_tailWeight (by linarith : 0 ≤ M) ((z - c) / L)
    rwa [abs_div, abs_of_pos hL] at this
  rw [Real.norm_eq_abs, abs_of_nonneg (hu0 z)]
  have hLi : 0 ≤ L⁻¹ := inv_nonneg.2 hL.le
  calc L⁻¹ * (1 + |z - c| / L) ^ (-M) * u z = L⁻¹ * ((1 + |z - c| / L) ^ (-M) * u z) := by ring
    _ ≤ L⁻¹ * (u z * V16.tailWeight M ((z - c) / L)) := by
        refine mul_le_mul_of_nonneg_left ?_ hLi
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left h1 (hu0 z)

/-- **`TreeLqBound`** (DPLMV `e:engbd1`): the single-tree estimate. -/
theorem treeLqBound {𝔭 : Params} (h𝔭 : 𝔭.Admissible) {s q M : ℝ} (hs : 1 < s) (hq : 1 < q) (hM : 3 ≤ M)
    (hN : M + 4 ≤ 𝔭.N) (hD : M + 1 ≤ 𝔭.D) : TreeLqBound 𝔭 s q M := by
  classical
  have hs0 : 0 < s := by linarith
  have hq0 : 0 < q := by linarith
  have hM1 : 1 < M := by linarith
  obtain ⟨C₀, hC₀, hC₀s⟩ := tileKernelOp_strong h𝔭 hq hs
  obtain ⟨Cφ, Cκ, hCφ, hCκ, hTBall⟩ := exists_tileBound h𝔭 (M := M) (by linarith) hD
    (C₀ := 2 * hullConst) (by unfold hullConst; norm_num)
  have hSC := stepConst_ne_top (𝔭.N : ℝ) M Cφ Cκ C₀ q hq0
  refine ⟨3 * (stepConst (𝔭.N : ℝ) M Cφ Cκ C₀ q).toReal, by positivity, ?_⟩
  intro P _ Qs hQ k Tr t hbox ht hlac ψ m hdata F hF hFb
  set θ : ℝ := t.2 * freqDir k with hθ
  have hTB : ∀ R ∈ Tr, TileBound (𝔭.N : ℝ) M Cφ Cκ R.box.scale R.pos (ψ R) (kernelDemod θ (m R)) := fun R hR =>
    hTBall R.box.scale R.pos (R.box.centre k) θ (ψ R) (m R) (hdata.1 R hR).1 (hdata.1 R hR).2
      (centre_sub_theta_le hQ (hbox R hR) (ht R hR).2 k)
  have hinj : Set.InjOn (fun R : TriTile => (R.box.scale, R.pos)) (Tr : Set TriTile) := by
    intro R hR R' hR' h
    simp only [Prod.mk.injEq] at h
    have hb : R.box = R'.box := ht.box_eq_of_scale_eq hQ hbox R hR R' hR' h.1
    cases R; cases R'
    simp only at hb h
    simp [hb, h.2]
  -- the demodulated function
  set F' : ℝ → ZMod P → ℂ := fun z y => Complex.exp (-(2 * π * Complex.I * θ * (z : ℂ))) * F z y with hF'
  have hexpn : ∀ z : ℝ, ‖Complex.exp (-(2 * π * Complex.I * θ * (z : ℂ)))‖ = 1 := fun z => by
    rw [show (-(2 * (π : ℂ) * Complex.I * θ * z)) = ((-(2 * π * θ * z) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hF'm : Measurable F' := by
    refine measurable_pi_iff.2 fun y => ?_
    exact (Complex.continuous_exp.comp (by fun_prop)).measurable.mul ((measurable_pi_apply y).comp hF)
  have hyF' : ∀ z, yNorm s (F' z) = yNorm s (F z) := fun z => by
    have := yNorm_fun_const_mul hs0 (Complex.exp (-(2 * π * Complex.I * θ * (z : ℂ)))) (F z)
    rw [hexpn z, one_mul] at this
    exact this
  have hker : ∀ x, CZ.kernelOp (tileKernel Tr ψ (fun R => kernelDemod θ (m R))) F' x =
      fun y => Complex.exp (-(2 * π * Complex.I * θ * (x : ℂ))) * treeOp Tr ψ m F x y := by
    intro x; funext y
    unfold CZ.kernelOp
    have hgm : Measurable fun z => F' z y := (measurable_pi_apply y).comp hF'm
    have hP0 : (0 : ℝ) ≤ (P : ℝ) ^ s⁻¹ := by positivity
    have hgb : ∀ z, ‖F' z y‖ ≤ (P : ℝ) ^ s⁻¹ * 1 := fun z =>
      (norm_apply_le_rpow_mul_yNorm hs0 (F' z) y).trans (by
        rw [hyF' z]; exact mul_le_mul_of_nonneg_left (hFb z) hP0)
    have := kernel_integral_eq (N := (𝔭.N : ℝ)) (M := M) (Cφ := Cφ) (Cκ := Cκ) hM1 hTB hgm hgb x
    rw [this]
    congr 1
    unfold treeOp
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 1
    rw [tmult_apply_eq_tm]
    congr 1
    funext z
    simp only [hF']
    rw [← mul_assoc, ← Complex.exp_add]
    simp
  have hy1 : ∀ x, yNorm s (treeOp Tr ψ m F x) =
      yNorm s (CZ.kernelOp (tileKernel Tr ψ (fun R => kernelDemod θ (m R))) F' x) := fun x => by
    rw [hker x, yNorm_fun_const_mul hs0, hexpn x, one_mul]
  -- kernels
  have hKm : ∀ T ⊆ Tr, Measurable (Function.uncurry (tileKernel T ψ (fun R => kernelDemod θ (m R)))) := fun T hT =>
    (continuous_tileKernel T ψ (fun R => kernelDemod θ (m R)) (fun R hR => (hTB R (hT hR)).φ_diff.continuous)
      (fun R hR => (hTB R (hT hR)).κ_diff.continuous)).measurable
  have hF'y : ∀ y, Measurable fun z => F' z y := fun y => (measurable_pi_apply y).comp hF'm
  -- the strong-type hypothesis in `Lq` form
  have hStrong : ∀ T ⊆ Tr, ∀ G : ℝ → ZMod P → ℂ, Measurable G → (∃ B, ∀ x, yNorm s (G x) ≤ B) →
      Lq q (fun x => ENNReal.ofReal (yNorm s (CZ.kernelOp (tileKernel T ψ (fun R => kernelDemod θ (m R))) G x))) ≤
        ENNReal.ofReal C₀ * Lq q (fun x => ENNReal.ofReal (yNorm s (G x))) := by
    intro T hT G hG hGb
    have h := hC₀s P Qs hQ k T t (fun R hR => hbox R (hT hR)) (fun R hR => ht R (hT hR))
      (fun R hR R' hR' h => hlac R (hT hR) R' (hT hR') h) ψ m
      ⟨fun Q hQ' => hdata.1 Q (hT hQ'), fun Q hQ' Q' hQ'' h => hdata.2 Q (hT hQ') Q' (hT hQ'') h⟩ G hG hGb
    have hGy : ∀ y, Measurable fun z => G z y := fun y => (measurable_pi_apply y).comp hG
    have hm1 : Measurable fun x => yNorm s (CZ.kernelOp (tileKernel T ψ (fun R => kernelDemod θ (m R))) G x) :=
      CZ.measurable_yNorm s (fun y => CZ.measurable_kop (hKm T hT) (hGy y))
    have hm2 : Measurable fun x => yNorm s (G x) := CZ.measurable_yNorm s hGy
    rw [eLpNorm_eq_Lq hq0 hm1.aestronglyMeasurable (fun x => CZ.yNorm_nonneg s _),
      eLpNorm_eq_Lq hq0 hm2.aestronglyMeasurable (fun x => CZ.yNorm_nonneg s _)] at h
    exact h
  -- the sup of the tail masses
  set lamE : ℝ≥0∞ := ⨆ R ∈ Tr, ENNReal.ofReal (V16.tailMass M (fun y => yNorm s (F y)) R.I) with hlamE
  have hlamE_top : lamE ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑ R ∈ Tr, V16.tailMass M (fun y => yNorm s (F y)) R.I)) ?_
    refine iSup₂_le fun R hR => ENNReal.ofReal_le_ofReal ?_
    exact Finset.single_le_sum (f := fun R => V16.tailMass M (fun y => yNorm s (F y)) R.I)
      (fun R _ => V16.tailMass_nonneg M _ _) hR
  set lam : ℝ := lamE.toReal with hlam
  have hlam0 : 0 ≤ lam := ENNReal.toReal_nonneg
  have hofl : ENNReal.ofReal lam = lamE := ENNReal.ofReal_toReal hlamE_top
  have hum : Measurable fun y => yNorm s (F y) := CZ.measurable_yNorm s fun y => (measurable_pi_apply y).comp hF
  have hdens : ∀ R ∈ Tr, ∫ z, ((2 : ℝ) ^ R.box.scale)⁻¹ *
      (1 + |z - (2 : ℝ) ^ R.box.scale * ((R.pos : ℝ) + 1 / 2)| / (2 : ℝ) ^ R.box.scale) ^ (-M) * yNorm s (F' z) ≤ lam := by
    intro R hR
    have h1 := density_le_tailMass hM1 R.box.scale R.pos hum (fun z => CZ.yNorm_nonneg s _) hFb
    have h2 : V16.tailMass M (fun y => yNorm s (F y)) R.I ≤ lam := by
      rw [hlam]
      refine (ENNReal.ofReal_le_iff_le_toReal hlamE_top).1 ?_
      exact le_iSup₂_of_le R hR le_rfl
    have e : (fun z => ((2 : ℝ) ^ R.box.scale)⁻¹ *
        (1 + |z - (2 : ℝ) ^ R.box.scale * ((R.pos : ℝ) + 1 / 2)| / (2 : ℝ) ^ R.box.scale) ^ (-M) * yNorm s (F' z)) =
        fun z => ((2 : ℝ) ^ R.box.scale)⁻¹ *
          (1 + |z - (2 : ℝ) ^ R.box.scale * ((R.pos : ℝ) + 1 / 2)| / (2 : ℝ) ^ R.box.scale) ^ (-M) * yNorm s (F z) := by
      funext z; rw [hyF' z]
    rw [e]
    exact h1.trans h2
  -- the abstract estimate
  have hmain := tile_bound_main (N := (𝔭.N : ℝ)) (M := M) (Cφ := Cφ) (Cκ := Cκ) (C₀ := C₀) (q := q) (s := s)
    hq hs hM hN hCφ hCκ hC₀ Tr (fun R => R.box.scale) (fun R => R.pos) ψ (fun R => kernelDemod θ (m R)) hTB hinj
    hStrong hF'm (fun z => by rw [hyF' z]; exact hFb z) hlam0 hdens Tr (Finset.Subset.refl _)
  -- assembling
  have hLq : eLpNorm (fun x => yNorm s (treeOp Tr ψ m F x)) (ENNReal.ofReal q) volume =
      Lq q (fun x => ENNReal.ofReal (yNorm s (CZ.kernelOp (tileKernel Tr ψ (fun R => kernelDemod θ (m R))) F' x))) := by
    have hm1 : Measurable fun x => yNorm s (CZ.kernelOp (tileKernel Tr ψ (fun R => kernelDemod θ (m R))) F' x) :=
      CZ.measurable_yNorm s (fun y => CZ.measurable_kop (hKm Tr (Finset.Subset.refl _)) (hF'y y))
    have e : (fun x => yNorm s (treeOp Tr ψ m F x)) =
        fun x => yNorm s (CZ.kernelOp (tileKernel Tr ψ (fun R => kernelDemod θ (m R))) F' x) := funext hy1
    rw [e, eLpNorm_eq_Lq hq0 hm1.aestronglyMeasurable (fun x => CZ.yNorm_nonneg s _)]
  have hVle := volume_Wset_tree_le ht
  set V : ℝ := (volume (Wset Tr (fun R => R.box.scale) (fun R => R.pos))).toReal with hV
  have hRt : (0 : ℝ) < (2 : ℝ) ^ t.1.1 := two_zpow_pos' t.1.1
  have hfac : ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (-1 / q)) * ENNReal.ofReal V ^ (1 / q) ≤ ENNReal.ofReal 3 := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
    have h1 : V ^ (1 / q) ≤ (3 * (2 : ℝ) ^ t.1.1) ^ (1 / q) := Real.rpow_le_rpow hV0 hVle (by positivity)
    have h2 : ((2 : ℝ) ^ t.1.1) ^ (-1 / q) * ((2 : ℝ) ^ t.1.1) ^ (1 / q) = 1 := by
      rw [← Real.rpow_add hRt]; simp [neg_div]
    calc ((2 : ℝ) ^ t.1.1) ^ (-1 / q) * V ^ (1 / q)
        ≤ ((2 : ℝ) ^ t.1.1) ^ (-1 / q) * (3 * (2 : ℝ) ^ t.1.1) ^ (1 / q) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 3 ^ (1 / q) := by
          rw [Real.mul_rpow (by norm_num) hRt.le, ← mul_assoc, mul_comm (((2 : ℝ) ^ t.1.1) ^ (-1 / q)),
            mul_assoc, h2, mul_one]
      _ ≤ 3 := by
          calc (3 : ℝ) ^ (1 / q) ≤ (3 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [div_le_one hq0]; exact hq.le)
            _ = 3 := Real.rpow_one 3
  unfold treeOpNorm
  rw [hLq]
  calc ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (-1 / q)) *
        Lq q (fun x => ENNReal.ofReal (yNorm s (CZ.kernelOp (tileKernel Tr ψ (fun R => kernelDemod θ (m R))) F' x)))
      ≤ ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (-1 / q)) *
          (stepConst (𝔭.N : ℝ) M Cφ Cκ C₀ q * ENNReal.ofReal lam * ENNReal.ofReal V ^ (1 / q)) :=
        mul_le_mul' le_rfl hmain
    _ = stepConst (𝔭.N : ℝ) M Cφ Cκ C₀ q * ENNReal.ofReal lam *
          (ENNReal.ofReal (((2 : ℝ) ^ t.1.1) ^ (-1 / q)) * ENNReal.ofReal V ^ (1 / q)) := by ring
    _ ≤ stepConst (𝔭.N : ℝ) M Cφ Cκ C₀ q * ENNReal.ofReal lam * ENNReal.ofReal 3 := mul_le_mul' le_rfl hfac
    _ = ENNReal.ofReal (3 * (stepConst (𝔭.N : ℝ) M Cφ Cκ C₀ q).toReal) * ⨆ R ∈ Tr,
          ENNReal.ofReal (V16.tailMass M (fun y => yNorm s (F y)) R.I) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hSC, hofl]
        ring

/-- **B5, corrected and unconditional**: `EngLeTailMassStatementD`. -/
theorem engLeTailMass : EngLeTailMassStatementD :=
  engLeTailMass_of_treeLqBound fun 𝔭 h𝔭 s q M hs hq hM hN hD =>
    treeLqBound h𝔭 hs (by linarith) (by linarith) (by linarith) (by linarith)

end PrimeBHT.TimeFrequency.X2
