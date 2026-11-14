module

public import PrimeBHT.TimeFrequency.X2.EngTail.L2
public import PrimeBHT.TimeFrequency.X2.EngTail.CZWeak

/-!
# X2, node B5: strong type of a lacunary tree operator

`treeOp_strong`: for `1 < q, s`, uniformly in `P`, in the rank-one box set, in the lacunary tree `Tr` with top `t`
and in the tree-operator data of the class `𝔭`:
`‖yNorm s ∘ T_Tr F‖_{L^q} ≤ C ‖yNorm s ∘ F‖_{L^q}` for every bounded measurable `F`.

Proof: demodulate by `θ = t.2 · freqDir k` (`|c_k(R) - θ| ≤ 256 · 2^{-scale}` from `t.2 ∈ hull`, `IsRankOne (h)`);
the kernel `∑_R ψ_R(x) 𝓕⁻(m_R(· + θ))(x - z)` is a CZ kernel (`EngTail/CZKernel.lean`) with the scalar `L²` bound of
`EngTail/L2.lean`; the strong type is `CZ.vectorCZ_strong_bdd`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform ComplexConjugate ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

theorem freqDir_pos (i : Fin 3) : 0 < freqDir i := by
  fin_cases i <;> simp [freqDir]

theorem freqDir_le_two (i : Fin 3) : freqDir i ≤ 2 := by
  fin_cases i <;> simp [freqDir]

theorem centre_div_mem_hull (B : Box) (k : Fin 3) : B.centre k / freqDir k ∈ B.hull := by
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
  have hd : 0 ≤ hullDil * (2 : ℝ) ^ (-B.scale) / 2 := by unfold hullDil; positivity
  have hA : ∀ i : Fin 3, (B.centre i - hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir i ≤ B.centre i / freqDir i :=
    fun i => div_le_div_of_nonneg_right (by linarith) (freqDir_pos i).le
  have hB : ∀ i : Fin 3, B.centre i / freqDir i ≤ (B.centre i + hullDil * (2 : ℝ) ^ (-B.scale) / 2) / freqDir i :=
    fun i => div_le_div_of_nonneg_right (by linarith) (freqDir_pos i).le
  unfold Box.hull
  rw [Set.mem_Icc]
  fin_cases k
  · exact ⟨(min_le_left _ _).trans ((min_le_left _ _).trans (hA 0)), (hB 0).trans ((le_max_left _ _).trans (le_max_left _ _))⟩
  · exact ⟨(min_le_left _ _).trans ((min_le_right _ _).trans (hA 1)), (hB 1).trans ((le_max_right _ _).trans (le_max_left _ _))⟩
  · exact ⟨(min_le_right _ _).trans (hA 2), (hB 2).trans (le_max_right _ _)⟩

/-- **Demodulation frequency**: `t.2 ∈ hull(B)` implies `|c_k(B) - t.2 · freqDir k| ≤ 2 hullConst · 2^{-scale}`. -/
theorem centre_sub_theta_le {J : ℕ} {Qs : Set Box} (hQ : IsRankOne J Qs) {B : Box} (hB : B ∈ Qs) {ξ : ℝ}
    (hξ : ξ ∈ B.hull) (k : Fin 3) :
    |B.centre k - ξ * freqDir k| ≤ 2 * hullConst * (2 : ℝ) ^ (-B.scale) := by
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-B.scale) := zpow_pos (by norm_num) _
  have hh := hQ.2.2.2.2.2.2.2.2 B hB (B.centre k / freqDir k) (centre_div_mem_hull B k) ξ hξ
  have hf := freqDir_pos k
  have h2 := freqDir_le_two k
  have e : B.centre k - ξ * freqDir k = freqDir k * (B.centre k / freqDir k - ξ) := by field_simp
  rw [e, abs_mul, abs_of_pos hf]
  calc freqDir k * |B.centre k / freqDir k - ξ| ≤ 2 * (hullConst * (2 : ℝ) ^ (-B.scale)) := by
        gcongr
    _ = 2 * hullConst * (2 : ℝ) ^ (-B.scale) := by ring


theorem CZ.IsCZKernel.mono {A A' : ℝ} {K : ℝ → ℝ → ℂ} (h : CZ.IsCZKernel A K) (hA : A ≤ A') :
    CZ.IsCZKernel A' K := by
  refine ⟨fun x z hxz => (h.1 x z hxz).trans (div_le_div_of_nonneg_right hA (abs_nonneg _)), fun x x' z hz => ?_⟩
  refine (h.2 x x' z hz).trans ?_
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hA (abs_nonneg _)) (by positivity)

/-- `z ↦ κ(x - z) g(z)` is integrable for a kernel with polynomial decay and a bounded measurable `g`. -/
theorem integrable_kernel_mul {κ g : ℝ → ℂ} (hκc : Continuous κ) {c M L b : ℝ} (hM : 1 < M) (hL : 0 < L)
    (hκ : ∀ w, ‖κ w‖ ≤ c * (L⁻¹ * (1 + |w| / L) ^ (-M))) (hg : Measurable g) (hgb : ∀ z, ‖g z‖ ≤ b) (x : ℝ) :
    Integrable (fun z => κ (x - z) * g z) := by
  have hint := integrable_one_add_abs_sub_div_rpow hM x hL
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hgb 0)
  have hc0 : 0 ≤ c := by
    have := hκ 0
    have h0 : 0 ≤ c * (L⁻¹ * (1 + |(0 : ℝ)| / L) ^ (-M)) := (norm_nonneg _).trans this
    have hp : 0 < L⁻¹ * (1 + |(0 : ℝ)| / L) ^ (-M) := by positivity
    exact nonneg_of_mul_nonneg_left h0 hp
  refine ((hint.const_mul (c * L⁻¹ * b))).mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact (hκc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hg.aestronglyMeasurable
  · rw [norm_mul]
    have h1 := hκ (x - z)
    rw [abs_sub_comm] at h1
    calc ‖κ (x - z)‖ * ‖g z‖ ≤ (c * (L⁻¹ * (1 + |z - x| / L) ^ (-M))) * b :=
          mul_le_mul h1 (hgb z) (norm_nonneg _) (by positivity)
      _ = c * L⁻¹ * b * (1 + |z - x| / L) ^ (-M) := by ring


theorem kernelDemod_eq (θ : ℝ) (m : ℝ → ℂ) (w : ℝ) :
    kernelDemod θ m w = Complex.exp (-(2 * π * Complex.I * θ * w)) * 𝓕⁻ m w := by
  rw [fourierInv_eq_exp_mul_kernelDemod θ w, ← mul_assoc, ← Complex.exp_add]
  simp

/-- The demodulated kernel operator in terms of the tile operators `tm`. -/
theorem kernel_integral_eq {N M Cφ Cκ : ℝ} (hM : 1 < M) {Tr : Finset TriTile} {ψ m : TriTile → ℝ → ℂ} {θ : ℝ}
    (hTB : ∀ Q ∈ Tr, TileBound N M Cφ Cκ Q.box.scale Q.pos (ψ Q) (kernelDemod θ (m Q)))
    {g : ℝ → ℂ} (hg : Measurable g) {b : ℝ} (hb : ∀ z, ‖g z‖ ≤ b) (x : ℝ) :
    ∫ z, tileKernel Tr ψ (fun Q => kernelDemod θ (m Q)) x z * g z =
      Complex.exp (-(2 * π * Complex.I * θ * x)) *
        ∑ Q ∈ Tr, ψ Q x * tm (m Q) (fun z => Complex.exp (2 * π * Complex.I * θ * z) * g z) x := by
  unfold tileKernel
  simp_rw [Finset.sum_mul]
  have hint : ∀ Q ∈ Tr, Integrable (fun z => ψ Q x * kernelDemod θ (m Q) (x - z) * g z) := by
    intro Q hQ
    have hL : (0 : ℝ) < (2 : ℝ) ^ Q.box.scale := zpow_pos (by norm_num) _
    have := integrable_kernel_mul (κ := kernelDemod θ (m Q)) (hTB Q hQ).κ_diff.continuous hM hL
      (hTB Q hQ).κ_le hg hb x
    exact (this.const_mul (ψ Q x)).congr (Eventually.of_forall fun z => by simp only [mul_assoc])
  rw [integral_finsetSum _ hint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  have e : ∀ z, ψ Q x * kernelDemod θ (m Q) (x - z) * g z =
      ψ Q x * (Complex.exp (-(2 * π * Complex.I * θ * x)) *
        (𝓕⁻ (m Q) (x - z) * (Complex.exp (2 * π * Complex.I * θ * z) * g z))) := by
    intro z
    rw [kernelDemod_eq]
    have : Complex.exp (-(2 * π * Complex.I * θ * ((x - z : ℝ) : ℂ))) =
        Complex.exp (-(2 * π * Complex.I * θ * x)) * Complex.exp (2 * π * Complex.I * θ * z) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  simp_rw [e]
  rw [integral_const_mul, integral_const_mul]
  unfold tm
  ring


theorem eLpNorm_two_le_of_integral_sq {G h : ℝ → ℂ} (hG : MemLp G 2 volume) (hh : MemLp h 2 volume) {c : ℝ}
    (hc : 0 ≤ c) (hle : ∫ x, ‖G x‖ ^ 2 ≤ c ^ 2 * ∫ x, ‖h x‖ ^ 2) :
    eLpNorm G 2 volume ≤ ENNReal.ofReal c * eLpNorm h 2 volume := by
  rw [hG.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    hh.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num), ← ENNReal.ofReal_mul hc]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  have hA : 0 ≤ ∫ x, ‖G x‖ ^ 2 := integral_nonneg fun x => by positivity
  have hB : 0 ≤ ∫ x, ‖h x‖ ^ 2 := integral_nonneg fun x => by positivity
  calc (∫ x, ‖G x‖ ^ 2) ^ (2 : ℝ)⁻¹ ≤ (c ^ 2 * ∫ x, ‖h x‖ ^ 2) ^ (2 : ℝ)⁻¹ :=
        Real.rpow_le_rpow hA hle (by norm_num)
    _ = c * (∫ x, ‖h x‖ ^ 2) ^ (2 : ℝ)⁻¹ := by
        rw [Real.mul_rpow (by positivity) hB]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc]
        norm_num


section Main

variable {𝔭 : Params}

theorem treeL2Const_nonneg (h𝔭 : 𝔭.Admissible) : 0 ≤ treeL2Const 𝔭 := by
  obtain ⟨-, hN, -, -, -, -, -, hC1⟩ := h𝔭
  have hC0 : 0 ≤ 𝔭.C := by linarith
  unfold treeL2Const
  have := sInv_nonneg
  have hN14 : 14 ≤ 𝔭.N := le_trans (by unfold classFloor; norm_num) hN
  have h4 : (4 : ℝ) ≤ (((𝔭.decN 10).N : ℕ) : ℝ) := by
    have : 4 ≤ 𝔭.N - 10 := by omega
    simp only [Params.decN]
    exact_mod_cast this
  have := latConst_nonneg (by linarith : (1 : ℝ) < (((𝔭.decN 10).N : ℕ) : ℝ))
  positivity

/-- **Strong type of the demodulated kernel operator of a sub-tree** (any bounded measurable `G`). -/
theorem tileKernelOp_strong (h𝔭 : 𝔭.Admissible) {q s : ℝ} (hq : 1 < q) (hs : 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (Qs : Set Box), IsRankOne 𝔭.J Qs → ∀ (k : Fin 3)
      (Tr : Finset TriTile) (t : Top), (∀ R ∈ Tr, R.box ∈ Qs) → IsTree Tr t → IsLacunary k Tr →
      ∀ (ψ m : TriTile → ℝ → ℂ), IsTreeOpData 𝔭 k Tr ψ m → ∀ (G : ℝ → ZMod P → ℂ), Measurable G →
      (∃ B, ∀ x, yNorm s (G x) ≤ B) →
        eLpNorm (fun x => yNorm s (CZ.kernelOp (tileKernel Tr ψ (fun R => kernelDemod (t.2 * freqDir k) (m R))) G x))
            (ENNReal.ofReal q) volume ≤
          ENNReal.ofReal C * eLpNorm (fun x => yNorm s (G x)) (ENNReal.ofReal q) volume := by
  classical
  obtain ⟨Cz, hCz0, hCz⟩ := CZ.vectorCZ_strong_bdd hq hs
  have h𝔭' := h𝔭
  obtain ⟨hJ, hNf, hDf, hδp, hδq, hβ1, hβ2, hC1⟩ := h𝔭'
  have hD2 : 2 ≤ 𝔭.D := le_trans (by have := classFloor_ge; omega) hDf
  have hβ0 : 0 ≤ 𝔭.β := by linarith
  have hD4 : (3 : ℝ) + 1 ≤ 𝔭.D := by
    have := h𝔭.2.2.1
    have h4 : (400 : ℝ) ≤ 𝔭.D := by exact_mod_cast (le_trans classFloor_ge this)
    linarith
  obtain ⟨Cφ, Cκ, hCφ, hCκ, hTBall⟩ := exists_tileBound h𝔭 (M := 3) (by norm_num) hD4
    (C₀ := 2 * hullConst) (by unfold hullConst; norm_num)
  set A : ℝ := max (tileCZ (𝔭.N : ℝ) 3 Cφ Cκ) (Real.sqrt (treeL2Const 𝔭)) with hA
  have hN1 : (1 : ℝ) < 𝔭.N := by
    have := h𝔭.2.1
    have h4 : (400 : ℝ) ≤ 𝔭.N := by exact_mod_cast (le_trans classFloor_ge this)
    linarith
  have hczpos : 0 ≤ tileCZ (𝔭.N : ℝ) 3 Cφ Cκ := by
    unfold tileCZ; have := latConst_nonneg hN1; positivity
  have hA0 : 0 ≤ A := le_trans hczpos (le_max_left _ _)
  refine ⟨Cz * A, by positivity, ?_⟩
  intro P _ Qs hQ k Tr t hbox ht hlac ψ m hdata G hG hGb
  set θ : ℝ := t.2 * freqDir k with hθ
  have hTB : ∀ R ∈ Tr, TileBound (𝔭.N : ℝ) 3 Cφ Cκ R.box.scale R.pos (ψ R) (kernelDemod θ (m R)) := fun R hR =>
    hTBall R.box.scale R.pos (R.box.centre k) θ (ψ R) (m R) (hdata.1 R hR).1 (hdata.1 R hR).2
      (centre_sub_theta_le hQ (hbox R hR) (ht R hR).2 k)
  have hinj : Set.InjOn (fun R : TriTile => (R.box.scale, R.pos)) (Tr : Set TriTile) := by
    intro R hR R' hR' h
    simp only [Prod.mk.injEq] at h
    have hb : R.box = R'.box := ht.box_eq_of_scale_eq hQ hbox R hR R' hR' h.1
    cases R; cases R'
    simp only at hb h
    simp [hb, h.2]
  set K' : ℝ → ℝ → ℂ := tileKernel Tr ψ (fun R => kernelDemod θ (m R)) with hK'
  have hcz : CZ.IsCZKernel A K' :=
    (isCZKernel_tileKernel (N := (𝔭.N : ℝ)) (M := 3) hN1 le_rfl Tr (fun R => R.box.scale) (fun R => R.pos) ψ
      (fun R => kernelDemod θ (m R)) hTB hinj hCφ hCκ).mono (le_max_left _ _)
  have hmeas : Measurable (Function.uncurry K') :=
    (continuous_tileKernel Tr ψ (fun R => kernelDemod θ (m R))
      (fun R hR => (hTB R hR).φ_diff.continuous) (fun R hR => (hTB R hR).κ_diff.continuous)).measurable
  have hbdd : ∃ M : ℝ, ∀ x z, ‖K' x z‖ ≤ M :=
    bounded_tileKernel (N := (𝔭.N : ℝ)) (M := 3) (by positivity) (by norm_num) Tr (fun R => R.box.scale)
      (fun R => R.pos) ψ (fun R => kernelDemod θ (m R)) hTB
  -- the scalar `L²` bound for bounded integrable `g`
  have hL2 : ∀ g : ℝ → ℂ, Measurable g → Integrable g volume → (∃ B' : ℝ, ∀ x, ‖g x‖ ≤ B') →
      eLpNorm (fun x => ∫ z, K' x z * g z) 2 volume ≤ ENNReal.ofReal A * eLpNorm g 2 volume := by
    intro g hg hgi hgb
    obtain ⟨b, hb⟩ := hgb
    set f : ℝ → ℂ := fun z => Complex.exp (2 * π * Complex.I * θ * z) * g z with hf
    have hfn : ∀ z, ‖f z‖ = ‖g z‖ := fun z => by
      simp only [hf, norm_mul]
      rw [show (2 * (π : ℂ) * Complex.I * θ * z) = ((2 * π * θ * z : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, one_mul]
    have hfm : Measurable f := by
      refine Measurable.mul ?_ hg
      exact (Complex.continuous_exp.comp (by fun_prop)).measurable
    have hfb : ∀ z, ‖f z‖ ≤ b := fun z => (hfn z).trans_le (hb z)
    have hfi : Integrable f volume := hgi.norm.mono' hfm.aestronglyMeasurable (Eventually.of_forall fun z => (hfn z).le)
    have hf2 : MemLp f 2 volume := CZ.memLp_two_of_bdd_integrable hfm hfi ⟨b, hfb⟩
    have hg2 : MemLp g 2 volume := CZ.memLp_two_of_bdd_integrable hg hgi ⟨b, hb⟩
    have hid : ∀ x, ∫ z, K' x z * g z = Complex.exp (-(2 * π * Complex.I * θ * x)) *
        ∑ R ∈ Tr, gfun (ψ R) (m R) f x := by
      intro x
      exact kernel_integral_eq (N := (𝔭.N : ℝ)) (M := 3) (Cφ := Cφ) (Cκ := Cκ) (by norm_num) hTB hg hb x
    have hcontG : ∀ R ∈ Tr, Continuous (gfun (ψ R) (m R) f) := fun R hR =>
      continuous_gfun hD2 hβ0 (hdata.1 R hR).1 (hdata.1 R hR).2 hfm hfb
    have hN2 : 2 ≤ 𝔭.N := le_trans (by have := classFloor_ge; omega) hNf
    have hgmem : ∀ R ∈ Tr, MemLp (gfun (ψ R) (m R) f) 2 volume := fun R hR =>
      (memLp_two_iff_integrable_sq_norm (hcontG R hR).aestronglyMeasurable).2
        (integrable_sq_gfun hN2 hD2 hβ0 (hdata.1 R hR).1 (hdata.1 R hR).2 hfm hfb)
    have hSmem : MemLp (fun x => ∑ R ∈ Tr, gfun (ψ R) (m R) f x) 2 volume := memLp_finsetSum _ hgmem
    have hcontS : Continuous (fun x => ∑ R ∈ Tr, gfun (ψ R) (m R) f x) := continuous_finsetSum _ hcontG
    have hnum := tree_L2 h𝔭 hQ hlac hbox hdata.1 hdata.2 hfm hfi hf2 hfb
    have hcsq : (Real.sqrt (treeL2Const 𝔭)) ^ 2 = treeL2Const 𝔭 := Real.sq_sqrt (treeL2Const_nonneg h𝔭)
    have hle := eLpNorm_two_le_of_integral_sq hSmem hf2 (Real.sqrt_nonneg _) (by rw [hcsq]; exact hnum)
    have hfg : eLpNorm f 2 volume = eLpNorm g 2 volume :=
      eLpNorm_congr_norm_ae hfm.aestronglyMeasurable hg.aestronglyMeasurable (Eventually.of_forall hfn)
    have hfun : (fun x => ∫ z, K' x z * g z) = fun x : ℝ => Complex.exp (-(2 * π * Complex.I * θ * (x : ℂ))) *
        ∑ R ∈ Tr, gfun (ψ R) (m R) f x := funext hid
    have hexpn : ∀ x : ℝ, ‖Complex.exp (-(2 * π * Complex.I * θ * x))‖ = 1 := fun x => by
      rw [show (-(2 * (π : ℂ) * Complex.I * θ * x)) = ((-(2 * π * θ * x) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    have hmeasL : AEStronglyMeasurable (fun x : ℝ => Complex.exp (-(2 * π * Complex.I * θ * (x : ℂ))) *
        ∑ R ∈ Tr, gfun (ψ R) (m R) f x) volume :=
      ((Complex.continuous_exp.comp (by fun_prop)).mul hcontS).aestronglyMeasurable
    rw [hfun]
    calc eLpNorm (fun x : ℝ => Complex.exp (-(2 * π * Complex.I * θ * (x : ℂ))) * ∑ R ∈ Tr, gfun (ψ R) (m R) f x) 2 volume
        = eLpNorm (fun x => ∑ R ∈ Tr, gfun (ψ R) (m R) f x) 2 volume :=
          eLpNorm_congr_norm_ae hmeasL hcontS.aestronglyMeasurable
            (Eventually.of_forall fun x => by rw [norm_mul, hexpn, one_mul])
      _ ≤ ENNReal.ofReal (Real.sqrt (treeL2Const 𝔭)) * eLpNorm f 2 volume := hle
      _ ≤ ENNReal.ofReal A * eLpNorm g 2 volume := by
          rw [hfg]
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) le_rfl
  exact hCz P A K' hcz hmeas hbdd hL2 G hG hGb

end Main

end PrimeBHT.TimeFrequency.X2
