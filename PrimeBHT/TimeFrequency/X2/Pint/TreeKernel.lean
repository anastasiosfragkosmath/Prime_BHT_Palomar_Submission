module

public import PrimeBHT.TimeFrequency.X2.Pint.TheoremIIMeas
public import PrimeBHT.TimeFrequency.X2.Pint.BMO
public import PrimeBHT.TimeFrequency.X2.EngTail.TreeStrong

/-!
# X2, V11: lacunary tree operators as kernel operators for Theorem II

* `treeKer Tr ψ m θ x w = tileKernel Tr ψ (kernelDemod θ ∘ m) x w · e^{-2πiθw}` (the modulated tree kernel);
* `kernelOp_treeKer`: `kernelOp (treeKer …) F x = e^{-2πiθx} • treeOp Tr ψ m F x` (bounded measurable `F`), hence
  `yNorm s (kernelOp (treeKer …) F x) = yNorm s (treeOp Tr ψ m F x)`;
* `tileKernel_row_col`: qualitative row and column `L¹` bounds;
* `treeKer_bmo`: the BMO endpoint, uniformly in the tree (`bmo_of_cz` with `isCZKernel_tileKernel` and
  `tileKernelOp_strong` at `(s₀, s₀)`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- The modulated tree kernel. -/
def treeKer (Tr : Finset TriTile) (ψ m : TriTile → ℝ → ℂ) (θ : ℝ) (x w : ℝ) : ℂ :=
  tileKernel Tr ψ (fun R => kernelDemod θ (m R)) x w * Complex.exp (-(2 * π * Complex.I * θ * w))

theorem norm_exp_phase (θ w : ℝ) : ‖Complex.exp (-(2 * π * Complex.I * θ * w))‖ = 1 := by
  rw [show (-(2 * (π : ℂ) * Complex.I * θ * w)) = ((-(2 * π * θ * w) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem norm_treeKer (Tr : Finset TriTile) (ψ m : TriTile → ℝ → ℂ) (θ x w : ℝ) :
    ‖treeKer Tr ψ m θ x w‖ = ‖tileKernel Tr ψ (fun R => kernelDemod θ (m R)) x w‖ := by
  rw [treeKer, norm_mul, norm_exp_phase, mul_one]

/-- The uniform tile bounds of a tree with data. -/
theorem exists_treeBounds {𝔭 : Params} (h𝔭 : 𝔭.Admissible) :
    ∃ Cφ Cκ : ℝ, 0 ≤ Cφ ∧ 0 ≤ Cκ ∧ ∀ (Qs : Set Box), IsRankOne 𝔭.J Qs → ∀ (k : Fin 3) (Tr : Finset TriTile)
      (t : Top), (∀ R ∈ Tr, R.box ∈ Qs) → IsTree Tr t → ∀ ψ m : TriTile → ℝ → ℂ, IsTreeOpData 𝔭 k Tr ψ m →
        (∀ R ∈ Tr, TileBound (𝔭.N : ℝ) 3 Cφ Cκ R.box.scale R.pos (ψ R) (kernelDemod (t.2 * freqDir k) (m R))) ∧
        Set.InjOn (fun R : TriTile => (R.box.scale, R.pos)) (Tr : Set TriTile) := by
  have hD4 : (3 : ℝ) + 1 ≤ 𝔭.D := by
    have := h𝔭.2.2.1
    have h4 : (400 : ℝ) ≤ 𝔭.D := by exact_mod_cast (le_trans classFloor_ge this)
    linarith
  obtain ⟨Cφ, Cκ, hCφ, hCκ, hTBall⟩ := exists_tileBound h𝔭 (M := 3) (by norm_num) hD4
    (C₀ := 2 * hullConst) (by unfold hullConst; norm_num)
  refine ⟨Cφ, Cκ, hCφ, hCκ, fun Qs hQ k Tr t hbox ht ψ m hdata => ⟨fun R hR => ?_, ?_⟩⟩
  · exact hTBall R.box.scale R.pos (R.box.centre k) _ (ψ R) (m R) (hdata.1 R hR).1 (hdata.1 R hR).2
      (centre_sub_theta_le hQ (hbox R hR) (ht R hR).2 k)
  · intro R hR R' hR' h
    simp only [Prod.mk.injEq] at h
    have hb : R.box = R'.box := ht.box_eq_of_scale_eq hQ hbox R hR R' hR' h.1
    cases R; cases R'
    simp only at hb h
    simp [hb, h.2]

section Generic

variable {ι : Type*} {N Cφ Cκ : ℝ} {S : Finset ι} {j v : ι → ℤ} {φ κ : ι → ℝ → ℂ}

/-- The decay weight integral is translation invariant and finite. -/
theorem lintegral_decay_shift {L : ℝ} (_hL : 0 < L) (c : ℝ) :
    ∫⁻ z, ENNReal.ofReal (L⁻¹ * (1 + |c - z| / L) ^ (-(3 : ℝ))) =
      ∫⁻ u, ENNReal.ofReal (L⁻¹ * (1 + |u| / L) ^ (-(3 : ℝ))) := by
  simp_rw [abs_sub_comm c]
  exact lintegral_sub_right_eq_self (μ := volume) (fun u => ENNReal.ofReal (L⁻¹ * (1 + |u| / L) ^ (-(3 : ℝ)))) c

theorem lintegral_decay_shift' {L : ℝ} (hL : 0 < L) (c : ℝ) :
    ∫⁻ z, ENNReal.ofReal (L⁻¹ * (1 + |z - c| / L) ^ (-(3 : ℝ))) =
      ∫⁻ u, ENNReal.ofReal (L⁻¹ * (1 + |u| / L) ^ (-(3 : ℝ))) := by
  simp_rw [abs_sub_comm _ c]; exact lintegral_decay_shift hL c

theorem lintegral_decay_lt_top {L : ℝ} (hL : 0 < L) :
    ∫⁻ u, ENNReal.ofReal (L⁻¹ * (1 + |u| / L) ^ (-(3 : ℝ))) < ⊤ := by
  have h := (integrable_one_add_abs_sub_div_rpow (p := 3) (by norm_num) 0 hL).const_mul L⁻¹
  simp only [sub_zero] at h
  exact h.lintegral_lt_top

theorem enorm_tileKernel_le (hN : 0 ≤ N) (hb : ∀ i ∈ S, TileBound N 3 Cφ Cκ (j i) (v i) (φ i) (κ i)) (x z : ℝ) :
    ‖tileKernel S φ κ x z‖ₑ ≤ ∑ i ∈ S, ENNReal.ofReal (Cφ * Cκ) *
      ENNReal.ofReal (((2 : ℝ) ^ j i)⁻¹ * (1 + |x - z| / (2 : ℝ) ^ j i) ^ (-(3 : ℝ))) := by
  unfold tileKernel
  refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [← ENNReal.ofReal_mul (mul_nonneg (hb i hi).nonneg_Cφ (hb i hi).nonneg_Cκ), ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [norm_mul]
  have h1 := (hb i hi).φ_le x
  have h2 := (hb i hi).κ_le (x - z)
  have h3 := tw_le_one hN (j i) (v i) x
  have hCφ := (hb i hi).nonneg_Cφ
  have hL : (0 : ℝ) < (2 : ℝ) ^ j i := zpow_pos (by norm_num) _
  calc ‖φ i x‖ * ‖κ i (x - z)‖ ≤ (Cφ * 1) * (Cκ * (((2 : ℝ) ^ j i)⁻¹ * (1 + |x - z| / (2 : ℝ) ^ j i) ^ (-(3 : ℝ)))) :=
        mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left h3 hCφ)) h2 (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Qualitative row and column `L¹` bounds of a finite tile kernel. -/
theorem tileKernel_row_col (hN : 0 ≤ N) (hb : ∀ i ∈ S, TileBound N 3 Cφ Cκ (j i) (v i) (φ i) (κ i)) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, ∫⁻ z, ‖tileKernel S φ κ x z‖ₑ ≤ ENNReal.ofReal C) ∧
      ∀ z, ∫⁻ x, ‖tileKernel S φ κ x z‖ₑ ≤ ENNReal.ofReal C := by
  set T : ℝ≥0∞ := ∑ i ∈ S, ENNReal.ofReal (Cφ * Cκ) *
    ∫⁻ u, ENNReal.ofReal (((2 : ℝ) ^ j i)⁻¹ * (1 + |u| / (2 : ℝ) ^ j i) ^ (-(3 : ℝ))) with hT
  have hTf : T ≠ ⊤ := ENNReal.sum_ne_top.2 fun i _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_decay_lt_top (zpow_pos (by norm_num) _)).ne
  have hm : ∀ i, Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (((2 : ℝ) ^ j i)⁻¹ * (1 + |p.1 - p.2| / (2 : ℝ) ^ j i) ^ (-(3 : ℝ))) := fun i => by
    fun_prop
  refine ⟨T.toReal, ENNReal.toReal_nonneg, fun x => ?_, fun z => ?_⟩
  · rw [ENNReal.ofReal_toReal hTf]
    refine (lintegral_mono fun z => enorm_tileKernel_le hN hb x z).trans (le_of_eq ?_)
    rw [lintegral_finset_sum _ fun i _ => by fun_prop]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_const_mul _ (by fun_prop)]
    congr 1
    exact lintegral_decay_shift (zpow_pos (by norm_num) _) x
  · rw [ENNReal.ofReal_toReal hTf]
    refine (lintegral_mono fun x => enorm_tileKernel_le hN hb x z).trans (le_of_eq ?_)
    rw [lintegral_finset_sum _ fun i _ => by fun_prop]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_const_mul _ (by fun_prop)]
    congr 1
    exact lintegral_decay_shift' (zpow_pos (by norm_num) _) z

end Generic

variable {P : ℕ} [NeZero P]

omit [NeZero P] in
/-- The modulated tree kernel operator is the tree operator up to a unimodular factor. -/
theorem kernelOp_treeKer {N Cφ Cκ : ℝ} {Tr : Finset TriTile} {ψ m : TriTile → ℝ → ℂ} {θ : ℝ}
    (hTB : ∀ Q ∈ Tr, TileBound N 3 Cφ Cκ Q.box.scale Q.pos (ψ Q) (kernelDemod θ (m Q)))
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {b : ℝ} (hb : ∀ z y, ‖F z y‖ ≤ b) (x : ℝ) :
    Pint.kernelOp (treeKer Tr ψ m θ) F x = Complex.exp (-(2 * π * Complex.I * θ * x)) • treeOp Tr ψ m F x := by
  funext y
  have hg : Measurable fun z : ℝ => Complex.exp (-(2 * π * Complex.I * θ * z)) * F z y :=
    (by fun_prop : Measurable fun z : ℝ => Complex.exp (-(2 * π * Complex.I * θ * z))).mul
      ((measurable_pi_apply y).comp hF)
  have h := kernel_integral_eq (N := N) (M := 3) (Cφ := Cφ) (Cκ := Cκ) (by norm_num) hTB hg (b := b)
    (fun z => by rw [norm_mul, norm_exp_phase, one_mul]; exact hb z y) x
  simp only [Pint.kernelOp, treeKer, Pi.smul_apply, smul_eq_mul, treeOp, Finset.sum_apply]
  have e : (fun w => tileKernel Tr ψ (fun R => kernelDemod θ (m R)) x w *
      Complex.exp (-(2 * π * Complex.I * θ * w)) * F w y) = fun z =>
      tileKernel Tr ψ (fun R => kernelDemod θ (m R)) x z * (Complex.exp (-(2 * π * Complex.I * θ * z)) * F z y) :=
    funext fun w => by ring
  rw [e, h]
  congr 1
  refine Finset.sum_congr rfl fun Q _ => ?_
  congr 1
  rw [tmult_apply_eq_tm]
  congr 1
  funext z
  rw [← mul_assoc, ← Complex.exp_add]
  simp

theorem yNorm_kernelOp_treeKer {N Cφ Cκ : ℝ} {Tr : Finset TriTile} {ψ m : TriTile → ℝ → ℂ} {θ : ℝ}
    (hTB : ∀ Q ∈ Tr, TileBound N 3 Cφ Cκ Q.box.scale Q.pos (ψ Q) (kernelDemod θ (m Q)))
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) {b : ℝ} (hb : ∀ z y, ‖F z y‖ ≤ b) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    yNorm s (Pint.kernelOp (treeKer Tr ψ m θ) F x) = yNorm s (treeOp Tr ψ m F x) := by
  rw [kernelOp_treeKer hTB hF hb x, Pint.yNorm_smul' hs, norm_exp_phase, one_mul]

/-- **The BMO endpoint for tree kernels**, uniformly in the tree and its data. -/
theorem treeKer_bmo {𝔭 : Params} (h𝔭 : 𝔭.Admissible) {p : ℝ} (hp : 1 < p) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (P : ℕ) [NeZero P] (Qs : Set Box), IsRankOne 𝔭.J Qs → ∀ (k : Fin 3)
      (Tr : Finset TriTile) (t : Top), (∀ R ∈ Tr, R.box ∈ Qs) → IsTree Tr t → IsLacunary k Tr →
      ∀ (ψ m : TriTile → ℝ → ℂ), IsTreeOpData 𝔭 k Tr ψ m → ∀ (G : ℝ → ZMod P → ℂ), Measurable G →
      (∀ w, yNorm p (G w) ≤ 1) → ∀ a b : ℝ, a < b →
        ∫⁻ x in Ico a b, ENNReal.ofReal (yNorm p (Pint.kernelOp (treeKer Tr ψ m (t.2 * freqDir k)) G x -
          Pint.avgOn a b (Pint.kernelOp (treeKer Tr ψ m (t.2 * freqDir k)) G))) ≤ ENNReal.ofReal (Cb * (b - a)) := by
  obtain ⟨Cs, hCs, hstr⟩ := tileKernelOp_strong h𝔭 hp hp
  obtain ⟨Cφ, Cκ, hCφ, hCκ, hTB⟩ := exists_treeBounds h𝔭
  have hN1 : (1 : ℝ) < 𝔭.N := by
    have h4 : (400 : ℝ) ≤ 𝔭.N := by exact_mod_cast (le_trans classFloor_ge h𝔭.2.1)
    linarith
  set A := tileCZ (𝔭.N : ℝ) 3 Cφ Cκ with hA
  have hA0 : 0 ≤ A := by unfold A tileCZ; have := latConst_nonneg hN1; positivity
  refine ⟨2 * (2 * Cs + A), by positivity, ?_⟩
  intro P _ Qs hQ k Tr t hbox ht hlac ψ m hdata G hG hG1 a b hab
  obtain ⟨hTB', hinj⟩ := hTB Qs hQ k Tr t hbox ht ψ m hdata
  set θ := t.2 * freqDir k with hθ
  set Kd : ℝ → ℝ → ℂ := tileKernel Tr ψ (fun R => kernelDemod θ (m R)) with hKd
  have hcz : CZ.IsCZKernel A Kd := isCZKernel_tileKernel (N := (𝔭.N : ℝ)) (M := 3) hN1 le_rfl Tr
    (fun R => R.box.scale) (fun R => R.pos) ψ (fun R => kernelDemod θ (m R)) hTB' hinj hCφ hCκ
  have hKm : StronglyMeasurable (Function.uncurry Kd) :=
    (continuous_tileKernel Tr ψ (fun R => kernelDemod θ (m R))
      (fun R hR => (hTB' R hR).φ_diff.continuous) (fun R hR => (hTB' R hR).κ_diff.continuous)).stronglyMeasurable
  obtain ⟨Cl, -, hrow, -⟩ := tileKernel_row_col (by positivity) hTB'
  set G' : ℝ → ZMod P → ℂ := fun w => Complex.exp (-(2 * π * Complex.I * θ * w)) • G w with hG'
  have hG'm : Measurable G' := by
    refine measurable_pi_iff.2 fun y => ?_
    exact (by fun_prop : Measurable fun z : ℝ => Complex.exp (-(2 * π * Complex.I * θ * z))).mul
      ((measurable_pi_apply y).comp hG)
  have hG'1 : ∀ w, yNorm p (G' w) ≤ 1 := fun w => by
    rw [hG', Pint.yNorm_smul' (by linarith), norm_exp_phase, one_mul]; exact hG1 w
  have he : Pint.kernelOp (treeKer Tr ψ m θ) G = Pint.kernelOp Kd G' := by
    funext x y
    simp only [Pint.kernelOp, treeKer, hKd, hG', Pi.smul_apply, smul_eq_mul]
    congr 1; funext w; ring
  rw [he]
  exact Pint.bmo_of_cz hp hcz hKm hrow hCs
    (fun G hG hGb => hstr P Qs hQ k Tr t hbox ht hlac ψ m hdata G hG hGb) hG'm hG'1 hab

end PrimeBHT.TimeFrequency.X2
