module

public import PrimeBHT.TimeFrequency.X2.Energy
public import PrimeBHT.TimeFrequency.X2.ClassLemmas
import PrimeBHT.TimeFrequency.X2.ClassKernel
import PrimeBHT.TimeFrequency.Tile.Gram.Pair

/-!
# X2, node V10: single-tile energies and the bound `tileEng ≲ ‖F‖_∞`

`tileEng 𝔭 k F R = sup_{ψ ∈ Ψ_{I_R}(𝔭), m ∈ M_{ω_{R,k}}(𝔭)} |I_R|^{-1/2} ‖ψ T_m F‖_{L²(ℝ; L²(Y))}`
(DPLMV (e:sscaleen), HLC `|⟨f,φ_P⟩|/|I_P|^{1/2}`), realized as the `topNorm` of the one-tile tree `{R}`.

* `measurable_tmult_inMult`: `T_m F` is measurable for measurable `F` (so the `L²`-norms are honest norms, not `⊤`);
* `tileEng_le`: DPLMV (e:sscaleentv): `tileEng ≤ C ‖F‖_∞` (from `norm_singleTile_le` and `L²` of the decay weight).
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal FourierTransform
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- The single-tile energy: the tree norm of the one-tile tree `{R}` (the top frequency plays no role). -/
def tileEng {P : ℕ} [NeZero P] (𝔭 : Params) (k : Fin 3) (F : ℝ → ZMod P → ℂ) (R : TriTile) : ℝ≥0∞ :=
  topNorm 𝔭 2 k F {R} ((R.box.scale, R.pos), 0) 2

theorem measurable_tmult_inMult {P : ℕ} {𝔭 : Params} {sc : ℤ} {c : ℝ} {m : ℝ → ℂ} (hm : InMult 𝔭 sc c m)
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) : Measurable (tmult m F) := by
  have hK : Continuous (𝓕⁻ m) :=
    continuous_fourierInv_of_integrable' (integrable_of_far hm.1.continuous hm.2.1)
  refine measurable_pi_iff.2 fun y => ?_
  have h1 : StronglyMeasurable (Function.uncurry fun (x z : ℝ) => 𝓕⁻ m (x - z) * F z y) :=
    ((hK.comp (continuous_fst.sub continuous_snd)).stronglyMeasurable).mul
      ((((measurable_pi_apply y).comp hF).comp measurable_snd).stronglyMeasurable)
  exact (h1.integral_prod_right).measurable

theorem measurable_psi_smul_tmult {P : ℕ} {𝔭 : Params} {sc v : ℤ} {c : ℝ} {ψ m : ℝ → ℂ}
    (hψ : InPsi 𝔭 sc v ψ) (hm : InMult 𝔭 sc c m) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) :
    Measurable (fun x => ψ x • tmult m F x) := by
  refine measurable_pi_iff.2 fun y => ?_
  have h1 : Measurable fun x => tmult m F x y := (measurable_pi_apply y).comp (measurable_tmult_inMult hm hF)
  show Measurable fun x => ψ x * tmult m F x y
  exact hψ.1.measurable.mul h1

theorem enorm_eq_ofReal_yNorm {P : ℕ} [NeZero P] (s : ℝ) (G : ZMod P → ℂ) :
    ‖yNorm s G‖ₑ = ENNReal.ofReal (yNorm s G) :=
  Real.enorm_eq_ofReal (by unfold yNorm; positivity)

/-- `‖(1 + |x - c|/L)^{-N}‖_{L²}` computed: `∫ ((1 + |x - c|/L)^{-N})² = 2L/(2N-1)`. -/
theorem lintegral_sq_jb_decay {N : ℕ} (hN : 1 ≤ N) (c : ℝ) {L : ℝ} (hL : 0 < L) (A : ℝ) (hA : 0 ≤ A) :
    ∫⁻ x, ENNReal.ofReal (A * (1 + |x - c| / L) ^ (-(N : ℝ))) ^ (2 : ℝ) =
      ENNReal.ofReal (A ^ 2 * (2 * L / (2 * N - 1))) := by
  have hN1 : (1 : ℝ) < 2 * N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hpt : ∀ x : ℝ, ENNReal.ofReal (A * (1 + |x - c| / L) ^ (-(N : ℝ))) ^ (2 : ℝ) =
      ENNReal.ofReal (A ^ 2 * (1 + |x - c| / L) ^ (-(2 * N : ℝ))) := by
    intro x
    have h0 : 0 ≤ 1 + |x - c| / L := by positivity
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 1
    rw [Real.rpow_two, mul_pow, ← Real.rpow_natCast ((1 + |x - c| / L) ^ (-(N : ℝ))) 2,
      ← Real.rpow_mul h0]
    congr 2
    push_cast; ring
  simp_rw [hpt]
  have hint : Integrable (fun x : ℝ => A ^ 2 * (1 + |x - c| / L) ^ (-(2 * N : ℝ))) :=
    (integrable_one_add_abs_sub_div_rpow hN1 c hL).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun x => by positivity)]
  congr 1
  rw [integral_const_mul, integral_one_add_abs_sub_div_rpow hN1 c hL]

/-- **DPLMV (e:sscaleentv)**: the single-tile energy is bounded by the sup norm. -/
theorem tileEng_le (𝔭 : Params) (h𝔭 : 𝔭.Admissible) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ℕ) [NeZero P] (k : Fin 3) (F : ℝ → ZMod P → ℂ) (B : ℝ), Measurable F →
      (∀ x, yNorm 2 (F x) ≤ B) → ∀ R : TriTile, tileEng 𝔭 k F R ≤ ENNReal.ofReal (C * B) := by
  obtain ⟨K, hK0, hK⟩ := norm_singleTile_le 𝔭 h𝔭 (s := 2) (by norm_num)
  obtain ⟨hN, -, -, -⟩ := h𝔭.bounds
  refine ⟨K, hK0, ?_⟩
  intro P _ k F B hF hB R
  have hB0 : 0 ≤ B := le_trans (by unfold yNorm; positivity) (hB 0)
  unfold tileEng
  refine topNorm_le_of_forall fun ψ m hdata => ?_
  obtain ⟨hψ, hm⟩ := hdata.1 R (Finset.mem_singleton_self R)
  set sc := R.box.scale with hsc
  set ℓ : ℝ := (2 : ℝ) ^ sc with hℓ
  have hℓ0 : 0 < ℓ := zpow_pos (by norm_num) _
  set c := dyCentre sc R.pos with hc
  have hsing : ∀ x, treeOp {R} ψ m F x = ψ R x • tmult (m R) F x := by
    intro x; simp [treeOp]
  have hmeas : Measurable fun x => ψ R x • tmult (m R) F x := measurable_psi_smul_tmult hψ hm hF
  -- pointwise bound
  have hpt : ∀ x, ‖yNorm 2 (treeOp {R} ψ m F x)‖ₑ ≤
      ‖K * B * (1 + |x - c| / ℓ) ^ (-(𝔭.N : ℝ))‖ₑ := by
    intro x
    rw [hsing, enorm_eq_ofReal_yNorm]
    have h1 := hK P sc R.pos (R.box.centre k) (ψ R) (m R) hψ hm F hF x
    have h2 : PrimeCarleson.Proof.Common.maximalHLR (fun z => ENNReal.ofReal (yNorm 2 (F z))) x ≤
        ENNReal.ofReal B :=
      PrimeBHT.TimeFrequency.Tile.maximalHLR_le_of_enorm_le
        (fun y => by simpa using ENNReal.ofReal_le_ofReal (hB y)) x
    have hjb : jb ((x - c) / ℓ) = 1 + |x - c| / ℓ := by
      unfold jb; rw [abs_div, abs_of_pos hℓ0]
    have hnn : 0 ≤ K * B * (1 + |x - c| / ℓ) ^ (-(𝔭.N : ℝ)) := by positivity
    rw [Real.enorm_eq_ofReal hnn]
    refine h1.trans ?_
    rw [hjb]
    calc ENNReal.ofReal (K * (1 + |x - c| / ℓ) ^ (-(𝔭.N : ℝ))) *
          PrimeCarleson.Proof.Common.maximalHLR (fun z => ENNReal.ofReal (yNorm 2 (F z))) x
        ≤ ENNReal.ofReal (K * (1 + |x - c| / ℓ) ^ (-(𝔭.N : ℝ))) * ENNReal.ofReal B := by gcongr
      _ = ENNReal.ofReal (K * B * (1 + |x - c| / ℓ) ^ (-(𝔭.N : ℝ))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  have hmeas2 : AEStronglyMeasurable (fun x => yNorm 2 (treeOp {R} ψ m F x)) volume := by
    have : (fun x => yNorm 2 (treeOp {R} ψ m F x)) = fun x => yNorm 2 (ψ R x • tmult (m R) F x) := by
      funext x; rw [hsing]
    rw [this]
    exact ((measurable_yNorm_fun 2).comp hmeas).aestronglyMeasurable
  have hL2 := eLpNorm_mono_enorm hmeas2 (p := ENNReal.ofReal 2) hpt
  -- the `L²` norm of the weight
  have hg : eLpNorm (fun x : ℝ => K * B * (1 + |x - c| / ℓ) ^ (-(𝔭.N : ℝ))) (ENNReal.ofReal 2) volume =
      ENNReal.ofReal (Real.sqrt (K ^ 2 * B ^ 2 * (2 * ℓ / (2 * 𝔭.N - 1)))) := by
    have hgc : Continuous fun x : ℝ => K * B * (1 + |x - c| / ℓ) ^ (-(𝔭.N : ℝ)) :=
      continuous_const.mul (Continuous.rpow_const (by fun_prop) (fun x => Or.inl (by positivity)))
    have hNp : (2 : ℝ) ≤ 2 * 𝔭.N - 1 := by
      have : (400 : ℝ) ≤ 𝔭.N := by exact_mod_cast hN
      linarith
    rw [ENNReal.ofReal_ofNat, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hgc.aestronglyMeasurable]
    have hA : 0 ≤ K * B := by positivity
    have := lintegral_sq_jb_decay (N := 𝔭.N) (by omega) c hℓ0 (K * B) hA
    simp only [ENNReal.toReal_ofNat]
    have e : ∀ x : ℝ, ‖K * B * (1 + |x - c| / ℓ) ^ (-(𝔭.N : ℝ))‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal (K * B * (1 + |x - c| / ℓ) ^ (-(𝔭.N : ℝ))) ^ (2 : ℝ) := by
      intro x
      rw [Real.enorm_eq_ofReal (by positivity)]
    simp_rw [e]
    rw [this, ENNReal.ofReal_rpow_of_nonneg
      (mul_nonneg (sq_nonneg _) (div_nonneg (by positivity) (by linarith))) (by norm_num),
      Real.sqrt_eq_rpow]
    congr 2
    ring
  rw [hg] at hL2
  -- assemble
  unfold treeOpNorm
  refine (mul_le_mul' le_rfl hL2).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hNpos : (2 : ℝ) ≤ 2 * 𝔭.N - 1 := by
    have : (400 : ℝ) ≤ 𝔭.N := by exact_mod_cast hN
    linarith
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ0
  have ha : ℓ ^ (-1 / (2 : ℝ)) = (Real.sqrt ℓ)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hℓ0.le]; norm_num
  have hb : Real.sqrt (K ^ 2 * B ^ 2 * (2 * ℓ / (2 * 𝔭.N - 1))) ≤ K * B * Real.sqrt ℓ := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hℓ0.le]
    have : 2 * ℓ / (2 * 𝔭.N - 1) ≤ ℓ := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    nlinarith [sq_nonneg (K * B), mul_le_mul_of_nonneg_left this (sq_nonneg (K * B))]
  calc ((2 : ℝ) ^ ((R.box.scale, R.pos), (0 : ℝ)).1.1) ^ (-1 / (2 : ℝ)) *
        Real.sqrt (K ^ 2 * B ^ 2 * (2 * ℓ / (2 * 𝔭.N - 1)))
      = (Real.sqrt ℓ)⁻¹ * Real.sqrt (K ^ 2 * B ^ 2 * (2 * ℓ / (2 * 𝔭.N - 1))) := by
        rw [← ha]
    _ ≤ (Real.sqrt ℓ)⁻¹ * (K * B * Real.sqrt ℓ) := by gcongr
    _ = K * B := by field_simp

end PrimeBHT.TimeFrequency.X2
