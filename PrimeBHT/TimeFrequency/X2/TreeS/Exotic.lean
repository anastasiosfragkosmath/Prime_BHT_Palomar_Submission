module

public import PrimeBHT.TimeFrequency.X2.Psp.Domination
import Mathlib.Analysis.Fourier.Convolution

/-!
# X2, node V15s: a lower-bounded cutoff of the TREE class `𝔭.tree`

The model cutoffs `θ_I = 1_I * η_s` (`IsEtaCut 𝔭 η`) have two-sided decay of order `𝔭.N`, while the energies are taken in the
class `𝔭.tree` of decay order `b = 𝔭.N / 8`.  To dominate weights of order `b` by an element of `Ψ_I(𝔭.tree)` we use
`ψ̃_I = ρ_I * η_s`, `ρ_I(y) = ⟨(y - c_I)/|I|⟩^{-b}`: it is continuous with `𝓕 ψ̃_I` supported in `[-δ/|I|, δ/|I|]`
(convolution with `η_s`), and has the two-sided bound `c ⟨(x - c_I)/|I|⟩^{-b} ≤ ψ̃_I(x) ≤ C ⟨(x - c_I)/|I|⟩^{-b}`.
`exists_psiTilde`: a multiple of `ψ̃_I` lies in `Ψ_I(𝔭.tree)` and is bounded below by `psiLow 𝔭 ⟨⟩^{-b}`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform Convolution Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

section Exotic

variable {𝔭 : Params} {η : ℝ → ℝ}

/-- The weight `ρ_I(y) = ⟨(y - c_I)/|I|⟩^{-b}`. -/
def expRho (b : ℝ) (s v : ℤ) (y : ℝ) : ℝ := jb ((y - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b)

/-- The convolution integrand `ρ_I(y) η_s(x - y)`. -/
def expInt (η : ℝ → ℝ) (b : ℝ) (s v : ℤ) (x y : ℝ) : ℝ :=
  expRho b s v y * ((2 : ℝ) ^ (-s) * η ((x - y) / (2 : ℝ) ^ s))

/-- `ψ̃_I = ρ_I * η_s`. -/
def expPsi (η : ℝ → ℝ) (b : ℝ) (s v : ℤ) (x : ℝ) : ℝ := ∫ y, expInt η b s v x y

theorem etaC_nonneg (hη : IsEtaCut 𝔭 η) : 0 ≤ 𝔭.C := by
  by_contra hC
  push Not at hC
  have h0 := hη.2.2.2.1 0
  have h00 := hη.2.1 0
  have : 𝔭.C * jb 0 ^ (-(𝔭.N : ℝ)) < 0 :=
    mul_neg_of_neg_of_pos hC (Real.rpow_pos_of_pos (jb_pos 0) _)
  linarith

theorem expRho_nonneg (b : ℝ) (s v : ℤ) (y : ℝ) : 0 ≤ expRho b s v y :=
  (Real.rpow_pos_of_pos (jb_pos _) _).le

theorem expInt_nonneg (hη : IsEtaCut 𝔭 η) (b : ℝ) (s v : ℤ) (x y : ℝ) : 0 ≤ expInt η b s v x y :=
  mul_nonneg (expRho_nonneg b s v y) (mul_nonneg (zpow_pos (by norm_num) _).le (hη.2.1 _))

theorem expPsi_nonneg (hη : IsEtaCut 𝔭 η) (b : ℝ) (s v : ℤ) (x : ℝ) : 0 ≤ expPsi η b s v x :=
  integral_nonneg fun y => expInt_nonneg hη b s v x y

/-- Pointwise upper bound of the integrand. -/
theorem expInt_le (hη : IsEtaCut 𝔭 η) {b : ℝ} (hb : 0 ≤ b) (s v : ℤ) (x y : ℝ) :
    expInt η b s v x y ≤ 𝔭.C * ((2 : ℝ) ^ (-s) * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b)) *
      (1 + |y - x| / (2 : ℝ) ^ s) ^ (-((𝔭.N : ℝ) - b)) := by
  have hl : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  have hl' : (0 : ℝ) < (2 : ℝ) ^ (-s) := zpow_pos (by norm_num) _
  have hCn := etaC_nonneg hη
  set A := jb ((y - dyCentre s v) / (2 : ℝ) ^ s) with hA
  set B := jb ((x - y) / (2 : ℝ) ^ s) with hB
  set X := jb ((x - dyCentre s v) / (2 : ℝ) ^ s) with hX
  have hA0 : 0 < A := jb_pos _
  have hB0 : 0 < B := jb_pos _
  have hX0 : 0 < X := jb_pos _
  have h1 : X ≤ B * A := by
    have := jb_add_le ((x - y) / (2 : ℝ) ^ s) ((y - dyCentre s v) / (2 : ℝ) ^ s)
    have e : (x - y) / (2 : ℝ) ^ s + (y - dyCentre s v) / (2 : ℝ) ^ s = (x - dyCentre s v) / (2 : ℝ) ^ s := by ring
    rw [e] at this; exact this
  have h2 : A ^ (-b) ≤ X ^ (-b) * B ^ b := by
    have h3 : X / B ≤ A := by rw [div_le_iff₀ hB0]; linarith [mul_comm A B]
    have := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < X / B) h3 (by linarith : -b ≤ 0)
    calc A ^ (-b) ≤ (X / B) ^ (-b) := this
      _ = X ^ (-b) * B ^ b := by
        rw [Real.div_rpow hX0.le hB0.le, Real.rpow_neg hB0.le, div_inv_eq_mul]
  have h4 : η ((x - y) / (2 : ℝ) ^ s) ≤ 𝔭.C * B ^ (-(𝔭.N : ℝ)) := hη.2.2.2.1 _
  have hBe : B = 1 + |y - x| / (2 : ℝ) ^ s := by
    rw [hB]; unfold jb; rw [abs_div, abs_of_pos hl, abs_sub_comm]
  have h5 : B ^ b * B ^ (-(𝔭.N : ℝ)) = B ^ (-((𝔭.N : ℝ) - b)) := by
    rw [← Real.rpow_add hB0]; congr 1; ring
  unfold expInt expRho
  calc A ^ (-b) * ((2 : ℝ) ^ (-s) * η ((x - y) / (2 : ℝ) ^ s))
      ≤ (X ^ (-b) * B ^ b) * ((2 : ℝ) ^ (-s) * (𝔭.C * B ^ (-(𝔭.N : ℝ)))) := by
        apply mul_le_mul h2 (mul_le_mul_of_nonneg_left h4 hl'.le) (mul_nonneg hl'.le (hη.2.1 _))
        positivity
    _ = 𝔭.C * ((2 : ℝ) ^ (-s) * X ^ (-b)) * (B ^ b * B ^ (-(𝔭.N : ℝ))) := by ring
    _ = _ := by rw [h5, hBe]

theorem integrable_expRho {b : ℝ} (hb : 1 < b) (s v : ℤ) : Integrable (expRho b s v) :=
  integrable_jb_rpow (c := dyCentre s v) (zpow_pos (by norm_num) _) hb

/-- The upper bound `ψ̃_I(x) ≤ 𝔭.C · 2/(N - b - 1) · ⟨(x - c_I)/|I|⟩^{-b}`. -/
theorem expPsi_le (hη : IsEtaCut 𝔭 η) {b : ℝ} (hb : 0 ≤ b) (hbN : b + 1 < 𝔭.N) (s v : ℤ) (x : ℝ) :
    expPsi η b s v x ≤ 𝔭.C * (2 / ((𝔭.N : ℝ) - b - 1)) * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b) := by
  have hl : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  have hp : 1 < (𝔭.N : ℝ) - b := by linarith
  have hint := (integrable_one_add_abs_sub_div_rpow hp x hl).const_mul
    (𝔭.C * ((2 : ℝ) ^ (-s) * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b)))
  unfold expPsi
  refine (integral_mono_of_nonneg (Eventually.of_forall fun y => expInt_nonneg hη b s v x y) hint
    (Eventually.of_forall fun y => ?_)).trans (le_of_eq ?_)
  · have := expInt_le hη hb s v x y
    simpa [neg_sub] using this
  · rw [integral_const_mul]
    have e1 := integral_one_add_abs_sub_div_rpow hp x hl
    simp only [neg_sub] at e1 ⊢
    rw [e1]
    have hq : (2 : ℝ) ^ (-s) * (2 : ℝ) ^ s = 1 := by rw [← zpow_add₀ (by norm_num)]; simp
    have hp0 : (𝔭.N : ℝ) - b - 1 ≠ 0 := by linarith
    calc 𝔭.C * ((2 : ℝ) ^ (-s) * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b)) * (2 * (2 : ℝ) ^ s / ((𝔭.N : ℝ) - b - 1))
        = 𝔭.C * (2 / ((𝔭.N : ℝ) - b - 1)) * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b) *
          ((2 : ℝ) ^ (-s) * (2 : ℝ) ^ s) := by field_simp
      _ = _ := by rw [hq, mul_one]

theorem continuous_jb : Continuous jb := by
  unfold jb; exact continuous_const.add continuous_abs

theorem continuous_expRho (b : ℝ) (s v : ℤ) : Continuous (expRho b s v) := by
  unfold expRho
  refine Continuous.rpow_const ?_ (fun y => Or.inl (jb_pos _).ne')
  exact continuous_jb.comp ((continuous_id.sub continuous_const).div_const _)

theorem expRho_le_one {b : ℝ} (hb : 0 ≤ b) (s v : ℤ) (y : ℝ) : expRho b s v y ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (one_le_jb _) (by linarith)

theorem integrable_expInt (hη : IsEtaCut 𝔭 η) (hN : 2 ≤ 𝔭.N) {b : ℝ} (hb : 0 ≤ b) (s v : ℤ) (x : ℝ) :
    Integrable (fun y => expInt η b s v x y) := by
  have h1 := (integrable_eta_scaled hη hN s).comp_sub_left x
  have := h1.bdd_mul (c := 1) (continuous_expRho b s v).aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (expRho_nonneg b s v y)]; exact expRho_le_one hb s v y)
  exact this

/-- Pointwise lower bound of the integrand on the window `|y - x| ≤ |I|/2`. -/
theorem expInt_ge (hη : IsEtaCut 𝔭 η) (hC : 0 < 𝔭.C) {b : ℝ} (hb : 0 ≤ b) (s v : ℤ) (x y : ℝ)
    (hy : |y - x| ≤ (2 : ℝ) ^ s / 2) :
    (cutK 𝔭)⁻¹ * (((3 : ℝ) / 2) ^ (-b) * ((2 : ℝ) ^ (-s) * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b))) ≤
      expInt η b s v x y := by
  have hl : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  have hl' : (0 : ℝ) < (2 : ℝ) ^ (-s) := zpow_pos (by norm_num) _
  have h1 : |(y - dyCentre s v) / (2 : ℝ) ^ s - (x - dyCentre s v) / (2 : ℝ) ^ s| ≤ 1 / 2 := by
    have e : (y - dyCentre s v) / (2 : ℝ) ^ s - (x - dyCentre s v) / (2 : ℝ) ^ s = (y - x) / (2 : ℝ) ^ s := by
      field_simp; ring
    rw [e, abs_div, abs_of_pos hl, div_le_iff₀ hl]; linarith
  have h2 := jb_le_three_halves_mul h1
  have hX0 : 0 < jb ((x - dyCentre s v) / (2 : ℝ) ^ s) := jb_pos _
  have h3 : ((3 : ℝ) / 2) ^ (-b) * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b) ≤
      jb ((y - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b) := by
    calc ((3 : ℝ) / 2) ^ (-b) * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b)
        = (3 / 2 * jb ((x - dyCentre s v) / (2 : ℝ) ^ s)) ^ (-b) := (Real.mul_rpow (by norm_num) hX0.le).symm
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos (jb_pos _) h2 (by linarith)
  have h4 : |0 - (x - y) / (2 : ℝ) ^ s| ≤ 1 / 2 := by
    rw [zero_sub, abs_neg, abs_div, abs_of_pos hl, div_le_iff₀ hl, abs_sub_comm]; linarith
  have h5 := le_eta_pt hη hC h4
  have h6 : jb (0 : ℝ) = 1 := by unfold jb; simp
  rw [h6, Real.one_rpow, mul_one] at h5
  unfold expInt expRho
  calc (cutK 𝔭)⁻¹ * (((3 : ℝ) / 2) ^ (-b) * ((2 : ℝ) ^ (-s) * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b)))
      = (((3 : ℝ) / 2) ^ (-b) * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b)) * ((2 : ℝ) ^ (-s) * (cutK 𝔭)⁻¹) := by
        ring
    _ ≤ jb ((y - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b) * ((2 : ℝ) ^ (-s) * η ((x - y) / (2 : ℝ) ^ s)) := by
        apply mul_le_mul h3 (mul_le_mul_of_nonneg_left h5 hl'.le)
        · exact mul_nonneg hl'.le (inv_nonneg.2 (cutK_pos hC).le)
        · exact (Real.rpow_pos_of_pos (jb_pos _) _).le

/-- The lower bound `ψ̃_I(x) ≥ K⁻¹ (3/2)^{-b} ⟨(x - c_I)/|I|⟩^{-b}`. -/
theorem le_expPsi (hη : IsEtaCut 𝔭 η) (hC : 0 < 𝔭.C) (hN : 2 ≤ 𝔭.N) {b : ℝ} (hb : 0 ≤ b) (s v : ℤ) (x : ℝ) :
    (cutK 𝔭)⁻¹ * ((3 / 2 : ℝ) ^ (-b)) * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b) ≤ expPsi η b s v x := by
  have hl : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  have hq : (2 : ℝ) ^ (-s) * (2 : ℝ) ^ s = 1 := by rw [← zpow_add₀ (by norm_num)]; simp
  have hint := integrable_expInt hη hN hb s v x
  set K : ℝ := (cutK 𝔭)⁻¹ * (((3 : ℝ) / 2) ^ (-b) * ((2 : ℝ) ^ (-s) * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b))) with hK
  have h1 : ∫ y in Set.Icc (x - (2 : ℝ) ^ s / 2) (x + (2 : ℝ) ^ s / 2), expInt η b s v x y ≤ expPsi η b s v x :=
    setIntegral_le_integral hint (Eventually.of_forall fun y => expInt_nonneg hη b s v x y)
  have h2 : ∫ y in Set.Icc (x - (2 : ℝ) ^ s / 2) (x + (2 : ℝ) ^ s / 2), K ≤
      ∫ y in Set.Icc (x - (2 : ℝ) ^ s / 2) (x + (2 : ℝ) ^ s / 2), expInt η b s v x y := by
    refine setIntegral_mono_on (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
      hint.integrableOn measurableSet_Icc fun y hy => expInt_ge hη hC hb s v x y ?_
    rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
  have h3 : ∫ y in Set.Icc (x - (2 : ℝ) ^ s / 2) (x + (2 : ℝ) ^ s / 2), K = K * (2 : ℝ) ^ s := by
    rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring_nf
  have h4 : K * (2 : ℝ) ^ s = (cutK 𝔭)⁻¹ * ((3 / 2 : ℝ) ^ (-b)) * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b) := by
    rw [hK]
    calc (cutK 𝔭)⁻¹ * (((3 : ℝ) / 2) ^ (-b) * ((2 : ℝ) ^ (-s) * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b))) * (2 : ℝ) ^ s
        = (cutK 𝔭)⁻¹ * ((3 / 2 : ℝ) ^ (-b)) * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b) *
          ((2 : ℝ) ^ (-s) * (2 : ℝ) ^ s) := by ring
      _ = _ := by rw [hq, mul_one]
  rw [← h4, ← h3]
  exact h2.trans h1


theorem continuous_expPsi (hη : IsEtaCut 𝔭 η) {b : ℝ} (hb : 1 < b) (s v : ℤ) : Continuous (expPsi η b s v) := by
  have hCn := etaC_nonneg hη
  have hηs : Continuous (fun x : ℝ => (2 : ℝ) ^ (-s) * η (x / (2 : ℝ) ^ s)) :=
    continuous_const.mul (hη.1.comp (continuous_id.div_const _))
  have hbdd : BddAbove (Set.range fun x : ℝ => ‖(2 : ℝ) ^ (-s) * η (x / (2 : ℝ) ^ s)‖) := by
    refine ⟨(2 : ℝ) ^ (-s) * 𝔭.C, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hl' : (0 : ℝ) < (2 : ℝ) ^ (-s) := zpow_pos (by norm_num) _
    simp only
    rw [Real.norm_of_nonneg (mul_nonneg hl'.le (hη.2.1 _))]
    refine mul_le_mul_of_nonneg_left ((hη.2.2.2.1 _).trans ?_) hl'.le
    have : jb (x / (2 : ℝ) ^ s) ^ (-(𝔭.N : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (one_le_jb _) (by simp)
    nlinarith
  have := BddAbove.continuous_convolution_right_of_integrable (L := ContinuousLinearMap.mul ℝ ℝ)
    (μ := volume) hbdd (integrable_expRho hb s v) hηs
  refine this.congr fun x => ?_
  rw [convolution_def]
  rfl

/-- `𝓕 ψ̃_I` vanishes for `|ξ| > δ/|I|`. -/
theorem fourier_expPsi (hη : IsEtaCut 𝔭 η) (hN : 2 ≤ 𝔭.N) {b : ℝ} (hb : 1 < b) (s v : ℤ) (ξ : ℝ)
    (hξ : 𝔭.δ * (2 : ℝ) ^ (-s) < |ξ|) : 𝓕 (fun x => (expPsi η b s v x : ℂ)) ξ = 0 := by
  have hL : (0 : ℝ) < (2 : ℝ) ^ s := zpow_pos (by norm_num) _
  set f₁ : ℝ → ℂ := fun y => (expRho b s v y : ℂ) with hf₁
  set f₂ : ℝ → ℂ := fun x => (((2 : ℝ) ^ (-s) * η (x / (2 : ℝ) ^ s) : ℝ) : ℂ) with hf₂
  have h1 : Integrable f₁ := (integrable_expRho hb s v).ofReal
  have h2 : Integrable f₂ := (integrable_eta_scaled hη hN s).ofReal
  have hconv : (fun x => (expPsi η b s v x : ℂ)) = f₁ ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] f₂ := by
    funext x
    rw [convolution_def]
    simp only [ContinuousLinearMap.mul_apply', hf₁, hf₂]
    have : ∀ y, ((expRho b s v y : ℝ) : ℂ) * ((((2 : ℝ) ^ (-s) * η ((x - y) / (2 : ℝ) ^ s) : ℝ)) : ℂ) =
        ((expInt η b s v x y : ℝ) : ℂ) := by
      intro y; unfold expInt; push_cast; ring
    simp_rw [this]
    unfold expPsi
    exact (integral_ofReal (𝕜 := ℂ)).symm
  rw [hconv, Real.fourier_mul_convolution_eq h1 h2, hf₂, fourier_eta_scaled]
  have : 𝓕 (fun x : ℝ => (η x : ℂ)) ((2 : ℝ) ^ s * ξ) = 0 := by
    refine hη.2.2.2.2.2 _ ?_
    rw [abs_mul, abs_of_pos hL]
    have : 𝔭.δ = 𝔭.δ * ((2 : ℝ) ^ (-s) * (2 : ℝ) ^ s) := by
      rw [← zpow_add₀ (by norm_num)]; simp
    calc 𝔭.δ = 𝔭.δ * (2 : ℝ) ^ (-s) * (2 : ℝ) ^ s := by rw [mul_assoc]; exact this
      _ < |ξ| * (2 : ℝ) ^ s := by gcongr
      _ = _ := mul_comm _ _
  rw [this, mul_zero]

/-- The lower constant of the tree cutoff: `K⁻¹ (3/2)^{-b} (N - b - 1)/2` (`K = cutK 𝔭`). -/
def psiLow (𝔭 : Params) (b : ℝ) : ℝ :=
  (cutK 𝔭)⁻¹ * ((3 / 2 : ℝ) ^ (-b)) * (((𝔭.N : ℝ) - b - 1) / 2)

/-- **A lower-bounded cutoff of the tree class**: for `IsEtaCut 𝔭 η` and `b = 𝔭.tree.N` there is `ψ ∈ Ψ_I(𝔭.tree)` with
`ψ ≥ psiLow 𝔭 b · ⟨(x - c_I)/|I|⟩^{-b}`. -/
theorem exists_psiTilde (h𝔭 : 𝔭.Admissible) (hη : IsEtaCut 𝔭 η) (s v : ℤ) :
    ∃ ψ : ℝ → ℂ, InPsi 𝔭.tree s v ψ ∧ ∀ x, psiLow 𝔭 (𝔭.tree.N : ℝ) *
      jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-(𝔭.tree.N : ℝ)) ≤ ‖ψ x‖ := by
  obtain ⟨-, hNf, -, hδp, -, -, -, hC1⟩ := h𝔭
  have hC : 0 < 𝔭.C := by linarith
  have hN400 : 400 ≤ 𝔭.N := le_trans classFloor_ge hNf
  have hN2 : 2 ≤ 𝔭.N := by omega
  set b : ℝ := (𝔭.tree.N : ℝ) with hb
  have hbN : b ≤ 𝔭.N / 8 := by
    rw [hb, Params.tree_N]
    have : (𝔭.N / 8 : ℕ) * 8 ≤ 𝔭.N := Nat.div_mul_le_self _ _
    have h' : ((𝔭.N / 8 : ℕ) : ℝ) * 8 ≤ 𝔭.N := by exact_mod_cast this
    linarith
  have hb50 : (50 : ℝ) ≤ b := by
    rw [hb, Params.tree_N]
    have : 50 ≤ 𝔭.N / 8 := by omega
    exact_mod_cast this
  have hN4 : (400 : ℝ) ≤ 𝔭.N := by exact_mod_cast hN400
  have hNb : (0 : ℝ) < (𝔭.N : ℝ) - b - 1 := by linarith
  set κ : ℝ := ((𝔭.N : ℝ) - b - 1) / 2 with hκ
  have hκ0 : 0 < κ := by positivity
  refine ⟨fun x => ((κ * expPsi η b s v x : ℝ) : ℂ), ⟨?_, fun x => ?_, fun ξ hξ => ?_⟩, fun x => ?_⟩
  · exact Complex.continuous_ofReal.comp (continuous_const.mul (continuous_expPsi hη (by linarith) s v))
  · show ‖((κ * expPsi η b s v x : ℝ) : ℂ)‖ ≤ 𝔭.C * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b)
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hκ0.le (expPsi_nonneg hη b s v x))]
    have h1 := expPsi_le hη (b := b) (by linarith) (by linarith) s v x
    calc κ * expPsi η b s v x ≤ κ * (𝔭.C * (2 / ((𝔭.N : ℝ) - b - 1)) * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b)) :=
          mul_le_mul_of_nonneg_left h1 hκ0.le
      _ = _ := by
          rw [hκ]; field_simp
  · have e : (fun x => ((κ * expPsi η b s v x : ℝ) : ℂ)) = fun x => ((κ : ℝ) : ℂ) * (expPsi η b s v x : ℂ) := by
      funext x; push_cast; rfl
    show 𝓕 (fun x => ((κ * expPsi η b s v x : ℝ) : ℂ)) ξ = 0
    rw [e, fourier_const_mul', fourier_expPsi hη hN2 (by linarith) s v ξ hξ, mul_zero]
  · show psiLow 𝔭 b * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b) ≤ ‖((κ * expPsi η b s v x : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hκ0.le (expPsi_nonneg hη b s v x))]
    have h1 := le_expPsi hη hC hN2 (b := b) (by linarith) s v x
    calc psiLow 𝔭 b * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b)
        = κ * ((cutK 𝔭)⁻¹ * ((3 / 2 : ℝ) ^ (-b)) * jb ((x - dyCentre s v) / (2 : ℝ) ^ s) ^ (-b)) := by
          unfold psiLow; rw [hκ]; ring
      _ ≤ κ * expPsi η b s v x := mul_le_mul_of_nonneg_left h1 hκ0.le

end Exotic

end PrimeBHT.TimeFrequency.X2
