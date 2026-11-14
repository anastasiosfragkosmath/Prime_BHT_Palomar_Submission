module

public import PrimeBHT.TransferenceAssembly.Anchor
public import PrimeBHT.TransferenceAssembly.TwistedForm
public import PrimeBHT.TransferenceAssembly.ExactChart
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import PrimeBHT.Frozen.YNorm
public import PrimeBHT.Frozen.TensorFun
public import PrimeBHT.Frozen.TensorFourier
public import PrimeBHT.Frozen.MultiplierForm

/-!
# The X2 anchor as a `Prop` (not proved)

`X2Statement` is the statement of the frozen theorem `PrimeBHT.Statements.t_finiteBV` (ruling R11),
copied verbatim over the frozen definitions `PrimeBHT.Statements.{yNorm, tensorFun, tensorFourier,
multiplierForm}` (checked equal to the frozen theorem's type by `scripts/interface_check.sh`).
`X2Core` is the same statement without the integrability conjunct, over this project's
`tensorFun`, `tensorFourier`, `multiplierForm` (`Anchor.lean`) and `Lift.yNorm`, which have the same
bodies as the frozen ones (`X2Statement.core`). Results using it are named `…_of_x2`.
-/

@[expose] public section

namespace PrimeBHT.TransferenceAssembly

open MeasureTheory PrimeBHT.Lift
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate ContDiff

/-- The statement of `t:finiteBV` (X2), all-multi-index form, without the integrability conjunct,
over the project's local copies of the definitions (`X2Statement.core`). -/
def X2Core : Prop :=
  ∀ u : ℝ, 1 < u → ∀ A : ℕ → ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℕ) [NeZero P]
      (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
      (m : ℝ → ℂ), ContDiffOn ℝ ∞ m {0}ᶜ →
      (∀ j : ℕ, ∀ t : ℝ, t ≠ 0 → |t| ^ j * ‖iteratedDeriv j m t‖ ≤ A j) →
      ∀ CT : ℝ,
      (∀ F G H : ZMod P → ℂ, ‖T F G H‖ ≤ CT * yNorm 2 F * yNorm 2 G * yNorm u H) →
      ∀ f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ),
        ‖multiplierForm m T f₁ f₂ f₃‖ₑ ≤
          ENNReal.ofReal (C * CT) *
            eLpNorm (fun x : ℝ => yNorm 2 (tensorFun f₁ x)) 2 volume *
            eLpNorm (fun x : ℝ => yNorm 2 (tensorFun f₂ x)) 2 volume *
            eLpNorm (fun x : ℝ => yNorm u (tensorFun f₃ x)) ⊤ volume

/-- **The statement of the frozen `t_finiteBV`** (ruling R11), as a `Prop`, written over the frozen
definitions. It is textually the type of `PrimeBHT.Statements.t_finiteBV`. -/
def X2Statement : Prop :=
  ∀ u : ℝ, 1 < u → ∀ A : ℕ → ℝ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : ℕ) [NeZero P] (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
      (m : ℝ → ℂ), ContDiffOn ℝ ∞ m {0}ᶜ →
      (∀ j : ℕ, ∀ t : ℝ, t ≠ 0 → |t| ^ j * ‖iteratedDeriv j m t‖ ≤ A j) →
      ∀ CT : ℝ, (∀ F G H : ZMod P → ℂ, ‖T F G H‖ ≤ CT * PrimeBHT.Statements.yNorm 2 F *
          PrimeBHT.Statements.yNorm 2 G * PrimeBHT.Statements.yNorm u H) →
      ∀ f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ),
        Integrable (fun ξ : ℝ × ℝ => m (ξ.2 - ξ.1) *
          T (PrimeBHT.Statements.tensorFourier f₁ ξ.1) (PrimeBHT.Statements.tensorFourier f₂ ξ.2)
            (PrimeBHT.Statements.tensorFourier f₃ (ξ.1 + ξ.2))) volume ∧
        ‖PrimeBHT.Statements.multiplierForm m T f₁ f₂ f₃‖ₑ ≤ ENNReal.ofReal (C * CT) *
          eLpNorm (fun x : ℝ => PrimeBHT.Statements.yNorm 2 (PrimeBHT.Statements.tensorFun f₁ x)) 2 volume *
          eLpNorm (fun x : ℝ => PrimeBHT.Statements.yNorm 2 (PrimeBHT.Statements.tensorFun f₂ x)) 2 volume *
          eLpNorm (fun x : ℝ => PrimeBHT.Statements.yNorm u (PrimeBHT.Statements.tensorFun f₃ x)) ⊤ volume

/-- The frozen statement implies the core statement: the local definitions have the same bodies as the
frozen ones (`rfl`), and the integrability conjunct is dropped. -/
theorem X2Statement.core (h : X2Statement) : X2Core := by
  intro u hu A
  obtain ⟨C, hC0, hC⟩ := h u hu A
  refine ⟨C, hC0, ?_⟩
  intro P _ T m hm hA CT hT f₁ f₂ f₃
  exact (hC P T m hm hA CT hT f₁ f₂ f₃).2

/-- `PeriodicBlock.l2 = Lift.yNorm 2` on `Y_N`. -/
theorem l2_eq_yNorm_two {N : ℕ} [NeZero N] (F : ZMod N → ℂ) :
    PrimeBHT.PeriodicBlock.l2 F = yNorm 2 F := by
  unfold PrimeBHT.PeriodicBlock.l2 yNorm
  rw [Real.sqrt_eq_rpow, Fintype.expect_eq_sum_div_card, ZMod.card, div_eq_inv_mul]
  norm_num [Real.rpow_two]

/-- The twisted form bound in the shape of the `X2Statement` hypothesis on `T`. -/
theorem norm_twistedFormMap_le_yNorm {N : ℕ} [NeZero N] {p u D : ℝ} (hpu : p.HolderConjugate u)
    (Λ : ZMod N → ℂ)
    (hD : ∀ F G : ZMod N → ℂ, yNorm p (PrimeBHT.PeriodicBlock.bilinAvg Λ F G) ≤
      D * yNorm 2 F * yNorm 2 G) (d v : ZMod N) (F₁ F₂ F₃ : ZMod N → ℂ) :
    ‖twistedFormMap Λ d v F₁ F₂ F₃‖ ≤ D * yNorm 2 F₁ * yNorm 2 F₂ * yNorm u F₃ := by
  have := norm_twistedFormMap_le Λ d v hpu (D := D) (fun F G => by
    rw [l2_eq_yNorm_two, l2_eq_yNorm_two]; exact hD F G) F₁ F₂ F₃
  rwa [l2_eq_yNorm_two, l2_eq_yNorm_two] at this

/-- The frequency shift: the Schwartz function with Fourier transform `ξ ↦ φ̂(ξ + c)`. -/
noncomputable def freqShift (φ : 𝓢(ℝ, ℂ)) (c : ℝ) : 𝓢(ℝ, ℂ) :=
  𝓕⁻ (SchwartzMap.compSubConstCLM ℂ (-c) (𝓕 φ))

theorem fourier_freqShift (φ : 𝓢(ℝ, ℂ)) (c ξ : ℝ) :
    𝓕 (⇑(freqShift φ c)) ξ = 𝓕 (⇑φ) (ξ + c) := by
  rw [← SchwartzMap.fourier_coe, freqShift, FourierInvPair.fourier_fourierInv_eq,
    SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, SchwartzMap.fourier_coe]

theorem tensorFourier_eq_sum_smul {P : ℕ} [NeZero P] (f : ZMod P → 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    tensorFourier f ξ = ∑ A, 𝓕 (⇑(f A)) ξ • fun y : ZMod P => (ZMod.stdAddChar (A * y) : ℂ) := by
  funext y; simp [tensorFourier, Finset.sum_apply]

/-- `Λ_m^Π` as an iterated integral, when `m` is continuous and `f̂_{1,A}`, `f̂_{2,A}` are compactly
supported. -/
theorem multiplierForm_eq_integral_integral {P : ℕ} [NeZero P] {m : ℝ → ℂ} (hm : Continuous m)
    (T : (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ[ℂ] (ZMod P → ℂ) →ₗ⋆[ℂ] ℂ)
    (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) (h₁ : ∀ A, HasCompactSupport (𝓕 (⇑(f₁ A))))
    (h₂ : ∀ A, HasCompactSupport (𝓕 (⇑(f₂ A)))) :
    multiplierForm m T f₁ f₂ f₃ = ∫ ξ₁ : ℝ, ∫ ξ₂ : ℝ, m (ξ₂ - ξ₁) *
      T (tensorFourier f₁ ξ₁) (tensorFourier f₂ ξ₂) (tensorFourier f₃ (ξ₁ + ξ₂)) := by
  have hexp : ∀ ξ : ℝ × ℝ, m (ξ.2 - ξ.1) *
      T (tensorFourier f₁ ξ.1) (tensorFourier f₂ ξ.2) (tensorFourier f₃ (ξ.1 + ξ.2)) =
      ∑ c, ∑ b, ∑ a, 𝓕 (⇑(f₁ a)) ξ.1 * 𝓕 (⇑(f₂ b)) ξ.2 *
        (m (ξ.2 - ξ.1) * conj (𝓕 (⇑(f₃ c)) (ξ.1 + ξ.2)) *
          T (fun y => (ZMod.stdAddChar (a * y) : ℂ)) (fun y => (ZMod.stdAddChar (b * y) : ℂ))
            (fun y => (ZMod.stdAddChar (c * y) : ℂ))) := by
    intro ξ
    simp only [tensorFourier_eq_sum_smul, map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun a _ => ?_
    ring
  have hint : Integrable (fun ξ : ℝ × ℝ => m (ξ.2 - ξ.1) *
      T (tensorFourier f₁ ξ.1) (tensorFourier f₂ ξ.2) (tensorFourier f₃ (ξ.1 + ξ.2)))
      (volume.prod volume) := by
    refine Integrable.congr ?_ (Filter.Eventually.of_forall fun ξ => (hexp ξ).symm)
    refine integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun b _ =>
      integrable_finsetSum _ fun a _ => ?_
    refine integrable_mul_mul_of_hasCompactSupport (h₁ a) (h₂ b) ?_
    refine Continuous.mul (Continuous.mul ((𝓕 (f₁ a)).continuous.comp continuous_fst)
      ((𝓕 (f₂ b)).continuous.comp continuous_snd)) (Continuous.mul (Continuous.mul
        (hm.comp (by fun_prop)) (Complex.continuous_conj.comp ((𝓕 (f₃ c)).continuous.comp
          (by fun_prop)))) continuous_const)
  unfold multiplierForm
  rw [Measure.volume_eq_prod, integral_prod _ hint]

theorem hasCompactSupport_fourier_freqShift {φ : 𝓢(ℝ, ℂ)} (hφ : HasCompactSupport (𝓕 (⇑φ)))
    (c : ℝ) : HasCompactSupport (𝓕 (⇑(freqShift φ c))) := by
  have : 𝓕 (⇑(freqShift φ c)) = 𝓕 (⇑φ) ∘ Homeomorph.addRight c :=
    funext fun ξ => fourier_freqShift φ c ξ
  rw [this]
  exact hφ.comp_homeomorph _

/-- **`e:chart-identification` (N42 step 7): `T = Λ_m^{Π_{B,d,v}}(F_{d,N}, G, H_{d,v,N})`** with
`m(t) = K̂(-t)`, `Π_{B,d,v} = twistedFormMap`, and the tensor coefficients
`F_{d,N}`: `freqShift f_a (d/N)` (Fourier transform `f̂_a(· + d/N)`), `G`: `g_b`,
`H_{d,v,N}`: `freqShift h_c ((d-v)/N)`. -/
theorem tsum_tsum_chartProj_eq_multiplierForm {N : ℕ} [NeZero N] {χ₁ χ₂ χ₃ : ℝ → ℂ}
    (hχ₁ : ContDiff ℝ ∞ χ₁) (hχ₁c : HasCompactSupport χ₁)
    (hχ₂ : ContDiff ℝ ∞ χ₂) (hχ₂c : HasCompactSupport χ₂)
    (hχ₃ : ContDiff ℝ ∞ χ₃) (hχ₃c : HasCompactSupport χ₃)
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ} (hI₁ : ∀ t, χ₁ t ≠ 0 → t ∈ Set.Icc a₁ b₁)
    (hI₂ : ∀ t, χ₂ t ≠ 0 → t ∈ Set.Icc a₂ b₂) (hI₃ : ∀ t, χ₃ t ≠ 0 → t ∈ Set.Icc a₃ b₃)
    {w : ℤ → ℂ} (hw : Function.Periodic w (N : ℤ))
    (K : 𝓢(ℝ, ℂ)) {δ : ℝ} (hK : ∀ t, δ < |t| → 𝓕 (K : ℝ → ℂ) t = 0)
    (hNδ : N * δ ≤ 1 / 1000) {d v : ℤ}
    (hd : ∀ d' : ℤ, ∀ s₁ ∈ Set.Icc a₁ b₁, ∀ s₂ ∈ Set.Icc a₂ b₂, |s₁ - s₂ - d'| ≤ 1 / 1000 → d' = d)
    (hv : ∀ v' : ℤ, ∀ s₁ ∈ Set.Icc a₁ b₁, ∀ s₂ ∈ Set.Icc a₂ b₂, ∀ s₃ ∈ Set.Icc a₃ b₃,
      (v' : ℝ) = s₁ + s₂ - s₃ → v' = v)
    (f g h : ℤ →₀ ℂ) :
    ∑' x : ℤ, ∑' n : ℤ, K n * w n * chartProj χ₁ N f (x - n) * chartProj χ₂ N g (x + n) *
        conj (chartProj χ₃ N h x) =
      multiplierForm (fun t => 𝓕 (K : ℝ → ℂ) (-t))
        (twistedFormMap (fun r : ZMod N => w (r.val : ℤ)) (d : ZMod N) (v : ZMod N))
        (fun a => freqShift (chartPiece hχ₁ hχ₁c f a) (d / N))
        (fun b => chartPiece hχ₂ hχ₂c g b)
        (fun c => freqShift (chartPiece hχ₃ hχ₃c h c) ((d - v) / N)) := by
  rw [multiplierForm_eq_integral_integral ((𝓕 K).continuous.comp continuous_neg) _ _ _ _
    (fun a => hasCompactSupport_fourier_freqShift
      (hasCompactSupport_fourier_chartPiece hχ₁ hχ₁c f a) _)
    (fun b => hasCompactSupport_fourier_chartPiece hχ₂ hχ₂c g b),
    tsum_tsum_chartProj_eq_integral_multiplier hχ₁ hχ₁c hχ₂ hχ₂c hχ₃ hχ₃c hI₁ hI₂ hI₃ hw K hK
      hNδ hd hv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ₁ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ₂ => ?_)
  have hF : ∀ (φ : ZMod N → 𝓢(ℝ, ℂ)) (c ξ : ℝ),
      tensorFourier (fun a => freqShift (φ a) c) ξ =
        fun y => ∑ a, 𝓕 (⇑(φ a)) (ξ + c) * charN a y := by
    intro φ c ξ; funext y
    simp only [tensorFourier, charN]
    exact Finset.sum_congr rfl fun a _ => by rw [fourier_freqShift]
  have hG : ∀ (φ : ZMod N → 𝓢(ℝ, ℂ)) (ξ : ℝ),
      tensorFourier φ ξ = fun y => ∑ a, 𝓕 (⇑(φ a)) ξ * charN a y := fun _ _ => rfl
  simp only []
  rw [twistedFormMap_apply, hF, hF, hG, add_assoc ξ₁ ξ₂]

/-- The frequency shift is a modulation: `freqShift φ c x = e(-c x) φ(x)`. Hence
`|F_{d,N}(x;y)| = |F(x;y)|` coefficientwise up to the common unimodular factor. -/
theorem freqShift_apply (φ : 𝓢(ℝ, ℂ)) (c x : ℝ) :
    freqShift φ c x = PrimeCarleson.e (-(c * x)) * φ x := by
  have hinv : ∀ ψ : 𝓢(ℝ, ℂ), (𝓕⁻ ψ) x = ∫ ξ, ψ ξ * PrimeCarleson.e (x * ξ) := by
    intro ψ
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [smul_eq_mul, PrimeCarleson.e, RCLike.inner_apply, conj_trivial]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  have hφ : φ x = ∫ ξ, (𝓕 φ) ξ * PrimeCarleson.e (x * ξ) := by
    rw [← hinv, FourierPair.fourierInv_fourier_eq]
  rw [freqShift, hinv, hφ, ← integral_const_mul]
  conv_rhs => rw [← integral_add_right_eq_self _ c]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
  have : x * (ξ + c) = c * x + x * ξ := by ring
  rw [this, e_add']
  have h0 : PrimeCarleson.e (-(c * x)) * PrimeCarleson.e (c * x) = 1 := by
    rw [← e_add', show -(c * x) + c * x = 0 by ring]
    simp [PrimeCarleson.e]
  linear_combination (-(𝓕 φ) (ξ + c) * PrimeCarleson.e (x * ξ)) * h0

/-- Frequency-shifting all coefficients does not change the fibre norms `‖F(x;·)‖_{L^s(Y_P)}`,
hence not the mixed norms of `F_{d,N}`, `H_{d,v,N}`. -/
theorem yNorm_tensorFun_freqShift {P : ℕ} [NeZero P] (s : ℝ) (φ : ZMod P → 𝓢(ℝ, ℂ)) (c x : ℝ) :
    yNorm s (tensorFun (fun a => freqShift (φ a) c) x) = yNorm s (tensorFun φ x) := by
  have : tensorFun (fun a => freqShift (φ a) c) x =
      fun y => PrimeCarleson.e (-(c * x)) * tensorFun φ x y := by
    funext y
    simp only [tensorFun, freqShift_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [this]
  unfold yNorm
  simp only [norm_mul, PrimeCarleson.Proof.Goal0.norm_e, one_mul]

end PrimeBHT.TransferenceAssembly
