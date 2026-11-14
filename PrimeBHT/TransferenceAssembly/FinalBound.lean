module

public import PrimeBHT.TransferenceAssembly.ChartLiftBounds

/-!
# Towards the N42 bound `…_of_x2` (partial): the X2 norms of the chart tensors are lift norms
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff ComplexConjugate ENNReal

namespace PrimeBHT.TransferenceAssembly

variable {N : ℕ} [NeZero N] {χ : ℝ → ℂ}

/-- The fibre norms of the (frequency-shifted) chart tensor are those of the lift. -/
theorem yNorm_tensorFun_freqShift_chartPiece (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (h : ℤ →₀ ℂ) (s c x : ℝ) :
    Lift.yNorm s (tensorFun (fun a => freqShift (chartPiece (N := N) hχ hχc h a) c) x) =
      Lift.yNorm s (Lift.lift (chartKernel χ) N h x) := by
  rw [yNorm_tensorFun_freqShift]
  congr 1
  funext y
  exact tensorFun_chartPiece_eq_lift hχ hχc h x y

theorem yNorm_tensorFun_chartPiece (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (h : ℤ →₀ ℂ) (s x : ℝ) :
    Lift.yNorm s (tensorFun (chartPiece (N := N) hχ hχc h) x) =
      Lift.yNorm s (Lift.lift (chartKernel χ) N h x) := by
  congr 1
  funext y
  exact tensorFun_chartPiece_eq_lift hχ hχc h x y

/-- **N42 bound for one chart triple, conditional on X2, lift-norm form.** For every `u > 1` and
symbol bounds `A` there is `C` such that, whenever `m = K̂(-·)` satisfies the all-order bounds
`A_j` and `‖A_B(F,G)‖_{L^p} ≤ D ‖F‖₂ ‖G‖₂` (`1/p + 1/u = 1`),
`|T| ≤ C D ‖F‖_{L²_x L²_y} ‖G‖_{L²_x L²_y} ‖H‖_{L^∞_x L^u_y}` for the lifts `F, G, H` of `f, g, h`. -/
theorem exists_norm_tsum_tsum_chartProj_le_of_x2 (hx2 : X2Statement) {p u : ℝ}
    (hpu : p.HolderConjugate u) (A : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] {χ₁ χ₂ χ₃ : ℝ → ℂ}
      (_hχ₁ : ContDiff ℝ ∞ χ₁) (_hχ₁c : HasCompactSupport χ₁)
      (_hχ₂ : ContDiff ℝ ∞ χ₂) (_hχ₂c : HasCompactSupport χ₂)
      (_hχ₃ : ContDiff ℝ ∞ χ₃) (_hχ₃c : HasCompactSupport χ₃)
      {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ} (_hI₁ : ∀ t, χ₁ t ≠ 0 → t ∈ Set.Icc a₁ b₁)
      (_hI₂ : ∀ t, χ₂ t ≠ 0 → t ∈ Set.Icc a₂ b₂) (_hI₃ : ∀ t, χ₃ t ≠ 0 → t ∈ Set.Icc a₃ b₃)
      {w : ℤ → ℂ} (_hw : Function.Periodic w (N : ℤ))
      (K : 𝓢(ℝ, ℂ)) {δ : ℝ} (_hK : ∀ t, δ < |t| → 𝓕 (K : ℝ → ℂ) t = 0)
      (_hNδ : N * δ ≤ 1 / 1000) {d v : ℤ}
      (_hd : ∀ d' : ℤ, ∀ s₁ ∈ Set.Icc a₁ b₁, ∀ s₂ ∈ Set.Icc a₂ b₂,
        |s₁ - s₂ - d'| ≤ 1 / 1000 → d' = d)
      (_hv : ∀ v' : ℤ, ∀ s₁ ∈ Set.Icc a₁ b₁, ∀ s₂ ∈ Set.Icc a₂ b₂, ∀ s₃ ∈ Set.Icc a₃ b₃,
        (v' : ℝ) = s₁ + s₂ - s₃ → v' = v)
      (_hm : ContDiffOn ℝ ∞ (fun t => 𝓕 (K : ℝ → ℂ) (-t)) {0}ᶜ)
      (_hA : ∀ j : ℕ, ∀ t : ℝ, t ≠ 0 →
        |t| ^ j * ‖iteratedDeriv j (fun t => 𝓕 (K : ℝ → ℂ) (-t)) t‖ ≤ A j)
      {D : ℝ} (_hD : ∀ F G : ZMod N → ℂ, Lift.yNorm p
        (PrimeBHT.PeriodicBlock.bilinAvg (fun r : ZMod N => w (r.val : ℤ)) F G) ≤
          D * Lift.yNorm 2 F * Lift.yNorm 2 G)
      (f g h : ℤ →₀ ℂ),
      ‖∑' x : ℤ, ∑' n : ℤ, K n * w n * chartProj χ₁ N f (x - n) * chartProj χ₂ N g (x + n) *
          conj (chartProj χ₃ N h x)‖ₑ ≤
        ENNReal.ofReal (C * D) *
          eLpNorm (fun x : ℝ => Lift.yNorm 2 (Lift.lift (chartKernel χ₁) N f x)) 2 volume *
          eLpNorm (fun x : ℝ => Lift.yNorm 2 (Lift.lift (chartKernel χ₂) N g x)) 2 volume *
          eLpNorm (fun x : ℝ => Lift.yNorm u (Lift.lift (chartKernel χ₃) N h x)) ⊤ volume := by
  obtain ⟨C, hC0, hC⟩ := hx2.core u (Real.holderConjugate_iff.1 hpu.symm).1 A
  refine ⟨C, hC0, ?_⟩
  intro N _ χ₁ χ₂ χ₃ hχ₁ hχ₁c hχ₂ hχ₂c hχ₃ hχ₃c a₁ b₁ a₂ b₂ a₃ b₃ hI₁ hI₂ hI₃ w hw K δ hK hNδ
    d v hd hv hm hA D hD f g h
  rw [tsum_tsum_chartProj_eq_multiplierForm hχ₁ hχ₁c hχ₂ hχ₂c hχ₃ hχ₃c hI₁ hI₂ hI₃ hw K hK hNδ
    hd hv f g h]
  have := hC N (twistedFormMap (fun r : ZMod N => w (r.val : ℤ)) (d : ZMod N) (v : ZMod N))
    _ hm hA D (norm_twistedFormMap_le_yNorm hpu _ hD _ _)
    (fun a => freqShift (chartPiece hχ₁ hχ₁c f a) (d / N)) (fun b => chartPiece hχ₂ hχ₂c g b)
    (fun c => freqShift (chartPiece hχ₃ hχ₃c h c) ((d - v) / N))
  simp only [yNorm_tensorFun_freqShift_chartPiece, yNorm_tensorFun_chartPiece] at this
  exact this

theorem measurable_yNorm_lift_chartKernel (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (s : ℝ) (h : ℤ →₀ ℂ) : Measurable fun x : ℝ => Lift.yNorm s (Lift.lift (chartKernel χ) N h x) := by
  simpa using Lift.measurable_yNorm_lift_rpow (measurable_chartKernel hχ hχc) (P := N) s 1 h

/-- `‖H‖_{L²_x L²_y}` of the chart lift, in `eLpNorm` form, is `≤ C' ‖h‖_{ℓ²}`. -/
theorem eLpNorm_yNorm_lift_two_le (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) {C : ℝ}
    (hC : ∀ t, ∑' j : ℤ, ‖chartKernel χ (t - j)‖ ≤ C) (h : ℤ →₀ ℂ) :
    eLpNorm (fun x : ℝ => Lift.yNorm 2 (Lift.lift (chartKernel χ) N h x)) 2 volume ≤
      ENNReal.ofReal (C ^ (((2 : ℝ) - 1) / 2) * (∫ x : ℝ, ‖chartKernel χ x‖) ^ (2 : ℝ)⁻¹ *
        Lift.lpNorm 2 h) := by
  have hb := Lift.mixedNormR_lift_le (measurable_chartKernel hχ hχc) (integrable_chartKernel hχ hχc)
    (summable_chartKernel_sub hχ hχc) hC (P := N) (p := 2) (by norm_num) h
  rw [eLpNorm_yNorm_two_eq 2 _
    (measurable_yNorm_lift_chartKernel hχ hχc 2 h).aestronglyMeasurable hb.1]
  exact ENNReal.ofReal_le_ofReal hb.2

/-- `‖H‖_{L^∞_x L^u_y}` of the chart lift, in `eLpNorm` form, is `≤ C ‖h‖_{ℓ^∞}`. -/
theorem eLpNorm_yNorm_lift_top_le (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) {C : ℝ}
    (hC : ∀ t, ∑' j : ℤ, ‖chartKernel χ (t - j)‖ ≤ C) {u : ℝ} (hu : 1 ≤ u) (h : ℤ →₀ ℂ) :
    eLpNorm (fun x : ℝ => Lift.yNorm u (Lift.lift (chartKernel χ) N h x)) ⊤ volume ≤
      ENNReal.ofReal (C * Lift.supNorm h) :=
  eLpNorm_yNorm_top_le u _ (measurable_yNorm_lift_chartKernel hχ hχc u h).aestronglyMeasurable
    fun x => (Lift.yNorm_lift_le_yNormInf_le (summable_chartKernel_sub hχ hχc) hC hu h x).1.trans
      (Lift.yNorm_lift_le_yNormInf_le (summable_chartKernel_sub hχ hχc) hC hu h x).2

/-- **N42 bound for one chart triple, conditional on X2, `ℓ²·ℓ²·ℓ^∞` form** (ENNReal). -/
theorem exists_norm_tsum_tsum_chartProj_le_lp_of_x2 (hx2 : X2Statement) {p u : ℝ}
    (hpu : p.HolderConjugate u) (A : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] {χ₁ χ₂ χ₃ : ℝ → ℂ}
      (_hχ₁ : ContDiff ℝ ∞ χ₁) (_hχ₁c : HasCompactSupport χ₁)
      (_hχ₂ : ContDiff ℝ ∞ χ₂) (_hχ₂c : HasCompactSupport χ₂)
      (_hχ₃ : ContDiff ℝ ∞ χ₃) (_hχ₃c : HasCompactSupport χ₃)
      {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ} (_hI₁ : ∀ t, χ₁ t ≠ 0 → t ∈ Set.Icc a₁ b₁)
      (_hI₂ : ∀ t, χ₂ t ≠ 0 → t ∈ Set.Icc a₂ b₂) (_hI₃ : ∀ t, χ₃ t ≠ 0 → t ∈ Set.Icc a₃ b₃)
      {w : ℤ → ℂ} (_hw : Function.Periodic w (N : ℤ))
      (K : 𝓢(ℝ, ℂ)) {δ : ℝ} (_hK : ∀ t, δ < |t| → 𝓕 (K : ℝ → ℂ) t = 0)
      (_hNδ : N * δ ≤ 1 / 1000) {d v : ℤ}
      (_hd : ∀ d' : ℤ, ∀ s₁ ∈ Set.Icc a₁ b₁, ∀ s₂ ∈ Set.Icc a₂ b₂,
        |s₁ - s₂ - d'| ≤ 1 / 1000 → d' = d)
      (_hv : ∀ v' : ℤ, ∀ s₁ ∈ Set.Icc a₁ b₁, ∀ s₂ ∈ Set.Icc a₂ b₂, ∀ s₃ ∈ Set.Icc a₃ b₃,
        (v' : ℝ) = s₁ + s₂ - s₃ → v' = v)
      (_hm : ContDiffOn ℝ ∞ (fun t => 𝓕 (K : ℝ → ℂ) (-t)) {0}ᶜ)
      (_hA : ∀ j : ℕ, ∀ t : ℝ, t ≠ 0 →
        |t| ^ j * ‖iteratedDeriv j (fun t => 𝓕 (K : ℝ → ℂ) (-t)) t‖ ≤ A j)
      {D : ℝ} (_hD : ∀ F G : ZMod N → ℂ, Lift.yNorm p
        (PrimeBHT.PeriodicBlock.bilinAvg (fun r : ZMod N => w (r.val : ℤ)) F G) ≤
          D * Lift.yNorm 2 F * Lift.yNorm 2 G)
      {C₁ C₂ C₃ : ℝ} (_hC₁ : ∀ t, ∑' j : ℤ, ‖chartKernel χ₁ (t - j)‖ ≤ C₁)
      (_hC₂ : ∀ t, ∑' j : ℤ, ‖chartKernel χ₂ (t - j)‖ ≤ C₂)
      (_hC₃ : ∀ t, ∑' j : ℤ, ‖chartKernel χ₃ (t - j)‖ ≤ C₃)
      (f g h : ℤ →₀ ℂ),
      ‖∑' x : ℤ, ∑' n : ℤ, K n * w n * chartProj χ₁ N f (x - n) * chartProj χ₂ N g (x + n) *
          conj (chartProj χ₃ N h x)‖ₑ ≤
        ENNReal.ofReal (C * D) *
          ENNReal.ofReal (C₁ ^ (((2 : ℝ) - 1) / 2) * (∫ x : ℝ, ‖chartKernel χ₁ x‖) ^ (2 : ℝ)⁻¹ *
            Lift.lpNorm 2 f) *
          ENNReal.ofReal (C₂ ^ (((2 : ℝ) - 1) / 2) * (∫ x : ℝ, ‖chartKernel χ₂ x‖) ^ (2 : ℝ)⁻¹ *
            Lift.lpNorm 2 g) *
          ENNReal.ofReal (C₃ * Lift.supNorm h) := by
  obtain ⟨C, hC0, hT⟩ := exists_norm_tsum_tsum_chartProj_le_of_x2 hx2 hpu A
  refine ⟨C, hC0, ?_⟩
  intro N _ χ₁ χ₂ χ₃ hχ₁ hχ₁c hχ₂ hχ₂c hχ₃ hχ₃c a₁ b₁ a₂ b₂ a₃ b₃ hI₁ hI₂ hI₃ w hw K δ hK hNδ
    d v hd hv hm hA D hD C₁ C₂ C₃ hC₁ hC₂ hC₃ f g h
  refine (hT N hχ₁ hχ₁c hχ₂ hχ₂c hχ₃ hχ₃c hI₁ hI₂ hI₃ hw K hK hNδ hd hv hm hA hD f g h).trans ?_
  gcongr
  · exact eLpNorm_yNorm_lift_two_le hχ₁ hχ₁c hC₁ f
  · exact eLpNorm_yNorm_lift_two_le hχ₂ hχ₂c hC₂ g
  · exact eLpNorm_yNorm_lift_top_le hχ₃ hχ₃c hC₃ (Real.holderConjugate_iff.1 hpu.symm).1.le h

end PrimeBHT.TransferenceAssembly
