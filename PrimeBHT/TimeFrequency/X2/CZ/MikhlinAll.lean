module

public import PrimeBHT.TimeFrequency.X2.CZ.ScalarAll

/-!
# V08 phase 3: the full strong-type matrix `(q, s)`, `1 < q, s < ∞`, for Mikhlin multipliers

* `exists_kStrong_normKernel`: for all `1 < q, s` there is a constant `A = A(q, s)` with
  `‖K^N_σ/B * F‖_{L^q(ℝ; L^s(Y_P))} ≤ A ‖F‖_{L^q(ℝ; L^s(Y_P))}` on `𝒞`, for every `P`, `N`,
  `σ ∈ IsMikhlin 3 B`, `B > 0`: for `q ≤ s` by Marcinkiewicz (`marcinkiewicz_kernel`) from the weak `(1,1)`
  bound and the strong `(s, s)` bound (`TruncScalarStrong s`, now unconditional), and for `q > s` by duality
  (`kStrong_of_adjoint`) from the case `q' < s'` for `conj σ`.
* `vectorMikhlinStrong_of_kStrong`: the passage `N → ∞` (Fatou) to `T_σ ⊗ Id` on tensor Schwartz data.
* `vectorMikhlinStrongStatement_three`, `vectorMikhlinWeakStatement_three`, `vectorMikhlinStatement_three`:
  the targets (a), (b), (f) of `Statements.lean`, **unconditional**, for `a₀ = 3`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology Real ComplexConjugate

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

open PrimeBHT.Statements

theorem one_lt_conjExponent' {q : ℝ} (hq : 1 < q) : 1 < Real.conjExponent q := by
  have h1 : 0 < q - 1 := by linarith
  unfold Real.conjExponent
  rw [lt_div_iff₀ h1]; linarith

/-- `KStrong` of the normalized truncated kernels for `1 < q ≤ s`. -/
theorem exists_kStrong_normKernel_le {q s : ℝ} (hq : 1 < q) (hqs : q ≤ s) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (P : ℕ) [NeZero P] (B : ℝ) (σ : ℝ → ℂ), IsMikhlin 3 B σ → 0 < B → ∀ N : ℕ,
      KStrong P (normKernel σ B N) q s A := by
  have hs : 1 < s := by linarith
  have hs0 : 0 < s := by linarith
  have hq0 : 0 < q := by linarith
  obtain ⟨A₀, hA₀, hT⟩ := exists_truncScalarStrong hs
  have hcH : 0 ≤ cH := by unfold cH; positivity
  rcases hqs.eq_or_lt with h | h
  · subst h
    refine ⟨A₀, hA₀, fun P _ B σ hσ hB N g hg => ?_⟩
    exact hGood_of_scalar (K := normKernel σ B N) hs (measurable_normKernel hσ N)
      (norm_normKernel_le hσ hB N) (hScalar_normKernel hT hσ hB N) g hg.1 hg.2.1 hg.2.2
  · have hM : 0 ≤ q * 2 ^ q * ((2 + 2 ^ (2 * s - 1) * A₀ ^ s + 4 * cH) / (q - 1) + A₀ ^ s / (s - q)) := by
      have h1 : 0 < q - 1 := by linarith
      have h2 : 0 < s - q := by linarith
      positivity
    refine ⟨(q * 2 ^ q * ((2 + 2 ^ (2 * s - 1) * A₀ ^ s + 4 * cH) / (q - 1) + A₀ ^ s / (s - q))) ^ q⁻¹,
      Real.rpow_nonneg hM _, fun P _ B σ hσ hB N g hg => ?_⟩
    have hKm := measurable_normKernel hσ N
    have hKb := norm_normKernel_le hσ hB N
    have hH := hH_normKernel hσ hB N
    have hGood : ∀ g : ℝ → ZMod P → ℂ, (∀ y, Measurable fun u => g u y) →
        (∀ y, Integrable fun u => g u y) → (∀ y, ∃ C, ∀ u, ‖g u y‖ ≤ C) →
        ∫⁻ x, ENNReal.ofReal (yNorm s (fun y => kop (normKernel σ B N) (fun u => g u y) x)) ^ s ≤
          ENNReal.ofReal A₀ ^ s * ∫⁻ u, ENNReal.ofReal (yNorm s (g u)) ^ s :=
      fun g hgm hgi hgb => hGood_of_scalar (K := normKernel σ B N) hs hKm hKb
        (hScalar_normKernel hT hσ hB N) g hgm hgi hgb
    have h1 := marcinkiewicz_kernel hs hKm hKb hA₀ hcH hH hGood hq h g hg.1 hg.2.1 hg.2.2
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hM _) hq0.le, ← Real.rpow_mul hM,
      inv_mul_cancel₀ hq0.ne', Real.rpow_one]
    exact h1

/-- **`KStrong` of the normalized truncated kernels for all `1 < q, s`**. -/
theorem exists_kStrong_normKernel {q s : ℝ} (hq : 1 < q) (hs : 1 < s) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (P : ℕ) [NeZero P] (B : ℝ) (σ : ℝ → ℂ), IsMikhlin 3 B σ → 0 < B → ∀ N : ℕ,
      KStrong P (normKernel σ B N) q s A := by
  rcases le_or_gt q s with h | h
  · exact exists_kStrong_normKernel_le hq h
  · have hq' : 1 < Real.conjExponent q := one_lt_conjExponent' hq
    have hs' : Real.conjExponent q ≤ Real.conjExponent s := by
      unfold Real.conjExponent
      have h1 : 0 < q - 1 := by linarith
      have h2 : 0 < s - 1 := by linarith
      rw [div_le_div_iff₀ h1 h2]; nlinarith
    obtain ⟨A, hA, hK⟩ := exists_kStrong_normKernel_le hq' hs'
    refine ⟨A, hA, fun P _ B σ hσ hB N => ?_⟩
    refine kStrong_of_adjoint (measurable_normKernel hσ N) (norm_normKernel_le hσ hB N) hq hs hA ?_
    rw [adjKernel_normKernel]
    exact hK P B _ hσ.conj hB N

/-- **The passage `N → ∞`**: a uniform strong `(q, s)` bound `A` for the normalized truncated kernels on `𝒞`
gives `‖(T_σ ⊗ Id) F‖_{L^q(ℝ; L^s(Y_P))} ≤ A B ‖F‖_{L^q(ℝ; L^s(Y_P))}` on tensor Schwartz data. -/
theorem vectorMikhlinStrong_of_kStrong {q s A : ℝ} (hq : 1 < q) (hs : 1 < s) (hA : 0 ≤ A)
    (hK : ∀ (P : ℕ) [NeZero P] (B : ℝ) (σ : ℝ → ℂ), IsMikhlin 3 B σ → 0 < B → ∀ N : ℕ,
      KStrong P (normKernel σ B N) q s A) : VectorMikhlinStrong 3 q s A := by
  intro P _ B σ hσ f
  have hs0 : 0 < s := by linarith
  have hq0 : 0 < q := by linarith
  obtain ⟨hFm, hFi, hFb⟩ := tensorFun_fibre_facts f
  have hFAE : ∀ y, AEStronglyMeasurable (fun x => tensorFun f x y) volume := fun y =>
    (hFm y).aestronglyMeasurable
  have hB0 := hσ.nonneg
  rcases hB0.eq_or_lt with hB | hB
  · subst hB
    have : tensorMult σ f = fun _ _ => 0 := by
      ext x y; exact tensorMult_eq_zero_of_B_zero hσ f x y
    have h0 : mixedENorm q s (tensorMult σ f) = 0 := by
      unfold mixedENorm
      have : (fun x => yNorm s (tensorMult σ f x)) = fun _ => (0 : ℝ) := by
        ext x; rw [this]; exact yNorm_zero' hs0
      rw [this]; simp
    rw [h0]; exact bot_le
  · have hTmeas : ∀ y, AEStronglyMeasurable (fun x => tensorMult σ f x y) volume := fun y => by
      have : (fun x => tensorMult σ f x y) = multOp σ (⇑(fibreSchwartz f y)) := by
        ext x; exact tensorMult_eq_multOp_fibreSchwartz hσ.isBoundedSymbol f x y
      rw [this]
      exact (hσ.isBoundedSymbol.continuous_multOp (fibreSchwartz f y)).aestronglyMeasurable
    have hbound : ∀ N : ℕ, ∫⁻ x, ENNReal.ofReal (yNorm s (fun y => multOp (symbolTrunc σ N)
        (⇑(fibreSchwartz f y)) x)) ^ q ≤ ENNReal.ofReal B ^ q * (ENNReal.ofReal A ^ q *
          ∫⁻ x, ENNReal.ofReal (yNorm s (tensorFun f x)) ^ q) := by
      intro N
      have h1 := hK P B σ hσ hB N (tensorFun f) ⟨hFm, hFi, hFb⟩
      have e : ∀ x, ENNReal.ofReal (yNorm s (fun y => multOp (symbolTrunc σ N)
          (⇑(fibreSchwartz f y)) x)) ^ q = ENNReal.ofReal B ^ q * ENNReal.ofReal
          (yNorm s (fun y => kop (normKernel σ B N) (fun u => tensorFun f u y) x)) ^ q := by
        intro x
        rw [yNorm_multOp_trunc_eq hs0 hσ hB N f x, ENNReal.ofReal_mul hB.le,
          ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
      simp_rw [e]
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top)]
      exact mul_le_mul' le_rfl h1
    have hmeasN : ∀ N : ℕ, Measurable fun x => ENNReal.ofReal (yNorm s (fun y => multOp
        (symbolTrunc σ N) (⇑(fibreSchwartz f y)) x)) ^ q := by
      intro N
      refine ((measurable_yNorm s (fun y => ?_)).ennreal_ofReal).pow_const q
      exact (continuous_fourierInv_of_integrable _
        ((isBoundedSymbol_symbolTrunc hσ N).integrable_mul_fourier (fibreSchwartz f y))).measurable
    have hlimN : ∀ x, Tendsto (fun N : ℕ => ENNReal.ofReal (yNorm s (fun y => multOp (symbolTrunc σ N)
        (⇑(fibreSchwartz f y)) x)) ^ q) atTop
        (nhds (ENNReal.ofReal (yNorm s (tensorMult σ f x)) ^ q)) := fun x =>
      ((ENNReal.continuous_rpow_const (y := q)).tendsto _).comp
        ((ENNReal.continuous_ofReal.tendsto _).comp (tendsto_yNorm_tensorMultTrunc hs0 hσ f x))
    have hfat := lintegral_le_of_tendsto_of_le hmeasN hlimN hbound
    have e1 := mixedENorm_rpow hq0 s hTmeas
    have e2 := mixedENorm_rpow hq0 s hFAE
    rw [← e1] at hfat
    rw [← e2] at hfat
    have hrhs : ENNReal.ofReal B ^ q * (ENNReal.ofReal A ^ q * mixedENorm q s (tensorFun f) ^ q) =
        (ENNReal.ofReal (A * B) * mixedENorm q s (tensorFun f)) ^ q := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ENNReal.ofReal_mul hA,
        ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
      ring
    rw [hrhs] at hfat
    exact (ENNReal.rpow_le_rpow_iff hq0).1 hfat

/-- **Target (a) of `Statements.lean`, unconditional (`a₀ = 3`)**: `T_σ ⊗ Id` is bounded on
`L^q(ℝ; L^s(Y_P))` for all `1 < q, s < ∞`, with `C = C(q, s)` independent of `P` and (beyond the factor
`B`) of the symbol. -/
theorem vectorMikhlinStrongStatement_three : VectorMikhlinStrongStatement 3 := by
  intro q s hq hs
  obtain ⟨A, hA, hK⟩ := exists_kStrong_normKernel hq hs
  exact ⟨A, vectorMikhlinStrong_of_kStrong hq hs hA fun P _ B σ hσ hB N => hK P B σ hσ hB N⟩

/-- **Target (b) of `Statements.lean`, unconditional (`a₀ = 3`)**: weak `(1,1)` into `L^{1,∞}(ℝ; L^s(Y_P))`
for every `1 < s < ∞`. -/
theorem vectorMikhlinWeakStatement_three : VectorMikhlinWeakStatement 3 := by
  intro s hs
  obtain ⟨A, hA, hT⟩ := exists_truncScalarStrong hs
  exact ⟨_, vectorMikhlinWeak_of_trunc hs hA hT⟩

/-- **Target (f) of `Statements.lean`, unconditional (`a₀ = 3`)**. -/
theorem vectorMikhlinStatement_three : VectorMikhlinStatement 3 :=
  ⟨vectorMikhlinStrongStatement_three, vectorMikhlinWeakStatement_three⟩

/-- The Mikhlin class is monotone in the order: `IsMikhlin a₁ B σ → IsMikhlin a₀ B σ` for `a₀ ≤ a₁`. -/
theorem IsMikhlin.mono {a₀ a₁ : ℕ} {B : ℝ} {σ : ℝ → ℂ} (h : a₀ ≤ a₁) (hσ : IsMikhlin a₁ B σ) :
    IsMikhlin a₀ B σ :=
  ⟨hσ.1.of_le (by exact_mod_cast h), fun a ha ξ hξ => hσ.2 a (ha.trans h) ξ hξ⟩

/-- **Targets (a), (b), (f) for every order `a₀ ≥ 3`** (the class is monotone in `a₀`). -/
theorem vectorMikhlinStatement_of_ge {a₀ : ℕ} (h : 3 ≤ a₀) : VectorMikhlinStatement a₀ := by
  obtain ⟨hS, hW⟩ := vectorMikhlinStatement_three
  refine ⟨fun q s hq hs => ?_, fun s hs => ?_⟩
  · obtain ⟨C, hC⟩ := hS q s hq hs
    exact ⟨C, fun P _ B σ hσ f => hC P B σ (hσ.mono h) f⟩
  · obtain ⟨C, hC⟩ := hW s hs
    exact ⟨C, fun P _ B σ hσ f t ht => hC P B σ (hσ.mono h) f t ht⟩

end PrimeBHT.TimeFrequency.X2.CZ
