module

public import PrimeBHT.TimeFrequency.X2.CZ.Statements
public import PrimeBHT.TimeFrequency.X2.CZ.MixedNorm
public import PrimeBHT.TimeFrequency.X2.CZ.Dyadic
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# V08: dyadic pieces of a Mikhlin symbol and the decay of their kernels

`σ ∈ IsMikhlin a₀ B`, `φ` a smooth bump supported in the open annulus `1/2 < |t| < 2`
(`AnnulusBump φ`) and `r > 0` a scale.  The *piece* `piece φ σ r ξ = σ(ξ) φ(rξ)` is `C^{a₀}` on `ℝ`
(it vanishes near `0`, where `σ` is singular), lives on `1/(2r) ≤ |ξ| ≤ 2/r`, and

* `norm_iteratedDeriv_piece_le`: `|piece^{(k)}(ξ)| ≤ B · C_k(φ) · r^k` for `k ≤ a₀`: the Mikhlin
  condition `|σ^{(i)}(ξ)| ≤ B |ξ|^{-i}` and `|ξ| ≥ 1/(2r)` on the support, by Leibniz
  (`norm_iteratedFDerivWithin_mul_le` on the open set `ℝ ∖ {0}`);
* `integral_norm_iteratedDeriv_piece_le`: `∫ |piece^{(k)}| ≤ 4 B C_k(φ) r^{k-1}`;
* `norm_fourierInv_piece_le`: the inverse Fourier transform `K = 𝓕⁻(piece)` satisfies
  `(2π|x|)^k |K(x)| ≤ 4 B C_k(φ) r^{k-1}` for `k ≤ a₀` (integration by parts `k` times:
  `Real.fourier_iteratedDeriv`).

Constants depend only on `φ` and `k`, never on `σ` (beyond the factor `B`), `r`, `x`, or the class order.
Everything is uniform in the symbol, as needed for the random-phase multipliers of V14.
-/

@[expose] public section

open MeasureTheory Set
open scoped FourierTransform ContDiff

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

/-- A smooth (complex valued) bump vanishing outside the open annulus `1/2 < |t| < 2`. -/
structure AnnulusBump (φ : ℝ → ℂ) : Prop where
  contDiff : ContDiff ℝ ∞ φ
  zero : ∀ t : ℝ, (|t| < 1 / 2 ∨ 2 < |t|) → φ t = 0

/-- The dyadic bump `ψ` as an `AnnulusBump`. -/
theorem annulusBump_dyadicPsi : AnnulusBump (fun t => ((dyadicPsi t : ℝ) : ℂ)) where
  contDiff := Complex.ofRealCLM.contDiff.comp contDiff_dyadicPsi
  zero t h := by
    have : dyadicPsi t = 0 := by
      rcases h with h | h
      · exact dyadicPsi_eq_zero_of_abs_le h.le
      · exact dyadicPsi_eq_zero_of_two_le_abs h.le
    simp [this]

namespace AnnulusBump

variable {φ : ℝ → ℂ}

/-- All derivatives of an `AnnulusBump` vanish in the open set `|t| < 1/2` and in `|t| > 2`. -/
theorem iteratedDeriv_eq_zero (hφ : AnnulusBump φ) (m : ℕ) {t : ℝ} (h : |t| < 1 / 2 ∨ 2 < |t|) :
    iteratedDeriv m φ t = 0 := by
  have hev : φ =ᶠ[nhds t] (fun _ => (0 : ℂ)) := by
    rcases h with h | h
    · have : {x : ℝ | |x| < 1 / 2} ∈ nhds t :=
        (isOpen_lt continuous_abs continuous_const).mem_nhds h
      filter_upwards [this] with x hx using hφ.zero x (Or.inl hx)
    · have : {x : ℝ | 2 < |x|} ∈ nhds t := (isOpen_lt continuous_const continuous_abs).mem_nhds h
      filter_upwards [this] with x hx using hφ.zero x (Or.inr hx)
  rw [hev.iteratedDeriv_eq m]
  simp

/-- Every derivative of an `AnnulusBump` is bounded. -/
theorem exists_bound (hφ : AnnulusBump φ) (m : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, ‖iteratedDeriv m φ t‖ ≤ M := by
  have hc : Continuous (iteratedDeriv m φ) :=
    hφ.contDiff.continuous_iteratedDeriv m (by exact_mod_cast le_top)
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (-2 : ℝ) 2
  · exact (hM t ht).trans (le_max_left _ _)
  · have : 2 < |t| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h
    rw [hφ.iteratedDeriv_eq_zero m (Or.inr this)]
    simp

/-- A bound `M_m` for `‖φ^{(m)}‖_∞`. -/
noncomputable def bound (hφ : AnnulusBump φ) (m : ℕ) : ℝ := (hφ.exists_bound m).choose

theorem bound_nonneg (hφ : AnnulusBump φ) (m : ℕ) : 0 ≤ hφ.bound m :=
  (hφ.exists_bound m).choose_spec.1

theorem norm_iteratedDeriv_le (hφ : AnnulusBump φ) (m : ℕ) (t : ℝ) :
    ‖iteratedDeriv m φ t‖ ≤ hφ.bound m :=
  (hφ.exists_bound m).choose_spec.2 t

/-- The constant `C_k(φ) = ∑_{i ≤ k} C(k, i) 2^i M_{k-i}` of the Leibniz estimate. -/
noncomputable def pieceConst (hφ : AnnulusBump φ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * 2 ^ i * hφ.bound (k - i)

theorem pieceConst_nonneg (hφ : AnnulusBump φ) (k : ℕ) : 0 ≤ hφ.pieceConst k :=
  Finset.sum_nonneg fun i _ => by
    have := hφ.bound_nonneg (k - i)
    positivity

end AnnulusBump

/-- The dyadic piece `ξ ↦ σ(ξ) φ(r ξ)` of the symbol `σ`. -/
noncomputable def piece (φ : ℝ → ℂ) (σ : ℝ → ℂ) (r : ℝ) (ξ : ℝ) : ℂ := σ ξ * φ (r * ξ)

section Piece

variable {φ : ℝ → ℂ} {σ : ℝ → ℂ} {a₀ : ℕ} {B r : ℝ}

theorem IsMikhlin.nonneg (hσ : IsMikhlin a₀ B σ) : 0 ≤ B := by
  have := hσ.2 0 (Nat.zero_le _) 1 one_ne_zero
  simp only [pow_zero, one_mul] at this
  exact (norm_nonneg _).trans this

/-- Away from the annulus `1/(2r) ≤ |ξ| ≤ 2/r` the piece vanishes in a neighbourhood. -/
theorem piece_eventuallyEq_zero (hφ : AnnulusBump φ) (hr : 0 < r) {ξ : ℝ}
    (h : |ξ| < 1 / (2 * r) ∨ 2 / r < |ξ|) : piece φ σ r =ᶠ[nhds ξ] (fun _ => (0 : ℂ)) := by
  have hmem : {x : ℝ | |x| < 1 / (2 * r) ∨ 2 / r < |x|} ∈ nhds ξ := by
    refine (IsOpen.mem_nhds ?_ h)
    exact (isOpen_lt continuous_abs continuous_const).union (isOpen_lt continuous_const continuous_abs)
  filter_upwards [hmem] with x hx
  have : |r * x| < 1 / 2 ∨ 2 < |r * x| := by
    rw [abs_mul, abs_of_pos hr]
    rcases hx with hx | hx
    · left
      rw [lt_div_iff₀ (by positivity)] at hx
      linarith
    · right
      rw [div_lt_iff₀ hr] at hx
      linarith
  simp [piece, hφ.zero _ this]

theorem iteratedDeriv_piece_eq_zero (hφ : AnnulusBump φ) (hr : 0 < r) (k : ℕ) {ξ : ℝ}
    (h : |ξ| < 1 / (2 * r) ∨ 2 / r < |ξ|) : iteratedDeriv k (piece φ σ r) ξ = 0 := by
  rw [(piece_eventuallyEq_zero (σ := σ) hφ hr h).iteratedDeriv_eq k]
  simp

/-- The piece is `C^{a₀}` on `ℝ` (it vanishes near the singularity `0` of `σ`). -/
theorem contDiff_piece (hσ : IsMikhlin a₀ B σ) (hφ : AnnulusBump φ) (hr : 0 < r) :
    ContDiff ℝ (a₀ : WithTop ℕ∞) (piece φ σ r) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ξ = 0
  · subst hξ
    have h0 : |(0 : ℝ)| < 1 / (2 * r) := by simp; positivity
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      (piece_eventuallyEq_zero (σ := σ) hφ hr (Or.inl h0))
  · have hs : IsOpen ({0}ᶜ : Set ℝ) := isOpen_compl_singleton
    have h1 : ContDiffAt ℝ (a₀ : WithTop ℕ∞) σ ξ := hσ.1.contDiffAt (hs.mem_nhds hξ)
    have h2 : ContDiffAt ℝ (a₀ : WithTop ℕ∞) (fun x => φ (r * x)) ξ :=
      ((hφ.contDiff.of_le (by exact_mod_cast le_top)).comp
        (contDiff_const.mul contDiff_id)).contDiffAt
    exact h1.mul h2

/-- **Leibniz estimate** for the dyadic pieces of a Mikhlin symbol. -/
theorem norm_iteratedDeriv_piece_le (hσ : IsMikhlin a₀ B σ) (hφ : AnnulusBump φ) (hr : 0 < r)
    {k : ℕ} (hk : k ≤ a₀) (ξ : ℝ) :
    ‖iteratedDeriv k (piece φ σ r) ξ‖ ≤ B * hφ.pieceConst k * r ^ k := by
  have hB := hσ.nonneg
  have hC := hφ.pieceConst_nonneg k
  by_cases hξ : |ξ| < 1 / (2 * r) ∨ 2 / r < |ξ|
  · rw [iteratedDeriv_piece_eq_zero hφ hr k hξ]
    simp only [norm_zero]
    positivity
  · rw [not_or, not_lt, not_lt] at hξ
    obtain ⟨hξ1, hξ2⟩ := hξ
    have hξ0 : ξ ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hξ1
      have : 0 < 1 / (2 * r) := by positivity
      linarith
    have hs : IsOpen ({0}ᶜ : Set ℝ) := isOpen_compl_singleton
    have hξs : ξ ∈ ({0}ᶜ : Set ℝ) := hξ0
    have hf : ContDiffOn ℝ (a₀ : WithTop ℕ∞) σ {0}ᶜ := hσ.1
    have hg : ContDiff ℝ (a₀ : WithTop ℕ∞) (fun x => φ (r * x)) :=
      (hφ.contDiff.of_le (by exact_mod_cast le_top)).comp (contDiff_const.mul contDiff_id)
    have key := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) hf hg.contDiffOn hs.uniqueDiffOn hξs
      (n := k) (by exact_mod_cast hk)
    have e1 : ∀ n (f : ℝ → ℂ), ‖iteratedFDerivWithin ℝ n f {0}ᶜ ξ‖ = ‖iteratedDeriv n f ξ‖ := by
      intro n f
      rw [iteratedFDerivWithin_of_isOpen n hs hξs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    simp only [e1] at key
    -- bounds on the two factors
    have hσi : ∀ i ∈ Finset.range (k + 1), ‖iteratedDeriv i σ ξ‖ ≤ B * (2 * r) ^ i := by
      intro i hi
      have hik : i ≤ a₀ := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hk
      have h1 := hσ.2 i hik ξ hξ0
      have hpos : 0 < |ξ| ^ i := pow_pos (abs_pos.2 hξ0) i
      have h2 : (2 * r) ^ i * |ξ| ^ i ≥ 1 := by
        rw [← mul_pow]
        exact one_le_pow₀ (by
          have : 1 / (2 * r) ≤ |ξ| := hξ1
          rw [div_le_iff₀ (by positivity)] at this
          linarith)
      calc ‖iteratedDeriv i σ ξ‖ ≤ (2 * r) ^ i * (|ξ| ^ i * ‖iteratedDeriv i σ ξ‖) := by
            have := norm_nonneg (iteratedDeriv i σ ξ)
            nlinarith
        _ ≤ (2 * r) ^ i * B := by gcongr
        _ = B * (2 * r) ^ i := mul_comm _ _
    have hφi : ∀ m : ℕ, ‖iteratedDeriv m (fun x => φ (r * x)) ξ‖ ≤ r ^ m * hφ.bound m := by
      intro m
      have h := iteratedDeriv_comp_const_smul (n := m) (f := φ)
        (hφ.contDiff.of_le (by exact_mod_cast le_top)) r
      have h' : iteratedDeriv m (fun x => φ (r * x)) = fun x => r ^ m • iteratedDeriv m φ (r * x) := by
        simpa only [smul_eq_mul] using h
      rw [h']
      simp only [norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos hr]
      gcongr
      exact hφ.norm_iteratedDeriv_le m _
    refine key.trans ?_
    calc ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedDeriv i σ ξ‖ *
          ‖iteratedDeriv (k - i) (fun x => φ (r * x)) ξ‖
        ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (B * (2 * r) ^ i) *
            (r ^ (k - i) * hφ.bound (k - i)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have := hσi i hi
          have := hφi (k - i)
          gcongr
      _ = B * hφ.pieceConst k * r ^ k := by
          unfold AnnulusBump.pieceConst
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i hi => ?_
          have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          have : r ^ k = r ^ i * r ^ (k - i) := by rw [← pow_add]; congr 1; omega
          rw [this, mul_pow]
          ring

/-- The pointwise bound of `piece^{(k)}` by the indicator of the support annulus. -/
theorem norm_iteratedDeriv_piece_le_indicator (hσ : IsMikhlin a₀ B σ) (hφ : AnnulusBump φ)
    (hr : 0 < r) {k : ℕ} (hk : k ≤ a₀) (ξ : ℝ) :
    ‖iteratedDeriv k (piece φ σ r) ξ‖ ≤
      (Icc (-(2 / r)) (2 / r)).indicator (fun _ => B * hφ.pieceConst k * r ^ k) ξ := by
  by_cases hξ : ξ ∈ Icc (-(2 / r)) (2 / r)
  · rw [indicator_of_mem hξ]
    exact norm_iteratedDeriv_piece_le hσ hφ hr hk ξ
  · rw [indicator_of_notMem hξ]
    have hpos : 0 < 2 / r := by positivity
    have : 2 / r < |ξ| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hξ
      rcases hξ with h | h
      · rw [abs_of_neg (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        exact h
    rw [iteratedDeriv_piece_eq_zero hφ hr k (Or.inr this)]
    simp

theorem integrable_iteratedDeriv_piece (hσ : IsMikhlin a₀ B σ) (hφ : AnnulusBump φ) (hr : 0 < r)
    {k : ℕ} (hk : k ≤ a₀) : Integrable (iteratedDeriv k (piece φ σ r)) := by
  have hc : Continuous (iteratedDeriv k (piece φ σ r)) :=
    (contDiff_piece hσ hφ hr).continuous_iteratedDeriv k (by exact_mod_cast hk)
  have hind : Integrable ((Icc (-(2 / r)) (2 / r)).indicator
      (fun _ => B * hφ.pieceConst k * r ^ k)) :=
    (integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (by simp))
  exact hind.mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_iteratedDeriv_piece_le_indicator hσ hφ hr hk))

/-- **`L¹` bound of the derivatives of a piece**: `∫ |piece^{(k)}| ≤ (4/r) · B C_k r^k`. -/
theorem integral_norm_iteratedDeriv_piece_le (hσ : IsMikhlin a₀ B σ) (hφ : AnnulusBump φ)
    (hr : 0 < r) {k : ℕ} (hk : k ≤ a₀) :
    ∫ ξ, ‖iteratedDeriv k (piece φ σ r) ξ‖ ≤ 4 / r * (B * hφ.pieceConst k * r ^ k) := by
  have hind : Integrable ((Icc (-(2 / r)) (2 / r)).indicator
      (fun _ => B * hφ.pieceConst k * r ^ k)) :=
    (integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (by simp))
  calc ∫ ξ, ‖iteratedDeriv k (piece φ σ r) ξ‖
      ≤ ∫ ξ, (Icc (-(2 / r)) (2 / r)).indicator (fun _ => B * hφ.pieceConst k * r ^ k) ξ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hind
          (Filter.Eventually.of_forall (norm_iteratedDeriv_piece_le_indicator hσ hφ hr hk))
    _ = 4 / r * (B * hφ.pieceConst k * r ^ k) := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul]
        have hpos : 0 < 2 / r := by positivity
        have : (volume.real (Icc (-(2 / r)) (2 / r))) = 4 / r := by
          rw [Real.volume_real_Icc_of_le (by linarith)]
          field_simp
          ring
        rw [this]

/-- **Kernel decay of a piece** (`k` integrations by parts): `K = 𝓕⁻(piece)` satisfies
`(2π|x|)^k |K(x)| ≤ (4/r) · B C_k r^k` for `k ≤ a₀`. -/
theorem norm_fourierInv_piece_le (hσ : IsMikhlin a₀ B σ) (hφ : AnnulusBump φ) (hr : 0 < r)
    {k : ℕ} (hk : k ≤ a₀) (x : ℝ) :
    (2 * Real.pi * |x|) ^ k * ‖𝓕⁻ (piece φ σ r) x‖ ≤ 4 / r * (B * hφ.pieceConst k * r ^ k) := by
  have hcd : ContDiff ℝ ((k : ℕ∞) : WithTop ℕ∞) (piece φ σ r) :=
    (contDiff_piece hσ hφ hr).of_le (by exact_mod_cast hk)
  have hint : ∀ n : ℕ, (n : ℕ∞) ≤ (k : ℕ∞) → Integrable (iteratedDeriv n (piece φ σ r)) := by
    intro n hn
    exact integrable_iteratedDeriv_piece hσ hφ hr ((Nat.cast_le.1 hn).trans hk)
  have hF := Real.fourier_iteratedDeriv hcd hint (le_refl (k : ℕ∞))
  have h1 : ‖𝓕 (iteratedDeriv k (piece φ σ r)) (-x)‖ ≤ ∫ v, ‖iteratedDeriv k (piece φ σ r) v‖ :=
    Real.norm_fourier_le_integral_norm _ _
  rw [hF] at h1
  simp [norm_pow, abs_of_pos Real.pi_pos] at h1
  rw [Real.fourierInv_eq_fourier_neg]
  exact h1.trans (integral_norm_iteratedDeriv_piece_le hσ hφ hr hk)

/-- `t ↦ t φ(t)` is again an `AnnulusBump`. -/
theorem AnnulusBump.mul_id (hφ : AnnulusBump φ) : AnnulusBump (fun t => (t : ℂ) * φ t) where
  contDiff := (Complex.ofRealCLM.contDiff.comp contDiff_id).mul hφ.contDiff
  zero t h := by simp [hφ.zero t h]

theorem piece_mul_id (φ : ℝ → ℂ) (σ : ℝ → ℂ) (r : ℝ) (ξ : ℝ) :
    piece (fun t => (t : ℂ) * φ t) σ r ξ = (r : ℂ) * ((ξ : ℂ) * piece φ σ r ξ) := by
  simp only [piece]
  push_cast
  ring

theorem integrable_piece (hσ : IsMikhlin a₀ B σ) (hφ : AnnulusBump φ) (hr : 0 < r) :
    Integrable (piece φ σ r) := by
  have := integrable_iteratedDeriv_piece hσ hφ hr (Nat.zero_le a₀)
  simpa using this

/-- **The derivative of the kernel of a piece**:
`d/dx 𝓕⁻(piece φ σ r) (x) = (2πi / r) · 𝓕⁻(piece (t φ) σ r)(x)`. -/
theorem hasDerivAt_fourierInv_piece (hσ : IsMikhlin a₀ B σ) (hφ : AnnulusBump φ) (hr : 0 < r)
    (x : ℝ) :
    HasDerivAt (𝓕⁻ (piece φ σ r))
      ((2 * Real.pi * Complex.I / r) *
        𝓕⁻ (piece (fun t => (t : ℂ) * φ t) σ r) x) x := by
  have hf : Integrable (piece φ σ r) := integrable_piece hσ hφ hr
  have hφ₁ := hφ.mul_id
  have hf₁ : Integrable (piece (fun t => (t : ℂ) * φ t) σ r) :=
    integrable_piece (a₀ := a₀) hσ hφ₁ hr
  have hξf : Integrable (fun ξ : ℝ => ξ • piece φ σ r ξ) := by
    have : (fun ξ : ℝ => ξ • piece φ σ r ξ) =
        fun ξ => ((r : ℂ)⁻¹) * piece (fun t => (t : ℂ) * φ t) σ r ξ := by
      ext ξ
      rw [piece_mul_id φ σ r, Complex.real_smul]
      have : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      field_simp
    rw [this]
    exact hf₁.const_mul _
  have hD := Real.hasDerivAt_fourier hf hξf (-x)
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) x := (hasDerivAt_id x).neg
  have hcomp := hD.scomp x hneg
  have hK : 𝓕⁻ (piece φ σ r) = fun y => 𝓕 (piece φ σ r) (-y) := by
    ext y; exact Real.fourierInv_eq_fourier_neg _ y
  rw [hK]
  refine HasDerivAt.congr_deriv (f' := -1 • 𝓕 (fun ξ : ℝ => (-2 * Real.pi * Complex.I * ξ) •
    piece φ σ r ξ) (-x)) hcomp ?_
  -- identify the derivative value
  have e1 : (fun ξ : ℝ => (-2 * Real.pi * Complex.I * ξ) • piece φ σ r ξ) =
      fun ξ => (-(2 * Real.pi * Complex.I / r)) *
        piece (fun t => (t : ℂ) * φ t) σ r ξ := by
    ext ξ
    rw [piece_mul_id φ σ r]
    have : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    simp only [smul_eq_mul]
    field_simp
  rw [e1]
  have e2 := fourierInv_const_mul (-(2 * Real.pi * Complex.I / r))
    (piece (fun t => (t : ℂ) * φ t) σ r) x
  have e3 : 𝓕 (fun ξ : ℝ => (-(2 * Real.pi * Complex.I / r)) *
      piece (fun t => (t : ℂ) * φ t) σ r ξ) (-x) =
      𝓕⁻ (fun ξ : ℝ => (-(2 * Real.pi * Complex.I / r)) *
      piece (fun t => (t : ℂ) * φ t) σ r ξ) x := (Real.fourierInv_eq_fourier_neg _ x).symm
  rw [e3, e2]
  simp only [neg_smul, one_smul]
  ring

end Piece

end PrimeBHT.TimeFrequency.X2.CZ
