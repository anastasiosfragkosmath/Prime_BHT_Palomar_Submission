module

public import PrimeBHT.TimeFrequency.X2.CZ.Hormander
public import PrimeBHT.TimeFrequency.X2.CZ.Basecase

/-!
# V08 phase 2: the truncated multipliers `T_N = ∑_{|j| ≤ N} T_{σ_j}`

The kernel `K = 𝓕⁻σ` of a Mikhlin multiplier is a distribution (`K = ∑_j K_j`, `Hormander.lean`),
and `T_σ` is only defined on nice functions (Schwartz, `Statements.lean`).  Every proof of the
Calderón-Zygmund theory needs `T` on non-Schwartz functions (bad atoms, good part); the clean way to get
them (and what the Carleson clone does with its truncated kernels) is to work with the **truncations**

`σ^N = ∑_{|j| ≤ N} σ ψ(2^{-j}·) = σ Ψ_N`,   `K^N = 𝓕⁻σ^N = ∑_{|j| ≤ N} K_j`,   `T_N h = K^N * h`,

which are convolution operators with an `L¹` kernel (so defined on every `h ∈ L¹`, no extension problem),
**bounded uniformly in `N`** (this is what the Hörmander estimates give, and Plancherel gives the
`L²` bound `2B`), and which converge to `T_σ` on Schwartz functions pointwise (`tendsto_multOp_symbolTrunc`).

Contents.
* `PsiN`: `Ψ_N = ∑_{|j| ≤ N} ψ(2^{-j}·)`: `|Ψ_N| ≤ 2` and `Ψ_N(ξ) = 1` for `N ≥ N₀(ξ)`, `ξ ≠ 0`.
* `symbolTrunc σ N = σ Ψ_N`: bounded measurable (`2B`), integrable, a finite sum of pieces.
* `kernelTrunc σ N = 𝓕⁻(σ^N) = ∑_{|j| ≤ N} K_j`; uniform-in-`N` pointwise bounds
  `|K^N(x)| ≤ cB/|x|`, `|K^N(x-y) - K^N(x)| ≤ cH B|y|/x²`.
* `multOp_eq_convolution`: `T_p h(x) = ∫ 𝓕⁻p(x - y) h(y) dy` (`p, h ∈ L¹`, Fubini).
* `eLpNorm_multOp_two_le_of_integrable`: `‖T_p h‖₂ ≤ B ‖h‖₂`, `h ∈ L¹ ∩ L²` (Plancherel).
* `tendsto_multOp_symbolTrunc`: `T_N g(x) → T_σ g(x)` for `g` Schwartz.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped FourierTransform ContDiff ENNReal Topology Real SchwartzMap

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

/-! ## `Ψ_N = ∑_{|j| ≤ N} ψ(2^{-j}·)` -/

theorem abs_dyadicPsi_le_one (t : ℝ) : |dyadicPsi t| ≤ 1 := by
  have h1 := dyadicBump.nonneg' t
  have h2 := dyadicBump.le_one (x := t)
  have h3 := dyadicBump.nonneg' (2 * t)
  have h4 := dyadicBump.le_one (x := 2 * t)
  rw [dyadicPsi, abs_le]
  constructor <;> linarith

/-- If `ψ(2^{-j} ξ) ≠ 0` then `2^j / 2 < |ξ| < 2 · 2^j`. -/
theorem dyadicPsi_scaled_ne_zero {ξ : ℝ} {j : ℤ} (h : dyadicPsi ((2 : ℝ) ^ (-j) * ξ) ≠ 0) :
    (2 : ℝ) ^ j / 2 < |ξ| ∧ |ξ| < 2 * (2 : ℝ) ^ j := by
  have hm := dyadicPsi_eq_zero_iff_mem h
  have hp : (0 : ℝ) < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hq : (2 : ℝ) ^ (-j) * (2 : ℝ) ^ j = 1 := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; simp
  rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)] at hm
  obtain ⟨h1, h2⟩ := hm
  constructor
  · have := mul_lt_mul_of_pos_right h1 hp
    nlinarith [mul_comm ((2 : ℝ) ^ (-j)) (2 ^ j)]
  · have := mul_lt_mul_of_pos_right h2 hp
    nlinarith [mul_comm ((2 : ℝ) ^ (-j)) (2 ^ j)]

/-- The nonzero terms `ψ(2^{-j} ξ)` occupy at most two consecutive indices `L, L+1`. -/
theorem exists_support_two {ξ : ℝ} (_hξ : ξ ≠ 0) :
    ∃ L : ℤ, ∀ j : ℤ, dyadicPsi ((2 : ℝ) ^ (-j) * ξ) ≠ 0 → j = L ∨ j = L + 1 := by
  by_cases hne : ∃ j : ℤ, dyadicPsi ((2 : ℝ) ^ (-j) * ξ) ≠ 0
  · obtain ⟨j₀, hj₀⟩ := hne
    have hlt : ∀ j j' : ℤ, dyadicPsi ((2 : ℝ) ^ (-j) * ξ) ≠ 0 →
        dyadicPsi ((2 : ℝ) ^ (-j') * ξ) ≠ 0 → j' ≤ j + 1 := by
      intro j j' hj hj'
      obtain ⟨a1, a2⟩ := dyadicPsi_scaled_ne_zero hj
      obtain ⟨b1, b2⟩ := dyadicPsi_scaled_ne_zero hj'
      have h : (2 : ℝ) ^ j' < (2 : ℝ) ^ (j + 2) := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num
        linarith
      have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h
      omega
    have hbdd : ∃ m : ℤ, ∀ j : ℤ, dyadicPsi ((2 : ℝ) ^ (-j) * ξ) ≠ 0 → m ≤ j := by
      refine ⟨j₀ - 1, fun j hj => ?_⟩
      have := hlt j j₀ hj hj₀
      omega
    obtain ⟨L, hL, hLmin⟩ := Int.exists_least_of_bdd (P := fun j : ℤ =>
      dyadicPsi ((2 : ℝ) ^ (-j) * ξ) ≠ 0) hbdd ⟨j₀, hj₀⟩
    refine ⟨L, fun j hj => ?_⟩
    have h1 := hLmin j hj
    have h2 := hlt L j hL hj
    omega
  · push Not at hne
    exact ⟨0, fun j hj => absurd (hne j) hj⟩

/-- The truncated partition of unity `Ψ_N = ∑_{|j| ≤ N} ψ(2^{-j}·)`. -/
noncomputable def PsiN (N : ℕ) (ξ : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc (-(N : ℤ)) N, dyadicPsi ((2 : ℝ) ^ (-j) * ξ)

theorem continuous_PsiN (N : ℕ) : Continuous (PsiN N) := by
  unfold PsiN
  refine continuous_finsetSum _ fun j _ => ?_
  exact contDiff_dyadicPsi.continuous.comp (continuous_const.mul continuous_id)

theorem abs_PsiN_le (N : ℕ) (ξ : ℝ) : |PsiN N ξ| ≤ 2 := by
  by_cases hξ : ξ = 0
  · subst hξ
    have h0 : dyadicPsi 0 = 0 := dyadicPsi_eq_zero_of_abs_le (by simp)
    simp [PsiN, h0]
  obtain ⟨L, hL⟩ := exists_support_two hξ
  unfold PsiN
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hsub : (Finset.Icc (-(N : ℤ)) N).filter (fun j => dyadicPsi ((2 : ℝ) ^ (-j) * ξ) ≠ 0) ⊆
      {L, L + 1} := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rcases hL j hj.2 with h | h <;> simp [h]
  have hsum : ∑ j ∈ Finset.Icc (-(N : ℤ)) N, |dyadicPsi ((2 : ℝ) ^ (-j) * ξ)| =
      ∑ j ∈ (Finset.Icc (-(N : ℤ)) N).filter (fun j => dyadicPsi ((2 : ℝ) ^ (-j) * ξ) ≠ 0),
        |dyadicPsi ((2 : ℝ) ^ (-j) * ξ)| := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : dyadicPsi ((2 : ℝ) ^ (-j) * ξ) = 0 <;> simp
  rw [hsum]
  calc ∑ j ∈ (Finset.Icc (-(N : ℤ)) N).filter (fun j => dyadicPsi ((2 : ℝ) ^ (-j) * ξ) ≠ 0),
        |dyadicPsi ((2 : ℝ) ^ (-j) * ξ)|
      ≤ ∑ j ∈ (Finset.Icc (-(N : ℤ)) N).filter (fun j => dyadicPsi ((2 : ℝ) ^ (-j) * ξ) ≠ 0), (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => abs_dyadicPsi_le_one _
    _ = ((Finset.Icc (-(N : ℤ)) N).filter (fun j => dyadicPsi ((2 : ℝ) ^ (-j) * ξ) ≠ 0)).card := by
        simp
    _ ≤ ({L, L + 1} : Finset ℤ).card := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ 2 := by exact_mod_cast Finset.card_le_two

theorem eventually_PsiN_eq_one {ξ : ℝ} (hξ : ξ ≠ 0) : ∀ᶠ N : ℕ in atTop, PsiN N ξ = 1 := by
  obtain ⟨L, hL⟩ := exists_support_two hξ
  rw [eventually_atTop]
  refine ⟨(|L| + 2).toNat, fun N hN => ?_⟩
  have hN' : (|L| + 2 : ℤ) ≤ N := by
    have := Int.self_le_toNat (|L| + 2)
    omega
  have hs : ∀ j : ℤ, j ∉ Finset.Icc (-(N : ℤ)) N →
      dyadicPsi ((2 : ℝ) ^ (-j) * ξ) = 0 := by
    intro j hj
    by_contra hne
    apply hj
    rw [Finset.mem_Icc]
    have hL1 : -|L| ≤ L := neg_abs_le L
    have hL2 : L ≤ |L| := le_abs_self L
    rcases hL j hne with h | h
    · rw [h]; constructor <;> omega
    · rw [h]; constructor <;> omega
  have h1 : HasSum (fun j : ℤ => dyadicPsi ((2 : ℝ) ^ (-j) * ξ))
      (∑ j ∈ Finset.Icc (-(N : ℤ)) N, dyadicPsi ((2 : ℝ) ^ (-j) * ξ)) :=
    hasSum_sum_of_ne_finset_zero hs
  exact h1.unique (hasSum_dyadicPsi_scaled hξ)

/-! ## The truncated symbol and kernel -/

variable {σ : ℝ → ℂ} {B : ℝ}

/-- The truncated symbol `σ^N = σ Ψ_N = ∑_{|j| ≤ N} σ ψ(2^{-j}·)`. -/
noncomputable def symbolTrunc (σ : ℝ → ℂ) (N : ℕ) (ξ : ℝ) : ℂ := σ ξ * ((PsiN N ξ : ℝ) : ℂ)

theorem symbolTrunc_eq_sum (σ : ℝ → ℂ) (N : ℕ) (ξ : ℝ) :
    symbolTrunc σ N ξ = ∑ j ∈ Finset.Icc (-(N : ℤ)) N, piece psiC σ ((2 : ℝ) ^ (-j)) ξ := by
  unfold symbolTrunc PsiN piece psiC
  push_cast
  rw [Finset.mul_sum]

theorem isBoundedSymbol_symbolTrunc (hσ : IsMikhlin 3 B σ) (N : ℕ) :
    IsBoundedSymbol (2 * B) (symbolTrunc σ N) := by
  have hb := hσ.isBoundedSymbol
  refine ⟨hb.aestronglyMeasurable.mul
    (Complex.continuous_ofReal.comp (continuous_PsiN N)).aestronglyMeasurable, ?_⟩
  filter_upwards [hb.ae_norm_le] with ξ hξ
  unfold symbolTrunc
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have := abs_PsiN_le N ξ
  have h0 : 0 ≤ ‖σ ξ‖ := norm_nonneg _
  nlinarith

theorem integrable_symbolTrunc (hσ : IsMikhlin 3 B σ) (N : ℕ) :
    Integrable (symbolTrunc σ N) := by
  have : symbolTrunc σ N = fun ξ => ∑ j ∈ Finset.Icc (-(N : ℤ)) N,
      piece psiC σ ((2 : ℝ) ^ (-j)) ξ := by
    ext ξ; exact symbolTrunc_eq_sum σ N ξ
  rw [this]
  exact integrable_finsetSum _ fun j _ => integrable_piece hσ annulusBump_psiC (two_zpow_neg_pos j)

/-- The truncated kernel `K^N = 𝓕⁻(σ^N)` (an `L¹` function, continuous). -/
noncomputable def kernelTrunc (σ : ℝ → ℂ) (N : ℕ) : ℝ → ℂ := 𝓕⁻ (symbolTrunc σ N)

theorem kernelTrunc_eq_sum (hσ : IsMikhlin 3 B σ) (N : ℕ) (x : ℝ) :
    kernelTrunc σ N x = ∑ j ∈ Finset.Icc (-(N : ℤ)) N, kernelPiece σ j x := by
  have : symbolTrunc σ N = fun ξ => ∑ j ∈ Finset.Icc (-(N : ℤ)) N,
      piece psiC σ ((2 : ℝ) ^ (-j)) ξ := by
    ext ξ; exact symbolTrunc_eq_sum σ N ξ
  unfold kernelTrunc
  rw [this]
  exact fourierInv_finset_sum_fun _ _
    (fun j _ => integrable_piece hσ annulusBump_psiC (two_zpow_neg_pos j)) x

/-- **Uniform Hörmander smoothness** (independent of `N`): for `2|y| ≤ |x|`, `x ≠ 0`,
`|K^N(x - y) - K^N(x)| ≤ cH B |y| / x²`. -/
theorem norm_kernelTrunc_sub_le (hσ : IsMikhlin 3 B σ) (hB : 0 < B) {x y : ℝ} (hx : x ≠ 0)
    (hy : 2 * |y| ≤ |x|) (N : ℕ) :
    ‖kernelTrunc σ N (x - y) - kernelTrunc σ N x‖ ≤ cH * B * |y| / x ^ 2 := by
  obtain ⟨hsum', hle⟩ := summable_majorant_sub_le (y := y) hB hx
  have hdom := fun j : ℤ => norm_kernelPiece_sub_le hσ hB j hx hy
  rw [kernelTrunc_eq_sum hσ, kernelTrunc_eq_sum hσ, ← Finset.sum_sub_distrib]
  calc ‖∑ j ∈ Finset.Icc (-(N : ℤ)) N, (kernelPiece σ j (x - y) - kernelPiece σ j x)‖
      ≤ ∑ j ∈ Finset.Icc (-(N : ℤ)) N, ‖kernelPiece σ j (x - y) - kernelPiece σ j x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.Icc (-(N : ℤ)) N, |y| * min ((8 * Real.pi * B * c₀' * σ₀ / |x|) * (2 : ℝ) ^ j)
        ((8 * B * c₃' / (Real.pi ^ 2 * |x| ^ 3)) * (2 : ℝ) ^ (-j)) :=
        Finset.sum_le_sum fun j _ => hdom j
    _ ≤ ∑' j : ℤ, |y| * min ((8 * Real.pi * B * c₀' * σ₀ / |x|) * (2 : ℝ) ^ j)
        ((8 * B * c₃' / (Real.pi ^ 2 * |x| ^ 3)) * (2 : ℝ) ^ (-j)) :=
        hsum'.sum_le_tsum _ (fun j _ => by
          have hxa : 0 < |x| := abs_pos.2 hx
          have hπ := Real.pi_pos
          have hc0 := one_le_c₀'
          have hc3 := one_le_c₃'
          have hσ1 := one_le_σ₀
          exact mul_nonneg (abs_nonneg _) (le_min (by positivity) (by positivity)))
    _ ≤ _ := hle

/-- **Hörmander condition from a pointwise smoothness bound**: any `Kf` with
`|Kf(x - y) - Kf(x)| ≤ c |y| / x²` for `2|y| ≤ |x|` satisfies
`∫_{|x| > 2|y|} |Kf(x - y) - Kf(x)| dx ≤ c`. -/
theorem lintegral_sub_le_of_pointwise {Kf : ℝ → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x y : ℝ, x ≠ 0 → 2 * |y| ≤ |x| → ‖Kf (x - y) - Kf x‖ ≤ c * |y| / x ^ 2) (y : ℝ) :
    ∫⁻ x in {x : ℝ | 2 * |y| < |x|}, ‖Kf (x - y) - Kf x‖ₑ ≤ ENNReal.ofReal c := by
  by_cases hy : y = 0
  · subst hy
    simp
  have hy0 : 0 < |y| := abs_pos.2 hy
  have hset : MeasurableSet {x : ℝ | 2 * |y| < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  calc ∫⁻ x in {x : ℝ | 2 * |y| < |x|}, ‖Kf (x - y) - Kf x‖ₑ
      ≤ ∫⁻ x in {x : ℝ | 2 * |y| < |x|}, ENNReal.ofReal (c * |y|) *
          ENNReal.ofReal (1 / x ^ 2) := by
        refine setLIntegral_mono' hset fun x hx => ?_
        have hx' : 2 * |y| < |x| := hx
        have hx0 : x ≠ 0 := by
          intro h0; rw [h0, abs_zero] at hx'; linarith
        have := h x y hx0 hx'.le
        rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal (this.trans (le_of_eq ?_))
        field_simp
    _ = ENNReal.ofReal (c * |y|) *
          ∫⁻ x in {x : ℝ | 2 * |y| < |x|}, ENNReal.ofReal (1 / x ^ 2) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal c := by
        rw [lintegral_tail_inv_sq (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-- The Hörmander condition for the truncated kernels, **uniform in `N`**. -/
theorem lintegral_kernelTrunc_sub_le (hσ : IsMikhlin 3 B σ) (hB : 0 < B) (N : ℕ) (y : ℝ) :
    ∫⁻ x in {x : ℝ | 2 * |y| < |x|}, ‖kernelTrunc σ N (x - y) - kernelTrunc σ N x‖ₑ ≤
      ENNReal.ofReal (cH * B) := by
  have hcH : 0 ≤ cH := by unfold cH; positivity
  exact lintegral_sub_le_of_pointwise (by positivity)
    (fun x y hx hy => norm_kernelTrunc_sub_le hσ hB hx hy N) y

/-! ## `T_p h = 𝓕⁻p * h` (Fubini), the `L²` bound, convergence of the truncations -/

theorem norm_exp_real_mul_I (t : ℝ) : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp_ofReal_mul_I]

theorem multOp_eq_integral_fourierInv {p g : ℝ → ℂ} (hp : Integrable p volume)
    (hg : Integrable g volume) (x : ℝ) :
    multOp p g x = ∫ y, 𝓕⁻ p (x - y) * g y := by
  unfold multOp
  simp only [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  set E : ℝ → ℝ → ℂ := fun ξ y => Complex.exp (↑(-2 * π * ξ * (-(x - y))) * Complex.I) with hE
  have hint : Integrable (Function.uncurry fun (ξ y : ℝ) => E ξ y * p ξ * g y)
      (volume.prod volume) := by
    refine (Integrable.mul_prod hp.norm hg.norm).mono' ?_ ?_
    · have hc : Continuous (Function.uncurry E) := by
        simp only [hE]
        fun_prop
      exact ((hc.aestronglyMeasurable).mul (hp.1.comp_fst)).mul (hg.1.comp_snd)
    · refine Eventually.of_forall fun z => ?_
      simp only [Function.uncurry, hE, norm_mul, norm_exp_real_mul_I, one_mul]
      exact le_rfl
  have h1 : ∀ ξ : ℝ, Complex.exp (↑(-2 * π * ξ * (-x)) * Complex.I) *
      (p ξ * ∫ y, Complex.exp (↑(-2 * π * y * ξ) * Complex.I) * g y) =
      ∫ y, E ξ y * p ξ * g y := by
    intro ξ
    rw [← integral_const_mul, ← integral_const_mul]
    congr 1
    ext y
    simp only [hE]
    rw [show Complex.exp (↑(-2 * π * ξ * (-(x - y))) * Complex.I) =
        Complex.exp (↑(-2 * π * ξ * (-x)) * Complex.I) *
          Complex.exp (↑(-2 * π * y * ξ) * Complex.I) by
      rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  have h2 : ∀ y : ℝ, (∫ ξ, Complex.exp (↑(-2 * π * ξ * (-(x - y))) * Complex.I) * p ξ) * g y =
      ∫ ξ, E ξ y * p ξ * g y := by
    intro y
    rw [← integral_mul_const]
  simp_rw [h1, h2]
  exact integral_integral_swap hint

theorem eLpNorm_neg_comp (h : ℝ → ℂ) (hm : AEStronglyMeasurable h volume) :
    eLpNorm (fun x => h (-x)) 2 volume = eLpNorm h 2 volume :=
  eLpNorm_comp_measurePreserving (g := h) (f := fun x : ℝ => -x) (p := 2) hm
    (Measure.measurePreserving_neg volume)

theorem eLpNorm_fourier_eq_of_integrable (h : ℝ → ℂ) (h1 : Integrable h volume)
    (h2 : MemLp h 2 volume) : eLpNorm (𝓕 h) 2 volume = eLpNorm h 2 volume := by
  have e : 𝓕 h = 𝓕⁻ (fun x => h (-x)) := by
    rw [Real.fourierInv_eq_fourier_comp_neg]
    simp
  have hneg1 : Integrable (fun x => h (-x)) volume := h1.comp_neg
  have hm : AEStronglyMeasurable h volume := h2.aestronglyMeasurable
  have hneg2 : MemLp (fun x => h (-x)) 2 volume := by
    unfold MemLp
    rw [eLpNorm_neg_comp h hm]
    exact h2
  rw [e, eLpNorm_fourierInv_eq_of_integrable _ hneg1 hneg2, eLpNorm_neg_comp h hm]

/-- `‖T_p h‖₂ ≤ B ‖h‖₂` for `h ∈ L¹ ∩ L²` and `p` integrable and bounded by `B`. -/
theorem eLpNorm_multOp_two_le_of_integrable {B : ℝ} {p h : ℝ → ℂ} (hp : IsBoundedSymbol B p)
    (hpi : Integrable p volume) (h1 : Integrable h volume) (h2 : MemLp h 2 volume) :
    eLpNorm (multOp p h) 2 volume ≤ ENNReal.ofReal B * eLpNorm h 2 volume := by
  have hbd : ∀ w, ‖𝓕 h w‖ ≤ ∫ v, ‖h v‖ := fun w => Real.norm_fourier_le_integral_norm h w
  have hcont : AEStronglyMeasurable (𝓕 h) volume := by
    have : Continuous (𝓕 h) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner h1
    exact this.aestronglyMeasurable
  have hint : Integrable (fun ξ => p ξ * 𝓕 h ξ) volume :=
    hpi.mul_bdd hcont (Eventually.of_forall hbd)
  have hF : AEStronglyMeasurable (fun ξ => p ξ * 𝓕 h ξ) volume := hint.aestronglyMeasurable
  have hB : eLpNorm (fun ξ => p ξ * 𝓕 h ξ) 2 volume ≤ ENNReal.ofReal B * eLpNorm h 2 volume := by
    rw [← eLpNorm_fourier_eq_of_integrable h h1 h2]
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul hF ?_ 2
    filter_upwards [hp.ae_norm_le] with ξ hξ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hξ (norm_nonneg _)
  have hlt : ENNReal.ofReal B * eLpNorm h 2 volume < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2
  have hL2 : MemLp (fun ξ => p ξ * 𝓕 h ξ) 2 volume := lt_of_le_of_lt hB hlt
  unfold multOp
  rw [eLpNorm_fourierInv_eq_of_integrable _ hint hL2]
  exact hB

theorem tendsto_multOp_symbolTrunc (hσ : IsMikhlin 3 B σ) (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Tendsto (fun N : ℕ => multOp (symbolTrunc σ N) (⇑g) x) atTop (𝓝 (multOp σ (⇑g) x)) := by
  have hb := hσ.isBoundedSymbol
  have hint : Integrable (𝓕 (⇑g)) volume := by
    have h : Integrable (⇑(𝓕 g : 𝓢(ℝ, ℂ))) volume := (𝓕 g : 𝓢(ℝ, ℂ)).integrable
    rwa [SchwartzMap.fourier_coe] at h
  have hcont : Continuous (𝓕 (⇑g)) := by
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner
      g.integrable
  have hm : ∀ (p : ℝ → ℂ), multOp p (⇑g) x =
      ∫ ξ, Complex.exp (↑(-2 * π * ξ * (-x)) * Complex.I) * (p ξ * 𝓕 (⇑g) ξ) := by
    intro p
    unfold multOp
    rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
    simp only [smul_eq_mul]
  simp only [hm]
  refine tendsto_integral_of_dominated_convergence (fun ξ => 2 * B * ‖𝓕 (⇑g) ξ‖) ?_ ?_ ?_ ?_
  · intro N
    have hs := (isBoundedSymbol_symbolTrunc hσ N).aestronglyMeasurable
    have hc : Continuous fun ξ : ℝ => Complex.exp (↑(-2 * π * ξ * (-x)) * Complex.I) := by
      fun_prop
    exact hc.aestronglyMeasurable.mul (hs.mul hcont.aestronglyMeasurable)
  · exact hint.norm.const_mul _
  · intro N
    filter_upwards [(isBoundedSymbol_symbolTrunc hσ N).ae_norm_le] with ξ hξ
    rw [norm_mul, norm_exp_real_mul_I, one_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right hξ (norm_nonneg _)
  · have hne : ∀ᵐ ξ ∂(volume : Measure ℝ), ξ ≠ 0 := by simp [ae_iff]
    filter_upwards [hne] with ξ hξ
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_PsiN_eq_one hξ] with N hN
    simp [symbolTrunc, hN]

end PrimeBHT.TimeFrequency.X2.CZ
