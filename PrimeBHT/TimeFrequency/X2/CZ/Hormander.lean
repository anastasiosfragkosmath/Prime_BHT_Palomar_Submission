module

public import PrimeBHT.TimeFrequency.X2.CZ.Pieces
public import PrimeBHT.TimeFrequency.X2.CZ.DyadicSum

/-!
# V08: the kernel of a Mikhlin multiplier and the Hörmander condition

`σ ∈ IsMikhlin 3 B`.  With the dyadic partition of unity of `Dyadic.lean` and the pieces of
`Pieces.lean`, the kernel `K = ∑_j K_j`, `K_j = 𝓕⁻(σ ψ(2^{-j}·))`, satisfies, with constants depending
only on the fixed bump `ψ`,

* `norm_kernelPiece_le_min`: `|K_j(x)| ≤ min(a 2^j, b_x 2^{-j})`, `a = 4 B c₀`, `b_x = 4 B c₂/(2π|x|)²`;
* `norm_deriv_kernelPiece_le_min`: `|K_j'(t)| ≤ min(α 4^j, κ|t|^{-3} 2^{-j})`;
* `norm_kernelSum_le`: `|K(x)| ≤ C B / |x|` (series over `j ∈ ℤ`, absolutely summable);
* `norm_kernelSum_sub_le`: `|K(x - y) - K(x)| ≤ C B |y| / x²` for `2|y| ≤ |x|`;
* `lintegral_kernelSum_sub_le`: the **Hörmander condition**
  `∫_{|x| > 2|y|} |K(x - y) - K(x)| dx ≤ C B`.

All constants are independent of `σ`, `B`, `x`, `y`.
-/

@[expose] public section

open MeasureTheory Set
open scoped FourierTransform ContDiff ENNReal

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

/-- The dyadic bump as a complex-valued function. -/
noncomputable def psiC : ℝ → ℂ := fun t => ((dyadicPsi t : ℝ) : ℂ)

theorem annulusBump_psiC : AnnulusBump psiC := annulusBump_dyadicPsi

/-- `t ψ(t)`. -/
noncomputable def psiC₁ : ℝ → ℂ := fun t => (t : ℂ) * psiC t

theorem annulusBump_psiC₁ : AnnulusBump psiC₁ := annulusBump_psiC.mul_id

/-- The constants (all `≥ 1`, depending only on `ψ`). -/
noncomputable def c₀ : ℝ := annulusBump_psiC.pieceConst 0 + 1
noncomputable def c₂ : ℝ := annulusBump_psiC.pieceConst 2 + 1
noncomputable def c₀' : ℝ := annulusBump_psiC₁.pieceConst 0 + 1
noncomputable def c₃' : ℝ := annulusBump_psiC₁.pieceConst 3 + 1

theorem one_le_c₀' : 1 ≤ c₀' := by unfold c₀'; linarith [annulusBump_psiC₁.pieceConst_nonneg 0]
theorem one_le_c₃' : 1 ≤ c₃' := by unfold c₃'; linarith [annulusBump_psiC₁.pieceConst_nonneg 3]

variable {σ : ℝ → ℂ} {B r : ℝ}

/-- `K_r = 𝓕⁻(σ ψ(r·))`. -/
noncomputable def kernelAt (σ : ℝ → ℂ) (r : ℝ) : ℝ → ℂ := 𝓕⁻ (piece psiC σ r)

/-- `K^{(1)}_r = 𝓕⁻(σ · (tψ)(r·))`: the kernel of the piece with the bump `tψ`; `K_r' = (2πi/r) K^{(1)}_r`. -/
noncomputable def kernelAt₁ (σ : ℝ → ℂ) (r : ℝ) : ℝ → ℂ := 𝓕⁻ (piece psiC₁ σ r)

theorem hasDerivAt_kernelAt (hσ : IsMikhlin 3 B σ) (hr : 0 < r) (x : ℝ) :
    HasDerivAt (kernelAt σ r) ((2 * Real.pi * Complex.I / r) * kernelAt₁ σ r x) x :=
  hasDerivAt_fourierInv_piece hσ annulusBump_psiC hr x

theorem norm_kernelAt₁_le_zero (hσ : IsMikhlin 3 B σ) (hr : 0 < r) (x : ℝ) :
    ‖kernelAt₁ σ r x‖ ≤ 4 * B * c₀' / r := by
  have h := norm_fourierInv_piece_le hσ annulusBump_psiC₁ hr (k := 0) (by norm_num) x
  simp only [pow_zero, one_mul, mul_one] at h
  have : 4 / r * (B * annulusBump_psiC₁.pieceConst 0) ≤ 4 * B * c₀' / r := by
    unfold c₀'
    have := hσ.nonneg
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hr]
    nlinarith
  exact h.trans this

theorem norm_kernelAt₁_le_three (hσ : IsMikhlin 3 B σ) (hr : 0 < r) (x : ℝ) :
    (2 * Real.pi * |x|) ^ 3 * ‖kernelAt₁ σ r x‖ ≤ 4 * B * c₃' * r ^ 2 := by
  have h := norm_fourierInv_piece_le hσ annulusBump_psiC₁ hr (k := 3) (by norm_num) x
  have : 4 / r * (B * annulusBump_psiC₁.pieceConst 3 * r ^ 3) ≤ 4 * B * c₃' * r ^ 2 := by
    unfold c₃'
    have := hσ.nonneg
    have hC := annulusBump_psiC₁.pieceConst_nonneg 3
    have e : 4 / r * (B * annulusBump_psiC₁.pieceConst 3 * r ^ 3) =
        4 * B * annulusBump_psiC₁.pieceConst 3 * r ^ 2 := by field_simp
    rw [e]
    nlinarith [mul_nonneg this (sq_nonneg r)]
  exact h.trans this

/-- Derivative of a kernel piece: `|K_r'(x)| ≤ 8π B c₀' / r²`. -/
theorem norm_deriv_kernelAt_le_zero (hσ : IsMikhlin 3 B σ) (hr : 0 < r) (x : ℝ) :
    ‖deriv (kernelAt σ r) x‖ ≤ 8 * Real.pi * B * c₀' / r ^ 2 := by
  rw [(hasDerivAt_kernelAt hσ hr x).deriv, norm_mul]
  have h1 : ‖(2 * Real.pi * Complex.I / r : ℂ)‖ = 2 * Real.pi / r := by
    rw [norm_div, norm_mul, norm_mul]
    simp [abs_of_pos hr, abs_of_pos Real.pi_pos]
  rw [h1]
  calc 2 * Real.pi / r * ‖kernelAt₁ σ r x‖ ≤ 2 * Real.pi / r * (4 * B * c₀' / r) :=
        mul_le_mul_of_nonneg_left (norm_kernelAt₁_le_zero hσ hr x) (by positivity)
    _ = 8 * Real.pi * B * c₀' / r ^ 2 := by field_simp; ring

/-- Derivative of a kernel piece: `(2π|x|)³ |K_r'(x)| ≤ 8π B c₃' r`. -/
theorem norm_deriv_kernelAt_le_three (hσ : IsMikhlin 3 B σ) (hr : 0 < r) (x : ℝ) :
    (2 * Real.pi * |x|) ^ 3 * ‖deriv (kernelAt σ r) x‖ ≤ 8 * Real.pi * B * c₃' * r := by
  rw [(hasDerivAt_kernelAt hσ hr x).deriv, norm_mul]
  have h1 : ‖(2 * Real.pi * Complex.I / r : ℂ)‖ = 2 * Real.pi / r := by
    rw [norm_div, norm_mul, norm_mul]
    simp [abs_of_pos hr, abs_of_pos Real.pi_pos]
  rw [h1]
  calc (2 * Real.pi * |x|) ^ 3 * (2 * Real.pi / r * ‖kernelAt₁ σ r x‖)
      = 2 * Real.pi / r * ((2 * Real.pi * |x|) ^ 3 * ‖kernelAt₁ σ r x‖) := by ring
    _ ≤ 2 * Real.pi / r * (4 * B * c₃' * r ^ 2) :=
        mul_le_mul_of_nonneg_left (norm_kernelAt₁_le_three hσ hr x) (by positivity)
    _ = 8 * Real.pi * B * c₃' * r := by field_simp; ring

/-! ## The kernel pieces at dyadic scales `r = 2^{-j}` -/

/-- The `j`-th dyadic piece of the kernel `K = 𝓕⁻σ`: `K_j = 𝓕⁻(σ ψ(2^{-j}·))`. -/
noncomputable def kernelPiece (σ : ℝ → ℂ) (j : ℤ) : ℝ → ℂ := kernelAt σ ((2 : ℝ) ^ (-j))

theorem two_zpow_neg_pos (j : ℤ) : (0 : ℝ) < (2 : ℝ) ^ (-j) := zpow_pos (by norm_num) _

/-- The crossover constant for the derivative bound. -/
noncomputable def σ₀ : ℝ := max 1 (c₃' / (Real.pi ^ 3 * c₀'))

theorem one_le_σ₀ : 1 ≤ σ₀ := le_max_left _ _

/-- **Derivative of a kernel piece** at a point `t` with `|t| ≥ |x|/2`:
`|K_j'(t)| ≤ min(a 2^j, g 2^{-j})`, `a = 8π B c₀' σ₀ / |x|`, `g = 8 B c₃' / (π² |x|³)`. -/
theorem norm_deriv_kernelPiece_le_min (hσ : IsMikhlin 3 B σ) (hB : 0 < B) (j : ℤ) {x t : ℝ}
    (hx : x ≠ 0) (ht : |x| / 2 ≤ |t|) :
    ‖deriv (kernelPiece σ j) t‖ ≤
      min ((8 * Real.pi * B * c₀' * σ₀ / |x|) * (2 : ℝ) ^ j)
        ((8 * B * c₃' / (Real.pi ^ 2 * |x| ^ 3)) * (2 : ℝ) ^ (-j)) := by
  have hxa : 0 < |x| := abs_pos.2 hx
  have hπ := Real.pi_pos
  have hr := two_zpow_neg_pos j
  have hu : (0 : ℝ) < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hc0 := one_le_c₀'
  have hc3 := one_le_c₃'
  set u : ℝ := (2 : ℝ) ^ j with hu_def
  have hru : (2 : ℝ) ^ (-j) = u⁻¹ := by rw [hu_def, zpow_neg]
  -- the two basic bounds
  have h0 : ‖deriv (kernelPiece σ j) t‖ ≤ 8 * Real.pi * B * c₀' * u ^ 2 := by
    have := norm_deriv_kernelAt_le_zero hσ hr t
    have e : 8 * Real.pi * B * c₀' / ((2 : ℝ) ^ (-j)) ^ 2 = 8 * Real.pi * B * c₀' * u ^ 2 := by
      rw [hru, inv_pow, div_inv_eq_mul]
    unfold kernelPiece
    rw [← e]; exact this
  have h3 : ‖deriv (kernelPiece σ j) t‖ ≤ 8 * B * c₃' / (Real.pi ^ 2 * |x| ^ 3) * u⁻¹ := by
    have h := norm_deriv_kernelAt_le_three hσ hr t
    have hpos : 0 < 2 * Real.pi * |t| := by
      have : 0 < |t| := lt_of_lt_of_le (by positivity) ht
      positivity
    have hlow : Real.pi * |x| ≤ 2 * Real.pi * |t| := by nlinarith
    have hpow : (Real.pi * |x|) ^ 3 ≤ (2 * Real.pi * |t|) ^ 3 := by gcongr
    have hpx : 0 < (Real.pi * |x|) ^ 3 := by positivity
    have hnn := norm_nonneg (deriv (kernelPiece σ j) t)
    unfold kernelPiece at hnn ⊢
    rw [hru] at h
    have h' : (Real.pi * |x|) ^ 3 * ‖deriv (kernelAt σ u⁻¹) t‖ ≤ 8 * Real.pi * B * c₃' * u⁻¹ :=
      le_trans (by gcongr) h
    rw [hru]
    calc ‖deriv (kernelAt σ u⁻¹) t‖ ≤ 8 * Real.pi * B * c₃' * u⁻¹ / (Real.pi * |x|) ^ 3 := by
          rw [le_div_iff₀ hpx]; linarith
      _ = 8 * B * c₃' / (Real.pi ^ 2 * |x| ^ 3) * u⁻¹ := by field_simp
  rw [hru]
  refine le_min ?_ h3
  -- the crossover
  have hσ1 := one_le_σ₀
  set S : ℝ := σ₀ / |x| with hS
  have hSpos : 0 < S := by positivity
  have hkey : 8 * B * c₃' / (Real.pi ^ 2 * |x| ^ 3) ≤
      8 * Real.pi * B * c₀' * S ^ 3 := by
    have hσ3 : c₃' / (Real.pi ^ 3 * c₀') ≤ σ₀ ^ 3 := by
      calc c₃' / (Real.pi ^ 3 * c₀') ≤ σ₀ := le_max_right _ _
        _ ≤ σ₀ ^ 3 := by nlinarith [sq_nonneg σ₀]
    rw [div_le_iff₀ (by positivity)] at hσ3
    rw [hS, div_pow]
    have : 8 * Real.pi * B * c₀' * (σ₀ ^ 3 / |x| ^ 3) =
        8 * Real.pi * B * c₀' * σ₀ ^ 3 / |x| ^ 3 := by ring
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    have h8 : 0 ≤ 8 * B * |x| ^ 3 := by positivity
    calc 8 * B * c₃' * |x| ^ 3 = (8 * B * |x| ^ 3) * c₃' := by ring
      _ ≤ (8 * B * |x| ^ 3) * (σ₀ ^ 3 * (Real.pi ^ 3 * c₀')) := mul_le_mul_of_nonneg_left hσ3 h8
      _ = 8 * Real.pi * B * c₀' * σ₀ ^ 3 * (Real.pi ^ 2 * |x| ^ 3) := by ring
  by_cases hcase : u ≤ S
  · calc ‖deriv (kernelPiece σ j) t‖ ≤ 8 * Real.pi * B * c₀' * u ^ 2 := h0
      _ ≤ 8 * Real.pi * B * c₀' * σ₀ / |x| * u := by
          rw [mul_div_assoc, ← hS]
          have hcc : 0 ≤ 8 * Real.pi * B * c₀' := by positivity
          calc 8 * Real.pi * B * c₀' * u ^ 2 = 8 * Real.pi * B * c₀' * (u * u) := by ring
            _ ≤ 8 * Real.pi * B * c₀' * (S * u) := by gcongr
            _ = 8 * Real.pi * B * c₀' * S * u := by ring
  · rw [not_le] at hcase
    calc ‖deriv (kernelPiece σ j) t‖ ≤ 8 * B * c₃' / (Real.pi ^ 2 * |x| ^ 3) * u⁻¹ := h3
      _ ≤ 8 * Real.pi * B * c₀' * S ^ 3 * u⁻¹ := by gcongr
      _ ≤ 8 * Real.pi * B * c₀' * σ₀ / |x| * u := by
          have hS3 : S ^ 3 * u⁻¹ ≤ S * u := by
            rw [← div_eq_mul_inv, div_le_iff₀ hu]
            nlinarith [mul_pos hSpos hSpos, mul_pos hSpos hu]
          rw [mul_div_assoc, ← hS]
          have hcc : 0 ≤ 8 * Real.pi * B * c₀' := by positivity
          calc 8 * Real.pi * B * c₀' * S ^ 3 * u⁻¹ = 8 * Real.pi * B * c₀' * (S ^ 3 * u⁻¹) := by ring
            _ ≤ 8 * Real.pi * B * c₀' * (S * u) := by gcongr
            _ = 8 * Real.pi * B * c₀' * S * u := by ring

theorem differentiableAt_kernelPiece (hσ : IsMikhlin 3 B σ) (j : ℤ) (t : ℝ) :
    DifferentiableAt ℝ (kernelPiece σ j) t :=
  (hasDerivAt_kernelAt hσ (two_zpow_neg_pos j) t).differentiableAt

/-- Mean value estimate for one kernel piece, `2|y| ≤ |x|`:
`|K_j(x - y) - K_j(x)| ≤ |y| min(a 2^j, g 2^{-j})`. -/
theorem norm_kernelPiece_sub_le (hσ : IsMikhlin 3 B σ) (hB : 0 < B) (j : ℤ) {x y : ℝ}
    (hx : x ≠ 0) (hy : 2 * |y| ≤ |x|) :
    ‖kernelPiece σ j (x - y) - kernelPiece σ j x‖ ≤
      |y| * min ((8 * Real.pi * B * c₀' * σ₀ / |x|) * (2 : ℝ) ^ j)
        ((8 * B * c₃' / (Real.pi ^ 2 * |x| ^ 3)) * (2 : ℝ) ^ (-j)) := by
  have hmem : ∀ t ∈ uIcc (x - y) x, |x| / 2 ≤ |t| := by
    intro t ht
    have h1 : |x - t| ≤ |x - (x - y)| := Set.abs_sub_right_of_mem_uIcc ht
    have h2 : |x - (x - y)| = |y| := by rw [sub_sub_cancel]
    have h3 : |x| - |t| ≤ |x - t| := abs_sub_abs_le_abs_sub x t
    linarith
  have := (convex_uIcc (x - y) x).norm_image_sub_le_of_norm_deriv_le
    (f := kernelPiece σ j)
    (C := min ((8 * Real.pi * B * c₀' * σ₀ / |x|) * (2 : ℝ) ^ j)
        ((8 * B * c₃' / (Real.pi ^ 2 * |x| ^ 3)) * (2 : ℝ) ^ (-j)))
    (fun t _ => differentiableAt_kernelPiece hσ j t)
    (fun t ht => norm_deriv_kernelPiece_le_min hσ hB j hx (hmem t ht))
    right_mem_uIcc left_mem_uIcc
  have e : ‖x - y - x‖ = |y| := by rw [sub_sub_cancel_left, norm_neg, Real.norm_eq_abs]
  rw [e] at this
  linarith [this]

/-- The constant of the Hörmander smoothness estimate. -/
noncomputable def cH : ℝ := 32 * Real.sqrt (c₀' * c₃' * σ₀ / Real.pi)

/-- The dyadic majorant of the mean value estimate: for `2|y| ≤ |x|`, `x ≠ 0` it is summable over `j`
and its sum is at most `cH B |y| / x²`.  (Used for `kernelSum` and for every partial sum of it.) -/
theorem summable_majorant_sub_le (hB : 0 < B) {x y : ℝ} (hx : x ≠ 0) :
    Summable (fun j : ℤ => |y| * min ((8 * Real.pi * B * c₀' * σ₀ / |x|) * (2 : ℝ) ^ j)
        ((8 * B * c₃' / (Real.pi ^ 2 * |x| ^ 3)) * (2 : ℝ) ^ (-j))) ∧
      ∑' j : ℤ, |y| * min ((8 * Real.pi * B * c₀' * σ₀ / |x|) * (2 : ℝ) ^ j)
        ((8 * B * c₃' / (Real.pi ^ 2 * |x| ^ 3)) * (2 : ℝ) ^ (-j)) ≤ cH * B * |y| / x ^ 2 := by
  have hxa : 0 < |x| := abs_pos.2 hx
  have hπ := Real.pi_pos
  have hc0 := one_le_c₀'
  have hc3 := one_le_c₃'
  have hσ1 := one_le_σ₀
  have ha : 0 < 8 * Real.pi * B * c₀' * σ₀ / |x| := by positivity
  have hg : 0 < 8 * B * c₃' / (Real.pi ^ 2 * |x| ^ 3) := by positivity
  obtain ⟨hsum, hle⟩ := hasSum_le_min_two_zpow ha hg
  refine ⟨hsum.mul_left _, ?_⟩
  rw [tsum_mul_left]
  have e : 8 * Real.pi * B * c₀' * σ₀ / |x| * (8 * B * c₃' / (Real.pi ^ 2 * |x| ^ 3)) =
      (8 * B / |x| ^ 2) ^ 2 * (c₀' * c₃' * σ₀ / Real.pi) := by
    field_simp
  have hs4 : 4 * Real.sqrt (8 * Real.pi * B * c₀' * σ₀ / |x| *
      (8 * B * c₃' / (Real.pi ^ 2 * |x| ^ 3))) = 32 * Real.sqrt (c₀' * c₃' * σ₀ / Real.pi) *
        B / x ^ 2 := by
    rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), ← sq_abs x]
    field_simp
    ring
  calc |y| * ∑' j : ℤ, min ((8 * Real.pi * B * c₀' * σ₀ / |x|) * (2 : ℝ) ^ j)
        ((8 * B * c₃' / (Real.pi ^ 2 * |x| ^ 3)) * (2 : ℝ) ^ (-j))
      ≤ |y| * (4 * Real.sqrt (8 * Real.pi * B * c₀' * σ₀ / |x| *
          (8 * B * c₃' / (Real.pi ^ 2 * |x| ^ 3)))) :=
        mul_le_mul_of_nonneg_left hle (abs_nonneg y)
    _ = cH * B * |y| / x ^ 2 := by rw [hs4]; unfold cH; ring

/-! ## The Hörmander integral condition -/

theorem lintegral_Ioi_inv_sq {a : ℝ} (ha : 0 < a) :
    ∫⁻ x in Ioi a, ENNReal.ofReal (1 / x ^ 2) = ENNReal.ofReal (1 / a) := by
  have hint : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) ha
  have h1 : ∫⁻ x in Ioi a, ENNReal.ofReal (x ^ (-2 : ℝ)) = ENNReal.ofReal (1 / a) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint]
    · rw [integral_Ioi_rpow_of_lt (by norm_num) ha]
      congr 1
      norm_num
      exact Real.rpow_neg_one a
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact Real.rpow_nonneg (ha.le.trans (le_of_lt hx)) _
  rw [← h1]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : 0 < x := ha.trans hx
  rw [Real.rpow_neg hx0.le, Real.rpow_two, one_div]

theorem lintegral_tail_inv_sq {a : ℝ} (ha : 0 < a) :
    ∫⁻ x in {x : ℝ | a < |x|}, ENNReal.ofReal (1 / x ^ 2) = ENNReal.ofReal (2 / a) := by
  have hset : {x : ℝ | a < |x|} = Ioi a ∪ Iio (-a) := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_union, mem_Ioi, mem_Iio, lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · right; linarith
    · rintro (h | h)
      · exact Or.inl h
      · right; linarith
  have hdisj : Disjoint (Ioi a) (Iio (-a)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [mem_Ioi, mem_Iio] at hx hx'
    linarith
  rw [hset, lintegral_union measurableSet_Iio hdisj]
  have hneg : ∫⁻ x in Iio (-a), ENNReal.ofReal (1 / x ^ 2) =
      ∫⁻ x in Ioi a, ENNReal.ofReal (1 / x ^ 2) := by
    rw [← lintegral_indicator measurableSet_Iio, ← lintegral_indicator measurableSet_Ioi,
      ← lintegral_neg_eq_self]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Ioi a
    · have : -x ∈ Iio (-a) := by simp only [mem_Iio, mem_Ioi] at hx ⊢; linarith
      rw [indicator_of_mem hx, indicator_of_mem this]
      simp
    · have : -x ∉ Iio (-a) := by simp only [mem_Iio, mem_Ioi, not_lt] at hx ⊢; linarith
      rw [indicator_of_notMem hx, indicator_of_notMem this]
  rw [hneg, lintegral_Ioi_inv_sq ha, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end PrimeBHT.TimeFrequency.X2.CZ
