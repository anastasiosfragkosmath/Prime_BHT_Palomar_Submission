module

public import PrimeBHT.TimeFrequency.X2.Assembly
public import PrimeBHT.TimeFrequency.X2.Disc.Assemble
public import PrimeBHT.TimeFrequency.X2.Disc.Params

/-!
# X2, node V05 (R4-5): `discretization : DiscretizationStatement`

The assembly of the discretization: `𝔭 = discPar N D`, the V04/R1 decomposition `Σ_{(k,n)} c_{k,n} wPieceForm (k,n) = multiplierForm`,
`wPieceForm (k,n) = Σ_{pairs} pairTerm` (`hasSum_pairTerm`), the bound of every finite double sum
(`finite_bound`, which partitions into fibres and applies the model bound), and the limit over finite sets.
Constant: `CdV = 2 |Slab| Σ_n B_n Q_a(n)² Q_c`.
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

open Disc

theorem Disc.Xn_le (n : ℤ) : Xn n ≤ 4 * (1 + |(n : ℝ)|) := by
  unfold Xn
  have : π * |(n : ℝ)| / 512 ≤ |(n : ℝ)| := by
    have := Real.pi_le_four
    nlinarith [abs_nonneg (n : ℝ)]
  linarith

/-- **V05: the discretization.** -/
theorem discretization : DiscretizationStatement := by
  intro N D₀
  -- the class `discPar N D` with `D ≥ 2N + 403` carries the margin `N/8 + 3 ≤ D` of `ProfileOK`
  set D : ℕ := max D₀ (2 * N + 403) with hDdef
  have hD₀ : D₀ ≤ D := le_max_left _ _
  have hDge : 2 * N + 403 ≤ D := le_max_right _ _
  obtain ⟨hadm, hN, hD, hJ, hβ, -, -, ⟨η, hη, hX⟩, hprof⟩ := discretization_params_good N D
  have hmargin : (discPar N D).N / 8 + 3 ≤ (discPar N D).D := by
    rw [discPar_N_div8, discPar_D]; omega
  refine ⟨discPar N D, hadm, hN, hD₀.trans hD, ⟨hprof, hmargin⟩, ?_⟩
  intro u hu A
  set 𝔭 : Params := discPar N D with h𝔭
  have hC : 0 < 𝔭.C := lt_of_lt_of_le one_pos hadm.2.2.2.2.2.2.2
  obtain ⟨M₁, h₁, hI₁⟩ := exists_IMStmt contDiff_wphi hasCompactSupport_wphi (-1 / 2) (3 / 2)
    (fun x hx => wphi_ne_zero hx) 𝔭 hβ
  obtain ⟨M₃, h₃, hI₃⟩ := exists_IMStmt contDiff_wphi3 hasCompactSupport_wphi3 (-3 / 2) (7 / 2)
    (fun x hx => wphi3_ne_zero hx) 𝔭 hβ
  obtain ⟨CV, hCV0, hCV⟩ := exists_whitney_decomposition_form
  set NA : ℕ := 2 * 𝔭.D + 2 with hNA
  set SA : ℝ := ∑ j ∈ Finset.range (NA + 1), A j with hSA
  set b0 : ℝ := |CV NA * SA| + 1 with hb0
  have hb0pos : 0 < b0 := by positivity
  set Bn : ℤ → ℝ := fun n => b0 / (1 + |(n : ℝ)|) ^ NA with hBn
  have hBnpos : ∀ n, 0 < Bn n := fun n => by simp only [hBn]; positivity
  set w : ℤ → ℝ := fun n => Bn n * Qa 𝔭 M₁ n * Qa 𝔭 M₁ n * Qc 𝔭 M₃ with hwdef
  have hQa0 := fun n => Qa_pos hC h₁ n
  have hQc0 := Qc_pos hC h₃
  have hw0 : ∀ n, 0 ≤ w n := fun n =>
    mul_nonneg (mul_nonneg (mul_nonneg (hBnpos n).le (hQa0 n).le) (hQa0 n).le) hQc0.le
  -- summability of w
  set a : ℝ := (M₁ + 1) * 4 ^ 𝔭.D / 𝔭.C with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have hQale : ∀ n : ℤ, Qa 𝔭 M₁ n ≤ a * (1 + |(n : ℝ)|) ^ 𝔭.D := by
    intro n
    unfold Qa
    have h1 : Xn n ^ 𝔭.D ≤ (4 * (1 + |(n : ℝ)|)) ^ 𝔭.D := pow_le_pow_left₀ (Xn_pos n).le (Disc.Xn_le n) _
    rw [ha, mul_pow] at *
    calc (M₁ + 1) * Xn n ^ 𝔭.D / 𝔭.C ≤ (M₁ + 1) * (4 ^ 𝔭.D * (1 + |(n : ℝ)|) ^ 𝔭.D) / 𝔭.C := by
          gcongr
      _ = (M₁ + 1) * 4 ^ 𝔭.D / 𝔭.C * (1 + |(n : ℝ)|) ^ 𝔭.D := by ring
  have hwle : ∀ n : ℤ, w n ≤ (b0 * a ^ 2 * Qc 𝔭 M₃) * ((1 + |(n : ℝ)|) ^ 2)⁻¹ := by
    intro n
    have hy : 0 < 1 + |(n : ℝ)| := by positivity
    have e1 : Bn n * (a * (1 + |(n : ℝ)|) ^ 𝔭.D) * (a * (1 + |(n : ℝ)|) ^ 𝔭.D) * Qc 𝔭 M₃ =
        (b0 * a ^ 2 * Qc 𝔭 M₃) * ((1 + |(n : ℝ)|) ^ 2)⁻¹ := by
      simp only [hBn, hNA]
      field_simp
      ring
    rw [← e1]
    simp only [hwdef]
    have hq := hQale n
    have hq0 := hQa0 n
    have hB := hBnpos n
    have hmain : Bn n * Qa 𝔭 M₁ n * Qa 𝔭 M₁ n * Qc 𝔭 M₃ ≤
        Bn n * (a * (1 + |(n : ℝ)|) ^ 𝔭.D) * (a * (1 + |(n : ℝ)|) ^ 𝔭.D) * Qc 𝔭 M₃ := by
      gcongr
    exact hmain
  have hws : Summable w := by
    exact Summable.of_nonneg_of_le hw0 hwle ((summable_inv_one_add_abs_pow (le_refl 2)).mul_left _)
  set CdV : ℝ := 2 * (Slab.card : ℝ) * ∑' n, w n with hCdV
  have hCdV0 : 0 ≤ CdV := by rw [hCdV]; exact mul_nonneg (by positivity) (tsum_nonneg hw0)
  refine ⟨CdV, hCdV0, ?_⟩
  intro C₀ hC₀ hMdl P _ T m hm hAm CT hT f₁ f₂ f₃ _ _ _
  have hM : ModelBoundAt u 𝔭 C₀ := hMdl
  have hCT : 0 ≤ CT := FormBound.nonneg hu hT
  obtain ⟨c, hdec, hform⟩ := hCV hm hAm
  have hcB : ∀ k n, ‖c k n‖ ≤ Bn n := by
    intro k n
    have h1 := hdec NA k n
    have hy : 0 < (1 + |(n : ℝ)|) ^ NA := by positivity
    simp only [hBn]
    rw [le_div_iff₀ hy, mul_comm]
    refine h1.trans ?_
    calc CV NA * ∑ j ∈ Finset.range (NA + 1), A j = CV NA * SA := rfl
      _ ≤ |CV NA * SA| := le_abs_self _
      _ ≤ b0 := by rw [hb0]; linarith
  have HS := hform T f₁ f₂ f₃
  set R : ℝ≥0∞ := ENNReal.ofReal (C₀ * CT) * eLpNorm (fun x : ℝ => yNorm 2 (tensorFun f₁ x)) 2 volume *
    eLpNorm (fun x : ℝ => yNorm 2 (tensorFun f₂ x)) 2 volume *
    eLpNorm (fun x : ℝ => yNorm u (tensorFun f₃ x)) ⊤ volume with hR
  have hG : ∀ G : Finset (ℤ × ℤ), ‖∑ p ∈ G, c p.1 p.2 * wPieceForm T f₁ f₂ f₃ p‖ₑ ≤ ENNReal.ofReal CdV * R := by
    intro G
    have htend : Tendsto (fun H : Finset (ℤ × ℤ) => ∑ p ∈ G, ∑ q ∈ H, c p.1 p.2 *
        (if 62 ≤ |q.2 - q.1| ∧ |q.2 - q.1| ≤ 258 then pairTerm T f₁ f₂ f₃ p.1 p.2 q.1 (q.2 - q.1) else 0))
        atTop (𝓝 (∑ p ∈ G, c p.1 p.2 * wPieceForm T f₁ f₂ f₃ p)) := by
      refine tendsto_finsetSum G fun p _ => ?_
      have := (hasSum_pairTerm T f₁ f₂ f₃ p.1 p.2).mul_left (c p.1 p.2)
      simp only [mul_ite, mul_zero] at this ⊢
      exact this
    exact le_of_tendsto' htend.enorm fun H =>
      finite_bound hM hJ hC h₁ h₃ hI₁ hI₃ hη hX hT f₁ f₂ f₃ c Bn hBnpos hcB hws G H
  have hTot : ‖multiplierForm m T f₁ f₂ f₃‖ₑ ≤ ENNReal.ofReal CdV * R :=
    le_of_tendsto' (Tendsto.enorm (show Tendsto (fun G : Finset (ℤ × ℤ) => ∑ p ∈ G, c p.1 p.2 * wPieceForm T f₁ f₂ f₃ p)
      atTop (𝓝 (multiplierForm m T f₁ f₂ f₃)) from HS)) hG
  calc ‖multiplierForm m T f₁ f₂ f₃‖ₑ ≤ ENNReal.ofReal CdV * R := hTot
    _ = ENNReal.ofReal (CdV * C₀ * CT) * eLpNorm (fun x : ℝ => yNorm 2 (tensorFun f₁ x)) 2 volume *
          eLpNorm (fun x : ℝ => yNorm 2 (tensorFun f₂ x)) 2 volume *
          eLpNorm (fun x : ℝ => yNorm u (tensorFun f₃ x)) ⊤ volume := by
        rw [hR, show CdV * C₀ * CT = CdV * (C₀ * CT) by ring, ENNReal.ofReal_mul hCdV0]
        ring

/-- **The frozen statement from V16.**  `V16 ⇒ X2Statement` (the type of `t_finiteBV`), with the PROVED discretization (V04 + V05),
the proved model-operator structure and `V17`, and the proved band-limited reduction V03. -/
theorem x2Statement_of_v16 (h16 : V16Statement) : PrimeBHT.TransferenceAssembly.X2Statement :=
  x2Statement_of_v16_discretization h16 discretization

end PrimeBHT.TimeFrequency.X2
