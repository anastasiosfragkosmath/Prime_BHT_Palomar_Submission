module

public import PrimeBHT.TimeFrequency.X1.RealLine.KernelDecomposition
public import PrimeBHT.TimeFrequency.X1.RealLine.LittlewoodPaley.DilAvgC
public import PrimeBHT.TimeFrequency.X1.RealLine.LittlewoodPaley.Triangle
public import PrimeBHT.TimeFrequency.X1.RealLine.LittlewoodPaley.Series

/-!
# Littlewood-Paley reduction: Theorem Θ ⇒ Theorem B (blueprint node R3, `docs/x1-blueprint.md` section 4)

* `dilAvgC` (file `LittlewoodPaley/DilAvgC.lean`) is the dilated average `B_t(φ, f, g)` with a COMPLEX profile
  `φ : ℝ → ℂ`; for a real profile it is the existing `dilAvg` (`dilAvg_eq_dilAvgC`); `dilAvg` is unchanged.
* `TheoremTheta p q r M C` (**Theorem Θ**, BD26's `Θ_0`, unshifted): for every finite family
  `(g_s)_{s ∈ S}`, `S ⊆ ℤ`, with `supp 𝓕 g_s ⊆ [8, 9]` and `|g_s(x)| ≤ (1 + |x|)^{-M}`, and all Schwartz
  `f₁, f₂`: `‖∑_{s ∈ S} B_{2^s}(g_s, f₁, f₂)‖_{L^r} ≤ C ‖f₁‖_{L^p} ‖f₂‖_{L^q}`.
* `theoremB_of_theta` (**R3**): Theorem Θ (for one `M`) implies `TheoremB χ p q r C'` for every cutoff `χ`,
  `1 < p, q`, `1/r = 1/p + 1/q`, `2/3 < r`; `C'` depends on `(χ, p, q, r, M, C)` only.

Scale convention: `TheoremB` uses `B_{2^{-j}}` for `j < J` (`((2:ℝ)^j)⁻¹`); `TheoremTheta` uses `B_{2^s}`
with `s ∈ ℤ` (`(2:ℝ)^s`); they match under `s = -j`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Finset
open scoped FourierTransform ContDiff ENNReal Real
open PrimeBHT.Statements

namespace PrimeBHT.TimeFrequency.RealLine

/-- **Theorem Θ** (the core model-sum theorem; BD26's `Θ_0`, unshifted).

The hypothesis `Integrable (g s)` is needed for the statement to be true in Lean: the Lean Fourier
transform of a non-integrable function is `0`, so without it "`𝓕 g_s` supported in `[8, 9]`" is vacuous for
non-measurable `g_s`, and the claim becomes false (take `g_s` an arbitrary bump `G` on a large ball and
non-measurable outside the ball; the finitely many averages `B_{2^s}` of compactly supported `f₁, f₂` see only
`G`). With `Integrable (g s)` (automatic from measurability when `M ≥ 2`) `𝓕 g_s` is the honest `L¹` Fourier
transform and this is the blueprint's statement. -/
def TheoremTheta (p q r : ℝ) (M : ℕ) (C : ℝ) : Prop :=
  ∀ (S : Finset ℤ) (g : ℤ → ℝ → ℂ),
    (∀ s ∈ S, Integrable (g s) volume) →
    (∀ s ∈ S, ∀ ξ : ℝ, ξ ∉ Set.Icc (8 : ℝ) 9 → 𝓕 (g s) ξ = 0) →
    (∀ s ∈ S, ∀ x : ℝ, ‖g s x‖ ≤ ((1 + |x|) ^ M)⁻¹) →
    ∀ f₁ f₂ : SchwartzMap ℝ ℂ,
      eLpNorm (∑ s ∈ S, dilAvgC (g s) ((2 : ℝ) ^ s) f₁ f₂) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal C * eLpNorm f₁ (ENNReal.ofReal p) volume *
          eLpNorm f₂ (ENNReal.ofReal q) volume

theorem TheoremTheta.mono {p q r : ℝ} {M : ℕ} {C C' : ℝ} (h : TheoremTheta p q r M C) (hC : C ≤ C') :
    TheoremTheta p q r M C' := fun S g h0 h1 h2 f₁ f₂ =>
  (h S g h0 h1 h2 f₁ f₂).trans (by gcongr)

/-! ## Auxiliary lemmas -/

theorem fourier_const_mul (a : ℂ) (g : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun y => a * g y) ξ = a * 𝓕 g ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]; ring

theorem exists_schwartz_conj (f : SchwartzMap ℝ ℂ) :
    ∃ f' : SchwartzMap ℝ ℂ, ∀ u, f' u = (starRingEnd ℂ) (f u) :=
  ⟨SchwartzMap.postcompCLM (𝕜 := ℝ) (E := ℝ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) f, fun _ => rfl⟩

/-- Dilation covariance transfers an `L^p × L^q → L^r` bound (as in `bhtOpR_bound_dilate`). -/
theorem bound_of_dilation_cov {T T' : (ℝ → ℂ) → (ℝ → ℂ) → ℝ → ℂ} {s : ℝ} (hs : 0 < s)
    {p q r C : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hpqr : 1 / r = 1 / p + 1 / q)
    (hcov : ∀ (f g : ℝ → ℂ) (x : ℝ), T (fun u => f (s * u)) (fun u => g (s * u)) x = T' f g (s * x))
    (h : ∀ f g : SchwartzMap ℝ ℂ,
      eLpNorm (T f g) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume *
          eLpNorm g (ENNReal.ofReal q) volume) :
    ∀ f g : SchwartzMap ℝ ℂ,
      eLpNorm (T' f g) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume *
          eLpNorm g (ENNReal.ofReal q) volume := by
  intro f g
  obtain ⟨f', hf'⟩ := exists_schwartz_dilate f hs
  obtain ⟨g', hg'⟩ := exists_schwartz_dilate g hs
  have hf'' : (⇑f' : ℝ → ℂ) = fun u => f (s * u) := funext hf'
  have hg'' : (⇑g' : ℝ → ℂ) = fun u => g (s * u) := funext hg'
  have hFt : (fun u => T' f g (s * u)) = T f' g' := by
    funext u
    rw [← hcov f g u, hf'', hg'']
  have h1 := h f' g'
  rw [← hFt, eLpNorm_comp_mul_left_ofReal _ hs hr, hf'', hg'',
    eLpNorm_comp_mul_left_ofReal _ hs hp, eLpNorm_comp_mul_left_ofReal _ hs hq] at h1
  have hA : ENNReal.ofReal (s ^ (-(1 / r))) =
      ENNReal.ofReal (s ^ (-(1 / p))) * ENNReal.ofReal (s ^ (-(1 / q))) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hs, hpqr, neg_add]
  rw [hA] at h1
  have h0 : ENNReal.ofReal (s ^ (-(1 / p))) * ENNReal.ofReal (s ^ (-(1 / q))) ≠ 0 := by
    apply mul_ne_zero <;> (rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity)
  have htop : ENNReal.ofReal (s ^ (-(1 / p))) * ENNReal.ofReal (s ^ (-(1 / q))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  refine (ENNReal.mul_le_mul_iff_right h0 htop).1 ?_
  refine h1.trans (le_of_eq ?_)
  ring

/-- Theorem Θ applied to a family with decay `a (1 + |x|)^{-M}`. -/
theorem theta_apply {p q r : ℝ} {M : ℕ} {CΘ : ℝ} (hΘ : TheoremTheta p q r M CΘ) (S : Finset ℤ)
    (G : ℤ → ℝ → ℂ) {a : ℝ} (ha : 0 < a) (hI : ∀ s ∈ S, Integrable (G s) volume)
    (hF : ∀ s ∈ S, ∀ ξ : ℝ, ξ ∉ Set.Icc (8 : ℝ) 9 → 𝓕 (G s) ξ = 0)
    (hD : ∀ s ∈ S, ∀ x : ℝ, ‖G s x‖ ≤ a * ((1 + |x|) ^ M)⁻¹) (f₁ f₂ : SchwartzMap ℝ ℂ) :
    eLpNorm (∑ s ∈ S, dilAvgC (G s) ((2 : ℝ) ^ s) f₁ f₂) (ENNReal.ofReal r) volume ≤
      ENNReal.ofReal (a * CΘ) * eLpNorm f₁ (ENNReal.ofReal p) volume *
        eLpNorm f₂ (ENNReal.ofReal q) volume := by
  have h := hΘ S (fun s y => ((a⁻¹ : ℝ) : ℂ) * G s y) (fun s hs => (hI s hs).const_mul _)
    (fun s hs ξ hξ => by rw [fourier_const_mul, hF s hs ξ hξ, mul_zero])
    (fun s hs x => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ha)]
      calc a⁻¹ * ‖G s x‖ ≤ a⁻¹ * (a * ((1 + |x|) ^ M)⁻¹) :=
            mul_le_mul_of_nonneg_left (hD s hs x) (inv_pos.2 ha).le
        _ = ((1 + |x|) ^ M)⁻¹ := by field_simp) f₁ f₂
  have hsum : (∑ s ∈ S, dilAvgC (G s) ((2 : ℝ) ^ s) f₁ f₂) =
      (a : ℂ) • ∑ s ∈ S, dilAvgC (fun y => ((a⁻¹ : ℝ) : ℂ) * G s y) ((2 : ℝ) ^ s) f₁ f₂ := by
    funext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, dilAvgC_const_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ ha.ne', Complex.ofReal_one, one_mul]
  have hen : ‖(a : ℂ)‖ₑ = ENNReal.ofReal a := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  rw [hsum, eLpNorm_const_smul, hen]
  calc ENNReal.ofReal a * eLpNorm (∑ s ∈ S, dilAvgC (fun y => ((a⁻¹ : ℝ) : ℂ) * G s y)
        ((2 : ℝ) ^ s) f₁ f₂) (ENNReal.ofReal r) volume
      ≤ ENNReal.ofReal a * (ENNReal.ofReal CΘ * eLpNorm f₁ (ENNReal.ofReal p) volume *
          eLpNorm f₂ (ENNReal.ofReal q) volume) := by gcongr
    _ = ENNReal.ofReal (a * CΘ) * eLpNorm f₁ (ENNReal.ofReal p) volume *
          eLpNorm f₂ (ENNReal.ofReal q) volume := by
        rw [ENNReal.ofReal_mul ha.le]; ring

theorem lpW_pos {l : ℝ} (hl : 0 < l) : 0 < lpW l := lt_min hl (by positivity)

theorem exists_bound_schwartz (f : SchwartzMap ℝ ℂ) : ∃ B : ℝ, ∀ x, ‖f x‖ ≤ B := by
  obtain ⟨C, -, hC⟩ := f.decay 0 0
  exact ⟨C, fun x => by simpa using hC x⟩

/-- The `ψ_k^+`-part: Theorem Θ + dilation (steps 3 and 5 of R3). -/
theorem eLpNorm_piece_le {χ : ℝ → ℝ} (hχ : IsCutoff χ) {p q r : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r) (hpqr : 1 / r = 1 / p + 1 / q) {M : ℕ} {CΘ : ℝ} (hΘ : TheoremTheta p q r M CΘ)
    {C0 : ℝ} (hC0pos : 0 < C0)
    (hC0 : ∀ c ∈ Set.Icc (1 : ℝ) 2, ∀ (k : ℤ) (x : ℝ),
      (1 + |x|) ^ M * ‖gPiece χ c k x‖ ≤ C0 * lpW (lpLam k))
    (J : ℕ) (cc : ℕ → ℝ) (hcc : ∀ j < J, cc j ∈ Set.Icc (1 : ℝ) 2) (k : ℤ)
    (f₁ f₂ : SchwartzMap ℝ ℂ) :
    eLpNorm (fun x => ∑ j ∈ range J, dilAvgC (psiPlus χ (cc j) k) ((2 : ℝ) ^ j)⁻¹ f₁ f₂ x)
        (ENNReal.ofReal r) volume ≤
      ENNReal.ofReal (C0 * lpW (lpLam k) * CΘ) * eLpNorm f₁ (ENNReal.ofReal p) volume *
        eLpNorm f₂ (ENNReal.ofReal q) volume := by
  set l := lpLam k with hl_def
  have hl : 0 < l := lpLam_pos k
  have ha : 0 < C0 * lpW l := mul_pos hC0pos (lpW_pos hl)
  let e : ℕ ↪ ℤ := ⟨fun j : ℕ => -(j : ℤ), fun a b h => by simpa using h⟩
  let S : Finset ℤ := (range J).map e
  let G : ℤ → ℝ → ℂ := fun s => gPiece χ (cc s.natAbs) k
  have he : ∀ j : ℕ, e j = -(j : ℤ) := fun j => rfl
  have hGe : ∀ j : ℕ, G (e j) = gPiece χ (cc j) k := fun j => by
    simp only [G, he, Int.natAbs_neg, Int.natAbs_natCast]
  have hθ := theta_apply hΘ S G ha
    (fun s hs => by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hs
      rw [hGe]
      exact integrable_gPiece hχ (hcc j (mem_range.1 hj)) k)
    (fun s hs ξ hξ => by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hs
      rw [hGe]
      exact fourier_gPiece_eq_zero hχ (hcc j (mem_range.1 hj)) k hξ)
    (fun s hs x => by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hs
      rw [hGe]
      have h := hC0 (cc j) (hcc j (mem_range.1 hj)) k x
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      linarith)
  have hTS : ∀ F1 F2 : ℝ → ℂ, (∑ s ∈ S, dilAvgC (G s) ((2 : ℝ) ^ s) F1 F2) =
      fun x => ∑ j ∈ range J, dilAvgC (gPiece χ (cc j) k) ((2 : ℝ) ^ j)⁻¹ F1 F2 x := by
    intro F1 F2
    funext x
    rw [Finset.sum_apply, Finset.sum_map]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hGe, he, zpow_neg, zpow_natCast]
  set T : (ℝ → ℂ) → (ℝ → ℂ) → ℝ → ℂ := fun F1 F2 x =>
    ∑ j ∈ range J, dilAvgC (gPiece χ (cc j) k) ((2 : ℝ) ^ j)⁻¹ F1 F2 x with hT
  set T' : (ℝ → ℂ) → (ℝ → ℂ) → ℝ → ℂ := fun F1 F2 x =>
    ∑ j ∈ range J, dilAvgC (gPiece χ (cc j) k) (((2 : ℝ) ^ j)⁻¹ * l⁻¹) F1 F2 x with hT'
  have hbT : ∀ F1 F2 : SchwartzMap ℝ ℂ, eLpNorm (T F1 F2) (ENNReal.ofReal r) volume ≤
      ENNReal.ofReal (C0 * lpW l * CΘ) * eLpNorm F1 (ENNReal.ofReal p) volume *
        eLpNorm F2 (ENNReal.ofReal q) volume := fun F1 F2 => by
    have := hθ F1 F2
    rw [hTS] at this
    exact this
  have hcov : ∀ (F1 F2 : ℝ → ℂ) (x : ℝ),
      T (fun u => F1 (l⁻¹ * u)) (fun u => F2 (l⁻¹ * u)) x = T' F1 F2 (l⁻¹ * x) := by
    intro F1 F2 x
    simp only [hT, hT']
    refine Finset.sum_congr rfl fun j _ => ?_
    exact dilAvgC_dilate _ (inv_pos.2 hl) (inv_pos.2 (pow_pos two_pos j)) F1 F2 x
  have hb := bound_of_dilation_cov (inv_pos.2 hl) hp hq hr hpqr hcov hbT f₁ f₂
  have heq : (fun x => ∑ j ∈ range J, dilAvgC (psiPlus χ (cc j) k) ((2 : ℝ) ^ j)⁻¹ f₁ f₂ x) =
      T' f₁ f₂ := by
    funext x
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : psiPlus χ (cc j) k = fun y => (l : ℂ) * gPiece χ (cc j) k (l * y) := rfl
    rw [h1, dilAvgC_scale_profile _ hl.ne' (inv_ne_zero (pow_pos two_pos j).ne') f₁ f₂ x,
      div_eq_mul_inv]
  rw [heq]
  exact hb

/-- The `ψ_k^-`-part, by conjugation. -/
theorem eLpNorm_piece_conj_le {χ : ℝ → ℝ} (hχ : IsCutoff χ) {p q r : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r) (hpqr : 1 / r = 1 / p + 1 / q) {M : ℕ} {CΘ : ℝ} (hΘ : TheoremTheta p q r M CΘ)
    {C0 : ℝ} (hC0pos : 0 < C0)
    (hC0 : ∀ c ∈ Set.Icc (1 : ℝ) 2, ∀ (k : ℤ) (x : ℝ),
      (1 + |x|) ^ M * ‖gPiece χ c k x‖ ≤ C0 * lpW (lpLam k))
    (J : ℕ) (cc : ℕ → ℝ) (hcc : ∀ j < J, cc j ∈ Set.Icc (1 : ℝ) 2) (k : ℤ)
    (f₁ f₂ : SchwartzMap ℝ ℂ) :
    eLpNorm (fun x => ∑ j ∈ range J,
        dilAvgC (fun y => (starRingEnd ℂ) (psiPlus χ (cc j) k y)) ((2 : ℝ) ^ j)⁻¹ f₁ f₂ x)
        (ENNReal.ofReal r) volume ≤
      ENNReal.ofReal (C0 * lpW (lpLam k) * CΘ) * eLpNorm f₁ (ENNReal.ofReal p) volume *
        eLpNorm f₂ (ENNReal.ofReal q) volume := by
  obtain ⟨f₁', hf₁'⟩ := exists_schwartz_conj f₁
  obtain ⟨f₂', hf₂'⟩ := exists_schwartz_conj f₂
  have h1 : (⇑f₁' : ℝ → ℂ) = star (⇑f₁ : ℝ → ℂ) := funext hf₁'
  have h2 : (⇑f₂' : ℝ → ℂ) = star (⇑f₂ : ℝ → ℂ) := funext hf₂'
  have hn1 : eLpNorm f₁' (ENNReal.ofReal p) volume = eLpNorm f₁ (ENNReal.ofReal p) volume := by
    rw [h1, eLpNorm_star]
  have hn2 : eLpNorm f₂' (ENNReal.ofReal q) volume = eLpNorm f₂ (ENNReal.ofReal q) volume := by
    rw [h2, eLpNorm_star]
  have hmain := eLpNorm_piece_le hχ hp hq hr hpqr hΘ hC0pos hC0 J cc hcc k f₁' f₂'
  have heq : (fun x => ∑ j ∈ range J,
        dilAvgC (fun y => (starRingEnd ℂ) (psiPlus χ (cc j) k y)) ((2 : ℝ) ^ j)⁻¹ f₁ f₂ x) =
      star (fun x => ∑ j ∈ range J, dilAvgC (psiPlus χ (cc j) k) ((2 : ℝ) ^ j)⁻¹ f₁' f₂' x) := by
    funext x
    simp only [Pi.star_apply, star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dilAvgC_conj, h1, h2]
    simp only [starRingEnd_apply]
    rfl
  rw [hn1, hn2] at hmain
  rw [heq, eLpNorm_star]
  exact hmain

/-- Bookkeeping in `ℝ≥0∞` for the geometric sum over `k` (step 6 of R3). -/
theorem sum_Icc_ofReal_mul_le {w : ℤ → ℝ} (hw0 : ∀ k, 0 ≤ w k) (hws : Summable w) {c : ℝ}
    (hc : 0 ≤ c) (Y : ℝ≥0∞) (K : ℕ) :
    ∑ k ∈ Finset.Icc (-(K : ℤ)) K, ENNReal.ofReal (c * w k) * Y ≤
      ENNReal.ofReal (c * ∑' k, w k) * Y := by
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg hc (hw0 k))]
  gcongr
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hws.sum_le_tsum _ (fun k _ => hw0 k)) hc

/-- **R3, for one `M`.** If Theorem Θ holds with the decay exponent `M` (and some constant), then Theorem B
holds for every cutoff `χ`. -/
theorem theoremB_of_theta_at {χ : ℝ → ℝ} (hχ : IsCutoff χ) {p q r : ℝ} (hp : 1 < p) (hq : 1 < q)
    (hpqr : 1 / r = 1 / p + 1 / q) (hr : 2 / 3 < r) {M : ℕ} {CΘ : ℝ}
    (hΘ : TheoremTheta p q r M CΘ) : ∃ C' : ℝ, TheoremB χ p q r C' := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hr0 : 0 < r := by linarith
  obtain ⟨Cθ, hCθ0, hΘ'⟩ : ∃ Cθ : ℝ, 0 ≤ Cθ ∧ TheoremTheta p q r M Cθ :=
    ⟨max CΘ 0, le_max_right _ _, hΘ.mono (le_max_left _ _)⟩
  obtain ⟨C0, hC0pos, hC0⟩ := exists_decay_gPiece hχ M
  have hrs : 0 < min r 1 := lt_min hr0 one_pos
  have hws : Summable (fun k : ℤ => lpW (lpLam k) ^ min r 1) := summable_lpW_rpow hrs
  have hw0 : ∀ k : ℤ, 0 ≤ lpW (lpLam k) ^ min r 1 := fun k =>
    Real.rpow_nonneg (lpW_nonneg (lpLam_pos k)) _
  have hW0 : 0 ≤ ∑' k : ℤ, lpW (lpLam k) ^ min r 1 := tsum_nonneg hw0
  have hc0 : 0 ≤ 2 * (C0 * Cθ) ^ min r 1 := by positivity
  refine ⟨(2 * (C0 * Cθ) ^ min r 1 * ∑' k : ℤ, lpW (lpLam k) ^ min r 1) ^ (1 / min r 1), ?_⟩
  intro J g hg f₁ f₂
  choose! cc hccI hccg using hg
  set X : ℝ≥0∞ := eLpNorm f₁ (ENNReal.ofReal p) volume * eLpNorm f₂ (ENNReal.ofReal q) volume
    with hX
  set A : ℤ → ℝ → ℂ := fun k x =>
    ∑ j ∈ range J, dilAvgC (psiPlus χ (cc j) k) ((2 : ℝ) ^ j)⁻¹ f₁ f₂ x with hA_def
  set Ab : ℤ → ℝ → ℂ := fun k x => ∑ j ∈ range J,
    dilAvgC (fun y => (starRingEnd ℂ) (psiPlus χ (cc j) k y)) ((2 : ℝ) ^ j)⁻¹ f₁ f₂ x with hAb_def
  set F : ℤ → ℝ → ℂ := fun k x => A k x + Ab k x with hF_def
  set Sx : ℝ → ℂ := fun x => ∑ j ∈ range J, dilAvgC (psiCC χ (cc j)) ((2 : ℝ) ^ j)⁻¹ f₁ f₂ x
    with hSx
  have hAm : ∀ k, AEStronglyMeasurable (A k) volume := fun k => by
    have := Finset.aestronglyMeasurable_sum (range J) (fun j hj =>
      aestronglyMeasurable_dilAvgC (continuous_psiPlus hχ (hccI j (mem_range.1 hj)) k)
        f₁.continuous f₂.continuous (((2 : ℝ) ^ j)⁻¹))
    convert this using 1
    ext x
    simp [hA_def]
  have hAbm : ∀ k, AEStronglyMeasurable (Ab k) volume := fun k => by
    have := Finset.aestronglyMeasurable_sum (range J) (fun j hj =>
      aestronglyMeasurable_dilAvgC
        ((continuous_star (R := ℂ)).comp (continuous_psiPlus hχ (hccI j (mem_range.1 hj)) k))
        f₁.continuous f₂.continuous (((2 : ℝ) ^ j)⁻¹))
    convert this using 1
    ext x
    simp only [hAb_def, Finset.sum_apply]
    rfl
  have hFm : ∀ k, AEStronglyMeasurable (F k) volume := fun k => (hAm k).add (hAbm k)
  have htend : ∀ x, Tendsto (fun K : ℕ => ∑ k ∈ Finset.Icc (-(K : ℤ)) K, F k x) atTop
      (𝓝 (Sx x)) := by
    intro x
    obtain ⟨Bf, hBf⟩ := exists_bound_schwartz f₁
    obtain ⟨Bg, hBg⟩ := exists_bound_schwartz f₂
    have hj : ∀ j ∈ range J, Tendsto (fun K : ℕ => ∑ k ∈ Finset.Icc (-(K : ℤ)) K,
        (dilAvgC (psiPlus χ (cc j) k) ((2 : ℝ) ^ j)⁻¹ f₁ f₂ x +
          dilAvgC (fun y => (starRingEnd ℂ) (psiPlus χ (cc j) k y)) ((2 : ℝ) ^ j)⁻¹ f₁ f₂ x))
        atTop (𝓝 (dilAvgC (psiCC χ (cc j)) ((2 : ℝ) ^ j)⁻¹ f₁ f₂ x)) := fun j hj =>
      tendsto_sum_dilAvgC hχ (hccI j (mem_range.1 hj)) (inv_pos.2 (pow_pos two_pos j))
        f₁.continuous f₂.continuous hBf hBg x
    refine (tendsto_finsetSum (range J) hj).congr fun K => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hF_def, hA_def, hAb_def, Finset.sum_add_distrib]
  have hk : ∀ k : ℤ, eLpNorm (F k) (ENNReal.ofReal r) volume ^ min r 1 ≤
      ENNReal.ofReal (2 * (C0 * Cθ) ^ min r 1 * lpW (lpLam k) ^ min r 1) * X ^ min r 1 := by
    intro k
    have h1 := eLpNorm_add_rpow_le hr0 (hAm k) (hAbm k)
    have hA := eLpNorm_piece_le hχ hp0 hq0 hr0 hpqr hΘ' hC0pos hC0 J cc hccI k f₁ f₂
    have hAb := eLpNorm_piece_conj_le hχ hp0 hq0 hr0 hpqr hΘ' hC0pos hC0 J cc hccI k f₁ f₂
    have hwk := lpW_nonneg (lpLam_pos k)
    have hY : (ENNReal.ofReal (C0 * lpW (lpLam k) * Cθ) * eLpNorm f₁ (ENNReal.ofReal p) volume *
        eLpNorm f₂ (ENNReal.ofReal q) volume) ^ min r 1 =
        ENNReal.ofReal ((C0 * Cθ) ^ min r 1 * lpW (lpLam k) ^ min r 1) * X ^ min r 1 := by
      rw [mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ hrs.le,
        ENNReal.ofReal_rpow_of_nonneg (by positivity) hrs.le, hX]
      congr 2
      rw [show C0 * lpW (lpLam k) * Cθ = (C0 * Cθ) * lpW (lpLam k) by ring,
        Real.mul_rpow (by positivity) hwk]
    have h2 : (A k + Ab k) = F k := rfl
    calc eLpNorm (F k) (ENNReal.ofReal r) volume ^ min r 1
        ≤ eLpNorm (A k) (ENNReal.ofReal r) volume ^ min r 1 +
            eLpNorm (Ab k) (ENNReal.ofReal r) volume ^ min r 1 := h1
      _ ≤ (ENNReal.ofReal (C0 * lpW (lpLam k) * Cθ) * eLpNorm f₁ (ENNReal.ofReal p) volume *
            eLpNorm f₂ (ENNReal.ofReal q) volume) ^ min r 1 +
          (ENNReal.ofReal (C0 * lpW (lpLam k) * Cθ) * eLpNorm f₁ (ENNReal.ofReal p) volume *
            eLpNorm f₂ (ENNReal.ofReal q) volume) ^ min r 1 :=
          add_le_add (ENNReal.rpow_le_rpow hA hrs.le) (ENNReal.rpow_le_rpow hAb hrs.le)
      _ = ENNReal.ofReal (2 * (C0 * Cθ) ^ min r 1 * lpW (lpLam k) ^ min r 1) * X ^ min r 1 := by
          rw [hY, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 2
          ring
  have hB : ∀ K : ℕ, ∑ k ∈ Finset.Icc (-(K : ℤ)) K,
      eLpNorm (F k) (ENNReal.ofReal r) volume ^ min r 1 ≤
      ENNReal.ofReal (2 * (C0 * Cθ) ^ min r 1 * ∑' k : ℤ, lpW (lpLam k) ^ min r 1) *
        X ^ min r 1 := fun K =>
    (Finset.sum_le_sum fun k _ => hk k).trans
      (sum_Icc_ofReal_mul_le hw0 hws hc0 (X ^ min r 1) K)
  have hfin := eLpNorm_rpow_le_of_tendsto_sum hr0 hFm htend hB
  have hSeq : (∑ j ∈ range J, dilAvg (g j) ((2 : ℝ) ^ j)⁻¹ f₁ f₂) = Sx := by
    funext x
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hccg j (mem_range.1 hj), dilAvg_eq_dilAvgC]
    rfl
  rw [hSeq]
  have hcW : 0 ≤ 2 * (C0 * Cθ) ^ min r 1 * ∑' k : ℤ, lpW (lpLam k) ^ min r 1 := by positivity
  have h3 := ENNReal.rpow_le_rpow hfin (one_div_pos.2 hrs).le
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hrs.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.2 hrs).le, ← ENNReal.rpow_mul,
    mul_one_div_cancel hrs.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hcW (one_div_pos.2 hrs).le] at h3
  rw [mul_assoc]
  exact h3

end PrimeBHT.TimeFrequency.RealLine

end
