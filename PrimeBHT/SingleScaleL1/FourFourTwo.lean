module

public import PrimeBHT.SingleScaleL1.Interp
public import PrimeBHT.U3MaxMod
public import PrimeCarleson.Proof.FplusProp21.Main

/-!
# N12 (b), `e:single-L1`: the `(4,4,2)` estimate with the reflection argument (stage (a))

For `Q ≥ 1` and `2^k ≥ Q^{20}`:
`‖T_k^Q(f,g)‖_{ℓ²} ≤ C Q^{δ-3/8} ‖f‖_{ℓ⁴} ‖g‖_{ℓ⁴}`.

* `phiPos χ t = ψ(t) 1_{t>0}` is `C^∞` (as `ψ = 0` on `|t| ≤ 1/4`), supported in `[0,1]`.
* the reflection `n ↦ -n` (`w_Q` even, `ψ_k` odd) gives
  `T_k^Q(f,g) = S₊(f,g) - S₊(g,f)` with `S₊(f,g)(x) = ∑_{n=1}^{2^k} 2^{-k} φ(n/2^k) w_Q(n) f(x-n) g(x+n)`;
* `l:U3maxmod` (b) (`eLpNorm_smooth_le_real`) bounds each `S₊` by `8 M ‖w_Q‖_{U³([2^k])}‖f‖₄‖g‖₄`;
* the vendored [F+, Prop 2.1] (`exists_gowersNormInterval_blockWeight_le`) gives
  `‖w_Q‖_{U³([2^k])} ≤ C_δ Q^{δ-3/8}` for `2^k ≥ Q^{20}`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal ContDiff

namespace PrimeBHT.SingleScaleL1

open PrimeBHT.Kernel PrimeCarleson

/-! ### The one-sided profile -/

/-- `φ = ψ 1_{(0,∞)}`. -/
noncomputable def phiPos (χ : ℝ → ℝ) (t : ℝ) : ℝ := if 0 < t then psi χ t else 0

lemma phiPos_of_pos {χ : ℝ → ℝ} {t : ℝ} (ht : 0 < t) : phiPos χ t = psi χ t := by
  simp [phiPos, ht]

lemma phiPos_of_nonpos {χ : ℝ → ℝ} {t : ℝ} (ht : t ≤ 0) : phiPos χ t = 0 := by
  simp [phiPos, not_lt.2 ht]

lemma phiPos_eq_zero_of_abs_le {χ : ℝ → ℝ} (hχ : IsCutoff χ) {t : ℝ} (ht : |t| ≤ 1 / 4) :
    phiPos χ t = 0 := by
  unfold phiPos
  split_ifs
  · exact hχ.psi_eq_zero_of_abs_le ht
  · rfl

lemma phiPos_eq_zero_of_notMem {χ : ℝ → ℝ} (hχ : IsCutoff χ) {t : ℝ} (ht : t ∉ Set.Icc (0 : ℝ) 1) :
    phiPos χ t = 0 := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with h | h
  · exact phiPos_of_nonpos h.le
  · rw [phiPos_of_pos (by linarith)]
    exact hχ.psi_eq_zero_of_one_le_abs (by rw [abs_of_pos (by linarith)]; exact h.le)

lemma contDiff_phiPos {χ : ℝ → ℝ} (hχ : IsCutoff χ) : ContDiff ℝ ∞ (phiPos χ) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have hev : phiPos χ =ᶠ[nhds t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact phiPos_of_nonpos hs.le
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · subst ht
    have hev : phiPos χ =ᶠ[nhds 0] fun _ => (0 : ℝ) := by
      filter_upwards [Ioo_mem_nhds (a := -(1 / 4 : ℝ)) (b := 1 / 4) (by norm_num)
        (by norm_num)] with s hs
      exact phiPos_eq_zero_of_abs_le hχ (abs_le.2 ⟨hs.1.le, hs.2.le⟩)
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hev : phiPos χ =ᶠ[nhds t] psi χ := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact phiPos_of_pos hs
    exact (hχ.contDiff_psi.contDiffAt).congr_of_eventuallyEq hev

lemma hasCompactSupport_phiPos {χ : ℝ → ℝ} (hχ : IsCutoff χ) : HasCompactSupport (phiPos χ) :=
  HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun _ ht =>
    phiPos_eq_zero_of_notMem hχ ht

lemma support_phiPos_subset {χ : ℝ → ℝ} (hχ : IsCutoff χ) :
    Function.support (phiPos χ) ⊆ Set.Icc (0 : ℝ) 1 := by
  intro t ht
  by_contra h
  exact ht (phiPos_eq_zero_of_notMem hχ h)

/-- `‖φ‖_∞, ‖φ''‖_∞ ≤ M` for a constant `M = M(χ)`. -/
lemma exists_bounds_phiPos {χ : ℝ → ℝ} (hχ : IsCutoff χ) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ t, |phiPos χ t| ≤ M) ∧ (∀ t, |deriv (deriv (phiPos χ)) t| ≤ M) := by
  have hd := contDiff_phiPos hχ
  have hc := hasCompactSupport_phiPos hχ
  have hd1 : ContDiff ℝ ∞ (deriv (phiPos χ)) := (contDiff_infty_iff_deriv.1 hd).2
  have hd2 : ContDiff ℝ ∞ (deriv (deriv (phiPos χ))) := (contDiff_infty_iff_deriv.1 hd1).2
  obtain ⟨C₁, hC₁⟩ := hd.continuous.bounded_above_of_compact_support hc
  obtain ⟨C₂, hC₂⟩ := hd2.continuous.bounded_above_of_compact_support hc.deriv.deriv
  refine ⟨max (max C₁ C₂) 0, le_max_right _ _, fun t => ?_, fun t => ?_⟩
  · exact (le_of_eq_of_le (Real.norm_eq_abs _).symm (hC₁ t)).trans
      ((le_max_left _ _).trans (le_max_left _ _))
  · exact (le_of_eq_of_le (Real.norm_eq_abs _).symm (hC₂ t)).trans
      ((le_max_right _ _).trans (le_max_left _ _))

/-! ### The reflection -/

/-- `2^k` as a positive natural number. -/
def pow2 (k : ℕ) : ℕ+ := ⟨2 ^ k, by positivity⟩

lemma pow2_coe (k : ℕ) : ((pow2 k : ℕ+) : ℕ) = 2 ^ k := rfl

/-- The half-line sum `S₊(f,g)(x) = ∑_{n=1}^{N} (N⁻¹ φ(n/N)) W(n) f(x-n) g(x+n)`. -/
noncomputable def Splus (φ : ℝ → ℝ) (N : ℕ+) (W : ℤ → ℂ) (f g : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑ n ∈ Finset.Icc (1 : ℤ) N,
    (((N : ℕ) : ℂ)⁻¹ * (φ ((n : ℝ) / (N : ℕ)) : ℂ)) * W n * f (x - n) * g (x + n)

lemma weight_of_pos {χ : ℝ → ℝ} (Q k : ℕ) {n : ℤ} (hn : 0 < n) :
    weight χ Q k n = (((pow2 k : ℕ+) : ℕ) : ℂ)⁻¹ *
      ((phiPos χ ((n : ℝ) / (((pow2 k : ℕ+) : ℕ) : ℝ)) : ℝ) : ℂ) *
        blockWeight (Finset.Ioc (Q / 2) Q) n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (((pow2 k : ℕ+) : ℕ) : ℝ) = 2 ^ k := by simp [pow2]
  rw [hpow, phiPos_of_pos (by positivity)]
  show ((psiK χ k n : ℝ) : ℂ) * _ = _
  simp only [psiK, pow2_coe]
  push_cast
  ring

lemma weight_neg {χ : ℝ → ℝ} (hχ : IsCutoff χ) (Q k : ℕ) (n : ℤ) :
    weight χ Q k (-n) = -weight χ Q k n := by
  show ((psiK χ k ((-n : ℤ) : ℝ) : ℝ) : ℂ) * blockWeight (Finset.Ioc (Q / 2) Q) (-n) = _
  rw [PrimeCarleson.Proof.Paper.blockWeight_neg, Int.cast_neg, hχ.psiK_neg]
  show _ = -(((psiK χ k n : ℝ) : ℂ) * _)
  push_cast
  ring

/-- The reflection identity: `T_k^Q(f,g) = S₊(f,g) - S₊(g,f)`. -/
lemma bilin_weight_eq {χ : ℝ → ℝ} (hχ : IsCutoff χ) (Q k : ℕ) (f g : ℤ → ℂ) (x : ℤ) :
    bilin (weight χ Q k) f g x =
      Splus (phiPos χ) (pow2 k) (blockWeight (Finset.Ioc (Q / 2) Q)) f g x -
        Splus (phiPos χ) (pow2 k) (blockWeight (Finset.Ioc (Q / 2) Q)) g f x := by
  set N0 : ℤ := ((2 ^ k : ℕ) : ℤ) with hN0
  set F : ℤ → ℂ := fun n => weight χ Q k n * f (x - n) * g (x + n) with hF
  have h1 : bilin (weight χ Q k) f g x = ∑ n ∈ Finset.Icc (-N0) N0, F n := by
    unfold bilin
    exact tsum_eq_sum (fun n hn => by
      show weight χ Q k n * f (x - n) * g (x + n) = 0
      rw [weight_eq_zero hχ Q k hn]
      simp)
  have hsplit : ∑ n ∈ Finset.Icc (-N0) N0, F n =
      ∑ n ∈ Finset.Icc (1 : ℤ) N0, F n + ∑ m ∈ Finset.Icc (1 : ℤ) N0, F (-m) := by
    have hdisj : Disjoint (Finset.Icc (1 : ℤ) N0) ((Finset.Icc (1 : ℤ) N0).image Neg.neg) := by
      rw [Finset.disjoint_left]
      intro n hn hn'
      simp only [Finset.mem_Icc, Finset.mem_image] at hn hn'
      obtain ⟨m, hm, rfl⟩ := hn'
      omega
    have himg : ∑ m ∈ Finset.Icc (1 : ℤ) N0, F (-m) =
        ∑ n ∈ (Finset.Icc (1 : ℤ) N0).image Neg.neg, F n :=
      (Finset.sum_image (f := F) (fun a _ b _ h => neg_injective h)).symm
    rw [himg, ← Finset.sum_union hdisj]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro n hn
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_image] at hn ⊢
      rcases hn with hn | ⟨m, hm, rfl⟩ <;> omega
    · intro n hn hn'
      have h0 : n = 0 := by
        simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_image, not_or, not_exists,
          not_and] at hn hn'
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact hn'.2 (-n) (by omega) (by omega)
        · exact hn'.1 (by omega) (by omega)
      subst h0
      simp only [hF]
      show ((psiK χ k ((0 : ℤ) : ℝ) : ℝ) : ℂ) * _ * _ * _ = 0
      simp [psiK_zero]
  rw [h1, hsplit]
  have hpos : ∑ n ∈ Finset.Icc (1 : ℤ) N0, F n =
      Splus (phiPos χ) (pow2 k) (blockWeight (Finset.Ioc (Q / 2) Q)) f g x := by
    unfold Splus
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    simp only [hF]
    rw [weight_of_pos (χ := χ) Q k (by omega)]
  have hneg : ∑ m ∈ Finset.Icc (1 : ℤ) N0, F (-m) =
      -Splus (phiPos χ) (pow2 k) (blockWeight (Finset.Ioc (Q / 2) Q)) g f x := by
    unfold Splus
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    simp only [hF]
    rw [weight_neg hχ, weight_of_pos (χ := χ) Q k (by omega)]
    simp only [sub_neg_eq_add, ← sub_eq_add_neg]
    ring
  rw [hpos, hneg]
  ring

/-! ### The `ℓ²` bound in terms of the `U³` norm -/

/-- `‖T_k^Q(f,g)‖_{ℓ²} ≤ 16 M ‖w_Q‖_{U³([2^k])} ‖f‖_{ℓ⁴} ‖g‖_{ℓ⁴}`. -/
theorem eLpNorm_bilin_weight_le_gowers {χ : ℝ → ℝ} (hχ : IsCutoff χ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (Q k : ℕ) (f g : ℤ →₀ ℂ),
      eLpNorm (bilin (weight χ Q k) ⇑f ⇑g) 2 Measure.count ≤
        ENNReal.ofReal (16 * M * gowersNormInterval 3 (pow2 k) (blockWeight (Finset.Ioc (Q / 2) Q))) *
          eLpNorm (⇑f) 4 Measure.count * eLpNorm (⇑g) 4 Measure.count := by
  obtain ⟨M, hM0, h0, h2⟩ := exists_bounds_phiPos hχ
  have hφ : ContDiff ℝ 2 (phiPos χ) := (contDiff_phiPos hχ).of_le (by simp)
  refine ⟨M, hM0, fun Q k f g => ?_⟩
  set W : ℤ → ℂ := blockWeight (Finset.Ioc (Q / 2) Q) with hW
  have hS : ∀ f g : ℤ →₀ ℂ, eLpNorm (Splus (phiPos χ) (pow2 k) W ⇑f ⇑g) 2 Measure.count ≤
      ENNReal.ofReal (8 * M * gowersNormInterval 3 (pow2 k) W) * eLpNorm (⇑f) 4 Measure.count *
        eLpNorm (⇑g) 4 Measure.count := fun f g =>
    PrimeBHT.U3MaxMod.eLpNorm_smooth_le_real (pow2 k) W f g hφ (support_phiPos_subset hχ) h0 h2
  have heq : bilin (weight χ Q k) ⇑f ⇑g =
      Splus (phiPos χ) (pow2 k) W ⇑f ⇑g - Splus (phiPos χ) (pow2 k) W ⇑g ⇑f := by
    funext x
    exact bilin_weight_eq hχ Q k _ _ x
  have hU0 : 0 ≤ gowersNormInterval 3 (pow2 k) W :=
    div_nonneg (PrimeCarleson.Proof.Paper.gowersNorm_nonneg _ _)
      (PrimeCarleson.Proof.Paper.gowersNorm_nonneg _ _)
  rw [heq]
  refine (eLpNorm_sub_le (by norm_num)).trans ?_
  have h16 : ENNReal.ofReal (16 * M * gowersNormInterval 3 (pow2 k) W) =
      2 * ENNReal.ofReal (8 * M * gowersNormInterval 3 (pow2 k) W) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  rw [h16]
  calc _ ≤ ENNReal.ofReal (8 * M * gowersNormInterval 3 (pow2 k) W) * eLpNorm (⇑f) 4 Measure.count *
        eLpNorm (⇑g) 4 Measure.count +
      ENNReal.ofReal (8 * M * gowersNormInterval 3 (pow2 k) W) * eLpNorm (⇑g) 4 Measure.count *
        eLpNorm (⇑f) 4 Measure.count := add_le_add (hS f g) (hS g f)
    _ = _ := by ring

/-! ### The `(4,4,2)` estimate -/

/-- **The `(4,4,2)` estimate** (stage (a)): for every `δ > 0` there is `C` such that for all `Q ≥ 1`
and `k` with `Q^{20} ≤ 2^k`, and all finitely supported `f, g`,
`‖T_k^Q(f,g)‖_{ℓ²} ≤ C Q^{δ-3/8} ‖f‖_{ℓ⁴} ‖g‖_{ℓ⁴}`. -/
theorem eLpNorm_single_442 {χ : ℝ → ℝ} (hχ : IsCutoff χ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q k : ℕ), 1 ≤ Q → (Q : ℝ) ^ 20 ≤ 2 ^ k → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (bilin (weight χ Q k) ⇑f ⇑g) (ENNReal.ofReal 2) Measure.count ≤
        ENNReal.ofReal (C * (Q : ℝ) ^ (δ - 3 / 8)) *
          eLpNorm f (ENNReal.ofReal 4) Measure.count * eLpNorm g (ENNReal.ofReal 4) Measure.count := by
  obtain ⟨M, hM0, hM⟩ := eLpNorm_bilin_weight_le_gowers hχ
  obtain ⟨C₁, hC₁⟩ := PrimeCarleson.Proof.FplusProp21.exists_gowersNormInterval_blockWeight_le hδ
  refine ⟨16 * M * max C₁ 0, by positivity, fun Q k hQ hQk f g => ?_⟩
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hB : ∀ q ∈ Finset.Ioc (Q / 2) Q, (Q : ℝ) / 2 ≤ (q : ℝ) ∧ (q : ℝ) ≤ Q := by
    intro q hq
    rw [Finset.mem_Ioc] at hq
    have h1 : Q < q * 2 := (Nat.div_lt_iff_lt_mul (by norm_num)).1 hq.1
    have h1' : (Q : ℝ) < q * 2 := by exact_mod_cast h1
    exact ⟨by linarith, by exact_mod_cast hq.2⟩
  have hU := hC₁ (Q : ℝ) hQ1 (Finset.Ioc (Q / 2) Q) hB (pow2 k) (by simpa [pow2] using hQk)
  have hU' : gowersNormInterval 3 (pow2 k) (blockWeight (Finset.Ioc (Q / 2) Q)) ≤
      max C₁ 0 * (Q : ℝ) ^ (δ - 3 / 8) :=
    hU.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hQ0.le _))
  have h := hM Q k f g
  simp only [ENNReal.ofReal_ofNat] at h ⊢
  refine h.trans ?_
  have : 16 * M * gowersNormInterval 3 (pow2 k) (blockWeight (Finset.Ioc (Q / 2) Q)) ≤
      16 * M * max C₁ 0 * (Q : ℝ) ^ (δ - 3 / 8) := by
    rw [mul_assoc (16 * M)]
    exact mul_le_mul_of_nonneg_left hU' (by positivity)
  gcongr

end PrimeBHT.SingleScaleL1
