module

public import PrimeBHT.TimeFrequency.X2.Disc.WhitneyCutoff
public import PrimeBHT.TimeFrequency.X2.SymbolDecomposition
import Mathlib.Data.Int.Log

/-!
# X2, node V05-3b (R1, scalar part): the symbol decomposition with weights `w_k`

`wcut` properties (`0 ≤ wcut ≤ 1`, continuity, `wcut ≠ 0 ⇒ 60 < |x₂ - x₁| < 260`), and the pointwise decomposition
`m(t) = Σ_{k,n} c_{k,n} w_k e^{iπ n 2^{-k} t/4}` for every weight family `w` with `|w_k| ≤ 1`,
`w_k ≠ 0 ⇒ 3/10 < |2^{-k} t| < 5/2`, `ρ(2^{-k} t) ≠ 0 ⇒ w_k = 1` (the cutoff `ρ̃(2^{-k}t)` of V04 may be replaced by any
such family; for the Whitney cutoff `w_k = wcut(2^{7-k} ξ)`).
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Real

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Disc

/-! ### `wcut` -/

theorem wcut_term_nonneg (lo hi : ℤ) (x : ℝ × ℝ) (p : ℤ × ℤ) :
    0 ≤ (if lo ≤ |p.2 - p.1| ∧ |p.2 - p.1| ≤ hi then wphi (x.1 - p.1) * wphi (x.2 - p.2) else 0) := by
  split_ifs
  · exact mul_nonneg (wphi_nonneg _) (wphi_nonneg _)
  · exact le_rfl

theorem wcut_nonneg (lo hi : ℤ) (x : ℝ × ℝ) : 0 ≤ wcut lo hi x :=
  tsum_nonneg (wcut_term_nonneg lo hi x)

theorem wcut_le_one (lo hi : ℤ) (x : ℝ × ℝ) : wcut lo hi x ≤ 1 := by
  have hs : Summable fun p : ℤ × ℤ => wphi (x.1 - p.1) * wphi (x.2 - p.2) :=
    Summable.mul_of_nonneg (f := fun n : ℤ => wphi (x.1 - n)) (g := fun n : ℤ => wphi (x.2 - n))
      (hasSum_wphi x.1).summable (hasSum_wphi x.2).summable
      (fun n => wphi_nonneg _) (fun n => wphi_nonneg _)
  have h1 := (hasSum_wphi x.1).mul (hasSum_wphi x.2) hs
  rw [mul_one] at h1
  have hle : ∀ p : ℤ × ℤ, (if lo ≤ |p.2 - p.1| ∧ |p.2 - p.1| ≤ hi then wphi (x.1 - p.1) * wphi (x.2 - p.2) else 0) ≤
      wphi (x.1 - p.1) * wphi (x.2 - p.2) := by
    intro p
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (wphi_nonneg _) (wphi_nonneg _)
  have hsum : Summable fun p : ℤ × ℤ =>
      (if lo ≤ |p.2 - p.1| ∧ |p.2 - p.1| ≤ hi then wphi (x.1 - p.1) * wphi (x.2 - p.2) else 0) :=
    Summable.of_nonneg_of_le (wcut_term_nonneg lo hi x) hle hs
  calc wcut lo hi x ≤ ∑' p : ℤ × ℤ, wphi (x.1 - p.1) * wphi (x.2 - p.2) := hsum.tsum_le_tsum hle hs
    _ = 1 := h1.tsum_eq

theorem wcut_ne_zero_bounds {lo hi : ℤ} {x : ℝ × ℝ} (h : wcut lo hi x ≠ 0) :
    (lo : ℝ) - 2 < |x.2 - x.1| ∧ |x.2 - x.1| < hi + 2 := by
  by_contra hc
  apply h
  unfold wcut
  have hterm : ∀ p : ℤ × ℤ, (if lo ≤ |p.2 - p.1| ∧ |p.2 - p.1| ≤ hi then
      wphi (x.1 - p.1) * wphi (x.2 - p.2) else 0) = 0 := by
    intro p
    by_cases h0 : wphi (x.1 - p.1) * wphi (x.2 - p.2) = 0
    · simp [h0]
    · obtain ⟨c1, c2⟩ := abs_close (abs_sub_lt_of_ne_zero h0)
      by_cases hcond : lo ≤ |p.2 - p.1| ∧ |p.2 - p.1| ≤ hi
      · exfalso
        apply hc
        have h1 : (lo : ℝ) ≤ |((p.2 - p.1 : ℤ) : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast hcond.1
        have h2 : |((p.2 - p.1 : ℤ) : ℝ)| ≤ hi := by
          rw [← Int.cast_abs]; exact_mod_cast hcond.2
        constructor <;> linarith
      · rw [ite_eq_right hcond]
  rw [tsum_congr hterm]
  simp

theorem continuous_wcut (lo hi : ℤ) : Continuous (wcut lo hi) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  set F : Finset (ℤ × ℤ) := Finset.Icc (⌊x₀.1⌋ - 3) (⌊x₀.1⌋ + 3) ×ˢ Finset.Icc (⌊x₀.2⌋ - 3) (⌊x₀.2⌋ + 3) with hF
  have hnhds : {x : ℝ × ℝ | |x.1 - x₀.1| < 1 ∧ |x.2 - x₀.2| < 1} ∈ nhds x₀ := by
    apply IsOpen.mem_nhds _ (by simp)
    exact (isOpen_lt (continuous_abs.comp (continuous_fst.sub continuous_const)) continuous_const).inter
      (isOpen_lt (continuous_abs.comp (continuous_snd.sub continuous_const)) continuous_const)
  have hw := contDiff_wphi.continuous
  have hcont : Continuous fun x : ℝ × ℝ => ∑ p ∈ F,
      (if lo ≤ |p.2 - p.1| ∧ |p.2 - p.1| ≤ hi then wphi (x.1 - p.1) * wphi (x.2 - p.2) else 0) := by
    refine continuous_finsetSum _ fun p _ => ?_
    split_ifs
    · fun_prop
    · exact continuous_const
  refine hcont.continuousAt.congr ?_
  filter_upwards [hnhds] with x hx
  symm
  unfold wcut
  apply tsum_eq_sum
  intro p hp
  by_cases h0 : wphi (x.1 - p.1) * wphi (x.2 - p.2) = 0
  · simp [h0]
  · exfalso
    apply hp
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h0
    obtain ⟨a1, a2⟩ := wphi_ne_zero h1
    obtain ⟨b1, b2⟩ := wphi_ne_zero h2
    obtain ⟨hx1, hx2⟩ := hx
    rw [abs_lt] at hx1 hx2
    have f1 := Int.floor_le x₀.1
    have f2 := Int.lt_floor_add_one x₀.1
    have g1 := Int.floor_le x₀.2
    have g2 := Int.lt_floor_add_one x₀.2
    rw [hF, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · have : ((⌊x₀.1⌋ : ℝ) - 3) < (p.1 : ℝ) := by linarith
      have : ⌊x₀.1⌋ - 3 < p.1 := by exact_mod_cast this
      omega
    · have : (p.1 : ℝ) < ((⌊x₀.1⌋ : ℝ) + 3) := by linarith
      have : p.1 < ⌊x₀.1⌋ + 3 := by exact_mod_cast this
      omega
    · have : ((⌊x₀.2⌋ : ℝ) - 3) < (p.2 : ℝ) := by linarith
      have : ⌊x₀.2⌋ - 3 < p.2 := by exact_mod_cast this
      omega
    · have : (p.2 : ℝ) < ((⌊x₀.2⌋ : ℝ) + 3) := by linarith
      have : p.2 < ⌊x₀.2⌋ + 3 := by exact_mod_cast this
      omega

/-! ### The weighted decomposition -/

/-- `c_{k,n} w_k e^{iπ n 2^{-k} t/4}`. -/
def gTerm (c : ℤ → ℤ → ℂ) (w : ℤ → ℝ) (t : ℝ) (p : ℤ × ℤ) : ℂ :=
  c p.1 p.2 * (w p.1 : ℂ) * Complex.exp (((π * p.2 * (2 : ℝ) ^ (-p.1) * t / 4 : ℝ) : ℂ) * Complex.I)

theorem norm_gTerm (c : ℤ → ℤ → ℂ) (w : ℤ → ℝ) (t : ℝ) (p : ℤ × ℤ) :
    ‖gTerm c w t p‖ = ‖c p.1 p.2‖ * |w p.1| := by
  rw [gTerm, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem exists_window' {t : ℝ} (ht : t ≠ 0) :
    ∃ k₀ : ℤ, ∀ k : ℤ, (3 / 10 < |(2 : ℝ) ^ (-k) * t| ∧ |(2 : ℝ) ^ (-k) * t| < 5 / 2) →
      k₀ ≤ k ∧ k ≤ k₀ + 3 := by
  have hat : 0 < |t| := abs_pos.2 ht
  set j : ℤ := Int.log 2 |t| with hj
  have hj1 : (2 : ℝ) ^ j ≤ |t| := Int.zpow_log_le_self (by norm_num) hat
  have hj2 : |t| < (2 : ℝ) ^ (j + 1) := Int.lt_zpow_succ_log_self (by norm_num) _
  refine ⟨j - 1, fun k hk => ?_⟩
  obtain ⟨h1, h2⟩ := hk
  rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)] at h1 h2
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-k) := zpow_pos (by norm_num) _
  have hA : (2 : ℝ) ^ (-k + j) < (2 : ℝ) ^ (2 : ℤ) := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    calc (2 : ℝ) ^ (-k) * 2 ^ j ≤ 2 ^ (-k) * |t| := by gcongr
      _ < 5 / 2 := h2
      _ < 2 ^ (2 : ℤ) := by norm_num
  have hB : (2 : ℝ) ^ (-2 : ℤ) < (2 : ℝ) ^ (-k + (j + 1)) := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    calc (2 : ℝ) ^ (-2 : ℤ) < 3 / 10 := by norm_num
      _ < 2 ^ (-k) * |t| := h1
      _ ≤ 2 ^ (-k) * 2 ^ (j + 1) := by gcongr
  rw [zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)] at hA hB
  constructor <;> omega

theorem hasSum_gTerm_fiber (m : ℝ → ℂ) (hm : ContDiffOn ℝ ∞ m {0}ᶜ) (t : ℝ) (k : ℤ) (w : ℝ)
    (hw2 : w ≠ 0 → |(2 : ℝ) ^ (-k) * t| < 5 / 2)
    (hw3 : rho ((2 : ℝ) ^ (-k) * t) ≠ 0 → w = 1) :
    HasSum (fun n : ℤ => symbolCoeff m k n * (w : ℂ) *
      Complex.exp (((π * n * (2 : ℝ) ^ (-k) * t / 4 : ℝ) : ℂ) * Complex.I))
      (m t * (rho ((2 : ℝ) ^ (-k) * t) : ℂ)) := by
  set s : ℝ := (2 : ℝ) ^ (-k) * t with hs
  have hms : m ((2 : ℝ) ^ k * s) = m t := by
    rw [hs, ← mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simp
  by_cases hw0 : w = 0
  · have hr : rho s = 0 := by
      by_contra hr
      have := hw3 hr
      rw [hw0] at this; norm_num at this
    have : (fun n : ℤ => symbolCoeff m k n * (w : ℂ) *
        Complex.exp (((π * n * (2 : ℝ) ^ (-k) * t / 4 : ℝ) : ℂ) * Complex.I)) = fun _ => 0 := by
      funext n; rw [hw0]; simp
    rw [this, hr]
    simp only [Complex.ofReal_zero, mul_zero]
    exact hasSum_zero
  · have hs4 : -4 ≤ s ∧ s < 4 := by
      have := hw2 hw0
      rw [abs_lt] at this
      constructor <;> linarith [this.1, this.2]
    have h1 := hasSum_fcoef (contDiff_symbolPiece hm k) (fun x hx => symbolPiece_eq_zero_of_two_le m k hx.le) hs4
    have h2 := h1.mul_left (w : ℂ)
    have hval : (w : ℂ) * symbolPiece m k s = m t * (rho s : ℂ) := by
      simp only [symbolPiece, hms]
      by_cases hr : rho s = 0
      · rw [hr]; simp
      · rw [hw3 hr]; simp; ring
    rw [hval] at h2
    convert h2 using 1
    funext n
    simp only [symbolCoeff]
    have : ((π * n * s / 4 : ℝ) : ℂ) * Complex.I = π * Complex.I * n * s / 4 := by
      push_cast; ring
    rw [show (π * n * (2 : ℝ) ^ (-k) * t / 4 : ℝ) = π * n * s / 4 by rw [hs]; ring, this]
    ring

theorem summable_norm_gTerm {c : ℤ → ℤ → ℂ} {b : ℤ → ℝ} (hb : Summable b)
    (hcb : ∀ k n, ‖c k n‖ ≤ b n) {t : ℝ} (ht : t ≠ 0) (w : ℤ → ℝ) (hw1 : ∀ k, |w k| ≤ 1)
    (hw2 : ∀ k, w k ≠ 0 → 3 / 10 < |(2 : ℝ) ^ (-k) * t| ∧ |(2 : ℝ) ^ (-k) * t| < 5 / 2) :
    Summable (fun p : ℤ × ℤ => ‖gTerm c w t p‖) ∧
      ∑' p : ℤ × ℤ, ‖gTerm c w t p‖ ≤ 4 * ∑' n, b n := by
  have hb0 : ∀ n, 0 ≤ b n := fun n => (norm_nonneg _).trans (hcb 0 n)
  obtain ⟨k₀, hk₀⟩ := exists_window' ht
  set wi : Finset ℤ := Finset.Icc k₀ (k₀ + 3) with hwi
  set f : ℤ → ℝ := fun k => if k ∈ wi then 1 else 0 with hf
  have hfs : Summable f := summable_of_ne_finset_zero (s := wi) (fun k hk => by simp [hf, hk])
  have hG : Summable (fun p : ℤ × ℤ => f p.1 * b p.2) :=
    Summable.mul_of_nonneg hfs hb (fun k => by simp only [hf, Pi.zero_apply]; split_ifs <;> norm_num)
      (fun n => hb0 n)
  have hle : ∀ p : ℤ × ℤ, ‖gTerm c w t p‖ ≤ f p.1 * b p.2 := by
    intro p
    rw [norm_gTerm]
    by_cases hp : p.1 ∈ wi
    · simp only [hf, hp, ite_true, one_mul]
      calc ‖c p.1 p.2‖ * |w p.1| ≤ b p.2 * 1 :=
            mul_le_mul (hcb _ _) (hw1 _) (abs_nonneg _) (hb0 _)
        _ = b p.2 := mul_one _
    · have : w p.1 = 0 := by
        by_contra hne
        obtain ⟨h1, h2⟩ := hk₀ p.1 (hw2 _ hne)
        exact hp (Finset.mem_Icc.2 ⟨h1, h2⟩)
      rw [this, abs_zero, mul_zero]
      simp [hf, hp]
  have hsum := Summable.of_nonneg_of_le (fun p => norm_nonneg _) hle hG
  refine ⟨hsum, ?_⟩
  have hfn : ∑' k, f k = 4 := by
    rw [tsum_eq_sum (s := wi) (fun k hk => by simp [hf, hk])]
    rw [Finset.sum_congr rfl (fun k hk => by simp [hf, hk] : ∀ k ∈ wi, f k = 1)]
    rw [Finset.sum_const, hwi, Int.card_Icc]
    have : (k₀ + 3 + 1 - k₀).toNat = 4 := by omega
    rw [this]
    norm_num
  calc ∑' p : ℤ × ℤ, ‖gTerm c w t p‖ ≤ ∑' p : ℤ × ℤ, f p.1 * b p.2 :=
        hsum.tsum_le_tsum hle hG
    _ = (∑' k, f k) * ∑' n, b n := by
        rw [← tsum_mul_tsum_of_summable_norm]
        · simpa [Real.norm_eq_abs, abs_of_nonneg] using hfs.norm
        · simpa [Real.norm_eq_abs, abs_of_nonneg (hb0 _)] using hb.norm
    _ = 4 * ∑' n, b n := by rw [hfn]

/-- **The weighted pointwise decomposition.**  For `t ≠ 0` and weights `w` with `|w_k| ≤ 1`,
`w_k ≠ 0 ⇒ 3/10 < |2^{-k}t| < 5/2`, `ρ(2^{-k}t) ≠ 0 ⇒ w_k = 1`: `m(t) = Σ_{k,n} c_{k,n} w_k e^{iπ n 2^{-k} t/4}`
(absolutely summable). -/
theorem hasSum_gTerm {m : ℝ → ℂ} (hm : ContDiffOn ℝ ∞ m {0}ᶜ) {b : ℤ → ℝ} (hb : Summable b)
    (hcb : ∀ k n, ‖symbolCoeff m k n‖ ≤ b n) {t : ℝ} (ht : t ≠ 0) (w : ℤ → ℝ) (hw1 : ∀ k, |w k| ≤ 1)
    (hw2 : ∀ k, w k ≠ 0 → 3 / 10 < |(2 : ℝ) ^ (-k) * t| ∧ |(2 : ℝ) ^ (-k) * t| < 5 / 2)
    (hw3 : ∀ k, rho ((2 : ℝ) ^ (-k) * t) ≠ 0 → w k = 1) :
    HasSum (gTerm (symbolCoeff m) w t) (m t) := by
  obtain ⟨hs1, -⟩ := summable_norm_gTerm hb hcb ht w hw1 hw2
  have hs : Summable (gTerm (symbolCoeff m) w t) := Summable.of_norm hs1
  have hf : ∀ k : ℤ, HasSum (fun n : ℤ => gTerm (symbolCoeff m) w t (k, n))
      (m t * (rho ((2 : ℝ) ^ (-k) * t) : ℂ)) := fun k =>
    hasSum_gTerm_fiber m hm t k (w k) (fun h => (hw2 k h).2) (hw3 k)
  have h1 : HasSum (fun k : ℤ => m t * (rho ((2 : ℝ) ^ (-k) * t) : ℂ)) (∑' p, gTerm (symbolCoeff m) w t p) :=
    hs.hasSum.prod_fiberwise hf
  have h2 := (Complex.hasSum_ofReal.2 (hasSum_rho_zpow ht)).mul_left (m t)
  rw [Complex.ofReal_one, mul_one] at h2
  have h3 := h1.unique h2
  have h4 := hs.hasSum
  rwa [h3] at h4

end PrimeBHT.TimeFrequency.X2.Disc
