module

public import PrimeBHT.TimeFrequency.X2.CZ.Statements
public import PrimeBHT.TimeFrequency.X2.SymbolDecomposition
public import PrimeBHT.TimeFrequency.X2.ClassKernel

/-!
# V14 (paraproduct), symbols: the classes `IsLowSymbol`, `IsLPSymbol`, the Mikhlin bounds of their sums

The symbol classes of the draft `drafts/x2-interface/05-V13-V15-Tree.lean.txt` (transcribed unchanged) and
the symbol calculus used by `X2/Paraproduct.lean`:

* `fscale J j = 2^{J j}`, the frequency scale of the `j`-th symbol;
* `IsAdaptedSymbol J j σ`: the weakest class (smooth, `supp σ ⊆ {|ξ| ≤ 2^{2J} 2^{J j}}`, derivatives of order `≤ 2`
  adapted at scale `2^{Jj}`): both `IsLowSymbol` and `IsLPSymbol` (for `a₀ ≥ 2`) are adapted;
* `isMikhlin_sum_lp`: `∑_{j ∈ js} c_j σ_j` is a Mikhlin symbol (order `3`) with a constant `3 · 2^{6J}` for LP symbols
  `σ_j`, `|c_j| ≤ 1`, uniformly in `js` (bounded overlap: at most three scales `j` see a given `ξ`);
* the low-frequency remainder `lowRem J j σ = σ - σ(0) ϑ_j` (`ϑ_j = θ(·/(2^{2J+1} 2^{Jj}))`, `θ = 1` on `[-1,1]`):
  `lowRem` vanishes at `0`, is `O(|ξ| / 2^{Jj})` and has derivatives `O(2^{-Jja})`, and the family
  `(lowRem J j (σ_j))_{j ∈ js}` has Mikhlin sums with a constant independent of `js`
  (`isMikhlin_sum_lowRem`: geometric series in `j`).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-! ## The symbol classes (anchored at a real number `A > 0`) -/

/-- A symbol adapted at frequency scale `A 2^{Jj}` with support in `{|ξ| ≤ A 2^{J(j + 1/2)}}`
(V14's first slot, DPLMV L766-768), `a₀` derivatives, amplitude `1`.  The anchor `A > 0` is a free real number
(V13 route check §4: the symbols of a tree live at the frequency scale `ℓ/8`, not at `2^{Jj}`). -/
def IsLowSymbol (A : ℝ) (J a₀ : ℕ) (j : ℤ) (σ : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ σ ∧ (∀ ξ, A * (2 : ℝ) ^ ((J : ℝ) * (j + 1 / 2)) < |ξ| → σ ξ = 0) ∧
    ∀ a : ℕ, a ≤ a₀ → ∀ ξ, (A * (2 : ℝ) ^ ((J : ℝ) * j)) ^ a * ‖iteratedDeriv a σ ξ‖ ≤ 1

/-- A Littlewood-Paley symbol at scale `A 2^{Jj}`: support in `{A 2^{Jj} ≤ |ξ| ≤ A 2^{J(j+2)}}`. -/
def IsLPSymbol (A : ℝ) (J a₀ : ℕ) (j : ℤ) (σ : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ σ ∧
    (∀ ξ, (|ξ| < A * (2 : ℝ) ^ ((J : ℝ) * j) ∨ A * (2 : ℝ) ^ ((J : ℝ) * (j + 2)) < |ξ|) → σ ξ = 0) ∧
    ∀ a : ℕ, a ≤ a₀ → ∀ ξ, (A * (2 : ℝ) ^ ((J : ℝ) * j)) ^ a * ‖iteratedDeriv a σ ξ‖ ≤ 1

/-! ## The scale `2^{Jj}` and the anchored scale `A 2^{Jj}` -/

/-- The power `2^{J j}`. -/
def pw (J : ℕ) (j : ℤ) : ℝ := (2 : ℝ) ^ ((J : ℝ) * j)

theorem pw_pos (J : ℕ) (j : ℤ) : 0 < pw J j := Real.rpow_pos_of_pos (by norm_num) _

theorem pw_eq_zpow (J : ℕ) (j : ℤ) : pw J j = (2 : ℝ) ^ ((J : ℤ) * j) := by
  unfold pw
  rw [← Real.rpow_intCast]
  push_cast
  rfl

theorem pw_add (J : ℕ) (j k : ℤ) : pw J (j + k) = pw J j * pw J k := by
  unfold pw
  rw [← Real.rpow_add (by norm_num)]
  congr 1
  push_cast
  ring

theorem pw_one_eq (J : ℕ) : pw J 1 = (2 : ℝ) ^ J := by
  rw [pw_eq_zpow]
  simp

theorem pw_succ (J : ℕ) (j : ℤ) : pw J (j + 1) = 2 ^ J * pw J j := by
  rw [pw_add, pw_one_eq, mul_comm]

theorem pw_lt_succ {J : ℕ} (hJ : 1 ≤ J) (j : ℤ) : pw J j < pw J (j + 1) := by
  rw [pw_succ]
  have h1 : (1 : ℝ) < 2 ^ J := one_lt_pow₀ (by norm_num) (by omega)
  nlinarith [pw_pos J j]

theorem pw_strictMono {J : ℕ} (hJ : 1 ≤ J) : StrictMono (pw J) :=
  strictMono_int_of_lt_succ fun j => pw_lt_succ hJ j

theorem pw_add_nat (J : ℕ) (j : ℤ) (n : ℕ) : pw J (j + n) = 2 ^ (J * n) * pw J j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show j + ((n + 1 : ℕ) : ℤ) = (j + n) + 1 by push_cast; ring, pw_succ, ih]
    rw [show J * (n + 1) = J * n + J by ring, pow_add]
    ring

/-- The anchored frequency scale `A 2^{J j}` of the `j`-th symbol. -/
def fscale (A : ℝ) (J : ℕ) (j : ℤ) : ℝ := A * pw J j

theorem fscale_pos {A : ℝ} (hA : 0 < A) (J : ℕ) (j : ℤ) : 0 < fscale A J j := mul_pos hA (pw_pos J j)

/-- `A 2^{J (j + 2)} = 2^{2J} · A 2^{J j}`. -/
theorem rpow_J_add_two (A : ℝ) (J : ℕ) (j : ℤ) :
    A * (2 : ℝ) ^ ((J : ℝ) * ((j : ℝ) + 2)) = (2 : ℝ) ^ (2 * J) * fscale A J j := by
  unfold fscale pw
  rw [mul_add, Real.rpow_add (by norm_num)]
  rw [show (J : ℝ) * 2 = ((2 * J : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  ring

/-- `A 2^{J (j + 1/2)} ≤ 2^{2J} A 2^{J j}`. -/
theorem rpow_J_add_half_le {A : ℝ} (hA : 0 < A) (J : ℕ) (j : ℤ) :
    A * (2 : ℝ) ^ ((J : ℝ) * ((j : ℝ) + 1 / 2)) ≤ (2 : ℝ) ^ (2 * J) * fscale A J j := by
  rw [← rpow_J_add_two]
  gcongr
  · norm_num
  have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  nlinarith

theorem fscale_strictMono {A : ℝ} (hA : 0 < A) {J : ℕ} (hJ : 1 ≤ J) : StrictMono (fscale A J) := by
  intro j k hjk
  unfold fscale
  exact mul_lt_mul_of_pos_left (pw_strictMono hJ hjk) hA

theorem fscale_add_nat (A : ℝ) (J : ℕ) (j : ℤ) (n : ℕ) :
    fscale A J (j + n) = 2 ^ (J * n) * fscale A J j := by
  unfold fscale
  rw [pw_add_nat]; ring

/-- Bounded overlap of the LP bands: at most three scales `j` satisfy `A 2^{Jj} ≤ |ξ| ≤ 2^{2J} A 2^{Jj}`. -/
theorem card_filter_band_le {A : ℝ} (hA : 0 < A) {J : ℕ} (hJ : 1 ≤ J) (js : Finset ℤ) (t : ℝ) :
    (js.filter fun j => fscale A J j ≤ t ∧ t ≤ (2 : ℝ) ^ (2 * J) * fscale A J j).card ≤ 3 := by
  set S := js.filter fun j => fscale A J j ≤ t ∧ t ≤ (2 : ℝ) ^ (2 * J) * fscale A J j with hS
  rcases S.eq_empty_or_nonempty with h | h
  · rw [h]; simp
  · set j₀ := S.min' h with hj₀
    have hj₀S : j₀ ∈ S := S.min'_mem h
    have hsub : S ⊆ Finset.Icc j₀ (j₀ + 2) := by
      intro j hj
      rw [Finset.mem_Icc]
      refine ⟨S.min'_le j hj, ?_⟩
      by_contra hlt
      push Not at hlt
      have hj3 : j₀ + 3 ≤ j := by omega
      have hmem := (Finset.mem_filter.1 hj).2
      have hmem0 := (Finset.mem_filter.1 hj₀S).2
      have hmono : fscale A J (j₀ + 3) ≤ fscale A J j := (fscale_strictMono hA hJ).monotone hj3
      have h3 : fscale A J (j₀ + 3) = 2 ^ (J * 3) * fscale A J j₀ := by
        have := fscale_add_nat A J j₀ 3
        simpa using this
      have h4 : (2 : ℝ) ^ (2 * J) < 2 ^ (J * 3) := pow_lt_pow_right₀ (by norm_num) (by omega)
      have hp := fscale_pos hA J j₀
      nlinarith [hmem.1, hmem0.2]
    calc S.card ≤ (Finset.Icc j₀ (j₀ + 2)).card := Finset.card_le_card hsub
      _ = 3 := by simp; omega

/-! ## Adapted symbols -/

/-- The weakest class used for the single-scale (maximal function) bound: smooth, supported in
`{|ξ| ≤ 2^{2J} 2^{Jj}}`, derivatives of order `≤ 2` adapted at scale `2^{Jj}` with amplitude `1`. -/
def IsAdaptedSymbol (A : ℝ) (J : ℕ) (j : ℤ) (σ : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ σ ∧ (∀ ξ, (2 : ℝ) ^ (2 * J) * fscale A J j < |ξ| → σ ξ = 0) ∧
    ∀ a : ℕ, a ≤ 2 → ∀ ξ, fscale A J j ^ a * ‖iteratedDeriv a σ ξ‖ ≤ 1

theorem IsLowSymbol.adapted {A : ℝ} (hA : 0 < A) {J a₀ : ℕ} (ha₀ : 2 ≤ a₀) {j : ℤ} {σ : ℝ → ℂ} (h : IsLowSymbol A J a₀ j σ) :
    IsAdaptedSymbol A J j σ :=
  ⟨h.1, fun ξ hξ => h.2.1 ξ (lt_of_le_of_lt (rpow_J_add_half_le hA J j) hξ),
    fun a ha ξ => h.2.2 a (le_trans ha ha₀) ξ⟩

theorem IsLPSymbol.adapted {A : ℝ} {J a₀ : ℕ} (ha₀ : 2 ≤ a₀) {j : ℤ} {σ : ℝ → ℂ} (h : IsLPSymbol A J a₀ j σ) :
    IsAdaptedSymbol A J j σ :=
  ⟨h.1, fun ξ hξ => h.2.1 ξ (Or.inr (by rw [rpow_J_add_two]; exact hξ)),
    fun a ha ξ => h.2.2 a (le_trans ha ha₀) ξ⟩

theorem IsAdaptedSymbol.contDiff {A : ℝ} {J : ℕ} {j : ℤ} {σ : ℝ → ℂ} (h : IsAdaptedSymbol A J j σ) :
    ContDiff ℝ ∞ σ := h.1

theorem IsAdaptedSymbol.hasCompactSupport {A : ℝ} {J : ℕ} {j : ℤ} {σ : ℝ → ℂ} (h : IsAdaptedSymbol A J j σ) :
    HasCompactSupport σ :=
  hasCompactSupport_of_far (c := 0) (r := (2 : ℝ) ^ (2 * J) * fscale A J j) (fun ξ hξ => h.2.1 ξ (by simpa using hξ))

/-! ## Mikhlin sums -/

theorem isMikhlin_sum_of_bound (js : Finset ℤ) (c : ℤ → ℂ) (hc : ∀ j, ‖c j‖ ≤ 1)
    (σ : ℤ → ℝ → ℂ) (hσ : ∀ j ∈ js, ContDiff ℝ ∞ (σ j)) {B : ℝ}
    (hB : ∀ a : ℕ, a ≤ 3 → ∀ ξ : ℝ, ξ ≠ 0 → ∑ j ∈ js, |ξ| ^ a * ‖iteratedDeriv a (σ j) ξ‖ ≤ B) :
    CZ.IsMikhlin 3 B (fun ξ => ∑ j ∈ js, c j * σ j ξ) := by
  have hcd : ContDiff ℝ ∞ (fun ξ => ∑ j ∈ js, c j * σ j ξ) :=
    ContDiff.sum fun j hj => contDiff_const.mul (hσ j hj)
  refine ⟨(hcd.contDiffOn).of_le (by norm_cast), fun a ha ξ hξ => ?_⟩
  have hder : iteratedDeriv a (fun ξ => ∑ j ∈ js, c j * σ j ξ) ξ =
      ∑ j ∈ js, c j * iteratedDeriv a (σ j) ξ := by
    have h1 : (fun ξ => ∑ j ∈ js, c j * σ j ξ) = ∑ j ∈ js, (fun ξ => c j * σ j ξ) := by
      ext ξ; simp
    rw [h1, iteratedDeriv_sum (fun j hj => ((contDiff_const.mul (hσ j hj)).of_le
      (by exact_mod_cast le_top)).contDiffAt)]
    refine Finset.sum_congr rfl fun j hj => ?_
    exact iteratedDeriv_const_mul (c j) ((hσ j hj).of_le (by exact_mod_cast le_top)).contDiffAt
  rw [hder]
  calc |ξ| ^ a * ‖∑ j ∈ js, c j * iteratedDeriv a (σ j) ξ‖
      ≤ |ξ| ^ a * ∑ j ∈ js, ‖c j * iteratedDeriv a (σ j) ξ‖ := by
        gcongr; exact norm_sum_le _ _
    _ = ∑ j ∈ js, |ξ| ^ a * ‖c j * iteratedDeriv a (σ j) ξ‖ := by rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ js, |ξ| ^ a * ‖iteratedDeriv a (σ j) ξ‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        gcongr
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hc j)
    _ ≤ B := hB a ha ξ hξ

theorem iteratedDeriv_eq_zero_of_open {σ : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U) (h : ∀ ξ ∈ U, σ ξ = 0)
    (a : ℕ) {ξ : ℝ} (hξ : ξ ∈ U) : iteratedDeriv a σ ξ = 0 := by
  have h' : σ =ᶠ[𝓝 ξ] (0 : ℝ → ℂ) := by
    filter_upwards [hU.mem_nhds hξ] with ξ' hξ' using h ξ' hξ'
  rw [h'.iteratedDeriv_eq a]
  simp

/-- A sum of LP symbols (coefficients `‖c_j‖ ≤ 1`) is a Mikhlin symbol of order `3`, uniformly in the index set. -/
theorem isMikhlin_sum_lp {A : ℝ} (hA : 0 < A) {J a₀ : ℕ} (hJ : 1 ≤ J) (ha₀ : 3 ≤ a₀) (js : Finset ℤ) (c : ℤ → ℂ)
    (hc : ∀ j, ‖c j‖ ≤ 1) (σ : ℤ → ℝ → ℂ) (hσ : ∀ j, IsLPSymbol A J a₀ j (σ j)) :
    CZ.IsMikhlin 3 (3 * 2 ^ (6 * J)) (fun ξ => ∑ j ∈ js, c j * σ j ξ) := by
  refine isMikhlin_sum_of_bound js c hc σ (fun j _ => (hσ j).1) fun a ha ξ hξ => ?_
  set S := js.filter fun j => fscale A J j ≤ |ξ| ∧ |ξ| ≤ (2 : ℝ) ^ (2 * J) * fscale A J j with hS
  have hzero : ∀ j ∈ js, j ∉ S → |ξ| ^ a * ‖iteratedDeriv a (σ j) ξ‖ = 0 := by
    intro j hj hjS
    have hnot : ¬ (fscale A J j ≤ |ξ| ∧ |ξ| ≤ (2 : ℝ) ^ (2 * J) * fscale A J j) := fun h =>
      hjS (Finset.mem_filter.2 ⟨hj, h⟩)
    rw [not_and_or, not_le, not_le] at hnot
    have : iteratedDeriv a (σ j) ξ = 0 := by
      rcases hnot with h | h
      · refine iteratedDeriv_eq_zero_of_open (U := {ξ' | |ξ'| < fscale A J j}) (isOpen_lt (by fun_prop) (by fun_prop))
          (fun ξ' hξ' => (hσ j).2.1 ξ' (Or.inl hξ')) a h
      · refine iteratedDeriv_eq_zero_of_open (U := {ξ' | (2 : ℝ) ^ (2 * J) * fscale A J j < |ξ'|})
          (isOpen_lt (by fun_prop) (by fun_prop))
          (fun ξ' hξ' => (hσ j).2.1 ξ' (Or.inr (by rw [rpow_J_add_two]; exact hξ'))) a h
    rw [this, norm_zero, mul_zero]
  have hbound : ∀ j ∈ S, |ξ| ^ a * ‖iteratedDeriv a (σ j) ξ‖ ≤ 2 ^ (6 * J) := by
    intro j hj
    obtain ⟨hb1, hb2⟩ := (Finset.mem_filter.1 hj).2
    have hLj := fscale_pos hA J j
    have h1 : |ξ| ^ a ≤ ((2 : ℝ) ^ (2 * J) * fscale A J j) ^ a := pow_le_pow_left₀ (abs_nonneg _) hb2 a
    have h2 := (hσ j).2.2 a (le_trans ha (by omega)) ξ
    calc |ξ| ^ a * ‖iteratedDeriv a (σ j) ξ‖
        ≤ ((2 : ℝ) ^ (2 * J) * fscale A J j) ^ a * ‖iteratedDeriv a (σ j) ξ‖ := by gcongr
      _ = ((2 : ℝ) ^ (2 * J)) ^ a * (fscale A J j ^ a * ‖iteratedDeriv a (σ j) ξ‖) := by ring
      _ ≤ ((2 : ℝ) ^ (2 * J)) ^ a * 1 := by gcongr; exact h2
      _ ≤ ((2 : ℝ) ^ (2 * J)) ^ 3 := by
        rw [mul_one]
        exact pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) ha
      _ = 2 ^ (6 * J) := by rw [← pow_mul]; ring_nf
  have hsub : S ⊆ js := Finset.filter_subset _ _
  rw [← Finset.sum_subset hsub fun j hj hjS => hzero j hj hjS]
  calc ∑ j ∈ S, |ξ| ^ a * ‖iteratedDeriv a (σ j) ξ‖ ≤ S.card • (2 : ℝ) ^ (6 * J) :=
        Finset.sum_le_card_nsmul _ _ _ hbound
    _ ≤ 3 • (2 : ℝ) ^ (6 * J) := by
        gcongr
        exact card_filter_band_le hA hJ js |ξ|
    _ = 3 * 2 ^ (6 * J) := by simp

/-! ## The low-frequency remainder -/

/-- The cutoff `ϑ_j = θ(·/(2^{2J+1} 2^{Jj}))`: `= 1` on `{|ξ| ≤ 2^{2J+1} 2^{Jj}}`, `= 0` for `|ξ| ≥ 2^{2J+2} 2^{Jj}`. -/
def lowCut (A : ℝ) (J : ℕ) (j : ℤ) (ξ : ℝ) : ℂ :=
  ((theta (((2 : ℝ) ^ (2 * J + 1) * fscale A J j)⁻¹ * ξ) : ℝ) : ℂ)

/-- The remainder `σ - σ(0) ϑ_j` of a low-frequency symbol. -/
def lowRem (A : ℝ) (J : ℕ) (j : ℤ) (σ : ℝ → ℂ) (ξ : ℝ) : ℂ := σ ξ - σ 0 * lowCut A J j ξ

theorem two_pow_mul_fscale_pos {A : ℝ} (hA : 0 < A) (J : ℕ) (j : ℤ) : 0 < (2 : ℝ) ^ (2 * J + 1) * fscale A J j :=
  mul_pos (by positivity) (fscale_pos hA J j)

theorem lowCut_eq_one {A : ℝ} (hA : 0 < A) {J : ℕ} {j : ℤ} {ξ : ℝ} (hξ : |ξ| ≤ (2 : ℝ) ^ (2 * J + 1) * fscale A J j) :
    lowCut A J j ξ = 1 := by
  unfold lowCut
  rw [theta_eq_one, Complex.ofReal_one]
  rw [abs_mul, abs_of_pos (inv_pos.2 (two_pow_mul_fscale_pos hA J j))]
  rw [inv_mul_le_iff₀ (two_pow_mul_fscale_pos hA J j)]
  linarith

theorem lowCut_eq_zero {A : ℝ} (hA : 0 < A) {J : ℕ} {j : ℤ} {ξ : ℝ} (hξ : (2 : ℝ) ^ (2 * J + 2) * fscale A J j ≤ |ξ|) :
    lowCut A J j ξ = 0 := by
  unfold lowCut
  rw [theta_eq_zero, Complex.ofReal_zero]
  rw [abs_mul, abs_of_pos (inv_pos.2 (two_pow_mul_fscale_pos hA J j))]
  rw [le_inv_mul_iff₀ (two_pow_mul_fscale_pos hA J j)]
  have : (2 : ℝ) ^ (2 * J + 2) * fscale A J j = 2 * ((2 : ℝ) ^ (2 * J + 1) * fscale A J j) := by ring
  linarith

theorem contDiff_lowCut (A : ℝ) (J : ℕ) (j : ℤ) : ContDiff ℝ ∞ (lowCut A J j) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_theta.comp (contDiff_const.mul contDiff_id))

theorem exists_bound_theta :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ i ≤ 3, ∀ s : ℝ, ‖iteratedDeriv i (fun s : ℝ => (theta s : ℂ)) s‖ ≤ R := by
  have hc : HasCompactSupport (fun s : ℝ => (theta s : ℂ)) :=
    thetaBump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hs : ContDiff ℝ ∞ (fun s : ℝ => (theta s : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_theta
  obtain ⟨C, hC0, hC⟩ := hc.exists_bound_iteratedFDeriv hs 3
  exact ⟨C, hC0, fun i hi s => by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact hC i hi s⟩

/-- The derivative bound of `ϑ_j`: `‖ϑ_j^{(i)}‖ ≤ Cθ 2^{-Jji}` for `i ≤ 3`. -/
theorem norm_iteratedDeriv_lowCut_le :
    ∃ Cθ : ℝ, 0 ≤ Cθ ∧ ∀ (A : ℝ), 0 < A → ∀ (J : ℕ) (j : ℤ), ∀ i ≤ 3, ∀ ξ : ℝ,
      ‖iteratedDeriv i (lowCut A J j) ξ‖ ≤ Cθ * (fscale A J j)⁻¹ ^ i := by
  obtain ⟨R, hR0, hR⟩ := exists_bound_theta
  refine ⟨R, hR0, fun A hA J j i hi ξ => ?_⟩
  have hf : ContDiff ℝ i (fun s : ℝ => (theta s : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp contDiff_theta).of_le (by exact_mod_cast le_top)
  have h1 : iteratedDeriv i (lowCut A J j) ξ =
      (((2 : ℝ) ^ (2 * J + 1) * fscale A J j)⁻¹) ^ i •
        iteratedDeriv i (fun s : ℝ => (theta s : ℂ)) (((2 : ℝ) ^ (2 * J + 1) * fscale A J j)⁻¹ * ξ) := by
    have := congrFun (iteratedDeriv_comp_const_smul hf
      (((2 : ℝ) ^ (2 * J + 1) * fscale A J j)⁻¹)) ξ
    exact this
  rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by have := two_pow_mul_fscale_pos hA J j; positivity)]
  have hc : ((2 : ℝ) ^ (2 * J + 1) * fscale A J j)⁻¹ ≤ (fscale A J j)⁻¹ := by
    apply inv_anti₀ (fscale_pos hA J j)
    have : (1 : ℝ) ≤ 2 ^ (2 * J + 1) := one_le_pow₀ (by norm_num)
    nlinarith [fscale_pos hA J j]
  calc (((2 : ℝ) ^ (2 * J + 1) * fscale A J j)⁻¹) ^ i * ‖iteratedDeriv i (fun s : ℝ => (theta s : ℂ)) _‖
      ≤ (fscale A J j)⁻¹ ^ i * R := by
        have h0 : 0 ≤ ((2 : ℝ) ^ (2 * J + 1) * fscale A J j)⁻¹ :=
          inv_nonneg.2 (two_pow_mul_fscale_pos hA J j).le
        have h2 : 0 ≤ (fscale A J j)⁻¹ := inv_nonneg.2 (fscale_pos hA J j).le
        exact mul_le_mul (pow_le_pow_left₀ h0 hc i) (hR i hi _) (norm_nonneg _) (pow_nonneg h2 _)
    _ = R * (fscale A J j)⁻¹ ^ i := by ring

theorem contDiff_lowRem {A : ℝ} {J : ℕ} {j : ℤ} {σ : ℝ → ℂ} (hσ : ContDiff ℝ ∞ σ) :
    ContDiff ℝ ∞ (lowRem A J j σ) :=
  hσ.sub (contDiff_const.mul (contDiff_lowCut A J j))

theorem lowRem_eq_zero_of_far {A : ℝ} (hA : 0 < A) {J a₀ : ℕ} {j : ℤ} {σ : ℝ → ℂ} (h : IsLowSymbol A J a₀ j σ) {ξ : ℝ}
    (hξ : (2 : ℝ) ^ (2 * J + 2) * fscale A J j < |ξ|) : lowRem A J j σ ξ = 0 := by
  unfold lowRem
  have h1 : σ ξ = 0 := by
    refine h.2.1 ξ (lt_of_le_of_lt (rpow_J_add_half_le hA J j) (lt_of_le_of_lt ?_ hξ))
    have : (2 : ℝ) ^ (2 * J) ≤ 2 ^ (2 * J + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith [fscale_pos hA J j]
  rw [h1, lowCut_eq_zero hA hξ.le]
  simp

theorem norm_lowRem_le {A : ℝ} (hA : 0 < A) {J a₀ : ℕ} (ha₀ : 1 ≤ a₀) {j : ℤ} {σ : ℝ → ℂ} (h : IsLowSymbol A J a₀ j σ) (ξ : ℝ) :
    ‖lowRem A J j σ ξ‖ ≤ |ξ| / fscale A J j := by
  have hL := fscale_pos hA J j
  by_cases hc : |ξ| ≤ (2 : ℝ) ^ (2 * J + 1) * fscale A J j
  · unfold lowRem
    rw [lowCut_eq_one hA hc, mul_one]
    have hd : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ σ x := fun x _ =>
      (h.1.differentiable (by simp)).differentiableAt
    have hb : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv σ x‖ ≤ (fscale A J j)⁻¹ := by
      intro x _
      have h1 : fscale A J j ^ 1 * ‖iteratedDeriv 1 σ x‖ ≤ 1 := h.2.2 1 ha₀ x
      rw [iteratedDeriv_one, pow_one] at h1
      calc ‖deriv σ x‖ = (fscale A J j)⁻¹ * (fscale A J j * ‖deriv σ x‖) := by field_simp
        _ ≤ (fscale A J j)⁻¹ * 1 := by gcongr
        _ = (fscale A J j)⁻¹ := mul_one _
    have := Convex.norm_image_sub_le_of_norm_deriv_le hd hb convex_univ (Set.mem_univ 0) (Set.mem_univ ξ)
    simpa [div_eq_inv_mul] using this
  · push Not at hc
    have h1 : σ ξ = 0 := by
      refine h.2.1 ξ (lt_of_le_of_lt (rpow_J_add_half_le hA J j) (lt_of_le_of_lt ?_ hc))
      have : (2 : ℝ) ^ (2 * J) ≤ 2 ^ (2 * J + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    unfold lowRem
    rw [h1, zero_sub, norm_neg, norm_mul]
    have h0 : ‖σ 0‖ ≤ 1 := by simpa using h.2.2 0 (Nat.zero_le _) 0
    have h2 : ‖lowCut A J j ξ‖ ≤ 1 := by
      unfold lowCut
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (theta_nonneg _)]
      exact theta_le_one _
    have h3 : (1 : ℝ) ≤ |ξ| / fscale A J j := by
      rw [le_div_iff₀ hL]
      have : (1 : ℝ) ≤ 2 ^ (2 * J + 1) := one_le_pow₀ (by norm_num)
      nlinarith
    calc ‖σ 0‖ * ‖lowCut A J j ξ‖ ≤ 1 * 1 := mul_le_mul h0 h2 (norm_nonneg _) zero_le_one
      _ ≤ _ := by linarith

theorem norm_iteratedDeriv_lowRem_le {Cθ : ℝ} {A : ℝ} (hA : 0 < A)
    (hCθ : ∀ (J : ℕ) (j : ℤ), ∀ i ≤ 3, ∀ ξ : ℝ,
      ‖iteratedDeriv i (lowCut A J j) ξ‖ ≤ Cθ * (fscale A J j)⁻¹ ^ i)
    {J a₀ : ℕ} (ha₀ : 3 ≤ a₀) {j : ℤ} {σ : ℝ → ℂ} (h : IsLowSymbol A J a₀ j σ) {a : ℕ} (ha : a ≤ 3)
    (ξ : ℝ) :
    ‖iteratedDeriv a (lowRem A J j σ) ξ‖ ≤ (1 + Cθ) * (fscale A J j)⁻¹ ^ a := by
  have hL := fscale_pos hA J j
  have h1 : ‖iteratedDeriv a σ ξ‖ ≤ (fscale A J j)⁻¹ ^ a := by
    have h2 : fscale A J j ^ a * ‖iteratedDeriv a σ ξ‖ ≤ 1 := h.2.2 a (le_trans ha ha₀) ξ
    rw [inv_pow]
    calc ‖iteratedDeriv a σ ξ‖ = (fscale A J j ^ a)⁻¹ * (fscale A J j ^ a * ‖iteratedDeriv a σ ξ‖) := by
          field_simp
      _ ≤ (fscale A J j ^ a)⁻¹ * 1 := by gcongr
      _ = _ := mul_one _
  have h0 : ‖σ 0‖ ≤ 1 := by simpa using h.2.2 0 (Nat.zero_le _) 0
  have hcd : ContDiffAt ℝ (a : WithTop ℕ∞) σ ξ := (h.1.of_le (by exact_mod_cast le_top)).contDiffAt
  have hcd2 : ContDiffAt ℝ (a : WithTop ℕ∞) (fun ξ => σ 0 * lowCut A J j ξ) ξ :=
    (contDiff_const.mul ((contDiff_lowCut A J j).of_le (by exact_mod_cast le_top))).contDiffAt
  have hder : iteratedDeriv a (lowRem A J j σ) ξ = iteratedDeriv a σ ξ - σ 0 * iteratedDeriv a (lowCut A J j) ξ := by
    have : lowRem A J j σ = fun ξ => σ ξ - σ 0 * lowCut A J j ξ := rfl
    rw [this, iteratedDeriv_fun_sub hcd hcd2,
      iteratedDeriv_const_mul (σ 0) ((contDiff_lowCut A J j).of_le (by exact_mod_cast le_top)).contDiffAt]
  rw [hder]
  calc ‖iteratedDeriv a σ ξ - σ 0 * iteratedDeriv a (lowCut A J j) ξ‖
      ≤ ‖iteratedDeriv a σ ξ‖ + ‖σ 0 * iteratedDeriv a (lowCut A J j) ξ‖ := norm_sub_le _ _
    _ ≤ (fscale A J j)⁻¹ ^ a + 1 * (Cθ * (fscale A J j)⁻¹ ^ a) := by
        gcongr
        · rw [norm_mul]
          exact mul_le_mul h0 (hCθ J j a ha ξ) (norm_nonneg _) zero_le_one
    _ = _ := by ring

theorem exists_lowRem_bound :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (A : ℝ), 0 < A → ∀ (J : ℕ), 1 ≤ J → ∀ (a₀ : ℕ), 3 ≤ a₀ → ∀ (j : ℤ) (σ : ℝ → ℂ),
      IsLowSymbol A J a₀ j σ → ∀ a ≤ 3, ∀ ξ : ℝ,
        |ξ| ^ a * ‖iteratedDeriv a (lowRem A J j σ) ξ‖ ≤
          (if |ξ| ≤ (2 : ℝ) ^ (2 * J + 2) * fscale A J j then K * (2 : ℝ) ^ (4 * J + 4) * (|ξ| / fscale A J j) else 0) := by
  obtain ⟨Cθ, hC0, hCθ⟩ := norm_iteratedDeriv_lowCut_le
  refine ⟨1 + Cθ, by linarith, fun A hA J hJ a₀ ha₀ j σ h a ha ξ => ?_⟩
  have hL := fscale_pos hA J j
  split_ifs with hξ
  · have hT : (1 : ℝ) ≤ 2 ^ (2 * J + 2) := one_le_pow₀ (by norm_num)
    have ht0 : 0 ≤ |ξ| / fscale A J j := by positivity
    have ht : |ξ| / fscale A J j ≤ 2 ^ (2 * J + 2) := by rw [div_le_iff₀ hL]; linarith
    have hK : 1 ≤ (1 + Cθ) * (2 : ℝ) ^ (4 * J + 4) := by
      have : (1 : ℝ) ≤ 2 ^ (4 * J + 4) := one_le_pow₀ (by norm_num)
      nlinarith
    rcases Nat.eq_zero_or_pos a with rfl | hapos
    · rw [iteratedDeriv_zero, pow_zero, one_mul]
      refine (norm_lowRem_le hA (by omega) h ξ).trans ?_
      calc |ξ| / fscale A J j = 1 * (|ξ| / fscale A J j) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hK ht0
    · have hd := norm_iteratedDeriv_lowRem_le hA (hCθ A hA) ha₀ h ha ξ
      have hta : (|ξ| / fscale A J j) ^ a ≤ (|ξ| / fscale A J j) * ((2 : ℝ) ^ (2 * J + 2)) ^ 2 := by
        have e : (|ξ| / fscale A J j) ^ a = (|ξ| / fscale A J j) * (|ξ| / fscale A J j) ^ (a - 1) := by
          rw [← pow_succ']; congr 1; omega
        rw [e]
        refine mul_le_mul_of_nonneg_left ?_ ht0
        calc (|ξ| / fscale A J j) ^ (a - 1) ≤ ((2 : ℝ) ^ (2 * J + 2)) ^ (a - 1) := pow_le_pow_left₀ ht0 ht _
          _ ≤ ((2 : ℝ) ^ (2 * J + 2)) ^ 2 := pow_le_pow_right₀ hT (by omega)
      calc |ξ| ^ a * ‖iteratedDeriv a (lowRem A J j σ) ξ‖
          ≤ |ξ| ^ a * ((1 + Cθ) * (fscale A J j)⁻¹ ^ a) := by gcongr
        _ = (1 + Cθ) * (|ξ| / fscale A J j) ^ a := by rw [div_pow, inv_pow]; ring
        _ ≤ (1 + Cθ) * ((|ξ| / fscale A J j) * ((2 : ℝ) ^ (2 * J + 2)) ^ 2) := by gcongr
        _ = (1 + Cθ) * (2 : ℝ) ^ (4 * J + 4) * (|ξ| / fscale A J j) := by
            rw [← pow_mul]; ring_nf
  · push Not at hξ
    rw [iteratedDeriv_eq_zero_of_open (U := {ξ' | (2 : ℝ) ^ (2 * J + 2) * fscale A J j < |ξ'|})
      (isOpen_lt (by fun_prop) (by fun_prop)) (fun ξ' hξ' => lowRem_eq_zero_of_far hA h hξ') a hξ]
    simp

/-- The geometric series over the scales: `∑_{j : |ξ| ≤ T₀ 2^{Jj}} |ξ| / 2^{Jj} ≤ 2 T₀`. -/
theorem sum_geom_filter_le {A : ℝ} (hA : 0 < A) {J : ℕ} (hJ : 1 ≤ J) (js : Finset ℤ) {T₀ : ℝ} (hT : 0 < T₀) (ξ : ℝ) :
    ∑ j ∈ js.filter (fun j => |ξ| ≤ T₀ * fscale A J j), |ξ| / fscale A J j ≤ 2 * T₀ := by
  set F := js.filter (fun j => |ξ| ≤ T₀ * fscale A J j) with hF
  rcases F.eq_empty_or_nonempty with h | h
  · rw [h]; simp; positivity
  · set j₁ := F.min' h with hj₁
    have hj₁F : j₁ ∈ F := F.min'_mem h
    have hξ₁ : |ξ| ≤ T₀ * fscale A J j₁ := (Finset.mem_filter.1 hj₁F).2
    set n : ℤ → ℕ := fun j => (j - j₁).toNat with hn
    have hpt : ∀ j ∈ F, |ξ| / fscale A J j ≤ T₀ * (1 / 2 : ℝ) ^ n j := by
      intro j hj
      have hjj : j₁ ≤ F.min' h := le_rfl
      have hj1 : j₁ ≤ j := F.min'_le j hj
      have hjn : j = j₁ + (n j : ℤ) := by simp only [hn]; omega
      have hfs : fscale A J j = 2 ^ (J * n j) * fscale A J j₁ := by
        conv_lhs => rw [hjn]
        exact fscale_add_nat A J j₁ (n j)
      have hL1 := fscale_pos hA J j₁
      have h2n : (2 : ℝ) ^ (n j) ≤ 2 ^ (J * n j) := pow_le_pow_right₀ (by norm_num) (by nlinarith)
      rw [hfs, div_le_iff₀ (by positivity)]
      calc |ξ| ≤ T₀ * fscale A J j₁ := hξ₁
        _ = T₀ * (1 / 2 : ℝ) ^ n j * (2 ^ (n j) * fscale A J j₁) := by
            rw [one_div, inv_pow]; field_simp
        _ ≤ T₀ * (1 / 2 : ℝ) ^ n j * (2 ^ (J * n j) * fscale A J j₁) := by gcongr
    calc ∑ j ∈ F, |ξ| / fscale A J j ≤ ∑ j ∈ F, T₀ * (1 / 2 : ℝ) ^ n j := Finset.sum_le_sum hpt
      _ = ∑ m ∈ F.image n, T₀ * (1 / 2 : ℝ) ^ m := by
          rw [Finset.sum_image]
          intro a ha b hb hab
          have h1 : j₁ ≤ a := F.min'_le a ha
          have h2 : j₁ ≤ b := F.min'_le b hb
          simp only [hn] at hab
          omega
      _ ≤ ∑ m ∈ Finset.range (F.sup n + 1), T₀ * (1 / 2 : ℝ) ^ m := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm
            obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hm
            exact Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := n) hj))
          · intro i _ _; positivity
      _ = T₀ * ∑ m ∈ Finset.range (F.sup n + 1), (1 / 2 : ℝ) ^ m := by rw [Finset.mul_sum]
      _ ≤ T₀ * 2 := by gcongr; exact sum_geometric_two_le _
      _ = 2 * T₀ := by ring

/-- **Mikhlin sums of the low-frequency remainders**: for `σ_j` low symbols and `‖c_j‖ ≤ 1`,
`∑_{j ∈ js} c_j (σ_j - σ_j(0) ϑ_j)` is a Mikhlin symbol of order `3` with a constant independent of `js`. -/
theorem exists_isMikhlin_sum_lowRem :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ), 0 < A → ∀ (J : ℕ), 1 ≤ J → ∀ (a₀ : ℕ), 3 ≤ a₀ → ∀ (js : Finset ℤ) (c : ℤ → ℂ),
      (∀ j, ‖c j‖ ≤ 1) → ∀ σ : ℤ → ℝ → ℂ, (∀ j, IsLowSymbol A J a₀ j (σ j)) →
        CZ.IsMikhlin 3 (K * 2 ^ (6 * J + 7)) (fun ξ => ∑ j ∈ js, c j * lowRem A J j (σ j) ξ) := by
  obtain ⟨K, hK1, hK⟩ := exists_lowRem_bound
  refine ⟨K, by linarith, fun A hA J hJ a₀ ha₀ js c hc σ hσ => ?_⟩
  refine isMikhlin_sum_of_bound js c hc (fun j => lowRem A J j (σ j))
    (fun j _ => contDiff_lowRem (hσ j).1) fun a ha ξ hξ => ?_
  set T₀ : ℝ := (2 : ℝ) ^ (2 * J + 2) with hT₀
  have hT0 : 0 < T₀ := by positivity
  set S := js.filter (fun j => |ξ| ≤ T₀ * fscale A J j) with hS
  have hsub : S ⊆ js := Finset.filter_subset _ _
  have hzero : ∀ j ∈ js, j ∉ S → |ξ| ^ a * ‖iteratedDeriv a (lowRem A J j (σ j)) ξ‖ = 0 := by
    intro j hj hjS
    have hnot : ¬ |ξ| ≤ T₀ * fscale A J j := fun h => hjS (Finset.mem_filter.2 ⟨hj, h⟩)
    have := hK A hA J hJ a₀ ha₀ j (σ j) (hσ j) a ha ξ
    have hnot' : ¬ |ξ| ≤ (2 : ℝ) ^ (2 * J + 2) * fscale A J j := hnot
    simp only [hnot', ↓reduceIte] at this
    exact le_antisymm this (mul_nonneg (pow_nonneg (abs_nonneg _) _) (norm_nonneg _))
  rw [← Finset.sum_subset hsub fun j hj hjS => hzero j hj hjS]
  calc ∑ j ∈ S, |ξ| ^ a * ‖iteratedDeriv a (lowRem A J j (σ j)) ξ‖
      ≤ ∑ j ∈ S, K * (2 : ℝ) ^ (4 * J + 4) * (|ξ| / fscale A J j) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have := hK A hA J hJ a₀ ha₀ j (σ j) (hσ j) a ha ξ
        have hin : |ξ| ≤ (2 : ℝ) ^ (2 * J + 2) * fscale A J j := (Finset.mem_filter.1 hj).2
        simpa only [hin, ↓reduceIte] using this
    _ = K * (2 : ℝ) ^ (4 * J + 4) * ∑ j ∈ S, |ξ| / fscale A J j := by rw [Finset.mul_sum]
    _ ≤ K * (2 : ℝ) ^ (4 * J + 4) * (2 * T₀) := by
        gcongr
        exact sum_geom_filter_le hA hJ js hT0 ξ
    _ = K * 2 ^ (6 * J + 7) := by
        rw [hT₀]
        have : (2 : ℝ) ^ (4 * J + 4) * (2 * 2 ^ (2 * J + 2)) = 2 ^ (6 * J + 7) := by
          rw [← pow_succ', ← pow_add]; congr 1; ring
        rw [mul_assoc, this]

end PrimeBHT.TimeFrequency.X2
