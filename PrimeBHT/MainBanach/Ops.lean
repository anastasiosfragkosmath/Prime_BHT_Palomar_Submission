module

public import PrimeBHT.GroupDecay
public import PrimeBHT.Decomposition
public import PrimeBHT.SingleScaleL1
public import PrimeBHT.SingleScale
public import PrimeBHT.Progression

/-!
# S24 (gate G1): operators and bridges for the case `r ≥ 1` of the main theorem

* `uOp`, `Key0Prop χ`: restated from the transient draft `docs/audits/Key0Statement.draft.lean.txt`
  (same shape as the body of its `p_key0` at a fixed `χ`; a frozen version will replace it).
  Duplicated on purpose: this file does not import `PrimeBHT.FinalGlue`.
* `blk χ j F = ∑_{k ∈ F} T_k^{2^j}` as a bilinear map on finitely supported sequences, and its bridges
  to `Decomposition.Tk`, `Hmod`, `Utail`, `Progression.opIQ`, `uOp`.
* the elementary counting and index lemmas (`card_le_of_mem`, `q_lt_eight_or`).
-/

@[expose] public noncomputable section

open MeasureTheory PrimeBHT.Kernel PrimeBHT.Decomposition PrimeCarleson PrimeCarleson.Proof.Paper
open scoped ENNReal

namespace PrimeBHT.MainBanach

/-! ## The operator `uOp` and the statement `Key0Prop` (as in the transient draft) -/

/-- The unsmoothed truncated long-scale operator `U^J_{Q;τ}(f, g)(x)` (copy of the draft `uOp`). -/
def uOp (χ : ℝ → ℝ) (Q : ℕ) (τ : ℝ) (J : ℕ) (f g : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑ k ∈ Finset.Icc ⌈(Q : ℝ) ^ τ⌉₊ J,
    ∑' n : ℤ, ((PrimeBHT.Kernel.psiK χ k (n : ℝ) : ℝ) : ℂ) *
      PrimeCarleson.blockWeight (Finset.Ioc (Q / 2) Q) n * f (x - n) * g (x + n)

/-- **`p:key0`** (blueprint N26, corrected form) for a fixed `χ`: the body of the theorem `p_key0`
of the draft `docs/audits/Key0Statement.draft.lean.txt`, instantiated at `χ`.  An anchor, NOT proved
here: every theorem using it is named `…_of_…`. -/
def Key0Prop (χ : ℝ → ℝ) : Prop :=
  PrimeBHT.Kernel.IsCutoff χ →
    ∀ τ : ℝ, 0 < τ → τ < 1 →
    ∀ η : ℝ, 0 < η →
      ∃ Q₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ Q : ℕ, (∃ j : ℕ, Q = 2 ^ j) → Q₀ ≤ Q →
        ∀ J : ℕ, ∀ f g : ℤ →₀ ℂ,
          eLpNorm (uOp χ Q τ J ⇑f ⇑g) 1 Measure.count ≤
            ENNReal.ofReal (C * (Q : ℝ) ^ (-τ / 2 + η)) *
              eLpNorm (⇑f) 2 Measure.count * eLpNorm (⇑g) 2 Measure.count

/-! ## The block operators -/

open PrimeBHT.SingleScaleL1 (single single_apply)

theorem pow_cast_two (j : ℕ) : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; rfl

theorem one_le_two_pow_real (j : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)

/-- `blk χ j F = ∑_{k ∈ F} T_k^Q`, `Q = 2^j`, as a bilinear map on finitely supported sequences. -/
def blk (χ : ℝ → ℝ) (j : ℕ) (F : Finset ℕ) :
    (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ) :=
  ∑ k ∈ F, single χ (2 ^ j) k

theorem blk_apply {χ : ℝ → ℝ} (hχ : IsCutoff χ) (j : ℕ) (F : Finset ℕ) (f g : ℤ →₀ ℂ) (x : ℤ) :
    blk χ j F f g x = ∑ k ∈ F, Tk χ j k ⇑f ⇑g x := by
  simp only [blk, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [single_apply hχ]
  rfl

theorem blk_coe (χ : ℝ → ℝ) (j : ℕ) (F : Finset ℕ) (f g : ℤ →₀ ℂ) :
    blk χ j F f g = ∑ k ∈ F, single χ (2 ^ j) k f g := by
  funext x
  simp only [blk, LinearMap.sum_apply, Finset.sum_apply]

theorem Utail_eq_blk {χ : ℝ → ℝ} (hχ : IsCutoff χ) (τ : ℝ) (J j : ℕ) (f g : ℤ →₀ ℂ) :
    Utail χ τ J j ⇑f ⇑g = blk χ j (Finset.Icc ⌈((2 : ℝ) ^ j) ^ τ⌉₊ J) f g := by
  funext x
  rw [blk_apply hχ]
  rfl

theorem Hmod_eq_blk {χ : ℝ → ℝ} (hχ : IsCutoff χ) (τ : ℝ) (J j : ℕ) (f g : ℤ →₀ ℂ) :
    Hmod χ τ J j ⇑f ⇑g =
      blk χ j ((Finset.Icc (bQ ((2 : ℝ) ^ j)) J).filter
        (fun k : ℕ => (k : ℝ) < ((2 : ℝ) ^ j) ^ τ)) f g := by
  funext x
  rw [blk_apply hχ]
  rfl

theorem Utail_eq_uOp (χ : ℝ → ℝ) (τ : ℝ) (J j : ℕ) (f g : ℤ → ℂ) :
    Utail χ τ J j f g = uOp χ (2 ^ j) τ J f g := by
  funext x
  simp only [Utail, Tk, uOp, wQ, Nat.cast_pow, Nat.cast_ofNat]

theorem blk_Icc_eq_uOp {χ : ℝ → ℝ} (hχ : IsCutoff χ) (τ : ℝ) (J j : ℕ) (f g : ℤ →₀ ℂ) :
    blk χ j (Finset.Icc ⌈((2 : ℝ) ^ j) ^ τ⌉₊ J) f g = uOp χ (2 ^ j) τ J ⇑f ⇑g := by
  rw [← Utail_eq_blk hχ, Utail_eq_uOp]

theorem finite_support_coe (f : ℤ →₀ ℂ) : (Function.support ⇑f).Finite :=
  f.support.finite_toSet.subset fun x hx => by simpa using hx

/-- The block over `[a, b]` is the progression operator `T_I^Q` of `e:progression`. -/
theorem blk_Icc_eq_opIQ {χ : ℝ → ℝ} (hχ : IsCutoff χ) (j a b : ℕ) (f g : ℤ →₀ ℂ) :
    blk χ j (Finset.Icc a b) f g = PrimeBHT.Progression.opIQ χ a b (2 ^ j) ⇑f ⇑g := by
  funext x
  rw [blk_apply hχ]
  unfold PrimeBHT.Progression.opIQ PrimeBHT.Kernel.bilin Tk
  have hs : ∀ k ∈ Finset.Icc a b, Summable (fun n : ℤ =>
      (psiK χ k n : ℂ) * wQ (2 ^ j) n * f (x - n) * g (x + n)) :=
    fun k _ => summable_summand (finite_support_coe f) (fun n => (psiK χ k n : ℂ) * wQ (2 ^ j) n) g x
  rw [← Summable.tsum_finsetSum hs]
  refine tsum_congr fun n => ?_
  simp only [kernelI, Complex.ofReal_sum, Finset.sum_mul]

/-! ## The triangle inequality for a block and counting -/

theorem eLpNorm_blk_le (χ : ℝ → ℝ) (j : ℕ) (F : Finset ℕ) (f g : ℤ →₀ ℂ) {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) {B : ℝ≥0∞}
    (h : ∀ k ∈ F, eLpNorm (single χ (2 ^ j) k f g) (ENNReal.ofReal r) Measure.count ≤ B) :
    eLpNorm (blk χ j F f g) (ENNReal.ofReal r) Measure.count ≤ (F.card : ℝ≥0∞) ^ (1 / r) * B := by
  rw [blk_coe]
  exact PrimeBHT.GroupDecay.eLpNorm_sum_le_card_mul F (fun k => single χ (2 ^ j) k f g) hr hr1 h

/-- A finite set of positive integers all `< x` has at most `x` elements. -/
theorem card_le_of_mem {F : Finset ℕ} {x : ℝ} (hx : 0 < x)
    (hF : ∀ k ∈ F, 1 ≤ k ∧ (k : ℝ) < x) : (F.card : ℝ) ≤ x := by
  have h1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.2 hx
  have hsub : F ⊆ Finset.Icc 1 (⌈x⌉₊ - 1) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := hF k hk
    have : k < ⌈x⌉₊ := Nat.lt_ceil.2 hk2
    rw [Finset.mem_Icc]
    omega
  have hc : F.card ≤ ⌈x⌉₊ - 1 := by
    have := Finset.card_le_card hsub
    simpa using this
  have h2 : ((⌈x⌉₊ - 1 : ℕ) : ℝ) + 1 = (⌈x⌉₊ : ℝ) := by
    have : ⌈x⌉₊ - 1 + 1 = ⌈x⌉₊ := Nat.sub_add_cancel h1
    exact_mod_cast this
  have h3 := Nat.ceil_lt_add_one hx.le
  have h4 : (F.card : ℝ) ≤ ((⌈x⌉₊ - 1 : ℕ) : ℝ) := by exact_mod_cast hc
  linarith

/-- For `Q = 2^j` and `k ≥ b_Q`: `Q < 8` or `Q^{20} ≤ 2^k` (blueprint N00 item 4). -/
theorem q_lt_eight_or {j k : ℕ} (hk : bQ ((2 : ℝ) ^ j) ≤ k) :
    2 ^ j < 8 ∨ ((2 ^ j : ℕ) : ℝ) ^ 20 ≤ 2 ^ k := by
  by_cases h8 : 2 ^ j < 8
  · exact Or.inl h8
  right
  have hj3 : 3 ≤ j := by
    by_contra hj
    have h2 : j ≤ 2 := by omega
    have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
    omega
  have hk1 : 1 ≤ k := (one_le_bQ_two_pow j).trans hk
  have hM := (two_pow_le_Mk_iff hk1).2 hk
  rw [le_Mk_iff (one_le_two_pow_real j), Real.log_pow] at hM
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hjR : (3 : ℝ) ≤ j := by exact_mod_cast hj3
  have ha2 : 2 ≤ (j : ℝ) * Real.log 2 := by
    have := mul_le_mul_of_nonneg_right hjR hl2.le
    linarith
  have hform : ((j : ℝ) * Real.log 2) ^ 10 / Real.log 2 = j * ((j : ℝ) * Real.log 2) ^ 9 := by
    field_simp
  rw [hform] at hM
  have h9 : (20 : ℝ) ≤ ((j : ℝ) * Real.log 2) ^ 9 :=
    calc (20 : ℝ) ≤ 2 ^ 9 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) ha2 9
  have h20 : (20 : ℝ) * j ≤ k := by
    have := mul_le_mul_of_nonneg_left h9 (by positivity : (0 : ℝ) ≤ j)
    linarith
  have h20' : 20 * j ≤ k := by exact_mod_cast h20
  rw [pow_cast_two, ← pow_mul]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

end PrimeBHT.MainBanach

end
