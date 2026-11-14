module

public import PrimeBHT.GroupDecay
public import PrimeBHT.Decomposition
public import PrimeBHT.SingleScaleL1
public import PrimeBHT.SingleScale
public import PrimeBHT.Progression

/-!
# S21: the operators of the N52 glue, `Key0Statement`, and bridges

* `uOp`, `Key0Statement χ`: restated from the transient draft `docs/audits/Key0Statement.draft.lean.txt`
  (same shape; a frozen version will replace it).
* `blk χ j F = ∑_{k ∈ F} T_k^{2^j}` as a bilinear map (from `SingleScaleL1.single`), and its bridges to
  `Decomposition.Hmod`, `Decomposition.Utail`, `Progression.opIQ` and `uOp`.
* `eLpNorm_blk_le`: the `r`-quasi-triangle inequality for `blk`; `card_le_of_mem`.
-/

@[expose] public noncomputable section

open MeasureTheory PrimeBHT.Kernel PrimeBHT.Decomposition PrimeCarleson PrimeCarleson.Proof.Paper
open scoped ENNReal

namespace PrimeBHT.FinalGlue

/-! ## The operator `uOp` and the statement `Key0Statement` (as in the transient draft) -/

/-- The unsmoothed truncated long-scale operator `U^J_{Q;τ}(f, g)(x)` (copy of the draft `uOp`). -/
def uOp (χ : ℝ → ℝ) (Q : ℕ) (τ : ℝ) (J : ℕ) (f g : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑ k ∈ Finset.Icc ⌈(Q : ℝ) ^ τ⌉₊ J,
    ∑' n : ℤ, ((PrimeBHT.Kernel.psiK χ k (n : ℝ) : ℝ) : ℂ) *
      PrimeCarleson.blockWeight (Finset.Ioc (Q / 2) Q) n * f (x - n) * g (x + n)

/-- **`p:key0`** (blueprint N26, corrected form), for a fixed `χ`: the body of the theorem `p_key0`
of the draft, instantiated at `χ`.  An anchor, NOT proved here. -/
def Key0Statement (χ : ℝ → ℝ) : Prop :=
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

/-- `blk χ j F = ∑_{k ∈ F} T_k^{Q}`, `Q = 2^j`, as a bilinear map on finitely supported sequences. -/
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

/-! ## The `r`-quasi-triangle inequality for a block, and counting -/

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

/-- `(#F)^{1/r} (C Q^β N) ≤ C Q^{c/r+β} N` for `#F ≤ Q^c`. -/
theorem card_rpow_mul_le {n : ℕ} {Q c r β C : ℝ} (hQ : 1 ≤ Q) (hr : 0 < r) (hC : 0 ≤ C)
    (hn : (n : ℝ) ≤ Q ^ c) (N : ℝ≥0∞) :
    (n : ℝ≥0∞) ^ (1 / r) * (ENNReal.ofReal (C * Q ^ β) * N) ≤
      ENNReal.ofReal (C * Q ^ (c * (1 / r) + β)) * N := by
  have hQ0 : 0 < Q := by linarith
  have h1 : ((n : ℝ) ^ (1 / r)) ≤ Q ^ (c * (1 / r)) := by
    rw [Real.rpow_mul hQ0.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg n) hn (by positivity)
  calc (n : ℝ≥0∞) ^ (1 / r) * (ENNReal.ofReal (C * Q ^ β) * N)
      = ENNReal.ofReal ((n : ℝ) ^ (1 / r) * (C * Q ^ β)) * N := by
        rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg n)
          (by positivity), ← mul_assoc,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    _ ≤ ENNReal.ofReal (C * Q ^ (c * (1 / r) + β)) * N := by
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) N
        rw [Real.rpow_add hQ0]
        calc (n : ℝ) ^ (1 / r) * (C * Q ^ β) ≤ Q ^ (c * (1 / r)) * (C * Q ^ β) := by gcongr
          _ = C * (Q ^ (c * (1 / r)) * Q ^ β) := by ring

end PrimeBHT.FinalGlue
