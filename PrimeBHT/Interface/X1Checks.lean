module

public import PrimeBHT.Frozen.IsCutoff
public import PrimeBHT.Frozen.BhtTrunc
public import PrimeBHT.Kernel

/-!
# Sanity checks for the frozen X1 statement (`PrimeBHT.Statements.bhtTrunc`, `x1_bht_smooth`)

Migrated from section 3 of the pre-freeze candidate draft `drafts/X1Statement.lean.txt`, over the
FROZEN definitions `PrimeBHT.Statements.bhtTrunc` and `PrimeBHT.Statements.IsCutoff` (ruling R11).
Everything here is fully proved. It does NOT mention the frozen theorem `x1_bht_smooth`
(quarantine of the `DRAFT_SORRY` anchor); the statement-level interface lives in
`PrimeBHT/Interface/X1Statement.lean`.

Contents:
* (i) the hypotheses are jointly satisfiable (non-vacuity);
* (ii) the `ℓ^s` quasi-norms (`eLpNorm` for counting measure), also for `s < 1`;
* (iii) the sum over `m` is a genuine finite sum, and the left side is finite;
* (iv) the guard `m ≠ 0` introduces no junk value;
* (v) the strict inequality `L₁ < L₂`, and the edge cases;
* (vi) a concrete evaluation, so the conclusion is not trivially satisfied by `C = 0`;
* (vii) the carrier `Function.support f` finite versus `ℤ →₀ ℂ`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal
open PrimeBHT.Statements (bhtTrunc IsCutoff)

set_option autoImplicit false

namespace PrimeBHT.Interface.X1

/-! ### The two cutoff notions -/

/-- The frozen cutoff predicate gives the project's `Kernel.IsCutoff` structure (whose API the
proofs below use). -/
theorem toKernel {χ : ℝ → ℝ} (h : IsCutoff χ) : PrimeBHT.Kernel.IsCutoff χ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- The project's `Kernel.IsCutoff` structure gives the frozen cutoff predicate. -/
theorem ofKernel {χ : ℝ → ℝ} (h : PrimeBHT.Kernel.IsCutoff χ) : IsCutoff χ :=
  ⟨h.contDiff, h.even, h.tsupport_subset, h.eq_one⟩

/-! ### (i) The hypotheses are satisfiable -/

/-- The frozen `IsCutoff` is inhabited (`PrimeBHT.Kernel.exists_isCutoff`, from Mathlib's
`ContDiffBump`). -/
theorem exists_isCutoff : ∃ χ : ℝ → ℝ, IsCutoff χ := by
  obtain ⟨χ, hχ⟩ := PrimeBHT.Kernel.exists_isCutoff
  exact ⟨χ, ofKernel hχ⟩

/-- `0 < r` is automatic from `1 < p`, `1 < q`, `1 / r = 1 / p + 1 / q`. -/
theorem r_pos_of_hyps {p q r : ℝ} (hp : 1 < p) (hq : 1 < q) (h : 1 / r = 1 / p + 1 / q) :
    0 < r := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have : 0 < 1 / r := by rw [h]; positivity
  exact one_div_pos.1 this

/-- Under the other hypotheses, `2/3 < r` is the same as `1/r < 3/2` (the paper's form of the open
BHT range, L261-264: `1/p + 1/q = 1/r < 3/2`). -/
theorem two_thirds_lt_iff {p q r : ℝ} (hp : 1 < p) (hq : 1 < q) (h : 1 / r = 1 / p + 1 / q) :
    2 / 3 < r ↔ 1 / r < 3 / 2 := by
  have hr := r_pos_of_hyps hp hq h
  rw [one_div_lt hr (by norm_num : (0 : ℝ) < 3 / 2)]
  norm_num

/-- ... in the Banach range: `(p, q, r) = (2, 2, 1)`. -/
example : (1 : ℝ) < 2 ∧ (1 : ℝ) < 2 ∧ 1 / (1 : ℝ) = 1 / 2 + 1 / 2 ∧ (2 : ℝ) / 3 < 1 := by
  norm_num

/-- ... in the quasi-Banach range, diagonal: `(7/4, 7/4, 7/8)`. -/
example : (1 : ℝ) < 7 / 4 ∧ (1 : ℝ) < 7 / 4 ∧ 1 / (7 / 8 : ℝ) = 1 / (7 / 4) + 1 / (7 / 4) ∧
    (2 : ℝ) / 3 < 7 / 8 := by norm_num

/-- ... in the quasi-Banach range, off the diagonal: `(3/2, 5/4, 15/22)` (`r ≈ 0.682`). -/
example : (1 : ℝ) < 3 / 2 ∧ (1 : ℝ) < 5 / 4 ∧ 1 / (15 / 22 : ℝ) = 1 / (3 / 2) + 1 / (5 / 4) ∧
    (2 : ℝ) / 3 < 15 / 22 := by norm_num

/-- ... with `r` just above `2/3`: `(401/300, 401/300, 401/600)` (`r ≈ 0.66833`). -/
example : (1 : ℝ) < 401 / 300 ∧ (1 : ℝ) < 401 / 300 ∧
    1 / (401 / 600 : ℝ) = 1 / (401 / 300) + 1 / (401 / 300) ∧ (2 : ℝ) / 3 < 401 / 600 := by
  norm_num

/-- The endpoint `(4/3, 4/3, 2/3)` satisfies `1 < p, q` and `1/r = 1/p + 1/q` but is excluded by
`2/3 < r` (it is Lacey's counterexample point: `r > 2/3` is necessary). -/
example : (1 : ℝ) < 4 / 3 ∧ 1 / (2 / 3 : ℝ) = 1 / (4 / 3) + 1 / (4 / 3) ∧
    ¬ ((2 : ℝ) / 3 < 2 / 3) := by norm_num

/-- All the hypotheses of `x1_bht_smooth` are jointly satisfiable (some cutoff, `(7/4, 7/4, 7/8)`). -/
theorem hypotheses_satisfiable : ∃ χ : ℝ → ℝ, IsCutoff χ ∧ ∃ p q r : ℝ, 1 < p ∧ 1 < q ∧
    1 / r = 1 / p + 1 / q ∧ 2 / 3 < r := by
  obtain ⟨χ, hχ⟩ := exists_isCutoff
  exact ⟨χ, hχ, 7 / 4, 7 / 4, 7 / 8, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ### (ii) The norms are the `ℓ^s` (quasi-)norms, also for `s < 1` -/

/-- `‖F‖_{ℓ^s} = (∑ₓ |F x|^s)^{1/s}` for every `s > 0`, in particular `s < 1`. -/
theorem eLpNorm_count_eq (F : ℤ → ℂ) {s : ℝ} (hs : 0 < s) :
    eLpNorm F (ENNReal.ofReal s) Measure.count = (∑' x, ‖F x‖ₑ ^ s) ^ (1 / s) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hs) ENNReal.ofReal_ne_top
    (measurable_of_countable F).aestronglyMeasurable, lintegral_count,
    ENNReal.toReal_ofReal hs.le]

/-- A function `ℤ → ℂ` with nonzero value has nonzero `ℓ^s` quasi-norm (`s > 0`). -/
theorem eLpNorm_count_ne_zero (F : ℤ → ℂ) {s : ℝ} (hs : 0 < s) {x : ℤ} (hx : F x ≠ 0) :
    eLpNorm F (ENNReal.ofReal s) Measure.count ≠ 0 := by
  rw [eLpNorm_count_eq F hs]
  intro h
  rcases ENNReal.rpow_eq_zero_iff.1 h with ⟨h0, -⟩ | ⟨-, h⟩
  · have := ENNReal.tsum_eq_zero.1 h0 x
    rcases ENNReal.rpow_eq_zero_iff.1 this with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact hx (by simpa using h1)
    · linarith
  · have : (0 : ℝ) < 1 / s := by positivity
    linarith

/-- A function `ℤ → ℂ` with finite support has finite `ℓ^p` norm, `0 < p < ∞`. -/
theorem eLpNorm_count_lt_top_of_finite_support {F : ℤ → ℂ} (hF : (Function.support F).Finite)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) : eLpNorm F p Measure.count < ∞ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (measurable_of_countable F).aestronglyMeasurable,
    lintegral_count]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
  have hpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [tsum_eq_sum (s := hF.toFinset)]
  · refine (ENNReal.sum_lt_top.2 fun x _ => ?_).ne
    exact ENNReal.rpow_lt_top_of_nonneg hpos.le enorm_lt_top.ne
  · intro x hx
    rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hx
    simp [hx, hpos]

/-! ### (iii) The sum over `m` is a genuine finite sum; the left side is finite -/

/-- The `m`-th term of the series defining `bhtTrunc χ L₁ L₂ f g x`. -/
def bhtTruncTerm (χ : ℝ → ℝ) (L₁ L₂ : ℝ) (f g : ℤ → ℂ) (x m : ℤ) : ℂ :=
  (if m = 0 then 0 else (((χ (m / L₂) - χ (m / L₁)) / m : ℝ) : ℂ)) * f (x - m) * g (x + m)

theorem bhtTrunc_eq_tsum_term (χ : ℝ → ℝ) (L₁ L₂ : ℝ) (f g : ℤ → ℂ) (x : ℤ) :
    bhtTrunc χ L₁ L₂ f g x = ∑' m : ℤ, bhtTruncTerm χ L₁ L₂ f g x m := rfl

/-- The term vanishes outside the finite set `{x - a : a ∈ f.support}`. -/
theorem bhtTruncTerm_eq_zero (χ : ℝ → ℝ) (L₁ L₂ : ℝ) {f : ℤ → ℂ} (hf : (Function.support f).Finite)
    (g : ℤ → ℂ) (x : ℤ) {m : ℤ} (hm : m ∉ hf.toFinset.image (fun a : ℤ => x - a)) :
    bhtTruncTerm χ L₁ L₂ f g x m = 0 := by
  have h : f (x - m) = 0 := by
    by_contra h
    exact hm (Finset.mem_image.2 ⟨x - m, (Set.Finite.mem_toFinset hf).2 h, by ring⟩)
  simp [bhtTruncTerm, h]

/-- `bhtTrunc χ L₁ L₂ f g x` is literally a `Finset.sum` over the finite set `x - f.support`. -/
theorem bhtTrunc_eq_sum (χ : ℝ → ℝ) (L₁ L₂ : ℝ) {f : ℤ → ℂ} (hf : (Function.support f).Finite)
    (g : ℤ → ℂ) (x : ℤ) :
    bhtTrunc χ L₁ L₂ f g x =
      ∑ m ∈ hf.toFinset.image (fun a : ℤ => x - a), bhtTruncTerm χ L₁ L₂ f g x m :=
  tsum_eq_sum fun _ hm => bhtTruncTerm_eq_zero χ L₁ L₂ hf g x hm

/-- The series is summable, so `bhtTrunc χ L₁ L₂ f g x` is its true sum (not the junk value `0`). -/
theorem bhtTrunc_hasSum (χ : ℝ → ℝ) (L₁ L₂ : ℝ) {f : ℤ → ℂ} (hf : (Function.support f).Finite)
    (g : ℤ → ℂ) (x : ℤ) :
    HasSum (fun m : ℤ => bhtTruncTerm χ L₁ L₂ f g x m) (bhtTrunc χ L₁ L₂ f g x) := by
  rw [bhtTrunc_eq_sum χ L₁ L₂ hf]
  exact hasSum_sum_of_ne_finset_zero fun _ hm => bhtTruncTerm_eq_zero χ L₁ L₂ hf g x hm

/-- For a cutoff, the kernel vanishes for `|m| ≥ L₂` (`0 < L₁ < L₂`): the sum over `m` is a finite
sum over `|m| < L₂` for ARBITRARY `f, g` (so `bhtTrunc` is well defined on all of `ℤ → ℂ`). -/
theorem bhtTruncTerm_eq_zero_of_cutoff {χ : ℝ → ℝ} (hχ : IsCutoff χ) {L₁ L₂ : ℝ} (hL₁ : 0 < L₁)
    (hL : L₁ < L₂) (f g : ℤ → ℂ) (x : ℤ) {m : ℤ} (hm : L₂ ≤ |(m : ℝ)|) :
    bhtTruncTerm χ L₁ L₂ f g x m = 0 := by
  have hL₂ : 0 < L₂ := hL₁.trans hL
  have h2 : χ ((m : ℝ) / L₂) = 0 := by
    apply (toKernel hχ).eq_zero_of_one_le_abs
    rw [abs_div, abs_of_pos hL₂, le_div_iff₀ hL₂]; linarith
  have h1 : χ ((m : ℝ) / L₁) = 0 := by
    apply (toKernel hχ).eq_zero_of_one_le_abs
    rw [abs_div, abs_of_pos hL₁, le_div_iff₀ hL₁]; linarith
  simp [bhtTruncTerm, h1, h2]

/-- For finitely supported `f, g`, `bhtTrunc f g` is supported on a finite set (`2x ∈ supp f +
supp g`), whatever `χ, L₁, L₂` are. -/
theorem bhtTrunc_support_finite (χ : ℝ → ℝ) (L₁ L₂ : ℝ) {f g : ℤ → ℂ}
    (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) :
    (Function.support (bhtTrunc χ L₁ L₂ f g)).Finite := by
  classical
  refine ((hf.toFinset ×ˢ hg.toFinset).image
    (fun p : ℤ × ℤ => (p.1 + p.2) / 2)).finite_toSet.subset ?_
  intro x hx
  rw [Function.mem_support] at hx
  have : ∃ m : ℤ, bhtTruncTerm χ L₁ L₂ f g x m ≠ 0 := by
    by_contra h
    have h' : ∀ m : ℤ, bhtTruncTerm χ L₁ L₂ f g x m = 0 := fun m =>
      by_contra fun hm => h ⟨m, hm⟩
    exact hx (by rw [bhtTrunc_eq_tsum_term, tsum_congr h', tsum_zero])
  obtain ⟨m, hm⟩ := this
  have hfm : f (x - m) ≠ 0 := fun h => hm (by simp [bhtTruncTerm, h])
  have hgm : g (x + m) ≠ 0 := fun h => hm (by simp [bhtTruncTerm, h])
  rw [Finset.mem_coe, Finset.mem_image]
  refine ⟨(x - m, x + m), Finset.mem_product.2 ⟨(Set.Finite.mem_toFinset hf).2 hfm,
    (Set.Finite.mem_toFinset hg).2 hgm⟩, ?_⟩
  show (x - m + (x + m)) / 2 = x
  omega

/-- The left side of `x1_bht_smooth` is finite for finitely supported inputs (`r > 0`). -/
theorem eLpNorm_bhtTrunc_lt_top (χ : ℝ → ℝ) (L₁ L₂ : ℝ) {f g : ℤ → ℂ}
    (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) {r : ℝ} (hr : 0 < r) :
    eLpNorm (bhtTrunc χ L₁ L₂ f g) (ENNReal.ofReal r) Measure.count < ∞ :=
  eLpNorm_count_lt_top_of_finite_support (bhtTrunc_support_finite χ L₁ L₂ hf hg)
    (ENNReal.ofReal_pos.2 hr).ne' ENNReal.ofReal_ne_top

/-- The right side of `x1_bht_smooth` is finite for finitely supported inputs: so the bound is a
genuine finite inequality, not satisfied through `⊤`. -/
theorem rhs_x1_lt_top (C : ℝ) {f g : ℤ → ℂ} (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) Measure.count *
      eLpNorm g (ENNReal.ofReal q) Measure.count < ∞ :=
  ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (eLpNorm_count_lt_top_of_finite_support hf (ENNReal.ofReal_pos.2 hp).ne' ENNReal.ofReal_ne_top))
    (eLpNorm_count_lt_top_of_finite_support hg (ENNReal.ofReal_pos.2 hq).ne' ENNReal.ofReal_ne_top)

/-! ### (iv) The guard `m ≠ 0`: no `1/0` junk -/

/-- Dropping the guard changes nothing (Lean's `a / 0 = 0`), so the explicit guard is a faithful
encoding of `m ≠ 0` and not a source of a different value. -/
theorem bhtTrunc_eq_unguarded (χ : ℝ → ℝ) (L₁ L₂ : ℝ) (f g : ℤ → ℂ) (x : ℤ) :
    bhtTrunc χ L₁ L₂ f g x =
      ∑' m : ℤ, (((χ (m / L₂) - χ (m / L₁)) / m : ℝ) : ℂ) * f (x - m) * g (x + m) := by
  unfold bhtTrunc
  refine tsum_congr fun m => ?_
  by_cases hm : m = 0
  · subst hm; simp
  · simp [hm]

/-- The same operator with the guard around the whole term (the form of `primeBHT` in T0). -/
theorem bhtTrunc_eq_guard_outside (χ : ℝ → ℝ) (L₁ L₂ : ℝ) (f g : ℤ → ℂ) (x : ℤ) :
    bhtTrunc χ L₁ L₂ f g x =
      ∑' m : ℤ, if m = 0 then 0 else
        (((χ (m / L₂) - χ (m / L₁)) / m : ℝ) : ℂ) * f (x - m) * g (x + m) := by
  unfold bhtTrunc
  refine tsum_congr fun m => ?_
  by_cases hm : m = 0
  · subst hm; simp
  · simp [hm]

/-- For a cutoff the numerator `χ(m/L₂) - χ(m/L₁)` of the kernel is already `0` at `m = 0`
(`χ(0) = 1`): the `0/0` is not a genuine singularity, and the guard value `0` is the right one. -/
theorem numerator_zero_at_zero {χ : ℝ → ℝ} (hχ : IsCutoff χ) (L₁ L₂ : ℝ) :
    χ (((0 : ℤ) : ℝ) / L₂) - χ (((0 : ℤ) : ℝ) / L₁) = 0 := by
  have h0 : χ 0 = 1 := (toKernel hχ).eq_one 0 ⟨by norm_num, by norm_num⟩
  simp [h0]

/-! ### (v) The strict inequality `L₁ < L₂`, and the unused edge cases are covered -/

/-- `L₁ = L₂` gives the zero operator. -/
theorem bhtTrunc_self (χ : ℝ → ℝ) (L : ℝ) (f g : ℤ → ℂ) (x : ℤ) : bhtTrunc χ L L f g x = 0 := by
  simp [bhtTrunc]

/-- Swapping the radii changes the sign: so the statement for `L₁ < L₂` is equivalent to the one
for all `L₁, L₂ > 0` (the ordering is cosmetic). -/
theorem bhtTrunc_swap (χ : ℝ → ℝ) (L₁ L₂ : ℝ) (f g : ℤ → ℂ) (x : ℤ) :
    bhtTrunc χ L₂ L₁ f g x = -bhtTrunc χ L₁ L₂ f g x := by
  unfold bhtTrunc
  rw [← tsum_neg]
  refine tsum_congr fun m => ?_
  by_cases hm : m = 0
  · simp [hm]
  · have : ((χ ((m : ℝ) / L₁) - χ ((m : ℝ) / L₂)) / m : ℝ) =
        -((χ ((m : ℝ) / L₂) - χ ((m : ℝ) / L₁)) / m) := by ring
    simp only [hm, ↓reduceIte, this, Complex.ofReal_neg]
    ring

/-- For a cutoff and `m ≠ 0`, `χ(m/L) = 0` as soon as `0 < L ≤ 1`. -/
theorem chi_div_eq_zero_of_le_one {χ : ℝ → ℝ} (hχ : IsCutoff χ) {L : ℝ} (hL : 0 < L)
    (hL1 : L ≤ 1) {m : ℤ} (hm : m ≠ 0) : χ ((m : ℝ) / L) = 0 := by
  have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
    exact_mod_cast this
  apply (toKernel hχ).eq_zero_of_one_le_abs
  rw [abs_div, abs_of_pos hL, le_div_iff₀ hL]; linarith

/-- For a cutoff the operator does not depend on the inner radius `L₁ ∈ (0, 1]`: the excluded
case `L₁ = 0` (intended meaning: the kernel `χ(m/L₂)/m`; in Lean `m / 0 = 0` would instead give
`χ(0) = 1`, a different kernel, which is why `0 < L₁` is essential) is the case `L₁ = 1`, covered. -/
theorem bhtTrunc_eq_of_le_one {χ : ℝ → ℝ} (hχ : IsCutoff χ) {L₁ L₁' : ℝ} (L₂ : ℝ) (h1 : 0 < L₁)
    (h1' : L₁ ≤ 1) (h2 : 0 < L₁') (h2' : L₁' ≤ 1) (f g : ℤ → ℂ) (x : ℤ) :
    bhtTrunc χ L₁ L₂ f g x = bhtTrunc χ L₁' L₂ f g x := by
  unfold bhtTrunc
  refine tsum_congr fun m => ?_
  by_cases hm : m = 0
  · simp [hm]
  · simp only [hm, ↓reduceIte, chi_div_eq_zero_of_le_one hχ h1 h1' hm,
      chi_div_eq_zero_of_le_one hχ h2 h2' hm]

/-! ### (vi) A concrete evaluation, and the operator is not identically zero -/

/-- Closed form of `bhtTrunc` on two point masses: the unique candidate `m = x - a` must satisfy
`m ≠ 0` and `x + m = b`; then the value is `K(m) c d` with `K(m) = (χ(m/L₂) - χ(m/L₁))/m`. -/
theorem bhtTrunc_single_single (χ : ℝ → ℝ) (L₁ L₂ : ℝ) (a b : ℤ) (c d : ℂ) (x : ℤ) :
    bhtTrunc χ L₁ L₂ (⇑(Finsupp.single a c)) (⇑(Finsupp.single b d)) x =
      if x - a ≠ 0 ∧ b = x + (x - a) then
        (((χ (((x - a : ℤ) : ℝ) / L₂) - χ (((x - a : ℤ) : ℝ) / L₁)) / ((x - a : ℤ) : ℝ) : ℝ) : ℂ) *
          c * d
      else 0 := by
  unfold bhtTrunc
  rw [tsum_eq_single (x - a)]
  · by_cases h : x - a ≠ 0 ∧ b = x + (x - a)
    · obtain ⟨h0, hb⟩ := h
      simp [h0, hb]
    · by_cases h0 : x - a = 0
      · simp [h0]
      · have hb : b ≠ x + (x - a) := fun hb => h ⟨h0, hb⟩
        simp [h0, hb]
  · intro n hn
    have : x - n ≠ a := fun h => hn (by omega)
    simp [Finsupp.single_apply, this]

/-- A concrete instance: for EVERY cutoff `χ`, `f = δ₀`, `g = δ₈`, `x = 4`, radii `L₁ = 4 < L₂ = 16`
(`m = 4`, `χ(4/16) = χ(1/4) = 1`, `χ(4/4) = χ(1) = 0`): the value is `1/4`. -/
theorem bhtTrunc_delta_zero_eight_four {χ : ℝ → ℝ} (hχ : IsCutoff χ) :
    bhtTrunc χ 4 16 (⇑(Finsupp.single (0 : ℤ) (1 : ℂ))) (⇑(Finsupp.single (8 : ℤ) (1 : ℂ))) 4 =
      1 / 4 := by
  rw [bhtTrunc_single_single]
  split_ifs with hc
  swap
  · exact absurd (by norm_num) hc
  have h1 : χ ((((4 : ℤ) - 0 : ℤ) : ℝ) / 16) = 1 :=
    (toKernel hχ).eq_one_of_abs_le (by norm_num [abs_of_pos])
  have h2 : χ ((((4 : ℤ) - 0 : ℤ) : ℝ) / 4) = 0 :=
    (toKernel hχ).eq_zero_of_one_le_abs (by norm_num [abs_of_pos])
  rw [h1, h2]
  norm_num

/-- ... at `x = 3` no `m` contributes: `0`. -/
theorem bhtTrunc_delta_zero_eight_three (χ : ℝ → ℝ) :
    bhtTrunc χ 4 16 (⇑(Finsupp.single (0 : ℤ) (1 : ℂ))) (⇑(Finsupp.single (8 : ℤ) (1 : ℂ))) 3 =
      0 := by
  rw [bhtTrunc_single_single]
  split_ifs with hc
  · exact absurd hc (by norm_num)
  · rfl

/-- ... and with the roles of `f, g` exchanged the sign flips (`m = -4`):
`bhtTrunc (δ₈, δ₀) 4 = -1/4`. -/
theorem bhtTrunc_delta_eight_zero_four {χ : ℝ → ℝ} (hχ : IsCutoff χ) :
    bhtTrunc χ 4 16 (⇑(Finsupp.single (8 : ℤ) (1 : ℂ))) (⇑(Finsupp.single (0 : ℤ) (1 : ℂ))) 4 =
      -(1 / 4) := by
  rw [bhtTrunc_single_single]
  split_ifs with hc
  swap
  · exact absurd (by norm_num) hc
  have h1 : χ ((((4 : ℤ) - 8 : ℤ) : ℝ) / 16) = 1 :=
    (toKernel hχ).eq_one_of_abs_le (by norm_num [abs_of_neg])
  have h2 : χ ((((4 : ℤ) - 8 : ℤ) : ℝ) / 4) = 0 :=
    (toKernel hχ).eq_zero_of_one_le_abs (by norm_num [abs_of_neg])
  rw [h1, h2]
  norm_num

/-- The conclusion of `x1_bht_smooth` is not trivial: the left side at `f = δ₀, g = δ₈`, radii
`(4, 16)` is nonzero for every `r > 0`, so `C = 0` is impossible. -/
theorem eLpNorm_bhtTrunc_delta_ne_zero {χ : ℝ → ℝ} (hχ : IsCutoff χ) {r : ℝ} (hr : 0 < r) :
    eLpNorm (bhtTrunc χ 4 16 (⇑(Finsupp.single (0 : ℤ) (1 : ℂ)))
      (⇑(Finsupp.single (8 : ℤ) (1 : ℂ)))) (ENNReal.ofReal r) Measure.count ≠ 0 := by
  refine eLpNorm_count_ne_zero _ hr (x := 4) ?_
  rw [bhtTrunc_delta_zero_eight_four hχ]
  norm_num

/-! ### (vii) The carrier: `Function.support` finite versus `ℤ →₀ ℂ` -/

/-- The finitely-supported-function carrier of `x1_bht_smooth` (as in `BilinBound` and in every
N24 consumer) is equivalent to the `ℤ →₀ ℂ` carrier used in `t_maintheorem` (T0): the choice is
cosmetic. This is the shape of the frozen statement's `∃ C` part (no `0 ≤ C` conjunct). -/
theorem x1_finsupp_iff (χ : ℝ → ℝ) (p q r : ℝ) :
    (∃ C : ℝ, ∀ L₁ L₂ : ℝ, 0 < L₁ → L₁ < L₂ →
        ∀ f g : ℤ → ℂ, (Function.support f).Finite → (Function.support g).Finite →
          eLpNorm (bhtTrunc χ L₁ L₂ f g) (ENNReal.ofReal r) Measure.count ≤
            ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) Measure.count *
              eLpNorm g (ENNReal.ofReal q) Measure.count) ↔
    (∃ C : ℝ, ∀ L₁ L₂ : ℝ, 0 < L₁ → L₁ < L₂ → ∀ f g : ℤ →₀ ℂ,
          eLpNorm (bhtTrunc χ L₁ L₂ ⇑f ⇑g) (ENNReal.ofReal r) Measure.count ≤
            ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count *
              eLpNorm (⇑g) (ENNReal.ofReal q) Measure.count) := by
  have hfin : ∀ f : ℤ →₀ ℂ, (Function.support ⇑f).Finite := fun f =>
    f.support.finite_toSet.subset fun x hx => by simpa using hx
  constructor
  · rintro ⟨C, h⟩
    exact ⟨C, fun L₁ L₂ h1 h2 f g => h L₁ L₂ h1 h2 f g (hfin f) (hfin g)⟩
  · rintro ⟨C, h⟩
    refine ⟨C, fun L₁ L₂ h1 h2 f g hf hg => ?_⟩
    exact h L₁ L₂ h1 h2 (Finsupp.ofSupportFinite f hf) (Finsupp.ofSupportFinite g hg)

/-- The same carrier equivalence with the conjunct `0 ≤ C` (the form of the pre-freeze draft and of
`t_maintheorem`). -/
theorem x1_finsupp_iff_nonneg (χ : ℝ → ℝ) (p q r : ℝ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ L₁ L₂ : ℝ, 0 < L₁ → L₁ < L₂ →
        ∀ f g : ℤ → ℂ, (Function.support f).Finite → (Function.support g).Finite →
          eLpNorm (bhtTrunc χ L₁ L₂ f g) (ENNReal.ofReal r) Measure.count ≤
            ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) Measure.count *
              eLpNorm g (ENNReal.ofReal q) Measure.count) ↔
    (∃ C : ℝ, 0 ≤ C ∧ ∀ L₁ L₂ : ℝ, 0 < L₁ → L₁ < L₂ → ∀ f g : ℤ →₀ ℂ,
          eLpNorm (bhtTrunc χ L₁ L₂ ⇑f ⇑g) (ENNReal.ofReal r) Measure.count ≤
            ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) Measure.count *
              eLpNorm (⇑g) (ENNReal.ofReal q) Measure.count) := by
  have hfin : ∀ f : ℤ →₀ ℂ, (Function.support ⇑f).Finite := fun f =>
    f.support.finite_toSet.subset fun x hx => by simpa using hx
  constructor
  · rintro ⟨C, hC, h⟩
    exact ⟨C, hC, fun L₁ L₂ h1 h2 f g => h L₁ L₂ h1 h2 f g (hfin f) (hfin g)⟩
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, fun L₁ L₂ h1 h2 f g hf hg => ?_⟩
    exact h L₁ L₂ h1 h2 (Finsupp.ofSupportFinite f hf) (Finsupp.ofSupportFinite g hg)

end PrimeBHT.Interface.X1

end
