module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The analytic core of the lift (`l:lift`, `c:lift`)

Setting.  `κ : ℝ → ℂ` is measurable and integrable, `P` is a natural number, `h : ℤ →₀ ℂ` is
finitely supported.  The lift is
`H(x; y) = ∑_{n ∈ ℤ, n ≡ y (mod P)} h(n) κ((x - n) / P)`, for `x : ℝ`, `y : ZMod P`.
`Y_P = ZMod P` carries the *normalised* counting measure; mixed norms are written as explicit real
numbers (integrals over `x`, normalised sums over `y`).

The hypothesis `C := sup_t ∑_j ‖κ (t - j)‖ < ∞` is stated as
`hκs : ∀ t, Summable fun j : ℤ => ‖κ (t - j)‖` and `hC : ∀ t, ∑' j : ℤ, ‖κ (t - j)‖ ≤ C`
(summability is part of finiteness: a bare `tsum ≤ C` would be vacuous for non-summable families).
For the discrete variable `x ∈ ℤ`, the hypothesis `P⁻¹ ∑_{m ∈ ℤ} ‖κ (m / P)‖ ≤ C₁` is used.
-/

open MeasureTheory
open scoped NNReal

namespace PrimeBHT.Lift

@[expose] public section

/-- The lift `H(x; y) = ∑_{n ≡ y (P)} h n * κ ((x - n) / P)` (a finite sum, `h` is finitely
supported). -/
noncomputable def lift (κ : ℝ → ℂ) (P : ℕ) (h : ℤ →₀ ℂ) (x : ℝ) (y : ZMod P) : ℂ :=
  ∑ n ∈ h.support with ((n : ℤ) : ZMod P) = y, h n * κ ((x - n) / P)

/-- The `L^s(Y_P)` norm of `F : Y_P → ℂ` for the *normalised* counting measure on `Y_P = ZMod P`:
`((1/P) ∑_y ‖F y‖^s)^(1/s)`. -/
noncomputable def yNorm {P : ℕ} [NeZero P] (s : ℝ) (F : ZMod P → ℂ) : ℝ :=
  ((P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ s) ^ s⁻¹

/-- The `L^∞(Y_P)` norm of `F : Y_P → ℂ`, i.e. `max_y ‖F y‖`. -/
noncomputable def yNormInf {P : ℕ} [NeZero P] (F : ZMod P → ℂ) : ℝ :=
  ((Finset.univ.sup fun y => ‖F y‖₊ : ℝ≥0) : ℝ)

/-- The mixed norm `‖F‖_{L^p_x(ℝ; L^s_y(Y_P))} = (∫ ‖F x‖_{L^s_y}^p dx)^(1/p)`. -/
noncomputable def mixedNormR {P : ℕ} [NeZero P] (p s : ℝ) (F : ℝ → ZMod P → ℂ) : ℝ :=
  (∫ x, yNorm s (F x) ^ p) ^ p⁻¹

/-- The `ℓ^p(ℤ)` norm of a finitely supported function, `(∑_n ‖h n‖^p)^(1/p)`. -/
noncomputable def lpNorm (p : ℝ) (h : ℤ →₀ ℂ) : ℝ :=
  (∑ n ∈ h.support, ‖h n‖ ^ p) ^ p⁻¹

/-- The `ℓ^∞(ℤ)` norm of a finitely supported function, `max_n ‖h n‖`. -/
noncomputable def supNorm (h : ℤ →₀ ℂ) : ℝ :=
  ((h.support.sup fun n => ‖h n‖₊ : ℝ≥0) : ℝ)

section YNorm

variable {P : ℕ} [NeZero P]

lemma avg_rpow_nonneg (s : ℝ) (F : ZMod P → ℂ) : 0 ≤ (P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ s :=
  mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)

lemma yNorm_nonneg (s : ℝ) (F : ZMod P → ℂ) : 0 ≤ yNorm s F :=
  Real.rpow_nonneg (avg_rpow_nonneg s F) _

lemma yNormInf_nonneg (F : ZMod P → ℂ) : 0 ≤ yNormInf F := NNReal.coe_nonneg _

lemma yNorm_rpow_self {p : ℝ} (hp : p ≠ 0) (F : ZMod P → ℂ) :
    yNorm p F ^ p = (P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ p := by
  unfold yNorm
  exact Real.rpow_inv_rpow (avg_rpow_nonneg p F) hp

lemma norm_le_yNormInf (F : ZMod P → ℂ) (y : ZMod P) : ‖F y‖ ≤ yNormInf F := by
  have : ‖F y‖₊ ≤ Finset.univ.sup fun y => ‖F y‖₊ := Finset.le_sup (f := fun y => ‖F y‖₊)
    (Finset.mem_univ y)
  exact_mod_cast this

lemma yNormInf_le {F : ZMod P → ℂ} {M : ℝ} (hM : 0 ≤ M) (hF : ∀ y, ‖F y‖ ≤ M) :
    yNormInf F ≤ M := by
  unfold yNormInf
  have : (Finset.univ.sup fun y => ‖F y‖₊ : ℝ≥0) ≤ (⟨M, hM⟩ : ℝ≥0) :=
    Finset.sup_le fun y _ => by exact_mod_cast hF y
  exact_mod_cast this

lemma yNorm_le_yNormInf {s : ℝ} (hs : 0 < s) (F : ZMod P → ℂ) : yNorm s F ≤ yNormInf F := by
  set M := yNormInf F with hMdef
  have hM : 0 ≤ M := yNormInf_nonneg F
  have hF : ∀ y, ‖F y‖ ≤ M := norm_le_yNormInf F
  have h1 : ∑ y, ‖F y‖ ^ s ≤ ∑ _y : ZMod P, M ^ s :=
    Finset.sum_le_sum fun y _ => Real.rpow_le_rpow (norm_nonneg _) (hF y) hs.le
  have hPpos : (0 : ℝ) < P := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P)
  have h2 : (P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ s ≤ M ^ s := by
    calc (P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ s ≤ (P : ℝ)⁻¹ * ∑ _y : ZMod P, M ^ s := by gcongr
      _ = M ^ s := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ hPpos.ne', one_mul]
  unfold yNorm
  calc ((P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ s) ^ s⁻¹ ≤ (M ^ s) ^ s⁻¹ :=
        Real.rpow_le_rpow (avg_rpow_nonneg s F) h2 (inv_nonneg.2 hs.le)
    _ = M := Real.rpow_rpow_inv hM hs.ne'

lemma yNorm_mono {s p : ℝ} (hs : 0 < s) (hsp : s ≤ p) (F : ZMod P → ℂ) :
    yNorm s F ≤ yNorm p F := by
  have hp : 0 < p := hs.trans_le hsp
  have hPpos : (0 : ℝ) < P := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P)
  have hw : ∀ y ∈ (Finset.univ : Finset (ZMod P)), 0 ≤ (P : ℝ)⁻¹ := fun _ _ => by positivity
  have hw' : ∑ _y : ZMod P, (P : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_inv_cancel₀ hPpos.ne']
  have hz : ∀ y ∈ (Finset.univ : Finset (ZMod P)), 0 ≤ ‖F y‖ ^ s := fun y _ =>
    Real.rpow_nonneg (norm_nonneg _) _
  have hq : 1 ≤ p / s := by rw [le_div_iff₀ hs]; linarith
  have key := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ (fun _ => (P : ℝ)⁻¹)
    (fun y => ‖F y‖ ^ s) hw hw' hz hq
  have e1 : ∑ y, (P : ℝ)⁻¹ * ‖F y‖ ^ s = (P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ s := by
    rw [Finset.mul_sum]
  have e2 : ∑ y, (P : ℝ)⁻¹ * (‖F y‖ ^ s) ^ (p / s) = (P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ _ hs.ne']
  rw [e1, e2] at key
  unfold yNorm
  have hA : 0 ≤ (P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ s := avg_rpow_nonneg s F
  calc ((P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ s) ^ s⁻¹
      = (((P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ s) ^ (p / s)) ^ p⁻¹ := by
        rw [← Real.rpow_mul hA]
        congr 1
        field_simp
    _ ≤ ((P : ℝ)⁻¹ * ∑ y, ‖F y‖ ^ p) ^ p⁻¹ :=
        Real.rpow_le_rpow (Real.rpow_nonneg hA _) key (inv_nonneg.2 hp.le)

end YNorm

section Pointwise

variable {κ : ℝ → ℂ} {C : ℝ}

/-- A finite family of integers in a single residue class mod `P` has `κ`-weights summing to at most
`C` (the hypothesis `sup_t ∑_j ‖κ (t - j)‖ ≤ C`). -/
lemma sum_norm_kappa_le (hκs : ∀ t, Summable fun j : ℤ => ‖κ (t - j)‖)
    (hC : ∀ t, ∑' j : ℤ, ‖κ (t - j)‖ ≤ C) {P : ℕ} (hP : P ≠ 0) (r : ℤ) (S : Finset ℤ)
    (hS : ∀ n ∈ S, (P : ℤ) ∣ n - r) (x : ℝ) :
    ∑ n ∈ S, ‖κ ((x - n) / P)‖ ≤ C := by
  have hPR : (P : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hP
  set j : ℤ → ℤ := fun n => (n - r) / P with hj
  have hn : ∀ n ∈ S, n = r + P * j n := by
    intro n hnS
    have := Int.mul_ediv_cancel' (hS n hnS)
    simp only [hj]
    omega
  have hinj : ∀ a ∈ S, ∀ b ∈ S, j a = j b → a = b := by
    intro a ha b hb hab
    rw [hn a ha, hn b hb, hab]
  have e : ∀ n ∈ S, ‖κ ((x - n) / P)‖ = ‖κ ((x - r) / P - (j n : ℤ))‖ := by
    intro n hnS
    have hcast : (n : ℝ) = r + P * (j n : ℝ) := by exact_mod_cast hn n hnS
    have : (x - n) / P = (x - r) / P - (j n : ℤ) := by
      rw [hcast]
      field_simp
      ring
    rw [this]
  calc ∑ n ∈ S, ‖κ ((x - n) / P)‖ = ∑ n ∈ S, ‖κ ((x - r) / P - (j n : ℤ))‖ :=
        Finset.sum_congr rfl e
    _ = ∑ m ∈ S.image j, ‖κ ((x - r) / P - m)‖ := (Finset.sum_image (f := fun m : ℤ => ‖κ ((x - r) / P - m)‖) hinj).symm
    _ ≤ ∑' m : ℤ, ‖κ ((x - r) / P - m)‖ := (hκs _).sum_le_tsum _ (fun _ _ => norm_nonneg _)
    _ ≤ C := hC _

lemma fiber_dvd {P : ℕ} [NeZero P] {y : ZMod P} {n : ℤ} (hn : (n : ZMod P) = y) :
    (P : ℤ) ∣ n - (y.val : ℤ) := by
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
  exact hn.symm

/-- The kernel weights over one residue class mod `P`. -/
lemma sum_fiber_norm_kappa_le (hκs : ∀ t, Summable fun j : ℤ => ‖κ (t - j)‖)
    (hC : ∀ t, ∑' j : ℤ, ‖κ (t - j)‖ ≤ C) {P : ℕ} [NeZero P] (h : ℤ →₀ ℂ) (x : ℝ) (y : ZMod P) :
    ∑ n ∈ h.support with ((n : ℤ) : ZMod P) = y, ‖κ ((x - n) / P)‖ ≤ C :=
  sum_norm_kappa_le hκs hC (NeZero.ne P) (y.val : ℤ) _
    (fun _ hn => fiber_dvd (Finset.mem_filter.1 hn).2) x

lemma kernel_const_nonneg (hC : ∀ t, ∑' j : ℤ, ‖κ (t - j)‖ ≤ C) : 0 ≤ C :=
  (tsum_nonneg fun _ => norm_nonneg _).trans (hC 0)

lemma norm_lift_le (κ : ℝ → ℂ) (P : ℕ) (h : ℤ →₀ ℂ) (x : ℝ) (y : ZMod P) :
    ‖lift κ P h x y‖ ≤
      ∑ n ∈ h.support with ((n : ℤ) : ZMod P) = y, ‖h n‖ * ‖κ ((x - n) / P)‖ :=
  (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun _ _ => norm_mul _ _)

lemma norm_le_supNorm (h : ℤ →₀ ℂ) (n : ℤ) : ‖h n‖ ≤ supNorm h := by
  by_cases hn : n ∈ h.support
  · have : ‖h n‖₊ ≤ h.support.sup fun n => ‖h n‖₊ :=
      Finset.le_sup (f := fun n => ‖h n‖₊) hn
    exact_mod_cast this
  · rw [Finsupp.notMem_support_iff.1 hn, norm_zero]
    exact NNReal.coe_nonneg _

/-- **`p = ∞`** (part (c)): `‖H (x; y)‖ ≤ C ‖h‖_∞`, for all `x : ℝ` (in particular for `x ∈ ℤ`)
and all `y`. -/
theorem norm_lift_le_mul_supNorm (hκs : ∀ t, Summable fun j : ℤ => ‖κ (t - j)‖)
    (hC : ∀ t, ∑' j : ℤ, ‖κ (t - j)‖ ≤ C) {P : ℕ} [NeZero P] (h : ℤ →₀ ℂ) (x : ℝ) (y : ZMod P) :
    ‖lift κ P h x y‖ ≤ C * supNorm h := by
  have hs : 0 ≤ supNorm h := NNReal.coe_nonneg _
  calc ‖lift κ P h x y‖
      ≤ ∑ n ∈ h.support with ((n : ℤ) : ZMod P) = y, ‖h n‖ * ‖κ ((x - n) / P)‖ :=
        norm_lift_le κ P h x y
    _ ≤ ∑ n ∈ h.support with ((n : ℤ) : ZMod P) = y, supNorm h * ‖κ ((x - n) / P)‖ :=
        Finset.sum_le_sum fun n _ => by gcongr; exact norm_le_supNorm h n
    _ = supNorm h * ∑ n ∈ h.support with ((n : ℤ) : ZMod P) = y, ‖κ ((x - n) / P)‖ := by
        rw [Finset.mul_sum]
    _ ≤ supNorm h * C := by gcongr; exact sum_fiber_norm_kappa_le hκs hC h x y
    _ = C * supNorm h := mul_comm _ _

/-- The weighted Hölder step of the blueprint:
`|H (x; y)|^p ≤ C^(p-1) ∑_{n ≡ y} |h n|^p |κ ((x - n)/P)|`. -/
theorem norm_lift_rpow_le (hκs : ∀ t, Summable fun j : ℤ => ‖κ (t - j)‖)
    (hC : ∀ t, ∑' j : ℤ, ‖κ (t - j)‖ ≤ C) {P : ℕ} [NeZero P] {p : ℝ} (hp : 1 ≤ p)
    (h : ℤ →₀ ℂ) (x : ℝ) (y : ZMod P) :
    ‖lift κ P h x y‖ ^ p ≤
      C ^ (p - 1) * ∑ n ∈ h.support with ((n : ℤ) : ZMod P) = y,
        ‖h n‖ ^ p * ‖κ ((x - n) / P)‖ := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  set S := h.support.filter fun n : ℤ => ((n : ℤ) : ZMod P) = y with hS
  have hw : ∀ n : ℤ, 0 ≤ ‖κ ((x - n) / P)‖ := fun _ => norm_nonneg _
  have hf : ∀ n : ℤ, 0 ≤ ‖h n‖ := fun _ => norm_nonneg _
  have hHol := Real.inner_le_weight_mul_Lp_of_nonneg S hp (fun n : ℤ => ‖κ ((x - n) / P)‖)
    (fun n : ℤ => ‖h n‖) hw hf
  have hsumw : ∑ n ∈ S, ‖κ ((x - n) / P)‖ ≤ C := sum_fiber_norm_kappa_le hκs hC h x y
  have hsumw0 : 0 ≤ ∑ n ∈ S, ‖κ ((x - n) / P)‖ := Finset.sum_nonneg fun n _ => hw n
  have h1 : ‖lift κ P h x y‖ ≤ ∑ n ∈ S, ‖κ ((x - n) / P)‖ * ‖h n‖ :=
    (norm_lift_le κ P h x y).trans_eq (Finset.sum_congr rfl fun n _ => mul_comm _ _)
  have hc0 : 0 ≤ ∑ n ∈ S, ‖κ ((x - n) / P)‖ * ‖h n‖ ^ p :=
    Finset.sum_nonneg fun n _ => mul_nonneg (hw n) (Real.rpow_nonneg (hf n) _)
  calc ‖lift κ P h x y‖ ^ p
      ≤ (∑ n ∈ S, ‖κ ((x - n) / P)‖ * ‖h n‖) ^ p :=
        Real.rpow_le_rpow (norm_nonneg _) h1 hp0.le
    _ ≤ ((∑ n ∈ S, ‖κ ((x - n) / P)‖) ^ (1 - p⁻¹) *
          (∑ n ∈ S, ‖κ ((x - n) / P)‖ * ‖h n‖ ^ p) ^ p⁻¹) ^ p :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun n _ => mul_nonneg (hw n) (hf n)) hHol hp0.le
    _ = (∑ n ∈ S, ‖κ ((x - n) / P)‖) ^ (p - 1) *
          ∑ n ∈ S, ‖κ ((x - n) / P)‖ * ‖h n‖ ^ p := by
        rw [Real.mul_rpow (Real.rpow_nonneg hsumw0 _) (Real.rpow_nonneg hc0 _),
          ← Real.rpow_mul hsumw0, ← Real.rpow_mul hc0, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
        congr 2
        field_simp
    _ ≤ C ^ (p - 1) * ∑ n ∈ S, ‖κ ((x - n) / P)‖ * ‖h n‖ ^ p := by
        gcongr
    _ = C ^ (p - 1) * ∑ n ∈ S, ‖h n‖ ^ p * ‖κ ((x - n) / P)‖ := by
        congr 1
        exact Finset.sum_congr rfl fun n _ => mul_comm _ _

/-- Average over `y ∈ Y_P` of the weighted Hölder bound. -/
theorem yNorm_lift_rpow_le (hκs : ∀ t, Summable fun j : ℤ => ‖κ (t - j)‖)
    (hC : ∀ t, ∑' j : ℤ, ‖κ (t - j)‖ ≤ C) {P : ℕ} [NeZero P] {p : ℝ} (hp : 1 ≤ p)
    (h : ℤ →₀ ℂ) (x : ℝ) :
    yNorm p (lift κ P h x) ^ p ≤
      C ^ (p - 1) * ((P : ℝ)⁻¹ * ∑ n ∈ h.support, ‖h n‖ ^ p * ‖κ ((x - n) / P)‖) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp).ne'
  rw [yNorm_rpow_self hp0]
  calc (P : ℝ)⁻¹ * ∑ y, ‖lift κ P h x y‖ ^ p
      ≤ (P : ℝ)⁻¹ * ∑ y : ZMod P, C ^ (p - 1) *
          ∑ n ∈ h.support with ((n : ℤ) : ZMod P) = y, ‖h n‖ ^ p * ‖κ ((x - n) / P)‖ := by
        gcongr with y _
        exact norm_lift_rpow_le hκs hC hp h x y
    _ = C ^ (p - 1) * ((P : ℝ)⁻¹ * ∑ n ∈ h.support, ‖h n‖ ^ p * ‖κ ((x - n) / P)‖) := by
        rw [← Finset.mul_sum, Finset.sum_fiberwise h.support
          (fun n : ℤ => ((n : ℤ) : ZMod P)) (fun n => ‖h n‖ ^ p * ‖κ ((x - n) / P)‖)]
        ring

end Pointwise

section RealLine

variable {κ : ℝ → ℂ} {C : ℝ}

lemma integrable_norm_kappa_shift (hκi : Integrable κ) {P : ℕ} (hP : P ≠ 0) (n : ℤ) :
    Integrable fun x : ℝ => ‖κ ((x - n) / P)‖ :=
  (hκi.norm.comp_div (Nat.cast_ne_zero.2 hP)).comp_sub_right (n : ℝ)

lemma integral_norm_kappa_shift {P : ℕ} (n : ℤ) :
    ∫ x : ℝ, ‖κ ((x - n) / P)‖ = P * ∫ x : ℝ, ‖κ x‖ := by
  have h1 := integral_sub_right_eq_self (μ := volume) (fun u : ℝ => ‖κ (u / P)‖) (n : ℝ)
  have h2 := Measure.integral_comp_div (fun x : ℝ => ‖κ x‖) (P : ℝ)
  rw [h1, h2, smul_eq_mul, abs_of_nonneg (Nat.cast_nonneg _)]

lemma measurable_lift (hκm : Measurable κ) (P : ℕ) (h : ℤ →₀ ℂ) (y : ZMod P) :
    Measurable fun x : ℝ => lift κ P h x y := by
  unfold lift
  exact Finset.measurable_sum _ fun n _ =>
    measurable_const.mul (hκm.comp ((measurable_id.sub_const _).div_const _))

lemma measurable_yNorm_lift_rpow (hκm : Measurable κ) {P : ℕ} [NeZero P] (s p : ℝ)
    (h : ℤ →₀ ℂ) : Measurable fun x : ℝ => yNorm s (lift κ P h x) ^ p := by
  unfold yNorm
  exact ((measurable_const.mul (Finset.measurable_sum _ fun y _ =>
    (measurable_lift hκm P h y).norm.pow_const s)).pow_const _).pow_const p

/-- The majorant of the `y`-averaged `p`-th power of the lift. -/
lemma integrable_majorant (hκi : Integrable κ) {P : ℕ} (hP : P ≠ 0) (p : ℝ) (c : ℝ)
    (h : ℤ →₀ ℂ) :
    Integrable fun x : ℝ =>
      c * ((P : ℝ)⁻¹ * ∑ n ∈ h.support, ‖h n‖ ^ p * ‖κ ((x - n) / P)‖) :=
  ((integrable_finsetSum _ fun n _ =>
    (integrable_norm_kappa_shift hκi hP n).const_mul (‖h n‖ ^ p)).const_mul _).const_mul _

lemma integral_majorant (hκi : Integrable κ) {P : ℕ} [NeZero P] (p : ℝ) (c : ℝ)
    (h : ℤ →₀ ℂ) :
    ∫ x : ℝ, c * ((P : ℝ)⁻¹ * ∑ n ∈ h.support, ‖h n‖ ^ p * ‖κ ((x - n) / P)‖)
      = c * ((∫ x : ℝ, ‖κ x‖) * ∑ n ∈ h.support, ‖h n‖ ^ p) := by
  have hPpos : (P : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne P)
  rw [integral_const_mul, integral_const_mul,
    integral_finsetSum _ fun n _ =>
      (integrable_norm_kappa_shift hκi (NeZero.ne P) n).const_mul (‖h n‖ ^ p)]
  simp_rw [integral_const_mul, integral_norm_kappa_shift]
  rw [← Finset.sum_mul]
  field_simp

end RealLine

section MainReal

variable {κ : ℝ → ℂ} {C : ℝ}

theorem integrable_yNorm_lift_rpow (hκm : Measurable κ) (hκi : Integrable κ)
    (hκs : ∀ t, Summable fun j : ℤ => ‖κ (t - j)‖)
    (hC : ∀ t, ∑' j : ℤ, ‖κ (t - j)‖ ≤ C) {P : ℕ} [NeZero P] {p : ℝ} (hp : 1 ≤ p)
    (h : ℤ →₀ ℂ) :
    Integrable fun x : ℝ => yNorm p (lift κ P h x) ^ p := by
  refine Integrable.mono' (integrable_majorant hκi (NeZero.ne P) p (C ^ (p - 1)) h)
    (measurable_yNorm_lift_rpow hκm p p h).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro x
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (yNorm_nonneg _ _) _)]
  exact yNorm_lift_rpow_le hκs hC hp h x

/-- **(a)** For `1 ≤ p < ∞`:
`‖H‖_{L^p_x(ℝ; L^p_y(Y_P))} ≤ C^((p-1)/p) ‖κ‖_{L¹}^(1/p) ‖h‖_{ℓ^p}`, with the integrand
integrable; the constant does not depend on `P`. -/
theorem mixedNormR_lift_le (hκm : Measurable κ) (hκi : Integrable κ)
    (hκs : ∀ t, Summable fun j : ℤ => ‖κ (t - j)‖)
    (hC : ∀ t, ∑' j : ℤ, ‖κ (t - j)‖ ≤ C) {P : ℕ} [NeZero P] {p : ℝ} (hp : 1 ≤ p)
    (h : ℤ →₀ ℂ) :
    Integrable (fun x : ℝ => yNorm p (lift κ P h x) ^ p) ∧
      mixedNormR p p (lift κ P h) ≤
        C ^ ((p - 1) / p) * (∫ x : ℝ, ‖κ x‖) ^ p⁻¹ * lpNorm p h := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hC0 : 0 ≤ C := kernel_const_nonneg hC
  refine ⟨integrable_yNorm_lift_rpow hκm hκi hκs hC hp h, ?_⟩
  have hI : 0 ≤ ∫ x : ℝ, ‖κ x‖ := integral_nonneg fun _ => norm_nonneg _
  have hB : 0 ≤ ∑ n ∈ h.support, ‖h n‖ ^ p :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
  have hint : ∫ x : ℝ, yNorm p (lift κ P h x) ^ p ≤
      C ^ (p - 1) * ((∫ x : ℝ, ‖κ x‖) * ∑ n ∈ h.support, ‖h n‖ ^ p) := by
    rw [← integral_majorant hκi (P := P) p (C ^ (p - 1)) h]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun x =>
        Real.rpow_nonneg (yNorm_nonneg _ _) _)
      (integrable_majorant hκi (NeZero.ne P) p (C ^ (p - 1)) h)
      (Filter.Eventually.of_forall fun x => yNorm_lift_rpow_le hκs hC hp h x)
  unfold mixedNormR lpNorm
  calc (∫ x : ℝ, yNorm p (lift κ P h x) ^ p) ^ p⁻¹
      ≤ (C ^ (p - 1) * ((∫ x : ℝ, ‖κ x‖) * ∑ n ∈ h.support, ‖h n‖ ^ p)) ^ p⁻¹ :=
        Real.rpow_le_rpow (integral_nonneg fun x => Real.rpow_nonneg (yNorm_nonneg _ _) _) hint
          (inv_nonneg.2 hp0.le)
    _ = C ^ ((p - 1) / p) * (∫ x : ℝ, ‖κ x‖) ^ p⁻¹ * (∑ n ∈ h.support, ‖h n‖ ^ p) ^ p⁻¹ := by
        rw [Real.mul_rpow (Real.rpow_nonneg hC0 _) (mul_nonneg hI hB),
          Real.mul_rpow hI hB, ← Real.rpow_mul hC0, div_eq_mul_inv, mul_assoc]

end MainReal

section Discrete

variable {κ : ℝ → ℂ} {C : ℝ}

end Discrete

section Monotone

variable {P : ℕ} [NeZero P]

end Monotone

section MonotoneLift

variable {κ : ℝ → ℂ} {C : ℝ} {P : ℕ} [NeZero P]

/-- **(c) and (d) for `p = ∞`**: for every `x : ℝ` (in particular `x ∈ ℤ`), and `1 ≤ s < ∞`,
`‖H (x; ·)‖_{L^s(Y_P)} ≤ ‖H (x; ·)‖_{L^∞(Y_P)} ≤ C ‖h‖_{ℓ^∞}`. -/
theorem yNorm_lift_le_yNormInf_le (hκs : ∀ t, Summable fun j : ℤ => ‖κ (t - j)‖)
    (hC : ∀ t, ∑' j : ℤ, ‖κ (t - j)‖ ≤ C) {s : ℝ} (hs : 1 ≤ s) (h : ℤ →₀ ℂ) (x : ℝ) :
    yNorm s (lift κ P h x) ≤ yNormInf (lift κ P h x) ∧
      yNormInf (lift κ P h x) ≤ C * supNorm h := by
  have hC0 : 0 ≤ C := kernel_const_nonneg hC
  have hinf : yNormInf (lift κ P h x) ≤ C * supNorm h :=
    yNormInf_le (mul_nonneg hC0 (NNReal.coe_nonneg _)) fun y =>
      norm_lift_le_mul_supNorm hκs hC h x y
  exact ⟨yNorm_le_yNormInf (lt_of_lt_of_le one_pos hs) _, hinf⟩

end MonotoneLift

end

end PrimeBHT.Lift
