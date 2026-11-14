module

public import PrimeBHT.Kernel
public import PrimeBHT.FixedAverage
public import PrimeCarleson.Proof.Paper.Defs.Weights
public import PrimeCarleson.Proof.Goal0.Exponents

/-!
# `e:progression` (blueprint node N24), conditional on the time-frequency anchor X1

The time-frequency input X1 (a bound for the bilinear Hilbert transform on `ℤ` with smooth
truncations, uniform in the truncation radii) is NOT proved in this project.  It is stated as the
explicit proposition `BHTSmooth χ p q r C`; every theorem that uses it is named `…_of_bhtSmooth`.

* Part (1) (N02, paper L650-656): the Möbius-inversion identity `bilin_kernelI_wQ`
  `T_I^Q(f,g) = ∑_{Q/2<q≤Q} μ(q)/φ(q) ∑_{d | q} μ(q/d) T_d^I(f,g)`, with
  `T_d^I(f,g)(x) = ∑_m d K_I(dm) f(x-dm) g(x+dm)` (`stepOp d (progKernel χ a b d)`); unconditional.
* Part (2) (N24 steps 2-4, FINDINGS F7(a),(b)): `eLpNorm_stepOp_le` (step `d` from step `1` by
  residue classes and Hölder with exponents `p/r, q/r`, valid for all `p, q, r > 0` with
  `1/r = 1/p + 1/q`; unconditional given a step-1 bound for the kernel), `progKernel_eq_truncKernel`
  (`d K_I(dm) = (χ(m/L₂) - χ(m/L₁))/m`, `L₂ = 2^b/d`, `L₁ = 2^{a-1}/d`) and
  `eLpNorm_stepOp_kernelI_le_of_bhtSmooth`.  (If `L₁ ≤ 1` the inner term vanishes:
  `truncKernel_eq_of_le_one`; X1 covers every `0 < L₁ < L₂`, so no case split is needed.)
* Part (3) (blueprint 3.6): `eLpNorm_sum_rpow_le`, `‖∑ T_i‖_r^σ ≤ ∑ ‖T_i‖_r^σ`, `σ = min r 1`
  (Mathlib's `eLpNorm_add_le'` is not used); unconditional.
* Counting (A3): `exists_coefSum_le`, `∑_{Q/2<q≤Q} d_div(q) φ(q)^{-σ} ≤ A Q^{1-σ+ε}`; unconditional.
* Part (4): `progression_coefSum_of_bhtSmooth` and `progression_of_bhtSmooth`.
-/

@[expose] public section

open scoped ENNReal ComplexConjugate

namespace PrimeBHT.Progression

open PrimeBHT.Kernel PrimeCarleson ArithmeticFunction

/-! ### Part (1): the Möbius-inversion identity (N02) -/

/-- The step-`d` operator `T_d(f,g)(x) = ∑_m a(m) f(x - d m) g(x + d m)`
(a finite sum when `f` or `g` is finitely supported). -/
noncomputable def stepOp (d : ℕ) (a : ℤ → ℂ) (f g : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑' m : ℤ, a m * f (x - d * m) * g (x + d * m)

/-- The coefficient `μ(q)/φ(q)` of `w_Q`. -/
noncomputable def coef (q : ℕ) : ℂ := (((moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ) : ℝ)

lemma blockWeight_eq_sum_ite (B : Finset ℕ) (n : ℤ) :
    blockWeight B n = ∑ q ∈ B, ∑ d ∈ q.divisors,
      (coef q * ((moebius (q / d) : ℤ) : ℂ)) * (if (d : ℤ) ∣ n then (d : ℂ) else 0) := by
  unfold blockWeight
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [PrimeCarleson.Proof.Goal0.ramanujanSum_eq_sum_divisors, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases h : (d : ℤ) ∣ n <;> simp [h, coef]
  ring

lemma tsum_ite_dvd (d : ℕ) (hd : 0 < d) (G : ℤ → ℂ) :
    ∑' n : ℤ, (if (d : ℤ) ∣ n then G n else 0) = ∑' m : ℤ, G (d * m) := by
  have hinj : Function.Injective (fun m : ℤ => (d : ℤ) * m) := by
    intro a b h
    have : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
    exact mul_left_cancel₀ this h
  rw [← hinj.tsum_eq (f := fun n : ℤ => if (d : ℤ) ∣ n then G n else 0)]
  · simp
  · intro n hn
    by_cases h : (d : ℤ) ∣ n
    · obtain ⟨m, rfl⟩ := h
      exact ⟨m, rfl⟩
    · exact absurd (by simp [h]) hn

lemma finite_support_shift {f : ℤ → ℂ} (hf : (Function.support f).Finite) (x : ℤ) :
    (Function.support fun n : ℤ => f (x - n)).Finite := by
  have hinj : Set.InjOn (fun n : ℤ => x - n) Set.univ := fun a _ b _ h => by simpa using h
  exact hf.preimage (hinj.mono (Set.subset_univ _))

lemma summable_of_support_finite {h : ℤ → ℂ} (hh : (Function.support h).Finite) : Summable h :=
  summable_of_ne_finset_zero (s := hh.toFinset) fun x hx => by simpa using hx

theorem bilin_mul_blockWeight (K : ℤ → ℂ) {f g : ℤ → ℂ} (hf : (Function.support f).Finite)
    (B : Finset ℕ) (x : ℤ) :
    bilin (fun n => K n * blockWeight B n) f g x =
      ∑ q ∈ B, ∑ d ∈ q.divisors, (coef q * ((moebius (q / d) : ℤ) : ℂ)) *
        stepOp d (fun m => (d : ℂ) * K (d * m)) f g x := by
  have hfin := finite_support_shift hf x
  unfold bilin
  have h1 : ∀ n : ℤ, K n * blockWeight B n * f (x - n) * g (x + n) =
      ∑ q ∈ B, ∑ d ∈ q.divisors, (coef q * ((moebius (q / d) : ℤ) : ℂ)) *
        (if (d : ℤ) ∣ n then (d : ℂ) * K n * f (x - n) * g (x + n) else 0) := by
    intro n
    rw [blockWeight_eq_sum_ite, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases h : (d : ℤ) ∣ n <;> simp [h]
    ring
  simp_rw [h1]
  have hsum : ∀ q d : ℕ, Summable fun n : ℤ => (coef q * ((moebius (q / d) : ℤ) : ℂ)) *
      (if (d : ℤ) ∣ n then (d : ℂ) * K n * f (x - n) * g (x + n) else 0) := by
    intro q d
    refine summable_of_support_finite (hfin.subset ?_)
    intro n hn
    rw [Function.mem_support] at hn ⊢
    intro h0
    apply hn
    by_cases h : (d : ℤ) ∣ n
    · simp [h, h0]
    · simp [h]
  rw [Summable.tsum_finsetSum (fun q _ => summable_sum fun d _ => hsum q d)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Summable.tsum_finsetSum (fun d _ => hsum q d)]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  rw [tsum_mul_left, tsum_ite_dvd d hd0, stepOp]


/-! ### The kernels of the progression step and the anchor X1 -/

/-- The kernel `d K_I(d m)` of the step-`d` operator, `K_I = kernelI χ a b`. -/
noncomputable def progKernel (χ : ℝ → ℝ) (a b d : ℕ) (m : ℤ) : ℂ :=
  (((d : ℝ) * kernelI χ a b ((d : ℝ) * m) : ℝ) : ℂ)

lemma progKernel_zero (χ : ℝ → ℝ) (a b d : ℕ) : progKernel χ a b d 0 = 0 := by
  simp [progKernel, kernelI_zero]

/-- The kernel `(χ(m/L₂) - χ(m/L₁))/m` of the anchor X1 (`0` at `m = 0`). -/
noncomputable def truncKernel (χ : ℝ → ℝ) (L₁ L₂ : ℝ) (m : ℤ) : ℂ :=
  if m = 0 then 0 else (((χ (m / L₂) - χ (m / L₁)) / m : ℝ) : ℂ)

/-- The `ℓ^r` bound with constant `C` for the bilinear operator with kernel `a`, for finitely
supported inputs. -/
def BilinBound (a : ℤ → ℂ) (p q r C : ℝ) : Prop :=
  ∀ f g : ℤ → ℂ, (Function.support f).Finite → (Function.support g).Finite →
    MeasureTheory.eLpNorm (bilin a f g) (ENNReal.ofReal r) MeasureTheory.Measure.count ≤
      ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count *
        MeasureTheory.eLpNorm g (ENNReal.ofReal q) MeasureTheory.Measure.count

/-- **The time-frequency anchor X1** (blueprint section 2.3): for all real `0 < L₁ < L₂` and all
finitely supported `f, g`,
`‖x ↦ ∑_{m ≠ 0} ((χ(m/L₂) - χ(m/L₁))/m) f(x-m) g(x+m)‖_{ℓ^r} ≤ C ‖f‖_p ‖g‖_q`.
NOT proved in this project; every theorem that assumes it is named `…_of_bhtSmooth`. -/
def BHTSmooth (χ : ℝ → ℝ) (p q r C : ℝ) : Prop :=
  ∀ L₁ L₂ : ℝ, 0 < L₁ → L₁ < L₂ → BilinBound (truncKernel χ L₁ L₂) p q r C

/-! ### Part (2): residue-class reduction -/

/-- The `ℓ^s` power sum `∑_x ‖h x‖^s` in `ℝ≥0∞`. -/
noncomputable def lsum (s : ℝ) (h : ℤ → ℂ) : ℝ≥0∞ := ∑' x, ENNReal.ofReal ‖h x‖ ^ s

lemma eLpNorm_eq_lsum (h : ℤ → ℂ) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.eLpNorm h (ENNReal.ofReal s) MeasureTheory.Measure.count = lsum s h ^ (1 / s) :=
  PrimeBHT.FixedAverage.eLpNorm_count_eq h hs

lemma tsum_residue (d : ℕ) [NeZero d] (h : ℤ → ℝ≥0∞) :
    ∑' x, h x = ∑ ρ : Fin d, ∑' y : ℤ, h (ρ + d * y) := by
  rw [← (Int.divModEquiv d).symm.tsum_eq]
  simp only [Int.divModEquiv_symm_apply]
  rw [ENNReal.tsum_prod (f := fun (y : ℤ) (ρ : Fin d) => h (y * d + ρ)), ENNReal.tsum_comm,
    tsum_fintype]
  refine Finset.sum_congr rfl fun ρ _ => tsum_congr fun y => ?_
  congr 1
  ring

lemma stepOp_residue (d : ℕ) (a f g : ℤ → ℂ) (ρ y : ℤ) :
    stepOp d a f g (ρ + d * y) =
      bilin a (fun z => f (ρ + d * z)) (fun z => g (ρ + d * z)) y := by
  unfold stepOp bilin
  refine tsum_congr fun m => ?_
  have h1 : ρ + d * y - d * m = ρ + d * (y - m) := by ring
  have h2 : ρ + d * y + d * m = ρ + d * (y + m) := by ring
  rw [h1, h2]

lemma lsum_stepOp (d : ℕ) [NeZero d] (a f g : ℤ → ℂ) (s : ℝ) :
    lsum s (stepOp d a f g) =
      ∑ ρ : Fin d, lsum s (bilin a (fun z => f (ρ + d * z)) (fun z => g (ρ + d * z))) := by
  unfold lsum
  rw [tsum_residue d]
  refine Finset.sum_congr rfl fun ρ _ => tsum_congr fun y => ?_
  rw [stepOp_residue]

lemma lsum_residue (d : ℕ) [NeZero d] (f : ℤ → ℂ) (s : ℝ) :
    lsum s f = ∑ ρ : Fin d, lsum s (fun z => f (ρ + d * z)) := by
  unfold lsum
  rw [tsum_residue d]

lemma lsum_bilin_le {a : ℤ → ℂ} {p q r C : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hb : BilinBound a p q r C) {F G : ℤ → ℂ} (hF : (Function.support F).Finite)
    (hG : (Function.support G).Finite) :
    lsum r (bilin a F G) ≤
      ENNReal.ofReal C ^ r * lsum p F ^ (r / p) * lsum q G ^ (r / q) := by
  have h := hb F G hF hG
  rw [eLpNorm_eq_lsum _ hr, eLpNorm_eq_lsum _ hp, eLpNorm_eq_lsum _ hq] at h
  have h2 := ENNReal.rpow_le_rpow h hr.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ hr.le, ENNReal.mul_rpow_of_nonneg _ _ hr.le,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h2
  convert h2 using 3 <;> ring_nf

lemma holder_residue {d : ℕ} {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpqr : 1 / r = 1 / p + 1 / q) (U V : Fin d → ℝ≥0∞) :
    ∑ ρ, U ρ ^ (r / p) * V ρ ^ (r / q) ≤ (∑ ρ, U ρ) ^ (r / p) * (∑ ρ, V ρ) ^ (r / q) := by
  have hrp : r / p + r / q = 1 := by
    have : r * (1 / p + 1 / q) = 1 := by rw [← hpqr]; field_simp
    rw [← this]; ring
  have hpr : (p / r).HolderConjugate (q / r) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [one_lt_div hr]
      have : 0 < 1 / q := by positivity
      have h3 : 1 / p < 1 / r := by linarith
      rw [one_div_lt_one_div hp hr] at h3
      exact h3
    · rw [inv_div, inv_div]; exact hrp
  have h := ENNReal.inner_le_Lp_mul_Lq Finset.univ (fun ρ => U ρ ^ (r / p))
    (fun ρ => V ρ ^ (r / q)) hpr
  have e1 : ∀ ρ, (U ρ ^ (r / p)) ^ (p / r) = U ρ := fun ρ => by
    rw [← ENNReal.rpow_mul, show r / p * (p / r) = 1 by field_simp, ENNReal.rpow_one]
  have e2 : ∀ ρ, (V ρ ^ (r / q)) ^ (q / r) = V ρ := fun ρ => by
    rw [← ENNReal.rpow_mul, show r / q * (q / r) = 1 by field_simp, ENNReal.rpow_one]
  simp only [e1, e2, one_div_div] at h
  exact h


lemma finite_support_residue {f : ℤ → ℂ} (hf : (Function.support f).Finite) (d : ℕ) (hd : 0 < d)
    (ρ : ℤ) : (Function.support fun z : ℤ => f (ρ + d * z)).Finite := by
  have hinj : Set.InjOn (fun z : ℤ => ρ + (d : ℤ) * z) Set.univ := by
    intro a _ b _ h
    have h0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
    exact mul_left_cancel₀ h0 (by simpa using h)
  exact hf.preimage (hinj.mono (Set.subset_univ _))

/-- **Residue-class reduction** (blueprint N24 steps 2 and 4; FINDINGS F7(a)): if the step-`1`
bound holds for the kernel `a` with constant `C`, then the step-`d` operator satisfies the same
bound with the same constant `C`, for every `d ≥ 1` and every `p, q, r > 0` with
`1/r = 1/p + 1/q` (Hölder with the conjugate exponents `p/r, q/r`). -/
theorem eLpNorm_stepOp_le {a : ℤ → ℂ} {p q r C : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpqr : 1 / r = 1 / p + 1 / q) (hb : BilinBound a p q r C) {d : ℕ} (hd : 0 < d)
    {f g : ℤ → ℂ} (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) :
    MeasureTheory.eLpNorm (stepOp d a f g) (ENNReal.ofReal r) MeasureTheory.Measure.count ≤
      ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count *
        MeasureTheory.eLpNorm g (ENNReal.ofReal q) MeasureTheory.Measure.count := by
  have : NeZero d := ⟨hd.ne'⟩
  set U : Fin d → ℝ≥0∞ := fun ρ => lsum p (fun z => f (ρ + d * z)) with hU
  set V : Fin d → ℝ≥0∞ := fun ρ => lsum q (fun z => g (ρ + d * z)) with hV
  have h1 : lsum r (stepOp d a f g) ≤
      ENNReal.ofReal C ^ r * (lsum p f ^ (r / p) * lsum q g ^ (r / q)) := by
    rw [lsum_stepOp]
    calc ∑ ρ : Fin d, lsum r (bilin a (fun z => f (ρ + d * z)) (fun z => g (ρ + d * z)))
        ≤ ∑ ρ : Fin d, ENNReal.ofReal C ^ r * (U ρ ^ (r / p) * V ρ ^ (r / q)) := by
          refine Finset.sum_le_sum fun ρ _ => ?_
          rw [← mul_assoc]
          exact lsum_bilin_le hp hq hr hb (finite_support_residue hf d hd ρ)
            (finite_support_residue hg d hd ρ)
      _ = ENNReal.ofReal C ^ r * ∑ ρ : Fin d, U ρ ^ (r / p) * V ρ ^ (r / q) := by
          rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal C ^ r * ((∑ ρ, U ρ) ^ (r / p) * (∑ ρ, V ρ) ^ (r / q)) := by
          gcongr
          exact holder_residue hp hq hr hpqr U V
      _ = _ := by rw [lsum_residue d f p, lsum_residue d g q]
  rw [eLpNorm_eq_lsum _ hr, eLpNorm_eq_lsum _ hp, eLpNorm_eq_lsum _ hq]
  calc lsum r (stepOp d a f g) ^ (1 / r)
      ≤ (ENNReal.ofReal C ^ r * (lsum p f ^ (r / p) * lsum q g ^ (r / q))) ^ (1 / r) :=
        ENNReal.rpow_le_rpow h1 (by positivity)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_assoc]
        have e0 : r * (1 / r) = 1 := by field_simp
        have e1 : r / p * (1 / r) = 1 / p := by field_simp
        have e2 : r / q * (1 / r) = 1 / q := by field_simp
        rw [e0, e1, e2, ENNReal.rpow_one]

/-- For `1 ≤ a ≤ b` and `d ≥ 1`, the kernel `d K_I(d m)` is the anchor kernel
`(χ(m/L₂) - χ(m/L₁))/m` with `L₂ = 2^b/d`, `L₁ = 2^{a-1}/d` (`0 < L₁ < L₂`). -/
lemma progKernel_eq_truncKernel (χ : ℝ → ℝ) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) {d : ℕ}
    (hd : 0 < d) :
    progKernel χ a b d = truncKernel χ ((2 : ℝ) ^ (a - 1) / d) ((2 : ℝ) ^ b / d) := by
  funext m
  by_cases hm : m = 0
  · subst hm; simp [progKernel_zero, truncKernel]
  · have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have key := mul_kernelI χ ha hab ((d : ℝ) * m)
    have hdm : (d : ℝ) * m ≠ 0 := mul_ne_zero hdR.ne' hmR
    have e1 : (m : ℝ) / ((2 : ℝ) ^ b / d) = d * m / 2 ^ b := by field_simp
    have e2 : (m : ℝ) / ((2 : ℝ) ^ (a - 1) / d) = d * m / 2 ^ (a - 1) := by field_simp
    simp only [progKernel, truncKernel, hm, ite_false, e1, e2]
    congr 1
    rw [← key]
    field_simp

lemma radii_pos_lt {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) {d : ℕ} (hd : 0 < d) :
    0 < (2 : ℝ) ^ (a - 1) / d ∧ (2 : ℝ) ^ (a - 1) / d < (2 : ℝ) ^ b / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨by positivity, ?_⟩
  apply div_lt_div_of_pos_right _ hdR
  exact pow_lt_pow_right₀ (by norm_num) (by omega)

/-- **Step `d` from X1** (blueprint N24 steps 2-4): the operator
`T_d^I(f,g)(x) = ∑_m d K_I(d m) f(x - d m) g(x + d m)` obeys `‖T_d^I(f,g)‖_{ℓ^r} ≤ C ‖f‖_p ‖g‖_q`,
uniformly in `d ≥ 1` and `I = [a, b]`, `1 ≤ a ≤ b`. -/
theorem eLpNorm_stepOp_kernelI_le_of_bhtSmooth {χ : ℝ → ℝ} {p q r C : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r) (hpqr : 1 / r = 1 / p + 1 / q) (hX : BHTSmooth χ p q r C) {a b : ℕ} (ha : 1 ≤ a)
    (hab : a ≤ b) {d : ℕ} (hd : 0 < d) {f g : ℤ → ℂ} (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) :
    MeasureTheory.eLpNorm (stepOp d (progKernel χ a b d) f g) (ENNReal.ofReal r)
        MeasureTheory.Measure.count ≤
      ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count *
        MeasureTheory.eLpNorm g (ENNReal.ofReal q) MeasureTheory.Measure.count := by
  have hrad := radii_pos_lt ha hab hd
  have hb := hX _ _ hrad.1 hrad.2
  rw [← progKernel_eq_truncKernel χ ha hab hd] at hb
  exact eLpNorm_stepOp_le hp hq hr hpqr hb hd hf hg

/-! ### Part (1), specialised to `K_I` and `w_Q` -/

/-- **Möbius-inversion identity** (blueprint N02(d), paper L650-656):
`∑_n K_I(n) w_Q(n) f(x-n) g(x+n)
  = ∑_{Q/2<q≤Q} (μ(q)/φ(q)) ∑_{d | q} μ(q/d) ∑_m d K_I(d m) f(x-dm) g(x+dm)`.
(`K_I(0) = 0`, `progKernel_zero`: the `m = 0` terms vanish; the identity itself does not need it.) -/
theorem bilin_kernelI_wQ (χ : ℝ → ℝ) (a b Q : ℕ) {f g : ℤ → ℂ} (hf : (Function.support f).Finite)
    (x : ℤ) :
    bilin (fun n : ℤ => ((kernelI χ a b (n : ℝ) : ℝ) : ℂ) * PrimeCarleson.Proof.Paper.wQ Q n)
        f g x =
      ∑ q ∈ Finset.Ioc (Q / 2) Q, coef q * ∑ d ∈ q.divisors,
        ((moebius (q / d) : ℤ) : ℂ) * stepOp d (progKernel χ a b d) f g x := by
  have h := bilin_mul_blockWeight (fun n : ℤ => ((kernelI χ a b (n : ℝ) : ℝ) : ℂ)) (g := g) hf
    (Finset.Ioc (Q / 2) Q) x
  have hK : ∀ d : ℕ, (fun m : ℤ => (d : ℂ) * ((kernelI χ a b (((d : ℤ) * m : ℤ) : ℝ) : ℝ) : ℂ)) =
      progKernel χ a b d := by
    intro d; funext m; simp [progKernel]
  simp only [hK] at h
  unfold PrimeCarleson.Proof.Paper.wQ
  rw [h]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring


/-! ### Part (3): the quasi-triangle inequality for `ℓ^r`, `r < 1` -/

lemma lsum_add_le {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (A B : ℤ → ℂ) :
    lsum s (A + B) ≤ lsum s A + lsum s B := by
  unfold lsum
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  have h1 : ENNReal.ofReal ‖(A + B) x‖ ≤ ENNReal.ofReal ‖A x‖ + ENNReal.ofReal ‖B x‖ := by
    rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
  exact (ENNReal.rpow_le_rpow h1 hs0.le).trans (ENNReal.rpow_add_le_add_rpow _ _ hs0.le hs1)

lemma lsum_zero {s : ℝ} (hs0 : 0 < s) : lsum s (0 : ℤ → ℂ) = 0 := by
  simp [lsum, ENNReal.zero_rpow_of_pos hs0]

lemma lsum_sum_le {ι : Type*} {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (t : Finset ι)
    (T : ι → ℤ → ℂ) : lsum s (∑ i ∈ t, T i) ≤ ∑ i ∈ t, lsum s (T i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [lsum_zero hs0]
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (lsum_add_le hs0 hs1 _ _).trans (by gcongr)

/-- **Quasi-triangle inequality** (blueprint 3.6, Q1 and Minkowski): for every `r > 0` and
`σ = min r 1`, `‖∑_i T_i‖_{ℓ^r}^σ ≤ ∑_i ‖T_i‖_{ℓ^r}^σ`, with no constant. -/
theorem eLpNorm_sum_rpow_le {ι : Type*} (t : Finset ι) (T : ι → ℤ → ℂ) {r : ℝ} (hr : 0 < r) :
    MeasureTheory.eLpNorm (∑ i ∈ t, T i) (ENNReal.ofReal r) MeasureTheory.Measure.count ^
        min r 1 ≤
      ∑ i ∈ t, MeasureTheory.eLpNorm (T i) (ENNReal.ofReal r) MeasureTheory.Measure.count ^
        min r 1 := by
  rcases le_total r 1 with h | h
  · rw [min_eq_left h]
    simp only [eLpNorm_eq_lsum _ hr, ← ENNReal.rpow_mul, one_div_mul_cancel hr.ne',
      ENNReal.rpow_one]
    exact lsum_sum_le hr h t T
  · rw [min_eq_right h]
    simp only [ENNReal.rpow_one]
    exact MeasureTheory.eLpNorm_sum_le (ENNReal.one_le_ofReal.2 h)

/-! ### The coefficient sum (A1)-(A3) -/

/-- The coefficient sum `∑_{Q/2<q≤Q} d_div(q) φ(q)^{-σ}` of L670-671. -/
noncomputable def coefSum (σ : ℝ) (Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ioc (Q / 2) Q, (q.divisors.card : ℝ) * (Nat.totient q : ℝ) ^ (-σ)

/-- (A3): `∑_{Q/2<q≤Q} d_div(q) φ(q)^{-σ} ≤ C_ε Q^{1-σ+ε}` for `σ ∈ (0, 1]`. Only (A1) (divisor
bound) and `q ≤ d_div(q) φ(q)` are used (this gives `1/φ(q) ≤ 2 C Q^{δ-1}` via the vendored
`inv_totient_le`). -/
theorem exists_coefSum_le {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ Q : ℕ, 1 ≤ Q → coefSum σ Q ≤ A * (Q : ℝ) ^ (1 - σ + ε) := by
  set δ : ℝ := min (ε / 2) (1 / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  obtain ⟨C, hC1, hC⟩ := PrimeCarleson.Proof.Goal0.exists_card_divisors_le_rpow hδ0
  refine ⟨2 * C ^ 2, by positivity, fun Q hQ => ?_⟩
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  -- bound for each term
  have hterm : ∀ q ∈ Finset.Ioc (Q / 2) Q,
      (q.divisors.card : ℝ) * (Nat.totient q : ℝ) ^ (-σ) ≤
        2 * C ^ 2 * (Q : ℝ) ^ (δ + (δ - 1) * σ) := by
    intro q hq
    rw [Finset.mem_Ioc] at hq
    have hqpos : 0 < q := by omega
    have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
    have hqQ : (q : ℝ) ≤ Q := by exact_mod_cast hq.2
    have hQq : (Q : ℝ) / 2 ≤ q := by
      have h2 : Q < q * 2 := (Nat.div_lt_iff_lt_mul (by norm_num)).1 hq.1
      have : (Q : ℝ) < q * 2 := by exact_mod_cast h2
      linarith
    have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hqpos
    have h1 : (q.divisors.card : ℝ) ≤ C * (Q : ℝ) ^ δ :=
      (hC q hqpos).trans (by gcongr)
    have h2 : (Nat.totient q : ℝ) ^ (-σ) ≤ 2 * C * (Q : ℝ) ^ ((δ - 1) * σ) := by
      have hinv := PrimeCarleson.Proof.Goal0.inv_totient_le hδ0 hδ1 hC hqpos hQq hQR
      rw [Real.rpow_neg hφ.le, ← Real.inv_rpow hφ.le]
      calc ((Nat.totient q : ℝ)⁻¹) ^ σ ≤ (2 * C * (Q : ℝ) ^ (δ - 1)) ^ σ :=
            Real.rpow_le_rpow (by positivity) hinv hσ.le
        _ = (2 * C) ^ σ * (Q : ℝ) ^ ((δ - 1) * σ) := by
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hQ0.le]
        _ ≤ 2 * C * (Q : ℝ) ^ ((δ - 1) * σ) := by
            gcongr
            calc (2 * C) ^ σ ≤ (2 * C) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by linarith) hσ1
              _ = 2 * C := Real.rpow_one _
    calc (q.divisors.card : ℝ) * (Nat.totient q : ℝ) ^ (-σ)
        ≤ (C * (Q : ℝ) ^ δ) * (2 * C * (Q : ℝ) ^ ((δ - 1) * σ)) := by
          gcongr
      _ = 2 * C ^ 2 * (Q : ℝ) ^ (δ + (δ - 1) * σ) := by
          rw [Real.rpow_add hQ0]; ring
  have hcard : ((Finset.Ioc (Q / 2) Q).card : ℝ) ≤ Q := by
    rw [Nat.card_Ioc]
    exact_mod_cast Nat.sub_le _ _
  calc coefSum σ Q ≤ (Finset.Ioc (Q / 2) Q).card • (2 * C ^ 2 * (Q : ℝ) ^ (δ + (δ - 1) * σ)) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((Finset.Ioc (Q / 2) Q).card : ℝ) * (2 * C ^ 2 * (Q : ℝ) ^ (δ + (δ - 1) * σ)) := by
        rw [nsmul_eq_mul]
    _ ≤ (Q : ℝ) * (2 * C ^ 2 * (Q : ℝ) ^ (δ + (δ - 1) * σ)) := by gcongr
    _ = 2 * C ^ 2 * (Q : ℝ) ^ (1 + (δ + (δ - 1) * σ)) := by
        have : (Q : ℝ) ^ (1 + (δ + (δ - 1) * σ)) = Q * (Q : ℝ) ^ (δ + (δ - 1) * σ) := by
          rw [Real.rpow_add hQ0, Real.rpow_one]
        rw [this]; ring
    _ ≤ 2 * C ^ 2 * (Q : ℝ) ^ (1 - σ + ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQR
          (by nlinarith [mul_nonneg hδ0.le (sub_nonneg.2 hσ1)])) (by positivity)


/-! ### Part (4): the assembly -/

/-- The operator `T_I^Q(f,g)(x) = ∑_n K_I(n) w_Q(n) f(x-n) g(x+n)`, `I = [a, b]`. -/
noncomputable def opIQ (χ : ℝ → ℝ) (a b Q : ℕ) (f g : ℤ → ℂ) : ℤ → ℂ :=
  bilin (fun n : ℤ => ((kernelI χ a b (n : ℝ) : ℝ) : ℂ) * PrimeCarleson.Proof.Paper.wQ Q n) f g

lemma opIQ_eq_sum (χ : ℝ → ℝ) (a b Q : ℕ) {f g : ℤ → ℂ} (hf : (Function.support f).Finite) :
    opIQ χ a b Q f g = ∑ q ∈ Finset.Ioc (Q / 2) Q, coef q • ∑ d ∈ q.divisors,
      ((moebius (q / d) : ℤ) : ℂ) • stepOp d (progKernel χ a b d) f g := by
  funext x
  rw [opIQ, bilin_kernelI_wQ χ a b Q hf x]
  simp [Finset.sum_apply]

lemma norm_moebius_le_one (n : ℕ) : ‖((moebius n : ℤ) : ℂ)‖ ≤ 1 := by
  have := abs_moebius_le_one (n := n)
  rw [Complex.norm_intCast]
  exact_mod_cast this

lemma enorm_coef_rpow_le (q : ℕ) (hq : 0 < q) {σ : ℝ} (hσ : 0 < σ) :
    ‖coef q‖ₑ ^ σ ≤ ENNReal.ofReal ((Nat.totient q : ℝ) ^ (-σ)) := by
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq
  have h1 : ‖coef q‖ ≤ ((Nat.totient q : ℝ))⁻¹ := by
    have hμ : |((moebius q : ℤ) : ℝ)| ≤ 1 := by
      have := abs_moebius_le_one (n := q)
      exact_mod_cast this
    simp only [coef, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hφ]
    rw [div_le_iff₀ hφ, inv_mul_cancel₀ hφ.ne']
    exact hμ
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hσ.le]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.rpow_neg hφ.le, ← Real.inv_rpow hφ.le]
  exact Real.rpow_le_rpow (norm_nonneg _) h1 hσ.le

lemma coefSum_nonneg (σ : ℝ) (Q : ℕ) : 0 ≤ coefSum σ Q :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- **`e:progression`, coefficient-sum form** (blueprint N24, first inequality; CONDITIONAL on the
anchor X1): for `p, q, r > 0` with `1/r = 1/p + 1/q`, `σ = min r 1`, every `Q ≥ 1`, every
`I = [a, b]` with `1 ≤ a ≤ b` and all finitely supported `f, g`,
`‖T_I^Q(f,g)‖_{ℓ^r} ≤ C (∑_{Q/2<q≤Q} d_div(q) φ(q)^{-σ})^{1/σ} ‖f‖_p ‖g‖_q`. -/
theorem progression_coefSum_of_bhtSmooth {χ : ℝ → ℝ} {p q r C : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r) (hpqr : 1 / r = 1 / p + 1 / q) (hX : BHTSmooth χ p q r C) {a b : ℕ} (ha : 1 ≤ a)
    (hab : a ≤ b) (Q : ℕ) {f g : ℤ → ℂ} (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) :
    MeasureTheory.eLpNorm (opIQ χ a b Q f g) (ENNReal.ofReal r) MeasureTheory.Measure.count ≤
      ENNReal.ofReal (C * coefSum (min r 1) Q ^ (1 / min r 1)) *
        MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g (ENNReal.ofReal q) MeasureTheory.Measure.count := by
  set σ : ℝ := min r 1 with hσ
  have hσ0 : 0 < σ := lt_min hr one_pos
  set M : ℝ≥0∞ := ENNReal.ofReal C *
    MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count *
      MeasureTheory.eLpNorm g (ENNReal.ofReal q) MeasureTheory.Measure.count with hM
  have hstep : ∀ q' ∈ Finset.Ioc (Q / 2) Q, ∀ d ∈ q'.divisors,
      MeasureTheory.eLpNorm (stepOp d (progKernel χ a b d) f g) (ENNReal.ofReal r)
        MeasureTheory.Measure.count ≤ M := fun q' _ d hd =>
    eLpNorm_stepOp_kernelI_le_of_bhtSmooth hp hq hr hpqr hX ha hab
      (Nat.pos_of_mem_divisors hd) hf hg
  -- bound for the block of a fixed `q'`
  have hblock : ∀ q' ∈ Finset.Ioc (Q / 2) Q,
      MeasureTheory.eLpNorm (coef q' • ∑ d ∈ q'.divisors,
        ((moebius (q' / d) : ℤ) : ℂ) • stepOp d (progKernel χ a b d) f g)
        (ENNReal.ofReal r) MeasureTheory.Measure.count ^ σ ≤
      ENNReal.ofReal ((q'.divisors.card : ℝ) * (Nat.totient q' : ℝ) ^ (-σ)) * M ^ σ := by
    intro q' hq'
    have hq'pos : 0 < q' := by
      rw [Finset.mem_Ioc] at hq'; omega
    rw [MeasureTheory.eLpNorm_const_smul, ENNReal.mul_rpow_of_nonneg _ _ hσ0.le]
    have hin := eLpNorm_sum_rpow_le q'.divisors
      (fun d => ((moebius (q' / d) : ℤ) : ℂ) • stepOp d (progKernel χ a b d) f g) hr
    have hin2 : ∀ d ∈ q'.divisors,
        MeasureTheory.eLpNorm (((moebius (q' / d) : ℤ) : ℂ) • stepOp d (progKernel χ a b d) f g)
          (ENNReal.ofReal r) MeasureTheory.Measure.count ^ σ ≤ M ^ σ := by
      intro d hd
      rw [MeasureTheory.eLpNorm_const_smul]
      refine ENNReal.rpow_le_rpow ?_ hσ0.le
      have hμ : ‖((moebius (q' / d) : ℤ) : ℂ)‖ₑ ≤ 1 := by
        rw [← ofReal_norm]
        have := norm_moebius_le_one (q' / d)
        simpa using this
      calc _ ≤ 1 * MeasureTheory.eLpNorm (stepOp d (progKernel χ a b d) f g) (ENNReal.ofReal r)
              MeasureTheory.Measure.count := by gcongr
        _ ≤ 1 * M := by gcongr; exact hstep q' hq' d hd
        _ = M := one_mul _
    have hsum : MeasureTheory.eLpNorm (∑ d ∈ q'.divisors,
        ((moebius (q' / d) : ℤ) : ℂ) • stepOp d (progKernel χ a b d) f g) (ENNReal.ofReal r)
        MeasureTheory.Measure.count ^ σ ≤ (q'.divisors.card : ℝ≥0∞) * M ^ σ := by
      refine hin.trans ?_
      refine (Finset.sum_le_sum hin2).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    calc ‖coef q'‖ₑ ^ σ * _ ≤ ENNReal.ofReal ((Nat.totient q' : ℝ) ^ (-σ)) *
          ((q'.divisors.card : ℝ≥0∞) * M ^ σ) :=
          mul_le_mul (enorm_coef_rpow_le q' hq'pos hσ0) hsum zero_le zero_le
      _ = _ := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
          ring
  have hT : MeasureTheory.eLpNorm (opIQ χ a b Q f g) (ENNReal.ofReal r)
      MeasureTheory.Measure.count ^ σ ≤ ENNReal.ofReal (coefSum σ Q) * M ^ σ := by
    rw [opIQ_eq_sum χ a b Q hf]
    refine (eLpNorm_sum_rpow_le (Finset.Ioc (Q / 2) Q) _ hr).trans ?_
    refine (Finset.sum_le_sum hblock).trans ?_
    rw [← Finset.sum_mul, coefSum, ENNReal.ofReal_sum_of_nonneg]
    intro q' _
    exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hT2 := ENNReal.rpow_le_rpow hT (inv_nonneg.2 hσ0.le)
  rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hσ0.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hσ0.le), ← ENNReal.rpow_mul,
    mul_inv_cancel₀ hσ0.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg (coefSum_nonneg σ Q) (inv_nonneg.2 hσ0.le)] at hT2
  rw [ENNReal.ofReal_mul' (Real.rpow_nonneg (coefSum_nonneg σ Q) _), one_div]
  refine hT2.trans (le_of_eq ?_)
  rw [hM]
  ring


lemma one_div_min_sub_one {r : ℝ} (hr : 0 < r) : 1 / min r 1 - 1 = max (1 / r - 1) 0 := by
  rcases le_total r 1 with h | h
  · rw [min_eq_left h, max_eq_left]
    have : 1 ≤ 1 / r := by rw [le_div_iff₀ hr]; linarith
    linarith
  · rw [min_eq_right h, max_eq_right]
    · norm_num
    · have : 1 / r ≤ 1 := by rw [div_le_iff₀ hr]; linarith
      linarith

lemma opIQ_eq_zero_of_lt (χ : ℝ → ℝ) {a b : ℕ} (hab : b < a) (Q : ℕ) (f g : ℤ → ℂ) :
    opIQ χ a b Q f g = 0 := by
  funext x
  simp [opIQ, bilin, kernelI, Finset.Icc_eq_empty_of_lt hab]

/-- **`e:progression`** (blueprint N24; CONDITIONAL on the anchor X1 = `BHTSmooth`): for `p, q, r > 0`
with `1/r = 1/p + 1/q` and every `ε > 0` there is a constant `C'`, depending only on `(ε, C, p, q)`
(through `σ = min r 1`), such that for every `Q ≥ 1`, every interval `I = [a, b]` of positive integers
and all finitely supported `f, g`:
`‖T_I^Q(f,g)‖_{ℓ^r} ≤ C' Q^{max{1/r - 1, 0} + ε} ‖f‖_p ‖g‖_q`. -/
theorem progression_of_bhtSmooth {χ : ℝ → ℝ} {p q r C : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r) (hpqr : 1 / r = 1 / p + 1 / q) (hX : BHTSmooth χ p q r C) {ε : ℝ} (hε : 0 < ε) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ a b : ℕ, 1 ≤ a → ∀ f g : ℤ → ℂ,
      (Function.support f).Finite → (Function.support g).Finite →
      MeasureTheory.eLpNorm (opIQ χ a b Q f g) (ENNReal.ofReal r) MeasureTheory.Measure.count ≤
        ENNReal.ofReal (C' * (Q : ℝ) ^ (max (1 / r - 1) 0 + ε)) *
          MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count *
            MeasureTheory.eLpNorm g (ENNReal.ofReal q) MeasureTheory.Measure.count := by
  set σ : ℝ := min r 1 with hσ
  have hσ0 : 0 < σ := lt_min hr one_pos
  have hσ1 : σ ≤ 1 := min_le_right _ _
  obtain ⟨A, hA0, hA⟩ := exists_coefSum_le hσ0 hσ1 (ε := ε * σ) (by positivity)
  refine ⟨max C 0 * A ^ (1 / σ), by positivity, fun Q hQ a b ha f g hf hg => ?_⟩
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  by_cases hab : a ≤ b
  · have hexp : (1 - σ + ε * σ) * (1 / σ) = max (1 / r - 1) 0 + ε := by
      rw [← one_div_min_sub_one hr]
      field_simp
      ring
    have hS := Real.rpow_nonneg (coefSum_nonneg σ Q) (1 / σ)
    have hle : C * coefSum σ Q ^ (1 / σ) ≤
        max C 0 * A ^ (1 / σ) * (Q : ℝ) ^ (max (1 / r - 1) 0 + ε) := by
      calc C * coefSum σ Q ^ (1 / σ) ≤ max C 0 * coefSum σ Q ^ (1 / σ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hS
        _ ≤ max C 0 * (A * (Q : ℝ) ^ (1 - σ + ε * σ)) ^ (1 / σ) := by
            apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
            exact Real.rpow_le_rpow (coefSum_nonneg σ Q) (hA Q hQ) (by positivity)
        _ = max C 0 * A ^ (1 / σ) * (Q : ℝ) ^ (max (1 / r - 1) 0 + ε) := by
            rw [Real.mul_rpow hA0 (by positivity), ← Real.rpow_mul hQ0.le, hexp]
            ring
    refine (progression_coefSum_of_bhtSmooth hp hq hr hpqr hX ha hab Q hf hg).trans ?_
    have hle' := ENNReal.ofReal_le_ofReal hle
    gcongr
  · rw [opIQ_eq_zero_of_lt χ (not_le.1 hab)]
    simp

end PrimeBHT.Progression
