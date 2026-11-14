module

public import PrimeBHT.TimeFrequency.X2.Pint.SingleOp
public import PrimeBHT.TimeFrequency.X2.YVec
public import PrimeBHT.TimeFrequency.X2.ClassKernel
public import PrimeBHT.TimeFrequency.X2.CZ.Minkowski

/-!
# X2, V11 / TB-4 shared core, part 4: Theorem I — PROOF (corrected statement)

`docs/audits/X2-V11-TB4-plan.md` §4c.  **The Prop `TheoremI` of `SingleOp.lean` is FALSE as printed** (Bochner-integral
conventions): with `K x w = k(x)·1_{[0,1]}(w)`, `k(x) = (1+|x|)^{-1/2}` (bounded, in `L^{qX}` for `qX > 2`, not in `L²`), every
`x ↦ yNorm 2 (kernelOp K G x)^2` is non-integrable, so its Bochner integral is `0` and the Hilbert hypothesis holds with
`A = B₂ = 0`, while the conclusion's left side `∫ |k|^{qX}·yNorm s (∫_0^1 F)^{qX}` is positive and the right side is `0`.
Also `∫ ‖K x w‖ ≤ Cinf` is vacuous for non-integrable `K x`.  The corrected statement `theoremI` below uses lower Lebesgue
integrals (`∫⁻ … ofReal`) for the operator sides, the `L¹` bound in `∫⁻ ‖·‖ₑ` form and joint measurability of the kernels;
the Hilbert hypothesis is needed only for step functions with the SAME step sets.

Proof: `pointwise_interp` is the finite-dimensional heart (for `u = ∑ c_k v_k` and the power families `famF` (forward) and
`famG` (dual, of a norming vector)), `Φ(z) = bil (∑ c_k famF (v k) z) (famG g z)` and `exists_pointwisePJ`; then
`kernelOp K (stepFun E v) x = ∑_k (∫_{E k} K x) • v k`, Tonelli in `(x, t)`, and the Hilbert hypothesis for the step
function `stepFun E (famF (v ·) (1 + it))` (with `yNorm 2 = (yNorm s)^{qX/2}` pointwise).
-/

@[expose] public noncomputable section

open MeasureTheory Complex Complex.HadamardThreeLines
open scoped ENNReal ComplexConjugate
open PrimeBHT.Statements

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Pint

variable {P : ℕ} [NeZero P]

/-! ## The bilinear pairing -/

theorem bil_eq_yPair (a b : ZMod P → ℂ) : bil a b = yPair a (fun y => conj (b y)) := by
  simp [bil, yPair]

theorem yNorm_conj (p : ℝ) (b : ZMod P → ℂ) : yNorm p (fun y => conj (b y)) = yNorm p b := by
  simp [yNorm]

theorem norm_bil_le {p p' : ℝ} (h : p.HolderConjugate p') (a b : ZMod P → ℂ) :
    ‖bil a b‖ ≤ yNorm p' a * yNorm p b := by
  rw [bil_eq_yPair]
  exact (norm_yPair_le h a _).trans_eq (by rw [yNorm_conj])

/-! ## Elementary bounds -/

theorem rpow_le_add_of_mem_uIcc {x r r₀ r₁ : ℝ} (hx : 0 < x) (hr : r ∈ Set.uIcc r₀ r₁) :
    x ^ r ≤ x ^ r₀ + x ^ r₁ := by
  have key : ∀ {a b : ℝ}, a ≤ r → r ≤ b → x ^ r ≤ x ^ a + x ^ b := by
    intro a b ha hb
    rcases le_total 1 x with hx1 | hx1
    · exact (Real.rpow_le_rpow_of_exponent_le hx1 hb).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _))
    · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 ha).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg hx.le _))
  rcases Set.mem_uIcc.1 hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact key h1 h2
  · exact (key h1 h2).trans_eq (add_comm _ _)

theorem affine_mem_uIcc {a b r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) : a + b * r ∈ Set.uIcc a (a + b) := by
  obtain ⟨h0, h1⟩ := hr
  rcases le_total 0 b with hb | hb
  · exact Set.mem_uIcc.2 (Or.inl ⟨by nlinarith, by nlinarith⟩)
  · exact Set.mem_uIcc.2 (Or.inr ⟨by nlinarith, by nlinarith⟩)

theorem affine_pos {a b r : ℝ} (ha : 0 < a) (hab : 0 < a + b) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    0 < a + b * r := by
  obtain ⟨h0, h1⟩ := hr
  rcases eq_or_lt_of_le h1 with h | h
  · rw [h, mul_one]; exact hab
  · have := mul_pos (sub_pos.2 h) ha
    nlinarith [mul_nonneg h0 hab.le]

/-- A bound for the power family on the closed strip, uniform in `im z`. -/
theorem norm_famVec_le {s a b a' b' : ℝ} (hs : 0 < s) (ha : 0 < a) (hab : 0 < a + b) (v : ZMod P → ℂ)
    (y : ZMod P) {z : ℂ} (hz : z.re ∈ Set.Icc (0 : ℝ) 1) :
    ‖famVec s a b a' b' v z y‖ ≤
      (‖v y‖ ^ a + ‖v y‖ ^ (a + b)) * (yNorm s v ^ a' + yNorm s v ^ (a' + b')) := by
  rcases eq_or_lt_of_le (yNorm_nonneg s v) with h0 | hv
  · have hv0 : v = 0 := (yNorm_eq_zero_iff_of_pos hs v).1 h0.symm
    simp only [famVec_of_eq_zero s a b a' b' hv0, Pi.zero_apply, norm_zero]
    have := yNorm_nonneg s v
    positivity
  rw [norm_famVec_apply hv (affine_pos ha hab hz)]
  refine mul_le_mul ?_ (rpow_le_add_of_mem_uIcc hv (affine_mem_uIcc hz)) (by positivity) (by positivity)
  rcases eq_or_lt_of_le (norm_nonneg (v y)) with h1 | h1
  · rw [← h1, Real.zero_rpow (affine_pos ha hab hz).ne']; positivity
  · exact rpow_le_add_of_mem_uIcc h1 (affine_mem_uIcc hz)

theorem yNorm_famVec_le {s a b a' b' p : ℝ} (hp : 0 < p) (hs : 0 < s) (v : ZMod P → ℂ) {z : ℂ}
    (hz : 0 < a + b * z.re) (hps : (a + b * z.re) * p = s) :
    yNorm p (famVec s a b a' b' v z) ≤ yNorm s v ^ (s / p + a' + b' * z.re) := by
  rcases eq_or_lt_of_le (yNorm_nonneg s v) with h0 | hv
  · have hv0 : v = 0 := (yNorm_eq_zero_iff_of_pos hs v).1 h0.symm
    rw [famVec_of_eq_zero s a b a' b' hv0, yNorm_zero_of_pos hp]
    exact Real.rpow_nonneg (yNorm_nonneg s v) _
  exact (yNorm_famVec hp hs.ne' hv hz hps).le

theorem yNorm_famVec_eq {s a b a' b' p : ℝ} (hp : 0 < p) (hs : 0 < s) (v : ZMod P → ℂ) {z : ℂ}
    (hz : 0 < a + b * z.re) (hps : (a + b * z.re) * p = s) (he : s / p + a' + b' * z.re ≠ 0) :
    yNorm p (famVec s a b a' b' v z) = yNorm s v ^ (s / p + a' + b' * z.re) := by
  rcases eq_or_lt_of_le (yNorm_nonneg s v) with h0 | hv
  · have hv0 : v = 0 := (yNorm_eq_zero_iff_of_pos hs v).1 h0.symm
    rw [famVec_of_eq_zero s a b a' b' hv0, yNorm_zero_of_pos hp, ← h0, Real.zero_rpow he]
  exact yNorm_famVec hp hs.ne' hv hz hps

theorem yNorm_sum_le {s : ℝ} (hs : 1 ≤ s) {κ : Type*} (S : Finset κ) (w : κ → ZMod P → ℂ) :
    yNorm s (∑ k ∈ S, w k) ≤ ∑ k ∈ S, yNorm s (w k) :=
  Finset.le_sum_of_subadditive (yNorm s) (yNorm_zero_of_pos (by linarith)).le (CZ.yNorm_add_le hs) S w

theorem yNorm_smul' {s : ℝ} (hs : 0 < s) (c : ℂ) (w : ZMod P → ℂ) : yNorm s (c • w) = ‖c‖ * yNorm s w :=
  yNorm_fun_const_mul hs c w

/-- `‖∑ c_k w_k‖_p ≤ ∑ ‖c_k‖` if every `‖w_k‖_p ≤ 1`. -/
theorem yNorm_sum_smul_le {p : ℝ} (hp : 1 ≤ p) {κ : Type*} [Fintype κ] (c : κ → ℂ) (w : κ → ZMod P → ℂ)
    (hw : ∀ k, yNorm p (w k) ≤ 1) : yNorm p (∑ k, c k • w k) ≤ ∑ k, ‖c k‖ := by
  refine (yNorm_sum_le hp _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [yNorm_smul' (by linarith)]
  exact mul_le_of_le_one_right (norm_nonneg _) (hw k)

/-! ## The exponents and the two power families

`θ = 2/qX`, `r = s/s₀ = (qX - s)/(qX - 2)`, `s₀ = s/r`; dual `s' = s/(s-1)`, `r' = s'/s₀' = (s - r)/(s - 1)`. -/

/-- `s/s₀`. -/
def rF (s qX : ℝ) : ℝ := (qX - s) / (qX - 2)

/-- The conjugate exponent `s' = s/(s-1)`. -/
def sC (s : ℝ) : ℝ := s / (s - 1)

/-- `s'/s₀'`. -/
def rG (s qX : ℝ) : ℝ := (s - rF s qX) / (s - 1)

/-- The forward family: `yNorm (s/r) = 1` on `re z = 0`, `yNorm 2 = (yNorm s)^{qX/2}` on `re z = 1`, `= v` at `θ`. -/
def famF (s qX : ℝ) (v : ZMod P → ℂ) (z : ℂ) : ZMod P → ℂ :=
  famVec s (rF s qX) (s / 2 - rF s qX) (-rF s qX) ((qX - s) / 2 + rF s qX) v z

/-- The dual family (of a vector with `yNorm s' ≤ 1`): `yNorm s₀' ≤ 1` on `re z = 0`, `yNorm 2 ≤ 1` on `re z = 1`. -/
def famG (s qX : ℝ) (v : ZMod P → ℂ) (z : ℂ) : ZMod P → ℂ :=
  famVec (sC s) (rG s qX) (sC s / 2 - rG s qX) 0 0 v z

theorem holder_two : (2 : ℝ).HolderConjugate 2 := by
  have h := Real.holderConjugate_one_div (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h


section Exponents

variable {s qX : ℝ} (hE : 1 < s ∧ s < qX ∧ s / (s - 1) < qX)
include hE

theorem nhe_key : s < qX * (s - 1) := by
  obtain ⟨hs, -, hs'⟩ := hE
  rwa [div_lt_iff₀ (by linarith)] at hs'

theorem two_lt_qX : 2 < qX := by
  have hk := nhe_key hE
  obtain ⟨hs, hsq, -⟩ := hE
  by_contra hq
  push Not at hq
  nlinarith [mul_le_mul_of_nonneg_right hq (by linarith : (0 : ℝ) ≤ s - 1)]

theorem rF_pos : 0 < rF s qX := div_pos (by linarith [hE.2.1]) (by linarith [two_lt_qX hE])

theorem rF_lt : rF s qX < s := by
  have hk := nhe_key hE
  rw [rF, div_lt_iff₀ (by linarith [two_lt_qX hE])]
  nlinarith

theorem rG_pos : 0 < rG s qX := div_pos (by linarith [rF_lt hE]) (by linarith [hE.1])

theorem sC_pos : 0 < sC s := div_pos (by linarith [hE.1]) (by linarith [hE.1])

theorem holder_s : (sC s).HolderConjugate s :=
  ((Real.holderConjugate_iff_eq_conjExponent hE.1).2 rfl).symm

theorem holder_0 : (sC s / rG s qX).HolderConjugate (s / rF s qX) := by
  have hs1 : 0 < s - 1 := by linarith [hE.1]
  have hs0 : s ≠ 0 := by linarith [hE.1]
  have h := Real.holderConjugate_one_div (a := rG s qX / sC s) (b := rF s qX / s)
    (div_pos (rG_pos hE) (sC_pos hE)) (div_pos (rF_pos hE) (by linarith [hE.1])) (by
      rw [rG, sC]; field_simp; ring)
  rwa [one_div_div, one_div_div] at h

theorem famF_theta (v : ZMod P → ℂ) : famF s qX v ((2 / qX : ℝ) : ℂ) = v := by
  have hq : qX ≠ 0 := by linarith [two_lt_qX hE]
  have hq2 : qX - 2 ≠ 0 := by linarith [two_lt_qX hE]
  refine famVec_theta v ?_ ?_
  · have : rF s qX + (s / 2 - rF s qX) * (2 / qX) = 1 := by rw [rF]; field_simp; ring
    exact_mod_cast this
  · have : -rF s qX + ((qX - s) / 2 + rF s qX) * (2 / qX) = 0 := by rw [rF]; field_simp; ring
    exact_mod_cast this

theorem famG_theta (v : ZMod P → ℂ) : famG s qX v ((2 / qX : ℝ) : ℂ) = v := by
  have hq : qX ≠ 0 := by linarith [two_lt_qX hE]
  have hq2 : qX - 2 ≠ 0 := by linarith [two_lt_qX hE]
  have hs1 : s - 1 ≠ 0 := by linarith [hE.1]
  refine famVec_theta v ?_ (by simp)
  have : rG s qX + (sC s / 2 - rG s qX) * (2 / qX) = 1 := by rw [rG, rF, sC]; field_simp; ring
  exact_mod_cast this

/-- `‖famF v (it)‖_{s₀} ≤ 1`. -/
theorem yNorm_famF_zero (v : ZMod P → ℂ) (t : ℝ) :
    yNorm (s / rF s qX) (famF s qX v (t * I)) ≤ 1 := by
  have hs : 0 < s := by linarith [hE.1]
  have hr := rF_pos hE
  have hre : ((t : ℂ) * I).re = 0 := by simp
  have h := yNorm_famVec_le (a' := -rF s qX) (b' := (qX - s) / 2 + rF s qX) (div_pos hs hr) hs v
    (z := t * I) (a := rF s qX) (b := s / 2 - rF s qX) (by rw [hre, mul_zero, add_zero]; exact hr)
    (by rw [hre, mul_zero, add_zero]; field_simp)
  refine h.trans (le_of_eq ?_)
  rw [hre, mul_zero, add_zero, div_div_cancel₀ hs.ne', add_neg_cancel, Real.rpow_zero]

/-- `‖famF v (1+it)‖_2 = (yNorm s v)^{qX/2}`. -/
theorem yNorm_famF_one (v : ZMod P → ℂ) (t : ℝ) :
    yNorm 2 (famF s qX v (1 + t * I)) = yNorm s v ^ (qX / 2) := by
  have hs : 0 < s := by linarith [hE.1]
  have hre : (1 + (t : ℂ) * I).re = 1 := by simp
  have h := yNorm_famVec_eq (a' := -rF s qX) (b' := (qX - s) / 2 + rF s qX) two_pos hs v
    (z := 1 + t * I) (a := rF s qX) (b := s / 2 - rF s qX) (by rw [hre]; linarith)
    (by rw [hre]; ring) (by rw [hre]; linarith [two_lt_qX hE])
  rw [famF, h, hre]
  congr 1; ring

/-- `‖famG g (it)‖_{s₀'} ≤ 1` if `‖g‖_{s'} ≤ 1`. -/
theorem yNorm_famG_zero {g : ZMod P → ℂ} (hg : yNorm (sC s) g ≤ 1) (t : ℝ) :
    yNorm (sC s / rG s qX) (famG s qX g (t * I)) ≤ 1 := by
  have hc := sC_pos hE
  have hr := rG_pos hE
  have hz : ((t : ℂ) * I).re = 0 := by simp
  have h := yNorm_famVec_le (a' := 0) (b' := 0) (div_pos hc hr) hc g (z := t * I) (a := rG s qX)
    (b := sC s / 2 - rG s qX) (by rw [hz, mul_zero, add_zero]; exact hr)
    (by rw [hz, mul_zero, add_zero]; field_simp)
  refine h.trans (Real.rpow_le_one (yNorm_nonneg _ _) hg ?_)
  rw [hz, mul_zero, add_zero, add_zero, div_div_cancel₀ hc.ne']; exact hr.le

/-- `‖famG g (1+it)‖_2 ≤ 1` if `‖g‖_{s'} ≤ 1`. -/
theorem yNorm_famG_one {g : ZMod P → ℂ} (hg : yNorm (sC s) g ≤ 1) (t : ℝ) :
    yNorm 2 (famG s qX g (1 + t * I)) ≤ 1 := by
  have hc := sC_pos hE
  have hr := rG_pos hE
  have hz : (1 + (t : ℂ) * I).re = 1 := by simp
  have h := yNorm_famVec_le (a' := 0) (b' := 0) two_pos hc g (z := 1 + t * I) (a := rG s qX)
    (b := sC s / 2 - rG s qX) (by rw [hz]; linarith) (by rw [hz]; ring)
  refine h.trans (Real.rpow_le_one (yNorm_nonneg _ _) hg ?_)
  rw [hz]; linarith

end Exponents


/-! ## The pointwise interpolation inequality (finite-dimensional heart of Theorem I) -/

/-- The Poisson-Jensen property of `ν₁` at `θ` (the conclusion of `exists_pointwisePJ`). -/
def PJProp (θ : ℝ) (ν₁ : Measure ℝ) : Prop :=
  ∀ (G : ℂ → ℂ), DiffContOnCl ℂ G (verticalStrip 0 1) →
    BddAbove ((fun z => ‖G z‖) '' verticalClosedStrip 0 1) →
    ∀ {M₀ : ℝ}, 0 ≤ M₀ → (∀ t : ℝ, ‖G (t * I)‖ ≤ M₀) →
      ‖G θ‖ₑ ^ (2 / θ) ≤ ENNReal.ofReal (M₀ ^ (2 / θ - 2)) * ∫⁻ t, ‖G (1 + t * I)‖ₑ ^ (2 : ℝ) ∂ν₁

/-- **Pointwise interpolation**: for `u = ∑ c_k v_k`,
`‖u‖_s^{qX} ≤ (∑‖c_k‖)^{qX-2} ∫ ‖∑ c_k famF (v k) (1+it)‖_2² dν₁(t)`. -/
theorem pointwise_interp {s qX : ℝ} (hE : 1 < s ∧ s < qX ∧ s / (s - 1) < qX) {ν₁ : Measure ℝ}
    (hν : PJProp (2 / qX) ν₁) {κ : Type*} [Fintype κ] (c : κ → ℂ) (v : κ → ZMod P → ℂ) :
    ENNReal.ofReal (yNorm s (∑ k, c k • v k) ^ qX) ≤
      ENNReal.ofReal ((∑ k, ‖c k‖) ^ (qX - 2)) *
        ∫⁻ t, ENNReal.ofReal (yNorm 2 (∑ k, c k • famF s qX (v k) (1 + t * I)) ^ 2) ∂ν₁ := by
  have hq2 := two_lt_qX hE
  have hs : 0 < s := by linarith [hE.1]
  have hrF := rF_pos hE
  have hrG := rG_pos hE
  have hsC := sC_pos hE
  set u := ∑ k, c k • v k with hu
  obtain ⟨h, hh1, hh2⟩ := exists_norming (holder_s hE) u
  set g : ZMod P → ℂ := fun y => conj (h y) with hg
  have hg1 : yNorm (sC s) g ≤ 1 := by rw [hg, yNorm_conj]; exact hh1
  set Φ : ℂ → ℂ := fun z =>
    (P : ℂ)⁻¹ * ∑ y, (∑ k, c k * famF s qX (v k) z y) * famG s qX g z y with hΦ
  have hΦbil : ∀ z, Φ z = bil (∑ k, c k • famF s qX (v k) z) (famG s qX g z) := by
    intro z; simp [hΦ, bil, Finset.sum_apply]
  have hdF : ∀ k y, Differentiable ℂ (fun z => famF s qX (v k) z y) :=
    fun k y => differentiable_famVec _ _ _ _ _ _ y
  have hdG : ∀ y, Differentiable ℂ (fun z => famG s qX g z y) :=
    fun y => differentiable_famVec _ _ _ _ _ _ y
  have hdiff : Differentiable ℂ Φ := by
    simp only [hΦ]
    fun_prop
  -- uniform bounds on the closed strip
  have habF : 0 < rF s qX + (s / 2 - rF s qX) := by linarith
  have habG : 0 < rG s qX + (sC s / 2 - rG s qX) := by linarith
  have hF := fun k y {z : ℂ} (hz : z.re ∈ Set.Icc (0 : ℝ) 1) =>
    norm_famVec_le (a' := -rF s qX) (b' := (qX - s) / 2 + rF s qX) hs hrF habF (v k) y hz
  have hG := fun y {z : ℂ} (hz : z.re ∈ Set.Icc (0 : ℝ) 1) =>
    norm_famVec_le (a' := 0) (b' := 0) hsC hrG habG g y hz
  have h0 : ((0 : ℂ)).re ∈ Set.Icc (0 : ℝ) 1 := by simp
  have hbd : BddAbove ((fun z => ‖Φ z‖) '' verticalClosedStrip 0 1) := by
    refine ⟨‖(P : ℂ)⁻¹‖ * ∑ y, (∑ k, ‖c k‖ * ((‖v k y‖ ^ rF s qX + ‖v k y‖ ^ (rF s qX + (s / 2 - rF s qX))) *
      (yNorm s (v k) ^ (-rF s qX) + yNorm s (v k) ^ (-rF s qX + ((qX - s) / 2 + rF s qX))))) *
      ((‖g y‖ ^ rG s qX + ‖g y‖ ^ (rG s qX + (sC s / 2 - rG s qX))) *
        (yNorm (sC s) g ^ (0 : ℝ) + yNorm (sC s) g ^ ((0 : ℝ) + 0))), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z.re ∈ Set.Icc (0 : ℝ) 1 := hz
    show ‖Φ z‖ ≤ _
    simp only [hΦ, norm_mul]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_))
      (norm_nonneg _)
    rw [norm_mul]
    refine mul_le_mul ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)) (hG y hz') (norm_nonneg _)
      (Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (hF k y h0)))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hF k y hz') (norm_nonneg _)
  -- the two endpoints
  have hp1 : 1 ≤ s / rF s qX := by rw [le_div_iff₀ hrF]; linarith [rF_lt hE]
  have hM0 : 0 ≤ ∑ k, ‖c k‖ := Finset.sum_nonneg fun k _ => norm_nonneg _
  have hit : ∀ t : ℝ, ‖Φ (t * I)‖ ≤ ∑ k, ‖c k‖ := by
    intro t
    rw [hΦbil]
    refine (norm_bil_le (holder_0 hE) _ _).trans ?_
    refine (mul_le_mul (yNorm_sum_smul_le hp1 c _ fun k => yNorm_famF_zero hE (v k) t)
      (yNorm_famG_zero hE hg1 t) (yNorm_nonneg _ _) hM0).trans_eq (mul_one _)
  have h1t : ∀ t : ℝ, ‖Φ (1 + t * I)‖ ≤ yNorm 2 (∑ k, c k • famF s qX (v k) (1 + t * I)) := by
    intro t
    rw [hΦbil]
    refine (norm_bil_le holder_two _ _).trans ?_
    exact (mul_le_of_le_one_right (yNorm_nonneg _ _) (yNorm_famG_one hE hg1 t))
  have hθ : Φ ((2 / qX : ℝ) : ℂ) = yPair u h := by
    rw [hΦbil]
    simp only [famF_theta hE, famG_theta hE, bil_eq_yPair, hg, Complex.conj_conj, hu]
  have hPJ := hν Φ hdiff.diffContOnCl hbd hM0 hit
  have hqq : 2 / (2 / qX) = qX := by field_simp
  rw [hqq] at hPJ
  have hq0 : (0 : ℝ) ≤ qX := by linarith
  have hu0 : yNorm s u ≤ ‖Φ ((2 / qX : ℝ) : ℂ)‖ := by
    rw [hθ]; exact hh2.trans (Complex.re_le_norm _)
  calc ENNReal.ofReal (yNorm s u ^ qX) = ENNReal.ofReal (yNorm s u) ^ qX :=
        (ENNReal.ofReal_rpow_of_nonneg (yNorm_nonneg _ _) hq0).symm
    _ ≤ ‖Φ ((2 / qX : ℝ) : ℂ)‖ₑ ^ qX := by
        refine ENNReal.rpow_le_rpow ?_ hq0
        rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hu0
    _ ≤ _ := hPJ
    _ ≤ _ := by
        gcongr with t
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.rpow_two]
        exact pow_le_pow_left₀ (norm_nonneg _) (h1t t) 2

/-! ## Step functions and kernel operators -/

omit [NeZero P] in
theorem stepFun_eq_of_mem {κ : Type*} [Fintype κ] {E : κ → Set ℝ}
    (hd : Pairwise fun k k' => Disjoint (E k) (E k')) (v : κ → ZMod P → ℂ) {w : ℝ} {k : κ} (hw : w ∈ E k) :
    stepFun E v w = v k := by
  funext y
  simp only [stepFun]
  rw [Finset.sum_eq_single k]
  · simp [hw]
  · intro j _ hj
    have : w ∉ E j := fun h => Set.disjoint_left.1 (hd hj) h hw
    simp [this]
  · simp

omit [NeZero P] in
theorem stepFun_eq_zero {κ : Type*} [Fintype κ] {E : κ → Set ℝ} (v : κ → ZMod P → ℂ) {w : ℝ}
    (hw : ∀ k, w ∉ E k) : stepFun E v w = 0 := by
  funext y; simp [stepFun, hw]

theorem yNorm_stepFun_famF {s qX : ℝ} (hE : 1 < s ∧ s < qX ∧ s / (s - 1) < qX) {κ : Type*} [Fintype κ]
    {E : κ → Set ℝ} (hd : Pairwise fun k k' => Disjoint (E k) (E k')) (v : κ → ZMod P → ℂ) (t w : ℝ) :
    yNorm 2 (stepFun E (fun k => famF s qX (v k) (1 + t * I)) w) = yNorm s (stepFun E v w) ^ (qX / 2) := by
  by_cases h : ∃ k, w ∈ E k
  · obtain ⟨k, hk⟩ := h
    rw [stepFun_eq_of_mem hd _ hk, stepFun_eq_of_mem hd _ hk]
    exact yNorm_famF_one hE (v k) t
  · push Not at h
    rw [stepFun_eq_zero _ h, stepFun_eq_zero _ h, yNorm_zero_of_pos two_pos,
      yNorm_zero_of_pos (by linarith [hE.1]), Real.zero_rpow (div_pos (by linarith [two_lt_qX hE]) two_pos).ne']

omit [NeZero P] in
/-- A kernel operator applied to a step function. -/
theorem kernelOp_stepFun {K : ℝ → ℝ → ℂ} {x : ℝ} (hK : Integrable (K x)) {κ : Type*} [Fintype κ]
    {E : κ → Set ℝ} (hE : ∀ k, MeasurableSet (E k)) (v : κ → ZMod P → ℂ) :
    kernelOp K (stepFun E v) x = ∑ k, (∫ w, (E k).indicator (K x) w) • v k := by
  funext y
  simp only [kernelOp, stepFun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum _ fun k _ => ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_mul_const]
    congr 1; funext w
    by_cases hw : w ∈ E k <;> simp [hw]
  · exact ((hK.indicator (hE k)).mul_const (v k y)).congr
      (ae_of_all _ fun w => by by_cases hw : w ∈ E k <;> simp [hw])

/-- The coefficients of a kernel operator on a step function: `∑_k ‖∫_{E k} K x‖ ≤ ∫ ‖K x‖`. -/
theorem sum_norm_coeff_le {K : ℝ → ℝ → ℂ} {x Cinf : ℝ} (hCinf : 0 ≤ Cinf)
    (hKb : ∫⁻ w, ‖K x w‖ₑ ≤ ENNReal.ofReal Cinf) {κ : Type*} [Fintype κ] {E : κ → Set ℝ} (hE : IsStepData E) :
    ∑ k, ‖∫ w, (E k).indicator (K x) w‖ ≤ Cinf := by
  rw [← ENNReal.ofReal_le_ofReal_iff hCinf, ENNReal.ofReal_sum_of_nonneg (fun k _ => norm_nonneg _)]
  calc ∑ k, ENNReal.ofReal ‖∫ w, (E k).indicator (K x) w‖ ≤ ∑ k, ∫⁻ w in E k, ‖K x w‖ₑ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [ofReal_norm, ← lintegral_indicator (hE.1 k)]
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        congr 1; funext w; by_cases hw : w ∈ E k <;> simp [hw]
    _ = ∫⁻ w in ⋃ k, E k, ‖K x w‖ₑ := by rw [lintegral_iUnion hE.1 hE.2.2, tsum_fintype]
    _ ≤ ∫⁻ w, ‖K x w‖ₑ := setLIntegral_le_lintegral _ _
    _ ≤ _ := hKb

/-! ## Theorem I -/

/-- **Theorem I (corrected statement, PROVED)**: interpolation for a finite family of `L¹`-kernel operators between the
pointwise `L^∞(L^{s₀})` bound and the Hilbert endpoint in HLC's intersection form, for step functions.
Replaces the false Prop `TheoremI` of `SingleOp.lean` (Bochner conventions; see the module docstring). -/
theorem theoremI {ι κ : Type*} [Fintype ι] [Fintype κ] {K : ι → ℝ → ℝ → ℂ} {Cinf A B₂ s qX : ℝ}
    (hE : 1 < s ∧ s < qX ∧ s / (s - 1) < qX) (hCinf : 0 ≤ Cinf)
    (hKm : ∀ i, StronglyMeasurable (Function.uncurry (K i)))
    (hK : ∀ i x, ∫⁻ w, ‖K i x w‖ₑ ≤ ENNReal.ofReal Cinf)
    (hH : ∀ (v : κ → ZMod P → ℂ) (E : κ → Set ℝ), IsStepData E → ∀ B₀ : ℝ,
      (∀ w, yNorm 2 (stepFun E v w) ≤ B₀) →
      ∑ i, ∫⁻ x, ENNReal.ofReal (yNorm 2 (kernelOp (K i) (stepFun E v) x) ^ 2) ≤
        ENNReal.ofReal ((A * B₀ + B₂ * (∫ x, yNorm 2 (stepFun E v x) ^ 2) ^ ((1 : ℝ) / 2)) ^ 2))
    (E : κ → Set ℝ) (v : κ → ZMod P → ℂ) (hEd : IsStepData E) (B : ℝ)
    (hB : ∀ w, yNorm s (stepFun E v w) ≤ B) :
    ∑ i, ∫⁻ x, ENNReal.ofReal (yNorm s (kernelOp (K i) (stepFun E v) x) ^ qX) ≤
      ENNReal.ofReal (Cinf ^ (qX - 2)) *
        ENNReal.ofReal ((A * B ^ (qX / 2) + B₂ * (∫ x, yNorm s (stepFun E v x) ^ qX) ^ ((1 : ℝ) / 2)) ^ 2) := by
  have hq2 := two_lt_qX hE
  obtain ⟨ν₁, hν₁, hν⟩ := exists_pointwisePJ (θ := 2 / qX)
    ⟨by positivity, by rw [div_lt_one (by linarith)]; linarith⟩
  have hKx : ∀ i x, Integrable (K i x) := fun i x =>
    ⟨((hKm i).comp_measurable measurable_prodMk_left).aestronglyMeasurable,
      (hK i x).trans_lt ENNReal.ofReal_lt_top⟩
  set c : ι → ℝ → κ → ℂ := fun i x k => ∫ w, (E k).indicator (K i x) w with hc
  have hrep : ∀ i x (v' : κ → ZMod P → ℂ), kernelOp (K i) (stepFun E v') x = ∑ k, c i x k • v' k :=
    fun i x v' => kernelOp_stepFun (hKx i x) hEd.1 v'
  have hcm : ∀ i k, Measurable (fun x => c i x k) := by
    intro i k
    have h1 : (Function.uncurry fun x w => (E k).indicator (K i x) w) =
        (Prod.snd ⁻¹' E k).indicator (Function.uncurry (K i)) := by
      funext p
      show (E k).indicator (K i p.1) p.2 = (Prod.snd ⁻¹' E k).indicator (Function.uncurry (K i)) p
      by_cases hp : p.2 ∈ E k
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show p ∈ Prod.snd ⁻¹' E k from hp)]; rfl
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (show p ∉ Prod.snd ⁻¹' E k from hp)]
    have h2 : StronglyMeasurable (Function.uncurry fun x w => (E k).indicator (K i x) w) := by
      rw [h1]; exact (hKm i).indicator (measurable_snd (hEd.1 k))
    exact (h2.integral_prod_right (ν := volume)).measurable
  have hcb : ∀ i x, ∑ k, ‖c i x k‖ ≤ Cinf := fun i x => sum_norm_coeff_le hCinf (hK i x) hEd
  set G : ℝ → κ → ZMod P → ℂ := fun t k => famF s qX (v k) (1 + t * I) with hG
  set f : ι → ℝ → ℝ → ℝ≥0∞ := fun i x t =>
    ENNReal.ofReal (yNorm 2 (kernelOp (K i) (stepFun E (G t)) x) ^ 2) with hf
  have hfm : ∀ i, Measurable (Function.uncurry (f i)) := by
    intro i
    have h1 : Function.uncurry (f i) =
        fun p : ℝ × ℝ => ENNReal.ofReal (yNorm 2 (∑ k, c i p.1 k • G p.2 k) ^ 2) := by
      funext p; simp only [Function.uncurry, hf, hrep]
    rw [h1]
    refine ENNReal.measurable_ofReal.comp (((measurable_yNorm_fun 2).comp ?_).pow_const 2)
    refine measurable_pi_iff.2 fun y => ?_
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.measurable_sum _ fun k _ => ((hcm i k).comp measurable_fst).mul ?_
    have hcont : Continuous fun t : ℝ => famF s qX (v k) (1 + t * I) y :=
      (differentiable_famVec _ _ _ _ _ _ y).continuous.comp (by fun_prop)
    exact hcont.measurable.comp measurable_snd
  have hpt : ∀ i x, ENNReal.ofReal (yNorm s (kernelOp (K i) (stepFun E v) x) ^ qX) ≤
      ENNReal.ofReal (Cinf ^ (qX - 2)) * ∫⁻ t, f i x t ∂ν₁ := by
    intro i x
    rw [hrep]
    refine (pointwise_interp hE hν (c i x) v).trans ?_
    gcongr ?_ * ?_
    · exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (Finset.sum_nonneg fun k _ => norm_nonneg _)
        (hcb i x) (by linarith))
    · refine le_of_eq (lintegral_congr fun t => ?_)
      simp only [hf, hrep, hG]
  have hH' : ∀ t, ∑ i, ∫⁻ x, f i x t ≤ ENNReal.ofReal ((A * B ^ (qX / 2) +
      B₂ * (∫ x, yNorm s (stepFun E v x) ^ qX) ^ ((1 : ℝ) / 2)) ^ 2) := by
    intro t
    have hpt2 : ∀ w, yNorm 2 (stepFun E (G t) w) = yNorm s (stepFun E v w) ^ (qX / 2) :=
      yNorm_stepFun_famF hE hEd.2.2 v t
    have hInt : ∫ x, yNorm 2 (stepFun E (G t) x) ^ 2 = ∫ x, yNorm s (stepFun E v x) ^ qX := by
      congr 1; funext x
      rw [hpt2, ← Real.rpow_natCast, ← Real.rpow_mul (yNorm_nonneg _ _)]
      congr 1; push_cast; ring
    have := hH (G t) E hEd (B ^ (qX / 2)) (fun w => by
      rw [hpt2]; exact Real.rpow_le_rpow (yNorm_nonneg _ _) (hB w) (by linarith))
    rwa [hInt] at this
  calc ∑ i, ∫⁻ x, ENNReal.ofReal (yNorm s (kernelOp (K i) (stepFun E v) x) ^ qX)
      ≤ ∑ i, ∫⁻ x, ENNReal.ofReal (Cinf ^ (qX - 2)) * ∫⁻ t, f i x t ∂ν₁ :=
        Finset.sum_le_sum fun i _ => lintegral_mono fun x => hpt i x
    _ = ENNReal.ofReal (Cinf ^ (qX - 2)) * ∑ i, ∫⁻ x, ∫⁻ t, f i x t ∂ν₁ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Cinf ^ (qX - 2)) * ∑ i, ∫⁻ t, (∫⁻ x, f i x t) ∂ν₁ := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => lintegral_lintegral_swap (μ := volume) (ν := ν₁) (hfm i).aemeasurable
    _ = ENNReal.ofReal (Cinf ^ (qX - 2)) * ∫⁻ t, (∑ i, ∫⁻ x, f i x t) ∂ν₁ := by
        rw [lintegral_finsetSum (μ := ν₁) Finset.univ (f := fun i t => ∫⁻ x, f i x t)
          fun i _ => (hfm i).lintegral_prod_left']
    _ ≤ ENNReal.ofReal (Cinf ^ (qX - 2)) * ∫⁻ _, ENNReal.ofReal ((A * B ^ (qX / 2) +
          B₂ * (∫ x, yNorm s (stepFun E v x) ^ qX) ^ ((1 : ℝ) / 2)) ^ 2) ∂ν₁ := by
        gcongr with t
        exact hH' t
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

end PrimeBHT.TimeFrequency.X2.Pint
