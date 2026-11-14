module

public import PrimeCarleson.Frozen.Exp
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Data.Finsupp.Basic

/-!
# N42 (42a) / N41(a): the chart pieces `h_A` (partial)

For a finitely supported `h : ℤ → ℂ`, `ĥ(α) = ∑_n h(n) e(-nα)` (`seqFourier`). For a smooth
compactly supported `χ` and `A ∈ Y_N` (representative `A.val ∈ {0, …, N-1}`),
`φ_A(α) = χ(Nα) ĥ(α + A/N)` (`chartCoeffHat`) is smooth and compactly supported, hence Schwartz,
and `h_A := 𝓕⁻ φ_A` (`chartPiece`) is Schwartz with `ĥ_A = φ_A` (`fourier_chartPiece`).

`chartPiece_mul_e`: `h_A(n) e(An/N) = ∫ χ(Nβ - A) ĥ(β) e(nβ) dβ` (blueprint N41 proof step 1,
first display). The summation over `A` (the periodization to `∑_j χ(Nβ - j)`) is not done here.
-/

@[expose] public noncomputable section

namespace PrimeBHT.TransferenceAssembly

open MeasureTheory PrimeCarleson
open scoped FourierTransform SchwartzMap Real ContDiff

/-- `ĥ(α) = ∑_n h(n) e(-nα)`. -/
def seqFourier (h : ℤ →₀ ℂ) (α : ℝ) : ℂ := ∑ n ∈ h.support, h n * e (-(n * α))

theorem contDiff_e : ContDiff ℝ ∞ e :=
  Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

theorem contDiff_seqFourier (h : ℤ →₀ ℂ) : ContDiff ℝ ∞ (seqFourier h) := by
  unfold seqFourier
  refine ContDiff.sum fun n _ => contDiff_const.mul (contDiff_e.comp ?_)
  fun_prop

/-- `φ_A(α) = χ(Nα) ĥ(α + A/N)`. -/
def chartCoeffHat (χ : ℝ → ℂ) (N : ℕ) (h : ℤ →₀ ℂ) (A : ZMod N) (α : ℝ) : ℂ :=
  χ (N * α) * seqFourier h (α + A.val / N)

variable {χ : ℝ → ℂ} {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem contDiff_chartCoeffHat (hχ : ContDiff ℝ ∞ χ) (h : ℤ →₀ ℂ) (A : ZMod N) :
    ContDiff ℝ ∞ (chartCoeffHat χ N h A) := by
  unfold chartCoeffHat
  exact (hχ.comp (by fun_prop)).mul ((contDiff_seqFourier h).comp (by fun_prop))

theorem hasCompactSupport_chartCoeffHat (hχc : HasCompactSupport χ) (h : ℤ →₀ ℂ) (A : ZMod N) :
    HasCompactSupport (chartCoeffHat χ N h A) := by
  unfold chartCoeffHat
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have : HasCompactSupport fun α : ℝ => χ (N * α) := by
    simpa [smul_eq_mul] using hχc.comp_smul hN
  exact this.mul_right

/-- `φ_A` as a Schwartz function. -/
def chartCoeffHatSchwartz (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (h : ℤ →₀ ℂ)
    (A : ZMod N) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_chartCoeffHat hχc h A).toSchwartzMap (contDiff_chartCoeffHat hχ h A)

/-- The chart piece `h_A = 𝓕⁻ φ_A`, a Schwartz function. -/
def chartPiece (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (h : ℤ →₀ ℂ)
    (A : ZMod N) : 𝓢(ℝ, ℂ) :=
  𝓕⁻ (chartCoeffHatSchwartz hχ hχc h A)

/-- Fourier side: `ĥ_A(α) = χ(Nα) ĥ(α + A/N)`. -/
theorem fourier_chartPiece (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (h : ℤ →₀ ℂ)
    (A : ZMod N) : 𝓕 (⇑(chartPiece hχ hχc h A)) = chartCoeffHat χ N h A := by
  rw [← SchwartzMap.fourier_coe, chartPiece, FourierInvPair.fourier_fourierInv_eq]
  rfl

/-- `h_A(x) = ∫ χ(Nα) ĥ(α + A/N) e(xα) dα`. -/
theorem chartPiece_apply (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (h : ℤ →₀ ℂ)
    (A : ZMod N) (x : ℝ) :
    chartPiece hχ hχc h A x = ∫ α, chartCoeffHat χ N h A α * e (x * α) := by
  rw [chartPiece, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
  simp only [smul_eq_mul, e, RCLike.inner_apply, conj_trivial]
  rw [mul_comm]
  congr 2
  push_cast
  ring

theorem e_add (s t : ℝ) : e (s + t) = e s * e t := by
  unfold e; rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- N41 step 1: `h_A(x) e(Ax/N) = ∫ χ(Nβ - A) ĥ(β) e(xβ) dβ` (substitution `β = α + A/N`). -/
theorem chartPiece_mul_e (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (h : ℤ →₀ ℂ)
    (A : ZMod N) (x : ℝ) :
    chartPiece hχ hχc h A x * e (A.val * x / N) =
      ∫ β, χ (N * β - A.val) * seqFourier h β * e (x * β) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  rw [chartPiece_apply, ← integral_mul_const,
    ← integral_add_right_eq_self (fun β => χ (N * β - A.val) * seqFourier h β * e (x * β))
      ((A.val : ℝ) / N)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
  simp only [chartCoeffHat]
  have h1 : (N : ℝ) * (α + A.val / N) - A.val = N * α := by field_simp; ring
  have h2 : x * (α + A.val / N) = x * α + A.val * x / N := by ring
  rw [h1, h2, e_add]
  ring

/-- The periodized symbol `∑_j χ(Nβ - j)` of `P_{ι,N}`. -/
def chartSymbol (χ : ℝ → ℂ) (N : ℕ) (β : ℝ) : ℂ := ∑' j : ℤ, χ (N * β - j)

/-- `P_{ι,N} h (n) = ∫_0^1 (∑_j χ(Nβ - j)) ĥ(β) e(nβ) dβ`: the Fourier multiplier on `𝕋` with the
symbol `chartSymbol χ N`. -/
def chartProj (χ : ℝ → ℂ) (N : ℕ) (h : ℤ →₀ ℂ) (n : ℤ) : ℂ :=
  ∫ β in (0 : ℝ)..1, chartSymbol χ N β * seqFourier h β * e (n * β)

theorem e_intCast (k : ℤ) : e k = 1 := by
  unfold e
  have : (2 * (π : ℂ) * Complex.I * (k : ℝ)) = k * (2 * π * Complex.I) := by push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

theorem seqFourier_add_intCast (h : ℤ →₀ ℂ) (x : ℝ) (m : ℤ) :
    seqFourier h (x + m) = seqFourier h x := by
  unfold seqFourier
  refine Finset.sum_congr rfl fun k _ => ?_
  have : -((k : ℝ) * (x + m)) = -(k * x) + ((-(k * m) : ℤ) : ℝ) := by push_cast; ring
  rw [this, e_add, e_intCast, mul_one]

/-- The bijection `Y_N × ℤ → ℤ`, `(A, m) ↦ A - N m`. -/
def chartEquiv (N : ℕ) [NeZero N] : ZMod N × ℤ ≃ ℤ where
  toFun p := (p.1.val : ℤ) - N * p.2
  invFun j := ((j : ZMod N), -(j / N))
  left_inv p := by
    obtain ⟨A, m⟩ := p
    have hN : (N : ℤ) ≠ 0 := Int.natCast_ne_zero.2 (NeZero.ne N)
    have hdiv : ((A.val : ℤ) + (N : ℤ) * (-m)) / N = -m := by
      rw [Int.add_mul_ediv_left _ _ hN, Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _)
        (Int.ofNat_lt.2 (ZMod.val_lt A)), zero_add]
    refine Prod.ext ?_ ?_
    · simp
    · simp only
      rw [sub_eq_add_neg, ← mul_neg, hdiv, neg_neg]
  right_inv j := by
    simp only
    rw [ZMod.val_intCast, mul_neg, sub_neg_eq_add, add_comm]
    exact Int.mul_ediv_add_emod j N

theorem exists_bound_of_hasCompactSupport (hχc : HasCompactSupport χ) :
    ∃ R : ℝ, ∀ t, χ t ≠ 0 → |t| ≤ R := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hχc.isCompact.isBounded
  refine ⟨R, fun t ht => ?_⟩
  have := hR (subset_tsupport _ ht)
  simpa [Real.dist_eq] using this

/-- **(42a) / N41(a): the chart decomposition.**
`P_{ι,N} h (n) = ∑_{A ∈ Y_N} h_A(n) e(An/N)`. -/
theorem chartProj_eq_sum (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (h : ℤ →₀ ℂ)
    (n : ℤ) :
    chartProj χ N h n = ∑ A : ZMod N, chartPiece hχ hχc h A n * e (A.val * n / N) := by
  classical
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set g : ℝ → ℂ := fun β => seqFourier h β * e (n * β) with hg_def
  have hg_cont : Continuous g :=
    (contDiff_seqFourier h).continuous.mul (contDiff_e.continuous.comp (by fun_prop))
  have hg_per : ∀ (x : ℝ) (m : ℤ), g (x + m) = g x := by
    intro x m
    simp only [hg_def, seqFourier_add_intCast]
    have : (n : ℝ) * (x + m) = n * x + ((n * m : ℤ) : ℝ) := by push_cast; ring
    rw [this, e_add, e_intCast, mul_one]
  have hχcont : Continuous χ := hχ.continuous
  obtain ⟨R, hR⟩ := exists_bound_of_hasCompactSupport hχc
  let J : Finset ℤ := Finset.Icc (-⌈R⌉) (N + ⌈R⌉)
  have hJ : ∀ x ∈ Set.uIcc (0 : ℝ) 1, ∀ j ∉ J, χ (N * x - j) = 0 := by
    intro x hx j hj
    by_contra hne
    have hb := abs_le.1 (hR _ hne)
    rw [Set.uIcc_of_le zero_le_one] at hx
    have h0 : 0 ≤ (N : ℝ) * x := mul_nonneg hN.le hx.1
    have h1 : (N : ℝ) * x ≤ N := by nlinarith [hx.2]
    have hc := Int.le_ceil R
    apply hj
    rw [Finset.mem_Icc]
    constructor
    · have : ((-⌈R⌉ : ℤ) : ℝ) ≤ j := by push_cast; linarith
      exact_mod_cast this
    · have : (j : ℝ) ≤ ((N + ⌈R⌉ : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  let b : ℤ → ℂ := fun j => ∫ x in (0 : ℝ)..1, χ (N * x - j) * g x
  have hbJ : ∀ j ∉ J, b j = 0 := by
    intro j hj
    simp only [b]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun x hx => by
      simp only [hJ x hx j hj, zero_mul]]
    simp
  -- the right side as a finite sum
  have hRHS : chartProj χ N h n = ∑ j ∈ J, b j := by
    unfold chartProj
    rw [intervalIntegral.integral_congr (g := fun x => ∑ j ∈ J, χ (N * x - j) * g x)
      fun x hx => by
        simp only [chartSymbol, hg_def]
        rw [tsum_eq_sum (fun j hj => hJ x hx j hj), Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring]
    rw [intervalIntegral.integral_finsetSum]
    intro j _
    exact ((hχcont.comp (by fun_prop : Continuous fun x : ℝ => (N : ℝ) * x - j)).mul
      hg_cont).intervalIntegrable _ _
  -- each chart piece
  have hA : ∀ A : ZMod N, HasSum (fun m : ℤ => (b ∘ (chartEquiv N)) (A, m))
      (chartPiece hχ hχc h A n * e (A.val * n / N)) := by
    intro A
    rw [chartPiece_mul_e]
    let fA : ℝ → ℂ := fun β => χ (N * β - A.val) * g β
    have hfA_cont : Continuous fA := (hχcont.comp (by fun_prop)).mul hg_cont
    have hfA_cs : HasCompactSupport fA := by
      refine HasCompactSupport.intro (K := Set.Icc ((A.val - R) / N) ((A.val + R) / N))
        isCompact_Icc fun β hβ => ?_
      by_contra hne
      have hne' : χ (N * β - A.val) ≠ 0 := fun h0 => hne (by simp only [fA, h0, zero_mul])
      have hb := abs_le.1 (hR _ hne')
      apply hβ
      constructor
      · rw [div_le_iff₀ hN]; linarith
      · rw [le_div_iff₀ hN]; linarith
    have hint := (hfA_cont.integrable_of_hasCompactSupport hfA_cs).hasSum_intervalIntegral_comp_add_int
    have heq : (∫ β, χ (N * β - A.val) * seqFourier h β * e (n * β)) = ∫ β, fA β := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
      simp only [fA, hg_def]; ring
    rw [heq]
    convert hint using 1
    funext m
    simp only [b, chartEquiv, Equiv.coe_fn_mk, fA]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [hg_per]
    congr 2
    push_cast
    ring
  have hb_sum : HasSum b (∑ j ∈ J, b j) := hasSum_sum_of_ne_finset_zero hbJ
  have hprod : HasSum (b ∘ (chartEquiv N)) (∑ j ∈ J, b j) :=
    (Equiv.hasSum_iff (f := b) (chartEquiv N)).2 hb_sum
  have hfib := hprod.prod_fiberwise hA
  rw [hRHS]
  exact hfib.unique (hasSum_fintype _)

end PrimeBHT.TransferenceAssembly
