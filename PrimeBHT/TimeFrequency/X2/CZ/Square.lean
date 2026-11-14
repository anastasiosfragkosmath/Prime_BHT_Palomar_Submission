module

public import PrimeBHT.TimeFrequency.X2.CZ.MikhlinAll
public import PrimeBHT.TimeFrequency.X2.CZ.Khintchine
public import PrimeBHT.TimeFrequency.X2.CZ.SquareAux

/-!
# V08(d), upper half: the lattice square function of a family of multipliers

`VectorMikhlinSquare a₀ q s C` for all `1 < q, s < ∞`, from the strong-type matrix
(`vectorMikhlinStrongStatement_three`) and the Khintchine inequality (`Khintchine.lean`):

* every `n_j` is a bounded symbol (`n_j = (σ_{η⁺} - σ_{η⁻})/2`), so `ε ↦ T_ε = Σ_j ε_j T_{n_j}` is linear
  (`tensorMult_sum_symbol`), and every sign symbol `Σ_j ε_j n_j` is in the Mikhlin class with the constant `B`;
* pointwise in `(x, y)` (Khintchine, exponent `p = min(q, s)`):
  `(Σ_j |T_{n_j}F|²)^{1/2} ≤ c_p (2^{-N} Σ_ε |T_εF|^p)^{1/p}`;
* Minkowski in `y` (`p ≤ s`) and in `x` (`p ≤ q`) (`SquareAux.lean`) and the bound for each `T_ε` give
  `‖(Σ_j |T_{n_j}F|²)^{1/2}‖_{L^q(L^s)} ≤ c_p C(q, s) B ‖F‖_{L^q(L^s)}`.

No Kahane inequality is needed: the exponent of the average is chosen as `min(q, s)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology Real ComplexConjugate FourierTransform SchwartzMap

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

open PrimeBHT.Statements

section Linear

variable {N : ℕ} {n : Fin N → ℝ → ℂ}

/-- Linearity of `T_σ` in the symbol, for finite combinations of bounded symbols. -/
theorem multOp_sum_symbol {B : ℝ} (hn : ∀ j, IsBoundedSymbol B (n j)) (c : Fin N → ℂ) (g : 𝓢(ℝ, ℂ))
    (x : ℝ) :
    multOp (fun ξ => ∑ j, c j * n j ξ) (⇑g) x = ∑ j, c j * multOp (n j) (⇑g) x := by
  unfold multOp
  have h1 : (fun ξ => (∑ j, c j * n j ξ) * 𝓕 (⇑g) ξ) =
      fun ξ => ∑ j, c j * (n j ξ * 𝓕 (⇑g) ξ) := by
    ext ξ
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h1, fourierInv_finset_sum_fun Finset.univ _
    (fun j _ => ((hn j).integrable_mul_fourier g).const_mul (c j))]
  exact Finset.sum_congr rfl fun j _ => fourierInv_const_mul (c j) _ x

theorem tensorMult_sum_symbol {P : ℕ} [NeZero P] {B : ℝ} (hn : ∀ j, IsBoundedSymbol B (n j))
    (c : Fin N → ℂ) (f : ZMod P → 𝓢(ℝ, ℂ)) (x : ℝ) (y : ZMod P) :
    tensorMult (fun ξ => ∑ j, c j * n j ξ) f x y = ∑ j, c j * tensorMult (n j) f x y := by
  unfold tensorMult
  simp_rw [multOp_sum_symbol hn, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun A _ => by ring

theorem continuous_tensorMult {P : ℕ} [NeZero P] {B : ℝ} {σ : ℝ → ℂ} (hσ : IsBoundedSymbol B σ)
    (f : ZMod P → 𝓢(ℝ, ℂ)) (y : ZMod P) : Continuous fun x => tensorMult σ f x y := by
  unfold tensorMult
  exact continuous_finsetSum _ fun A _ => (hσ.continuous_multOp (f A)).mul continuous_const

/-- Each member of the family is a bounded symbol. -/
theorem isBoundedSymbol_of_family {a₀ : ℕ} {B : ℝ}
    (hη : ∀ η : Fin N → ℂ, (∀ j, ‖η j‖ = 1) → IsMikhlin a₀ B (fun ξ => ∑ j, η j * n j ξ))
    (j : Fin N) : IsBoundedSymbol B (n j) := by
  classical
  set ηp : Fin N → ℂ := fun i => if i = j then 1 else 1 with hηp
  set ηm : Fin N → ℂ := fun i => if i = j then -1 else 1 with hηm
  have hp : ∀ i, ‖ηp i‖ = 1 := fun i => by simp [hηp]
  have hm : ∀ i, ‖ηm i‖ = 1 := fun i => by by_cases h : i = j <;> simp [hηm, h]
  have hbp := (hη ηp hp).isBoundedSymbol
  have hbm := (hη ηm hm).isBoundedSymbol
  have e : n j = fun ξ => (1 / 2 : ℂ) * ((∑ i, ηp i * n i ξ) - ∑ i, ηm i * n i ξ) := by
    ext ξ
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single j]
    · simp [hηp, hηm]; ring
    · intro i _ hi
      simp [hηp, hηm, hi]
    · intro h; exact absurd (Finset.mem_univ j) h
  refine ⟨?_, ?_⟩
  · rw [e]
    exact (hbp.aestronglyMeasurable.sub hbm.aestronglyMeasurable).const_mul _
  · filter_upwards [hbp.ae_norm_le, hbm.ae_norm_le] with ξ h1 h2
    rw [e]
    simp only
    rw [norm_mul]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [this]
    have := norm_sub_le (∑ i, ηp i * n i ξ) (∑ i, ηm i * n i ξ)
    linarith

end Linear

/-- **The square-function bound from the strong-type bound and Khintchine.** -/
theorem vectorMikhlinSquare_of_strong {a₀ : ℕ} {q s Cs : ℝ} (hq : 1 < q) (hs : 1 < s)
    (hC : VectorMikhlinStrong a₀ q s Cs) :
    VectorMikhlinSquare a₀ q s (khinConst (min q s) * Cs) := by
  intro P _ N n B hη f
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < s := by linarith
  set p := min q s with hp
  have hp0 : 0 < p := lt_min hq0 hs0
  have hpq : p ≤ q := min_le_left _ _
  have hps : p ≤ s := min_le_right _ _
  set c := khinConst p with hc
  have hc0 : 0 ≤ c := khinConst_nonneg p
  have hbd : ∀ j, IsBoundedSymbol B (n j) := isBoundedSymbol_of_family hη
  -- sign symbols
  set σε : (Fin N → Bool) → ℝ → ℂ := fun ε ξ => ∑ j, ((sgn (ε j) : ℝ) : ℂ) * n j ξ with hσε
  have hMik : ∀ ε, IsMikhlin a₀ B (σε ε) := fun ε =>
    hη (fun j => ((sgn (ε j) : ℝ) : ℂ)) (fun j => by rw [Complex.norm_real, Real.norm_eq_abs, abs_sgn])
  set V : (Fin N → Bool) → ℝ → ZMod P → ℂ := fun ε x y => tensorMult (σε ε) f x y with hV
  have hVsum : ∀ ε x y, V ε x y = rsum (fun j => tensorMult (n j) f x y) ε := by
    intro ε x y; exact tensorMult_sum_symbol hbd _ f x y
  have hVcont : ∀ ε y, Continuous fun x => V ε x y := fun ε y =>
    continuous_tensorMult (hMik ε).isBoundedSymbol f y
  have hUcont : ∀ j y, Continuous fun x => tensorMult (n j) f x y := fun j y =>
    continuous_tensorMult (hbd j) f y
  -- the square function
  set Q : ℝ → ZMod P → ℝ := fun x y => latticeSquare (fun j => tensorMult (n j) f x) y with hQ
  have hQ0 : ∀ x y, 0 ≤ Q x y := fun x y =>
    Real.rpow_nonneg (Finset.sum_nonneg fun j _ => by positivity) _
  have hQcont : ∀ y, Continuous fun x => Q x y := by
    intro y
    refine Continuous.rpow_const (continuous_finsetSum _ fun j _ => ?_) (fun _ => Or.inr (by norm_num))
    exact ((hUcont j y).norm).pow 2
  -- the strong bounds for the sign symbols
  set M : ℝ≥0∞ := ENNReal.ofReal (Cs * B) * mixedENorm q s (tensorFun f) with hM
  have hVM : ∀ ε, mixedENorm q s (V ε) ≤ M := fun ε => hC P B (σε ε) (hMik ε) f
  -- pointwise Khintchine
  set w : ℝ := ((2 : ℝ) ^ N)⁻¹ with hw
  have hw0 : 0 ≤ w := by positivity
  have hKh : ∀ x y, Q x y ≤ c * (∑ ε : Fin N → Bool, w * ‖V ε x y‖ ^ p) ^ p⁻¹ := by
    intro x y
    have h := khintchine_lower (fun j => tensorMult (n j) f x y) hp0
    rw [← Finset.mul_sum]
    simp_rw [hVsum]
    exact h
  have hY : ∀ x, yNorm s (fun y => ((Q x y : ℝ) : ℂ)) ≤
      c * (∑ ε : Fin N → Bool, w * yNorm s (fun y => V ε x y) ^ p) ^ p⁻¹ := fun x =>
    yNorm_avg_le hs.le hp0 hps hc0 Finset.univ (fun _ => w) (fun _ _ => hw0) (fun ε y => V ε x y)
      (fun y => Q x y) (hQ0 x) (hKh x)
  have hX := eLpNorm_avg_le (Finset.univ : Finset (Fin N → Bool)) hp0 hpq hc0 (fun _ => w)
    (fun _ _ => hw0) (fun ε x => yNorm s (fun y => V ε x y)) (fun ε x => yNorm_nonneg s _)
    (fun ε => measurable_yNorm s (fun y => (hVcont ε y).measurable))
    (fun x => yNorm s (fun y => ((Q x y : ℝ) : ℂ))) (fun x => yNorm_nonneg s _)
    (measurable_yNorm s (fun y => Complex.measurable_ofReal.comp (hQcont y).measurable)) hY
  -- sum of the weights
  have hwsum : ∑ _ε : Fin N → Bool, ENNReal.ofReal w = 1 := by
    rw [Finset.sum_const]
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    rw [hw, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    push_cast
    rw [mul_inv_cancel₀ (by positivity)]
    simp
  have hsumM : ∑ ε : Fin N → Bool, ENNReal.ofReal w *
      eLpNorm (fun x => yNorm s (fun y => V ε x y)) (ENNReal.ofReal q) volume ^ p ≤ M ^ p := by
    calc ∑ ε : Fin N → Bool, ENNReal.ofReal w *
          eLpNorm (fun x => yNorm s (fun y => V ε x y)) (ENNReal.ofReal q) volume ^ p
        ≤ ∑ _ε : Fin N → Bool, ENNReal.ofReal w * M ^ p := by
          refine Finset.sum_le_sum fun ε _ => ?_
          refine mul_le_mul' le_rfl (ENNReal.rpow_le_rpow ?_ hp0.le)
          exact hVM ε
      _ = M ^ p := by rw [← Finset.sum_mul, hwsum, one_mul]
  have hfin : (∑ ε : Fin N → Bool, ENNReal.ofReal w *
      eLpNorm (fun x => yNorm s (fun y => V ε x y)) (ENNReal.ofReal q) volume ^ p) ^ p⁻¹ ≤ M := by
    calc _ ≤ (M ^ p) ^ p⁻¹ := ENNReal.rpow_le_rpow hsumM (inv_nonneg.2 hp0.le)
      _ = M := by rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one]
  calc eLpNorm (fun x => yNorm s (fun y => ((latticeSquare (fun j => tensorMult (n j) f x) y : ℝ) : ℂ)))
        (ENNReal.ofReal q) volume
      ≤ ENNReal.ofReal c * M := hX.trans (mul_le_mul' le_rfl hfin)
    _ = ENNReal.ofReal (khinConst (min q s) * Cs * B) * mixedENorm q s (tensorFun f) := by
        rw [hM, ← mul_assoc, ← ENNReal.ofReal_mul hc0, mul_assoc]

/-- **Target (d), upper half, unconditional (`a₀ ≥ 3`)**: `VectorMikhlinSquareStatement a₀`, i.e. the lattice
square function of a family of multipliers whose unimodular combinations are Mikhlin with constant `B` is
bounded on `L^q(ℝ; L^s(Y_P))` for all `1 < q, s < ∞`, with `C = c_{min(q,s)} C_strong(q, s)`. -/
theorem vectorMikhlinSquareStatement_of_ge {a₀ : ℕ} (h : 3 ≤ a₀) : VectorMikhlinSquareStatement a₀ := by
  intro q s hq hs
  obtain ⟨Cs, hCs⟩ := (vectorMikhlinStatement_of_ge h).1 q s hq hs
  exact ⟨_, vectorMikhlinSquare_of_strong hq hs hCs⟩

/-- **Target (d), upper half, for `a₀ = 3`**. -/
theorem vectorMikhlinSquareStatement_three : VectorMikhlinSquareStatement 3 :=
  vectorMikhlinSquareStatement_of_ge le_rfl

end PrimeBHT.TimeFrequency.X2.CZ
