module

public import PrimeBHT.Periodic
public import PrimeBHT.PeriodicBlock
public import PrimeBHT.PeriodicAssembly.D4

/-!
# Interpolation: `p:interpsetup` (blueprint N37)

For `1 ≤ p ≤ 2` and `h : Y → ℂ` on a finite probability space (normalized counting measure),
the Lyapunov (log-convexity) inequality `‖h‖_p ≤ ‖h‖₁^{1-θ} ‖h‖₂^θ`, `θ = 2(1 - 1/p)`
(`lpNorm_le`), proved by the weighted AM-GM inequality applied pointwise to `|h|/‖h‖₁` and
`|h|²/‖h‖₂²` (no Hölder/Riesz-Thorin needed).

Combined with `d_B(1)` (N36, `exists_l1_bilinAvg_le`) and `d_B(2)` (N30, `exists_l2_bilinAvg_le`):
`exists_lpNorm_bilinAvg_le`: `‖A_B(F,G)‖_{L^p} ≤ C_ε |B|^{1/2} Q^{-1/p+ε} ‖F‖₂ ‖G‖₂`.
-/

@[expose] public section

namespace PrimeBHT.PeriodicAssembly

open Finset PrimeBHT.Periodic
open scoped BigOperators ComplexConjugate

open PrimeBHT.PeriodicBlock (lam bilinAvg exists_l2_bilinAvg_le)
open PrimeCarleson.Proof.Paper (lcmQ)

/-- The `L^p` norm for the normalized counting measure: `(E_x ‖h x‖^p)^{1/p}`. -/
noncomputable def lpNorm {X : Type*} [Fintype X] (p : ℝ) (h : X → ℂ) : ℝ :=
  (𝔼 x, ‖h x‖ ^ p) ^ p⁻¹

theorem lpNorm_nonneg {X : Type*} [Fintype X] (p : ℝ) (h : X → ℂ) : 0 ≤ lpNorm p h :=
  Real.rpow_nonneg (Finset.expect_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _

/-- Pointwise Young/AM-GM inequality behind the Lyapunov inequality. -/
theorem rpow_le_young {p m₁ m₂ x : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) (hx : 0 ≤ x) :
    x ^ p ≤ m₁ ^ (2 - p) * m₂ ^ (p - 1) * ((2 - p) * (x / m₁) + (p - 1) * (x ^ 2 / m₂)) := by
  have hM : 0 < m₁ ^ (2 - p) * m₂ ^ (p - 1) :=
    mul_pos (Real.rpow_pos_of_pos hm₁ _) (Real.rpow_pos_of_pos hm₂ _)
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := 2 - p) (w₂ := p - 1) (p₁ := x / m₁)
    (p₂ := x ^ 2 / m₂) (by linarith) (by linarith) (div_nonneg hx hm₁.le)
    (div_nonneg (sq_nonneg x) hm₂.le) (by ring)
  have key : (x / m₁) ^ (2 - p) * (x ^ 2 / m₂) ^ (p - 1) =
      x ^ p / (m₁ ^ (2 - p) * m₂ ^ (p - 1)) := by
    rw [Real.div_rpow hx hm₁.le, Real.div_rpow (sq_nonneg x) hm₂.le]
    have e1 : (x ^ 2) ^ (p - 1) = x ^ (2 * (p - 1)) := by
      rw [Real.rpow_mul hx]
      norm_num
    have e2 : x ^ (2 - p) * x ^ (2 * (p - 1)) = x ^ p := by
      rw [← Real.rpow_add' hx (by linarith)]
      congr 1
      ring
    rw [e1, div_mul_div_comm, e2]
  rw [key, div_le_iff₀ hM] at h
  linarith

/-- **Lyapunov interpolation** on a finite probability space, `1 ≤ p ≤ 2`:
`‖h‖_p ≤ ‖h‖₁^{(2-p)/p} ‖h‖₂^{2(p-1)/p}` (`= ‖h‖₁^{1-θ} ‖h‖₂^θ`, `θ = 2(1 - 1/p)`). -/
theorem lpNorm_le {X : Type*} [Fintype X] [Nonempty X] {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (h : X → ℂ) : lpNorm p h ≤ l1 h ^ ((2 - p) / p) * l2 h ^ (2 * (p - 1) / p) := by
  have hp0 : 0 < p := by linarith
  by_cases hm : l1 h = 0
  · have hz : (fun x => ‖h x‖) = 0 :=
      (Fintype.expect_eq_zero_iff_of_nonneg (fun x => norm_nonneg (h x))).1 hm
    have hz' : ∀ x, ‖h x‖ = 0 := fun x => congrFun hz x
    have : lpNorm p h = 0 := by
      unfold lpNorm
      simp [hz', Real.zero_rpow hp0.ne', Real.zero_rpow (inv_ne_zero hp0.ne')]
    rw [this]
    exact mul_nonneg (Real.rpow_nonneg (l1_nonneg _) _) (Real.rpow_nonneg (l2_nonneg _) _)
  · have hm₁ : 0 < l1 h := lt_of_le_of_ne (l1_nonneg _) (Ne.symm hm)
    have hm₂ : 0 < l2 h ^ 2 := pow_pos (lt_of_lt_of_le hm₁ (l1_le_l2 h)) 2
    have hE : 𝔼 x, ‖h x‖ ^ p ≤ l1 h ^ (2 - p) * (l2 h ^ 2) ^ (p - 1) := by
      have h1 : 𝔼 x, ‖h x‖ ^ p ≤ 𝔼 x, (l1 h ^ (2 - p) * (l2 h ^ 2) ^ (p - 1)) *
          ((2 - p) * (‖h x‖ / l1 h) + (p - 1) * (‖h x‖ ^ 2 / l2 h ^ 2)) :=
        Finset.expect_le_expect fun x _ => rpow_le_young hp1 hp2 hm₁ hm₂ (norm_nonneg _)
      refine h1.trans (le_of_eq ?_)
      rw [← Finset.mul_expect]
      have e1 : 𝔼 x, ((2 - p) * (‖h x‖ / l1 h) + (p - 1) * (‖h x‖ ^ 2 / l2 h ^ 2)) = 1 := by
        rw [Finset.expect_add_distrib, ← Finset.mul_expect, ← Finset.mul_expect,
          ← Finset.expect_div, ← Finset.expect_div, ← l2_sq]
        show (2 - p) * (l1 h / l1 h) + (p - 1) * (l2 h ^ 2 / l2 h ^ 2) = 1
        rw [div_self hm₁.ne', div_self hm₂.ne']
        ring
      rw [e1, mul_one]
    have e2 : (l2 h ^ 2) ^ ((p - 1) * p⁻¹) = l2 h ^ (2 * (p - 1) / p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (l2_nonneg h)]
      congr 1
      push_cast
      field_simp
    unfold lpNorm
    calc (𝔼 x, ‖h x‖ ^ p) ^ p⁻¹ ≤ (l1 h ^ (2 - p) * (l2 h ^ 2) ^ (p - 1)) ^ p⁻¹ :=
          Real.rpow_le_rpow (Finset.expect_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
            hE (inv_nonneg.2 hp0.le)
      _ = l1 h ^ ((2 - p) / p) * l2 h ^ (2 * (p - 1) / p) := by
          rw [Real.mul_rpow (Real.rpow_nonneg (l1_nonneg _) _) (Real.rpow_nonneg (sq_nonneg _) _),
            ← Real.rpow_mul (l1_nonneg _), ← Real.rpow_mul (sq_nonneg _), e2, ← div_eq_mul_inv]

/-- **N37** (`p:interpsetup`), explicit-`ε` form: for `1 ≤ p ≤ 2`,
`‖A_B(F,G)‖_{L^p(Y_N)} ≤ C_ε |B|^{1/2} Q^{-1/p+ε} ‖F‖₂ ‖G‖₂`, i.e. `d_B(p) ≤ C_ε |B|^{1/2} Q^{-1/p+ε}`,
with `C_ε` independent of `p`, `Q`, `B`, `N`. -/
theorem exists_lpNorm_bilinAvg_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p Q : ℝ) (B : Finset ℕ), 1 ≤ p → p ≤ 2 → B.Nonempty → 1 ≤ Q →
      (∀ q ∈ B, Q / 2 < (q : ℝ) ∧ (q : ℝ) ≤ Q) → (∀ q ∈ B, Squarefree q) →
      ∀ (N : ℕ) [NeZero N], lcmQ B = N → ∀ F G : ZMod N → ℂ,
        lpNorm p (bilinAvg (lam B N) F G) ≤
          C * √(B.card : ℝ) * Q ^ (-1 / p + ε) * l2 F * l2 G := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_l1_bilinAvg_le hε hε1
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_l2_bilinAvg_le hε hε1
  refine ⟨max C₁ (√C₂), lt_max_of_lt_left hC₁0, fun p Q B hp1 hp2 hB hQ hBQ hsq N _ hN F G => ?_⟩
  have hp0 : 0 < p := by linarith
  have hQ0 : 0 < Q := by linarith
  have h1 := hC₁ Q B hB hQ hBQ hsq N hN F G
  have h2 : l2 (bilinAvg (lam B N) F G) ≤
      √(C₂ * B.card) * Q ^ ((ε - 1) / 2) * l2 F * l2 G := hC₂ Q B hQ hBQ hsq N hN F G
  rw [Real.sqrt_mul hC₂0.le] at h2
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = √(B.card : ℝ) := ⟨_, rfl⟩
  rw [← hr_def] at h1 h2 ⊢
  have hr0 : 0 ≤ r := by rw [hr_def]; exact Real.sqrt_nonneg _
  have hl2F := l2_nonneg F
  have hl2G := l2_nonneg G
  set C : ℝ := max C₁ (√C₂) with hCdef
  have hCC₁ : C₁ ≤ C := le_max_left _ _
  have hCC₂ : √C₂ ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := hC₁0.le.trans hCC₁
  set K : ℝ := C * r * (l2 F * l2 G) with hK
  have hK0 : 0 ≤ K := by positivity
  have hQe1 : 0 ≤ Q ^ (ε - 1) := Real.rpow_nonneg hQ0.le _
  have hQe2 : 0 ≤ Q ^ ((ε - 1) / 2) := Real.rpow_nonneg hQ0.le _
  have hx1 : l1 (bilinAvg (lam B N) F G) ≤ K * Q ^ (ε - 1) := by
    refine h1.trans ?_
    have : C₁ * r * Q ^ (ε - 1) * l2 F * l2 G = (C₁ * r * (l2 F * l2 G)) * Q ^ (ε - 1) := by ring
    rw [this]
    have hKa : C₁ * r * (l2 F * l2 G) ≤ K :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC₁ hr0) (mul_nonneg hl2F hl2G)
    exact mul_le_mul_of_nonneg_right hKa hQe1
  have hx2 : l2 (bilinAvg (lam B N) F G) ≤ K * Q ^ ((ε - 1) / 2) := by
    refine h2.trans ?_
    have : √C₂ * r * Q ^ ((ε - 1) / 2) * l2 F * l2 G =
        (√C₂ * r * (l2 F * l2 G)) * Q ^ ((ε - 1) / 2) := by ring
    rw [this]
    have hKa : √C₂ * r * (l2 F * l2 G) ≤ K :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC₂ hr0) (mul_nonneg hl2F hl2G)
    exact mul_le_mul_of_nonneg_right hKa hQe2
  have hu : 0 ≤ (2 - p) / p := div_nonneg (by linarith) hp0.le
  have hv : 0 ≤ 2 * (p - 1) / p := div_nonneg (by linarith) hp0.le
  have huv : (2 - p) / p + 2 * (p - 1) / p = 1 := by field_simp; ring
  have hlp := lpNorm_le hp1 hp2 (bilinAvg (lam B N) F G)
  have hexp : (ε - 1) / p ≤ -1 / p + ε := by
    have : (ε - 1) / p = ε / p + -1 / p := by ring
    have h3 := div_le_self hε.le hp1
    rw [this]
    linarith
  calc lpNorm p (bilinAvg (lam B N) F G)
      ≤ l1 (bilinAvg (lam B N) F G) ^ ((2 - p) / p) *
          l2 (bilinAvg (lam B N) F G) ^ (2 * (p - 1) / p) := hlp
    _ ≤ (K * Q ^ (ε - 1)) ^ ((2 - p) / p) * (K * Q ^ ((ε - 1) / 2)) ^ (2 * (p - 1) / p) :=
        mul_le_mul (Real.rpow_le_rpow (l1_nonneg _) hx1 hu)
          (Real.rpow_le_rpow (l2_nonneg _) hx2 hv) (Real.rpow_nonneg (l2_nonneg _) _)
          (Real.rpow_nonneg (mul_nonneg hK0 hQe1) _)
    _ = K * Q ^ ((ε - 1) / p) := by
        rw [Real.mul_rpow hK0 hQe1, Real.mul_rpow hK0 hQe2, ← Real.rpow_mul hQ0.le,
          ← Real.rpow_mul hQ0.le]
        have e1 : K ^ ((2 - p) / p) * K ^ (2 * (p - 1) / p) = K := by
          rw [← Real.rpow_add' hK0 (by rw [huv]; norm_num), huv, Real.rpow_one]
        have e2 : Q ^ ((ε - 1) * ((2 - p) / p)) * Q ^ ((ε - 1) / 2 * (2 * (p - 1) / p)) =
            Q ^ ((ε - 1) / p) := by
          rw [← Real.rpow_add hQ0]
          congr 1
          field_simp
          ring
        calc K ^ ((2 - p) / p) * Q ^ ((ε - 1) * ((2 - p) / p)) *
              (K ^ (2 * (p - 1) / p) * Q ^ ((ε - 1) / 2 * (2 * (p - 1) / p)))
            = (K ^ ((2 - p) / p) * K ^ (2 * (p - 1) / p)) *
              (Q ^ ((ε - 1) * ((2 - p) / p)) * Q ^ ((ε - 1) / 2 * (2 * (p - 1) / p))) := by ring
          _ = K * Q ^ ((ε - 1) / p) := by rw [e1, e2]
    _ ≤ K * Q ^ (-1 / p + ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ hexp) hK0
    _ = C * r * Q ^ (-1 / p + ε) * l2 F * l2 G := by rw [hK]; ring

end PrimeBHT.PeriodicAssembly
