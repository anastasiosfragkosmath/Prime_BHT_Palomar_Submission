module

public import PrimeBHT.FinalAssembly
public import PrimeBHT.Progression

/-!
# S17: the group-aggregated decay of the case `r < 1` (blueprint N52 (C), (D))

Conditional provider.  Everything is stated for an abstract family of bilinear maps indexed by an
arbitrary type `ι` with a real parameter `Q : ι → ℝ`, constants uniform in `i` once `Q₁ ≤ Q i`.

* `interp_epsilon_icc`: two-point power interpolation with `ε`-losses, weight `θ ∈ [0,1]`.
* `group_decay_of_estimates` (N52 (C)): from the three estimates `e:secondinterp`,
  `e:thirdinterp`, `e:fourthinterp` for `V_{Q,j}`, two successive two-point interpolations (first
  between `(1/2,1/2,1)` and `(1-δ,δ,1)`, then between the resulting Banach point and
  `(1-δ,1-δ,2-2δ)`) give `‖V_{Q,j}‖_{ℓ^r} ≲ Q^{σ_j(δ)+ε} ‖f‖_p ‖g‖_q`, the combined exponent being
  exactly `sigma D.p' D.t D.τ j D.δ`.
* `complexity_decay_of_group_decays` (N52 (D)): quasi-triangle inequality for `ℓ^r`, `r < 1`, over
  the `M + 1` groups, plus the `U`-bound, giving `Q^{-μ/2}`.
* `complexity_decay_of_estimates`: the composite statement from the raw estimates.
-/

public section

namespace PrimeBHT.GroupDecay

open MeasureTheory PrimeBHT.Exponents PrimeBHT.FinalAssembly
open scoped ENNReal

variable {ι : Type*} {p q r : ℝ}

/-! ## Two-point interpolation with `ε`-losses and weight in `[0,1]` -/

/-- Two-point power interpolation with `ε`-losses for a weight `θ ∈ [0, 1]` (the endpoints are
the trivial cases; the interior is `interp_power`). -/
theorem interp_epsilon_icc
    (T : ι → (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) (Q : ι → ℝ)
    {p₀ p₁ q₀ q₁ r₀ r₁ α₀ α₁ θ p q r : ℝ}
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁)
    (hr₀ : 1 / r₀ = 1 / p₀ + 1 / q₀) (hr₁ : 1 / r₁ = 1 / p₁ + 1 / q₁)
    (h₀ : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (T i f g) (ENNReal.ofReal r₀) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ (α₀ + ε)) * eLpNorm f (ENNReal.ofReal p₀) Measure.count *
          eLpNorm g (ENNReal.ofReal q₀) Measure.count)
    (h₁ : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (T i f g) (ENNReal.ofReal r₁) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ (α₁ + ε)) * eLpNorm f (ENNReal.ofReal p₁) Measure.count *
          eLpNorm g (ENNReal.ofReal q₁) Measure.count)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (hp : 1 / p = (1 - θ) / p₀ + θ / p₁)
    (hq : 1 / q = (1 - θ) / q₀ + θ / q₁) (hr : 1 / r = 1 / p + 1 / q) :
    ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (T i f g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ ((1 - θ) * α₀ + θ * α₁ + ε)) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count := by
  intro ε hε
  obtain ⟨C₀, Qa, hC₀, ha⟩ := h₀ ε hε
  obtain ⟨C₁, Qb, hC₁, hb⟩ := h₁ ε hε
  rcases hθ.1.eq_or_lt with h0 | h0
  · -- `θ = 0`
    subst h0
    have hp' : p = p₀ := by simpa using hp
    have hq' : q = q₀ := by simpa using hq
    have hr' : r = r₀ := by
      have h1 : 1 / r = 1 / r₀ := by rw [hr, hr₀, hp', hq']
      simpa using h1
    subst hp' hq' hr'
    refine ⟨C₀, Qa, hC₀, fun i hi f g => ?_⟩
    have hex : (1 - 0) * α₀ + 0 * α₁ + ε = α₀ + ε := by ring
    rw [hex]
    exact ha i hi f g
  rcases hθ.2.eq_or_lt with h1 | h1
  · -- `θ = 1`
    subst h1
    have hp' : p = p₁ := by simpa using hp
    have hq' : q = q₁ := by simpa using hq
    have hr' : r = r₁ := by
      have h1 : 1 / r = 1 / r₁ := by rw [hr, hr₁, hp', hq']
      simpa using h1
    subst hp' hq' hr'
    refine ⟨C₁, Qb, hC₁, fun i hi f g => ?_⟩
    have hex : (1 - 1) * α₀ + 1 * α₁ + ε = α₁ + ε := by ring
    rw [hex]
    exact hb i hi f g
  · have hθ' : θ ∈ Set.Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
    refine ⟨C₀ ^ (1 - θ) * C₁ ^ θ, max (max Qa Qb) 1,
      mul_pos (Real.rpow_pos_of_pos hC₀ _) (Real.rpow_pos_of_pos hC₁ _), ?_⟩
    intro i hi f g
    have hQ : 0 < Q i := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hi)
    have hQa : Qa ≤ Q i := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hi
    have hQb : Qb ≤ Q i := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hi
    have h := interp_power (T i) hQ hp₀ hp₁ hq₀ hq₁ hr₀ hr₁ hC₀ hC₁ (ha i hQa) (hb i hQb) hθ' hp hq
      hr f g
    have hex : (1 - θ) * (α₀ + ε) + θ * (α₁ + ε) = (1 - θ) * α₀ + θ * α₁ + ε := by ring
    rwa [hex] at h

/-! ## The intermediate Banach point -/

/-- The intermediate point of the first interpolation of `group_decay_of_estimates`:
`(1/p_m, 1/q_m) = (l₀ (1/2,1/2) + l₁ (1-δ, δ)) / (l₀ + l₁)`. -/
theorem exists_mid_point {l₀ l₁ δ : ℝ} (hl₀ : 0 < l₀) (hl₁ : 0 ≤ l₁) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ pm qm : ℝ, 1 ≤ pm ∧ 1 ≤ qm ∧ 1 / pm = (l₀ / 2 + l₁ * (1 - δ)) / (l₀ + l₁) ∧
      1 / qm = (l₀ / 2 + l₁ * δ) / (l₀ + l₁) := by
  have hs : 0 < l₀ + l₁ := by linarith
  have hA : 0 < l₀ / 2 + l₁ * (1 - δ) := by
    have := mul_nonneg hl₁ (sub_nonneg.2 hδ1.le)
    linarith
  have hB : 0 < l₀ / 2 + l₁ * δ := by
    have := mul_nonneg hl₁ hδ0.le
    linarith
  refine ⟨(l₀ + l₁) / (l₀ / 2 + l₁ * (1 - δ)), (l₀ + l₁) / (l₀ / 2 + l₁ * δ), ?_, ?_,
    one_div_div _ _, one_div_div _ _⟩
  · rw [one_le_div hA]
    nlinarith [mul_nonneg hl₁ hδ0.le]
  · rw [one_le_div hB]
    nlinarith [mul_nonneg hl₁ (sub_nonneg.2 hδ1.le)]

/-- The exponent identity of `e:group-decay` (blueprint N52 (C)):
`λ₀ (-τ_{j-1}/2) + λ₂ (2 τ_j (1-δ)) = σ_j(δ)`. -/
theorem exponent_eq_sigma (D : ExponentData p q r) (j : ℕ) :
    D.l₀ * (-(D.τ (j - 1) / 2)) + D.l₂ * (2 * D.τ j * (1 - D.δ)) =
      sigma D.p' D.t D.τ j D.δ := by
  have hδ : 1 - 2 * D.δ ≠ 0 := by
    have := D.δ_lt
    have h2 := (lt_min_iff.1 this).1
    linarith
  unfold sigma
  rw [D.l₀_eq, D.l₂_eq]
  field_simp

/-! ## N52 (C): the group decay -/

/-- **N52 (C), `e:group-decay`, conditional on the three estimates.**
For the operator `V = V_{Q,j}` of the scales between `Q^{τ_{j-1}}` and `Q^{τ_j}`:
* (E2) `e:secondinterp`: `‖V‖_{ℓ¹} ≲ Q^{-τ_{j-1}/2+ε} ‖f‖₂ ‖g‖₂`;
* (E3) `e:thirdinterp`: `‖V‖_{ℓ¹} ≲ Q^{ε} ‖f‖_{1/(1-δ)} ‖g‖_{1/δ}`;
* (E4) `e:fourthinterp`: `‖V‖_{ℓ^{1/(2-2δ)}} ≲ Q^{2τ_j(1-δ)+ε} ‖f‖_{1/(1-δ)} ‖g‖_{1/(1-δ)}`.
Conclusion: `‖V‖_{ℓ^r} ≲ Q^{σ_j(δ)+ε} ‖f‖_p ‖g‖_q`, `σ_j(δ) = sigma D.p' D.t D.τ j D.δ`. -/
theorem group_decay_of_estimates
    (V : ι → (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) (Q : ι → ℝ)
    (D : ExponentData p q r) (j : ℕ)
    (hE2 : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (V i f g) (ENNReal.ofReal 1) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ (-(D.τ (j - 1) / 2) + ε)) *
          eLpNorm f (ENNReal.ofReal 2) Measure.count * eLpNorm g (ENNReal.ofReal 2) Measure.count)
    (hE3 : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (V i f g) (ENNReal.ofReal 1) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ ε) *
          eLpNorm f (ENNReal.ofReal (1 / (1 - D.δ))) Measure.count *
            eLpNorm g (ENNReal.ofReal (1 / D.δ)) Measure.count)
    (hE4 : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (V i f g) (ENNReal.ofReal (1 / (2 - 2 * D.δ))) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ (2 * D.τ j * (1 - D.δ) + ε)) *
          eLpNorm f (ENNReal.ofReal (1 / (1 - D.δ))) Measure.count *
            eLpNorm g (ENNReal.ofReal (1 / (1 - D.δ))) Measure.count) :
    ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (V i f g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ (sigma D.p' D.t D.τ j D.δ + ε)) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count := by
  have hδ0 : 0 < D.δ := D.δ_pos
  have hδhalf : D.δ < 1 / 2 := lt_of_lt_of_le D.δ_lt (min_le_left _ _)
  have hδp' : D.δ < 1 / D.p' := lt_of_lt_of_le D.δ_lt (min_le_right _ _)
  have hδ1 : D.δ < 1 := by linarith
  have h1δ : 0 < 1 - D.δ := by linarith
  have hl₀ : 0 < D.l₀ := by
    rw [D.l₀_eq]
    exact div_pos (by linarith) (by linarith)
  have hl₁ := D.l₁_nonneg
  have hl₂ := D.l₂_pos
  have hl₂1 := D.l₂_lt_one
  have hsum : D.l₀ + D.l₁ = 1 - D.l₂ := by linarith [D.l_sum]
  have hs : 0 < D.l₀ + D.l₁ := by rw [hsum]; linarith
  obtain ⟨pm, qm, hpm, hqm, hpm', hqm'⟩ := exists_mid_point hl₀ hl₁ hδ0 hδ1
  have hp₁ : (1 : ℝ) ≤ 1 / (1 - D.δ) := one_le_one_div h1δ (by linarith)
  have hq₁ : (1 : ℝ) ≤ 1 / D.δ := one_le_one_div hδ0 hδ1.le
  have hp₂ : (1 : ℝ) ≤ 1 / (1 - D.δ) := hp₁
  have hs' : D.l₀ + D.l₁ ≠ 0 := hs.ne'
  have h1δ' : 1 - D.δ ≠ 0 := h1δ.ne'
  have hδ' : D.δ ≠ 0 := hδ0.ne'
  -- the reciprocal sum at the intermediate point
  have hrm : 1 / (1 : ℝ) = 1 / pm + 1 / qm := by
    rw [hpm', hqm', ← add_div]
    have : D.l₀ / 2 + D.l₁ * (1 - D.δ) + (D.l₀ / 2 + D.l₁ * D.δ) = D.l₀ + D.l₁ := by ring
    rw [this, div_self hs']
    norm_num
  -- first interpolation: `(1/2,1/2,1)` and `(1-δ,δ,1)`
  have step1 := interp_epsilon_icc V Q (p₀ := 2) (p₁ := 1 / (1 - D.δ)) (q₀ := 2)
    (q₁ := 1 / D.δ) (r₀ := 1) (r₁ := 1) (α₀ := -(D.τ (j - 1) / 2)) (α₁ := 0)
    (θ := D.l₁ / (D.l₀ + D.l₁)) (p := pm) (q := qm) (r := 1) (by norm_num) hp₁ (by norm_num) hq₁
    (by norm_num) (by simp only [one_div_one_div]; ring) hE2
    (by intro ε hε; simpa only [zero_add] using hE3 ε hε)
    ⟨div_nonneg hl₁ hs.le, (div_le_one hs).2 (by linarith)⟩
    (by rw [hpm']; field_simp; ring) (by rw [hqm']; field_simp; ring) hrm
  -- second interpolation: the intermediate point and `(1-δ,1-δ,2-2δ)`
  have hp2 : 1 / p = (1 - D.l₂) / pm + D.l₂ / (1 / (1 - D.δ)) := by
    have h : (1 - D.l₂) / pm = D.l₀ * (1 / 2) + D.l₁ * (1 - D.δ) := by
      rw [div_eq_mul_one_div, hpm', ← hsum]
      field_simp
    rw [h, ← D.coord_p]
    field_simp
  have hq2 : 1 / q = (1 - D.l₂) / qm + D.l₂ / (1 / (1 - D.δ)) := by
    have h : (1 - D.l₂) / qm = D.l₀ * (1 / 2) + D.l₁ * D.δ := by
      rw [div_eq_mul_one_div, hqm', ← hsum]
      field_simp
    rw [h, ← D.coord_q]
    field_simp
  have step2 := interp_epsilon_icc V Q (p₀ := pm) (p₁ := 1 / (1 - D.δ)) (q₀ := qm)
    (q₁ := 1 / (1 - D.δ)) (r₀ := 1) (r₁ := 1 / (2 - 2 * D.δ))
    (α₀ := (1 - D.l₁ / (D.l₀ + D.l₁)) * (-(D.τ (j - 1) / 2)) + D.l₁ / (D.l₀ + D.l₁) * 0)
    (α₁ := 2 * D.τ j * (1 - D.δ)) (θ := D.l₂) (p := p) (q := q) (r := r)
    hpm hp₁ hqm hp₂ hrm (by simp only [one_div_one_div]; ring) step1 hE4 ⟨hl₂.le, hl₂1.le⟩
    hp2 hq2 (exponentData_inv_r D)
  intro ε hε
  obtain ⟨C, Q₁, hC, h⟩ := step2 ε hε
  refine ⟨C, Q₁, hC, fun i hi f g => ?_⟩
  have hex : (1 - D.l₂) * ((1 - D.l₁ / (D.l₀ + D.l₁)) * (-(D.τ (j - 1) / 2)) +
      D.l₁ / (D.l₀ + D.l₁) * 0) + D.l₂ * (2 * D.τ j * (1 - D.δ)) + ε =
        sigma D.p' D.t D.τ j D.δ + ε := by
    rw [← exponent_eq_sigma D j, ← hsum]
    field_simp
    ring
  have := h i hi f g
  rwa [hex] at this

/-! ## N52 (D): aggregation over the `M + 1` groups -/

/-- A finite family of estimates with constants and thresholds can be made uniform (the constant
may only be enlarged, which is allowed by `hmono` once `Q i > 0`). -/
theorem exists_uniform (Q : ι → ℝ) (S : Finset ℕ) (P : ℕ → ι → ℝ → Prop)
    (hmono : ∀ j i C C', 0 < Q i → C ≤ C' → P j i C → P j i C')
    (h : ∀ j ∈ S, ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → P j i C) :
    ∃ C Q₁ : ℝ, 0 < C ∧ 1 ≤ Q₁ ∧ ∀ i, Q₁ ≤ Q i → ∀ j ∈ S, P j i C := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, 1, one_pos, le_rfl, by simp⟩
  | insert a S ha ih =>
    obtain ⟨C, Q₁, hC, hQ₁, hall⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨C', Q', hC', hall'⟩ := h a (Finset.mem_insert_self a S)
    refine ⟨max C C', max Q₁ Q', lt_of_lt_of_le hC (le_max_left _ _),
      le_trans hQ₁ (le_max_left _ _), fun i hi j hj => ?_⟩
    have hQi : 0 < Q i := lt_of_lt_of_le one_pos (le_trans hQ₁ (le_trans (le_max_left _ _) hi))
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact hmono j i C' _ hQi (le_max_right _ _)
        (hall' i (le_trans (le_max_right _ _) hi))
    · exact hmono j i C _ hQi (le_max_left _ _)
        (hall i (le_trans (le_max_left _ _) hi) j hj)

/-- Monotonicity of `C Q^x` in `C` and in the exponent, for `Q ≥ 1`, after `ENNReal.ofReal`. -/
theorem ofReal_mul_rpow_le {C C' Q x y : ℝ} (hQ : 1 ≤ Q) (hC0 : 0 ≤ C) (hC : C ≤ C')
    (hxy : x ≤ y) : ENNReal.ofReal (C * Q ^ x) ≤ ENNReal.ofReal (C' * Q ^ y) :=
  ENNReal.ofReal_le_ofReal (mul_le_mul hC (Real.rpow_le_rpow_of_exponent_le hQ hxy)
    (Real.rpow_nonneg (zero_le_one.trans hQ) _) (hC0.trans hC))

/-- The `ℓ^r`-quasi-triangle inequality, `0 < r ≤ 1`, for a finite sum of terms each bounded by `B`:
`‖∑_{k ∈ t} X_k‖_r ≤ (#t)^{1/r} B`. -/
theorem eLpNorm_sum_le_card_mul {κ : Type*} (t : Finset κ) (X : κ → ℤ → ℂ) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) {B : ℝ≥0∞}
    (h : ∀ k ∈ t, eLpNorm (X k) (ENNReal.ofReal r) Measure.count ≤ B) :
    eLpNorm (∑ k ∈ t, X k) (ENNReal.ofReal r) Measure.count ≤ (t.card : ℝ≥0∞) ^ (1 / r) * B := by
  have h1 := PrimeBHT.Progression.eLpNorm_sum_rpow_le t X hr
  rw [min_eq_left hr1] at h1
  have h2 : ∑ k ∈ t, eLpNorm (X k) (ENNReal.ofReal r) Measure.count ^ r ≤ ∑ k ∈ t, B ^ r :=
    Finset.sum_le_sum fun k hk => ENNReal.rpow_le_rpow (h k hk) hr.le
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  have h3 := h1.trans h2
  have h4 : (t.card : ℝ≥0∞) * B ^ r = ((t.card : ℝ≥0∞) ^ (1 / r) * B) ^ r := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← ENNReal.rpow_mul, one_div_mul_cancel hr.ne',
      ENNReal.rpow_one]
  rw [h4] at h3
  exact (ENNReal.rpow_le_rpow_iff hr).1 h3

/-- `0 < r < 1` for the target of an `ExponentData`. -/
theorem exponentData_r_mem (D : ExponentData p q r) : 0 < r ∧ r < 1 := by
  have hθ := (exponentData_theta_mem D).1
  have h0 : 0 < r * D.θ := by linarith [D.τ_zero_pos, D.τ_zero_lt]
  have hr0 : 0 < r := by
    by_contra h
    have h := not_lt.1 h
    nlinarith [mul_nonneg (neg_nonneg.2 h) hθ.le]
  refine ⟨hr0, ?_⟩
  by_contra h
  have h := not_lt.1 h
  have : 1 / r ≤ 1 := (div_le_one hr0).2 h
  linarith [D.t_eq, D.t_pos]

/-- **N52 (D), `e:complexity-decay`, conditional on the group decays.**
With `H_mod = H₀ + ∑_{j=1}^M V_j` (the consecutive ranges `[b_Q,Q^{τ₀})`, `[Q^{τ_{j-1}},Q^{τ_j})`),
* the initial group `‖H₀‖_r ≲ Q^{τ₀/r - θ/4 + ε}` (N52 (B)),
* the groups `‖V_j‖_r ≲ Q^{σ_j(δ)+ε}`, `1 ≤ j ≤ M` (N52 (C), `group_decay_of_estimates`),
* the tail `‖U‖_r ≲ Q^{t - 3θ/8 + ε}` (N52 (A), `power_decay_quasiBanach_of_estimates`),
the `r`-quasi-triangle inequality (`r < 1`) over `M + 1` terms and `μ ≤` all the strict gaps give
`‖H_mod‖_r + ‖U‖_r ≲ Q^{-μ/2} ‖f‖_p ‖g‖_q`. -/
theorem complexity_decay_of_group_decays
    (Hmod H₀ U : ι → (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ))
    (V : ℕ → ι → (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) (Q : ι → ℝ)
    (D : ExponentData p q r)
    (hdecomp : ∀ i (f g : ℤ →₀ ℂ), Hmod i f g = H₀ i f g + ∑ j ∈ Finset.Icc 1 D.M, V j i f g)
    (hH₀ : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (H₀ i f g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ (D.τ 0 / r - D.θ / 4 + ε)) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count)
    (hV : ∀ j, 1 ≤ j → j ≤ D.M → ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧
      ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
        eLpNorm (V j i f g) (ENNReal.ofReal r) Measure.count ≤
          ENNReal.ofReal (C * Q i ^ (sigma D.p' D.t D.τ j D.δ + ε)) *
            eLpNorm f (ENNReal.ofReal p) Measure.count *
              eLpNorm g (ENNReal.ofReal q) Measure.count)
    (hU : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (U i f g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ (D.t - 3 * D.θ / 8 + ε)) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count) :
    ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (Hmod i f g) (ENNReal.ofReal r) Measure.count +
          eLpNorm (U i f g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ (-(D.μ / 2))) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count := by
  classical
  obtain ⟨hr0, hr1⟩ := exponentData_r_mem D
  have hμ : 0 < D.μ / 2 := half_pos D.μ_pos
  obtain ⟨C₀, Q₀, hC₀, h₀⟩ := hH₀ (D.μ / 2) hμ
  obtain ⟨C_U, Q_U, hC_U, h_U⟩ := hU (D.μ / 2) hμ
  obtain ⟨C_V, Q_V, hC_V, hQ_V, h_V⟩ := exists_uniform Q (Finset.Icc 1 D.M)
    (fun j i C => ∀ f g : ℤ →₀ ℂ,
      eLpNorm (V j i f g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ (sigma D.p' D.t D.τ j D.δ + D.μ / 2)) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count)
    (fun j i C C' hQ hCC' hP f g => (hP f g).trans (by
      refine mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl) le_rfl
      exact mul_le_mul_of_nonneg_right hCC' (Real.rpow_nonneg hQ.le _)))
    (fun j hj => hV j (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2 (D.μ / 2) hμ)
  set A : ℝ := C₀ + C_U + C_V with hA
  have hApos : 0 < A := by positivity
  set t : Finset ℕ := insert 0 (Finset.Icc 1 D.M) with ht
  set c : ℝ := ((t.card : ℝ)) ^ (1 / r) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨(c + 1) * A, max (max Q₀ Q_U) Q_V, by positivity, fun i hi f g => ?_⟩
  have hQ₀ : Q₀ ≤ Q i := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hi
  have hQU : Q_U ≤ Q i := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hi
  have hQV : Q_V ≤ Q i := le_trans (le_max_right _ _) hi
  have hQ1 : 1 ≤ Q i := le_trans hQ_V hQV
  set B : ℝ≥0∞ := ENNReal.ofReal (A * Q i ^ (-(D.μ / 2))) *
    eLpNorm f (ENNReal.ofReal p) Measure.count * eLpNorm g (ENNReal.ofReal q) Measure.count
    with hB
  -- the bound for `U`
  have bU : eLpNorm (U i f g) (ENNReal.ofReal r) Measure.count ≤ B := by
    refine (h_U i hQU f g).trans ?_
    refine mul_le_mul' (mul_le_mul' (ofReal_mul_rpow_le hQ1 hC_U.le (by linarith) ?_) le_rfl) le_rfl
    linarith [D.μ_le_E_U]
  -- the bound for `H₀`
  have b0 : eLpNorm (H₀ i f g) (ENNReal.ofReal r) Measure.count ≤ B := by
    refine (h₀ i hQ₀ f g).trans ?_
    refine mul_le_mul' (mul_le_mul' (ofReal_mul_rpow_le hQ1 hC₀.le (by linarith) ?_) le_rfl) le_rfl
    linarith [D.μ_le_E₀]
  -- the bounds for `V_j`
  have bV : ∀ j ∈ Finset.Icc 1 D.M,
      eLpNorm (V j i f g) (ENNReal.ofReal r) Measure.count ≤ B := by
    intro j hj
    have hj' := Finset.mem_Icc.1 hj
    refine (h_V i hQV j hj f g).trans ?_
    refine mul_le_mul' (mul_le_mul' (ofReal_mul_rpow_le hQ1 hC_V.le (by linarith) ?_) le_rfl) le_rfl
    linarith [D.μ_le_sigma j hj'.1 hj'.2]
  -- the quasi-triangle inequality over `t = {0} ∪ [1, M]`
  let X : ℕ → ℤ → ℂ := fun k => if k = 0 then H₀ i f g else V k i f g
  have h0t : (0 : ℕ) ∉ Finset.Icc 1 D.M := by simp
  have hsumX : ∑ k ∈ t, X k = Hmod i f g := by
    rw [ht, Finset.sum_insert h0t, hdecomp i f g]
    have : ∑ k ∈ Finset.Icc 1 D.M, X k = ∑ k ∈ Finset.Icc 1 D.M, V k i f g := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have : k ≠ 0 := by have := (Finset.mem_Icc.1 hk).1; omega
      simp [X, this]
    rw [this]
    simp [X]
  have hXb : ∀ k ∈ t, eLpNorm (X k) (ENNReal.ofReal r) Measure.count ≤ B := by
    intro k hk
    rcases Finset.mem_insert.1 hk with rfl | hk
    · simpa [X] using b0
    · have : k ≠ 0 := by have := (Finset.mem_Icc.1 hk).1; omega
      simpa [X, this] using bV k hk
  have hH := eLpNorm_sum_le_card_mul t X hr0 hr1.le hXb
  rw [hsumX] at hH
  -- collect
  have hcE : ((t.card : ℝ≥0∞)) ^ (1 / r) = ENNReal.ofReal c := by
    rw [hc, ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) (by positivity),
      ENNReal.ofReal_natCast]
  have hfin : ENNReal.ofReal ((c + 1) * A * Q i ^ (-(D.μ / 2))) =
      ENNReal.ofReal c * ENNReal.ofReal (A * Q i ^ (-(D.μ / 2))) +
        ENNReal.ofReal (A * Q i ^ (-(D.μ / 2))) := by
    have hnn : 0 ≤ A * Q i ^ (-(D.μ / 2)) :=
      mul_nonneg hApos.le (Real.rpow_nonneg (zero_le_one.trans hQ1) _)
    rw [show (c + 1) * A * Q i ^ (-(D.μ / 2)) = c * (A * Q i ^ (-(D.μ / 2))) +
      A * Q i ^ (-(D.μ / 2)) by ring, ENNReal.ofReal_add (mul_nonneg hc0 hnn) hnn,
      ENNReal.ofReal_mul hc0]
  calc eLpNorm (Hmod i f g) (ENNReal.ofReal r) Measure.count +
        eLpNorm (U i f g) (ENNReal.ofReal r) Measure.count
      ≤ ENNReal.ofReal c * B + B := by
        rw [hcE] at hH
        exact add_le_add hH bU
    _ = ENNReal.ofReal ((c + 1) * A * Q i ^ (-(D.μ / 2))) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count := by
        rw [hfin, hB]
        ring

/-- **N52, the case `r < 1`, conditional on the raw estimates.**
From the three estimates for each group `V_j` (`1 ≤ j ≤ M`), the initial-group bound, the `U`-bound
at `τ = 3/4` (N26, exponent `-3/8 + ε`) and the progression bound at `(p₀, q₀, r₀)` (N24,
exponent `1/r₀ - 1 + ε`), one gets `‖H_mod‖_r + ‖U‖_r ≲ Q^{-μ/2} ‖f‖_p ‖g‖_q`. -/
theorem complexity_decay_of_estimates
    (Hmod H₀ U : ι → (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ))
    (V : ℕ → ι → (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ)) (Q : ι → ℝ)
    (D : ExponentData p q r)
    (hdecomp : ∀ i (f g : ℤ →₀ ℂ), Hmod i f g = H₀ i f g + ∑ j ∈ Finset.Icc 1 D.M, V j i f g)
    (hH₀ : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (H₀ i f g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ (D.τ 0 / r - D.θ / 4 + ε)) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count)
    (hE2 : ∀ j, 1 ≤ j → j ≤ D.M → ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧
      ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
        eLpNorm (V j i f g) (ENNReal.ofReal 1) Measure.count ≤
          ENNReal.ofReal (C * Q i ^ (-(D.τ (j - 1) / 2) + ε)) *
            eLpNorm f (ENNReal.ofReal 2) Measure.count *
              eLpNorm g (ENNReal.ofReal 2) Measure.count)
    (hE3 : ∀ j, 1 ≤ j → j ≤ D.M → ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧
      ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
        eLpNorm (V j i f g) (ENNReal.ofReal 1) Measure.count ≤
          ENNReal.ofReal (C * Q i ^ ε) *
            eLpNorm f (ENNReal.ofReal (1 / (1 - D.δ))) Measure.count *
              eLpNorm g (ENNReal.ofReal (1 / D.δ)) Measure.count)
    (hE4 : ∀ j, 1 ≤ j → j ≤ D.M → ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧
      ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
        eLpNorm (V j i f g) (ENNReal.ofReal (1 / (2 - 2 * D.δ))) Measure.count ≤
          ENNReal.ofReal (C * Q i ^ (2 * D.τ j * (1 - D.δ) + ε)) *
            eLpNorm f (ENNReal.ofReal (1 / (1 - D.δ))) Measure.count *
              eLpNorm g (ENNReal.ofReal (1 / (1 - D.δ))) Measure.count)
    (hU₂ : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (U i f g) (ENNReal.ofReal 1) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ (-(3 / 8 : ℝ) + ε)) *
          eLpNorm f (ENNReal.ofReal 2) Measure.count * eLpNorm g (ENNReal.ofReal 2) Measure.count)
    (hU₀ : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (U i f g) (ENNReal.ofReal D.r₀) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ (1 / D.r₀ - 1 + ε)) *
          eLpNorm f (ENNReal.ofReal D.p₀) Measure.count *
            eLpNorm g (ENNReal.ofReal D.q₀) Measure.count) :
    ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i, Q₁ ≤ Q i → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (Hmod i f g) (ENNReal.ofReal r) Measure.count +
          eLpNorm (U i f g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * Q i ^ (-(D.μ / 2))) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count :=
  complexity_decay_of_group_decays Hmod H₀ U V Q D hdecomp hH₀
    (fun j h1 h2 => group_decay_of_estimates (V j) Q D j (hE2 j h1 h2) (hE3 j h1 h2)
      (hE4 j h1 h2))
    (power_decay_quasiBanach_of_estimates U Q D hU₂ hU₀)

end PrimeBHT.GroupDecay
