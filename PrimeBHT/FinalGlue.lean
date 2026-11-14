module

public import PrimeBHT.FinalGlue.Estimates

/-!
# S21: the N52 glue (case `r < 1`)

`complexity_decay_of_key0_of_bhtSmooth` derives, from the base nodes, every hypothesis that
`GroupDecay.complexity_decay_of_estimates` takes (E2, E3, E4, the initial group, the `U` bounds,
the decomposition `Hmod = H₀ + ∑ V_j`), so that the only remaining hypotheses are

* `Key0Statement χ` (the anchor `p:key0`, used at `τ ∈ {τ₀, …, τ_{M-1}, 3/4}`), and
* `BHTSmooth χ` (the anchor X1) at exactly two tuples:
  `(p₀, q₀, r₀)` (the auxiliary BHT-range tuple of the exponent data, for the `U`-bound) and the
  Banach tuple `(1/(1-δ), 1/δ, 1)` (for `e:thirdinterp`).
  X1 at the target `(p, q, r)` itself is not needed.

The conclusion is stated for the operators `Decomposition.Hmod` and `Decomposition.Utail` at `τ = 3/4`.
-/

@[expose] public noncomputable section

open MeasureTheory PrimeBHT.Kernel PrimeBHT.Decomposition PrimeBHT.Exponents PrimeBHT.FinalAssembly
open scoped ENNReal

namespace PrimeBHT.FinalGlue

open PrimeBHT.Progression (BHTSmooth)

/-! ## The decomposition identity `Hmod_{τ_M} = Hmod_{τ_0} + ∑_{m=1}^M U_{τ_{m-1}}^{J'_m}` -/

theorem hmod_step {χ : ℝ → ℝ} {τ τ' : ℝ} (hττ' : τ ≤ τ') (j J : ℕ)
    (hb : (bQ ((2 : ℝ) ^ j) : ℝ) ≤ ((2 : ℝ) ^ j) ^ τ) (f g : ℤ → ℂ) (x : ℤ) :
    Hmod χ τ' J j f g x =
      Hmod χ τ J j f g x + Utail χ τ (min J (⌈((2 : ℝ) ^ j) ^ τ'⌉₊ - 1)) j f g x := by
  unfold Hmod Utail
  have hQ1 := one_le_two_pow_real j
  have hQ0 : (0 : ℝ) < (2 : ℝ) ^ j := by linarith
  have hpos' : 1 ≤ ⌈((2 : ℝ) ^ j) ^ τ'⌉₊ := Nat.one_le_ceil_iff.2 (Real.rpow_pos_of_pos hQ0 _)
  have hmono : ((2 : ℝ) ^ j) ^ τ ≤ ((2 : ℝ) ^ j) ^ τ' :=
    Real.rpow_le_rpow_of_exponent_le hQ1 hττ'
  rw [← Finset.sum_union]
  · refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, le_min_iff, Nat.ceil_le]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases h4 : (k : ℝ) < ((2 : ℝ) ^ j) ^ τ
      · exact Or.inl ⟨⟨h1, h2⟩, h4⟩
      · right
        have : k < ⌈((2 : ℝ) ^ j) ^ τ'⌉₊ := Nat.lt_ceil.2 h3
        exact ⟨not_lt.1 h4, h2, by omega⟩
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨⟨h1, h2⟩, lt_of_lt_of_le h3 hmono⟩
      · refine ⟨⟨?_, h2⟩, Nat.lt_ceil.1 (by omega)⟩
        have : (bQ ((2 : ℝ) ^ j) : ℝ) ≤ k := hb.trans h1
        exact_mod_cast this
  · rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.ceil_le] at hk1 hk2
    exact absurd hk1.2 (not_lt.2 hk2.1)

theorem tau_zero_le {p q r : ℝ} (D : ExponentData p q r) : ∀ m, m ≤ D.M → D.τ 0 ≤ D.τ m := by
  intro m
  induction m with
  | zero => intro _; exact le_rfl
  | succ m ih => intro hm; exact (ih (by omega)).trans (D.τ_lt_succ m (by omega)).le

theorem hmod_eq_sum {χ : ℝ → ℝ} {p q r : ℝ} (D : ExponentData p q r) (j J : ℕ)
    (hb : (bQ ((2 : ℝ) ^ j) : ℝ) ≤ ((2 : ℝ) ^ j) ^ D.τ 0) (f g : ℤ → ℂ) (x : ℤ) :
    ∀ m, m ≤ D.M → Hmod χ (D.τ m) J j f g x = Hmod χ (D.τ 0) J j f g x +
      ∑ m' ∈ Finset.Icc 1 m,
        Utail χ (D.τ (m' - 1)) (min J (⌈((2 : ℝ) ^ j) ^ D.τ m'⌉₊ - 1)) j f g x := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    rw [Finset.sum_Icc_succ_top (by omega), ← add_assoc, ← ih (by omega)]
    have hbm : (bQ ((2 : ℝ) ^ j) : ℝ) ≤ ((2 : ℝ) ^ j) ^ D.τ m :=
      hb.trans (Real.rpow_le_rpow_of_exponent_le (one_le_two_pow_real j)
        (tau_zero_le D m (by omega)))
    rw [hmod_step (D.τ_lt_succ m (by omega)).le j J hbm]
    simp only [Nat.add_sub_cancel]

/-! ## The families of operators -/

/-- The group `V_{Q,m} = U^{J'}_{Q;τ_{m-1}}`, `J' = min(J, ⌈Q^{τ_m}⌉ - 1)`, `i = (j, J)`, `Q = 2^j`. -/
def Vop (χ : ℝ → ℝ) {p q r : ℝ} (D : ExponentData p q r) (m : ℕ) (i : ℕ × ℕ) :
    (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ) :=
  blk χ i.1 (Finset.Icc ⌈((2 : ℝ) ^ i.1) ^ D.τ (m - 1)⌉₊
    (min i.2 (⌈((2 : ℝ) ^ i.1) ^ D.τ m⌉₊ - 1)))

/-- The initial group `H₀ = ∑_{b_Q ≤ k ≤ J, k < Q^{τ_0}} T_k^Q`. -/
def H0op (χ : ℝ → ℝ) {p q r : ℝ} (D : ExponentData p q r) (i : ℕ × ℕ) :
    (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ) :=
  blk χ i.1 ((Finset.Icc (bQ ((2 : ℝ) ^ i.1)) i.2).filter
    (fun k : ℕ => (k : ℝ) < ((2 : ℝ) ^ i.1) ^ D.τ 0))

/-- `H₀ + ∑_{m=1}^M V_{Q,m}` (equal to `H_{mod;3/4}` once `b_Q ≤ Q^{τ_0}`). -/
def Hop (χ : ℝ → ℝ) {p q r : ℝ} (D : ExponentData p q r) (i : ℕ × ℕ) :
    (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ) :=
  H0op χ D i + ∑ m ∈ Finset.Icc 1 D.M, Vop χ D m i

/-- The tail `U^J_{Q;3/4}`. -/
def Uop (χ : ℝ → ℝ) (i : ℕ × ℕ) : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ) :=
  blk χ i.1 (Finset.Icc ⌈((2 : ℝ) ^ i.1) ^ (3 / 4 : ℝ)⌉₊ i.2)

theorem Hop_eq_Hmod {χ : ℝ → ℝ} (hχ : IsCutoff χ) {p q r : ℝ} (D : ExponentData p q r) (j J : ℕ)
    (hb : (bQ ((2 : ℝ) ^ j) : ℝ) ≤ ((2 : ℝ) ^ j) ^ D.τ 0) (f g : ℤ →₀ ℂ) :
    Hop χ D (j, J) f g = Hmod χ (3 / 4) J j ⇑f ⇑g := by
  funext x
  have hM : (3 / 4 : ℝ) = D.τ D.M := D.τ_M.symm
  rw [hM, hmod_eq_sum D j J hb ⇑f ⇑g x D.M le_rfl]
  simp only [Hop, LinearMap.add_apply, LinearMap.sum_apply, Pi.add_apply, Finset.sum_apply]
  have e0 : H0op χ D (j, J) f g x = Hmod χ (D.τ 0) J j ⇑f ⇑g x := by
    rw [Hmod_eq_blk hχ]; rfl
  have eV : ∀ m, Vop χ D m (j, J) f g x =
      Utail χ (D.τ (m - 1)) (min J (⌈((2 : ℝ) ^ j) ^ D.τ m⌉₊ - 1)) j ⇑f ⇑g x := by
    intro m; rw [Utail_eq_blk hχ]; rfl
  rw [e0, Finset.sum_congr rfl (fun m _ => eV m)]

/-! ## The exponent bounds `0 < τ_m < 1` -/

theorem tau_pos_lt {p q r : ℝ} (D : ExponentData p q r) (m : ℕ) : 0 < D.τ m ∧ D.τ m < 1 := by
  have hp' : 0 < D.p' := one_div_pos.1 (lt_trans (mul_pos two_pos D.t_pos) D.two_t_lt)
  have hρ : 0 < D.ρ := lt_trans (mul_pos (mul_pos two_pos D.t_pos) hp') D.ρ_gt
  rw [D.τ_def m]
  refine ⟨mul_pos (by norm_num) (pow_pos hρ _), ?_⟩
  have := pow_le_one₀ hρ.le D.ρ_lt_one.le (n := D.M - m)
  linarith

/-! ## The main theorem -/

/-- **N52, the case `r < 1`, from the base nodes.**  Let `D` be the exponent data of `(p, q, r)`
(`r < 1`, `p ≤ q`).  Assume

* `hK : Key0Statement χ` (anchor `p:key0`; applied at `τ_{m-1}` for `1 ≤ m ≤ M` and at `τ = 3/4`),
* `hX₀ : BHTSmooth χ p₀ q₀ r₀ C₀` (anchor X1 at the auxiliary tuple of `D`),
* `hX₁ : BHTSmooth χ (1/(1-δ)) (1/δ) 1 C₁` (anchor X1 at the Banach tuple of `e:thirdinterp`).

Then there are `σ > 0`, `C`, `Q₁` with `‖H_{mod;3/4}‖_r + ‖U_{Q;3/4}‖_r ≤ C Q^{-σ} ‖f‖_p ‖g‖_q`
for dyadic `Q = 2^j ≥ Q₁`, all `J`, all finitely supported `f, g`.
Everything else (E2, E3, E4, `e:negpower`, the decomposition) is derived. -/
theorem complexity_decay_of_key0_of_bhtSmooth {χ : ℝ → ℝ} (hχ : IsCutoff χ)
    (hK : Key0Statement χ) {p q r : ℝ} (D : ExponentData p q r) {C₀ C₁ : ℝ}
    (hX₀ : BHTSmooth χ D.p₀ D.q₀ D.r₀ C₀)
    (hX₁ : BHTSmooth χ (1 / (1 - D.δ)) (1 / D.δ) 1 C₁) :
    ∃ σ C Q₁ : ℝ, 0 < σ ∧ 0 < C ∧ ∀ j J : ℕ, Q₁ ≤ (2 : ℝ) ^ j → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (Hmod χ (3 / 4) J j ⇑f ⇑g) (ENNReal.ofReal r) Measure.count +
          eLpNorm (Utail χ (3 / 4) J j ⇑f ⇑g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-σ)) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count := by
  have hδ0 : 0 < D.δ := D.δ_pos
  have hδhalf : D.δ < 1 / 2 := lt_of_lt_of_le D.δ_lt (min_le_left _ _)
  have hδ1 : D.δ < 1 := by linarith
  have h1δ : 0 < 1 - D.δ := by linarith
  have hr₀ : 0 < D.r₀ := lt_trans (by norm_num) D.two_thirds_lt_r₀
  have hp₀ : 0 < D.p₀ := lt_trans one_pos D.one_lt_p₀
  have hq₀ : 0 < D.q₀ := lt_trans one_pos D.one_lt_q₀
  have hone : (1 : ℝ) < 1 / (1 - D.δ) := one_lt_one_div h1δ (by linarith)
  have hQ : ∀ i : ℕ × ℕ, (1 : ℝ) ≤ (2 : ℝ) ^ i.1 := fun i => one_le_two_pow_real i.1
  have hqpos : ∀ i : ℕ × ℕ, (0 : ℝ) < (2 : ℝ) ^ i.1 := fun i => by linarith [hQ i]
  have hceil : ∀ (i : ℕ × ℕ) (τ : ℝ), 1 ≤ ⌈((2 : ℝ) ^ i.1) ^ τ⌉₊ := fun i τ =>
    Nat.one_le_ceil_iff.2 (Real.rpow_pos_of_pos (hqpos i) _)
  -- the estimates
  have hH₀ : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i : ℕ × ℕ, Q₁ ≤ (2 : ℝ) ^ i.1 →
      ∀ f g : ℤ →₀ ℂ,
      eLpNorm (H0op χ D i f g) (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ i.1) ^ (D.τ 0 / r - D.θ / 4 + ε)) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count := by
    intro ε hε
    obtain ⟨C, Q₁, hC, h⟩ := blk_initial_decay hχ D hε
    exact ⟨C, Q₁, hC, fun i hi f g => h i.1 i.2 hi f g⟩
  have hE2 : ∀ m, 1 ≤ m → m ≤ D.M → ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧
      ∀ i : ℕ × ℕ, Q₁ ≤ (2 : ℝ) ^ i.1 → ∀ f g : ℤ →₀ ℂ,
        eLpNorm (Vop χ D m i f g) (ENNReal.ofReal 1) Measure.count ≤
          ENNReal.ofReal (C * ((2 : ℝ) ^ i.1) ^ (-(D.τ (m - 1) / 2) + ε)) *
            eLpNorm f (ENNReal.ofReal 2) Measure.count *
              eLpNorm g (ENNReal.ofReal 2) Measure.count := by
    intro m _ _ ε hε
    obtain ⟨C, Q₁, hC, h⟩ := blk_tail_decay_of_key0 hK hχ (tau_pos_lt D (m - 1)).1
      (tau_pos_lt D (m - 1)).2 hε
    exact ⟨C, Q₁, hC, fun i hi f g => h i.1 _ hi f g⟩
  have hE3 : ∀ m, 1 ≤ m → m ≤ D.M → ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧
      ∀ i : ℕ × ℕ, Q₁ ≤ (2 : ℝ) ^ i.1 → ∀ f g : ℤ →₀ ℂ,
        eLpNorm (Vop χ D m i f g) (ENNReal.ofReal 1) Measure.count ≤
          ENNReal.ofReal (C * ((2 : ℝ) ^ i.1) ^ ε) *
            eLpNorm f (ENNReal.ofReal (1 / (1 - D.δ))) Measure.count *
              eLpNorm g (ENNReal.ofReal (1 / D.δ)) Measure.count := by
    intro m _ _ ε hε
    obtain ⟨C, hC, h⟩ := blk_progression_of_bhtSmooth hχ (one_div_pos.2 h1δ) (one_div_pos.2 hδ0)
      one_pos (by rw [one_div_one_div, one_div_one_div]; ring) hX₁ hε
    have e : max (1 / (1 : ℝ) - 1) 0 + ε = ε := by norm_num
    rw [e] at h
    exact ⟨C, 1, hC, fun i _ f g => h i.1 _ _ (hceil i _) f g⟩
  have hE4 : ∀ m, 1 ≤ m → m ≤ D.M → ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧
      ∀ i : ℕ × ℕ, Q₁ ≤ (2 : ℝ) ^ i.1 → ∀ f g : ℤ →₀ ℂ,
        eLpNorm (Vop χ D m i f g) (ENNReal.ofReal (1 / (2 - 2 * D.δ))) Measure.count ≤
          ENNReal.ofReal (C * ((2 : ℝ) ^ i.1) ^ (2 * D.τ m * (1 - D.δ) + ε)) *
            eLpNorm f (ENNReal.ofReal (1 / (1 - D.δ))) Measure.count *
              eLpNorm g (ENNReal.ofReal (1 / (1 - D.δ))) Measure.count := by
    intro m _ _ ε hε
    obtain ⟨C, hC, h⟩ := blk_rough_decay hχ (p := 1 / (1 - D.δ)) (q := 1 / (1 - D.δ))
      (r := 1 / (2 - 2 * D.δ)) (c := D.τ m) hone hone
      (by rw [one_div_one_div, one_div_one_div]; ring)
      ((div_le_one (by linarith)).2 (by linarith)) hε
    have e : D.τ m * (1 / (1 / (2 - 2 * D.δ))) + ε = 2 * D.τ m * (1 - D.δ) + ε := by
      rw [one_div_one_div]; ring
    rw [e] at h
    refine ⟨C, 1, hC, fun i _ f g => h i.1 _ ?_ f g⟩
    exact card_Icc_le_rpow (Real.rpow_pos_of_pos (hqpos i) _) (hceil i _) (min_le_right _ _)
  have hU₂ : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i : ℕ × ℕ, Q₁ ≤ (2 : ℝ) ^ i.1 →
      ∀ f g : ℤ →₀ ℂ,
      eLpNorm (Uop χ i f g) (ENNReal.ofReal 1) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ i.1) ^ (-(3 / 8 : ℝ) + ε)) *
          eLpNorm f (ENNReal.ofReal 2) Measure.count *
            eLpNorm g (ENNReal.ofReal 2) Measure.count := by
    intro ε hε
    obtain ⟨C, Q₁, hC, h⟩ := blk_tail_decay_of_key0 hK hχ (τ := 3 / 4) (by norm_num)
      (by norm_num) hε
    have e : -((3 / 4 : ℝ) / 2) + ε = -(3 / 8 : ℝ) + ε := by ring
    rw [e] at h
    exact ⟨C, Q₁, hC, fun i hi f g => h i.1 i.2 hi f g⟩
  have hU₀ : ∀ ε : ℝ, 0 < ε → ∃ C Q₁ : ℝ, 0 < C ∧ ∀ i : ℕ × ℕ, Q₁ ≤ (2 : ℝ) ^ i.1 →
      ∀ f g : ℤ →₀ ℂ,
      eLpNorm (Uop χ i f g) (ENNReal.ofReal D.r₀) Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ i.1) ^ (1 / D.r₀ - 1 + ε)) *
          eLpNorm f (ENNReal.ofReal D.p₀) Measure.count *
            eLpNorm g (ENNReal.ofReal D.q₀) Measure.count := by
    intro ε hε
    obtain ⟨C, hC, h⟩ := blk_progression_of_bhtSmooth hχ hp₀ hq₀ hr₀
      D.inv_p₀_add_inv_q₀.symm hX₀ hε
    have hnn : 0 ≤ 1 / D.r₀ - 1 := by
      have := one_lt_one_div hr₀ D.r₀_lt_one
      linarith
    rw [max_eq_left hnn] at h
    exact ⟨C, 1, hC, fun i _ f g => h i.1 _ _ (hceil i _) f g⟩
  obtain ⟨C, Q₁, hC, h⟩ := PrimeBHT.GroupDecay.complexity_decay_of_estimates
    (Hop χ D) (H0op χ D) (Uop χ) (fun m i => Vop χ D m i) (fun i : ℕ × ℕ => (2 : ℝ) ^ i.1) D
    (fun i f g => by simp only [Hop, LinearMap.add_apply, LinearMap.sum_apply])
    hH₀ hE2 hE3 hE4 hU₂ hU₀
  obtain ⟨j₀, hj₀⟩ := exists_bQ_le_rpow D.τ_zero_pos
  refine ⟨D.μ / 2, C, max Q₁ ((2 : ℝ) ^ (j₀ + 1)), half_pos D.μ_pos, hC, fun j J hj f g => ?_⟩
  have hj₁ : Q₁ ≤ (2 : ℝ) ^ j := (le_max_left _ _).trans hj
  have hj₂ : j₀ < j := by
    have := (le_max_right _ _).trans hj
    have := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 this
    omega
  have key := h (j, J) hj₁ f g
  rw [Hop_eq_Hmod hχ D j J (hj₀ j hj₂) f g] at key
  have eU : Uop χ (j, J) f g = Utail χ (3 / 4) J j ⇑f ⇑g := (Utail_eq_blk hχ _ J j f g).symm
  rw [eU] at key
  exact key

/-! ## The form `‖H_mod + U‖_r ≤ C_H Q^{-σ} ‖f‖_p ‖g‖_q` (the shape of `FinalSum`'s `hH`) -/

theorem eLpNorm_add_le_two_rpow {A B : ℤ → ℂ} {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    eLpNorm (A + B) (ENNReal.ofReal r) Measure.count ≤
      (2 : ℝ≥0∞) ^ (1 / r) * (eLpNorm A (ENNReal.ofReal r) Measure.count +
        eLpNorm B (ENNReal.ofReal r) Measure.count) := by
  have h := PrimeBHT.GroupDecay.eLpNorm_sum_le_card_mul (Finset.range 2)
    (fun k => if k = 0 then A else B) hr hr1
    (B := eLpNorm A (ENNReal.ofReal r) Measure.count + eLpNorm B (ENNReal.ofReal r) Measure.count)
    (by
      intro k _
      by_cases h0 : k = 0
      · simp only [h0, ite_true]; exact le_self_add
      · simp only [h0, ite_false]; exact le_add_self)
  simpa [Finset.sum_range_succ] using h

/-- Same hypotheses as `complexity_decay_of_key0_of_bhtSmooth`; conclusion for the function
`H_{mod;3/4} + U_{Q;3/4}` and all `j > j₁` (the shape of the hypothesis `hH` of
`FinalSum.eLpNorm_HJ_le_assemblyConst_of_estimates` with `τ = 3/4`). -/
theorem complexity_decay_add_of_key0_of_bhtSmooth {χ : ℝ → ℝ} (hχ : IsCutoff χ)
    (hK : Key0Statement χ) {p q r : ℝ} (D : ExponentData p q r) {C₀ C₁ : ℝ}
    (hX₀ : BHTSmooth χ D.p₀ D.q₀ D.r₀ C₀)
    (hX₁ : BHTSmooth χ (1 / (1 - D.δ)) (1 / D.δ) 1 C₁) :
    ∃ σ C : ℝ, ∃ j₁ : ℕ, 0 < σ ∧ 0 < C ∧ ∀ j J : ℕ, j₁ < j → ∀ f g : ℤ →₀ ℂ,
      eLpNorm (Hmod χ (3 / 4) J j ⇑f ⇑g + Utail χ (3 / 4) J j ⇑f ⇑g) (ENNReal.ofReal r)
          Measure.count ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-σ)) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count := by
  obtain ⟨σ, C, Q₁, hσ, hC, h⟩ := complexity_decay_of_key0_of_bhtSmooth hχ hK D hX₀ hX₁
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt Q₁ (by norm_num : (1 : ℝ) < 2)
  obtain ⟨hr0, hr1⟩ := PrimeBHT.GroupDecay.exponentData_r_mem D
  refine ⟨σ, 2 ^ (1 / r) * C, n, hσ, by positivity, fun j J hj f g => ?_⟩
  have hQ : Q₁ ≤ (2 : ℝ) ^ j := hn.le.trans (pow_le_pow_right₀ (by norm_num) hj.le)
  have h1 := eLpNorm_add_le_two_rpow (A := Hmod χ (3 / 4) J j ⇑f ⇑g)
    (B := Utail χ (3 / 4) J j ⇑f ⇑g) hr0 hr1.le
  have h2 := h j J hQ f g
  have e2 : (2 : ℝ≥0∞) ^ (1 / r) = ENNReal.ofReal ((2 : ℝ) ^ (1 / r)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by positivity), ENNReal.ofReal_ofNat]
  have hnn : 0 ≤ C * ((2 : ℝ) ^ j) ^ (-σ) :=
    mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)
  calc eLpNorm (Hmod χ (3 / 4) J j ⇑f ⇑g + Utail χ (3 / 4) J j ⇑f ⇑g) (ENNReal.ofReal r)
          Measure.count
      ≤ (2 : ℝ≥0∞) ^ (1 / r) * (eLpNorm (Hmod χ (3 / 4) J j ⇑f ⇑g) (ENNReal.ofReal r)
          Measure.count + eLpNorm (Utail χ (3 / 4) J j ⇑f ⇑g) (ENNReal.ofReal r)
            Measure.count) := h1
    _ ≤ (2 : ℝ≥0∞) ^ (1 / r) * (ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ (-σ)) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count) := mul_le_mul' le_rfl h2
    _ = ENNReal.ofReal (2 ^ (1 / r) * C * ((2 : ℝ) ^ j) ^ (-σ)) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count := by
        rw [e2, mul_assoc (2 ^ (1 / r) : ℝ), ENNReal.ofReal_mul (p := (2 : ℝ) ^ (1 / r)) (by positivity)]
        ring

end PrimeBHT.FinalGlue
