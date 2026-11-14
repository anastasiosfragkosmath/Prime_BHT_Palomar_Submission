module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# V16 counting lemma (X2, blueprint B8, B9 and the explicit region of B6'/B10/B11)

Pure real analysis; no time-frequency theory. The source is `docs/audits/X2-V16B-route-check.md` §2.3.

## Main results

* **B9 (`min` tricks).** `min_mul_le_mul_min`: `min (c a) x ≤ c min a x` for `c ≥ 1`, `0 ≤ x`;
  `min_le_rpow_mul_min_one`: `min ε x ≤ ε^θ min 1 (x^(1-θ))` for `0 ≤ ε ≤ 1`, `0 ≤ x`, `θ ∈ [0,1]`;
  and the underlying `min_le_rpow_mul_rpow`: `min a x ≤ a^s x^(1-s)` for `a, x ≥ 0`, `s ∈ [0,1]`.
* **Two-sided geometric sum.** `sum_min_two_pow_le`: for `X, Y ≥ 0`, `c > 0` and every finite `S ⊆ ℤ`,
  `∑ k ∈ S, min (X 2^(k c)) (Y 2^(-(k c))) ≤ 2 √(X Y) / (1 - 2^(-c))`; `summable_min_two_pow` and
  `tsum_min_two_pow_le` are the `Summable`/`tsum` forms.
* **B8 (counting lemma).** With `levelTerm q A τ k = 2^k ∏_v min (A_v / A_τ) ((2^(-k) A_v)^(1/q_v))`
  and `levelExponent q s₀ v = s₀_v + (1 - s₀_v)/q_v`:
  `sum_levelTerm_le` (every finite sum), `summable_levelTerm`, `tsum_levelTerm_le` give the bound
  `(2/(1 - 2^(-c))) A_τ ∏_{v ≠ τ} (A_v/A_τ)^(g_v)`, `c = ∑_v d_v/q_v`, `g = levelExponent q s₀`;
  `sum_levelTerm_le_prod` and `tsum_levelTerm_le_prod` give the corollary `≤ (2/(1 - 2^(-c))) ∏_v A_v^(β_v)`
  for `∑ β = 1` and `β_v ≤ g_v` (`v ≠ τ`).
* **Explicit region.** `etaR R = 1/(16 R)`, `qPlus R = ((1+η)2, (1+η)2, (1+η)R)`, `qTau R θ τ` (the slot `τ`
  of `qPlus R` divided by `1 - θ`; `θ = 0` is the type of B10, `θ = η` the type of B11), and the explicit
  `countS R θ τ` (= `s⁰`), `countD R θ τ` (= `d`) satisfy, for `R ≥ 4`, `0 ≤ θ ≤ η`:
  `countSum` (`∑ (1 - s⁰_v)/q_v = 1`), `countS_add_mem`, `countS_sub_mem` (`s⁰ ± d ∈ [0,1]³`),
  `countC_ge` (`c ≥ 2/(5R)`), `countG_ge` (`g_v ≥ 1/2 + 1/(8R)` for `v ∈ {1,2}`, `g_3 ≥ 1/(4R)`; for
  `v ≠ τ`), and `le_regionBound` (every `β ∈ 𝒩_R` has `β_v` below these thresholds). The packaged result is
  `sum_levelTerm_le_region` (and `tsum_`, `summable_` forms): for `0 < A_v ≤ A_τ`,
  `∑ k ∈ S, levelTerm (qTau R θ τ) A τ k ≤ countConst R * ∏ v, A v ^ β v` with the constant
  `countConst R = 2/(1 - 2^(-2/(5R)))` depending on `R` only.

## Deviations from the audit (all strengthenings or corrections of numbers)

* B8's hypotheses `q_v > 1`, `s⁰ ∈ [0,1]³` and `A_v ≤ A_τ` are not needed for the finite-sum bound:
  `s⁰ = ((s⁰+d) + (s⁰-d))/2 ∈ [0,1]³` follows from `s⁰ ± d ∈ [0,1]³`, and `q` enters only through
  the `rpow` identities. `A_v ≤ A_τ` is used only for the corollary (it makes `(A_v/A_τ)^g ≤ (A_v/A_τ)^β`).
* The audit claims margins `≥ 0.18/R`. With the explicit choices of B8 and `η = θ = 1/(16R)` the geometric
  exponent is `c ≥ 0.44/R` (we prove `c ≥ 2/(5R)`); the slack of `g_v` over the region thresholds
  `1/2 + 1/(8R)` (`v ∈ {1,2}`), `1/(4R)` (`v = 3`) is about `1/(16R)` for `τ = 3` and larger otherwise.
  It is positive, which is all that is needed; the printed explicit `s⁰, d` of B8 work unchanged
  after the `η`, `θ` modifications (`σ` is the only quantity that changes).
* The region lemma is proved for every `θ ∈ [0, η]` (not only `θ = η`), since B10 uses the type `q⁺` (`θ = 0`)
  and B11 the type `q⁺_τ/(1-θ)` (`θ = η`); the case `R ≥ 4` is the standing assumption `R = 2 max(u,u') ≥ 4`.
-/

@[expose] public section

namespace PrimeBHT.TimeFrequency.X2.V16

/-! ### B9: two `min` tricks -/

/-- B9: `min (c a) x ≤ c min a x` for `c ≥ 1` and `0 ≤ x` (no sign condition on `a` is needed). -/
theorem min_mul_le_mul_min {c a x : ℝ} (hc : 1 ≤ c) (hx : 0 ≤ x) :
    min (c * a) x ≤ c * min a x := by
  rw [mul_min_of_nonneg _ _ (by linarith)]
  exact min_le_min le_rfl (by nlinarith)

/-- The geometric-mean bound `min a x ≤ a^s x^(1-s)` for `a, x ≥ 0` and `s ∈ [0,1]`. -/
theorem min_le_rpow_mul_rpow {a x s : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    min a x ≤ a ^ s * x ^ (1 - s) := by
  have hsum : s + (1 - s) ≠ 0 := by rw [add_sub_cancel]; exact one_ne_zero
  rcases le_total a x with h | h
  · rw [min_eq_left h]
    calc a = a ^ s * a ^ (1 - s) := by
          rw [← Real.rpow_add' ha hsum, add_sub_cancel, Real.rpow_one]
      _ ≤ a ^ s * x ^ (1 - s) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha h (by linarith)) (Real.rpow_nonneg ha s)
  · rw [min_eq_right h]
    calc x = x ^ s * x ^ (1 - s) := by
          rw [← Real.rpow_add' hx hsum, add_sub_cancel, Real.rpow_one]
      _ ≤ a ^ s * x ^ (1 - s) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx h hs0) (Real.rpow_nonneg hx _)

/-- B9: `min ε x ≤ ε^θ min 1 (x^(1-θ))` for `0 ≤ ε ≤ 1`, `0 ≤ x`, `θ ∈ [0,1]`. -/
theorem min_le_rpow_mul_min_one {ε x θ : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hx : 0 ≤ x)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    min ε x ≤ ε ^ θ * min 1 (x ^ (1 - θ)) := by
  rw [mul_min_of_nonneg _ _ (Real.rpow_nonneg hε0 θ)]
  refine le_min ?_ (min_le_rpow_mul_rpow hε0 hx hθ0 hθ1)
  calc min ε x ≤ ε := min_le_left _ _
    _ ≤ ε ^ θ := by simpa using Real.rpow_le_rpow_of_exponent_ge' hε0 hε1 hθ0 hθ1
    _ = ε ^ θ * 1 := (mul_one _).symm

/-! ### The two-sided geometric sum -/

/-- A finite sum of pairwise distinct powers of `r ∈ [0,1)` is at most `1/(1-r)`. -/
theorem sum_pow_le_of_injOn {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (S : Finset ℤ) (g : ℤ → ℕ)
    (hg : Set.InjOn g S) : ∑ k ∈ S, r ^ g k ≤ (1 - r)⁻¹ := by
  rw [← Finset.sum_image (f := fun j : ℕ => r ^ j) hg]
  calc _ ≤ ∑' j : ℕ, r ^ j :=
        (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (fun j _ => pow_nonneg hr0 j)
    _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1

/-- If `f k ≤ B r^(g k)` on `S` with `g` injective on `S`, then `∑_S f ≤ B/(1-r)`. -/
theorem sum_le_of_pow_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (S : Finset ℤ) (g : ℤ → ℕ)
    (hg : Set.InjOn g S) (f : ℤ → ℝ) {B : ℝ} (hB : 0 ≤ B) (hf : ∀ k ∈ S, f k ≤ B * r ^ g k) :
    ∑ k ∈ S, f k ≤ B / (1 - r) := by
  calc ∑ k ∈ S, f k ≤ ∑ k ∈ S, B * r ^ g k := Finset.sum_le_sum hf
    _ = B * ∑ k ∈ S, r ^ g k := (Finset.mul_sum _ _ _).symm
    _ ≤ B * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left (sum_pow_le_of_injOn hr0 hr1 S g hg) hB
    _ = B / (1 - r) := (div_eq_mul_inv B _).symm

/-- `2^(k c) = 2^(m c) (2^(-c))^(m-k)` for `k ≤ m`. -/
theorem rpow_two_mul_le {c : ℝ} (m k : ℤ) (h : k ≤ m) :
    (2 : ℝ) ^ ((k : ℝ) * c) = (2 : ℝ) ^ ((m : ℝ) * c) * ((2 : ℝ) ^ (-c)) ^ (m - k).toNat := by
  have hn : (((m - k).toNat : ℕ) : ℝ) = (m : ℝ) - k := by
    have : (((m - k).toNat : ℕ) : ℤ) = m - k := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num), hn]
  congr 1
  ring

/-- `2^(-(k c)) = 2^(-(m c)) (2^(-c))^(k-m)` for `m ≤ k`. -/
theorem rpow_two_neg_mul_le {c : ℝ} (m k : ℤ) (h : m ≤ k) :
    (2 : ℝ) ^ (-((k : ℝ) * c)) = (2 : ℝ) ^ (-((m : ℝ) * c)) * ((2 : ℝ) ^ (-c)) ^ (k - m).toNat := by
  have hn : (((k - m).toNat : ℕ) : ℝ) = (k : ℝ) - m := by
    have : (((k - m).toNat : ℕ) : ℤ) = k - m := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num), hn]
  congr 1
  ring

/-- The two-sided geometric sum, uniform over finite `S ⊆ ℤ`: `∑_{k∈S} min (X 2^(k c)) (Y 2^(-(k c)))
≤ 2 √(X Y)/(1 - 2^(-c))` for `X, Y ≥ 0`, `c > 0`. -/
theorem sum_min_two_pow_le {X Y c : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hc : 0 < c) (S : Finset ℤ) :
    ∑ k ∈ S, min (X * (2 : ℝ) ^ ((k : ℝ) * c)) (Y * (2 : ℝ) ^ (-((k : ℝ) * c))) ≤
      2 * Real.sqrt (X * Y) / (1 - (2 : ℝ) ^ (-c)) := by
  set r : ℝ := (2 : ℝ) ^ (-c) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsq : 0 ≤ Real.sqrt (X * Y) := Real.sqrt_nonneg _
  set a : ℤ → ℝ := fun k => X * (2 : ℝ) ^ ((k : ℝ) * c) with ha
  set b : ℤ → ℝ := fun k => Y * (2 : ℝ) ^ (-((k : ℝ) * c)) with hb
  have ha0 : ∀ k, 0 ≤ a k := fun k => mul_nonneg hX (Real.rpow_nonneg (by norm_num) _)
  have hb0 : ∀ k, 0 ≤ b k := fun k => mul_nonneg hY (Real.rpow_nonneg (by norm_num) _)
  have hab : ∀ k, a k * b k = X * Y := fun k => by
    simp only [ha, hb]
    have : (2 : ℝ) ^ ((k : ℝ) * c) * (2 : ℝ) ^ (-((k : ℝ) * c)) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    calc X * 2 ^ ((k : ℝ) * c) * (Y * 2 ^ (-((k : ℝ) * c)))
        = X * Y * (2 ^ ((k : ℝ) * c) * 2 ^ (-((k : ℝ) * c))) := by ring
      _ = X * Y := by rw [this, mul_one]
  change ∑ k ∈ S, min (a k) (b k) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not S (fun k => a k ≤ b k)]
  have h2 : 2 * Real.sqrt (X * Y) / (1 - r) =
      Real.sqrt (X * Y) / (1 - r) + Real.sqrt (X * Y) / (1 - r) := by ring
  rw [h2]
  have hnn : 0 ≤ Real.sqrt (X * Y) / (1 - r) := div_nonneg hsq (by linarith)
  refine add_le_add ?_ ?_
  · -- the part where `a k ≤ b k`
    set S₁ := S.filter (fun k => a k ≤ b k) with hS₁
    rcases S₁.eq_empty_or_nonempty with he | hne
    · rw [he]; simpa using hnn
    · set m := S₁.max' hne with hm
      have hmS : m ∈ S₁ := S₁.max'_mem hne
      have hle : ∀ k ∈ S₁, k ≤ m := fun k hk => S₁.le_max' k hk
      have ham : a m ≤ Real.sqrt (X * Y) := by
        have hm' : a m ≤ b m := (Finset.mem_filter.mp hmS).2
        have : a m ^ 2 ≤ X * Y := by rw [← hab m, sq]; exact mul_le_mul_of_nonneg_left hm' (ha0 m)
        exact (le_abs_self _).trans (Real.abs_le_sqrt this)
      refine sum_le_of_pow_bound hr0.le hr1 S₁ (fun k => (m - k).toNat) ?_ (fun k => min (a k) (b k))
        ((ha0 m).trans ham) ?_
      · intro k hk k' hk' hkk
        have h1 := hle k hk
        have h2 := hle k' hk'
        simp only at hkk
        omega
      · intro k hk
        have hk' : a k ≤ b k := (Finset.mem_filter.mp hk).2
        refine (min_le_left _ _).trans ?_
        have e : a k = a m * r ^ (m - k).toNat := by
          simp only [ha, hr]
          rw [rpow_two_mul_le (c := c) m k (hle k hk), mul_assoc]
        rw [e]
        exact mul_le_mul_of_nonneg_right ham (pow_nonneg hr0.le _)
  · -- the part where `b k < a k`
    set S₂ := S.filter (fun k => ¬ a k ≤ b k) with hS₂
    rcases S₂.eq_empty_or_nonempty with he | hne
    · rw [he]; simpa using hnn
    · set m := S₂.min' hne with hm
      have hmS : m ∈ S₂ := S₂.min'_mem hne
      have hle : ∀ k ∈ S₂, m ≤ k := fun k hk => S₂.min'_le k hk
      have hbm : b m ≤ Real.sqrt (X * Y) := by
        have hm' : b m < a m := not_le.mp (Finset.mem_filter.mp hmS).2
        have : b m ^ 2 ≤ X * Y := by
          rw [← hab m, sq, mul_comm (a m)]; exact mul_le_mul_of_nonneg_left hm'.le (hb0 m)
        exact (le_abs_self _).trans (Real.abs_le_sqrt this)
      refine sum_le_of_pow_bound hr0.le hr1 S₂ (fun k => (k - m).toNat) ?_ (fun k => min (a k) (b k))
        ((hb0 m).trans hbm) ?_
      · intro k hk k' hk' hkk
        have h1 := hle k hk
        have h2 := hle k' hk'
        simp only at hkk
        omega
      · intro k hk
        have hk' : ¬ a k ≤ b k := (Finset.mem_filter.mp hk).2
        refine (min_le_right _ _).trans ?_
        have e : b k = b m * r ^ (k - m).toNat := by
          simp only [hb, hr]
          rw [rpow_two_neg_mul_le (c := c) m k (hle k hk), mul_assoc]
        rw [e]
        exact mul_le_mul_of_nonneg_right hbm (pow_nonneg hr0.le _)

/-! ### B8: the counting lemma -/

/-- The level summand `F(k) = 2^k ∏_v min (A_v / A_τ) ((2^{-k} A_v)^{1/q_v})`. -/
noncomputable def levelTerm (q A : Fin 3 → ℝ) (τ : Fin 3) (k : ℤ) : ℝ :=
  (2 : ℝ) ^ k * ∏ v : Fin 3, min (A v / A τ) (((2 : ℝ) ^ (-k) * A v) ^ (1 / q v))

/-- The exponent `g_v = s_v + (1 - s_v) / q_v`. -/
noncomputable def levelExponent (q s : Fin 3 → ℝ) (v : Fin 3) : ℝ := s v + (1 - s v) / q v

/-- The constant `∏_v (A_v / A_τ)^{s_v} A_v^{(1 - s_v)/q_v}` attached to a parameter vector `s`. -/
noncomputable def levelConst (q A : Fin 3 → ℝ) (τ : Fin 3) (s : Fin 3 → ℝ) : ℝ :=
  ∏ v : Fin 3, ((A v / A τ) ^ (s v) * A v ^ ((1 - s v) / q v))

theorem levelConst_nonneg (q A : Fin 3 → ℝ) (τ : Fin 3) (s : Fin 3 → ℝ) (hA : ∀ v, 0 < A v) :
    0 ≤ levelConst q A τ s :=
  Finset.prod_nonneg fun v _ => mul_nonneg (Real.rpow_nonneg (div_nonneg (hA v).le (hA τ).le) _)
    (Real.rpow_nonneg (hA v).le _)

theorem levelTerm_nonneg (q A : Fin 3 → ℝ) (τ : Fin 3) (hA : ∀ v, 0 < A v) (k : ℤ) :
    0 ≤ levelTerm q A τ k :=
  mul_nonneg (zpow_nonneg (by norm_num) _) <| Finset.prod_nonneg fun v _ =>
    le_min (div_nonneg (hA v).le (hA τ).le)
      (Real.rpow_nonneg (mul_nonneg (zpow_nonneg (by norm_num) _) (hA v).le) _)

/-- Per-slot rewriting of `a^s ((2^(-k) A)^(1/q))^(1-s)`. -/
theorem factor_eq (k : ℤ) {a A q s : ℝ} (hA : 0 ≤ A) :
    a ^ s * (((2 : ℝ) ^ (-k) * A) ^ (1 / q)) ^ (1 - s) =
      (2 : ℝ) ^ (-(k : ℝ) * ((1 - s) / q)) * (a ^ s * A ^ ((1 - s) / q)) := by
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-k) := zpow_nonneg (by norm_num) _
  have e1 : (((2 : ℝ) ^ (-k) * A) ^ (1 / q)) ^ (1 - s) = ((2 : ℝ) ^ (-k) * A) ^ ((1 - s) / q) := by
    rw [← Real.rpow_mul (mul_nonneg h2 hA)]
    congr 1
    ring
  have e2 : ((2 : ℝ) ^ (-k)) ^ ((1 - s) / q) = (2 : ℝ) ^ (-(k : ℝ) * ((1 - s) / q)) := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_intCast]
    simp
  rw [e1, Real.mul_rpow h2 hA, e2]
  ring

/-- The pointwise bound `F(k) ≤ 2^{k(1 - Σ(1-s_v)/q_v)} ∏_v (A_v/A_τ)^{s_v} A_v^{(1-s_v)/q_v}`
for every `s ∈ [0,1]³`. -/
theorem levelTerm_le (q A : Fin 3 → ℝ) (τ : Fin 3) (hA : ∀ v, 0 < A v) (s : Fin 3 → ℝ)
    (hs0 : ∀ v, 0 ≤ s v) (hs1 : ∀ v, s v ≤ 1) (k : ℤ) :
    levelTerm q A τ k ≤
      (2 : ℝ) ^ ((k : ℝ) * (1 - ∑ v, (1 - s v) / q v)) * levelConst q A τ s := by
  have hmin : ∏ v : Fin 3, min (A v / A τ) (((2 : ℝ) ^ (-k) * A v) ^ (1 / q v)) ≤
      ∏ v : Fin 3, ((A v / A τ) ^ (s v) *
        (((2 : ℝ) ^ (-k) * A v) ^ (1 / q v)) ^ (1 - s v)) := by
    refine Finset.prod_le_prod₀ (fun v _ => le_min (div_nonneg (hA v).le (hA τ).le)
      (Real.rpow_nonneg (mul_nonneg (zpow_nonneg (by norm_num) _) (hA v).le) _)) fun v _ => ?_
    exact min_le_rpow_mul_rpow (div_nonneg (hA v).le (hA τ).le)
      (Real.rpow_nonneg (mul_nonneg (zpow_nonneg (by norm_num) _) (hA v).le) _) (hs0 v) (hs1 v)
  have hprod : ∏ v : Fin 3, ((A v / A τ) ^ (s v) *
        (((2 : ℝ) ^ (-k) * A v) ^ (1 / q v)) ^ (1 - s v)) =
      (2 : ℝ) ^ (-(k : ℝ) * ∑ v, (1 - s v) / q v) * levelConst q A τ s := by
    rw [levelConst, Finset.prod_congr rfl (fun v _ => factor_eq k
      (hA v).le), Finset.prod_mul_distrib,
      ← Real.rpow_sum_of_pos (by norm_num), ← Finset.mul_sum]
  calc levelTerm q A τ k = (2 : ℝ) ^ k * ∏ v : Fin 3,
        min (A v / A τ) (((2 : ℝ) ^ (-k) * A v) ^ (1 / q v)) := rfl
    _ ≤ (2 : ℝ) ^ k * _ := mul_le_mul_of_nonneg_left hmin (zpow_nonneg (by norm_num) _)
    _ = _ := by
      rw [hprod, ← mul_assoc, ← Real.rpow_intCast, ← Real.rpow_add (by norm_num)]
      congr 2
      ring

/-- Per-slot identity behind `√(B⁺ B⁻) = B⁰`. -/
theorem factor_mul_factor {a A q s d : ℝ} (ha : 0 < a) (hA : 0 < A) :
    (a ^ (s + d) * A ^ ((1 - (s + d)) / q)) * (a ^ (s - d) * A ^ ((1 - (s - d)) / q)) =
      (a ^ s * A ^ ((1 - s) / q)) * (a ^ s * A ^ ((1 - s) / q)) := by
  have e1 : a ^ (s + d) * a ^ (s - d) = a ^ s * a ^ s := by
    rw [← Real.rpow_add ha, ← Real.rpow_add ha]; congr 1; ring
  have e2 : A ^ ((1 - (s + d)) / q) * A ^ ((1 - (s - d)) / q) =
      A ^ ((1 - s) / q) * A ^ ((1 - s) / q) := by
    rw [← Real.rpow_add hA, ← Real.rpow_add hA]; congr 1; ring
  calc _ = (a ^ (s + d) * a ^ (s - d)) * (A ^ ((1 - (s + d)) / q) * A ^ ((1 - (s - d)) / q)) := by
        ring
    _ = _ := by rw [e1, e2]; ring

/-- `levelConst (s+d) * levelConst (s-d) = levelConst s ^ 2`. -/
theorem levelConst_add_mul_sub (q A : Fin 3 → ℝ) (τ : Fin 3) (hA : ∀ v, 0 < A v)
    (s d : Fin 3 → ℝ) :
    levelConst q A τ (s + d) * levelConst q A τ (s - d) =
      levelConst q A τ s * levelConst q A τ s := by
  unfold levelConst
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ =>
    factor_mul_factor (div_pos (hA v) (hA τ)) (hA v)

/-- If `∑ (1-s_v)/q_v = 1` then `levelConst s = A_τ ∏_{v≠τ} (A_v/A_τ)^(g_v)`. -/
theorem levelConst_eq (q A : Fin 3 → ℝ) (τ : Fin 3) (hA : ∀ v, 0 < A v) (s : Fin 3 → ℝ)
    (hs : ∑ v, (1 - s v) / q v = 1) :
    levelConst q A τ s =
      A τ * ∏ v ∈ Finset.univ.erase τ, (A v / A τ) ^ (levelExponent q s v) := by
  have hf : ∀ v, (A v / A τ) ^ (s v) * A v ^ ((1 - s v) / q v) =
      (A v / A τ) ^ (levelExponent q s v) * A τ ^ ((1 - s v) / q v) := by
    intro v
    have h1 : A v = (A v / A τ) * A τ := by field_simp [(hA τ).ne']
    have h2 : A v ^ ((1 - s v) / q v) = (A v / A τ) ^ ((1 - s v) / q v) * A τ ^ ((1 - s v) / q v) := by
      conv_lhs => rw [h1]
      exact Real.mul_rpow (div_nonneg (hA v).le (hA τ).le) (hA τ).le
    rw [h2, levelExponent, Real.rpow_add (div_pos (hA v) (hA τ))]
    ring
  have hτ : (A τ / A τ) ^ (levelExponent q s τ) = 1 := by
    rw [div_self (hA τ).ne', Real.one_rpow]
  unfold levelConst
  rw [Finset.prod_congr rfl fun v _ => hf v, Finset.prod_mul_distrib,
    ← Real.rpow_sum_of_pos (hA τ), hs, Real.rpow_one,
    ← Finset.mul_prod_erase Finset.univ (fun v => (A v / A τ) ^ (levelExponent q s v))
      (Finset.mem_univ τ), hτ, one_mul, mul_comm]

/-- **B8 (counting lemma), finite-sum form.** For `0 < A_v`, `∑ (1-s⁰_v)/q_v = 1`, `s⁰ ± d ∈ [0,1]³`
and `c = ∑ d_v/q_v > 0`, every finite sum of `levelTerm q A τ` is at most
`(2/(1-2^(-c))) A_τ ∏_{v≠τ} (A_v/A_τ)^(g_v)` with `g = levelExponent q s⁰`. -/
theorem sum_levelTerm_le (q A : Fin 3 → ℝ) (τ : Fin 3) (hA : ∀ v, 0 < A v)
    (s₀ d : Fin 3 → ℝ)
    (hsum : ∑ v, (1 - s₀ v) / q v = 1)
    (hp : ∀ v, s₀ v + d v ∈ Set.Icc (0 : ℝ) 1) (hm : ∀ v, s₀ v - d v ∈ Set.Icc (0 : ℝ) 1)
    (hc : 0 < ∑ v, d v / q v) (S : Finset ℤ) :
    ∑ k ∈ S, levelTerm q A τ k ≤
      2 / (1 - (2 : ℝ) ^ (-(∑ v, d v / q v))) *
        (A τ * ∏ v ∈ Finset.univ.erase τ, (A v / A τ) ^ (levelExponent q s₀ v)) := by
  set c : ℝ := ∑ v, d v / q v with hcdef
  have hEp : 1 - ∑ v, (1 - (s₀ + d) v) / q v = c := by
    have : ∑ v, (1 - (s₀ + d) v) / q v = ∑ v, (1 - s₀ v) / q v - ∑ v, d v / q v := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun v _ => by simp only [Pi.add_apply]; ring
    rw [this, hsum]; ring
  have hEm : 1 - ∑ v, (1 - (s₀ - d) v) / q v = -c := by
    have : ∑ v, (1 - (s₀ - d) v) / q v = ∑ v, (1 - s₀ v) / q v + ∑ v, d v / q v := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun v _ => by simp only [Pi.sub_apply]; ring
    rw [this, hsum]; ring
  set Bp := levelConst q A τ (s₀ + d) with hBp
  set Bm := levelConst q A τ (s₀ - d) with hBm
  set B0 := levelConst q A τ s₀ with hB0
  have hBp0 : 0 ≤ Bp := levelConst_nonneg q A τ _ hA
  have hBm0 : 0 ≤ Bm := levelConst_nonneg q A τ _ hA
  have hB00 : 0 ≤ B0 := levelConst_nonneg q A τ _ hA
  have hup : ∀ k : ℤ, levelTerm q A τ k ≤ Bp * (2 : ℝ) ^ ((k : ℝ) * c) := fun k => by
    have := levelTerm_le q A τ hA (s₀ + d) (fun v => (hp v).1) (fun v => (hp v).2) k
    rwa [hEp, mul_comm] at this
  have hdown : ∀ k : ℤ, levelTerm q A τ k ≤ Bm * (2 : ℝ) ^ (-((k : ℝ) * c)) := fun k => by
    have := levelTerm_le q A τ hA (s₀ - d) (fun v => (hm v).1) (fun v => (hm v).2) k
    rw [hEm, mul_comm] at this
    convert this using 3
    ring
  have hsqrt : Real.sqrt (Bp * Bm) = B0 := by
    rw [hBp, hBm, levelConst_add_mul_sub q A τ hA, ← sq, Real.sqrt_sq hB00]
  calc ∑ k ∈ S, levelTerm q A τ k
      ≤ ∑ k ∈ S, min (Bp * (2 : ℝ) ^ ((k : ℝ) * c)) (Bm * (2 : ℝ) ^ (-((k : ℝ) * c))) :=
        Finset.sum_le_sum fun k _ => le_min (hup k) (hdown k)
    _ ≤ 2 * Real.sqrt (Bp * Bm) / (1 - (2 : ℝ) ^ (-c)) :=
        sum_min_two_pow_le hBp0 hBm0 hc S
    _ = 2 / (1 - (2 : ℝ) ^ (-c)) * B0 := by rw [hsqrt]; ring
    _ = _ := by rw [hB0, levelConst_eq q A τ hA s₀ hsum]

/-- `A_τ ∏_{v≠τ} (A_v/A_τ)^(g_v) ≤ ∏_v A_v^(β_v)` for `∑ β = 1`, `β_v ≤ g_v` (`v ≠ τ`),
`0 < A_v ≤ A_τ`. -/
theorem mul_prod_erase_div_rpow_le (A : Fin 3 → ℝ) (τ : Fin 3) (hA : ∀ v, 0 < A v)
    (hAτ : ∀ v, A v ≤ A τ) (g β : Fin 3 → ℝ) (hβ : ∑ v, β v = 1) (hβg : ∀ v ≠ τ, β v ≤ g v) :
    A τ * ∏ v ∈ Finset.univ.erase τ, (A v / A τ) ^ (g v) ≤ ∏ v, A v ^ (β v) := by
  have h1 : ∏ v ∈ Finset.univ.erase τ, (A v / A τ) ^ (g v) ≤
      ∏ v ∈ Finset.univ.erase τ, (A v / A τ) ^ (β v) :=
    Finset.prod_le_prod₀ (fun v _ => Real.rpow_nonneg (div_nonneg (hA v).le (hA τ).le) _)
      fun v hv => Real.rpow_le_rpow_of_exponent_ge (div_pos (hA v) (hA τ))
        ((div_le_one (hA τ)).2 (hAτ v)) (hβg v (Finset.ne_of_mem_erase hv))
  have h2 : A τ * ∏ v ∈ Finset.univ.erase τ, (A v / A τ) ^ (β v) = ∏ v, A v ^ (β v) := by
    have e1 : ∏ v ∈ Finset.univ.erase τ, (A v / A τ) ^ (β v) =
        (∏ v ∈ Finset.univ.erase τ, A v ^ (β v)) / A τ ^ (1 - β τ) := by
      have : ∑ v ∈ Finset.univ.erase τ, β v = 1 - β τ := by
        rw [Finset.sum_erase_eq_sub (Finset.mem_univ τ), hβ]
      rw [← this, Real.rpow_sum_of_pos (hA τ), ← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun v _ => Real.div_rpow (hA v).le (hA τ).le _
    rw [e1, ← Finset.mul_prod_erase Finset.univ (fun v => A v ^ (β v)) (Finset.mem_univ τ),
      Real.rpow_sub (hA τ), Real.rpow_one]
    have hτ : A τ ≠ 0 := (hA τ).ne'
    have hτβ : A τ ^ (β τ) ≠ 0 := (Real.rpow_pos_of_pos (hA τ) _).ne'
    field_simp
  rw [← h2]
  exact mul_le_mul_of_nonneg_left h1 (hA τ).le

/-- **B8 (counting lemma), corollary.** If `Σβ = 1` and `β_v ≤ g_v` for `v ≠ τ`, then
`Σ_k F k ≤ (2 / (1 - 2^{-c})) ∏_v A_v^{β_v}`. -/
theorem sum_levelTerm_le_prod (q A : Fin 3 → ℝ) (τ : Fin 3) (hA : ∀ v, 0 < A v)
    (hAτ : ∀ v, A v ≤ A τ) (s₀ d : Fin 3 → ℝ) (hsum : ∑ v, (1 - s₀ v) / q v = 1)
    (hp : ∀ v, s₀ v + d v ∈ Set.Icc (0 : ℝ) 1) (hm : ∀ v, s₀ v - d v ∈ Set.Icc (0 : ℝ) 1)
    (hc : 0 < ∑ v, d v / q v) (β : Fin 3 → ℝ) (hβ : ∑ v, β v = 1)
    (hβg : ∀ v ≠ τ, β v ≤ levelExponent q s₀ v) (S : Finset ℤ) :
    ∑ k ∈ S, levelTerm q A τ k ≤
      2 / (1 - (2 : ℝ) ^ (-(∑ v, d v / q v))) * ∏ v, A v ^ (β v) := by
  have hr : (2 : ℝ) ^ (-(∑ v, d v / q v)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine (sum_levelTerm_le q A τ hA s₀ d hsum hp hm hc S).trans ?_
  exact mul_le_mul_of_nonneg_left (mul_prod_erase_div_rpow_le A τ hA hAτ _ β hβ hβg)
    (div_nonneg (by norm_num) (by linarith))

/-! ### The explicit region lemma -/

/-- The loss `η = θ = 1/(16 R)` of the route. -/
noncomputable def etaR (R : ℝ) : ℝ := 1 / (16 * R)

/-- The perturbed type `q⁺ = ((1+η)·2, (1+η)·2, (1+η)·R)`. -/
noncomputable def qPlus (R : ℝ) (v : Fin 3) : ℝ :=
  if v = 2 then R * (1 + etaR R) else 2 * (1 + etaR R)

/-- The type used for the slot `τ`: `q⁺_τ/(1-θ)` in slot `τ`, and `q⁺_v` in the other slots.
(`θ = 0` gives `q⁺`; `θ = η = 1/(16 R)` is the type of B11.) -/
noncomputable def qTau (R θ : ℝ) (τ v : Fin 3) : ℝ :=
  if v = τ then qPlus R v / (1 - θ) else qPlus R v

/-- The number `σ` of the explicit choice of `s⁰`. -/
noncomputable def countSigma (R θ : ℝ) (τ : Fin 3) : ℝ :=
  if τ = 2 then (1 - θ) / (2 * R) - etaR R else (2 / R - θ - 2 * etaR R) / (2 - θ)

/-- The explicit `s⁰`: `(σ, σ, 1/2)` for `τ = 3` and `(σ, σ, 0)` for `τ ∈ {1, 2}`. -/
noncomputable def countS (R θ : ℝ) (τ v : Fin 3) : ℝ :=
  if v = 2 then (if τ = 2 then 1 / 2 else 0) else countSigma R θ τ

/-- The explicit `d`: `(0, 0, 1/2)` for `τ = 3` and `σ e_τ` for `τ ∈ {1, 2}`. -/
noncomputable def countD (R θ : ℝ) (τ v : Fin 3) : ℝ :=
  if v = τ then (if τ = 2 then 1 / 2 else countSigma R θ τ) else 0

/-- `η` in terms of `x = 1/R`. -/
private theorem etaR_inv (x : ℝ) (hx : x ≠ 0) : etaR (1 / x) = x / 16 := by
  unfold etaR; field_simp

/-- `R ≥ 4` is `R = 1/x` with `0 < x ≤ 1/4`. -/
private theorem exists_inv {R : ℝ} (hR : 4 ≤ R) : ∃ x : ℝ, 0 < x ∧ x ≤ 1 / 4 ∧ R = 1 / x := by
  have hR0 : 0 < R := by linarith
  refine ⟨1 / R, by positivity, ?_, by field_simp⟩
  rw [div_le_div_iff₀ hR0 (by norm_num)]; linarith

private theorem sigma2_bounds {x θ : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 4) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ x / 16) : x / 4 ≤ (1 - θ) * x / 2 - x / 16 ∧ (1 - θ) * x / 2 - x / 16 ≤ x / 2 := by
  constructor <;> nlinarith [mul_nonneg hθ0 hx0.le, mul_nonneg hx0.le (sub_nonneg.2 hθ)]

private theorem sigma1_bounds {x θ : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 4) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ x / 16) :
    29 * x / 32 ≤ (2 * x - θ - 2 * (x / 16)) / (2 - θ) ∧
      (2 * x - θ - 2 * (x / 16)) / (2 - θ) ≤ 1 / 2 := by
  have h2 : 0 < 2 - θ := by linarith
  constructor
  · rw [le_div_iff₀ h2]
    nlinarith [mul_nonneg hθ0 hx0.le, mul_nonneg hx0.le (sub_nonneg.2 hθ)]
  · rw [div_le_iff₀ h2]
    nlinarith

/-- The normalization `∑_v (1 - s⁰_v)/q_v = 1` of the explicit `s⁰`. -/
theorem countSum {R θ : ℝ} (hR : 4 ≤ R) (hθ : θ ≤ etaR R) (τ : Fin 3) :
    ∑ v, (1 - countS R θ τ v) / qTau R θ τ v = 1 := by
  have hR0 : R ≠ 0 := by positivity
  have hε : etaR R ≤ 1 / 64 := by
    unfold etaR; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h1 : 1 - θ ≠ 0 := by linarith
  have h2 : 2 - θ ≠ 0 := by linarith
  have h3 : 16 * R + 1 ≠ 0 := by positivity
  fin_cases τ <;> simp [Fin.sum_univ_three, countS, qTau, qPlus, countSigma] <;> unfold etaR <;>
    field_simp <;> ring

/-- The bounds `0 ≤ σ ≤ 1/2`, and the lower bound `σ ≥ 29/(32 R)` when `τ ≠ 3`. -/
private theorem countSigma_bounds {R θ : ℝ} (hR : 4 ≤ R) (hθ0 : 0 ≤ θ) (hθ : θ ≤ etaR R)
    (τ : Fin 3) :
    0 ≤ countSigma R θ τ ∧ countSigma R θ τ ≤ 1 / 2 ∧
      (τ ≠ 2 → 29 / (32 * R) ≤ countSigma R θ τ) := by
  obtain ⟨x, hx0, hx4, rfl⟩ := exists_inv hR
  rw [etaR_inv x hx0.ne'] at hθ
  by_cases hτ : τ = 2
  · subst hτ
    have e : (1 - θ) / (2 * (1 / x)) = (1 - θ) * x / 2 := by field_simp
    obtain ⟨h1, h2⟩ := sigma2_bounds hx0 hx4 hθ0 hθ
    simp only [countSigma, ↓reduceIte, etaR_inv x hx0.ne', e]
    exact ⟨by linarith, by linarith, fun h => absurd rfl h⟩
  · have e : 2 / (1 / x) = 2 * x := by field_simp
    have e2 : 29 / (32 * (1 / x)) = 29 * x / 32 := by field_simp
    obtain ⟨h1, h2⟩ := sigma1_bounds hx0 hx4 hθ0 hθ
    simp only [countSigma, hτ, ↓reduceIte, etaR_inv x hx0.ne', e, e2]
    exact ⟨by linarith, h2, fun _ => h1⟩

/-- `s⁰ + d ∈ [0,1]³` for the explicit choices. -/
theorem countS_add_mem {R θ : ℝ} (hR : 4 ≤ R) (hθ0 : 0 ≤ θ) (hθ : θ ≤ etaR R) (τ v : Fin 3) :
    countS R θ τ v + countD R θ τ v ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1, -⟩ := countSigma_bounds hR hθ0 hθ τ
  fin_cases τ <;> fin_cases v <;> simp [countS, countD] at h0 h1 ⊢ <;> (try constructor) <;>
    linarith

/-- `s⁰ - d ∈ [0,1]³` for the explicit choices. -/
theorem countS_sub_mem {R θ : ℝ} (hR : 4 ≤ R) (hθ0 : 0 ≤ θ) (hθ : θ ≤ etaR R) (τ v : Fin 3) :
    countS R θ τ v - countD R θ τ v ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1, -⟩ := countSigma_bounds hR hθ0 hθ τ
  fin_cases τ <;> fin_cases v <;> simp [countS, countD] at h0 h1 ⊢ <;> (try constructor) <;>
    linarith

/-- The geometric exponent `c = ∑_v d_v/q_v` of the explicit choices is at least `2/(5R)`. -/
theorem countC_ge {R θ : ℝ} (hR : 4 ≤ R) (hθ0 : 0 ≤ θ) (hθ : θ ≤ etaR R) (τ : Fin 3) :
    2 / (5 * R) ≤ ∑ v, countD R θ τ v / qTau R θ τ v := by
  obtain ⟨x, hx0, hx4, rfl⟩ := exists_inv hR
  rw [etaR_inv x hx0.ne'] at hθ
  have h1 : 0 < 1 - θ := by linarith
  have h2 : 0 < 2 - θ := by linarith
  fin_cases τ <;>
    simp only [Fin.sum_univ_three, countD, qTau, qPlus, countSigma, etaR_inv x hx0.ne'] <;>
    simp <;> field_simp <;>
    nlinarith [mul_nonneg hx0.le (sub_nonneg.2 hθ), mul_nonneg (mul_nonneg hx0.le hx0.le) (sub_nonneg.2 hθ),
      mul_nonneg hx0.le hx0.le, mul_nonneg (mul_nonneg hx0.le hx0.le) (sub_nonneg.2 hx4), mul_pos hx0 hx0,
      mul_nonneg hx0.le hθ0]

/-- For `v ≠ τ`, `g_v = s⁰_v + (1 - s⁰_v)/q_v` is at least `1/2 + 1/(8R)` (`v ∈ {1,2}`), resp.
`1/(4R)` (`v = 3`). -/
theorem countG_ge {R θ : ℝ} (hR : 4 ≤ R) (hθ0 : 0 ≤ θ) (hθ : θ ≤ etaR R) (τ v : Fin 3)
    (hv : v ≠ τ) :
    (if v = 2 then 1 / (4 * R) else 1 / 2 + 1 / (8 * R)) ≤
      levelExponent (qTau R θ τ) (countS R θ τ) v := by
  obtain ⟨x, hx0, hx4, rfl⟩ := exists_inv hR
  rw [etaR_inv x hx0.ne'] at hθ
  have h1 : 0 < 1 - θ := by linarith
  have h2 : 0 < 2 - θ := by linarith
  fin_cases τ <;> fin_cases v <;> simp at hv <;>
    simp only [levelExponent, countS, qTau, qPlus, countSigma, etaR_inv x hx0.ne'] <;> simp <;>
    field_simp <;>
    nlinarith [mul_nonneg hx0.le (sub_nonneg.2 hθ), mul_nonneg (mul_nonneg hx0.le hx0.le) (sub_nonneg.2 hθ),
      mul_nonneg hx0.le hx0.le, mul_nonneg (mul_nonneg hx0.le hx0.le) (sub_nonneg.2 hx4), mul_pos hx0 hx0,
      mul_nonneg hx0.le hθ0]

/-- On `𝒩_R`: `β_1, β_2 ≤ 1/2 + 1/(8R)` and `β_3 ≤ 1/(4R)`. -/
theorem le_regionBound {R : ℝ} (hR : 4 ≤ R) {β : Fin 3 → ℝ} (hβ : ∑ v, β v = 1)
    (h0 : |β 0 - 1 / 2| ≤ 1 / (8 * R)) (h1 : |β 1 - 1 / 2| ≤ 1 / (8 * R)) (v : Fin 3) :
    β v ≤ if v = 2 then 1 / (4 * R) else 1 / 2 + 1 / (8 * R) := by
  have hsum : β 0 + β 1 + β 2 = 1 := by simpa [Fin.sum_univ_three] using hβ
  have hR0 : 0 < R := by linarith
  have e : 1 / (4 * R) = 2 * (1 / (8 * R)) := by field_simp; norm_num
  obtain ⟨a0, b0⟩ := abs_le.1 h0
  obtain ⟨a1, b1⟩ := abs_le.1 h1
  by_cases hv : v = 2
  · subst hv
    simp only [↓reduceIte]
    linarith
  · simp only [hv, ↓reduceIte]
    have : v = 0 ∨ v = 1 := by fin_cases v <;> simp_all
    rcases this with rfl | rfl <;> linarith

/-- The constant `2/(1 - 2^{-c₀})` with `c₀ = 2/(5R)`; it depends on `R` only. -/
noncomputable def countConst (R : ℝ) : ℝ := 2 / (1 - (2 : ℝ) ^ (-(2 / (5 * R))))

theorem countConst_nonneg {R : ℝ} (hR : 4 ≤ R) : 0 ≤ countConst R := by
  have hR0 : 0 < R := by linarith
  have hpos : 0 < 2 / (5 * R) := by positivity
  have : (2 : ℝ) ^ (-(2 / (5 * R))) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact div_nonneg (by norm_num) (by linarith)

/-- **Region lemma (B8 at the explicit choices).** Let `R ≥ 4`, `0 ≤ θ ≤ η = 1/(16R)`, `τ ∈ Fin 3`,
and `β` in the region `𝒩_R`. For `q = qTau R θ τ` (the type `q⁺` with slot `τ` divided by `1 - θ`;
`θ = 0` is the type of B10, `θ = η` the type of B11) and `0 < A_v ≤ A_τ`, every finite level sum
`Σ_{k∈S} F(k)` is at most `countConst R · ∏_v A_v^{β_v}`; the constant depends on `R` only. -/
theorem sum_levelTerm_le_region {R θ : ℝ} (hR : 4 ≤ R) (hθ0 : 0 ≤ θ) (hθ : θ ≤ etaR R)
    (τ : Fin 3) (A : Fin 3 → ℝ) (hA : ∀ v, 0 < A v) (hAτ : ∀ v, A v ≤ A τ)
    {β : Fin 3 → ℝ} (hβ : ∑ v, β v = 1) (h0 : |β 0 - 1 / 2| ≤ 1 / (8 * R))
    (h1 : |β 1 - 1 / 2| ≤ 1 / (8 * R)) (S : Finset ℤ) :
    ∑ k ∈ S, levelTerm (qTau R θ τ) A τ k ≤ countConst R * ∏ v, A v ^ (β v) := by
  have hR0 : 0 < R := by linarith
  have hc0 : 2 / (5 * R) ≤ ∑ v, countD R θ τ v / qTau R θ τ v := countC_ge hR hθ0 hθ τ
  have hcpos : 0 < 2 / (5 * R) := by positivity
  have hmain := sum_levelTerm_le_prod (qTau R θ τ) A τ hA hAτ (countS R θ τ) (countD R θ τ)
    (countSum hR hθ τ) (countS_add_mem hR hθ0 hθ τ) (countS_sub_mem hR hθ0 hθ τ)
    (hcpos.trans_le hc0) β hβ
    (fun v hv => (le_regionBound hR hβ h0 h1 v).trans (countG_ge hR hθ0 hθ τ v hv)) S
  refine hmain.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun v _ => Real.rpow_nonneg (hA v).le _)
  have hlt : (2 : ℝ) ^ (-(2 / (5 * R))) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hle : (2 : ℝ) ^ (-(∑ v, countD R θ τ v / qTau R θ τ v)) ≤ (2 : ℝ) ^ (-(2 / (5 * R))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

/-- `tsum` form of `sum_levelTerm_le_region`. -/
theorem tsum_levelTerm_le_region {R θ : ℝ} (hR : 4 ≤ R) (hθ0 : 0 ≤ θ) (hθ : θ ≤ etaR R)
    (τ : Fin 3) (A : Fin 3 → ℝ) (hA : ∀ v, 0 < A v) (hAτ : ∀ v, A v ≤ A τ)
    {β : Fin 3 → ℝ} (hβ : ∑ v, β v = 1) (h0 : |β 0 - 1 / 2| ≤ 1 / (8 * R))
    (h1 : |β 1 - 1 / 2| ≤ 1 / (8 * R)) :
    ∑' k : ℤ, levelTerm (qTau R θ τ) A τ k ≤ countConst R * ∏ v, A v ^ (β v) :=
  Real.tsum_le_of_sum_le (fun k => levelTerm_nonneg _ A τ hA k)
    (sum_levelTerm_le_region hR hθ0 hθ τ A hA hAτ hβ h0 h1)

/-- Summability of the level sum in the region. -/
theorem summable_levelTerm_region {R θ : ℝ} (hR : 4 ≤ R) (hθ0 : 0 ≤ θ) (hθ : θ ≤ etaR R)
    (τ : Fin 3) (A : Fin 3 → ℝ) (hA : ∀ v, 0 < A v) (hAτ : ∀ v, A v ≤ A τ)
    {β : Fin 3 → ℝ} (hβ : ∑ v, β v = 1) (h0 : |β 0 - 1 / 2| ≤ 1 / (8 * R))
    (h1 : |β 1 - 1 / 2| ≤ 1 / (8 * R)) :
    Summable (levelTerm (qTau R θ τ) A τ) :=
  summable_of_sum_le (fun k => levelTerm_nonneg _ A τ hA k)
    (sum_levelTerm_le_region hR hθ0 hθ τ A hA hAτ hβ h0 h1)

end PrimeBHT.TimeFrequency.X2.V16
