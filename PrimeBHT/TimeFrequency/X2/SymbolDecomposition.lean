module

public import PrimeBHT.TimeFrequency.X2.SymbolFourier
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Int.Log

/-!
# X2, node V04 (i)-(ii): decomposition of the symbol `m` into dyadic pieces and Fourier series

Blueprint `docs/x2-blueprint.md`, node V04 (i), (ii) (the form-level identity (iii) is in
`PrimeBHT.TimeFrequency.X2.SymbolForm`). Fully proved. Cutoffs (fixed, universal): `θ = thetaBump`
(`1` on `[-1, 1]`, support in `[-2, 2]`), `ρ(s) = θ(s) - θ(2s)` (`rho`; support in `1/2 < |s| < 2`),
`ρ̃ = symbolCutoff` (smooth, values in `[-1, 1]`, `= 1` on `1/2 ≤ |s| ≤ 2`,
`tsupport ρ̃ ⊆ {3/10 ≤ |s| ≤ 5/2} ⊆ {1/4 < |s| < 3}`), `m_k(s) = ρ(s) m(2^k s)` (`symbolPiece`),
`c_{k,n} = (1/8) ∫_{-4}^{4} m_k(s) e^{-iπ n s/4} ds` (`symbolCoeff`, Mathlib's `fourierCoeffOn`).

## Final signatures (namespace `PrimeBHT.TimeFrequency.X2`)

* `hasSum_rho_zpow : t ≠ 0 → HasSum (k ↦ ρ(2^{-k} t)) 1` (partition of unity);
  `exists_window : t ≠ 0 → ∃ k₀, ∀ k, ρ̃(2^{-k} t) ≠ 0 → k₀ ≤ k ∧ k ≤ k₀ + 3` (at most four scales);
  `tsupport_symbolCutoff_subset`, `symbolCutoff_eq_one`, `symbolCutoff_mul_rho : ρ̃ ρ = ρ`.
* `contDiff_symbolPiece`, `exists_bound_iteratedDeriv_symbolPiece` (Leibniz, uniform in `k`).
* `exists_decay_symbolCoeff : ∃ C : ℕ → ℝ, (∀ N, 0 ≤ C N) ∧ ∀ {m}, ContDiffOn ℝ ∞ m {0}ᶜ → ∀ {A}, (∀ j t, t ≠ 0 →
  |t|^j ‖iteratedDeriv j m t‖ ≤ A j) → ∀ N k n, (1 + |n|)^N * ‖symbolCoeff m k n‖ ≤ C N * ∑ j ∈ range (N+1), A j`.
* `exists_symbol_decomposition` (`symbolTerm c t (k, n) = c k n * ρ̃(2^{-k} t) * exp (↑(π n 2^{-k} t / 4) * I)`):
  `∃ C, (∀ N, 0 ≤ C N) ∧ ∀ {m} hm {A} hA, (i: the decay above) ∧ (ii: ∀ t ≠ 0, HasSum (symbolTerm (symbolCoeff m) t)
  (m t)) ∧ (∀ t ≠ 0, absolute summability over ℤ × ℤ with ∑_p ‖term_p‖ ≤ 4 (C 2 ∑_{j<3} A j) ∑_n (1+|n|)^{-2})`.

Auxiliary: `PrimeBHT.TimeFrequency.X2.SymbolFourier` (Fourier series on `[-4, 4)` of smooth functions supported in
`[-2, 2]`: `N` integrations by parts via `fourierCoeffOn_of_hasDerivAt`, pointwise sums via
`has_pointwise_sum_fourier_series_of_summable`).

## Corrections / remarks on the blueprint

None of substance: the constants (`m_k` supported in `|s| ≤ 2 ⊂ (-4, 4)`, period `8`, `e^{iπ n s/4}`, `ρ̃ = 1` on
`supp ρ`, at most four `k` per `t`) are as stated. `|c_{k,n}| ≤ (4/(π|n|))^N sup |m_k^{(N)}|` (integration by
parts) is what `norm_fcoef_mul_le` proves. `A_j ≥ 0` follows from the hypothesis (`t = 1`).
-/

@[expose] public noncomputable section

open MeasureTheory Complex
open scoped Real ComplexConjugate ContDiff

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2

/-- The bump `θ`: equal to `1` on `[-1, 1]`, supported in `[-2, 2]`, with values in `[0, 1]`. -/
noncomputable def thetaBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- `θ(x)`. -/
noncomputable def theta (x : ℝ) : ℝ := thetaBump x

theorem contDiff_theta : ContDiff ℝ ∞ theta := thetaBump.contDiff

theorem theta_eq_one {x : ℝ} (hx : |x| ≤ 1) : theta x = 1 :=
  thetaBump.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hx)

theorem theta_eq_zero {x : ℝ} (hx : 2 ≤ |x|) : theta x = 0 :=
  thetaBump.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hx)

theorem theta_nonneg (x : ℝ) : 0 ≤ theta x := thetaBump.nonneg
theorem theta_le_one (x : ℝ) : theta x ≤ 1 := thetaBump.le_one

/-- The dyadic piece `ρ(s) = θ(s) - θ(2s)`, supported in `1/2 < |s| < 2`. -/
noncomputable def rho (s : ℝ) : ℝ := theta s - theta (2 * s)

theorem contDiff_rho : ContDiff ℝ ∞ rho :=
  contDiff_theta.sub (contDiff_theta.comp (contDiff_const.mul contDiff_id))

theorem rho_eq_zero_of_abs_le {s : ℝ} (hs : |s| ≤ 1 / 2) : rho s = 0 := by
  have h1 : |2 * s| ≤ 1 := by rw [abs_mul]; norm_num; linarith
  rw [rho, theta_eq_one (by linarith), theta_eq_one h1, sub_self]

theorem rho_eq_zero_of_two_le {s : ℝ} (hs : 2 ≤ |s|) : rho s = 0 := by
  have h1 : 2 ≤ |2 * s| := by rw [abs_mul]; norm_num; linarith
  rw [rho, theta_eq_zero hs, theta_eq_zero h1, sub_self]

theorem abs_lt_of_rho_ne_zero {s : ℝ} (hs : rho s ≠ 0) : 1 / 2 < |s| ∧ |s| < 2 :=
  ⟨lt_of_not_ge fun h => hs (rho_eq_zero_of_abs_le h), lt_of_not_ge fun h => hs (rho_eq_zero_of_two_le h)⟩

theorem hasCompactSupport_rho : HasCompactSupport rho := by
  refine HasCompactSupport.intro (K := Set.Icc (-2 : ℝ) 2) isCompact_Icc fun x hx => ?_
  apply rho_eq_zero_of_two_le
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hx | hx
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- Partition of unity: `∑_{k ∈ ℤ} ρ(2^{-k} t) = 1` for `t ≠ 0`. -/
theorem hasSum_int_telescope {a : ℤ → ℝ} {j₀ : ℤ} {n : ℕ} (h0 : ∀ k ≤ j₀, a k = 0)
    (h1 : ∀ k, j₀ + n ≤ k → a k = 1) : HasSum (fun k : ℤ => a k - a (k - 1)) 1 := by
  have hsupp : ∀ k ∉ (Finset.range n).image (fun j : ℕ => j₀ + 1 + (j : ℤ)),
      a k - a (k - 1) = 0 := by
    intro k hk
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and] at hk
    by_cases hk1 : k ≤ j₀
    · rw [h0 k hk1, h0 (k - 1) (by omega)]; ring
    · have : j₀ + n ≤ k - 1 := by
        by_contra hlt
        exact hk (k - j₀ - 1).toNat (by omega) (by omega)
      rw [h1 k (by omega), h1 (k - 1) this]; ring
  have h2 : HasSum (fun k : ℤ => a k - a (k - 1))
      (∑ k ∈ (Finset.range n).image (fun j : ℕ => j₀ + 1 + (j : ℤ)), (a k - a (k - 1))) :=
    hasSum_sum_of_ne_finset_zero hsupp
  convert h2 using 1
  rw [Finset.sum_image (by intro x _ y _ hxy; simpa using hxy)]
  have e : ∀ j : ℕ, a (j₀ + 1 + (j : ℤ)) - a (j₀ + 1 + (j : ℤ) - 1) =
      a (j₀ + ((j + 1 : ℕ) : ℤ)) - a (j₀ + (j : ℤ)) := fun j => by
    congr 2 <;> push_cast <;> ring
  simp only [e]
  rw [Finset.sum_range_sub (fun j : ℕ => a (j₀ + (j : ℤ))) n]
  simp only [Nat.cast_zero, add_zero]
  rw [h0 j₀ le_rfl, h1 (j₀ + n) le_rfl]
  ring

theorem hasSum_rho_zpow {t : ℝ} (ht : t ≠ 0) :
    HasSum (fun k : ℤ => rho ((2 : ℝ) ^ (-k) * t)) 1 := by
  set a : ℤ → ℝ := fun k => theta ((2 : ℝ) ^ (-k) * t) with ha
  have hat : 0 < |t| := abs_pos.2 ht
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt (2 / |t|) (one_lt_two : (1 : ℝ) < 2)
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt |t| (one_lt_two : (1 : ℝ) < 2)
  have key : ∀ k : ℤ, rho ((2 : ℝ) ^ (-k) * t) = a k - a (k - 1) := fun k => by
    simp only [rho, ha]
    congr 2
    rw [show (-(k - 1) : ℤ) = -k + 1 by ring, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    ring
  simp only [key]
  refine hasSum_int_telescope (j₀ := -(M : ℤ)) (n := L + M) ?_ ?_
  · intro k hk
    apply theta_eq_zero
    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
    have h2 : (2 : ℝ) ^ M ≤ (2 : ℝ) ^ (-k) := by
      rw [← zpow_natCast]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    have : 2 < 2 ^ M * |t| := by
      rw [div_lt_iff₀ hat] at hM; exact hM
    nlinarith
  · intro k hk
    apply theta_eq_one
    rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) _)]
    have h2 : (2 : ℝ) ^ (-k) ≤ ((2 : ℝ) ^ L)⁻¹ := by
      rw [← zpow_natCast, ← zpow_neg]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h3 : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
    calc (2 : ℝ) ^ (-k) * |t| ≤ ((2 : ℝ) ^ L)⁻¹ * |t| := by gcongr
      _ ≤ 1 := by
        rw [inv_mul_le_iff₀ h3]; linarith

/-! ### The fixed cutoff `ρ̃` -/

/-- A bump equal to `1` on `[-2, 2]` and supported in `|x| ≤ 5/2`. -/
noncomputable def betaBump : ContDiffBump (0 : ℝ) := ⟨2, 5 / 2, by norm_num, by norm_num⟩

/-- A bump equal to `1` on `|x| ≤ 3/10` and supported in `|x| ≤ 1/2`. -/
noncomputable def gammaBump : ContDiffBump (0 : ℝ) := ⟨3 / 10, 1 / 2, by norm_num, by norm_num⟩

/-- **The fixed cutoff `ρ̃`** of the symbol decomposition: smooth, with values in `[-1, 1]`,
`ρ̃ = 1` on `1/2 ≤ |s| ≤ 2`, `tsupport ρ̃ ⊆ {3/10 ≤ |s| ≤ 5/2} ⊆ {1/4 < |s| < 3}`. -/
noncomputable def symbolCutoff (s : ℝ) : ℝ := betaBump s - gammaBump s

/-! ### The pieces `m_k(s) = ρ(s) m(2^k s)` -/

/-- `m_k(s) = ρ(s) m(2^k s)`; `ρ` vanishes near `s = 0`, so this is `0` there. -/
noncomputable def symbolPiece (m : ℝ → ℂ) (k : ℤ) (s : ℝ) : ℂ := (rho s : ℂ) * m ((2 : ℝ) ^ k * s)

theorem symbolPiece_eq_zero_of_two_le (m : ℝ → ℂ) (k : ℤ) {s : ℝ} (hs : 2 ≤ |s|) :
    symbolPiece m k s = 0 := by
  simp [symbolPiece, rho_eq_zero_of_two_le hs]

theorem symbolPiece_eq_zero_of_abs_le (m : ℝ → ℂ) (k : ℤ) {s : ℝ} (hs : |s| ≤ 1 / 2) :
    symbolPiece m k s = 0 := by
  simp [symbolPiece, rho_eq_zero_of_abs_le hs]

theorem contDiff_symbolPiece {m : ℝ → ℂ} (hm : ContDiffOn ℝ ∞ m {0}ᶜ) (k : ℤ) :
    ContDiff ℝ ∞ (symbolPiece m k) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s = 0
  · subst hs
    have hev : symbolPiece m k =ᶠ[nhds 0] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_abs continuous_const :
        IsOpen {s : ℝ | |s| < 1 / 2}).mem_nhds (by simp)] with y hy
      exact symbolPiece_eq_zero_of_abs_le m k hy.le
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have h1 : ContDiffAt ℝ ∞ (fun s : ℝ => (rho s : ℂ)) s :=
      (Complex.ofRealCLM.contDiff.comp contDiff_rho).contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fun s : ℝ => m ((2 : ℝ) ^ k * s)) s := by
      have hne : (2 : ℝ) ^ k * s ≠ 0 := mul_ne_zero (zpow_ne_zero _ two_ne_zero) hs
      have hm' : ContDiffAt ℝ ∞ m ((2 : ℝ) ^ k * s) :=
        hm.contDiffAt (isOpen_compl_singleton.mem_nhds hne)
      exact hm'.comp s (contDiff_const.mul contDiff_id).contDiffAt
    exact h1.mul h2

theorem iteratedDeriv_comp_const_mul_of_isOpen {m : ℝ → ℂ} (hm : ContDiffOn ℝ ∞ m {0}ᶜ) {c : ℝ}
    (hc : c ≠ 0) (i : ℕ) {s : ℝ} (hs : s ≠ 0) :
    iteratedDeriv i (fun x => m (c * x)) s = c ^ i • iteratedDeriv i m (c * s) := by
  have hopen : IsOpen ({0}ᶜ : Set ℝ) := isOpen_compl_singleton
  have hmaps : Set.MapsTo (fun x : ℝ => c * x) ({0}ᶜ : Set ℝ) ({0}ᶜ : Set ℝ) := fun x hx => by
    simpa using And.intro hc hx
  have h1 := iteratedDerivWithin_comp_const_smul (n := i) (s := ({0}ᶜ : Set ℝ)) (x := s)
    (f := m) hs hopen.uniqueDiffOn (hm.of_le (by exact_mod_cast le_top)) c hmaps
  rw [iteratedDerivWithin_of_isOpen hopen hs,
    iteratedDerivWithin_of_isOpen hopen (by simpa using And.intro hc hs)] at h1
  exact h1

/-- Scale invariance of the symbol class: `|s|^i ‖(m(2^k ·))^{(i)}(s)‖ ≤ A i`. -/
theorem norm_iteratedDeriv_scaled_le {m : ℝ → ℂ} (hm : ContDiffOn ℝ ∞ m {0}ᶜ) {A : ℕ → ℝ}
    (hA : ∀ j : ℕ, ∀ t : ℝ, t ≠ 0 → |t| ^ j * ‖iteratedDeriv j m t‖ ≤ A j) (k : ℤ) (i : ℕ)
    {s : ℝ} (hs : s ≠ 0) :
    |s| ^ i * ‖iteratedDeriv i (fun x => m ((2 : ℝ) ^ k * x)) s‖ ≤ A i := by
  have hc : (2 : ℝ) ^ k ≠ 0 := zpow_ne_zero _ two_ne_zero
  rw [iteratedDeriv_comp_const_mul_of_isOpen hm hc i hs, norm_smul]
  have := hA i ((2 : ℝ) ^ k * s) (mul_ne_zero hc hs)
  calc |s| ^ i * (‖((2 : ℝ) ^ k) ^ i‖ * ‖iteratedDeriv i m ((2 : ℝ) ^ k * s)‖)
      = |(2 : ℝ) ^ k * s| ^ i * ‖iteratedDeriv i m ((2 : ℝ) ^ k * s)‖ := by
        rw [abs_mul, mul_pow, Real.norm_eq_abs, abs_pow]; ring
    _ ≤ A i := this

theorem nonneg_of_symbolClass {m : ℝ → ℂ} {A : ℕ → ℝ}
    (hA : ∀ j : ℕ, ∀ t : ℝ, t ≠ 0 → |t| ^ j * ‖iteratedDeriv j m t‖ ≤ A j) (j : ℕ) : 0 ≤ A j :=
  (mul_nonneg (pow_nonneg (abs_nonneg _) _) (norm_nonneg _)).trans (hA j 1 one_ne_zero)

theorem exists_bound_rho (j : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ i ≤ j, ∀ s : ℝ, ‖iteratedDeriv i (fun s : ℝ => (rho s : ℂ)) s‖ ≤ R := by
  have hc : HasCompactSupport (fun s : ℝ => (rho s : ℂ)) :=
    hasCompactSupport_rho.comp_left Complex.ofReal_zero
  have hs : ContDiff ℝ ∞ (fun s : ℝ => (rho s : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_rho
  obtain ⟨C, hC0, hC⟩ := hc.exists_bound_iteratedFDeriv hs j
  exact ⟨C, hC0, fun i hi s => by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact hC i hi s⟩

/-- **Uniform derivative bounds** for the pieces: `‖m_k^{(j)}(s)‖ ≤ K_j ∑_{i ≤ j} A_i`, with `K_j` depending only
on `j`, uniformly in the scale `k`. -/
theorem exists_bound_iteratedDeriv_symbolPiece (j : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {m : ℝ → ℂ}, ContDiffOn ℝ ∞ m {0}ᶜ → ∀ {A : ℕ → ℝ},
      (∀ i : ℕ, ∀ t : ℝ, t ≠ 0 → |t| ^ i * ‖iteratedDeriv i m t‖ ≤ A i) → ∀ (k : ℤ) (s : ℝ),
      ‖iteratedDeriv j (symbolPiece m k) s‖ ≤ K * ∑ i ∈ Finset.range (j + 1), A i := by
  obtain ⟨R, hR0, hR⟩ := exists_bound_rho j
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * R * 2 ^ (j - i), by positivity, ?_⟩
  intro m hm A hA k s
  have hA0 := nonneg_of_symbolClass hA
  have hsumA : 0 ≤ ∑ i ∈ Finset.range (j + 1), A i := Finset.sum_nonneg fun i _ => hA0 i
  by_cases hs : s = 0
  · subst hs
    have hev : symbolPiece m k =ᶠ[nhds 0] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_abs continuous_const :
        IsOpen {s : ℝ | |s| < 1 / 2}).mem_nhds (by simp)] with y hy
      exact symbolPiece_eq_zero_of_abs_le m k hy.le
    rw [hev.iteratedDeriv_eq j]
    simp only [iteratedDeriv_const]
    split_ifs <;> simp only [norm_zero] <;> positivity
  · have h1 : ContDiffAt ℝ j (fun s : ℝ => (rho s : ℂ)) s :=
      ((Complex.ofRealCLM.contDiff.comp contDiff_rho).contDiffAt).of_le (by exact_mod_cast le_top)
    have h2 : ContDiffAt ℝ j (fun s : ℝ => m ((2 : ℝ) ^ k * s)) s := by
      have hne : (2 : ℝ) ^ k * s ≠ 0 := mul_ne_zero (zpow_ne_zero _ two_ne_zero) hs
      have hm' : ContDiffAt ℝ j m ((2 : ℝ) ^ k * s) :=
        (hm.contDiffAt (isOpen_compl_singleton.mem_nhds hne)).of_le (by exact_mod_cast le_top)
      exact hm'.comp s (contDiff_const.mul contDiff_id).contDiffAt
    have hleib := iteratedDeriv_mul h1 h2
    have e : symbolPiece m k = (fun s : ℝ => (rho s : ℂ)) * (fun s : ℝ => m ((2 : ℝ) ^ k * s)) := rfl
    rw [e, hleib]
    have hterm : ∀ i ∈ Finset.range (j + 1),
        ‖(j.choose i : ℂ) * iteratedDeriv i (fun s : ℝ => (rho s : ℂ)) s *
            iteratedDeriv (j - i) (fun s : ℝ => m ((2 : ℝ) ^ k * s)) s‖ ≤
          (j.choose i : ℝ) * R * 2 ^ (j - i) * ∑ l ∈ Finset.range (j + 1), A l := by
      intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      set a := iteratedDeriv i (fun s : ℝ => (rho s : ℂ)) s with ha
      set b := iteratedDeriv (j - i) (fun s : ℝ => m ((2 : ℝ) ^ k * s)) s with hb
      have hAl : A (j - i) ≤ ∑ l ∈ Finset.range (j + 1), A l :=
        Finset.single_le_sum (f := A) (fun l _ => hA0 l) (Finset.mem_range.2 (by omega))
      have hab : ‖a‖ * ‖b‖ ≤ R * (2 ^ (j - i) * A (j - i)) := by
        by_cases hs2 : 1 / 2 ≤ |s|
        · have hb1 := norm_iteratedDeriv_scaled_le hm hA k (j - i) hs
          have hpow : ((1 : ℝ) / 2) ^ (j - i) ≤ |s| ^ (j - i) := pow_le_pow_left₀ (by norm_num) hs2 _
          have : ‖b‖ ≤ 2 ^ (j - i) * A (j - i) := by
            have h3 : ((1 : ℝ) / 2) ^ (j - i) * ‖b‖ ≤ A (j - i) :=
              (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans hb1
            rw [one_div, inv_pow] at h3
            have h4 : (0 : ℝ) < 2 ^ (j - i) := by positivity
            calc ‖b‖ = 2 ^ (j - i) * ((2 ^ (j - i))⁻¹ * ‖b‖) := by field_simp
              _ ≤ 2 ^ (j - i) * A (j - i) := by gcongr
          exact mul_le_mul (hR i hij s) this (norm_nonneg _) hR0
        · have hz : a = 0 := by
            have hev : (fun s : ℝ => (rho s : ℂ)) =ᶠ[nhds s] fun _ => 0 := by
              filter_upwards [(isOpen_lt continuous_abs continuous_const :
                IsOpen {s : ℝ | |s| < 1 / 2}).mem_nhds (not_le.1 hs2)] with y hy
              simp [rho_eq_zero_of_abs_le hy.le]
            rw [ha, hev.iteratedDeriv_eq i]
            simp only [iteratedDeriv_const]
            split_ifs <;> rfl
          rw [hz, norm_zero, zero_mul]
          exact mul_nonneg hR0 (mul_nonneg (by positivity) (hA0 _))
      calc (j.choose i : ℝ) * ‖a‖ * ‖b‖ = (j.choose i : ℝ) * (‖a‖ * ‖b‖) := by ring
        _ ≤ (j.choose i : ℝ) * (R * (2 ^ (j - i) * A (j - i))) := by gcongr
        _ ≤ (j.choose i : ℝ) * (R * (2 ^ (j - i) * ∑ l ∈ Finset.range (j + 1), A l)) := by gcongr
        _ = (j.choose i : ℝ) * R * 2 ^ (j - i) * ∑ l ∈ Finset.range (j + 1), A l := by ring
    calc _ ≤ ∑ i ∈ Finset.range (j + 1), ‖(j.choose i : ℂ) * iteratedDeriv i (fun s : ℝ => (rho s : ℂ)) s *
            iteratedDeriv (j - i) (fun s : ℝ => m ((2 : ℝ) ^ k * s)) s‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * R * 2 ^ (j - i) *
            ∑ l ∈ Finset.range (j + 1), A l := Finset.sum_le_sum hterm
      _ = _ := by rw [← Finset.sum_mul]

/-! ### The coefficients `c_{k,n}` and the decay estimate (i) -/

/-- The coefficients `c_{k,n}`: the Fourier coefficients on `[-4, 4)` of `m_k = ρ · m(2^k ·)`. -/
noncomputable def symbolCoeff (m : ℝ → ℂ) (k n : ℤ) : ℂ := fcoef (symbolPiece m k) n

/-- **(i)** `(1 + |n|)^N ‖c_{k,n}‖ ≤ C_N ∑_{j ≤ N} A_j`, uniformly in `k`, with `C_N` depending only on `N`
(the cutoffs are fixed). -/
theorem exists_decay_symbolCoeff :
    ∃ C : ℕ → ℝ, (∀ N, 0 ≤ C N) ∧ ∀ {m : ℝ → ℂ}, ContDiffOn ℝ ∞ m {0}ᶜ → ∀ {A : ℕ → ℝ},
      (∀ j : ℕ, ∀ t : ℝ, t ≠ 0 → |t| ^ j * ‖iteratedDeriv j m t‖ ≤ A j) → ∀ (N : ℕ) (k n : ℤ),
      (1 + |(n : ℝ)|) ^ N * ‖symbolCoeff m k n‖ ≤ C N * ∑ j ∈ Finset.range (N + 1), A j := by
  choose K hK0 hK using fun j => exists_bound_iteratedDeriv_symbolPiece j
  refine ⟨fun N => max (K 0) ((8 / π) ^ N * K N), fun N => (hK0 0).trans (le_max_left _ _), ?_⟩
  intro m hm A hA N k n
  have hA0 := nonneg_of_symbolClass hA
  have hsum0 : A 0 ≤ ∑ j ∈ Finset.range (N + 1), A j :=
    Finset.single_le_sum (f := A) (fun l _ => hA0 l) (Finset.mem_range.2 (by omega))
  have hvan : ∀ x, 2 < |x| → symbolPiece m k x = 0 := fun x hx =>
    symbolPiece_eq_zero_of_two_le m k hx.le
  have hM₀ : ∀ x, ‖symbolPiece m k x‖ ≤ K 0 * A 0 := fun x => by
    have := hK 0 hm hA k x
    simpa using this
  have hM : ∀ x, ‖iteratedDeriv N (symbolPiece m k) x‖ ≤
      K N * ∑ j ∈ Finset.range (N + 1), A j := fun x => hK N hm hA k x
  have key := norm_fcoef_mul_le (contDiff_symbolPiece hm k) hvan N hM₀ hM n
  refine key.trans ?_
  have hsumA : 0 ≤ ∑ j ∈ Finset.range (N + 1), A j := Finset.sum_nonneg fun l _ => hA0 l
  refine max_le ?_ ?_
  · calc K 0 * A 0 ≤ K 0 * ∑ j ∈ Finset.range (N + 1), A j := by gcongr; exact hK0 0
      _ ≤ max (K 0) ((8 / π) ^ N * K N) * ∑ j ∈ Finset.range (N + 1), A j := by
        gcongr; exact le_max_left _ _
  · calc (8 / π) ^ N * (K N * ∑ j ∈ Finset.range (N + 1), A j)
        = ((8 / π) ^ N * K N) * ∑ j ∈ Finset.range (N + 1), A j := by ring
      _ ≤ max (K 0) ((8 / π) ^ N * K N) * ∑ j ∈ Finset.range (N + 1), A j := by
        gcongr; exact le_max_right _ _

/-! ### The Fourier series of one piece, at one point -/

/-! ### Absolute summability over `ℤ × ℤ` and the joint expansion (ii) -/

end PrimeBHT.TimeFrequency.X2
