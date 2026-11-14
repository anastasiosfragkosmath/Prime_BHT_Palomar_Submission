module

public import PrimeBHT.Periodic
public import PrimeBHT.PeriodicBlock
public import PrimeBHT.PeriodicAssembly.Decomp
public import PrimeBHT.PeriodicAssembly.Structured

/-!
# The bound for `d_B(1)`: `l:d4` (blueprint N36)

`‖A_B(F,G)‖_{L¹(Y_N)} ≤ C_ε |B|^{1/2} Q^{ε-1} ‖F‖₂ ‖G‖₂` for `B ⊆ (Q/2, Q]` squarefree and
`N = lcm B`, with `C_ε` independent of `Q`, `B`, `N`.

Proof (blueprint): greedy decomposition `F = ∑_{j ≤ J} c_j Φ_j + R` (N35) with `t = |B|^{-1/2}`
over `Dset_B = {d ∣ N : d ∣ q for some q ∈ B}`; the structured part is bounded by N34, the
remainder by N31(c) and N32, using `a_B = ∑_d β_d ≤ C_ε |B| Q^{ε-1}` (N31(d)).
-/

@[expose] public section

namespace PrimeBHT.PeriodicAssembly

open Finset PrimeBHT.Periodic
open scoped BigOperators ComplexConjugate

open PrimeBHT.PeriodicBlock (lam bilinAvg beta exists_sum_beta_le)
open PrimeCarleson.Proof.Paper (lcmQ dvd_lcmQ)
open PrimeCarleson.Proof.Goal0 (squarefree_lcm_of_forall)

section Linear

variable {X : Type*} [Fintype X]

theorem l1_add_le (f g : X → ℂ) : l1 (f + g) ≤ l1 f + l1 g := by
  unfold l1
  rw [← Finset.expect_add_distrib]
  exact Finset.expect_le_expect fun x _ => norm_add_le _ _

/-- Triangle inequality for `L¹` of a finite linear combination. -/
theorem l1_sum_smul_le {ι : Type*} (s : Finset ι) (a : ι → ℂ) (f : ι → X → ℂ) :
    l1 (∑ i ∈ s, a i • f i) ≤ ∑ i ∈ s, ‖a i‖ * l1 (f i) := by
  unfold l1
  calc 𝔼 x, ‖(∑ i ∈ s, a i • f i) x‖ ≤ 𝔼 x, ∑ i ∈ s, ‖a i‖ * ‖f i x‖ := by
        refine Finset.expect_le_expect fun x _ => ?_
        rw [Finset.sum_apply]
        refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
        simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    _ = ∑ i ∈ s, ‖a i‖ * 𝔼 x, ‖f i x‖ := by
        rw [Finset.expect_sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_expect]

end Linear

section Bilinear

variable {N : ℕ} [NeZero N]

theorem bilinAvg_add_left (Λ F₁ F₂ G : ZMod N → ℂ) :
    bilinAvg Λ (F₁ + F₂) G = bilinAvg Λ F₁ G + bilinAvg Λ F₂ G := by
  funext y
  simp only [PrimeBHT.PeriodicBlock.bilinAvg, Pi.add_apply]
  rw [← Finset.expect_add_distrib]
  refine Finset.expect_congr rfl fun r _ => ?_
  ring

theorem bilinAvg_sum_smul_left {ι : Type*} (s : Finset ι) (Λ G : ZMod N → ℂ) (c : ι → ℂ)
    (Φ : ι → ZMod N → ℂ) :
    bilinAvg Λ (∑ j ∈ s, c j • Φ j) G = ∑ j ∈ s, c j • bilinAvg Λ (Φ j) G := by
  funext y
  simp only [PrimeBHT.PeriodicBlock.bilinAvg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : ∀ r : ZMod N, Λ r * (∑ j ∈ s, c j * Φ j (y - r)) * G (y + r) =
      ∑ j ∈ s, c j * (Λ r * Φ j (y - r) * G (y + r)) := by
    intro r
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [h1]
  rw [Finset.expect_sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_expect]

end Bilinear

/-- **N36** (`l:d4`), explicit-`ε` form: there is `C_ε` such that for every dyadic-block data
`B ⊆ (Q/2, Q]` (nonempty, squarefree elements), `N = lcm B` and all `F, G : Y_N → ℂ`,
`‖A_B(F,G)‖_{L¹(Y_N)} ≤ C_ε |B|^{1/2} Q^{ε-1} ‖F‖_{L²(Y_N)} ‖G‖_{L²(Y_N)}`. -/
theorem exists_l1_bilinAvg_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ) (B : Finset ℕ), B.Nonempty → 1 ≤ Q →
      (∀ q ∈ B, Q / 2 < (q : ℝ) ∧ (q : ℝ) ≤ Q) → (∀ q ∈ B, Squarefree q) →
      ∀ (N : ℕ) [NeZero N], lcmQ B = N → ∀ F G : ZMod N → ℂ,
        l1 (bilinAvg (lam B N) F G) ≤ C * √(B.card : ℝ) * Q ^ (ε - 1) * l2 F * l2 G := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_l1_bilinAvg_atom_le hε hε1
  obtain ⟨Cβ, hCβ0, hCβ⟩ := exists_sum_beta_le hε hε1
  refine ⟨C₁ + √2 * Cβ, by positivity, fun Q B hB hQ hBQ hsq N _ hN F G => ?_⟩
  classical
  have hQ0 : 0 < Q := by linarith
  have hNsq : Squarefree N := hN ▸ squarefree_lcm_of_forall hsq
  have hBN : ∀ q ∈ B, q ∣ N := fun q hq => hN ▸ dvd_lcmQ hq
  have hN0 : N ≠ 0 := NeZero.ne N
  have hcard : (1 : ℝ) ≤ B.card := by exact_mod_cast hB.card_pos
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = √(B.card : ℝ) := ⟨_, rfl⟩
  rw [← hr_def]
  have hr1 : 1 ≤ r := by rw [hr_def]; exact Real.one_le_sqrt.2 hcard
  have hr0 : 0 < r := by linarith
  have hrsq : r ^ 2 = B.card := by rw [hr_def]; exact Real.sq_sqrt (Nat.cast_nonneg _)
  have hl2F := l2_nonneg F
  have hl2G := l2_nonneg G
  have hQe : 0 ≤ Q ^ (ε - 1) := Real.rpow_nonneg hQ0.le _
  -- the set `Dset_B`
  set Ds : Finset ℕ := N.divisors.filter (fun d => ∃ q ∈ B, d ∣ q) with hDs_def
  have hDs : ∀ d ∈ Ds, d ∣ N := fun d hd => Nat.dvd_of_mem_divisors (Finset.mem_filter.1 hd).1
  obtain ⟨J, d, hd, Φ, c, hJ, hA, hc, hsum, hstop⟩ :=
    exists_greedy_decomposition_of_dvd hNsq Ds hDs (inv_pos.2 hr0) F
  rw [inv_inv] at hJ
  obtain ⟨S, hS⟩ : ∃ S : ZMod N → ℂ, S = ∑ j, (c j : ℂ) • Φ j := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ZMod N → ℂ, R = F - S := ⟨_, rfl⟩
  rw [← hS, ← hR] at hstop
  have hFR : F = S + R := by rw [hR]; abel
  have hsplit : bilinAvg (lam B N) F G = bilinAvg (lam B N) S G + bilinAvg (lam B N) R G := by
    rw [← bilinAvg_add_left, ← hFR]
  -- the structured part
  have hsc : ∑ j, c j ≤ r * l2 F := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin J)) c (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h1
    have h2 : (∑ j, c j) ^ 2 ≤ (r * l2 F) ^ 2 := by
      calc (∑ j, c j) ^ 2 ≤ (∑ j, c j ^ 2) * J := h1
        _ ≤ l2 F ^ 2 * r ^ 2 :=
            mul_le_mul hsum hJ (Nat.cast_nonneg _) (sq_nonneg _)
        _ = (r * l2 F) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun j _ => (hc j).le)
      (mul_nonneg hr0.le hl2F) two_ne_zero).1 h2
  have hstruct : l1 (bilinAvg (lam B N) S G) ≤ r * l2 F * (C₁ * Q ^ (ε - 1) * l2 G) := by
    rw [hS, bilinAvg_sum_smul_left]
    refine (l1_sum_smul_le _ _ _).trans ?_
    have h1 : ∀ j, ‖(c j : ℂ)‖ * l1 (bilinAvg (lam B N) (Φ j) G) ≤
        c j * (C₁ * Q ^ (ε - 1) * l2 G) := by
      intro j
      rw [Complex.norm_real, Real.norm_of_nonneg (hc j).le]
      obtain ⟨q, hq, hdq⟩ := (Finset.mem_filter.1 (hd j)).2
      exact mul_le_mul_of_nonneg_left
        (hC₁ Q B hB N hQ hBQ hBN (Split.ofDvd hNsq (hDs _ (hd j))) ⟨q, hq, hdq⟩ (hA j) G)
        (hc j).le
    refine (Finset.sum_le_sum fun j _ => h1 j).trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hsc (mul_nonneg (mul_nonneg hC₁0.le hQe) hl2G)
  -- the remainder
  have hrem : l1 (bilinAvg (lam B N) R G) ≤
      (∑ d ∈ N.divisors, beta B d) * (√2 * r⁻¹ * l2 F * l2 G) := by
    rw [PrimeBHT.PeriodicAssembly.bilinAvg_lam_eq_sum_divisors_fun hsq hBN hNsq R G]
    refine (l1_sum_smul_le _ _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun d hdiv => ?_
    have hdN := Nat.dvd_of_mem_divisors hdiv
    have hβ0 : 0 ≤ beta B d := Finset.sum_nonneg fun q _ => inv_nonneg.2 (Nat.cast_nonneg _)
    have hμ : ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hmain : beta B d * l1 (Ad hNsq d R G) ≤ beta B d * (√2 * r⁻¹ * l2 F * l2 G) := by
      by_cases hdD : ∃ q ∈ B, d ∣ q
      · refine mul_le_mul_of_nonneg_left ?_ hβ0
        rw [Ad_of_dvd hNsq hdN]
        have hdDs : d ∈ Ds := Finset.mem_filter.2 ⟨hdiv, hdD⟩
        have h2 : l2 ((Split.ofDvd hNsq hdN).M R) ≤ r⁻¹ * l2 F := hstop d hdDs
        refine (Split.l1_A_le _ R G).trans ?_
        calc √2 * l2 ((Split.ofDvd hNsq hdN).M R) * l2 G ≤ √2 * (r⁻¹ * l2 F) * l2 G := by
              gcongr
          _ = √2 * r⁻¹ * l2 F * l2 G := by ring
      · have h0 : beta B d = 0 :=
          Finset.sum_eq_zero fun q hq => absurd
            ⟨q, (Finset.mem_filter.1 hq).1, (Finset.mem_filter.1 hq).2⟩ hdD
        rw [h0]
        simp
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ0]
    calc ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ * beta B d * l1 (Ad hNsq d R G)
        ≤ 1 * beta B d * l1 (Ad hNsq d R G) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμ hβ0) (l1_nonneg _)
      _ = beta B d * l1 (Ad hNsq d R G) := by ring
      _ ≤ _ := hmain
  have haB := hCβ Q B N hN0 hQ hBN hBQ
  rw [← hrsq] at haB
  have hl1 := l1_add_le (bilinAvg (lam B N) S G) (bilinAvg (lam B N) R G)
  rw [hsplit]
  have hrem' : l1 (bilinAvg (lam B N) R G) ≤
      (Cβ * r ^ 2 * Q ^ (ε - 1)) * (√2 * r⁻¹ * l2 F * l2 G) :=
    hrem.trans (mul_le_mul_of_nonneg_right haB
      (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.2 hr0.le)) hl2F)
        hl2G))
  calc l1 (bilinAvg (lam B N) S G + bilinAvg (lam B N) R G)
      ≤ r * l2 F * (C₁ * Q ^ (ε - 1) * l2 G) +
        (Cβ * r ^ 2 * Q ^ (ε - 1)) * (√2 * r⁻¹ * l2 F * l2 G) :=
        hl1.trans (add_le_add hstruct hrem')
    _ = (C₁ + √2 * Cβ) * r * Q ^ (ε - 1) * l2 F * l2 G := by
        field_simp

end PrimeBHT.PeriodicAssembly
