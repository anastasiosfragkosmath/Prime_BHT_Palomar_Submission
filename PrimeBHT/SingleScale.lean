module

public import PrimeBHT.Kernel
public import PrimeBHT.FixedAverage
public import PrimeCarleson.Proof.KMTT.BlockMoment
public import PrimeCarleson.Proof.Paper.Defs.Weights

/-!
# The single-scale rough bound (blueprint node N12 (a), `e:single-rough`)

For `T_k^Q(f,g)(x) = ∑ₙ ψ_k(n) w_Q(n) f(x-n) g(x+n)` we prove, for `1 < p, q < ∞`,
`1/r = 1/p + 1/q`, a bound `‖T_k^Q(f,g)‖_{ℓ^r} ≤ C (1 + log Q)^b ‖f‖_p ‖g‖_q`, uniformly in `k`
(the polylogarithmic loss of the blueprint, not `Q^{o(1)}`).

Conventions.
* `w_Q` is the vendored `PrimeCarleson.blockWeight (Finset.Ioc (Q / 2) Q)`:
  `blockWeight B n = ∑_{q ∈ B} μ(q)/φ(q) · c_q(n)` with `c_q` the Ramanujan sum, so for
  `B = (Q/2, Q] ∩ ℕ` it is the paper's `Λ_Q(n)` (for `Q = 2^j` the frozen block of
  `heathBrownModel`; natural-number division is exact for `Q = 2^j`, and for `Q = 1` the block is
  `{1}`, i.e. `w_1 = 1`).  The paper's `w_Q(n) = Λ_Q(|n|)` is the same function, because
  `c_q(-n) = c_q(n)`: `PrimeCarleson.Proof.Paper.blockWeight_neg`.
* The moment input is the vendored KMTT Lemma 4.6 in the form
  `PrimeCarleson.Proof.KMTT.moment_wQ`: for every integer `m ≥ 1`,
  `E_{n ∈ [N]} |w_Q(n)|^m ≤ C_m (1 + log Q)^(2^m + m)` for all natural `Q ≥ 1` and real `N ≥ 1`
  (this is already the dyadic annulus `Λ_{≤Q} - Λ_{≤Q/2}`, see `blockWeight_Ioc_eq_sub`).
* The theorem is proved for arbitrary `f, g : ℤ → ℂ` (finite support is not needed: the weight
  `ψ_k(n)` has finite support in `n`, so the `n`-sum is finite, and N11 needs no support
  hypothesis), arbitrary natural `Q ≥ 1` (dyadic `Q = 2^j` is a special case), and every scale
  `k : ℕ` (not only `k ≥ 1`).
* Proof (blueprint N12 (a)): choose an integer `m ≥ 2` with `s = m/(m-1) < min(p,q)`, so the
  Hölder conjugate of `s` is the integer `m`; Hölder in `n`, evenness of `w_Q`, the KMTT moment,
  then N11 (`PrimeBHT.FixedAverage.eLpNorm_B_le_real`) at `|f|^s, |g|^s`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace PrimeBHT.SingleScale

open PrimeBHT.Kernel PrimeBHT.FixedAverage PrimeCarleson PrimeCarleson.Proof.KMTT

/-! ### Choice of the Hölder exponent -/

/-- Integer exponent `m ≥ 2` and `s = m/(m-1)` with `s ≤ min p q`, `m⁻¹ + s⁻¹ = 1`. -/
lemma exists_nat_conj {p q : ℝ} (hp : 1 < p) (hq : 1 < q) :
    ∃ (m : ℕ) (s : ℝ), 2 ≤ m ∧ 1 < s ∧ s ≤ p ∧ s ≤ q ∧ (m : ℝ)⁻¹ + s⁻¹ = 1 := by
  set δ : ℝ := min p q - 1 with hδ
  have hδ0 : 0 < δ := by
    have : 1 < min p q := lt_min hp hq
    linarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌈δ⁻¹⌉₊ + 2 := ⟨_, rfl⟩
  have hm2 : 2 ≤ m := by omega
  have hmr : δ⁻¹ < (m : ℝ) - 1 := by
    have h1 : δ⁻¹ ≤ (⌈δ⁻¹⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (m : ℝ) = (⌈δ⁻¹⌉₊ : ℝ) + 2 := by rw [hm]; push_cast; ring
    linarith
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := lt_trans (inv_pos.2 hδ0) hmr
  have hδm : 1 < δ * ((m : ℝ) - 1) := by
    have := mul_lt_mul_of_pos_left hmr hδ0
    rwa [mul_inv_cancel₀ hδ0.ne'] at this
  have key : ∀ a : ℝ, min p q ≤ a → (m : ℝ) / ((m : ℝ) - 1) ≤ a := by
    intro a ha
    rw [div_le_iff₀ hm1]
    have : δ ≤ a - 1 := by linarith
    nlinarith
  refine ⟨m, (m : ℝ) / ((m : ℝ) - 1), hm2, ?_, key p (min_le_left _ _),
    key q (min_le_right _ _), ?_⟩
  · rw [lt_div_iff₀ hm1]; linarith
  · have hm0 : (m : ℝ) ≠ 0 := by
      have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
      linarith
    rw [inv_div]
    field_simp
    ring

/-! ### The moment of `w_Q` on the symmetric window -/

/-- `m`-th moment of `w_Q` over the symmetric window `0 < |n| ≤ L`: evenness of `w_Q`
(`blockWeight_neg`) doubles the one-sided KMTT moment bound `moment_wQ`. -/
lemma sum_blockWeight_pow_le (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q L : ℕ), 1 ≤ Q → 1 ≤ L →
      ∑ n ∈ (Finset.Icc (-(L : ℤ)) L).erase 0,
          ‖blockWeight (Finset.Ioc (Q / 2) Q) n‖ ^ m ≤
        2 * L * (C * (1 + Real.log Q) ^ (2 ^ m + m)) := by
  obtain ⟨C, hC0, hC⟩ := moment_wQ m hm
  refine ⟨C, hC0, fun Q L hQ hL => ?_⟩
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have h1 := sum_le_two_mul_of_even (S := (Finset.Icc (-(L : ℤ)) L).erase 0) (N := (L : ℝ))
    (fun n => ‖blockWeight (Finset.Ioc (Q / 2) Q) n‖ ^ m) (fun n => by positivity)
    (fun n => by simp only [PrimeCarleson.Proof.Paper.blockWeight_neg]) (by
      intro n hn
      rw [Finset.mem_erase, Finset.mem_Icc] at hn
      obtain ⟨hn0, hn1, hn2⟩ := hn
      refine ⟨Int.one_le_abs hn0, ?_⟩
      have : |n| ≤ (L : ℤ) := abs_le.2 ⟨hn1, hn2⟩
      have h' : ((|n| : ℤ) : ℝ) ≤ ((L : ℤ) : ℝ) := by exact_mod_cast this
      simpa using h')
  have h2 := hC Q (L : ℝ) hQ hLR
  rw [card_intervalN hLR, Nat.floor_natCast, one_div, inv_mul_le_iff₀ (by positivity)] at h2
  calc _ ≤ 2 * ∑ n ∈ intervalN (L : ℝ), ‖blockWeight (Finset.Ioc (Q / 2) Q) n‖ ^ m := h1
    _ ≤ 2 * ((L : ℝ) * (C * (1 + Real.log Q) ^ (2 ^ m + m))) := by gcongr
    _ = _ := by ring

/-! ### Real-variable helpers -/

/-- Hölder in `n` with the integer exponent `m` and its conjugate `s`. -/
lemma holder_nat {m : ℕ} {s : ℝ} (hm : 2 ≤ m) (hms : (m : ℝ)⁻¹ + s⁻¹ = 1) (S : Finset ℤ)
    (u v : ℤ → ℝ) (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n) :
    ∑ n ∈ S, u n * v n ≤
      (∑ n ∈ S, u n ^ m) ^ (1 / (m : ℝ)) * (∑ n ∈ S, v n ^ s) ^ (1 / s) := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  have hpq : (m : ℝ).HolderConjugate s := Real.holderConjugate_iff.2 ⟨hm1, hms⟩
  have := Real.inner_le_Lp_mul_Lq_of_nonneg S hpq (fun n _ => hu n) (fun n _ => hv n)
  simpa only [Real.rpow_natCast] using this

/-- The powers of `L` cancel exactly. -/
lemma rpow_combine {L M Bx c m s : ℝ} (hL : 0 < L) (hM : 0 ≤ M) (hB : 0 ≤ Bx)
    (hms : m⁻¹ + s⁻¹ = 1) :
    c / L * ((2 * L * M) ^ (1 / m) * (3 * L * Bx) ^ (1 / s)) =
      c * 3 ^ (1 / s) * (2 * M) ^ (1 / m) * Bx ^ (1 / s) := by
  have h1 : (2 * L * M) ^ (1 / m) = L ^ (1 / m) * (2 * M) ^ (1 / m) := by
    rw [show 2 * L * M = L * (2 * M) by ring, Real.mul_rpow hL.le (by positivity)]
  have h2 : (3 * L * Bx) ^ (1 / s) = L ^ (1 / s) * 3 ^ (1 / s) * Bx ^ (1 / s) := by
    rw [show 3 * L * Bx = L * (3 * Bx) by ring, Real.mul_rpow hL.le (by positivity),
      Real.mul_rpow (by norm_num) hB, mul_assoc]
  have h3 : L ^ (1 / m) * L ^ (1 / s) = L := by
    rw [← Real.rpow_add hL]
    have : 1 / m + 1 / s = 1 := by simpa only [one_div] using hms
    rw [this, Real.rpow_one]
  rw [h1, h2]
  calc c / L * (L ^ (1 / m) * (2 * M) ^ (1 / m) * (L ^ (1 / s) * 3 ^ (1 / s) * Bx ^ (1 / s)))
      = c / L * (L ^ (1 / m) * L ^ (1 / s)) *
          (3 ^ (1 / s) * (2 * M) ^ (1 / m) * Bx ^ (1 / s)) := by ring
    _ = _ := by rw [h3]; field_simp

lemma norm_ofReal_rpow (z : ℂ) (s : ℝ) : ‖(((‖z‖ ^ s : ℝ)) : ℂ)‖ = ‖z‖ ^ s := by
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]

/-! ### The pointwise bound -/

/-- Pointwise bound `|T_k^Q(f,g)(x)| ≤ K · (B_{2^k}(|f|^s,|g|^s)(x))^{1/s}`, the Hölder step of
the blueprint (steps 1-3), with `K` expressed through the moment bound `M`. -/
lemma norm_bilin_le {χ : ℝ → ℝ} (hχ : IsCutoff χ) {c : ℝ} (hc : ∀ t, |psi χ t| ≤ c)
    {m : ℕ} {s : ℝ} (hm : 2 ≤ m) (hms : (m : ℝ)⁻¹ + s⁻¹ = 1) (Q k : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hMom : ∑ n ∈ (Finset.Icc (-((2 ^ k : ℕ) : ℤ)) ((2 ^ k : ℕ) : ℤ)).erase 0,
        ‖blockWeight (Finset.Ioc (Q / 2) Q) n‖ ^ m ≤ 2 * ((2 ^ k : ℕ) : ℝ) * M)
    (f g : ℤ → ℂ) (x : ℤ) :
    ‖bilin (fun n => ((psiK χ k n : ℝ) : ℂ) * blockWeight (Finset.Ioc (Q / 2) Q) n) f g x‖ ≤
      c * 3 ^ (1 / s) * (2 * M) ^ (1 / (m : ℝ)) *
        (B (2 ^ k) (fun y => ((‖f y‖ ^ s : ℝ) : ℂ)) (fun y => ((‖g y‖ ^ s : ℝ) : ℂ)) x) ^
          (1 / s) := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  have hs0 : 0 < s := by
    have : 0 < s⁻¹ := by
      have h : (m : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hm1
      linarith
    exact inv_pos.1 this
  set L : ℕ := 2 ^ k with hL
  have hL1 : 1 ≤ L := Nat.one_le_two_pow
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hLpos : (0 : ℝ) < L := by linarith
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hLeq : (L : ℝ) = 2 ^ k := by rw [hL]; push_cast; rfl
  set S : Finset ℤ := (Finset.Icc (-(L : ℤ)) L).erase 0 with hS
  set w : ℤ → ℂ := fun n => blockWeight (Finset.Ioc (Q / 2) Q) n with hw
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0)
  -- the weight vanishes off `S`
  have hsupp : ∀ n ∉ S, ((psiK χ k n : ℝ) : ℂ) * blockWeight (Finset.Ioc (Q / 2) Q) n = 0 := by
    intro n hn
    by_cases h0 : n = 0
    · subst h0; simp [psiK_zero]
    · have hnI : n ∉ Finset.Icc (-(L : ℤ)) L := fun h => hn (Finset.mem_erase.2 ⟨h0, h⟩)
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hnI
      have hle : (2 : ℝ) ^ k ≤ |(n : ℝ)| := by
        rw [← hLeq]
        rcases hnI with h | h
        · have : ((n : ℤ) : ℝ) < -(L : ℝ) := by exact_mod_cast h
          rw [abs_of_neg (by linarith)]; linarith
        · have : (L : ℝ) < (n : ℝ) := by exact_mod_cast h
          rw [abs_of_pos (by linarith)]; linarith
      rw [hχ.psiK_eq_zero_of_le_abs k hle]
      simp
  have hbil : bilin (fun n => ((psiK χ k n : ℝ) : ℂ) * blockWeight (Finset.Ioc (Q / 2) Q) n) f g x
      = ∑ n ∈ S, ((psiK χ k n : ℝ) : ℂ) * blockWeight (Finset.Ioc (Q / 2) Q) n *
          f (x - n) * g (x + n) := by
    unfold bilin
    exact tsum_eq_sum (fun n hn => by beta_reduce; rw [hsupp n hn]; simp)
  rw [hbil]
  -- termwise bound
  have hterm : ∀ n ∈ S, ‖((psiK χ k n : ℝ) : ℂ) * blockWeight (Finset.Ioc (Q / 2) Q) n *
      f (x - n) * g (x + n)‖ ≤
      c / L * (‖blockWeight (Finset.Ioc (Q / 2) Q) n‖ * (‖f (x - n)‖ * ‖g (x + n)‖)) := by
    intro n _
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := abs_psiK_le hc k n
    rw [← hLeq] at h1
    have h2 : |psiK χ k n| * ‖blockWeight (Finset.Ioc (Q / 2) Q) n‖ ≤
        c / L * ‖blockWeight (Finset.Ioc (Q / 2) Q) n‖ :=
      mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    calc |psiK χ k n| * ‖blockWeight (Finset.Ioc (Q / 2) Q) n‖ * ‖f (x - n)‖ * ‖g (x + n)‖
        = (|psiK χ k n| * ‖blockWeight (Finset.Ioc (Q / 2) Q) n‖) *
            (‖f (x - n)‖ * ‖g (x + n)‖) := by ring
      _ ≤ (c / L * ‖blockWeight (Finset.Ioc (Q / 2) Q) n‖) * (‖f (x - n)‖ * ‖g (x + n)‖) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = _ := by ring
  have h1 : ‖∑ n ∈ S, ((psiK χ k n : ℝ) : ℂ) * blockWeight (Finset.Ioc (Q / 2) Q) n *
      f (x - n) * g (x + n)‖ ≤
      c / L * ∑ n ∈ S, ‖blockWeight (Finset.Ioc (Q / 2) Q) n‖ * (‖f (x - n)‖ * ‖g (x + n)‖) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  -- Hölder in `n`
  have h2 := holder_nat hm hms S (fun n => ‖blockWeight (Finset.Ioc (Q / 2) Q) n‖)
    (fun n => ‖f (x - n)‖ * ‖g (x + n)‖) (fun n => norm_nonneg _)
    (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  -- the second factor is dominated by `(2L+1) B_L(F,G)(x)`
  set Bx := B L (fun y => ((‖f y‖ ^ s : ℝ) : ℂ)) (fun y => ((‖g y‖ ^ s : ℝ) : ℂ)) x with hBx
  have hBx0 : 0 ≤ Bx := B_nonneg _ _ _ _
  have hY : ∑ n ∈ S, (‖f (x - n)‖ * ‖g (x + n)‖) ^ s ≤ 3 * L * Bx := by
    have e1 : ∀ n, (‖f (x - n)‖ * ‖g (x + n)‖) ^ s =
        ‖(((‖f (x - n)‖ ^ s : ℝ)) : ℂ)‖ * ‖(((‖g (x + n)‖ ^ s : ℝ)) : ℂ)‖ := fun n => by
      rw [norm_ofReal_rpow, norm_ofReal_rpow, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    simp_rw [e1]
    have e2 : ∑ n ∈ Finset.Icc (-(L : ℤ)) L,
        ‖(((‖f (x - n)‖ ^ s : ℝ)) : ℂ)‖ * ‖(((‖g (x + n)‖ ^ s : ℝ)) : ℂ)‖ =
        (2 * (L : ℝ) + 1) * Bx := by
      rw [hBx, B, ← mul_assoc, mul_one_div_cancel (by positivity), one_mul]
    calc ∑ n ∈ S, ‖(((‖f (x - n)‖ ^ s : ℝ)) : ℂ)‖ * ‖(((‖g (x + n)‖ ^ s : ℝ)) : ℂ)‖
        ≤ ∑ n ∈ Finset.Icc (-(L : ℤ)) L,
          ‖(((‖f (x - n)‖ ^ s : ℝ)) : ℂ)‖ * ‖(((‖g (x + n)‖ ^ s : ℝ)) : ℂ)‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun n _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (2 * (L : ℝ) + 1) * Bx := e2
      _ ≤ 3 * L * Bx := by gcongr; linarith
  have hX0 : 0 ≤ ∑ n ∈ S, ‖blockWeight (Finset.Ioc (Q / 2) Q) n‖ ^ m :=
    Finset.sum_nonneg fun n _ => by positivity
  have hY0 : 0 ≤ ∑ n ∈ S, (‖f (x - n)‖ * ‖g (x + n)‖) ^ s :=
    Finset.sum_nonneg fun n _ => Real.rpow_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _
  have hXb : (∑ n ∈ S, ‖blockWeight (Finset.Ioc (Q / 2) Q) n‖ ^ m) ^ (1 / (m : ℝ)) ≤
      (2 * L * M) ^ (1 / (m : ℝ)) :=
    Real.rpow_le_rpow hX0 hMom (by positivity)
  have hYb : (∑ n ∈ S, (‖f (x - n)‖ * ‖g (x + n)‖) ^ s) ^ (1 / s) ≤ (3 * L * Bx) ^ (1 / s) :=
    Real.rpow_le_rpow hY0 hY (by positivity)
  calc _ ≤ c / L * ∑ n ∈ S, ‖blockWeight (Finset.Ioc (Q / 2) Q) n‖ *
          (‖f (x - n)‖ * ‖g (x + n)‖) := h1
    _ ≤ c / L * ((2 * L * M) ^ (1 / (m : ℝ)) * (3 * L * Bx) ^ (1 / s)) := by
        refine mul_le_mul_of_nonneg_left (h2.trans ?_) (by positivity)
        exact mul_le_mul hXb hYb (by positivity) (by positivity)
    _ = _ := rpow_combine hLpos hM hBx0 hms

/-! ### From the pointwise bound to `ℓ^r` norms -/

/-- Pointwise `‖T x‖ ≤ K (Bf x)^{1/s}` gives `‖T‖_{ℓ^r} ≤ K ‖Bf‖_{ℓ^{r/s}}^{1/s}`. -/
lemma eLpNorm_le_of_pointwise {T : ℤ → ℂ} {Bf : ℤ → ℝ} {K r s : ℝ} (hK : 0 ≤ K) (hr : 0 < r)
    (hs : 0 < s) (hBf : ∀ x, 0 ≤ Bf x) (h : ∀ x, ‖T x‖ ≤ K * Bf x ^ (1 / s)) :
    eLpNorm T (ENNReal.ofReal r) Measure.count ≤
      ENNReal.ofReal K * eLpNorm Bf (ENNReal.ofReal (r / s)) Measure.count ^ (1 / s) := by
  have hrs : 0 < r / s := div_pos hr hs
  rw [eLpNorm_count_eq T hr, eLpNorm_count_eq Bf hrs]
  have hpt : ∀ x, ENNReal.ofReal ‖T x‖ ^ r ≤
      ENNReal.ofReal K ^ r * ENNReal.ofReal (Bf x) ^ (r / s) := by
    intro x
    have h1 : ENNReal.ofReal ‖T x‖ ≤ ENNReal.ofReal K * ENNReal.ofReal (Bf x) ^ (1 / s) := by
      calc ENNReal.ofReal ‖T x‖ ≤ ENNReal.ofReal (K * Bf x ^ (1 / s)) :=
            ENNReal.ofReal_le_ofReal (h x)
        _ = _ := by
          rw [ENNReal.ofReal_mul hK,
            ENNReal.ofReal_rpow_of_nonneg (hBf x) (by positivity)]
    calc ENNReal.ofReal ‖T x‖ ^ r
        ≤ (ENNReal.ofReal K * ENNReal.ofReal (Bf x) ^ (1 / s)) ^ r :=
          ENNReal.rpow_le_rpow h1 hr.le
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← ENNReal.rpow_mul]
          congr 2
          field_simp
  have hsum : ∑' x, ENNReal.ofReal ‖T x‖ ^ r ≤
      ENNReal.ofReal K ^ r * ∑' x, ENNReal.ofReal ‖Bf x‖ ^ (r / s) := by
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun x => ?_
    rw [Real.norm_of_nonneg (hBf x)]
    exact hpt x
  calc (∑' x, ENNReal.ofReal ‖T x‖ ^ r) ^ (1 / r)
      ≤ (ENNReal.ofReal K ^ r * ∑' x, ENNReal.ofReal ‖Bf x‖ ^ (r / s)) ^ (1 / r) :=
        ENNReal.rpow_le_rpow hsum (by positivity)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        have e1 : r * (1 / r) = 1 := by field_simp
        have e2 : 1 / (r / s) * (1 / s) = 1 / r := by field_simp
        rw [e1, ENNReal.rpow_one, e2]

/-- The `ℓ^{p/s}` norm of `|f|^s` is the `s`-th power of the `ℓ^p` norm of `f`. -/
lemma eLpNorm_norm_rpow_count (f : ℤ → ℂ) {p s : ℝ} (hp : 0 < p) (hs : 0 < s) :
    eLpNorm (fun y => ((‖f y‖ ^ s : ℝ) : ℂ)) (ENNReal.ofReal (p / s)) Measure.count =
      eLpNorm f (ENNReal.ofReal p) Measure.count ^ s := by
  have hps : 0 < p / s := div_pos hp hs
  rw [eLpNorm_count_eq _ hps, eLpNorm_count_eq f hp, ← ENNReal.rpow_mul]
  have e1 : ∀ y, ENNReal.ofReal ‖(((‖f y‖ ^ s : ℝ)) : ℂ)‖ ^ (p / s) = ENNReal.ofReal ‖f y‖ ^ p := by
    intro y
    rw [norm_ofReal_rpow, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hs.le, ← ENNReal.rpow_mul]
    congr 1
    field_simp
  simp_rw [e1]
  congr 1
  field_simp

/-! ### The main estimate -/

/-- **N12 (a), `e:single-rough`** (blueprint node N12): for `1 < p, q < ∞` and
`1/r = 1/p + 1/q` there are `b ≥ 0` and `C ≥ 0` (depending on `χ, p, q, r` only) such that for all
natural `Q ≥ 1`, all scales `k`, and all `f, g : ℤ → ℂ`
`‖x ↦ ∑ₙ ψ_k(n) w_Q(n) f(x-n) g(x+n)‖_{ℓ^r} ≤ C (1 + log Q)^b ‖f‖_{ℓ^p} ‖g‖_{ℓ^q}`.
Here `w_Q = blockWeight (Ioc (Q/2) Q)`, the sum is `bilin`, and `ℓ^r` is `eLpNorm` for counting
measure on `ℤ` (a quasi-norm when `r < 1`; `r > 1/2` is automatic). -/
theorem eLpNorm_bilin_psiK_blockWeight_le {χ : ℝ → ℝ} (hχ : IsCutoff χ) {p q r : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 / r = 1 / p + 1 / q) :
    ∃ b C : ℝ, 0 ≤ b ∧ 0 ≤ C ∧ ∀ (Q k : ℕ), 1 ≤ Q → ∀ f g : ℤ → ℂ,
      eLpNorm (bilin (fun n => ((psiK χ k n : ℝ) : ℂ) * blockWeight (Finset.Ioc (Q / 2) Q) n) f g)
          (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * (1 + Real.log Q) ^ b) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count := by
  obtain ⟨m, s, hm, hs1, hsp, hsq, hms⟩ := exists_nat_conj hp hq
  obtain ⟨c, hc0, hc⟩ := hχ.exists_bound_psi
  obtain ⟨Cm, hCm0, hCm⟩ := sum_blockWeight_pow_le m (by omega)
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < s := by linarith
  have hm0 : (0 : ℝ) < m := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hr0 : 0 < r := by
    have : 0 < 1 / r := by rw [hr]; positivity
    exact one_div_pos.1 this
  refine ⟨((2 : ℝ) ^ m + m) / m,
    c * 3 ^ (1 / s) * (2 * Cm) ^ (1 / (m : ℝ)) * 9 ^ (1 / s), by positivity, by positivity, ?_⟩
  intro Q k hQ f g
  have hl0 : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ)
  set ℓ : ℝ := 1 + Real.log Q with hℓ
  have hℓ0 : 0 < ℓ := by linarith
  set M : ℝ := Cm * ℓ ^ (2 ^ m + m) with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hMom := hCm Q (2 ^ k) hQ Nat.one_le_two_pow
  have hpt := fun x => norm_bilin_le hχ hc hm hms Q k hM0 hMom f g x
  set F : ℤ → ℂ := fun y => ((‖f y‖ ^ s : ℝ) : ℂ) with hF
  set G : ℤ → ℂ := fun y => ((‖g y‖ ^ s : ℝ) : ℂ) with hG
  set K : ℝ := c * 3 ^ (1 / s) * (2 * M) ^ (1 / (m : ℝ)) with hK
  have hK0 : 0 ≤ K := by positivity
  have h1 := eLpNorm_le_of_pointwise (T := bilin (fun n => ((psiK χ k n : ℝ) : ℂ) *
      blockWeight (Finset.Ioc (Q / 2) Q) n) f g) (Bf := B (2 ^ k) F G) hK0 hr0 hs0
    (fun x => B_nonneg _ _ _ _) hpt
  -- N11 at `F = |f|^s`, `G = |g|^s`
  have hu : (1 : ℝ) ≤ p / s := by rw [le_div_iff₀ hs0]; linarith
  have hv : (1 : ℝ) ≤ q / s := by rw [le_div_iff₀ hs0]; linarith
  have huvt : 1 / (r / s) = 1 / (p / s) + 1 / (q / s) := by
    have : 1 / (r / s) = s * (1 / r) := by field_simp
    rw [this, hr]
    field_simp
  have h2 := eLpNorm_B_le_real (2 ^ k) F G hu hv huvt
  rw [hF, hG, eLpNorm_norm_rpow_count f hp0 hs0, eLpNorm_norm_rpow_count g hq0 hs0] at h2
  have h3 : eLpNorm (B (2 ^ k) F G) (ENNReal.ofReal (r / s)) Measure.count ^ (1 / s) ≤
      (9 : ℝ≥0∞) ^ (1 / s) * eLpNorm f (ENNReal.ofReal p) Measure.count *
        eLpNorm g (ENNReal.ofReal q) Measure.count := by
    calc _ ≤ (9 * eLpNorm f (ENNReal.ofReal p) Measure.count ^ s *
            eLpNorm g (ENNReal.ofReal q) Measure.count ^ s) ^ (1 / s) :=
          ENNReal.rpow_le_rpow h2 (by positivity)
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
            ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            ← ENNReal.rpow_mul, mul_one_div_cancel hs0.ne', ENNReal.rpow_one, ENNReal.rpow_one]
  have e9 : ENNReal.ofReal ((9 : ℝ) ^ (1 / s)) = (9 : ℝ≥0∞) ^ (1 / s) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by positivity), ENNReal.ofReal_ofNat]
  -- the constant
  have hconst : K * 9 ^ (1 / s) = c * 3 ^ (1 / s) * (2 * Cm) ^ (1 / (m : ℝ)) * 9 ^ (1 / s) *
      ℓ ^ (((2 : ℝ) ^ m + m) / m) := by
    have e1 : (2 * M) ^ (1 / (m : ℝ)) = (2 * Cm) ^ (1 / (m : ℝ)) * ℓ ^ (((2 : ℝ) ^ m + m) / m) := by
      rw [hMdef, show 2 * (Cm * ℓ ^ (2 ^ m + m)) = (2 * Cm) * ℓ ^ (2 ^ m + m) by ring,
        Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_mul hℓ0.le]
      congr 2
      push_cast
      ring
    rw [hK, e1]
    ring
  calc _ ≤ ENNReal.ofReal K * eLpNorm (B (2 ^ k) F G) (ENNReal.ofReal (r / s)) Measure.count ^
        (1 / s) := h1
    _ ≤ ENNReal.ofReal K * ((9 : ℝ≥0∞) ^ (1 / s) * eLpNorm f (ENNReal.ofReal p) Measure.count *
        eLpNorm g (ENNReal.ofReal q) Measure.count) := by gcongr
    _ = ENNReal.ofReal (K * 9 ^ (1 / s)) * eLpNorm f (ENNReal.ofReal p) Measure.count *
        eLpNorm g (ENNReal.ofReal q) Measure.count := by
        rw [ENNReal.ofReal_mul hK0, e9]
        ring
    _ = _ := by rw [hconst]

/-- **N12 (a), `e:single-rough`, dyadic form**: as `eLpNorm_bilin_psiK_blockWeight_le`, for
dyadic `Q = 2^j` (so `w_Q = Λ_Q` is the Heath-Brown block `blockWeight (Ioc (2^j/2) (2^j))`). -/
theorem eLpNorm_single_rough {χ : ℝ → ℝ} (hχ : IsCutoff χ) {p q r : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 / r = 1 / p + 1 / q) :
    ∃ b C : ℝ, 0 ≤ b ∧ 0 ≤ C ∧ ∀ (Q k : ℕ), (∃ j : ℕ, Q = 2 ^ j) → ∀ f g : ℤ → ℂ,
      eLpNorm (bilin (fun n => ((psiK χ k n : ℝ) : ℂ) * blockWeight (Finset.Ioc (Q / 2) Q) n) f g)
          (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * (1 + Real.log Q) ^ b) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count := by
  obtain ⟨b, C, hb, hC, h⟩ := eLpNorm_bilin_psiK_blockWeight_le hχ hp hq hr
  refine ⟨b, C, hb, hC, fun Q k hQ f g => ?_⟩
  obtain ⟨j, rfl⟩ := hQ
  exact h _ k Nat.one_le_two_pow f g

/-- `(1 + log Q)^b ≲_ε Q^ε` for every `b ≥ 0`, `ε > 0` and `Q ≥ 1`. -/
lemma one_add_log_rpow_le {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℝ, 1 ≤ Q → (1 + Real.log Q) ^ b ≤ C * Q ^ ε := by
  rcases hb.eq_or_lt with rfl | hb0
  · exact ⟨1, zero_le_one, fun Q hQ => by simpa using Real.one_le_rpow hQ hε.le⟩
  · have hδ : 0 < ε / b := div_pos hε hb0
    refine ⟨(1 + 1 / (ε / b)) ^ b, by positivity, fun Q hQ => ?_⟩
    have hQ0 : 0 ≤ Q := by linarith
    have h1 : Real.log Q ≤ Q ^ (ε / b) / (ε / b) := Real.log_le_rpow_div hQ0 hδ
    have h2 : 1 ≤ Q ^ (ε / b) := Real.one_le_rpow hQ hδ.le
    have h3 : 1 + Real.log Q ≤ (1 + 1 / (ε / b)) * Q ^ (ε / b) := by
      have : Q ^ (ε / b) / (ε / b) = 1 / (ε / b) * Q ^ (ε / b) := by ring
      nlinarith
    calc (1 + Real.log Q) ^ b ≤ ((1 + 1 / (ε / b)) * Q ^ (ε / b)) ^ b :=
          Real.rpow_le_rpow (by linarith [Real.log_nonneg hQ]) h3 hb
      _ = (1 + 1 / (ε / b)) ^ b * (Q ^ (ε / b)) ^ b :=
          Real.mul_rpow (by positivity) (by positivity)
      _ = _ := by
          rw [← Real.rpow_mul hQ0]
          congr 2
          field_simp

/-- **N12 (a)**, "in particular" form: for every `ε > 0` the loss may be taken `C_ε Q^ε`
(dyadic `Q`). -/
theorem eLpNorm_single_rough_rpow {χ : ℝ → ℝ} (hχ : IsCutoff χ) {p q r : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 / r = 1 / p + 1 / q) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q k : ℕ), (∃ j : ℕ, Q = 2 ^ j) → ∀ f g : ℤ → ℂ,
      eLpNorm (bilin (fun n => ((psiK χ k n : ℝ) : ℂ) * blockWeight (Finset.Ioc (Q / 2) Q) n) f g)
          (ENNReal.ofReal r) Measure.count ≤
        ENNReal.ofReal (C * (Q : ℝ) ^ ε) *
          eLpNorm f (ENNReal.ofReal p) Measure.count *
            eLpNorm g (ENNReal.ofReal q) Measure.count := by
  obtain ⟨b, C, hb, hC, h⟩ := eLpNorm_single_rough hχ hp hq hr
  obtain ⟨C', hC', hC'le⟩ := one_add_log_rpow_le hb hε
  refine ⟨C * C', by positivity, fun Q k hQ f g => ?_⟩
  have hQ1 : (1 : ℝ) ≤ Q := by
    obtain ⟨j, rfl⟩ := hQ
    exact_mod_cast Nat.one_le_two_pow
  refine (h Q k hQ f g).trans ?_
  have : C * (1 + Real.log Q) ^ b ≤ C * C' * (Q : ℝ) ^ ε := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC'le _ hQ1) hC
  gcongr

end PrimeBHT.SingleScale
