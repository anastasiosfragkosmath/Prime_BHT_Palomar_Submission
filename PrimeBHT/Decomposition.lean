module

public import PrimeBHT.Kernel
public import PrimeCarleson.Proof.Paper.Defs.Weights

/-!
# The exact decomposition `e:exactred` (blueprint node N23, index-set facts of N00)

Objects (all reusing the audited vendored model `PrimeCarleson.heathBrownModel`
`= ∑_{j : 2^j ≤ T} blockWeight (Ioc (2^j/2) (2^j))`, dyadic `Q = 2^j`, `j ≥ 0`, `Q = 1` included):

* `Mk k = M_k = exp ((log 2^k)^{1/10})` (literally the cutoff of the vendored `X3`);
* `bQ Q = b_Q = min {k ≥ 1 : Q ≤ M_k}`, with `bQ_eq : b_Q = max 1 ⌈(log Q)^10 / log 2⌉` (`Q ≥ 1`);
* `w n = Λ(|n|)` (`w 0 = 0`), `wLe T n = Λ_{≤T}(|n|)`, `E k = w - w_{≤M_k}`;
* `dyadicSet T = {j : 2^j ≤ T}` as the finite set used by `heathBrownModel`, `jset J = dyadicSet (M_J)`;
* `Tk χ j k f g x = ∑_n ψ_k(n) w_{2^j}(n) f(x-n) g(x+n)`, `Serr`, `HJ`, `Hmod`, `Utail`.

Main results: `bQ_eq`, `le_Mk_iff_bQ_le` (`Q ≤ M_k ↔ b_Q ≤ k`), `w_eq_E_add_sum` (`w = E_k + ∑_{Q ≤ M_k} w_Q`),
`exactred_weights` (the identity at the level of the weights `ψ_k(n) · (·)`, no summability),
`exactred` (the identity of operators for finitely supported `f, g`), `exists_bQ_le_rpow`
(`b_Q ≤ Q^τ` for large dyadic `Q`), `Utail_eq_zero_of_lt` and `Hmod_eq_of_lt` (`J < ⌈Q^τ⌉`).

Index sets: every pair `(Q = 2^j, k)` with `b_Q ≤ k ≤ J` appears exactly once, where
`j ∈ jset J ↔ 2^j ≤ M_J ↔ b_{2^j} ≤ J` (`mem_jset_iff`).
-/

@[expose] public section

open PrimeBHT.Kernel PrimeCarleson PrimeCarleson.Proof.Paper

namespace PrimeBHT.Decomposition

/-! ### `M_k`, `b_Q` -/

/-- `M_k = exp ((log 2^k)^{1/10})`. -/
noncomputable def Mk (k : ℕ) : ℝ := Real.exp (Real.log ((2 : ℝ) ^ k) ^ ((1 : ℝ) / 10))

/-- `b_Q = min {k ≥ 1 : Q ≤ M_k}`. -/
noncomputable def bQ (Q : ℝ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ Q ≤ Mk k}

/-- For `Q ≥ 1`: `Q ≤ M_k ↔ (log Q)^10 / log 2 ≤ k`. -/
theorem le_Mk_iff {Q : ℝ} (hQ : 1 ≤ Q) (k : ℕ) :
    Q ≤ Mk k ↔ Real.log Q ^ 10 / Real.log 2 ≤ k := by
  have hQpos : 0 < Q := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hk : 0 ≤ (k : ℝ) * Real.log 2 := by positivity
  rw [Mk, ← Real.log_le_iff_le_exp hQpos, Real.log_pow, one_div,
    Real.le_rpow_inv_iff_of_pos hlQ hk (by norm_num), div_le_iff₀ hlog2]
  have : Real.log Q ^ (10 : ℝ) = Real.log Q ^ 10 := by simp
  rw [this]

theorem div_nonneg_aux {Q : ℝ} (hQ : 1 ≤ Q) : 0 ≤ Real.log Q ^ 10 / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : 0 ≤ Real.log Q := Real.log_nonneg hQ
  positivity

/-- The formula `b_Q = max {1, ⌈(log Q)^10 / log 2⌉}` for real `Q ≥ 1`. -/
theorem bQ_eq {Q : ℝ} (hQ : 1 ≤ Q) :
    bQ Q = max 1 ⌈Real.log Q ^ 10 / Real.log 2⌉₊ := by
  set x := Real.log Q ^ 10 / Real.log 2 with hx
  have hmem : max 1 ⌈x⌉₊ ∈ {k : ℕ | 1 ≤ k ∧ Q ≤ Mk k} := by
    refine ⟨le_max_left _ _, ?_⟩
    rw [le_Mk_iff hQ]
    exact (Nat.le_ceil x).trans (by exact_mod_cast le_max_right 1 ⌈x⌉₊)
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · apply le_csInf ⟨_, hmem⟩
    rintro k ⟨hk1, hk⟩
    rw [le_Mk_iff hQ] at hk
    exact max_le hk1 (Nat.ceil_le.mpr hk)

theorem one_le_bQ {Q : ℝ} (hQ : 1 ≤ Q) : 1 ≤ bQ Q := by
  rw [bQ_eq hQ]; exact le_max_left _ _

/-- `Q ≤ M_k ↔ b_Q ≤ k` for real `Q ≥ 1` and `k ≥ 1`. -/
theorem le_Mk_iff_bQ_le {Q : ℝ} (hQ : 1 ≤ Q) {k : ℕ} (hk : 1 ≤ k) :
    Q ≤ Mk k ↔ bQ Q ≤ k := by
  rw [bQ_eq hQ, max_le_iff, le_Mk_iff hQ, Nat.ceil_le]
  exact ⟨fun h => ⟨hk, h⟩, fun h => h.2⟩

/-- The same for dyadic `Q = 2^j`. -/
theorem two_pow_le_Mk_iff {j k : ℕ} (hk : 1 ≤ k) : (2 : ℝ) ^ j ≤ Mk k ↔ bQ ((2 : ℝ) ^ j) ≤ k :=
  le_Mk_iff_bQ_le (one_le_pow₀ (by norm_num)) hk

theorem one_le_bQ_two_pow (j : ℕ) : 1 ≤ bQ ((2 : ℝ) ^ j) := one_le_bQ (one_le_pow₀ (by norm_num))

/-! ### The weights `w`, `w_{≤T}`, `E_k` -/

/-- `w(n) = Λ(|n|)` as a complex number (`w(0) = Λ(0) = 0`). -/
noncomputable def w (n : ℤ) : ℂ := ((ArithmeticFunction.vonMangoldt n.natAbs : ℝ) : ℂ)

/-- `w_{≤T}(n) = Λ_{≤T}(|n|)` with the vendored `Λ_{≤T} = heathBrownModel T`. -/
noncomputable def wLe (T : ℝ) (n : ℤ) : ℂ := heathBrownModel T |n|

/-- The error `E_k = w - w_{≤M_k}`. -/
noncomputable def E (k : ℕ) (n : ℤ) : ℂ := w n - wLe (Mk k) n

theorem w_neg (n : ℤ) : w (-n) = w n := by simp [w]

/-- `w_{≤T}(n) = Λ_{≤T}(n)`: the vendored model is even. -/
theorem wLe_eq (T : ℝ) (n : ℤ) : wLe T n = heathBrownModel T n := by
  rcases abs_choice n with h | h
  · rw [wLe, h]
  · rw [wLe, h, heathBrownModel_neg]

/-- Same as the statement of the vendored `X3`, in terms of the vendored model for natural `n`. -/
theorem E_eq (k : ℕ) (n : ℤ) :
    E k n = ((ArithmeticFunction.vonMangoldt n.natAbs : ℝ) : ℂ) - heathBrownModel (Mk k) n := by
  rw [E, wLe_eq]; rfl

/-- Interface with the vendored `X3` (`vonMangoldt_sub_heathBrown_U3`), which writes the summand for
positive `n` with `n.toNat`: it is `E_k(n)`. -/
theorem E_eq_of_pos (k : ℕ) {n : ℤ} (hn : 0 ≤ n) :
    E k n = ((ArithmeticFunction.vonMangoldt n.toNat : ℝ) : ℂ) - heathBrownModel (Mk k) n := by
  have : n.natAbs = n.toNat := by omega
  rw [E_eq, this]

theorem E_neg (k : ℕ) (n : ℤ) : E k (-n) = E k n := by
  simp [E, w_neg, wLe_eq, heathBrownModel_neg]

/-! ### The dyadic index sets -/

/-- The finite set `{j : 2^j ≤ T}` used by `heathBrownModel T`. -/
noncomputable def dyadicSet (T : ℝ) : Finset ℕ :=
  (Finset.range (⌊T⌋₊ + 1)).filter (fun j => (2 : ℝ) ^ j ≤ T)

theorem mem_dyadicSet {T : ℝ} {j : ℕ} : j ∈ dyadicSet T ↔ (2 : ℝ) ^ j ≤ T := by
  simp only [dyadicSet, Finset.mem_filter, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have h1 : (j : ℝ) < (2 : ℝ) ^ j := by exact_mod_cast Nat.lt_two_pow_self
  have : j ≤ ⌊T⌋₊ := Nat.le_floor (by linarith)
  omega

/-- The vendored model is the dyadic sum of the vendored weights `w_Q`, `Q = 2^j`, `j ∈ dyadicSet T`. -/
theorem heathBrownModel_eq_sum_dyadicSet (T : ℝ) (n : ℤ) :
    heathBrownModel T n = ∑ j ∈ dyadicSet T, wQ (2 ^ j) n := rfl

/-- The finite set of dyadic exponents `j` with `2^j ≤ M_J`. -/
noncomputable abbrev jset (J : ℕ) : Finset ℕ := dyadicSet (Mk J)

/-- `j ∈ jset J ↔ 2^j ≤ M_J ↔ b_{2^j} ≤ J` (for `J ≥ 1`). -/
theorem mem_jset_iff {J j : ℕ} (hJ : 1 ≤ J) : j ∈ jset J ↔ bQ ((2 : ℝ) ^ j) ≤ J := by
  rw [mem_dyadicSet, two_pow_le_Mk_iff hJ]

/-! ### (2) The decomposition of `w` -/

/-- `w = E_k + ∑_{dyadic Q ≤ M_k} w_Q` (a definition of `E_k`, made explicit with the vendored model). -/
theorem w_eq_E_add_sum (k : ℕ) (n : ℤ) :
    w n = E k n + ∑ j ∈ jset k, wQ (2 ^ j) n := by
  rw [← heathBrownModel_eq_sum_dyadicSet, E, wLe_eq]
  ring

/-! ### The reindexing of finite sums -/

section Reindex

variable {A : Type*} [AddCommMonoid A]

/-- `∑_{k=1}^J ∑_{Q ≤ M_k} = ∑_{Q ≤ M_J} ∑_{b_Q ≤ k ≤ J}`: each pair `(2^j, k)` with `b ≤ k ≤ J` once. -/
theorem sum_Icc_sum_jset (J : ℕ) (F : ℕ → ℕ → A) :
    ∑ k ∈ Finset.Icc 1 J, ∑ j ∈ jset k, F k j =
      ∑ j ∈ jset J, ∑ k ∈ Finset.Icc (bQ ((2 : ℝ) ^ j)) J, F k j := by
  refine Finset.sum_comm' ?_
  intro k j
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hk1, hkJ⟩, hj⟩
    rw [mem_jset_iff hk1] at hj
    refine ⟨⟨hj, hkJ⟩, ?_⟩
    rw [mem_jset_iff (by omega)]; omega
  · rintro ⟨⟨hbk, hkJ⟩, hj⟩
    have h1 := one_le_bQ_two_pow j
    rw [mem_jset_iff (by omega)] at hj
    refine ⟨⟨by omega, hkJ⟩, ?_⟩
    rw [mem_jset_iff (by omega)]; exact hbk

/-- For `b ≤ Q^τ` the range `[b, J]` is the disjoint union of the moderate part `k < Q^τ` and
the tail `⌈Q^τ⌉ ≤ k ≤ J`. -/
theorem sum_Icc_split {b J : ℕ} {a : ℝ} (hb : (b : ℝ) ≤ a) (G : ℕ → A) :
    ∑ k ∈ Finset.Icc b J, G k =
      ∑ k ∈ (Finset.Icc b J).filter (fun k : ℕ => (k : ℝ) < a), G k +
        ∑ k ∈ Finset.Icc ⌈a⌉₊ J, G k := by
  have hba : b ≤ ⌈a⌉₊ := by
    have : (b : ℝ) ≤ (⌈a⌉₊ : ℝ) := hb.trans (Nat.le_ceil a)
    exact_mod_cast this
  have hset : (Finset.Icc b J).filter (fun k : ℕ => ¬ (k : ℝ) < a) = Finset.Icc ⌈a⌉₊ J := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, not_lt]
    constructor
    · rintro ⟨⟨_, hkJ⟩, hk⟩
      exact ⟨Nat.ceil_le.mpr hk, hkJ⟩
    · rintro ⟨hk, hkJ⟩
      exact ⟨⟨hba.trans hk, hkJ⟩, Nat.ceil_le.mp hk⟩
  rw [← hset, Finset.sum_filter_add_sum_filter_not]

/-- The abstract form of `e:exactred`.  `a k = e k + ∑_{Q ≤ M_k} t k Q` for `1 ≤ k ≤ J`
(this is the decomposition of `w`), `C` a threshold with `b_Q ≤ Q^τ` for dyadic `Q > C`. -/
theorem exactred_abstract (J : ℕ) (τ C : ℝ)
    (hC : ∀ j : ℕ, C < (2 : ℝ) ^ j → (bQ ((2 : ℝ) ^ j) : ℝ) ≤ ((2 : ℝ) ^ j) ^ τ)
    (a e : ℕ → A) (t : ℕ → ℕ → A)
    (h : ∀ k ∈ Finset.Icc 1 J, a k = e k + ∑ j ∈ jset k, t k j) :
    ∑ k ∈ Finset.Icc 1 J, a k =
      ∑ k ∈ Finset.Icc 1 J, e k
        + ∑ j ∈ (jset J).filter (fun j => (2 : ℝ) ^ j ≤ C),
            ∑ k ∈ Finset.Icc (bQ ((2 : ℝ) ^ j)) J, t k j
        + ∑ j ∈ (jset J).filter (fun j => ¬ (2 : ℝ) ^ j ≤ C),
            (∑ k ∈ (Finset.Icc (bQ ((2 : ℝ) ^ j)) J).filter
                (fun k : ℕ => (k : ℝ) < ((2 : ℝ) ^ j) ^ τ), t k j
              + ∑ k ∈ Finset.Icc ⌈((2 : ℝ) ^ j) ^ τ⌉₊ J, t k j) := by
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, sum_Icc_sum_jset J t, add_assoc]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not (jset J) (fun j => (2 : ℝ) ^ j ≤ C)]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_filter] at hj
  exact sum_Icc_split (hC j (not_le.mp hj.2)) (fun k => t k j)

end Reindex

/-! ### Operators and the exact identity for finitely supported `f, g` -/

section Operators

variable (χ : ℝ → ℝ)

/-- `T_k^Q(f,g)(x) = ∑_n ψ_k(n) w_Q(n) f(x-n) g(x+n)` for `Q = 2^j` (an absolutely convergent
`tsum`; a finite sum for finitely supported `f, g`). -/
noncomputable def Tk (j k : ℕ) (f g : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑' n : ℤ, (psiK χ k n : ℂ) * wQ (2 ^ j) n * f (x - n) * g (x + n)

/-- `S_k^err(f,g)(x) = ∑_n ψ_k(n) E_k(n) f(x-n) g(x+n)`. -/
noncomputable def Serr (k : ℕ) (f g : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑' n : ℤ, (psiK χ k n : ℂ) * E k n * f (x - n) * g (x + n)

/-- `H^J(f,g)(x) = ∑_{k=1}^J ∑_n ψ_k(n) w(n) f(x-n) g(x+n)`. -/
noncomputable def HJ (J : ℕ) (f g : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 J, ∑' n : ℤ, (psiK χ k n : ℂ) * w n * f (x - n) * g (x + n)

/-- `H^J_{Q,mod;τ}(f,g) = ∑_{b_Q ≤ k < Q^τ, k ≤ J} T_k^Q(f,g)`, `Q = 2^j`. -/
noncomputable def Hmod (τ : ℝ) (J j : ℕ) (f g : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑ k ∈ (Finset.Icc (bQ ((2 : ℝ) ^ j)) J).filter (fun k : ℕ => (k : ℝ) < ((2 : ℝ) ^ j) ^ τ),
    Tk χ j k f g x

/-- `U^J_{Q;τ}(f,g) = ∑_{Q^τ ≤ k ≤ J} T_k^Q(f,g)`, `Q = 2^j` (`k ≥ ⌈Q^τ⌉`). -/
noncomputable def Utail (τ : ℝ) (J j : ℕ) (f g : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑ k ∈ Finset.Icc ⌈((2 : ℝ) ^ j) ^ τ⌉₊ J, Tk χ j k f g x

variable {χ}

/-- Summability of the summand when `f` has finite support. -/
theorem summable_summand {f : ℤ → ℂ} (hf : f.support.Finite) (K : ℤ → ℂ) (g : ℤ → ℂ) (x : ℤ) :
    Summable fun n : ℤ => K n * f (x - n) * g (x + n) := by
  classical
  refine summable_of_ne_finset_zero (s := hf.toFinset.image (fun m => x - m)) ?_
  intro n hn
  have : f (x - n) = 0 := by
    by_contra hne
    exact hn (Finset.mem_image.mpr ⟨x - n, by simpa using hne, by ring⟩)
  simp [this]

/-! #### The identity at the level of the weights (no summability needed) -/

/-! #### The identity of operators for finitely supported `f, g` -/

/-- For each scale `k`: `ψ_k w = ψ_k E_k + ∑_{Q ≤ M_k} ψ_k w_Q`, summed against `f(x-n) g(x+n)`. -/
theorem sum_w_eq_Serr_add {f g : ℤ → ℂ} (hf : f.support.Finite) (x : ℤ) (k : ℕ) :
    ∑' n : ℤ, (psiK χ k n : ℂ) * w n * f (x - n) * g (x + n) =
      Serr χ k f g x + ∑ j ∈ jset k, Tk χ j k f g x := by
  have hs : ∀ n : ℤ, (psiK χ k n : ℂ) * w n * f (x - n) * g (x + n) =
      (psiK χ k n : ℂ) * E k n * f (x - n) * g (x + n) +
        ∑ j ∈ jset k, (psiK χ k n : ℂ) * wQ (2 ^ j) n * f (x - n) * g (x + n) := by
    intro n
    rw [w_eq_E_add_sum k n]
    simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
  have h1 : Summable fun n : ℤ => (psiK χ k n : ℂ) * E k n * f (x - n) * g (x + n) :=
    summable_summand hf (fun n => (psiK χ k n : ℂ) * E k n) g x
  have h2 : Summable fun n : ℤ =>
      ∑ j ∈ jset k, (psiK χ k n : ℂ) * wQ (2 ^ j) n * f (x - n) * g (x + n) :=
    summable_sum fun j _ => summable_summand hf (fun n => (psiK χ k n : ℂ) * wQ (2 ^ j) n) g x
  rw [tsum_congr hs, h1.tsum_add h2, Summable.tsum_finsetSum
    (fun j _ => summable_summand hf (fun n => (psiK χ k n : ℂ) * wQ (2 ^ j) n) g x)]
  rfl

/-- **The exact identity `e:exactred`** (blueprint N23), pointwise in `x`, for finitely supported
`f, g` (so all `n`-sums are finite).  `C` is any threshold such that `b_Q ≤ Q^τ` for every dyadic
`Q = 2^j > C` (it exists for every `τ > 0`, see `exists_bQ_le_rpow`).  All sums over dyadic `Q = 2^j`
run over the finite set `jset J = {j : 2^j ≤ M_J} = {j : b_{2^j} ≤ J}`; the inner `k`-ranges are
`[b_Q, J]` (for `Q ≤ C`), `[b_Q, Q^τ) ∩ [b_Q, J]` and `[⌈Q^τ⌉, J]` (for `Q > C`). -/
theorem exactred (J : ℕ) (τ C : ℝ)
    (hC : ∀ j : ℕ, C < (2 : ℝ) ^ j → (bQ ((2 : ℝ) ^ j) : ℝ) ≤ ((2 : ℝ) ^ j) ^ τ)
    {f g : ℤ → ℂ} (hf : f.support.Finite) (x : ℤ) :
    HJ χ J f g x =
      ∑ k ∈ Finset.Icc 1 J, Serr χ k f g x
        + ∑ j ∈ (jset J).filter (fun j => (2 : ℝ) ^ j ≤ C),
            ∑ k ∈ Finset.Icc (bQ ((2 : ℝ) ^ j)) J, Tk χ j k f g x
        + ∑ j ∈ (jset J).filter (fun j => ¬ (2 : ℝ) ^ j ≤ C),
            (Hmod χ τ J j f g x + Utail χ τ J j f g x) :=
  exactred_abstract J τ C hC
    (fun k => ∑' n : ℤ, (psiK χ k n : ℂ) * w n * f (x - n) * g (x + n))
    (fun k => Serr χ k f g x) (fun k j => Tk χ j k f g x)
    (fun k _ => sum_w_eq_Serr_add hf x k)

end Operators

/-! ### Existence of the threshold `C` -/

/-- `b_{2^j} ≤ (log 2)^9 j^10 + 1`. -/
theorem bQ_two_pow_le (j : ℕ) :
    (bQ ((2 : ℝ) ^ j) : ℝ) ≤ Real.log 2 ^ 9 * (j : ℝ) ^ 10 + 1 := by
  have hQ : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx : Real.log ((2 : ℝ) ^ j) ^ 10 / Real.log 2 = Real.log 2 ^ 9 * (j : ℝ) ^ 10 := by
    rw [Real.log_pow]
    field_simp
  have hnn : 0 ≤ Real.log ((2 : ℝ) ^ j) ^ 10 / Real.log 2 := div_nonneg_aux hQ
  rw [bQ_eq hQ, hx]
  rw [hx] at hnn
  have h1 := Nat.ceil_lt_add_one hnn
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le (by linarith) h1.le

/-- For every `τ > 0`: `b_Q ≤ Q^τ` for all dyadic `Q = 2^j` with `j > j₀`. -/
theorem exists_bQ_le_rpow {τ : ℝ} (hτ : 0 < τ) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ < j → (bQ ((2 : ℝ) ^ j) : ℝ) ≤ ((2 : ℝ) ^ j) ^ τ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : 0 < τ * Real.log 2 := mul_pos hτ hlog2
  have hL9 : 0 < Real.log 2 ^ 9 := pow_pos hlog2 9
  have hlo := isLittleO_pow_exp_pos_mul_atTop 10 ha
  have hc : (0 : ℝ) < 1 / (2 * Real.log 2 ^ 9) := by positivity
  have hev1 := hlo.bound hc
  have hev2 : ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ Real.exp (τ * Real.log 2 * x) :=
    (Real.tendsto_exp_atTop.comp (Filter.tendsto_id.const_mul_atTop ha)).eventually_ge_atTop 2
  have hev3 : ∀ᶠ x : ℝ in Filter.atTop, 0 ≤ x := Filter.eventually_ge_atTop 0
  have hev := (hev1.and hev2).and hev3
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨N, fun j hj => ?_⟩
  obtain ⟨⟨hb, hE⟩, hj0⟩ := hN j hj.le
  have hbq := bQ_two_pow_le j
  have hpow : ((2 : ℝ) ^ j) ^ τ = Real.exp (τ * Real.log 2 * (j : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num)]
    congr 1; ring
  rw [hpow]
  set Ex := Real.exp (τ * Real.log 2 * (j : ℝ)) with hEx
  have hEpos : 0 < Ex := Real.exp_pos _
  rw [Real.norm_of_nonneg (pow_nonneg hj0 10), Real.norm_of_nonneg hEpos.le] at hb
  have h4 : Real.log 2 ^ 9 * (j : ℝ) ^ 10 ≤ Real.log 2 ^ 9 * (1 / (2 * Real.log 2 ^ 9) * Ex) :=
    mul_le_mul_of_nonneg_left hb hL9.le
  have h5 : Real.log 2 ^ 9 * (1 / (2 * Real.log 2 ^ 9) * Ex) = Ex / 2 := by
    field_simp
  linarith

section Final

variable (χ : ℝ → ℝ)

end Final

end PrimeBHT.Decomposition
