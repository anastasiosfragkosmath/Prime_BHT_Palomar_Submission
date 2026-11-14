module

public import PrimeBHT.Decomposition
public import PrimeCarleson.Proof.KMTT.BlockMoment
public import PrimeCarleson.Proof.Paper.Defs.Weights

/-!
# N20, moments of `E_k = Λ - Λ_{≤ M_k}` (ingredient of `e:errrough`)

* `heathBrownModel_eq_blockWeight_hbIndex`: for `T ≥ 1` the cumulative Heath-Brown model is
  `Λ_{HB,Q'}` with the KMTT index set `{1 ≤ q < Q'}`, `Q' = 2^J + 1 ≤ 2T`
  (telescoping `w_{2^j} = Λ_{HB,2^j+1} - Λ_{HB,2^{j-1}+1}`).
* `moment_heathBrownModel`: KMTT Lemma 4.6 (display (4.8)) for the cumulative approximant:
  `E_{n ∈ [N]} |Λ_{≤T}(n)|^m ≤ C_m (1 + log T)^(2^m + m)`.
* `sum_E_pow_le`: the polylogarithmic moment of `E_k` on `0 < |n| ≤ 2^k`:
  `∑_{0<|n|≤2^k} |E_k(n)|^m ≤ 2 · 2^k · C k^{m + (2^m+m)/10}`
  (`Λ(n) ≤ log n ≤ k` pointwise, and `log M_k = (k log 2)^{1/10} ≤ k^{1/10}`).
-/

@[expose] public section

open Finset
open PrimeCarleson PrimeCarleson.Proof.KMTT PrimeCarleson.Proof.Paper

namespace PrimeBHT.ErrorTerms

open PrimeBHT.Decomposition

/-! ### The cumulative model as a KMTT Heath-Brown approximant -/

lemma hbIndex_one : hbIndex ((1 : ℕ) : ℝ) = ∅ := by
  unfold hbIndex
  rw [Nat.ceil_natCast]
  rfl

lemma blockWeight_hbIndex_one (n : ℤ) : blockWeight (hbIndex ((1 : ℕ) : ℝ)) n = 0 := by
  rw [hbIndex_one]
  simp [blockWeight]

/-- Telescoping: `∑_{j ≤ J} w_{2^j} = Λ_{HB,2^J+1}`. -/
theorem sum_range_blockWeight_eq (n : ℤ) (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), blockWeight (Finset.Ioc (2 ^ j / 2) (2 ^ j)) n =
      blockWeight (hbIndex (((2 ^ J + 1 : ℕ)) : ℝ)) n := by
  induction J with
  | zero =>
    rw [Finset.sum_range_one, blockWeight_Ioc_eq_sub]
    have h : (2 ^ 0 / 2 + 1 : ℕ) = 1 := by norm_num
    rw [h, blockWeight_hbIndex_one, sub_zero]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, blockWeight_Ioc_eq_sub]
    have h : (2 ^ (J + 1) / 2 + 1 : ℕ) = 2 ^ J + 1 := by
      rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    rw [h]
    ring

/-- For `T ≥ 1`: `Λ_{≤T} = Λ_{HB,Q'}` with `Q' = 2^J + 1`, `1 ≤ Q' ≤ 2T`. -/
theorem heathBrownModel_eq_blockWeight_hbIndex {T : ℝ} (hT : 1 ≤ T) :
    ∃ Q' : ℝ, 1 ≤ Q' ∧ Q' ≤ 2 * T ∧
      ∀ n : ℤ, heathBrownModel T n = blockWeight (hbIndex Q') n := by
  have hfl : 1 ≤ ⌊T⌋₊ := Nat.le_floor (by exact_mod_cast hT)
  set J : ℕ := Nat.log 2 ⌊T⌋₊ with hJ
  have hS : ∀ j : ℕ, j ∈ Finset.range (J + 1) ↔ (2 : ℝ) ^ j ≤ T := by
    intro j
    rw [Finset.mem_range, Nat.lt_succ_iff, hJ, Nat.le_log_iff_pow_le (by norm_num) (by omega),
      Nat.le_floor_iff (by linarith)]
    push_cast
    rfl
  have hJle : (2 : ℝ) ^ J ≤ T := (hS J).1 (by simp)
  refine ⟨((2 ^ J + 1 : ℕ) : ℝ), ?_, ?_, fun n => ?_⟩
  · have : (1 : ℝ) ≤ (2 : ℝ) ^ J := one_le_pow₀ (by norm_num)
    push_cast
    linarith
  · push_cast
    linarith
  · rw [heathBrownModel_eq_sum_of_mem_iff T (Finset.range (J + 1)) hS n]
    exact sum_range_blockWeight_eq n J

/-! ### KMTT's moment bound for the cumulative approximant -/

/-- KMTT Lemma 4.6, display (4.8), for the cumulative model: for every `m ≥ 1` there is `C_m` with
`E_{n ∈ [N]} |Λ_{≤T}(n)|^m ≤ C_m (1 + log T)^(2^m + m)` for all real `T, N ≥ 1`. -/
theorem moment_heathBrownModel (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T N : ℝ), 1 ≤ T → 1 ≤ N →
      (1 / ((intervalN N).card : ℝ)) * ∑ n ∈ intervalN N, ‖heathBrownModel T n‖ ^ m ≤
        C * (1 + Real.log T) ^ (2 ^ m + m) := by
  obtain ⟨C0, hC0, h0⟩ := moment_blockWeight_hbIndex m hm
  refine ⟨C0 * 2 ^ (2 ^ m + m), by positivity, fun T N hT hN => ?_⟩
  obtain ⟨Q', hQ1, hQ2, hQ⟩ := heathBrownModel_eq_blockWeight_hbIndex hT
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hL := logBracket_le_two_mul_one_add_log hQ1 hT hQ2
  have hL0 : 0 ≤ logBracket Q' := (logBracket_pos _).le
  have hP : logBracket Q' ^ (2 ^ m + m) ≤ (2 * (1 + Real.log T)) ^ (2 ^ m + m) :=
    pow_le_pow_left₀ hL0 hL _
  have h1 := h0 Q' N hQ1 hN
  have e1 : ∑ n ∈ intervalN N, ‖heathBrownModel T n‖ ^ m =
      ∑ n ∈ intervalN N, ‖blockWeight (hbIndex Q') n‖ ^ m :=
    Finset.sum_congr rfl fun n _ => by rw [hQ n]
  rw [e1]
  refine h1.trans ?_
  calc C0 * logBracket Q' ^ (2 ^ m + m) ≤ C0 * (2 * (1 + Real.log T)) ^ (2 ^ m + m) :=
        mul_le_mul_of_nonneg_left hP hC0
    _ = _ := by rw [mul_pow]; ring

/-- The symmetric-window moment of the cumulative model: `∑_{0<|n|≤L} |Λ_{≤T}(n)|^m
≤ 2 L C_m (1 + log T)^(2^m+m)` (evenness doubles the one-sided moment). -/
lemma sum_heathBrownModel_pow_le (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ) (L : ℕ), 1 ≤ T → 1 ≤ L →
      ∑ n ∈ (Finset.Icc (-(L : ℤ)) L).erase 0, ‖heathBrownModel T n‖ ^ m ≤
        2 * L * (C * (1 + Real.log T) ^ (2 ^ m + m)) := by
  obtain ⟨C, hC0, hC⟩ := moment_heathBrownModel m hm
  refine ⟨C, hC0, fun T L hT hL => ?_⟩
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have h1 := sum_le_two_mul_of_even (S := (Finset.Icc (-(L : ℤ)) L).erase 0) (N := (L : ℝ))
    (fun n => ‖heathBrownModel T n‖ ^ m) (fun n => by positivity)
    (fun n => by simp only [heathBrownModel_neg]) (by
      intro n hn
      rw [Finset.mem_erase, Finset.mem_Icc] at hn
      obtain ⟨hn0, hn1, hn2⟩ := hn
      refine ⟨Int.one_le_abs hn0, ?_⟩
      have : |n| ≤ (L : ℤ) := abs_le.2 ⟨hn1, hn2⟩
      have h' : ((|n| : ℤ) : ℝ) ≤ ((L : ℤ) : ℝ) := by exact_mod_cast this
      simpa using h')
  have h2 := hC T (L : ℝ) hT hLR
  rw [card_intervalN hLR, Nat.floor_natCast, one_div, inv_mul_le_iff₀ (by positivity)] at h2
  calc _ ≤ 2 * ∑ n ∈ intervalN (L : ℝ), ‖heathBrownModel T n‖ ^ m := h1
    _ ≤ 2 * ((L : ℝ) * (C * (1 + Real.log T) ^ (2 ^ m + m))) := by gcongr
    _ = _ := by ring

/-! ### The moment of `E_k` -/

lemma one_le_Mk (k : ℕ) : 1 ≤ Mk k := by
  unfold Mk
  refine Real.one_le_exp (Real.rpow_nonneg ?_ _)
  rw [Real.log_pow]
  have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  positivity

lemma log_Mk (k : ℕ) : Real.log (Mk k) = ((k : ℝ) * Real.log 2) ^ ((1 : ℝ) / 10) := by
  rw [Mk, Real.log_exp, Real.log_pow]

/-- `1 + log M_k ≤ 2 k^{1/10}` for `k ≥ 1`. -/
lemma one_add_log_Mk_le {k : ℕ} (hk : 1 ≤ k) :
    1 + Real.log (Mk k) ≤ 2 * (k : ℝ) ^ ((1 : ℝ) / 10) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hl2 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1 : (k : ℝ) * Real.log 2 ≤ k := by nlinarith
  have h2 : ((k : ℝ) * Real.log 2) ^ ((1 : ℝ) / 10) ≤ (k : ℝ) ^ ((1 : ℝ) / 10) :=
    Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have h3 : (1 : ℝ) ≤ (k : ℝ) ^ ((1 : ℝ) / 10) := Real.one_le_rpow hk1 (by norm_num)
  rw [log_Mk]
  linarith

/-- On `0 < |n| ≤ 2^k`: `‖Λ(|n|)‖ ≤ k` (`Λ(n) ≤ log n ≤ k log 2 ≤ k`). -/
lemma norm_vonMangoldt_le {k : ℕ} {n : ℤ} (hn : |n| ≤ ((2 ^ k : ℕ) : ℤ)) :
    ‖((ArithmeticFunction.vonMangoldt n.natAbs : ℝ) : ℂ)‖ ≤ k := by
  rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
  have hna : n.natAbs ≤ 2 ^ k := by
    have h1 : (n.natAbs : ℤ) ≤ ((2 ^ k : ℕ) : ℤ) := by rwa [← Int.abs_eq_natAbs]
    exact_mod_cast h1
  have hpos : (0 : ℝ) < n.natAbs ∨ n.natAbs = 0 := by
    rcases Nat.eq_zero_or_pos n.natAbs with h | h
    · exact Or.inr h
    · exact Or.inl (by exact_mod_cast h)
  rcases hpos with hpos | h0
  · have h1 : Real.log (n.natAbs : ℝ) ≤ Real.log ((2 : ℝ) ^ k) :=
      Real.log_le_log hpos (by exact_mod_cast hna)
    rw [Real.log_pow] at h1
    have hl2 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
    have : (k : ℝ) * Real.log 2 ≤ k := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    linarith
  · rw [h0]
    simp

/-- **The polylogarithmic moment of `E_k`**: for every `m ≥ 1` there is `C` such that for all
`k ≥ 1`, `∑_{0<|n|≤2^k} |E_k(n)|^m ≤ 2 · 2^k · C k^{m + (2^m+m)/10}`
(blueprint N20 (b): `(E |w_{≤M_k}|^m)^{1/m} ≤ C (1 + log M_k)^{(2^m+m)/m}`, `log M_k ≤ k^{1/10}`). -/
theorem sum_E_pow_le (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      ∑ n ∈ (Finset.Icc (-((2 ^ k : ℕ) : ℤ)) ((2 ^ k : ℕ) : ℤ)).erase 0, ‖E k n‖ ^ m ≤
        2 * ((2 ^ k : ℕ) : ℝ) * (C * (k : ℝ) ^ ((m : ℝ) + ((2 : ℝ) ^ m + m) / 10)) := by
  obtain ⟨Cm, hCm0, hCm⟩ := sum_heathBrownModel_pow_le m hm
  set e : ℝ := (m : ℝ) + ((2 : ℝ) ^ m + m) / 10 with he
  refine ⟨2 ^ (m - 1) * (1 + Cm * 2 ^ (2 ^ m + m)), by positivity, fun k hk => ?_⟩
  set L : ℕ := 2 ^ k with hL
  have hL1 : 1 ≤ L := Nat.one_le_two_pow
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL1
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  set S : Finset ℤ := (Finset.Icc (-(L : ℤ)) L).erase 0 with hS
  have hcard : (S.card : ℝ) ≤ 2 * L := by
    have h1 : S.card ≤ (Finset.Icc (-(L : ℤ)) L).card := Finset.card_erase_le
    have h2 : (Finset.Icc (-(L : ℤ)) L).card = 2 * L + 1 := by
      rw [Int.card_Icc]; omega
    have : S.card ≤ 2 * L := by
      have h3 : S.card = (Finset.Icc (-(L : ℤ)) L).card - 1 :=
        Finset.card_erase_of_mem (by simp)
      omega
    exact_mod_cast this
  -- pointwise bound
  have hpt : ∀ n ∈ S, ‖E k n‖ ^ m ≤ 2 ^ (m - 1) *
      ((k : ℝ) ^ m + ‖heathBrownModel (Mk k) n‖ ^ m) := by
    intro n hn
    rw [Finset.mem_erase, Finset.mem_Icc] at hn
    have habs : |n| ≤ (L : ℤ) := abs_le.2 ⟨hn.2.1, hn.2.2⟩
    have h1 : ‖((ArithmeticFunction.vonMangoldt n.natAbs : ℝ) : ℂ)‖ ≤ k := norm_vonMangoldt_le habs
    have h2 := norm_sub_pow_le (a := ((ArithmeticFunction.vonMangoldt n.natAbs : ℝ) : ℂ))
      (b := heathBrownModel (Mk k) n) m
    rw [← E_eq] at h2
    refine h2.trans ?_
    gcongr
  have hsum : ∑ n ∈ S, ‖E k n‖ ^ m ≤
      2 ^ (m - 1) * ((S.card : ℝ) * (k : ℝ) ^ m +
        ∑ n ∈ S, ‖heathBrownModel (Mk k) n‖ ^ m) := by
    calc ∑ n ∈ S, ‖E k n‖ ^ m
        ≤ ∑ n ∈ S, 2 ^ (m - 1) * ((k : ℝ) ^ m + ‖heathBrownModel (Mk k) n‖ ^ m) :=
          Finset.sum_le_sum hpt
      _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
          simp
  have hmom := hCm (Mk k) L (one_le_Mk k) hL1
  have hlog := one_add_log_Mk_le hk
  have hlog0 : 0 ≤ 1 + Real.log (Mk k) := by
    have := Real.log_nonneg (one_le_Mk k)
    linarith
  have hpow : (1 + Real.log (Mk k)) ^ (2 ^ m + m) ≤ 2 ^ (2 ^ m + m) * (k : ℝ) ^ (((2 : ℝ) ^ m + m) / 10) := by
    calc (1 + Real.log (Mk k)) ^ (2 ^ m + m) ≤ (2 * (k : ℝ) ^ ((1 : ℝ) / 10)) ^ (2 ^ m + m) :=
          pow_le_pow_left₀ hlog0 hlog _
      _ = 2 ^ (2 ^ m + m) * ((k : ℝ) ^ ((1 : ℝ) / 10)) ^ (2 ^ m + m) := by rw [mul_pow]
      _ = _ := by
          congr 1
          rw [← Real.rpow_natCast ((k : ℝ) ^ ((1 : ℝ) / 10)) (2 ^ m + m),
            ← Real.rpow_mul hk0.le]
          congr 1
          push_cast
          ring
  have hke : (k : ℝ) ^ (((2 : ℝ) ^ m + m) / 10) ≤ (k : ℝ) ^ e :=
    Real.rpow_le_rpow_of_exponent_le hk1 (by
      rw [he]
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)
  have hkm : (k : ℝ) ^ m ≤ (k : ℝ) ^ e := by
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hk1 ?_
    rw [he]
    have : (0 : ℝ) ≤ ((2 : ℝ) ^ m + m) / 10 := by positivity
    linarith
  have hmain : ∑ n ∈ S, ‖E k n‖ ^ m ≤
      2 * L * (2 ^ (m - 1) * (1 + Cm * 2 ^ (2 ^ m + m)) * (k : ℝ) ^ e) := by
    refine hsum.trans ?_
    have hA : (S.card : ℝ) * (k : ℝ) ^ m ≤ 2 * L * (k : ℝ) ^ e := by
      gcongr
    have hB : ∑ n ∈ S, ‖heathBrownModel (Mk k) n‖ ^ m ≤
        2 * L * (Cm * 2 ^ (2 ^ m + m) * (k : ℝ) ^ e) := by
      refine hmom.trans ?_
      have : Cm * (1 + Real.log (Mk k)) ^ (2 ^ m + m) ≤
          Cm * (2 ^ (2 ^ m + m) * (k : ℝ) ^ e) :=
        mul_le_mul_of_nonneg_left (hpow.trans (by gcongr)) hCm0
      calc 2 * (L : ℝ) * (Cm * (1 + Real.log (Mk k)) ^ (2 ^ m + m))
          ≤ 2 * L * (Cm * (2 ^ (2 ^ m + m) * (k : ℝ) ^ e)) := by gcongr
        _ = _ := by ring
    calc 2 ^ (m - 1) * ((S.card : ℝ) * (k : ℝ) ^ m +
          ∑ n ∈ S, ‖heathBrownModel (Mk k) n‖ ^ m)
        ≤ 2 ^ (m - 1) * (2 * L * (k : ℝ) ^ e + 2 * L * (Cm * 2 ^ (2 ^ m + m) * (k : ℝ) ^ e)) := by
          gcongr
      _ = _ := by ring
  exact hmain

end PrimeBHT.ErrorTerms
