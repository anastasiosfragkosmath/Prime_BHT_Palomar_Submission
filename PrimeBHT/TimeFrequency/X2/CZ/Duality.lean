module

public import PrimeBHT.TimeFrequency.X2.CZ.MikhlinStrong

/-!
# V08 phase 3: duality `L^q(ℝ; L^s(Y))' = L^{q'}(ℝ; L^{s'}(Y))` (norming half)

* `mixedENorm_le_of_dual` (the norming half of (e), **proved**): if `|⟨H, G⟩| ≤ c` for every test function `G`
  (bounded, compactly supported, measurable fibres) of unit `L^{q'}(L^{s'})` norm, then
  `‖H‖_{L^q(L^s)} ≤ c`.  Extremizer `G = N^{q-s} ‖H‖^{1-q} · ‖H‖^{s-2} H`, `N(x) = ‖H(x)‖_{L^s(Y)}`, on
  the truncations `{|x| ≤ M, N ≤ M}`, then Fatou in `M`.
* `mixedNormDuality`: the statement `MixedNormDuality q s` of `MixedNorm.lean`, for all `1 < q, s < ∞`.

The Fubini pairing `⟨K g, G⟩ = ⟨g, K^* G⟩` and the transfer of strong bounds to adjoint kernels are in
`KernelDuality.lean`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology Real ComplexConjugate

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.CZ

open PrimeBHT.Statements

section Extremiser

variable {P : ℕ} [NeZero P]

theorem pairingY_extremiser {s : ℝ} (hs : 1 < s) (Z : ZMod P → ℂ) {a : ℝ} :
    pairingY Z (fun y => (a : ℂ) * extremiser s Z y) = ((a * yNorm s Z ^ s : ℝ) : ℂ) := by
  have hP : (P : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne P
  unfold pairingY
  have e : ∀ y, Z y * conj ((a : ℂ) * extremiser s Z y) = (a : ℂ) * ((‖Z y‖ ^ s : ℝ) : ℂ) := by
    intro y
    rw [map_mul, Complex.conj_ofReal, ← mul_assoc, mul_comm (Z y), mul_assoc, mul_conj_extremiser hs]
  simp_rw [e]
  rw [← Finset.mul_sum]
  have h := yNorm_rpow_self (P := P) (by linarith : s ≠ 0) Z
  push_cast
  rw [← mul_assoc, mul_comm (P : ℂ)⁻¹, mul_assoc]
  congr 1
  have : ((∑ y, ‖Z y‖ ^ s : ℝ) : ℂ) = ∑ y, ((‖Z y‖ ^ s : ℝ) : ℂ) := by push_cast; rfl
  rw [← this]
  have h' : ((yNorm s Z ^ s : ℝ) : ℂ) = ((P : ℝ)⁻¹ : ℂ) * ((∑ y, ‖Z y‖ ^ s : ℝ) : ℂ) := by
    rw [h]; push_cast; rfl
  push_cast at h' ⊢
  rw [h']

theorem yNorm_dual_extremiser {s : ℝ} (hs : 1 < s) (Z : ZMod P → ℂ) {a : ℝ} (ha : 0 ≤ a) :
    yNorm (Real.conjExponent s) (fun y => (a : ℂ) * extremiser s Z y) = a * yNorm s Z ^ (s - 1) := by
  have hs' : 0 < Real.conjExponent s := (Real.HolderConjugate.conjExponent hs).symm.pos
  rw [yNorm_const_mul hs', Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha,
    yNorm_conj_exponent_extremiser hs]

theorem norm_le_rpow_mul_yNorm {s : ℝ} (hs : 0 < s) (Z : ZMod P → ℂ) (y : ZMod P) :
    ‖Z y‖ ≤ (P : ℝ) ^ s⁻¹ * yNorm s Z := by
  have hP : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
  have h1 : ‖Z y‖ ^ s ≤ (P : ℝ) * yNorm s Z ^ s := by
    rw [yNorm_rpow_self hs.ne']
    have : ‖Z y‖ ^ s ≤ ∑ y', ‖Z y'‖ ^ s :=
      Finset.single_le_sum (f := fun y' => ‖Z y'‖ ^ s) (fun y' _ => Real.rpow_nonneg (norm_nonneg _) _)
        (Finset.mem_univ y)
    field_simp
    exact this
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) h1 (inv_nonneg.2 hs.le)
  rw [← Real.rpow_mul (norm_nonneg _), mul_inv_cancel₀ hs.ne', Real.rpow_one,
    Real.mul_rpow hP.le (Real.rpow_nonneg (yNorm_nonneg s Z) _), ← Real.rpow_mul (yNorm_nonneg s Z),
    mul_inv_cancel₀ hs.ne', Real.rpow_one] at h2
  exact h2

end Extremiser

section Norming

variable {P : ℕ} [NeZero P]

/-- The truncation of `H` to `{|x| ≤ M, ‖H(x)‖_{L^s(Y)} ≤ M}`. -/
def truncSet (s : ℝ) (H : ℝ → ZMod P → ℂ) (M : ℕ) (x : ℝ) : Prop :=
  |x| ≤ M ∧ yNorm s (H x) ≤ M

noncomputable def truncH (s : ℝ) (H : ℝ → ZMod P → ℂ) (M : ℕ) : ℝ → ZMod P → ℂ :=
  fun x y => if |x| ≤ M ∧ yNorm s (H x) ≤ M then H x y else 0

theorem yNorm_truncH {s : ℝ} (hs : 0 < s) (H : ℝ → ZMod P → ℂ) (M : ℕ) (x : ℝ) :
    yNorm s (truncH s H M x) = if |x| ≤ M ∧ yNorm s (H x) ≤ M then yNorm s (H x) else 0 := by
  unfold truncH
  by_cases h : |x| ≤ M ∧ yNorm s (H x) ≤ M
  · simp [h]
  · have : (fun y => if |x| ≤ M ∧ yNorm s (H x) ≤ M then H x y else 0) = 0 := by ext y; simp [h]
    rw [this]; simp [h, yNorm_zero' hs]

theorem measurable_truncH {s : ℝ} {H : ℝ → ZMod P → ℂ} (hHm : ∀ y, Measurable fun x => H x y) (M : ℕ)
    (y : ZMod P) : Measurable fun x => truncH s H M x y := by
  have hN : Measurable fun x => yNorm s (H x) := measurable_yNorm s hHm
  have hset : MeasurableSet {x : ℝ | |x| ≤ M ∧ yNorm s (H x) ≤ M} :=
    (measurableSet_le continuous_abs.measurable measurable_const).inter
      (measurableSet_le hN measurable_const)
  exact Measurable.ite hset (hHm y) measurable_const

omit [NeZero P] in
theorem extremiser_zero {s : ℝ} (y : ZMod P) : extremiser s (0 : ZMod P → ℂ) y = 0 := by
  simp [extremiser]

/-- One truncation of the norming statement. -/
theorem mixedENorm_truncH_le {q s : ℝ} (hq : 1 < q) (hs : 1 < s) {H : ℝ → ZMod P → ℂ}
    (hHm : ∀ y, Measurable fun x => H x y) {c : ℝ≥0∞}
    (h : ∀ G : ℝ → ZMod P → ℂ, IsTestFun G →
      mixedENorm (Real.conjExponent q) (Real.conjExponent s) G ≤ 1 →
      ENNReal.ofReal ‖mixedPairing H G‖ ≤ c) (M : ℕ) :
    mixedENorm q s (truncH s H M) ≤ c := by
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < s := by linarith
  have hq' := Real.HolderConjugate.conjExponent hq
  have hs' := Real.HolderConjugate.conjExponent hs
  set q' := Real.conjExponent q with hq'def
  set s' := Real.conjExponent s with hs'def
  have hq'0 : 0 < q' := hq'.symm.pos
  have hs'0 : 0 < s' := hs'.symm.pos
  have hqq' : (q - 1) * q' = q := by rw [hq'def, Real.conjExponent]; field_simp
  set HM := truncH s H M with hHM
  have hHMm : ∀ y, Measurable fun x => HM x y := measurable_truncH hHm M
  have hNm : Measurable fun x => yNorm s (HM x) := measurable_yNorm s hHMm
  set N : ℝ → ℝ := fun x => yNorm s (HM x) with hN
  have hN0 : ∀ x, 0 ≤ N x := fun x => yNorm_nonneg s _
  have hNM : ∀ x, N x ≤ (M : ℝ) := by
    intro x; simp only [hN, hHM]; rw [yNorm_truncH hs0]
    by_cases hh : |x| ≤ M ∧ yNorm s (H x) ≤ M
    · simp [hh]
    · simp [hh]
  have hNsupp : ∀ x, (M : ℝ) < |x| → N x = 0 := by
    intro x hx; simp only [hN, hHM]; rw [yNorm_truncH hs0]
    have : ¬ (|x| ≤ M ∧ yNorm s (H x) ≤ M) := fun hh => absurd hh.1 (not_le.2 hx)
    simp [this]
  have hHM0 : ∀ x, N x = 0 → HM x = 0 := by
    intro x hx
    have : yNorm s (HM x) = 0 := hx
    -- `yNorm s v = 0` forces `v = 0`
    ext y
    have h1 := norm_le_rpow_mul_yNorm hs0 (HM x) y
    rw [this, mul_zero] at h1
    simpa using h1
  set J : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (N x) ^ q with hJ
  have hAE : ∀ y, AEStronglyMeasurable (fun x => HM x y) volume := fun y => (hHMm y).aestronglyMeasurable
  have hmJ : mixedENorm q s HM ^ q = J := mixedENorm_rpow hq0 s hAE
  have hJfin : J < ⊤ := by
    calc J ≤ ∫⁻ x, (Icc (-(M : ℝ)) M).indicator (fun _ => ENNReal.ofReal (M : ℝ) ^ q) x := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ Icc (-(M : ℝ)) M
          · rw [indicator_of_mem hx]
            exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hNM x)) hq0.le
          · rw [indicator_of_notMem hx]
            have : (M : ℝ) < |x| := by
              simp only [mem_Icc, not_and_or, not_le] at hx
              rcases hx with h1 | h1
              · rw [abs_of_neg (by have : (0 : ℝ) ≤ M := Nat.cast_nonneg M; linarith)]; linarith
              · rw [abs_of_pos (by have : (0 : ℝ) ≤ M := Nat.cast_nonneg M; linarith)]; exact h1
            rw [hNsupp x this]; simp [ENNReal.zero_rpow_of_pos hq0]
      _ = ENNReal.ofReal (M : ℝ) ^ q * volume (Icc (-(M : ℝ)) M) := by
          rw [lintegral_indicator measurableSet_Icc, setLIntegral_const]
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq0.le ENNReal.ofReal_ne_top)
          measure_Icc_lt_top
  have hmfin : mixedENorm q s HM ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.top_rpow_of_pos hq0] at hmJ
    exact absurd hmJ.symm hJfin.ne
  by_cases hJ0 : J = 0
  · have : mixedENorm q s HM = 0 := by
      rw [hJ0] at hmJ
      rcases (ENNReal.rpow_eq_zero_iff.1 hmJ) with h1 | h1
      · exact h1.1
      · exact absurd h1.2 (not_lt.2 hq0.le)
    rw [this]; exact zero_le
  set Jr : ℝ := (mixedENorm q s HM).toReal with hJrdef
  have hJr0 : 0 < Jr := by
    refine ENNReal.toReal_pos ?_ hmfin
    intro h0; apply hJ0; rw [← hmJ, h0, ENNReal.zero_rpow_of_pos hq0]
  have hmJr : mixedENorm q s HM = ENNReal.ofReal Jr := (ENNReal.ofReal_toReal hmfin).symm
  have hJJr : J = ENNReal.ofReal (Jr ^ q) := by
    rw [← hmJ, hmJr, ENNReal.ofReal_rpow_of_nonneg hJr0.le hq0.le]
  -- the extremiser
  set a : ℝ → ℝ := fun x => N x ^ (q - s) * Jr ^ (1 - q) with ha
  have ha0 : ∀ x, 0 ≤ a x := fun x => mul_nonneg (Real.rpow_nonneg (hN0 x) _) (Real.rpow_nonneg hJr0.le _)
  set G : ℝ → ZMod P → ℂ := fun x y => (a x : ℂ) * extremiser s (HM x) y with hG
  have hNx : ∀ x, yNorm s (HM x) = N x := fun x => rfl
  have hG1 : ∀ x, pairingY (HM x) (G x) = ((N x ^ q * Jr ^ (1 - q) : ℝ) : ℂ) := by
    intro x
    have := pairingY_extremiser (P := P) hs (HM x) (a := a x)
    simp only [hG]
    rw [this, hNx x]
    congr 1
    rcases (hN0 x).eq_or_lt with h0 | hpos
    · rw [← h0]
      simp [Real.zero_rpow hs0.ne', Real.zero_rpow hq0.ne']
    · simp only [ha]
      rw [mul_assoc, mul_comm (Jr ^ (1 - q)), ← mul_assoc, ← Real.rpow_add hpos]
      congr 3; ring
  have hG2 : ∀ x, yNorm s' (G x) = N x ^ (q - 1) * Jr ^ (1 - q) := by
    intro x
    have := yNorm_dual_extremiser (P := P) hs (HM x) (ha0 x)
    simp only [hG]
    rw [this, hNx x]
    rcases (hN0 x).eq_or_lt with h0 | hpos
    · rw [← h0]
      simp [ha, Real.zero_rpow (by linarith : q - 1 ≠ 0), Real.zero_rpow (by linarith : s - 1 ≠ 0)]
    · simp only [ha]
      rw [mul_right_comm, ← Real.rpow_add hpos]
      congr 2; ring
  -- `G` is a test function
  have hGm : ∀ y, Measurable fun x => G x y := by
    intro y
    have hext : Measurable fun x => extremiser s (HM x) y := by
      unfold extremiser
      exact (Complex.measurable_ofReal.comp ((hHMm y).norm.pow_const _)).mul (hHMm y)
    have hax : Measurable a := by
      simp only [ha]
      exact ((hNm.pow_const _).mul measurable_const)
    exact (Complex.measurable_ofReal.comp hax).mul hext
  have hGb : ∃ C : ℝ, ∀ x y, ‖G x y‖ ≤ C := by
    have hP : (0 : ℝ) < P := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne P))
    refine ⟨(((P : ℝ) ^ s⁻¹) ^ (s - 1)) * ((M : ℝ) ^ (q - 1) * Jr ^ (1 - q)), fun x y => ?_⟩
    have hCb : 0 ≤ (((P : ℝ) ^ s⁻¹) ^ (s - 1)) * ((M : ℝ) ^ (q - 1) * Jr ^ (1 - q)) := by positivity
    rcases (hN0 x).eq_or_lt with h0 | hpos
    · have : HM x = 0 := hHM0 x h0.symm
      have hG0 : G x y = 0 := by simp only [hG, this, extremiser_zero, mul_zero]
      rw [hG0, norm_zero]; exact hCb
    · simp only [hG]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 x), norm_extremiser hs]
      have h1 : ‖HM x y‖ ^ (s - 1) ≤ (((P : ℝ) ^ s⁻¹) ^ (s - 1)) * N x ^ (s - 1) := by
        rw [← Real.mul_rpow (Real.rpow_nonneg hP.le _) (hN0 x)]
        exact Real.rpow_le_rpow (norm_nonneg _) (norm_le_rpow_mul_yNorm hs0 (HM x) y) (by linarith)
      have h2 : N x ^ (q - 1) ≤ (M : ℝ) ^ (q - 1) :=
        Real.rpow_le_rpow (hN0 x) (hNM x) (by linarith)
      simp only [ha]
      calc N x ^ (q - s) * Jr ^ (1 - q) * ‖HM x y‖ ^ (s - 1)
          ≤ N x ^ (q - s) * Jr ^ (1 - q) * ((((P : ℝ) ^ s⁻¹) ^ (s - 1)) * N x ^ (s - 1)) :=
            mul_le_mul_of_nonneg_left h1 (mul_nonneg (Real.rpow_nonneg (hN0 x) _) (Real.rpow_nonneg hJr0.le _))
        _ = (((P : ℝ) ^ s⁻¹) ^ (s - 1)) * (N x ^ (q - 1) * Jr ^ (1 - q)) := by
            have : N x ^ (q - s) * N x ^ (s - 1) = N x ^ (q - 1) := by
              rw [← Real.rpow_add hpos]; congr 1; ring
            calc N x ^ (q - s) * Jr ^ (1 - q) * ((((P : ℝ) ^ s⁻¹) ^ (s - 1)) * N x ^ (s - 1))
                = (((P : ℝ) ^ s⁻¹) ^ (s - 1)) * (N x ^ (q - s) * N x ^ (s - 1)) * Jr ^ (1 - q) := by ring
              _ = _ := by rw [this]; ring
        _ ≤ (((P : ℝ) ^ s⁻¹) ^ (s - 1)) * ((M : ℝ) ^ (q - 1) * Jr ^ (1 - q)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hJr0.le _)
  have hGs : ∃ R : ℝ, ∀ x, R < |x| → ∀ y, G x y = 0 := by
    refine ⟨M, fun x hx y => ?_⟩
    have h0 : HM x = 0 := hHM0 x (hNsupp x hx)
    simp only [hG, h0, extremiser_zero, mul_zero]
  have hGtest : IsTestFun G := ⟨hGm, hGb, hGs⟩
  have hGAE : ∀ y, AEStronglyMeasurable (fun x => G x y) volume := fun y => (hGm y).aestronglyMeasurable
  -- the dual norm is `1`
  have hGnorm : mixedENorm q' s' G ≤ 1 := by
    have h1 := mixedENorm_rpow hq'0 s' hGAE
    have h2 : ∀ x, ENNReal.ofReal (yNorm s' (G x)) ^ q' =
        ENNReal.ofReal (Jr ^ (-q)) * ENNReal.ofReal (N x) ^ q := by
      intro x
      rw [hG2 x, ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Real.rpow_nonneg (hN0 x) _)
        (Real.rpow_nonneg hJr0.le _)) hq'0.le, ENNReal.ofReal_rpow_of_nonneg (hN0 x) hq0.le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hJr0.le _)]
      congr 1
      rw [Real.mul_rpow (Real.rpow_nonneg (hN0 x) _) (Real.rpow_nonneg hJr0.le _),
        ← Real.rpow_mul (hN0 x), ← Real.rpow_mul hJr0.le, hqq']
      have : (1 - q) * q' = -q := by
        have : q' = q / (q - 1) := by rw [hq'def, Real.conjExponent]
        rw [this]; field_simp; ring
      rw [this]; ring
    simp_rw [h2] at h1
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hJ, hJJr, ← ENNReal.ofReal_mul (Real.rpow_nonneg hJr0.le _),
      ← Real.rpow_add hJr0] at h1
    have h3 : mixedENorm q' s' G ^ q' = 1 := by
      rw [h1]; simp
    exact (ENNReal.rpow_le_rpow_iff hq'0).1 (h3.le.trans (by simp))
  -- the pairings
  have hpair_eq : mixedPairing H G = mixedPairing HM G := by
    unfold mixedPairing
    congr 1; ext x
    by_cases hx : |x| ≤ M ∧ yNorm s (H x) ≤ M
    · have : HM x = H x := by ext y; simp [hHM, truncH, hx]
      rw [this]
    · have h0 : HM x = 0 := by ext y; simp [hHM, truncH, hx]
      have hG0 : G x = 0 := by ext y; simp only [hG, h0, extremiser_zero, mul_zero]; rfl
      simp [pairingY, hG0]
  have hmp : mixedPairing HM G = ((Jr : ℝ) : ℂ) := by
    unfold mixedPairing
    simp_rw [hG1]
    rw [integral_complex_ofReal]
    congr 1
    rw [integral_mul_const]
    have hint : ∫ x, N x ^ q = Jr ^ q := by
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => Real.rpow_nonneg (hN0 x) _)
        (hNm.pow_const q).aestronglyMeasurable]
      have : ∀ x, ENNReal.ofReal (N x ^ q) = ENNReal.ofReal (N x) ^ q := fun x =>
        (ENNReal.ofReal_rpow_of_nonneg (hN0 x) hq0.le).symm
      simp_rw [this]
      rw [← hJ, hJJr, ENNReal.toReal_ofReal (Real.rpow_nonneg hJr0.le _)]
    rw [hint, ← Real.rpow_add hJr0]; simp
  have hfin := h G hGtest hGnorm
  rw [hpair_eq, hmp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hJr0] at hfin
  rw [hmJr]; exact hfin


/-- **Duality, norming half**: the mixed norm is bounded by the supremum of the pairings against test
functions of unit dual norm. -/
theorem mixedENorm_le_of_dual {q s : ℝ} (hq : 1 < q) (hs : 1 < s) {H : ℝ → ZMod P → ℂ}
    (hHm : ∀ y, Measurable fun x => H x y) {c : ℝ≥0∞}
    (h : ∀ G : ℝ → ZMod P → ℂ, IsTestFun G →
      mixedENorm (Real.conjExponent q) (Real.conjExponent s) G ≤ 1 →
      ENNReal.ofReal ‖mixedPairing H G‖ ≤ c) :
    mixedENorm q s H ≤ c := by
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < s := by linarith
  have hAE : ∀ y, AEStronglyMeasurable (fun x => H x y) volume := fun y => (hHm y).aestronglyMeasurable
  have hNm : Measurable fun x => yNorm s (H x) := measurable_yNorm s hHm
  have key : ∀ M : ℕ, ∫⁻ x, ENNReal.ofReal (yNorm s (truncH s H M x)) ^ q ≤ c ^ q := by
    intro M
    have h1 := mixedENorm_truncH_le hq hs hHm h M
    have h2 := mixedENorm_rpow hq0 s (F := truncH s H M)
      (fun y => (measurable_truncH (s := s) hHm M y).aestronglyMeasurable)
    rw [← h2]
    exact ENNReal.rpow_le_rpow h1 hq0.le
  have hfat := lintegral_le_of_tendsto_of_le
    (f := fun M x => ENNReal.ofReal (yNorm s (truncH s H M x)) ^ q)
    (g := fun x => ENNReal.ofReal (yNorm s (H x)) ^ q) (c := c ^ q)
    (fun M => by
      have : Measurable fun x => yNorm s (truncH s H M x) := measurable_yNorm s (measurable_truncH (s := s) hHm M)
      exact this.ennreal_ofReal.pow_const q)
    (fun x => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (max ⌈|x|⌉₊ ⌈yNorm s (H x)⌉₊)] with M hM
      have h1 : |x| ≤ M := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_left _ _).trans hM)
      have h2 : yNorm s (H x) ≤ M :=
        (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hM)
      rw [yNorm_truncH hs0]; simp [h1, h2])
    key
  rw [← mixedENorm_rpow hq0 s hAE] at hfat
  exact (ENNReal.rpow_le_rpow_iff hq0).1 hfat

end Norming

end PrimeBHT.TimeFrequency.X2.CZ
