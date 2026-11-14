module

public import PrimeBHT.Frozen.IsAdapted
public import PrimeBHT.Frozen.Pairing
public import PrimeBHT.Frozen.TriIdx
public import PrimeBHT.Frozen.TimeInt
public import PrimeBHT.Frozen.FreqInt
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Packet inner products: (G1), (G2), (G3) of blueprint node C2 (`TT.gram`)

For packets adapted in the sense of the frozen `PrimeBHT.Statements.IsAdapted`:

* (G1) `norm_pairing_le_of_isAdapted`: `|⟨φ, ψ⟩| ≤ C_N |I|^{-1/2} |I'|^{1/2} (1 + |c(I) - c(I')|/|I|)^{-(N-1)}`
  for `0 < |I'| ≤ |I|`, `N ≥ 2`, `C_N = gramConst N = 3 · 2^N / (N - 1)` (only the `n = 0` bound is used;
  the integral is split at `|x - c(I)| = |c(I) - c(I')|/2`, the tail integral gives exactly `N - 1`);
* (G2) `pairing_eq_zero_of_disjoint`: `⟨φ, ψ⟩ = 0` if the frequency sets are disjoint (`ω'` bounded),
  and the general `pairing_eq_zero_of_fourier_Icc` (Fourier supports in closed intervals whose half-open
  versions are disjoint);
* (G3) `sum_norm_pairing_sameScale_le`: for tri-tile packets of one class `Idx_{s',α}`,
  `Σ_{t' ∈ P, s(t') = s(t)} |⟨φ_{t,k}, φ_{t',k}⟩| ≤ sameScaleConst N` (`N ≥ 3`), from
  `disjoint_freqInt_of_ne` (same scale, distinct congruent `ℓ`: disjoint cells; proved here, no grid
  hypothesis needed) and `norm_pairing_le_sameScale` (`≤ C_N (1 + |j|)^{-(N-1)}`, `I_{t'} = I_t + j|I_t|`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform

namespace PrimeBHT.TimeFrequency.Tile

open PrimeBHT.Statements

/-! ### Weight integrals -/

/-- The tail integral `∫_{t > r} (1 + t)^{-p} dt = (1 + r)^{1-p}/(p-1)`. -/
theorem integral_Ioi_one_add_rpow_neg {p : ℝ} (hp : 1 < p) {r : ℝ} (hr : 0 ≤ r) :
    ∫ t in Ioi r, (1 + t) ^ (-p) = (1 + r) ^ (1 - p) / (p - 1) := by
  have hp1 : p - 1 ≠ 0 := by linarith
  have hderiv : ∀ x ∈ Ici r, HasDerivAt (fun t : ℝ => -((1 + t) ^ (1 - p) / (p - 1)))
      ((1 + x) ^ (-p)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < 1 + x := by have : r ≤ x := hx; linarith
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 x := (hasDerivAt_id x).const_add 1
    have h2 := (h1.rpow_const (p := 1 - p) (Or.inl hx0.ne')).div_const (p - 1) |>.neg
    convert h2 using 1
    have : (1 - p - 1) = -p := by ring
    rw [this]
    field_simp
    ring
  have hint : IntegrableOn (fun t : ℝ => (1 + t) ^ (-p)) (Ioi r) := by
    have h := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := p)
      (by simpa using hp)).integrableOn (s := Ioi r)
    refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have : 0 ≤ t := le_trans hr (le_of_lt ht)
    simp [Real.norm_eq_abs, abs_of_nonneg this]
  have hlim : Tendsto (fun t : ℝ => -((1 + t) ^ (1 - p) / (p - 1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => 1 + t) atTop atTop := tendsto_atTop_add_const_left _ 1 tendsto_id
    have h2 := (tendsto_rpow_neg_atTop (y := p - 1) (by linarith)).comp h1
    have h3 := (h2.div_const (p - 1)).neg
    simp only [zero_div, neg_zero] at h3
    refine h3.congr (fun t => ?_)
    simp only [Function.comp_apply, neg_sub]
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  ring

/-- Change of variables `x ↦ |x - c| / L` for an even weight. -/
theorem integral_comp_abs_sub_div {f : ℝ → ℝ} (c : ℝ) {L : ℝ} (hL : 0 < L) :
    ∫ x, f (|x - c| / L) = 2 * L * ∫ t in Ioi (0 : ℝ), f t := by
  have h1 : (fun x : ℝ => f (|x - c| / L)) = fun x => (fun y : ℝ => f (|y / L|)) (x - c) := by
    funext x
    show f _ = f |(x - c) / L|
    rw [abs_div, abs_of_pos hL]
  rw [h1, integral_sub_right_eq_self (fun y : ℝ => f (|y / L|)) c,
    Measure.integral_comp_div (fun y : ℝ => f |y|) L, integral_comp_abs, abs_of_pos hL,
    smul_eq_mul]
  ring

/-- `∫ (1 + |x - c|/L)^{-p} dx = 2L/(p-1)`. -/
theorem integral_one_add_abs_sub_div_rpow {p : ℝ} (hp : 1 < p) (c : ℝ) {L : ℝ} (hL : 0 < L) :
    ∫ x, (1 + |x - c| / L) ^ (-p) = 2 * L / (p - 1) := by
  rw [integral_comp_abs_sub_div (f := fun t => (1 + t) ^ (-p)) c hL,
    integral_Ioi_one_add_rpow_neg hp le_rfl]
  simp only [add_zero, Real.one_rpow]
  ring

/-- The tail `∫_{|x - c| > r} (1 + |x - c|/L)^{-p} dx = 2L(1 + r/L)^{1-p}/(p-1)`. -/
theorem integral_indicator_one_add_abs_sub_div_rpow {p : ℝ} (hp : 1 < p) (c : ℝ) {L : ℝ}
    (hL : 0 < L) {r : ℝ} (hr : 0 ≤ r) :
    ∫ x, {x : ℝ | r < |x - c|}.indicator (fun x => (1 + |x - c| / L) ^ (-p)) x =
      2 * L * ((1 + r / L) ^ (1 - p) / (p - 1)) := by
  have h1 : (fun x : ℝ => {x : ℝ | r < |x - c|}.indicator (fun x => (1 + |x - c| / L) ^ (-p)) x) =
      fun x => (Ioi (r / L)).indicator (fun t => (1 + t) ^ (-p)) (|x - c| / L) := by
    funext x
    by_cases hx : r < |x - c|
    · have : r / L < |x - c| / L := div_lt_div_of_pos_right hx hL
      simp [Set.indicator, hx, this]
    · have : ¬ r / L < |x - c| / L := fun h => hx ((div_lt_div_iff_of_pos_right hL).1 h)
      simp [Set.indicator, hx, this]
  rw [h1, integral_comp_abs_sub_div (f := (Ioi (r / L)).indicator (fun t => (1 + t) ^ (-p))) c hL,
    setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi,
    max_eq_right (div_nonneg hr hL.le), integral_Ioi_one_add_rpow_neg hp (div_nonneg hr hL.le)]

theorem integrable_one_add_abs_sub_div_rpow {p : ℝ} (hp : 1 < p) (c : ℝ) {L : ℝ} (hL : 0 < L) :
    Integrable (fun x : ℝ => (1 + |x - c| / L) ^ (-p)) := by
  have h := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := p) (by simpa using hp))
  have h2 := (h.comp_div hL.ne').comp_sub_right c
  refine h2.congr (ae_of_all _ fun x => ?_)
  simp [Real.norm_eq_abs, abs_of_pos hL]

/-! ### Basic consequences of adaptedness -/

theorem norm_cexp_neg_two_pi_I_mul (c y : ℝ) :
    ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (c : ℂ) * (y : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- The pointwise bound (`n = 0`): `|φ(x)| ≤ |I|^{-1/2} (1 + |x - c(I)|/|I|)^{-N}`. -/
theorem IsAdapted.norm_le {N : ℕ} {I ω : Set ℝ} {φ : ℝ → ℂ} (hφ : IsAdapted N I ω φ) (x : ℝ) :
    ‖φ x‖ ≤ (volume I).toReal ^ (-(1 / 2 : ℝ)) *
      (1 + |x - intervalCentre I| / (volume I).toReal) ^ (-(N : ℝ)) := by
  have h := hφ.2.2.2 0 (Nat.zero_le _) x
  rw [iteratedDeriv_zero, norm_mul, norm_cexp_neg_two_pi_I_mul, one_mul] at h
  convert h using 3
  simp

theorem IsAdapted.continuous {N : ℕ} {I ω : Set ℝ} {φ : ℝ → ℂ} (hφ : IsAdapted N I ω φ) :
    Continuous φ :=
  hφ.1.continuous

theorem IsAdapted.integrable {N : ℕ} {I ω : Set ℝ} {φ : ℝ → ℂ} (hφ : IsAdapted N I ω φ) :
    Integrable φ :=
  hφ.2.1

/-! ### (G1) the pair estimate -/

/-- The constant of (G1): `3 · 2^N / (N - 1)`. -/
noncomputable def gramConst (N : ℕ) : ℝ := 3 * 2 ^ N / ((N : ℝ) - 1)

theorem gramConst_nonneg {N : ℕ} (hN : 2 ≤ N) : 0 ≤ gramConst N := by
  have : (2 : ℝ) ≤ N := by exact_mod_cast hN
  unfold gramConst
  apply div_nonneg (by positivity)
  linarith

/-- Pointwise splitting used for (G1). -/
theorem rpow_mul_rpow_le_split {N : ℕ} {L L' c c' : ℝ} (hL : 0 < L) (hL' : 0 < L') (x : ℝ) :
    (1 + |x - c| / L) ^ (-(N : ℝ)) * (1 + |x - c'| / L') ^ (-(N : ℝ)) ≤
      2 ^ N * (1 + |c - c'| / L) ^ (-((N : ℝ) - 1)) * (1 + |x - c'| / L') ^ (-(N : ℝ)) +
      {x : ℝ | |c - c'| / 2 < |x - c'|}.indicator
        (fun x => (1 + |x - c'| / L') ^ (-(N : ℝ))) x := by
  set u := |c - c'|
  set D := 1 + u / L
  have hu : 0 ≤ u := abs_nonneg _
  have hD1 : 1 ≤ D := by have : 0 ≤ u / L := div_nonneg hu hL.le; linarith
  have hB : 0 ≤ (1 + |x - c'| / L') ^ (-(N : ℝ)) := by positivity
  have hind : 0 ≤ {x : ℝ | u / 2 < |x - c'|}.indicator
      (fun x => (1 + |x - c'| / L') ^ (-(N : ℝ))) x :=
    Set.indicator_nonneg (fun _ _ => by positivity) _
  have hA1 : 1 ≤ 1 + |x - c| / L := by
    have : 0 ≤ |x - c| / L := div_nonneg (abs_nonneg _) hL.le
    linarith
  by_cases h : u / 2 ≤ |x - c|
  · have hDA : D / 2 ≤ 1 + |x - c| / L := by
      have : u / 2 / L ≤ |x - c| / L := div_le_div_of_nonneg_right h hL.le
      have : D / 2 = 1 / 2 + u / 2 / L := by simp only [D]; ring
      rw [this]
      linarith
    have hA : (1 + |x - c| / L) ^ (-(N : ℝ)) ≤ 2 ^ N * D ^ (-((N : ℝ) - 1)) := by
      calc (1 + |x - c| / L) ^ (-(N : ℝ)) ≤ (D / 2) ^ (-(N : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by linarith) hDA (by simp)
        _ = 2 ^ N * D ^ (-(N : ℝ)) := by
            rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
              Real.rpow_natCast]
            field_simp
        _ ≤ 2 ^ N * D ^ (-((N : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hD1 (by linarith))
              (by positivity)
    calc _ ≤ 2 ^ N * D ^ (-((N : ℝ) - 1)) * (1 + |x - c'| / L') ^ (-(N : ℝ)) :=
          mul_le_mul_of_nonneg_right hA hB
      _ ≤ _ := le_add_of_nonneg_right hind
  · push Not at h
    have hx' : u / 2 < |x - c'| := by
      have : u ≤ |x - c| + |x - c'| := by
        calc u = |(x - c') - (x - c)| := by simp only [u]; congr 1; ring
          _ ≤ |x - c'| + |x - c| := abs_sub _ _
          _ = _ := add_comm _ _
      linarith
    have hA : (1 + |x - c| / L) ^ (-(N : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hA1 (by simp)
    have hi : {x : ℝ | u / 2 < |x - c'|}.indicator
        (fun x => (1 + |x - c'| / L') ^ (-(N : ℝ))) x = (1 + |x - c'| / L') ^ (-(N : ℝ)) :=
      Set.indicator_of_mem (s := {x : ℝ | u / 2 < |x - c'|}) hx' _
    rw [hi]
    have h0 : 0 ≤ 2 ^ N * D ^ (-((N : ℝ) - 1)) * (1 + |x - c'| / L') ^ (-(N : ℝ)) := by
      positivity
    nlinarith

/-- **(G1)** `|⟨φ, ψ⟩| ≤ C_N |I|^{-1/2} |I'|^{1/2} (1 + |c(I) - c(I')|/|I|)^{-(N-1)}` for adapted
`φ` (to `(I, ω)`) and `ψ` (to `(I', ω')`) with `0 < |I'| ≤ |I|` (BD26 L1216). The modulations cancel in
absolute values, so only the `n = 0` bound of `IsAdapted` is used. -/
theorem norm_pairing_le_of_isAdapted {N : ℕ} (hN : 2 ≤ N) {I I' ω ω' : Set ℝ} {φ ψ : ℝ → ℂ}
    (hφ : IsAdapted N I ω φ) (hψ : IsAdapted N I' ω' ψ) (hI' : 0 < (volume I').toReal)
    (hle : (volume I').toReal ≤ (volume I).toReal) :
    ‖pairing φ ψ‖ ≤ gramConst N * (volume I).toReal ^ (-(1 / 2 : ℝ)) *
      (volume I').toReal ^ (1 / 2 : ℝ) *
      (1 + |intervalCentre I - intervalCentre I'| / (volume I).toReal) ^ (-((N : ℝ) - 1)) := by
  set L := (volume I).toReal
  set L' := (volume I').toReal
  set c := intervalCentre I
  set c' := intervalCentre I'
  have hL : 0 < L := lt_of_lt_of_le hI' hle
  set u := |c - c'|
  set D := 1 + u / L
  have hN1 : (1 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hu : 0 ≤ u := abs_nonneg _
  set K := L ^ (-(1 / 2 : ℝ)) * L' ^ (-(1 / 2 : ℝ))
  have hK : 0 ≤ K := by positivity
  set B : ℝ → ℝ := fun x => (1 + |x - c'| / L') ^ (-(N : ℝ))
  set S : Set ℝ := {x : ℝ | u / 2 < |x - c'|}
  have hBint : Integrable B := integrable_one_add_abs_sub_div_rpow hN1 c' hI'
  have hS : MeasurableSet S := measurableSet_lt measurable_const (by fun_prop)
  have hIint : Integrable (S.indicator B) := hBint.indicator hS
  have hpt : ∀ x, ‖φ x * (starRingEnd ℂ) (ψ x)‖ ≤
      K * (2 ^ N * D ^ (-((N : ℝ) - 1)) * B x + S.indicator B x) := by
    intro x
    rw [norm_mul, Complex.norm_conj]
    calc ‖φ x‖ * ‖ψ x‖ ≤ (L ^ (-(1 / 2 : ℝ)) * (1 + |x - c| / L) ^ (-(N : ℝ))) *
          (L' ^ (-(1 / 2 : ℝ)) * B x) :=
          mul_le_mul (IsAdapted.norm_le hφ x) (IsAdapted.norm_le hψ x) (norm_nonneg _) (by positivity)
      _ = K * ((1 + |x - c| / L) ^ (-(N : ℝ)) * B x) := by simp only [K]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (rpow_mul_rpow_le_split hL hI' x) hK
  have hmaj : Integrable (fun x => K * (2 ^ N * D ^ (-((N : ℝ) - 1)) * B x + S.indicator B x)) :=
    ((hBint.const_mul _).add hIint).const_mul K
  have h1 : ‖pairing φ ψ‖ ≤ ∫ x, K * (2 ^ N * D ^ (-((N : ℝ) - 1)) * B x + S.indicator B x) := by
    unfold pairing
    refine (norm_integral_le_integral_norm _).trans ?_
    exact integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hmaj (ae_of_all _ hpt)
  have hBval : ∫ x, B x = 2 * L' / ((N : ℝ) - 1) :=
    integral_one_add_abs_sub_div_rpow hN1 c' hI'
  have hSval : ∫ x, S.indicator B x = 2 * L' * ((1 + u / 2 / L') ^ (1 - (N : ℝ)) / ((N : ℝ) - 1)) :=
    integral_indicator_one_add_abs_sub_div_rpow hN1 c' hI' (by positivity)
  have h2 : ∫ x, K * (2 ^ N * D ^ (-((N : ℝ) - 1)) * B x + S.indicator B x) =
      K * (2 ^ N * D ^ (-((N : ℝ) - 1)) * (2 * L' / ((N : ℝ) - 1)) +
        2 * L' * ((1 + u / 2 / L') ^ (1 - (N : ℝ)) / ((N : ℝ) - 1))) := by
    rw [integral_const_mul, integral_add (hBint.const_mul _) hIint, integral_const_mul, hBval,
      hSval]
  -- the tail term
  have htail : (1 + u / 2 / L') ^ (1 - (N : ℝ)) ≤ 2 ^ (N - 1) * D ^ (-((N : ℝ) - 1)) := by
    have hDA : D / 2 ≤ 1 + u / 2 / L' := by
      have : u / 2 / L ≤ u / 2 / L' := div_le_div_of_nonneg_left (by positivity) hI' hle
      have : D / 2 = 1 / 2 + u / 2 / L := by simp only [D]; ring
      rw [this]
      linarith
    have hD0 : 0 < D / 2 := by have : 0 ≤ u / L := div_nonneg hu hL.le; simp only [D]; linarith
    calc (1 + u / 2 / L') ^ (1 - (N : ℝ)) ≤ (D / 2) ^ (1 - (N : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hD0 hDA (by linarith)
      _ = 2 ^ (N - 1) * D ^ (-((N : ℝ) - 1)) := by
          have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega)]
            simp
          rw [Real.div_rpow (by linarith) (by norm_num), show (1 - (N : ℝ)) = -((N : ℝ) - 1) by ring,
            Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), ← hcast, Real.rpow_natCast]
          field_simp
  have hL'half : L' ^ (-(1 / 2 : ℝ)) * L' = L' ^ (1 / 2 : ℝ) := by
    have h := Real.rpow_add hI' (-(1 / 2 : ℝ)) 1
    rw [Real.rpow_one] at h
    rw [← h]
    norm_num
  have hpow : (2 : ℝ) ^ N = 2 * 2 ^ (N - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hNpos : 0 < (N : ℝ) - 1 := by linarith
  rw [h2] at h1
  refine h1.trans ?_
  have hE : 0 ≤ D ^ (-((N : ℝ) - 1)) := by positivity
  calc K * (2 ^ N * D ^ (-((N : ℝ) - 1)) * (2 * L' / ((N : ℝ) - 1)) +
        2 * L' * ((1 + u / 2 / L') ^ (1 - (N : ℝ)) / ((N : ℝ) - 1)))
      ≤ K * (2 ^ N * D ^ (-((N : ℝ) - 1)) * (2 * L' / ((N : ℝ) - 1)) +
        2 * L' * (2 ^ (N - 1) * D ^ (-((N : ℝ) - 1)) / ((N : ℝ) - 1))) := by
        gcongr
    _ = gramConst N * L ^ (-(1 / 2 : ℝ)) * (L' ^ (-(1 / 2 : ℝ)) * L') * D ^ (-((N : ℝ) - 1)) := by
        simp only [K, gramConst]
        rw [hpow]
        field_simp
        ring
    _ = _ := by rw [hL'half]

/-! ### Orthogonality from Fourier supports meeting in a null set -/

/-- Plancherel: `∫ conj(𝓕u) 𝓕v = ∫ conj(u) v` for integrable `u`, continuous integrable `v` with
integrable `𝓕 v`. -/
theorem integral_conj_fourier_mul_eq {u v : ℝ → ℂ} (hu : Integrable u) (hv : Continuous v)
    (hvi : Integrable v) (hFv : Integrable (𝓕 v)) :
    ∫ ξ, (starRingEnd ℂ) (𝓕 u ξ) * 𝓕 v ξ = ∫ x, (starRingEnd ℂ) (u x) * v x := by
  have key := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip (innerSL ℂ)
    (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hu hFv
  have hinv := Continuous.fourierInv_fourier_eq hv hvi hFv
  simp only [flip_innerₗ, innerSL_apply_apply] at key
  have h2 : ∀ x, VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ) (𝓕 v) x = v x := by
    intro x
    exact congrFun hinv x
  simp only [h2] at key
  convert key using 2 with ξ x
  · simp only [RCLike.inner_apply, mul_comm]
    rfl
  · simp [RCLike.inner_apply, mul_comm]

/-- `⟨u, v⟩ = 0` if `conj(𝓕u) 𝓕v = 0` almost everywhere. -/
theorem pairing_eq_zero_of_ae {u v : ℝ → ℂ} (hu : Integrable u) (hv : Continuous v)
    (hvi : Integrable v) (hFv : Integrable (𝓕 v))
    (h : ∀ᵐ ξ, (starRingEnd ℂ) (𝓕 u ξ) * 𝓕 v ξ = 0) : pairing u v = 0 := by
  have h1 := integral_conj_fourier_mul_eq hu hv hvi hFv
  rw [integral_eq_zero_of_ae h] at h1
  unfold pairing
  have h3 : ∫ x, u x * (starRingEnd ℂ) (v x) =
      (starRingEnd ℂ) (∫ x, (starRingEnd ℂ) (u x) * v x) := by
    rw [← integral_conj]
    congr 1
    funext x
    simp [mul_comm]
  rw [h3, ← h1, map_zero]

/-- A continuous function vanishing off a bounded set is integrable. -/
theorem integrable_of_continuous_of_eq_zero {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Continuous f) {S : Set ℝ}
    (hS : Bornology.IsBounded S) (h : ∀ ξ, ξ ∉ S → f ξ = 0) : Integrable f :=
  hf.integrable_of_hasCompactSupport
    (HasCompactSupport.intro hS.isCompact_closure (fun ξ hξ => h ξ (fun h' => hξ (subset_closure h'))))

theorem continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf

/-- Two closed intervals whose half-open versions are disjoint meet in at most one point. -/
theorem Icc_inter_Icc_subset_of_disjoint {a b a' b' : ℝ}
    (h : Disjoint (Ico a b) (Ico a' b')) : Icc a b ∩ Icc a' b' ⊆ {max a a'} := by
  rw [Set.Ico_disjoint_Ico] at h
  rintro ξ ⟨⟨h1, h2⟩, h3, h4⟩
  simp only [Set.mem_singleton_iff]
  apply le_antisymm
  · calc ξ ≤ min b b' := le_min h2 h4
      _ ≤ _ := h
  · exact max_le h1 h3

/-- If `𝓕u` vanishes off `Icc a b`, `𝓕v` off `Icc a' b'` and `Ico a b`, `Ico a' b'` are disjoint, then
`⟨u, v⟩ = 0`. -/
theorem pairing_eq_zero_of_fourier_Icc {u v : ℝ → ℂ} (hu : Integrable u) (hv : Continuous v)
    (hvi : Integrable v) {a b a' b' : ℝ} (hFu : ∀ ξ, ξ ∉ Icc a b → 𝓕 u ξ = 0)
    (hFv : ∀ ξ, ξ ∉ Icc a' b' → 𝓕 v ξ = 0) (h : Disjoint (Ico a b) (Ico a' b')) :
    pairing u v = 0 := by
  have hFvi : Integrable (𝓕 v) :=
    integrable_of_continuous_of_eq_zero (continuous_fourier_of_integrable hvi)
      (Metric.isBounded_Icc a' b') hFv
  refine pairing_eq_zero_of_ae hu hv hvi hFvi ?_
  have hnull : volume ({max a a'} : Set ℝ) = 0 := measure_singleton _
  refine measure_mono_null (fun ξ hξ => ?_) hnull
  apply Icc_inter_Icc_subset_of_disjoint h
  constructor
  · by_contra hc
    have : (starRingEnd ℂ) (𝓕 u ξ) * 𝓕 v ξ = 0 := by rw [hFu ξ hc, map_zero, zero_mul]
    exact hξ this
  · by_contra hc
    have : (starRingEnd ℂ) (𝓕 u ξ) * 𝓕 v ξ = 0 := by rw [hFv ξ hc, mul_zero]
    exact hξ this

/-! ### (G2) disjoint frequency supports -/

/-- The Fourier transform of an adapted packet with bounded frequency set is integrable. -/
theorem IsAdapted.integrable_fourier {N : ℕ} {I ω : Set ℝ} {φ : ℝ → ℂ} (hφ : IsAdapted N I ω φ)
    (hω : Bornology.IsBounded ω) : Integrable (𝓕 φ) :=
  integrable_of_continuous_of_eq_zero (continuous_fourier_of_integrable hφ.2.1) hω hφ.2.2.1

/-- **(G2)** `⟨φ, ψ⟩ = 0` for adapted packets whose frequency sets are disjoint (`ω'` bounded;
Plancherel). -/
theorem pairing_eq_zero_of_disjoint {N N' : ℕ} {I I' ω ω' : Set ℝ} {φ ψ : ℝ → ℂ}
    (hφ : IsAdapted N I ω φ) (hψ : IsAdapted N' I' ω' ψ) (hω' : Bornology.IsBounded ω')
    (hdisj : Disjoint ω ω') : pairing φ ψ = 0 :=
  pairing_eq_zero_of_ae hφ.2.1 (IsAdapted.continuous hψ) hψ.2.1
    (IsAdapted.integrable_fourier hψ hω') (ae_of_all _ fun ξ => by
      by_cases hξ : ξ ∈ ω
      · rw [hψ.2.2.1 ξ (Set.disjoint_left.1 hdisj hξ), mul_zero]
      · rw [hφ.2.2.1 ξ hξ, map_zero, zero_mul])

/-! ### Tri-tile geometry at one scale -/

theorem volume_timeInt (t : ℤ × ℤ × ℤ) : (volume (timeInt t)).toReal = (2 : ℝ) ^ t.1 := by
  unfold timeInt
  rw [Real.volume_Ico, ENNReal.toReal_ofReal (by
    have : (0 : ℝ) < 2 ^ t.1 := zpow_pos (by norm_num) _
    nlinarith)]
  ring

theorem intervalCentre_timeInt (t : ℤ × ℤ × ℤ) :
    intervalCentre (timeInt t) = (2 : ℝ) ^ t.1 * (t.2.1 + 1 / 2) := by
  have h : (2 : ℝ) ^ t.1 * t.2.1 < (2 : ℝ) ^ t.1 * (t.2.1 + 1) := by
    have : (0 : ℝ) < 2 ^ t.1 := zpow_pos (by norm_num) _
    nlinarith
  unfold intervalCentre timeInt
  rw [csInf_Ico h, csSup_Ico h]
  ring

theorem isBounded_freqInt (a b : ℤ) (k : Fin 3) (t : ℤ × ℤ × ℤ) :
    Bornology.IsBounded (freqInt a b k t) :=
  Metric.isBounded_Ico _ _

/-- The difference of two numerators of one slot is a multiple (`1` or `2`) of `ℓ - ℓ'`. -/
theorem freqNum_sub (a b : ℤ) (k : Fin 3) (t t' : ℤ × ℤ × ℤ) :
    ∃ m : ℤ, (m = 1 ∨ m = 2) ∧ freqNum a b t k - freqNum a b t' k = m * (t.2.2 - t'.2.2) := by
  fin_cases k
  · exact ⟨1, Or.inl rfl, by simp [freqNum]⟩
  · exact ⟨1, Or.inl rfl, by simp [freqNum]⟩
  · exact ⟨2, Or.inr rfl, by simp [freqNum]; ring⟩

/-- At one scale, the frequency cells of two tri-tiles with distinct congruent `ℓ` are disjoint
(the same-scale case of C1 (a), (c)). -/
theorem disjoint_freqInt_of_ne {a b : ℤ} (k : Fin 3) {t t' : ℤ × ℤ × ℤ} (hs : t.1 = t'.1)
    (hℓ : t.2.2 ≡ t'.2.2 [ZMOD 3]) (hne : t.2.2 ≠ t'.2.2) :
    Disjoint (freqInt a b k t) (freqInt a b k t') := by
  obtain ⟨m, hm, hsub⟩ := freqNum_sub a b k t t'
  set n := freqNum a b t k
  set n' := freqNum a b t' k
  have h3 : (3 : ℤ) ∣ n - n' := by
    rw [hsub]
    exact Dvd.dvd.mul_left (Int.ModEq.dvd hℓ.symm) _
  have hne' : n - n' ≠ 0 := by
    rw [hsub]
    have : t.2.2 - t'.2.2 ≠ 0 := sub_ne_zero.2 hne
    rcases hm with hm | hm <;> subst hm <;> simpa using this
  have hsep : 3 ≤ n - n' ∨ n - n' ≤ -3 := by
    obtain ⟨q, hq⟩ := h3
    rw [hq] at hne' ⊢
    have : q ≠ 0 := by rintro rfl; simp at hne'
    omega
  unfold freqInt
  rw [← hs]
  set A : ℝ := (2 : ℝ) ^ (-t.1)
  have hA : 0 < A := zpow_pos (by norm_num) _
  rw [Set.Ico_disjoint_Ico]
  rcases hsep with h | h
  · have h' : (n' : ℝ) / 3 + 1 ≤ (n : ℝ) / 3 := by
      have : (3 : ℝ) ≤ (n : ℝ) - n' := by exact_mod_cast h
      linarith
    calc min (A * ((n : ℝ) / 3 + 1)) (A * ((n' : ℝ) / 3 + 1)) ≤ A * ((n' : ℝ) / 3 + 1) :=
          min_le_right _ _
      _ ≤ A * ((n : ℝ) / 3) := mul_le_mul_of_nonneg_left h' hA.le
      _ ≤ _ := le_max_left _ _
  · have h' : (n : ℝ) / 3 + 1 ≤ (n' : ℝ) / 3 := by
      have : (n : ℝ) - n' ≤ -3 := by exact_mod_cast h
      linarith
    calc min (A * ((n : ℝ) / 3 + 1)) (A * ((n' : ℝ) / 3 + 1)) ≤ A * ((n : ℝ) / 3 + 1) :=
          min_le_left _ _
      _ ≤ A * ((n' : ℝ) / 3) := mul_le_mul_of_nonneg_left h' hA.le
      _ ≤ _ := le_max_right _ _

/-! ### (G3) the same-scale row sum -/

theorem summable_one_add_abs_int_rpow_neg {p : ℝ} (hp : 1 < p) :
    Summable fun j : ℤ => (1 + |(j : ℝ)|) ^ (-p) := by
  refine Summable.of_norm_bounded_eventually (Real.summable_abs_int_rpow hp) ?_
  filter_upwards [eventually_cofinite_ne 0] with j hj
  have hj' : (0 : ℝ) < |(j : ℝ)| := abs_pos.2 (by exact_mod_cast hj)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos hj' (by linarith) (by linarith)

/-- The constant of (G3): `C_N · Σ_{j ∈ ℤ} (1 + |j|)^{-(N-1)}`. -/
noncomputable def sameScaleConst (N : ℕ) : ℝ :=
  gramConst N * ∑' j : ℤ, (1 + |(j : ℝ)|) ^ (-((N : ℝ) - 1))

/-- (G1) at one scale: two tri-tiles with the same scale and the same `ℓ`, `I_{t'} = I_t + j|I_t|`. -/
theorem norm_pairing_le_sameScale {N : ℕ} (hN : 2 ≤ N) {a b : ℤ} (k : Fin 3) {t t' : ℤ × ℤ × ℤ}
    {φ ψ : ℝ → ℂ} (hφ : IsAdapted N (timeInt t) (freqInt a b k t) φ)
    (hψ : IsAdapted N (timeInt t') (freqInt a b k t') ψ) (hs : t'.1 = t.1) :
    ‖pairing φ ψ‖ ≤ gramConst N * (1 + |((t'.2.1 - t.2.1 : ℤ) : ℝ)|) ^ (-((N : ℝ) - 1)) := by
  have hL : (volume (timeInt t)).toReal = (2 : ℝ) ^ t.1 := volume_timeInt t
  have hL' : (volume (timeInt t')).toReal = (2 : ℝ) ^ t.1 := by rw [volume_timeInt, hs]
  have hpos : (0 : ℝ) < 2 ^ t.1 := zpow_pos (by norm_num) _
  have h := norm_pairing_le_of_isAdapted hN hφ hψ (by rw [hL']; exact hpos) (by rw [hL, hL'])
  rw [hL, hL', intervalCentre_timeInt, intervalCentre_timeInt, hs] at h
  have h1 : ((2 : ℝ) ^ t.1) ^ (-(1 / 2 : ℝ)) * ((2 : ℝ) ^ t.1) ^ (1 / 2 : ℝ) = 1 := by
    rw [Real.rpow_neg hpos.le, inv_mul_cancel₀ (by positivity)]
  have h2 : |(2 : ℝ) ^ t.1 * (t.2.1 + 1 / 2) - (2 : ℝ) ^ t.1 * (t'.2.1 + 1 / 2)| / 2 ^ t.1 =
      |((t'.2.1 - t.2.1 : ℤ) : ℝ)| := by
    rw [show (2 : ℝ) ^ t.1 * (t.2.1 + 1 / 2) - (2 : ℝ) ^ t.1 * (t'.2.1 + 1 / 2) =
      (2 : ℝ) ^ t.1 * -((t'.2.1 - t.2.1 : ℤ) : ℝ) by push_cast; ring, abs_mul, abs_of_pos hpos,
      abs_neg]
    field_simp
  rw [h2, mul_assoc (gramConst N), h1, mul_one] at h
  exact h

/-- **(G3)** For tri-tile packets in one class `Idx_{s',α}`: the same-scale row sum
`Σ_{t' ∈ P, s(t') = s(t)} |⟨φ_{t,k}, φ_{t',k}⟩| ≤ C'_N` (only `t'` with the same `ℓ` contribute, by (G2);
those are determined by `v'`, and (G1) gives `C_N (1 + |v' - v|)^{-(N-1)}`). -/
theorem sum_norm_pairing_sameScale_le {N : ℕ} (hN : 3 ≤ N) {a b s' α : ℤ} (k : Fin 3)
    (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (P : Finset (ℤ × ℤ × ℤ)) (hP : ∀ t ∈ P, t ∈ triIdx s' α)
    (hφ : ∀ t ∈ P, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) {t : ℤ × ℤ × ℤ}
    (ht : t ∈ P) :
    ∑ t' ∈ P with t'.1 = t.1, ‖pairing (φ t k) (φ t' k)‖ ≤ sameScaleConst N := by
  set f : ℤ → ℝ := fun j => (1 + |(j : ℝ)|) ^ (-((N : ℝ) - 1))
  have hN1 : (1 : ℝ) < (N : ℝ) - 1 := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hf : Summable f := summable_one_add_abs_int_rpow_neg hN1
  have hpt : ∀ t' ∈ P.filter (fun t' => t'.1 = t.1), ‖pairing (φ t k) (φ t' k)‖ ≤
      if t'.2.2 = t.2.2 then gramConst N * f (t'.2.1 - t.2.1) else 0 := by
    intro t' ht'
    rw [Finset.mem_filter] at ht'
    split_ifs with hℓ
    · exact norm_pairing_le_sameScale (by omega) k (hφ t ht) (hφ t' ht'.1) ht'.2
    · have hmod : t.2.2 ≡ t'.2.2 [ZMOD 3] := ((hP t ht).2).trans ((hP t' ht'.1).2).symm
      have hdisj := disjoint_freqInt_of_ne (a := a) (b := b) k ht'.2.symm hmod (Ne.symm hℓ)
      rw [pairing_eq_zero_of_disjoint (hφ t ht) (hφ t' ht'.1) (isBounded_freqInt a b k t') hdisj,
        norm_zero]
  have hinj : Set.InjOn (fun t' : ℤ × ℤ × ℤ => t'.2.1 - t.2.1)
      ((P.filter (fun t' => t'.1 = t.1)).filter (fun t' => t'.2.2 = t.2.2) : Set _) := by
    intro x hx y hy hxy
    simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_ofPred_eq] at hx hy
    simp only at hxy
    ext
    · rw [hx.1.2, hy.1.2]
    · omega
    · rw [hx.2, hy.2]
  calc ∑ t' ∈ P with t'.1 = t.1, ‖pairing (φ t k) (φ t' k)‖
      ≤ ∑ t' ∈ P with t'.1 = t.1, (if t'.2.2 = t.2.2 then gramConst N * f (t'.2.1 - t.2.1) else 0) :=
        Finset.sum_le_sum hpt
    _ = ∑ t' ∈ (P.filter (fun t' => t'.1 = t.1)).filter (fun t' => t'.2.2 = t.2.2),
          gramConst N * f (t'.2.1 - t.2.1) := by
        rw [Finset.sum_filter (fun t' : ℤ × ℤ × ℤ => t'.2.2 = t.2.2)]
    _ = gramConst N * ∑ j ∈ ((P.filter (fun t' => t'.1 = t.1)).filter
          (fun t' => t'.2.2 = t.2.2)).image (fun t' => t'.2.1 - t.2.1), f j := by
        rw [Finset.mul_sum, Finset.sum_image hinj]
    _ ≤ gramConst N * ∑' j, f j :=
        mul_le_mul_of_nonneg_left (hf.sum_le_tsum _ (fun _ _ => by positivity))
          (gramConst_nonneg (by omega))
    _ = sameScaleConst N := rfl

end PrimeBHT.TimeFrequency.Tile
