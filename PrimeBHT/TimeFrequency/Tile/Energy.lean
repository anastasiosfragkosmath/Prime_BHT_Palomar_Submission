module

public import PrimeCarleson.Proof.Oplus.External.THAssembly
public import PrimeBHT.Frozen.IsAdapted
public import PrimeBHT.Frozen.Pairing
public import PrimeBHT.Frozen.TimeInt
public import PrimeBHT.Frozen.FreqInt

/-!
# Node C7 of the X1 blueprint: the refined energy bound (route 2, via Oplus)

The estimate C7' that C9 step 5 needs, obtained from the abstract tile-energy bound
`PrimeCarleson.Proof.Oplus.tile_energy_abstract` of the earlier project (Grafakos-Tao-Terwilleger,
Lemma 1; Hardy-Littlewood superlevel set of `M 1_E`, packets with the bounds `PacketBounds` of
exponent `4`, a Bessel hypothesis with constant `B`).

* `packetBounds_of_isAdapted`: the glue `IsAdapted ⇒ PacketBounds`: a packet adapted (exponent
  `N ≥ 4`) to `(I, ω)` with `I` dyadic, demodulated by a frequency `ξ` with `|ξ - c(ω)| ≤ Λ/|I|`,
  has `PacketBounds (1 + 2πΛ)`. No mean-zero property of the demodulated packet is needed:
  `tile_energy_abstract` uses only the mean zero of the Calderon-Zygmund bad pieces of `f`.
  Consequently only `ξ' ∈ 50 ω_{t,k}` (not `ξ' ∉ 2 ω_{t,k}`) of the lacunarity fact C1(e) is used
  here; the lacunarity enters through the Bessel hypothesis (C8(a)).
* `sum_le_three_mul_of_card_fibre_le`: splitting a finite family in which at most `3` members share
  a key into `3` subfamilies on which the key is injective.
* `sum_norm_sq_pairing_le_of_bessel` (C7'): for a finite family `T` of tri-tile indices with time
  intervals inside `I_T`, at most `3` per time interval, packets `φ t k` adapted to
  `(timeInt t, freqInt a b k t)`, a frequency `ξ' ∈ 50 ω_{t,k}` for all `t ∈ T`, the Bessel
  inequality for `(φ t k)_{t ∈ T}` with constant `B`, `|f| ≤ A 1_E` and `I_t ⊄ {M 1_E > λ}`:
  `∑_{t ∈ T} |⟨f, φ_{t,k}⟩|² ≤ energyConst B · A² λ² |I_T|`.
* `sum_norm_sq_pairing_normalized_le_of_bessel` (C9 step 5): for `g₁ = |E₁|⁻¹ h₁`,
  `|h₁| ≤ 1_{E₁}`, and `I_t ⊄ F ⊇ {M 1_{E₁} > C₀ |E₁|}`:
  `|I_T|⁻¹ ∑_{t ∈ T} |⟨g₁, φ_{t,k}⟩|² ≤ energyConst B · C₀²`.

The maximal function is `PrimeCarleson.Proof.Common.maximalHLR` (blueprint C6 after the audit).

**Deviation from the blueprint's C7 statement.** `tile_energy_abstract` has the hypothesis
`I_t ⊄ {M 1_E > λ}` for `|f| ≤ 1_E` (superlevel set of the maximal function of the *indicator*),
not `I_t ⊄ {M f > λ}`. This is exactly what C9 step 5 uses (`{M 1_{E₁} > C₀|E₁|} ⊆ F`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PrimeBHT.Statements
open PrimeCarleson.Proof
open PrimeCarleson.Proof.Common (maximalHLR)
open PrimeCarleson.Proof.Oplus (PacketBounds maxSuperlevel tile_energy_abstract)
open scoped ENNReal

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Tile

/-! ### Demodulation -/

/-- The phase `e^{-2πi ξ y}`. -/
def energyPhase (ξ y : ℝ) : ℂ := Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ) * (y : ℂ)))

theorem norm_energyPhase (ξ y : ℝ) : ‖energyPhase ξ y‖ = 1 := by
  rw [energyPhase, Complex.norm_exp]
  simp

theorem energyPhase_mul_energyPhase (ξ η y : ℝ) :
    energyPhase ξ y * energyPhase η y = energyPhase (ξ + η) y := by
  rw [energyPhase, energyPhase, energyPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem hasDerivAt_energyPhase (ξ y : ℝ) :
    HasDerivAt (energyPhase ξ) (-(2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) * energyPhase ξ y) y := by
  have h1 : HasDerivAt (fun y : ℝ => -(2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ) * (y : ℂ)))
      (-(2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ))) y := by
    have := ((hasDerivAt_id y).ofReal_comp).const_mul (-(2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)))
    convert this using 1
    · funext z; simp
    · simp
  have h2 := h1.cexp
  have he : energyPhase ξ =
      fun y : ℝ => Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ) * (y : ℂ))) := rfl
  rw [he]
  exact h2.congr_deriv (mul_comm _ _)

/-- The demodulated pairing: `⟨g, e^{-2πiξ·} φ⟩ = ⟨e^{2πiξ·} g, φ⟩`. -/
theorem pairing_energyPhase_mul (g φ : ℝ → ℂ) (ξ : ℝ) :
    pairing g (fun y => energyPhase ξ y * φ y) = pairing (fun y => energyPhase (-ξ) y * g y) φ := by
  unfold pairing
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have h : (starRingEnd ℂ) (energyPhase ξ y) = energyPhase (-ξ) y := by
    rw [energyPhase, energyPhase, ← Complex.exp_conj]
    congr 1
    simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  simp only [map_mul, h]
  ring

/-- Modulating both arguments does not change the pairing. -/
theorem pairing_energyPhase_mul_mul (f φ : ℝ → ℂ) (ξ : ℝ) :
    pairing (fun y => energyPhase ξ y * f y) (fun y => energyPhase ξ y * φ y) = pairing f φ := by
  rw [pairing_energyPhase_mul]
  unfold pairing
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [← mul_assoc, energyPhase_mul_energyPhase, neg_add_cancel]
  simp [energyPhase]

/-! ### `IsAdapted ⇒ PacketBounds` -/

private theorem intervalCentre_toSet (D : Oplus.Dyadic) : intervalCentre D.toSet = D.center := by
  unfold intervalCentre Oplus.Dyadic.toSet
  rw [csInf_Ico D.left_lt_right, csSup_Ico D.left_lt_right]
  unfold Oplus.Dyadic.left Oplus.Dyadic.right Oplus.Dyadic.center
  ring

private theorem toReal_volume_toSet (D : Oplus.Dyadic) : (volume D.toSet).toReal = D.length := by
  rw [Oplus.Dyadic.volume_toSet, ENNReal.toReal_ofReal D.length_pos.le]

/-- `w^{-N} ≤ w^{-4}` for `w ≥ 1`, `N ≥ 4` (rpow to zpow). -/
private theorem rpow_neg_natCast_le_zpow_neg_four {w : ℝ} (hw : 1 ≤ w) {N : ℕ} (hN : 4 ≤ N) :
    w ^ (-(N : ℝ)) ≤ w ^ (-4 : ℤ) := by
  rw [← Real.rpow_intCast]
  refine Real.rpow_le_rpow_of_exponent_le hw ?_
  have : (4 : ℝ) ≤ N := by exact_mod_cast hN
  push_cast
  linarith

private theorem rpow_neg_half_eq {L : ℝ} (hL : 0 < L) : L ^ (-((0 : ℕ) : ℝ) - 1 / 2) = (√L)⁻¹ := by
  rw [show (-((0 : ℕ) : ℝ) - 1 / 2) = -(1 / 2) by norm_num, Real.rpow_neg hL.le,
    Real.sqrt_eq_rpow]

private theorem rpow_neg_three_halves_eq {L : ℝ} (hL : 0 < L) :
    L ^ (-((1 : ℕ) : ℝ) - 1 / 2) = (L * √L)⁻¹ := by
  rw [show (-((1 : ℕ) : ℝ) - 1 / 2) = -(1 + 1 / 2) by norm_num, Real.rpow_neg hL.le,
    Real.rpow_add hL, Real.rpow_one, Real.sqrt_eq_rpow]

/-- **Glue `IsAdapted ⇒ PacketBounds`.** A packet adapted with exponent `N ≥ 4` to `(I, ω)`, `I`
dyadic, demodulated by a frequency `ξ` with `|ξ - c(ω)| ≤ Λ / |I|`, satisfies the packet bounds of
`tile_energy_abstract` with constant `1 + 2πΛ`. -/
theorem packetBounds_of_isAdapted {N : ℕ} (hN : 4 ≤ N) {D : Oplus.Dyadic} {ω : Set ℝ}
    {φ : ℝ → ℂ} (hφ : IsAdapted N D.toSet ω φ) {ξ Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hξ : |ξ - intervalCentre ω| ≤ Λ / D.length) :
    PacketBounds (1 + 2 * Real.pi * Λ) D (fun y => energyPhase ξ y * φ y) := by
  obtain ⟨hC1, -, -, hb⟩ := hφ
  have hL := D.length_pos
  have hs : 0 < √D.length := Real.sqrt_pos.2 hL
  rw [toReal_volume_toSet, intervalCentre_toSet] at hb
  set c := intervalCentre ω with hc
  set u : ℝ → ℂ := fun y => Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (c : ℂ) * (y : ℂ))) * φ y
    with hu
  have hφd : Differentiable ℝ φ := hC1.differentiable (by norm_num)
  have hud : Differentiable ℝ u := fun y => ((hasDerivAt_energyPhase c y).differentiableAt).mul (hφd y)
  have hψeq : (fun y => energyPhase ξ y * φ y) = fun y => energyPhase (ξ - c) y * u y := by
    funext y
    simp only [hu]
    rw [← mul_assoc]
    change _ = energyPhase (ξ - c) y * energyPhase c y * φ y
    rw [energyPhase_mul_energyPhase, sub_add_cancel]
  set W : ℝ → ℝ := fun y => (1 + |y - D.center| / D.length) ^ (-4 : ℤ) with hW
  have hw1 : ∀ y, 1 ≤ 1 + |y - D.center| / D.length := fun y => by
    have : 0 ≤ |y - D.center| / D.length := by positivity
    linarith
  have hu0 : ∀ y, ‖u y‖ ≤ (√D.length)⁻¹ * W y := by
    intro y
    have h := hb 0 (Nat.zero_le _) y
    rw [iteratedDeriv_zero, rpow_neg_half_eq hL] at h
    refine h.trans ?_
    gcongr
    exact rpow_neg_natCast_le_zpow_neg_four (hw1 y) hN
  have hu1 : ∀ y, ‖deriv u y‖ ≤ (D.length * √D.length)⁻¹ * W y := by
    intro y
    have h := hb 1 le_rfl y
    rw [iteratedDeriv_one, rpow_neg_three_halves_eq hL] at h
    refine h.trans ?_
    gcongr
    exact rpow_neg_natCast_le_zpow_neg_four (hw1 y) hN
  have hW0 : ∀ y, 0 ≤ W y := fun y => by positivity
  clear_value u
  rw [hψeq]
  refine ⟨fun y => ((hasDerivAt_energyPhase (ξ - c) y).differentiableAt).mul (hud y),
    fun y => ?_, fun y => ?_⟩
  · rw [norm_mul, norm_energyPhase, one_mul]
    refine (hu0 y).trans ?_
    have : 0 ≤ 2 * Real.pi * Λ := by positivity
    have h2 : 0 ≤ (√D.length)⁻¹ * W y := mul_nonneg (by positivity) (hW0 y)
    nlinarith
  · have hder : deriv (fun y => energyPhase (ξ - c) y * u y) y =
        -(2 * (Real.pi : ℂ) * Complex.I * ((ξ - c : ℝ) : ℂ)) * energyPhase (ξ - c) y * u y +
          energyPhase (ξ - c) y * deriv u y :=
      ((hasDerivAt_energyPhase (ξ - c) y).mul (hud y).hasDerivAt).deriv
    rw [hder]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_energyPhase, norm_mul, norm_energyPhase, mul_one, one_mul,
      norm_neg]
    have hr : ‖2 * (Real.pi : ℂ) * Complex.I * ((ξ - c : ℝ) : ℂ)‖ = 2 * Real.pi * |ξ - c| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simp [abs_of_pos Real.pi_pos]
    rw [hr]
    have hξ' : 2 * Real.pi * |ξ - c| ≤ 2 * Real.pi * (Λ / D.length) := by
      have := Real.pi_pos
      gcongr
    have key : 2 * Real.pi * (Λ / D.length) * ((√D.length)⁻¹ * W y) =
        2 * Real.pi * Λ * ((D.length * √D.length)⁻¹ * W y) := by
      field_simp
    calc 2 * Real.pi * |ξ - c| * ‖u y‖ + ‖deriv u y‖
        ≤ 2 * Real.pi * (Λ / D.length) * ((√D.length)⁻¹ * W y) +
            (D.length * √D.length)⁻¹ * W y := by
          gcongr
          · exact hu0 y
          · exact hu1 y
      _ = (1 + 2 * Real.pi * Λ) * (D.length * √D.length)⁻¹ * W y := by
          rw [key]; ring

/-! ### Splitting a family with multiplicity at most `3` -/

/-- If at most `3` members of the finite family `T` share a key, and members with the same key are
separated by an integer label `ord`, then any bound `K` on the sums over the subfamilies on which the
key is injective gives `∑_T ≤ 3 K`. -/
theorem sum_le_three_mul_of_card_fibre_le {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (T : Finset ι) (key : ι → κ) (ord : ι → ℤ)
    (hinj : ∀ i ∈ T, ∀ j ∈ T, key i = key j → ord i = ord j → i = j)
    (hcard : ∀ i ∈ T, (T.filter fun j => key j = key i).card ≤ 3) (F : ι → ℝ) (K : ℝ)
    (hK : ∀ Q ⊆ T, Set.InjOn key (Q : Set ι) → ∑ i ∈ Q, F i ≤ K) :
    ∑ i ∈ T, F i ≤ 3 * K := by
  set below : ι → Finset ι := fun i => T.filter fun j => key j = key i ∧ ord j < ord i with hbelow
  set r : ι → ℕ := fun i => (below i).card with hr
  have hr3 : ∀ i ∈ T, r i ∈ Finset.range 3 := by
    intro i hi
    rw [Finset.mem_range]
    refine lt_of_lt_of_le (Finset.card_lt_card ?_) (hcard i hi)
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨i, Finset.mem_filter.2 ⟨hi, rfl⟩, fun h => ?_⟩
      exact lt_irrefl _ (Finset.mem_filter.1 h).2.2
    · intro j hj
      have hj' := Finset.mem_filter.1 hj
      exact Finset.mem_filter.2 ⟨hj'.1, hj'.2.1⟩
  have hlt : ∀ i ∈ T, ∀ j ∈ T, key i = key j → ord i < ord j → r i < r j := by
    intro i hi j hj hk ho
    refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨i, Finset.mem_filter.2 ⟨hi, hk, ho⟩, fun h => lt_irrefl _ (Finset.mem_filter.1 h).2.2⟩
    · intro l hl
      have hl' := Finset.mem_filter.1 hl
      exact Finset.mem_filter.2 ⟨hl'.1, hl'.2.1.trans hk, hl'.2.2.trans ho⟩
  rw [← Finset.sum_fiberwise_of_maps_to hr3]
  calc ∑ m ∈ Finset.range 3, ∑ i ∈ T with r i = m, F i ≤ ∑ _m ∈ Finset.range 3, K := by
        refine Finset.sum_le_sum fun m _ => hK _ (Finset.filter_subset _ _) ?_
        intro i hi j hj hk
        have hi' := Finset.mem_filter.1 (Finset.mem_coe.1 hi)
        have hj' := Finset.mem_filter.1 (Finset.mem_coe.1 hj)
        rcases lt_trichotomy (ord i) (ord j) with h | h | h
        · exact absurd (hlt i hi'.1 j hj'.1 hk h) (by rw [hi'.2, hj'.2]; exact lt_irrefl _)
        · exact hinj i hi'.1 j hj'.1 hk h
        · exact absurd (hlt j hj'.1 i hi'.1 hk.symm h) (by rw [hi'.2, hj'.2]; exact lt_irrefl _)
    _ = 3 * K := by simp

/-! ### Elementary facts on the frozen grid -/

private theorem toReal_volume_freqInt (a b : ℤ) (k : Fin 3) (t : ℤ × ℤ × ℤ) :
    (volume (freqInt a b k t)).toReal = (2 : ℝ) ^ (-t.1) := by
  unfold freqInt
  rw [Real.volume_Ico, ENNReal.toReal_ofReal (by ring_nf; positivity)]
  ring

/-- The pairing is linear in the first argument. -/
private theorem pairing_const_mul (c : ℂ) (f φ : ℝ → ℂ) :
    pairing (fun x => c * f x) φ = c * pairing f φ := by
  unfold pairing
  simp_rw [mul_assoc]
  exact integral_const_mul c _

private theorem abs_sub_intervalCentre_le_of_mem_dilate {ω : Set ℝ} {ξ C : ℝ}
    (h : ξ ∈ Set.Ico (intervalCentre ω - C * (volume ω).toReal / 2)
      (intervalCentre ω + C * (volume ω).toReal / 2)) :
    |ξ - intervalCentre ω| ≤ C / 2 * (volume ω).toReal := by
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

/-! ### The energy bound C7' -/

/-- The constant of the energy bound: `3 · 15000000 · ((1 + 50π)² + B)`; `3` from the split into
families with one tile per time interval, `1 + 50π` the packet constant for `|ξ' - c(ω)| ≤ 25|ω|`,
`B` the Bessel constant (C8(a)). -/
def energyConst (B : ℝ) : ℝ := 3 * (15000000 * ((1 + 2 * Real.pi * 25) ^ 2 + B))

theorem energyConst_nonneg {B : ℝ} (hB : 0 ≤ B) : 0 ≤ energyConst B := by
  unfold energyConst; positivity

/-- **The energy bound C7' (conditional on the Bessel inequality C8(a)).**
Let `T` be a finite family of tri-tile indices whose time intervals lie in the dyadic interval
`I_T = 2^{sT}[vT, vT+1)`, at most `3` of them sharing a time interval; let `φ t k` be adapted with
exponent `N ≥ 4` to `(I_t, ω_{t,k})`, let `ξ' ∈ 50 ω_{t,k}` for all `t ∈ T` (C1(e)), and let the
family `(φ t k)_{t ∈ T}` satisfy the Bessel inequality with constant `B` (C8(a)). Then for `|f| ≤ A 1_E`
and `I_t ⊄ {M 1_E > λ}` for all `t ∈ T`:
`∑_{t ∈ T} |⟨f, φ_{t,k}⟩|² ≤ energyConst B · A² λ² |I_T|`. -/
theorem sum_norm_sq_pairing_le_of_bessel {N : ℕ} (hN : 4 ≤ N) {a b : ℤ} {k : Fin 3}
    {T : Finset (ℤ × ℤ × ℤ)} {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hφ : ∀ t ∈ T, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k))
    {ξ' : ℝ}
    (hξ' : ∀ t ∈ T, ξ' ∈ Set.Ico
      (intervalCentre (freqInt a b k t) - 50 * (volume (freqInt a b k t)).toReal / 2)
      (intervalCentre (freqInt a b k t) + 50 * (volume (freqInt a b k t)).toReal / 2))
    {sT vT : ℤ} (hsub : ∀ t ∈ T, timeInt t ⊆ Set.Ico ((2 : ℝ) ^ sT * vT) ((2 : ℝ) ^ sT * (vT + 1)))
    (hmult : ∀ t ∈ T, (T.filter fun t' => (t'.1, t'.2.1) = (t.1, t.2.1)).card ≤ 3)
    {B : ℝ} (hB : 0 ≤ B)
    (hBessel : ∀ g : ℝ → ℂ, MemLp g 2 volume →
      ∑ t ∈ T, ‖pairing g (φ t k)‖ ^ 2 ≤ B * ∫ x, ‖g x‖ ^ 2)
    {E : Set ℝ} (hE : MeasurableSet E) {A lam : ℝ} (hA : 0 ≤ A) (hlam : 0 < lam)
    {f : ℝ → ℂ} (hfm : AEStronglyMeasurable f volume)
    (hf : ∀ x, ‖f x‖ ≤ A * E.indicator (1 : ℝ → ℝ) x)
    (hnot : ∀ t ∈ T,
      ¬ timeInt t ⊆ {x | ENNReal.ofReal lam < maximalHLR (E.indicator (1 : ℝ → ℝ)) x}) :
    ∑ t ∈ T, ‖pairing f (φ t k)‖ ^ 2 ≤
      energyConst B * A ^ 2 * lam ^ 2 *
        (volume (Set.Ico ((2 : ℝ) ^ sT * vT) ((2 : ℝ) ^ sT * (vT + 1)))).toReal := by
  set IT : Oplus.Dyadic := ⟨sT, vT⟩ with hIT
  have hITlen : (volume (Set.Ico ((2 : ℝ) ^ sT * vT) ((2 : ℝ) ^ sT * (vT + 1)))).toReal =
      IT.length := toReal_volume_toSet IT
  rw [hITlen]
  have hLT := IT.length_pos
  rcases hA.eq_or_lt with hA0 | hApos
  · -- `A = 0`: `f = 0`
    have hf0 : f = 0 := funext fun x => by
      have := hf x
      rw [← hA0, zero_mul] at this
      exact norm_le_zero_iff.1 this
    subst hf0
    have : ∀ t, pairing (0 : ℝ → ℂ) (φ t k) = 0 := fun t => by simp [pairing]
    simp only [this, norm_zero]
    rw [← hA0]
    simp
  set ψ : ℤ × ℤ × ℤ → ℝ → ℂ := fun t y => energyPhase ξ' y * φ t k y with hψdef
  set f₀ : ℝ → ℂ := fun y => energyPhase ξ' y * (((A : ℂ)⁻¹) * f y) with hf₀def
  have hphase : ∀ η : ℝ, Continuous (energyPhase η) := fun η => by unfold energyPhase; fun_prop
  have hf₀m : AEStronglyMeasurable f₀ volume :=
    (hphase ξ').aestronglyMeasurable.mul (aestronglyMeasurable_const.mul hfm)
  have hf₀ : ∀ x, ‖f₀ x‖ ≤ E.indicator (fun _ => (1 : ℝ)) x := by
    intro x
    simp only [hf₀def, norm_mul, norm_energyPhase, one_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hApos]
    rw [inv_mul_le_iff₀ hApos]
    exact hf x
  have hpair : ∀ t, pairing f₀ (ψ t) = ((A : ℂ)⁻¹) * pairing f (φ t k) := by
    intro t
    rw [hf₀def, hψdef]
    simp only
    rw [pairing_energyPhase_mul_mul, pairing_const_mul]
  have hpb : ∀ t ∈ T, PacketBounds (1 + 2 * Real.pi * 25) ⟨t.1, t.2.1⟩ (ψ t) := by
    intro t ht
    rw [hψdef]
    refine packetBounds_of_isAdapted (D := ⟨t.1, t.2.1⟩) (ω := freqInt a b k t) (φ := φ t k)
      (ξ := ξ') (Λ := 25) hN (hφ t ht) (by norm_num) ?_
    refine (abs_sub_intervalCentre_le_of_mem_dilate (hξ' t ht)).trans_eq ?_
    rw [toReal_volume_freqInt]
    change 50 / 2 * (2 : ℝ) ^ (-t.1) = 25 / (2 : ℝ) ^ t.1
    rw [zpow_neg]
    ring
  have hbes : ∀ Q ⊆ T, ∀ g : ℝ → ℂ, MemLp g 2 volume →
      ∑ t ∈ Q, ‖pairing g (ψ t)‖ ^ 2 ≤ B * ∫ x, ‖g x‖ ^ 2 := by
    intro Q hQ g hg
    have hg' : MemLp (fun y => energyPhase (-ξ') y * g y) 2 volume :=
      hg.congr_norm ((hphase _).aestronglyMeasurable.mul hg.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun y => by rw [norm_mul, norm_energyPhase, one_mul])
    calc ∑ t ∈ Q, ‖pairing g (ψ t)‖ ^ 2
        = ∑ t ∈ Q, ‖pairing (fun y => energyPhase (-ξ') y * g y) (φ t k)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hψdef]; simp only; rw [pairing_energyPhase_mul]
      _ ≤ ∑ t ∈ T, ‖pairing (fun y => energyPhase (-ξ') y * g y) (φ t k)‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hQ fun _ _ _ => by positivity
      _ ≤ B * ∫ x, ‖energyPhase (-ξ') x * g x‖ ^ 2 := hBessel _ hg'
      _ = B * ∫ x, ‖g x‖ ^ 2 := by simp only [norm_mul, norm_energyPhase, one_mul]
  clear_value ψ f₀
  -- the bound on each injective subfamily
  set K : ℝ := 15000000 * ((1 + 2 * Real.pi * 25) ^ 2 + B) * lam ^ 2 * IT.length with hK
  have hQ : ∀ Q ⊆ T, Set.InjOn (fun t : ℤ × ℤ × ℤ => (t.1, t.2.1)) (Q : Set (ℤ × ℤ × ℤ)) →
      ∑ t ∈ Q, ‖pairing f₀ (ψ t)‖ ^ 2 ≤ K := by
    intro Q hQT hinj
    have hinj' : Set.InjOn (fun t : ℤ × ℤ × ℤ => (⟨t.1, t.2.1⟩ : Oplus.Dyadic))
        (Q : Set (ℤ × ℤ × ℤ)) := by
      intro t ht t' ht' h
      refine hinj ht ht' ?_
      have h1 := congrArg Oplus.Dyadic.k h
      have h2 := congrArg Oplus.Dyadic.m h
      simp only at h1 h2 ⊢
      rw [h1, h2]
    exact tile_energy_abstract (F := E) (lam := lam) (IT := IT) (f := f₀) hE hlam hf₀m hf₀ Q
      (fun t => (⟨t.1, t.2.1⟩ : Oplus.Dyadic)) ψ (by positivity) hB hinj'
      (fun t ht => hsub t (hQT ht)) (fun t ht => hpb t (hQT ht))
      (fun t ht => hnot t (hQT ht)) (hbes Q hQT)
  have hsplit := sum_le_three_mul_of_card_fibre_le T (fun t : ℤ × ℤ × ℤ => (t.1, t.2.1))
    (fun t => t.2.2)
    (fun t _ t' _ hk ho => by
      simp only [Prod.mk.injEq] at hk
      exact Prod.ext hk.1 (Prod.ext hk.2 ho))
    hmult (fun t => ‖pairing f₀ (ψ t)‖ ^ 2) K hQ
  have hlhs : ∑ t ∈ T, ‖pairing f₀ (ψ t)‖ ^ 2 = (A ^ 2)⁻¹ * ∑ t ∈ T, ‖pairing f (φ t k)‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hpair, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hApos]
    ring
  rw [hlhs, inv_mul_le_iff₀ (by positivity)] at hsplit
  calc ∑ t ∈ T, ‖pairing f (φ t k)‖ ^ 2 ≤ A ^ 2 * (3 * K) := hsplit
    _ = energyConst B * A ^ 2 * lam ^ 2 * IT.length := by
      rw [hK, energyConst]; ring

/-! ### The consequence used in C9 step 5 -/

/-- **C9 step 5 (conditional on the Bessel inequality C8(a)).** In the setting of
`sum_norm_sq_pairing_le_of_bessel`, let `g₁ = |E₁|⁻¹ h₁` with `|h₁| ≤ 1_{E₁}`, `0 < |E₁| < ∞`, and let
`I_t ⊄ F` for all `t ∈ T`, where `F ⊇ {M 1_{E₁} > C₀ |E₁|}`. Then
`|I_T|⁻¹ ∑_{t ∈ T} |⟨g₁, φ_{t,k}⟩|² ≤ energyConst B · C₀²`. -/
theorem sum_norm_sq_pairing_normalized_le_of_bessel {N : ℕ} (hN : 4 ≤ N) {a b : ℤ} {k : Fin 3}
    {T : Finset (ℤ × ℤ × ℤ)} {φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ}
    (hφ : ∀ t ∈ T, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k))
    {ξ' : ℝ}
    (hξ' : ∀ t ∈ T, ξ' ∈ Set.Ico
      (intervalCentre (freqInt a b k t) - 50 * (volume (freqInt a b k t)).toReal / 2)
      (intervalCentre (freqInt a b k t) + 50 * (volume (freqInt a b k t)).toReal / 2))
    {sT vT : ℤ} (hsub : ∀ t ∈ T, timeInt t ⊆ Set.Ico ((2 : ℝ) ^ sT * vT) ((2 : ℝ) ^ sT * (vT + 1)))
    (hmult : ∀ t ∈ T, (T.filter fun t' => (t'.1, t'.2.1) = (t.1, t.2.1)).card ≤ 3)
    {B : ℝ} (hB : 0 ≤ B)
    (hBessel : ∀ g : ℝ → ℂ, MemLp g 2 volume →
      ∑ t ∈ T, ‖pairing g (φ t k)‖ ^ 2 ≤ B * ∫ x, ‖g x‖ ^ 2)
    {E₁ : Set ℝ} (hE₁ : MeasurableSet E₁) (hE₁0 : volume E₁ ≠ 0) (hE₁top : volume E₁ ≠ ⊤)
    {h₁ : ℝ → ℂ} (hh₁m : AEStronglyMeasurable h₁ volume)
    (hh₁ : ∀ x, ‖h₁ x‖ ≤ E₁.indicator (1 : ℝ → ℝ) x)
    {C₀ : ℝ} (hC₀ : 0 < C₀) {F : Set ℝ}
    (hF : {x | ENNReal.ofReal C₀ * volume E₁ < maximalHLR (E₁.indicator (1 : ℝ → ℝ)) x} ⊆ F)
    (hnot : ∀ t ∈ T, ¬ timeInt t ⊆ F) :
    ((volume (Set.Ico ((2 : ℝ) ^ sT * vT) ((2 : ℝ) ^ sT * (vT + 1)))).toReal)⁻¹ *
      ∑ t ∈ T, ‖pairing (fun x => ((((volume E₁).toReal)⁻¹ : ℝ) : ℂ) * h₁ x) (φ t k)‖ ^ 2 ≤
        energyConst B * C₀ ^ 2 := by
  set e : ℝ := (volume E₁).toReal with he
  have hepos : 0 < e := ENNReal.toReal_pos hE₁0 hE₁top
  set L : ℝ := (volume (Set.Ico ((2 : ℝ) ^ sT * vT) ((2 : ℝ) ^ sT * (vT + 1)))).toReal with hL
  have hLpos : 0 < L := by
    have := toReal_volume_toSet ⟨sT, vT⟩
    rw [hL]
    exact this ▸ Oplus.Dyadic.length_pos _
  have hfm : AEStronglyMeasurable (fun x => ((e⁻¹ : ℝ) : ℂ) * h₁ x) volume :=
    aestronglyMeasurable_const.mul hh₁m
  have hf : ∀ x, ‖((e⁻¹ : ℝ) : ℂ) * h₁ x‖ ≤ e⁻¹ * E₁.indicator (1 : ℝ → ℝ) x := by
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hepos)]
    gcongr
    exact hh₁ x
  have hset : {x | ENNReal.ofReal (C₀ * e) < maximalHLR (E₁.indicator (1 : ℝ → ℝ)) x} =
      {x | ENNReal.ofReal C₀ * volume E₁ < maximalHLR (E₁.indicator (1 : ℝ → ℝ)) x} := by
    rw [ENNReal.ofReal_mul hC₀.le, he, ENNReal.ofReal_toReal hE₁top]
  have hnot' : ∀ t ∈ T,
      ¬ timeInt t ⊆ {x | ENNReal.ofReal (C₀ * e) < maximalHLR (E₁.indicator (1 : ℝ → ℝ)) x} := by
    intro t ht hsub'
    rw [hset] at hsub'
    exact hnot t ht (hsub'.trans hF)
  have key := sum_norm_sq_pairing_le_of_bessel hN hφ hξ' hsub hmult hB hBessel hE₁
    (inv_pos.2 hepos).le (mul_pos hC₀ hepos) hfm hf hnot'
  rw [← hL] at key
  rw [inv_mul_le_iff₀ hLpos]
  refine key.trans_eq ?_
  field_simp

end PrimeBHT.TimeFrequency.Tile
