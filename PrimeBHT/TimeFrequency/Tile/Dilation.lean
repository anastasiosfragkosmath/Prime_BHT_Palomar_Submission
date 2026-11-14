module

public import PrimeBHT.TimeFrequency.Tile.Grid
public import PrimeBHT.Frozen.IsAdapted
public import PrimeBHT.Frozen.Pairing
public import PrimeBHT.Frozen.TriForm
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Basic.Real.Pointwise
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Dilation symmetry of the tri-tile form (blueprint C0 item 5)

`T_c h (x) = h (c x)` and `φ^c = c^{1/2} T_c φ` for a real `c > 0` (`scaleFun`, `scalePacket`) and, for
`c = 2^m`, `dilFun m`, `dilPacket m`.  We prove that the frozen `IsAdapted N I ω` is mapped to
`IsAdapted N (c⁻¹ I) (c ω)` (same exponent `N`, no constant), that the pairing scales by `c^{-1/2}`
and that the frozen form `triForm` scales by `c⁻¹` when the tile set is moved by the tile dilation
`dilTile` of `Grid.lean`.

Finally `M1Statement ε N C` is the body of the frozen `tri_restricted_eps` after `∃ N C, 0 < C ∧`,
`NormM1 ε N C` its restriction to `1/2 < |E_{σ2}| ≤ 1`, and `M1Statement_of_normM1` is the
normalization reduction (blueprint C11 (d)) with the same `N` and `C`.
-/

@[expose] public noncomputable section

open MeasureTheory
open PrimeBHT.Statements
open scoped ENNReal FourierTransform Pointwise

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.Tile

/-! ### The dilation operators -/

/-- `T_c h (x) = h (c x)`. -/
def scaleFun (c : ℝ) (h : ℝ → ℂ) : ℝ → ℂ := fun x => h (c * x)

/-- The normalized dilated packet `φ^c := c^{1/2} T_c φ`, i.e. `x ↦ c^{1/2} φ (c x)`. -/
def scalePacket (c : ℝ) (φ : ℝ → ℂ) : ℝ → ℂ := fun x => ((Real.sqrt c : ℝ) : ℂ) * φ (c * x)

/-- `T_λ` for `λ = 2^m`. -/
def dilFun (m : ℤ) (h : ℝ → ℂ) : ℝ → ℂ := scaleFun ((2 : ℝ) ^ m) h

/-- `φ^λ` for `λ = 2^m`. -/
def dilPacket (m : ℤ) (φ : ℝ → ℂ) : ℝ → ℂ := scalePacket ((2 : ℝ) ^ m) φ

/-! ### Dilates of sets: centre and measure -/

theorem image_mul_left_eq_preimage {c : ℝ} (hc : c ≠ 0) (S : Set ℝ) :
    (fun x : ℝ => c * x) '' S = (fun x : ℝ => c⁻¹ * x) ⁻¹' S := by
  have h := Set.image_eq_preimage_of_inverse (f := fun x : ℝ => c * x) (g := fun x : ℝ => c⁻¹ * x)
    (fun x => by simp [hc]) (fun x => by simp [hc])
  exact congrFun h S

theorem image_mul_left_eq_smul (c : ℝ) (S : Set ℝ) : (fun x : ℝ => c * x) '' S = c • S := by
  simpa only [smul_eq_mul] using Set.image_smul (a := c) (t := S)

/-- `c (S)` has centre `c · c(S)` (for `c ≥ 0`, any set). -/
theorem intervalCentre_image_mul_left {c : ℝ} (hc : 0 ≤ c) (S : Set ℝ) :
    intervalCentre ((fun x : ℝ => c * x) '' S) = c * intervalCentre S := by
  unfold intervalCentre
  rw [image_mul_left_eq_smul, Real.sInf_smul_of_nonneg hc, Real.sSup_smul_of_nonneg hc]
  simp only [smul_eq_mul]
  ring

theorem volume_image_mul_left {c : ℝ} (hc : 0 < c) (S : Set ℝ) :
    volume ((fun x : ℝ => c * x) '' S) = ENNReal.ofReal c * volume S := by
  rw [image_mul_left_eq_preimage hc.ne', Real.volume_preimage_mul_left (inv_ne_zero hc.ne'),
    inv_inv, abs_of_pos hc]

theorem toReal_volume_image_mul_left {c : ℝ} (hc : 0 < c) (S : Set ℝ) :
    (volume ((fun x : ℝ => c * x) '' S)).toReal = c * (volume S).toReal := by
  rw [volume_image_mul_left hc, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]

theorem volume_preimage_mul_left_of_pos {c : ℝ} (hc : 0 < c) (S : Set ℝ) :
    volume ((fun x : ℝ => c * x) ⁻¹' S) = ENNReal.ofReal c⁻¹ * volume S := by
  rw [Real.volume_preimage_mul_left hc.ne', abs_of_pos (inv_pos.2 hc)]

theorem toReal_volume_preimage_mul_left {c : ℝ} (hc : 0 < c) (S : Set ℝ) :
    (volume ((fun x : ℝ => c * x) ⁻¹' S)).toReal = c⁻¹ * (volume S).toReal := by
  rw [volume_preimage_mul_left_of_pos hc, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_pos.2 hc).le]

/-! ### Fourier transform and pairing -/

/-- `𝓕 (φ^c) ξ = c^{-1/2} 𝓕 φ (ξ / c)` in the form `√c · c⁻¹ · 𝓕 φ (c⁻¹ ξ)`. -/
theorem fourier_scalePacket {c : ℝ} (hc : 0 < c) (φ : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (scalePacket c φ) ξ = ((Real.sqrt c * c⁻¹ : ℝ) : ℂ) * 𝓕 φ (c⁻¹ * ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  have h1 : (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) • scalePacket c φ v) =
      fun v => (fun u : ℝ => ((Real.sqrt c : ℝ) : ℂ) *
        (Complex.exp (↑(-2 * Real.pi * u * (c⁻¹ * ξ)) * Complex.I) • φ u)) (c * v) := by
    funext v
    have e : (-2 * Real.pi * v * ξ : ℝ) = -2 * Real.pi * (c * v) * (c⁻¹ * ξ) := by
      field_simp
    simp only [scalePacket, smul_eq_mul]
    rw [e]
    ring
  rw [h1, Measure.integral_comp_mul_left (fun u : ℝ => ((Real.sqrt c : ℝ) : ℂ) *
    (Complex.exp (↑(-2 * Real.pi * u * (c⁻¹ * ξ)) * Complex.I) • φ u)) c, integral_const_mul,
    abs_of_pos (inv_pos.2 hc)]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- The pairing scales as `⟨T_c h, φ^c⟩ = c⁻¹ √c ⟨h, φ⟩ = c^{-1/2} ⟨h, φ⟩`. -/
theorem pairing_scale {c : ℝ} (hc : 0 < c) (h φ : ℝ → ℂ) :
    pairing (scaleFun c h) (scalePacket c φ) = ((c⁻¹ * Real.sqrt c : ℝ) : ℂ) * pairing h φ := by
  unfold pairing
  have h1 : (fun x : ℝ => scaleFun c h x * (starRingEnd ℂ) (scalePacket c φ x)) =
      fun x => (fun u : ℝ => ((Real.sqrt c : ℝ) : ℂ) * (h u * (starRingEnd ℂ) (φ u))) (c * x) := by
    funext x
    simp only [scaleFun, scalePacket, map_mul, Complex.conj_ofReal]
    ring
  rw [h1, Measure.integral_comp_mul_left (fun u : ℝ => ((Real.sqrt c : ℝ) : ℂ) *
    (h u * (starRingEnd ℂ) (φ u))) c, integral_const_mul, abs_of_pos (inv_pos.2 hc)]
  simp only [Complex.real_smul]
  push_cast
  ring

theorem inv_mul_sqrt_eq {c : ℝ} (hc : 0 < c) : c⁻¹ * Real.sqrt c = c ^ (-(1 : ℝ) / 2) := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have h1 : c ^ (-(1 : ℝ) / 2) = (Real.sqrt c)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hc.le]
    congr 1
    ring
  rw [h1]
  have h2 : c = Real.sqrt c * Real.sqrt c := (Real.mul_self_sqrt hc.le).symm
  field_simp
  nlinarith [h2]

/-- **Pairing identity** `⟨T_λ h, φ^λ⟩ = λ^{-1/2} ⟨h, φ⟩`. -/
theorem pairing_scale_rpow {c : ℝ} (hc : 0 < c) (h φ : ℝ → ℂ) :
    pairing (scaleFun c h) (scalePacket c φ) = ((c ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * pairing h φ := by
  rw [pairing_scale hc, inv_mul_sqrt_eq hc]

theorem norm_pairing_scale {c : ℝ} (hc : 0 < c) (h φ : ℝ → ℂ) :
    ‖pairing (scaleFun c h) (scalePacket c φ)‖ = c ^ (-(1 : ℝ) / 2) * ‖pairing h φ‖ := by
  rw [pairing_scale_rpow hc, norm_mul, Complex.norm_real, Real.norm_of_nonneg
    (Real.rpow_nonneg hc.le _)]

/-! ### Adaptedness under dilation -/

theorem rpow_inv_scale {c : ℝ} (hc : 0 < c) (n : ℕ) :
    (c⁻¹) ^ (-(n : ℝ) - 1 / 2) = Real.sqrt c * c ^ n := by
  rw [Real.inv_rpow hc.le, ← Real.rpow_neg hc.le, neg_sub_left, neg_neg, add_comm,
    Real.rpow_add hc, Real.rpow_natCast, Real.sqrt_eq_rpow]
  ring

theorem abs_sub_inv_mul_div {c m v : ℝ} (hc : 0 < c) (x : ℝ) :
    |x - c⁻¹ * m| / (c⁻¹ * v) = |c * x - m| / v := by
  have h1 : x - c⁻¹ * m = c⁻¹ * (c * x - m) := by field_simp
  rw [h1, abs_mul, abs_of_pos (inv_pos.2 hc)]
  exact mul_div_mul_left _ _ (inv_ne_zero hc.ne')

/-- The demodulated dilated packet is `c^{1/2}` times the dilation of the demodulated packet. -/
theorem demod_scalePacket (c cω : ℝ) (φ : ℝ → ℂ) :
    (fun y : ℝ => Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((c * cω : ℝ) : ℂ) * (y : ℂ))) *
        scalePacket c φ y) =
      fun y => ((Real.sqrt c : ℝ) : ℂ) *
        (fun z : ℝ => Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (cω : ℂ) * (z : ℂ))) * φ z)
          (c * y) := by
  funext y
  simp only [scalePacket]
  have e : -(2 * (Real.pi : ℂ) * Complex.I * ((c * cω : ℝ) : ℂ) * (y : ℂ)) =
      -(2 * (Real.pi : ℂ) * Complex.I * (cω : ℂ) * (((c * y : ℝ)) : ℂ)) := by
    push_cast; ring
  rw [e]
  ring

/-- **Adaptedness scaling.** If `φ` is adapted to `(I, ω)` with exponent `N` then `φ^c` is adapted
to `(c⁻¹ I, c ω)` with the same exponent `N` (no constant). -/
theorem isAdapted_scalePacket {N : ℕ} {I ω : Set ℝ} {φ : ℝ → ℂ} {c : ℝ} (hc : 0 < c)
    (h : IsAdapted N I ω φ) :
    IsAdapted N ((fun x : ℝ => c⁻¹ * x) '' I) ((fun x : ℝ => c * x) '' ω)
      (scalePacket c φ) := by
  obtain ⟨hφ1, hφint, hsupp, hbd⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold scalePacket
    exact contDiff_const.mul (hφ1.comp (contDiff_const.mul contDiff_id))
  · exact (hφint.comp_mul_left' hc.ne').const_mul _
  · intro ξ hξ
    rw [fourier_scalePacket hc]
    have h0 : 𝓕 φ (c⁻¹ * ξ) = 0 :=
      hsupp _ (fun hmem => hξ ⟨c⁻¹ * ξ, hmem, by field_simp⟩)
    rw [h0, mul_zero]
  · intro n hn x
    rw [intervalCentre_image_mul_left hc.le ω, demod_scalePacket,
      toReal_volume_image_mul_left (inv_pos.2 hc), intervalCentre_image_mul_left (inv_pos.2 hc).le I]
    set g : ℝ → ℂ := fun z : ℝ =>
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (intervalCentre ω : ℂ) * (z : ℂ))) * φ z with hg
    have hgC : ContDiff ℝ 1 g := by
      have : ContDiff ℝ 1 (fun z : ℝ =>
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (intervalCentre ω : ℂ) * (z : ℂ)))) := by
        apply Complex.contDiff_exp.comp
        exact (contDiff_const.mul Complex.ofRealCLM.contDiff).neg
      exact this.mul hφ1
    have hgn : ContDiff ℝ n g := hgC.of_le (by exact_mod_cast hn)
    have hder : iteratedDeriv n (fun y : ℝ => ((Real.sqrt c : ℝ) : ℂ) * g (c * y)) x =
        ((Real.sqrt c : ℝ) : ℂ) * (((c ^ n : ℝ) : ℂ) * iteratedDeriv n g (c * x)) := by
      have := iteratedDeriv_fun_const_smul_field (n := n) (x := x) (((Real.sqrt c : ℝ) : ℂ))
        (fun y : ℝ => g (c * y))
      simp only [smul_eq_mul] at this
      rw [this, iteratedDeriv_comp_const_smul hgn c]
      simp only [Complex.real_smul]
    rw [hder, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (pow_nonneg hc.le _),
      Real.mul_rpow (inv_pos.2 hc).le (by positivity), rpow_inv_scale hc n,
      abs_sub_inv_mul_div hc]
    have hb := hbd n hn (c * x)
    have hmul : 0 ≤ Real.sqrt c * c ^ n := by positivity
    calc Real.sqrt c * (c ^ n * ‖iteratedDeriv n g (c * x)‖)
        = (Real.sqrt c * c ^ n) * ‖iteratedDeriv n g (c * x)‖ := by ring
      _ ≤ (Real.sqrt c * c ^ n) * ((volume I).toReal ^ (-(n : ℝ) - 1 / 2) *
          (1 + |c * x - intervalCentre I| / (volume I).toReal) ^ (-(N : ℝ))) :=
        mul_le_mul_of_nonneg_left hb hmul
      _ = _ := by ring

/-! #### The case `λ = 2^m` -/

/-! ### The tile dilation: adaptedness and the form identity -/

/-- The dilated packet of a packet adapted to the tile `t` is adapted to the tile `dilTile k t`
(`I_{t'} = λ⁻¹ I_t`, `ω_{t',i} = λ ω_{t,i}`, `λ = 2^k`), with the same exponent. -/
theorem isAdapted_dilTile {N : ℕ} {a b : ℤ} {i : Fin 3} {t : ℤ × ℤ × ℤ} {φ : ℝ → ℂ} (k : ℤ)
    (h : IsAdapted N (timeInt t) (freqInt a b i t) φ) :
    IsAdapted N (timeInt (dilTile k t)) (freqInt a b i (dilTile k t)) (dilPacket k φ) := by
  have h' := isAdapted_scalePacket (c := (2 : ℝ) ^ k) (zpow_pos (by norm_num) _) h
  rw [timeInt_dilTile, freqInt_dilTile]
  simp only [← zpow_neg] at h'
  exact h'

theorem scale_arith {c : ℝ} (hc : 0 < c) (v Y : ℝ) (hv : 0 ≤ v) :
    (c⁻¹ * v) ^ (-(1 : ℝ) / 2) * ((c ^ (-(1 : ℝ) / 2)) ^ 3 * Y) = c⁻¹ * (v ^ (-(1 : ℝ) / 2) * Y) := by
  have hr : (c ^ (-(1 : ℝ) / 2)) ^ 2 = c⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    norm_num
    exact Real.rpow_neg_one c
  have hrpos : 0 < c ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hc _
  rw [Real.mul_rpow (inv_pos.2 hc).le hv, Real.inv_rpow hc.le, ← hr]
  field_simp

/-- **Form identity.** `Λ_{P'}(T_λ h) = λ⁻¹ Λ_P(h)` for `P' = dilTile k '' P`, `λ = 2^k`, and
packets `φ'_{t'} = (φ_t)^λ`. -/
theorem triForm_dilTile (k : ℤ) (P : Finset (ℤ × ℤ × ℤ)) (φ φ' : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ)
    (h : Fin 3 → ℝ → ℂ) (hφ : ∀ t ∈ P, ∀ i, φ' (dilTile k t) i = dilPacket k (φ t i)) :
    triForm (P.image (dilTile k)) φ' (fun i => dilFun k (h i)) = (2 : ℝ) ^ (-k) * triForm P φ h := by
  unfold triForm
  rw [Finset.sum_image (fun t _ t' _ e => dilTile_injective k e), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  have hc : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  simp only [hφ t ht, dilFun, dilPacket, norm_pairing_scale hc, toReal_volume_timeInt_dilTile,
    zpow_neg]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact scale_arith hc _ _ ENNReal.toReal_nonneg

/-- The explicit version: `φ' u i := (φ (dilTile (-k) u) i)^λ`. -/
theorem triForm_dilTile_explicit (k : ℤ) (P : Finset (ℤ × ℤ × ℤ))
    (φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ) (h : Fin 3 → ℝ → ℂ) :
    triForm (P.image (dilTile k)) (fun u i => dilPacket k (φ (dilTile (-k) u) i))
        (fun i => dilFun k (h i)) = (2 : ℝ) ^ (-k) * triForm P φ h :=
  triForm_dilTile k P φ _ h (fun t _ i => by simp only [dilTile_neg_dilTile])

/-! ### The normalization reduction (blueprint C11 (d)) -/

/-- The body of the frozen theorem `tri_restricted_eps` after `∃ N C, 0 < C ∧` (M1(ε) with the
constants `N`, `C`), copied from `PrimeBHT/Frozen/TriRestrictedEps.lean`. -/
def M1Statement (ε : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin 3)) (E : Fin 3 → Set ℝ), (∀ i, MeasurableSet (E i)) →
    (∀ i, 0 < volume (E i) ∧ volume (E i) < ⊤) →
    volume (E (σ 0)) ≤ volume (E (σ 1)) → volume (E (σ 1)) ≤ volume (E (σ 2)) →
    ∃ Et : Set ℝ, MeasurableSet Et ∧ Et ⊆ E (σ 2) ∧ volume (E (σ 2)) ≤ 2 * volume Et ∧
      ∀ (a b s' α : ℤ), TriValid a b s' α →
      ∀ (P : Finset (ℤ × ℤ × ℤ)), (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α →
        ∀ φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ,
          (∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) →
          ∀ h : Fin 3 → ℝ → ℂ, (∀ i, Measurable (h i)) →
            (∀ i, i ≠ σ 2 → ∀ x, ‖h i x‖ ≤ (E i).indicator (1 : ℝ → ℝ) x) →
            (∀ x, ‖h (σ 2) x‖ ≤ Et.indicator (1 : ℝ → ℝ) x) →
            triForm P φ h ≤ C * (volume (E (σ 0))).toReal ^ (1 - ε) *
              (volume (E (σ 1))).toReal ^ ((1 : ℝ) / 2) *
              (volume (E (σ 2))).toReal ^ (-(1 : ℝ) / 2 + ε)

/-- The normalized form of M1(ε) (blueprint C10, "Statement (normalized form of M1(ε))"): the
conclusion of `M1Statement ε N C` restricted to `σ`-ordered sets with `1/2 < |E_{σ2}| ≤ 1`.  The major
subset `Et` is chosen before the parameters `(a, b, s', α)`, the tile set, the packets and the test
functions. -/
def NormM1 (ε : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin 3)) (E : Fin 3 → Set ℝ), (∀ i, MeasurableSet (E i)) →
    (∀ i, 0 < volume (E i) ∧ volume (E i) < ⊤) →
    volume (E (σ 0)) ≤ volume (E (σ 1)) → volume (E (σ 1)) ≤ volume (E (σ 2)) →
    (1 : ℝ) / 2 < (volume (E (σ 2))).toReal → (volume (E (σ 2))).toReal ≤ 1 →
    ∃ Et : Set ℝ, MeasurableSet Et ∧ Et ⊆ E (σ 2) ∧ volume (E (σ 2)) ≤ 2 * volume Et ∧
      ∀ (a b s' α : ℤ), TriValid a b s' α →
      ∀ (P : Finset (ℤ × ℤ × ℤ)), (↑P : Set (ℤ × ℤ × ℤ)) ⊆ triIdx s' α →
        ∀ φ : ℤ × ℤ × ℤ → Fin 3 → ℝ → ℂ,
          (∀ t ∈ P, ∀ k, IsAdapted N (timeInt t) (freqInt a b k t) (φ t k)) →
          ∀ h : Fin 3 → ℝ → ℂ, (∀ i, Measurable (h i)) →
            (∀ i, i ≠ σ 2 → ∀ x, ‖h i x‖ ≤ (E i).indicator (1 : ℝ → ℝ) x) →
            (∀ x, ‖h (σ 2) x‖ ≤ Et.indicator (1 : ℝ → ℝ) x) →
            triForm P φ h ≤ C * (volume (E (σ 0))).toReal ^ (1 - ε) *
              (volume (E (σ 1))).toReal ^ ((1 : ℝ) / 2) *
              (volume (E (σ 2))).toReal ^ (-(1 : ℝ) / 2 + ε)

theorem indicator_preimage_mul_left (c : ℝ) (S : Set ℝ) (x : ℝ) :
    ((fun x : ℝ => c * x) ⁻¹' S).indicator (1 : ℝ → ℝ) x = S.indicator (1 : ℝ → ℝ) (c * x) := by
  by_cases hx : c * x ∈ S
  · rw [Set.indicator_of_mem (by exact hx), Set.indicator_of_mem hx]
    rfl
  · rw [Set.indicator_of_notMem (by exact hx), Set.indicator_of_notMem hx]

/-- The exponents `(1 - ε) + 1/2 + (-1/2 + ε) = 1` of the right-hand side scale the product of the
measures by `c⁻¹` when all three measures are multiplied by `c⁻¹`. -/
theorem rpow_triple_scale {c : ℝ} (hc : 0 < c) {x0 x1 x2 : ℝ} (h0 : 0 ≤ x0) (h1 : 0 ≤ x1)
    (h2 : 0 ≤ x2) (ε : ℝ) :
    (c⁻¹ * x0) ^ (1 - ε) * (c⁻¹ * x1) ^ ((1 : ℝ) / 2) * (c⁻¹ * x2) ^ (-(1 : ℝ) / 2 + ε) =
      c⁻¹ * (x0 ^ (1 - ε) * x1 ^ ((1 : ℝ) / 2) * x2 ^ (-(1 : ℝ) / 2 + ε)) := by
  have hci : 0 < c⁻¹ := inv_pos.2 hc
  rw [Real.mul_rpow hci.le h0, Real.mul_rpow hci.le h1, Real.mul_rpow hci.le h2]
  have e : (c⁻¹) ^ (1 - ε) * (c⁻¹) ^ ((1 : ℝ) / 2) * (c⁻¹) ^ (-(1 : ℝ) / 2 + ε) = c⁻¹ := by
    rw [← Real.rpow_add hci, ← Real.rpow_add hci]
    have e1 : (1 - ε) + (1 : ℝ) / 2 + (-(1 : ℝ) / 2 + ε) = 1 := by ring
    rw [e1, Real.rpow_one]
  calc _ = ((c⁻¹) ^ (1 - ε) * (c⁻¹) ^ ((1 : ℝ) / 2) * (c⁻¹) ^ (-(1 : ℝ) / 2 + ε)) *
        (x0 ^ (1 - ε) * x1 ^ ((1 : ℝ) / 2) * x2 ^ (-(1 : ℝ) / 2 + ε)) := by ring
    _ = _ := by rw [e]

/-- **The normalization reduction (blueprint C11 (d)).** M1(ε) for general finite positive measures
(the same `N` and `C`) follows from the normalized form `1/2 < |E_{σ2}| ≤ 1`, by dilation by
`λ = 2^k` with `2^{-k} |E_{σ2}| ∈ (1/2, 1]`. -/
theorem M1Statement_of_normM1 {ε : ℝ} {N : ℕ} {C : ℝ} (hN : NormM1 ε N C) :
    M1Statement ε N C := by
  intro σ E hmeas hpos h01 h12
  have hm2 : 0 < (volume (E (σ 2))).toReal :=
    ENNReal.toReal_pos (hpos _).1.ne' (hpos _).2.ne
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hm2 (one_lt_two : (1 : ℝ) < 2)
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = n + 1 := ⟨_, rfl⟩
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = (2 : ℝ) ^ k := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hc_def]; exact zpow_pos (by norm_num) _
  have hc2 : c = 2 * 2 ^ n := by
    rw [hc_def, hk, zpow_add_one₀ (by norm_num)]; ring
  have hc3 : c = (2 : ℝ) ^ (n + 1) := by rw [hc_def, hk]
  -- the dilated sets `E' i = λ⁻¹ E i`
  obtain ⟨E', hE'⟩ : ∃ E' : Fin 3 → Set ℝ, E' = fun i => (fun x : ℝ => c * x) ⁻¹' E i := ⟨_, rfl⟩
  have hvolE' : ∀ i, volume (E' i) = ENNReal.ofReal c⁻¹ * volume (E i) := fun i => by
    rw [hE']; exact volume_preimage_mul_left_of_pos hc _
  have htoE' : ∀ i, (volume (E' i)).toReal = c⁻¹ * (volume (E i)).toReal := fun i => by
    rw [hE']; exact toReal_volume_preimage_mul_left hc _
  have hofpos : 0 < ENNReal.ofReal c⁻¹ := ENNReal.ofReal_pos.2 (inv_pos.2 hc)
  have hoflt : ENNReal.ofReal c⁻¹ < ⊤ := ENNReal.ofReal_lt_top
  have hmeasE' : ∀ i, MeasurableSet (E' i) := fun i => by
    rw [hE']; exact (measurable_const_mul c) (hmeas i)
  have hposE' : ∀ i, 0 < volume (E' i) ∧ volume (E' i) < ⊤ := fun i => by
    rw [hvolE']
    exact ⟨ENNReal.mul_pos hofpos.ne' (hpos i).1.ne', ENNReal.mul_lt_top hoflt (hpos i).2⟩
  have h01' : volume (E' (σ 0)) ≤ volume (E' (σ 1)) := by
    rw [hvolE', hvolE']; exact mul_le_mul_right h01 _
  have h12' : volume (E' (σ 1)) ≤ volume (E' (σ 2)) := by
    rw [hvolE', hvolE']; exact mul_le_mul_right h12 _
  have hlow : (1 : ℝ) / 2 < (volume (E' (σ 2))).toReal := by
    rw [htoE', inv_mul_eq_div, lt_div_iff₀ hc]
    linarith
  have hup : (volume (E' (σ 2))).toReal ≤ 1 := by
    rw [htoE', inv_mul_eq_div, div_le_one hc, hc3]
    exact hn2
  obtain ⟨Et', hEt'm, hEt'sub, hEt'vol, hEt'⟩ := hN σ E' hmeasE' hposE' h01' h12' hlow hup
  refine ⟨(fun x : ℝ => c⁻¹ * x) ⁻¹' Et', (measurable_const_mul c⁻¹) hEt'm, ?_, ?_, ?_⟩
  · intro x hx
    have h1 := hEt'sub hx
    rw [hE'] at h1
    simpa only [Set.mem_preimage, mul_inv_cancel_left₀ hc.ne'] using h1
  · rw [volume_preimage_mul_left_of_pos (inv_pos.2 hc), inv_inv]
    have h2 := hEt'vol
    rw [hvolE'] at h2
    calc volume (E (σ 2)) = ENNReal.ofReal c * (ENNReal.ofReal c⁻¹ * volume (E (σ 2))) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal c * (2 * volume Et') := mul_le_mul_right h2 _
      _ = 2 * (ENNReal.ofReal c * volume Et') := by ring
  · intro a b s' α hv P hP φ hφ h hhm hh1 hh2
    have hv' := triValid_dilTile k hv
    have hP' : (↑(P.image (dilTile k)) : Set (ℤ × ℤ × ℤ)) ⊆ triIdx ((s' - k) % 10) α := by
      rw [Finset.coe_image, ← image_dilTile_triIdx]
      exact Set.image_mono hP
    have hφ' : ∀ u ∈ P.image (dilTile k), ∀ i,
        IsAdapted N (timeInt u) (freqInt a b i u)
          ((fun u i => dilPacket k (φ (dilTile (-k) u) i)) u i) := by
      intro u hu i
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
      simp only [dilTile_neg_dilTile]
      exact isAdapted_dilTile k (hφ t ht i)
    have hhm' : ∀ i, Measurable ((fun i => dilFun k (h i)) i) := fun i => by
      have e : (fun x : ℝ => dilFun k (h i) x) = fun x => h i (c * x) := by
        funext x; rw [hc_def]; rfl
      show Measurable (dilFun k (h i))
      rw [show dilFun k (h i) = fun x => h i (c * x) from e]
      exact (hhm i).comp (measurable_const_mul c)
    have hh1' : ∀ i, i ≠ σ 2 → ∀ x, ‖(fun i => dilFun k (h i)) i x‖ ≤
        (E' i).indicator (1 : ℝ → ℝ) x := by
      intro i hi x
      have e : (fun i => dilFun k (h i)) i x = h i (c * x) := by rw [hc_def]; rfl
      rw [e]
      refine (hh1 i hi (c * x)).trans (le_of_eq ?_)
      rw [hE']
      exact (indicator_preimage_mul_left c (E i) x).symm
    have hh2' : ∀ x, ‖(fun i => dilFun k (h i)) (σ 2) x‖ ≤ Et'.indicator (1 : ℝ → ℝ) x := by
      intro x
      have e : (fun i => dilFun k (h i)) (σ 2) x = h (σ 2) (c * x) := by rw [hc_def]; rfl
      rw [e]
      refine (hh2 (c * x)).trans (le_of_eq ?_)
      rw [indicator_preimage_mul_left, inv_mul_cancel_left₀ hc.ne']
    have key := hEt' a b ((s' - k) % 10) α hv' _ hP' _ hφ' _ hhm' hh1' hh2'
    have hform := triForm_dilTile_explicit k P φ h
    rw [htoE', htoE', htoE'] at key
    have e := rpow_triple_scale hc (ENNReal.toReal_nonneg (a := volume (E (σ 0))))
      (ENNReal.toReal_nonneg (a := volume (E (σ 1))))
      (ENNReal.toReal_nonneg (a := volume (E (σ 2)))) ε
    have hcinv : (2 : ℝ) ^ (-k) = c⁻¹ := by rw [hc_def, zpow_neg]
    rw [hform, hcinv] at key
    have key2 : c⁻¹ * triForm P φ h ≤ c⁻¹ * (C * ((volume (E (σ 0))).toReal ^ (1 - ε) *
        (volume (E (σ 1))).toReal ^ ((1 : ℝ) / 2) *
        (volume (E (σ 2))).toReal ^ (-(1 : ℝ) / 2 + ε))) := by
      refine key.trans (le_of_eq ?_)
      calc _ = C * ((c⁻¹ * (volume (E (σ 0))).toReal) ^ (1 - ε) *
            (c⁻¹ * (volume (E (σ 1))).toReal) ^ ((1 : ℝ) / 2) *
            (c⁻¹ * (volume (E (σ 2))).toReal) ^ (-(1 : ℝ) / 2 + ε)) := by ring
        _ = _ := by rw [e]; ring
    calc triForm P φ h ≤ C * ((volume (E (σ 0))).toReal ^ (1 - ε) *
        (volume (E (σ 1))).toReal ^ ((1 : ℝ) / 2) *
        (volume (E (σ 2))).toReal ^ (-(1 : ℝ) / 2 + ε)) :=
          le_of_mul_le_mul_left key2 (inv_pos.2 hc)
      _ = _ := by ring

/-- The existential form: `∃ N C, 0 < C ∧ NormM1 ε N C` gives the frozen conclusion
`∃ N C, 0 < C ∧ M1Statement ε N C` (the body of `tri_restricted_eps ε`). -/
theorem exists_m1Statement_of_exists_normM1 {ε : ℝ}
    (h : ∃ (N : ℕ) (C : ℝ), 0 < C ∧ NormM1 ε N C) :
    ∃ (N : ℕ) (C : ℝ), 0 < C ∧ M1Statement ε N C := by
  obtain ⟨N, C, hC, hN⟩ := h
  exact ⟨N, C, hC, M1Statement_of_normM1 hN⟩

end PrimeBHT.TimeFrequency.Tile
