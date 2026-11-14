module

public import PrimeBHT.TimeFrequency.X2.Psp.Overlap
public import PrimeBHT.TimeFrequency.X2.Psp.Bernstein
public import PrimeBHT.TimeFrequency.X2.Psp.Domination
public import PrimeBHT.TimeFrequency.X2.Psp.LacunaryLinf

/-!
# X2, V13 part 2 (B): estimate O-a (the pointwise bound of the low-pass `T_σ F` by `engTop`)

`docs/audits/X2-V13-route-check.md` §2.6 (O-a):

* `lowSym_inMult_c0`, `lowSym_inTopMult_c0`: the fixed constant `c₀ = lowC0 𝔭`: `c₀ · lowSym θ σ` is a multiplier of the class
  `{𝔭 with β := 17/2}` at `(σ, θ)` and, for the REV3 data, a top multiplier;
* `exists_fat_datum_topMult`: a fat grid datum `ξ'` (`isTopDatum_of_nonlacunary`) at which `c₀ · lowSym` is an `InTopMult`;
* `lowpass_sup_le`: `‖θ'_W(x)‖ ‖T_σ F(x)‖_{L^s(Y)} ≤ C engTop` for a lattice interval `W ⊇ I_R` (Bernstein + top energy);
* `overlap_Oa`: `‖T_σ F(x)‖_{L^s(Y)} ≤ C engTop` for every `x` in a `σ`-interval `I'` with `3I' ∩ Ẽ_σ ≠ ∅` (G-3 +
  lower bound of the cutoff).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform ContDiff Real
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-! ## The constant `c₀` -/

/-- A bound `Λ_D` of the derivatives of order `≤ D` of the fixed profile `lowProfile`. -/
def lowLam (D : ℕ) : ℝ := Classical.choose (exists_lowProfile_deriv_bound D)

theorem lowLam_spec (D : ℕ) : 0 ≤ lowLam D ∧ ∀ a ≤ D, ∀ u : ℝ,
    ‖iteratedDeriv a (fun u : ℝ => ((lowProfile u : ℝ) : ℂ)) u‖ ≤ lowLam D :=
  Classical.choose_spec (exists_lowProfile_deriv_bound D)

/-- `c₀ = 𝔭.C/(Λ_D + 1)`. -/
def lowC0 (𝔭 : Params) : ℝ := 𝔭.C / (lowLam 𝔭.D + 1)

theorem lowC0_pos {𝔭 : Params} (hC : 0 < 𝔭.C) : 0 < lowC0 𝔭 := by
  unfold lowC0
  have := (lowLam_spec 𝔭.D).1
  exact div_pos hC (by linarith)

theorem lowSym_deriv_c0 {𝔭 : Params} (hC : 0 < 𝔭.C) (θ : ℝ) (σ : ℤ) {a : ℕ} (ha : a ≤ 𝔭.D) (η : ℝ) :
    ((2 : ℝ) ^ (-σ)) ^ a * ‖iteratedDeriv a (fun η => (lowC0 𝔭 : ℂ) * lowSym θ σ η) η‖ ≤ 𝔭.C := by
  obtain ⟨hΛ0, hΛ⟩ := lowLam_spec 𝔭.D
  have hΛ1 : 0 < lowLam 𝔭.D + 1 := by linarith
  have hf : ContDiffAt ℝ (a : WithTop ℕ∞) (lowSym θ σ) η :=
    ((contDiff_lowSym θ σ).of_le (by exact_mod_cast le_top)).contDiffAt
  rw [iteratedDeriv_const_mul ((lowC0 𝔭 : ℝ) : ℂ) hf, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (lowC0_pos hC).le]
  have h4 := norm_iteratedDeriv_lowSym_le hΛ θ σ ha η
  have e : ((2 : ℝ) ^ (-σ)) ^ a * ((2 : ℝ) ^ σ) ^ a = 1 := by
    rw [← mul_pow, ← zpow_add₀ (by norm_num)]; simp
  unfold lowC0
  calc ((2 : ℝ) ^ (-σ)) ^ a * (𝔭.C / (lowLam 𝔭.D + 1) * ‖iteratedDeriv a (lowSym θ σ) η‖)
      ≤ ((2 : ℝ) ^ (-σ)) ^ a * (𝔭.C / (lowLam 𝔭.D + 1) * (((2 : ℝ) ^ σ) ^ a * lowLam 𝔭.D)) := by gcongr
    _ = (𝔭.C / (lowLam 𝔭.D + 1)) * lowLam 𝔭.D * (((2 : ℝ) ^ (-σ)) ^ a * ((2 : ℝ) ^ σ) ^ a) := by ring
    _ ≤ 𝔭.C := by
      rw [e, mul_one, div_mul_eq_mul_div, div_le_iff₀ hΛ1]
      nlinarith

/-- `c₀ lowSym θ σ ∈ M_{ω}({𝔭 with β := 17/2})` at the scale `σ`, centre `θ` (support radius `17/4 · 2^{-σ}`). -/
theorem lowSym_inMult_c0 {𝔭 : Params} (hC : 0 < 𝔭.C) (θ : ℝ) (σ : ℤ) :
    InMult { 𝔭 with β := 17 / 2 } σ θ (fun η => (lowC0 𝔭 : ℂ) * lowSym θ σ η) := by
  refine ⟨contDiff_const.mul (contDiff_lowSym θ σ), fun η hη => ?_, fun a ha η => ?_⟩
  · have : 17 / 4 * (2 : ℝ) ^ (-σ) ≤ |η - θ| := by
      have h : (17 / 2 : ℝ) * (2 : ℝ) ^ (-σ) / 2 < |η - θ| := hη
      linarith
    beta_reduce
    rw [lowSym_eq_zero this, mul_zero]
  · exact lowSym_deriv_c0 hC θ σ ha η

theorem lowSym_inTopMult_c0 {𝔭 : Params} (hC : 0 < 𝔭.C) (θ : ℝ) (W : ℤ × ℤ) (ξ' : ℝ) (k : Fin 3)
    (h1 : 9 / 2 * (2 : ℝ) ^ (-W.1) ≤ |ξ' * freqDir k - θ|) (h2 : |ξ' * freqDir k - θ| ≤ 31 / 4 * (2 : ℝ) ^ (-W.1)) :
    InTopMult 𝔭 W ξ' k (fun η => (lowC0 𝔭 : ℂ) * lowSym θ W.1 η) := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (-W.1) := zpow_pos (by norm_num) _
  refine ⟨(contDiff_const.mul (contDiff_lowSym θ W.1)), fun η hη => ?_, fun η hη => ?_, fun a ha η => ?_⟩
  · unfold topRad at hη
    beta_reduce
    rw [lowSym_eq_zero, mul_zero]
    have h3 : |η - θ| ≥ |η - ξ' * freqDir k| - |ξ' * freqDir k - θ| := by
      have := abs_sub_abs_le_abs_sub (η - ξ' * freqDir k) (-(ξ' * freqDir k - θ))
      rw [abs_neg] at this
      have e : η - ξ' * freqDir k - -(ξ' * freqDir k - θ) = η - θ := by ring
      rw [e] at this; exact this
    linarith
  · unfold topHole at hη
    beta_reduce
    rw [lowSym_eq_zero, mul_zero]
    have h3 : |η - θ| ≥ |ξ' * freqDir k - θ| - |η - ξ' * freqDir k| := by
      have := abs_sub_abs_le_abs_sub (ξ' * freqDir k - θ) (ξ' * freqDir k - η)
      have e : ξ' * freqDir k - θ - (ξ' * freqDir k - η) = η - θ := by ring
      rw [e, abs_sub_comm (ξ' * freqDir k) η] at this; exact this
    linarith
  · exact lowSym_deriv_c0 hC θ W.1 ha η

theorem fat_abs_bounds {A B a : ℝ} (ha : 0 < a) (h1 : |A - (B + 5 * 1 * a)| ≤ a / 8) :
    9 / 2 * a ≤ |A - B| ∧ |A - B| ≤ 31 / 4 * a := by
  rw [abs_le] at h1
  have h2 : 0 < A - B := by linarith [h1.1]
  rw [abs_of_pos h2]
  constructor <;> linarith [h1.1, h1.2]

/-- A fat grid datum at which `c₀ · lowSym(θ_k, W.1)` is a top multiplier (`ε = 1`: the datum `ξ' ≈ ξ_T + 5·2^{-W.1}/f_k`). -/
theorem exists_fat_datum_topMult {𝔭 : Params} (hC : 0 < 𝔭.C) {Cs : Finset TriTile} {R : TriTile} (hR : R ∈ Cs)
    {k : Fin 3} {t : Top} (hov : IsOvSlot t k R.box) {W : ℤ × ℤ} (hW : R.I ⊆ dyadicInt W.1 W.2)
    (hJ : (𝔭.J : ℤ) ∣ W.1 - R.box.scale) :
    ∃ ξ' : ℝ, IsTopDatum 𝔭.J Cs W ξ' ∧
      InTopMult 𝔭 W ξ' k (fun η => (lowC0 𝔭 : ℂ) * lowSym (t.2 * freqDir k) W.1 η) := by
  obtain ⟨ξ', h1, hd⟩ := exists_fat_grid_datum hR hov hW hJ 1 (by simp)
  have ha : (0 : ℝ) < (2 : ℝ) ^ (-W.1) := zpow_pos (by norm_num) _
  set a : ℝ := (2 : ℝ) ^ (-W.1) with hadef
  obtain ⟨hb1, hb2⟩ := fat_abs_bounds ha h1
  refine ⟨ξ', hd, lowSym_inTopMult_c0 hC (t.2 * freqDir k) W ξ' k hb1 hb2⟩

/-! ## The low-pass operator is bounded by `engTop` (pointwise, with the cutoff `θ'_W`) -/

/-- The constant of `lowpass_sup_le`. -/
def lowSupConst (𝔭 : Params) (q : ℝ) : ℝ :=
  (lowC0 𝔭)⁻¹ * (bernC2 * (2 / (2 * Real.conjExponent q - 1)) ^ (1 / Real.conjExponent q) *
    (17 / 2 + 2 * 𝔭.δ) ^ (1 / q))

/-- **O-a, single operator**: for a lattice interval `W ⊇ I_R` (`J ∣ W.1 - R.scale`, `R ∈ Cs` overlapping in slot `k`) and the cutoff
`θ'_W` of the profile `η'` of the class `𝔭`:
`‖θ'_W(x)‖ ‖T_{lowSym(θ_k, W.1)}F(x)‖_{L^s(Y)} ≤ C engTop 𝔭 s k F Cs q`.  (Bernstein `L^q → L^∞` for the band-limited piece
`θ'_W T_σ F`, whose Fourier support is `[θ_k ± (17/4 + δ) 2^{-W.1}]`, and the top-energy bound at the fat datum of
`exists_fat_datum_topMult`.) -/
theorem lowpass_sup_le {𝔭 : Params} (h𝔭 : 𝔭.Admissible) {η' : ℝ → ℝ} (hη' : IsEtaCut 𝔭 η')
    {P : ℕ} [NeZero P] {s q : ℝ} (hs : 1 ≤ s) (hq : 1 < q) {k : Fin 3} {F : ℝ → ZMod P → ℂ} (hF : Measurable F)
    (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) {Cs : Finset TriTile} {R : TriTile} (hR : R ∈ Cs) {t : Top}
    (hov : IsOvSlot t k R.box) {W : ℤ × ℤ} (hW : R.I ⊆ dyadicInt W.1 W.2) (hJ : (𝔭.J : ℤ) ∣ W.1 - R.box.scale)
    (x : ℝ) :
    ENNReal.ofReal (‖cutoffPsi 𝔭 η' W.1 W.2 x‖ * yNorm s (tmult (lowSym (t.2 * freqDir k) W.1) F x)) ≤
      ENNReal.ofReal (lowSupConst 𝔭 q) * engTop 𝔭 s k F Cs q := by
  obtain ⟨hN, hD, hβ, hC⟩ := h𝔭.bounds
  have hδ0 : 0 < 𝔭.δ := h𝔭.2.2.2.1
  have hCpos : 0 < 𝔭.C := by linarith
  obtain ⟨B, hB⟩ := hFb
  have hc₀ := lowC0_pos hCpos
  set c₀ : ℝ := lowC0 𝔭 with hc₀def
  set θk : ℝ := t.2 * freqDir k with hθk
  set ψ : ℝ → ℂ := cutoffPsi 𝔭 η' W.1 W.2 with hψdef
  have hψ : InPsi 𝔭 W.1 W.2 ψ := inPsi_cutoffPsi hη' hCpos (by omega) W.1 W.2
  set m : ℝ → ℂ := fun η => (c₀ : ℂ) * lowSym θk W.1 η with hmdef
  have hm'' : InMult { 𝔭 with β := 17 / 2 } W.1 θk m := lowSym_inMult_c0 hCpos θk W.1
  set w : ℝ := (17 / 2 / 2 + 𝔭.δ) * (2 : ℝ) ^ (-W.1) with hw
  have hw0 : 0 < w := by have := zpow_two_pos (-W.1); positivity
  set G : ℝ → ZMod P → ℂ := fun z => ψ z • tmult m F z with hG
  have hcoord : ∀ y : ZMod P, IsBandLimited (fun z => G z y) (Icc (θk - w) (θk + w)) := by
    intro y
    have hf : Measurable (fun z => F z y) := (measurable_pi_apply y).comp hF
    have hfB : ∀ z, ‖F z y‖ ≤ (P : ℝ) ^ (2 : ℝ)⁻¹ * B := fun z =>
      (norm_apply_le_rpow_mul_yNorm (by norm_num) (F z) y).trans
        (mul_le_mul_of_nonneg_left (hB z) (by positivity))
    exact isBandLimited_gfun (𝔭 := { 𝔭 with β := 17 / 2 }) (by show 2 ≤ 𝔭.N; omega) (by show 2 ≤ 𝔭.D; omega)
      (by show (0 : ℝ) ≤ 17 / 2; norm_num) hψ hm'' hf hfB
  have hmeasG : Measurable fun z => yNorm s (G z) :=
    (measurable_yNorm_fun s).comp (measurable_pi_iff.2 fun y => (hcoord y).continuous.measurable)
  set L' : ℝ := (2 * w)⁻¹ with hL'
  have hL'0 : 0 < L' := inv_pos.2 (by linarith)
  have hS : Icc (θk - w) (θk + w) ⊆ Icc (θk - 1 / (2 * L')) (θk + 1 / (2 * L')) := by
    have : 1 / (2 * L') = w := by rw [hL']; field_simp
    rw [this]
  have hb := bernstein_Lq_Linf hs hq hcoord hL'0 hS hmeasG x
  obtain ⟨ξ', hd, hmult⟩ := exists_fat_datum_topMult hCpos hR hov hW hJ
  have hE := topOp_le_engTop (s := s) (q := q) (k := k) (F := F) hd hψ hmult
  have ha : 0 < ((2 : ℝ) ^ W.1) ^ (-1 / q) := Real.rpow_pos_of_pos (zpow_two_pos W.1) _
  have hE2 : eLpNorm (fun z => yNorm s (G z)) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (((2 : ℝ) ^ W.1) ^ (1 / q)) * engTop 𝔭 s k F Cs q := by
    have e : ENNReal.ofReal (((2 : ℝ) ^ W.1) ^ (1 / q)) * ENNReal.ofReal (((2 : ℝ) ^ W.1) ^ (-1 / q)) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (zpow_two_pos W.1).le _), ← Real.rpow_add (zpow_two_pos W.1)]
      have : 1 / q + -1 / q = 0 := by ring
      rw [this, Real.rpow_zero, ENNReal.ofReal_one]
    calc eLpNorm (fun z => yNorm s (G z)) (ENNReal.ofReal q) volume
        = ENNReal.ofReal (((2 : ℝ) ^ W.1) ^ (1 / q)) * (ENNReal.ofReal (((2 : ℝ) ^ W.1) ^ (-1 / q)) *
            eLpNorm (fun z => yNorm s (G z)) (ENNReal.ofReal q) volume) := by
          rw [← mul_assoc, e, one_mul]
      _ ≤ _ := mul_le_mul' le_rfl hE
  -- the pointwise relation between `G` and `T_σ`
  have hnorm : ‖ψ x‖ * yNorm s (tmult (lowSym θk W.1) F x) = c₀⁻¹ * yNorm s (G x) := by
    have e1 : tmult m F x = (c₀ : ℂ) • tmult (lowSym θk W.1) F x := tmult_const_mul _ _ _ _
    have e2 : G x = ((c₀ : ℝ) : ℂ) • (ψ x • tmult (lowSym θk W.1) F x) := by
      show ψ x • tmult m F x = _
      rw [e1]; exact smul_comm _ _ _
    have e3 : yNorm s (G x) = c₀ * (‖ψ x‖ * yNorm s (tmult (lowSym θk W.1) F x)) := by
      have hs0 : 0 < s := by linarith
      have h1 : yNorm s (((c₀ : ℝ) : ℂ) • (ψ x • tmult (lowSym θk W.1) F x)) =
          ‖((c₀ : ℝ) : ℂ)‖ * yNorm s (ψ x • tmult (lowSym θk W.1) F x) := yNorm_fun_const_mul hs0 _ _
      have h2 : yNorm s (ψ x • tmult (lowSym θk W.1) F x) = ‖ψ x‖ * yNorm s (tmult (lowSym θk W.1) F x) :=
        yNorm_fun_const_mul hs0 _ _
      rw [e2, h1, h2, Complex.norm_real, Real.norm_of_nonneg hc₀.le]
    rw [e3]; field_simp
  rw [hnorm, ENNReal.ofReal_mul (inv_pos.2 hc₀).le]
  have hCq : 0 ≤ bernC2 * (2 / (2 * Real.conjExponent q - 1)) ^ (1 / Real.conjExponent q) *
      L' ^ (-(1 / q)) := by
    have hq' : 1 < Real.conjExponent q := (Real.HolderConjugate.conjExponent hq).symm.lt
    have : 0 < 2 * Real.conjExponent q - 1 := by linarith
    have := bernC2_pos
    have := Real.rpow_pos_of_pos hL'0 (-(1 / q))
    positivity
  have hconst : bernC2 * (2 / (2 * Real.conjExponent q - 1)) ^ (1 / Real.conjExponent q) * L' ^ (-(1 / q)) *
      ((2 : ℝ) ^ W.1) ^ (1 / q) =
      bernC2 * (2 / (2 * Real.conjExponent q - 1)) ^ (1 / Real.conjExponent q) * (17 / 2 + 2 * 𝔭.δ) ^ (1 / q) := by
    have h2w : 2 * w = (17 / 2 + 2 * 𝔭.δ) * (2 : ℝ) ^ (-W.1) := by rw [hw]; ring
    have e1 : L' ^ (-(1 / q)) = (2 * w) ^ (1 / q) := by
      rw [hL', Real.rpow_neg (inv_pos.2 (by linarith)).le, Real.inv_rpow (by linarith), inv_inv]
    have hbd : 0 < 17 / 2 + 2 * 𝔭.δ := by linarith
    have e2 : (2 * w) ^ (1 / q) * ((2 : ℝ) ^ W.1) ^ (1 / q) = (17 / 2 + 2 * 𝔭.δ) ^ (1 / q) := by
      rw [h2w, Real.mul_rpow hbd.le (zpow_two_pos _).le, mul_assoc,
        ← Real.mul_rpow (zpow_two_pos _).le (zpow_two_pos _).le, ← zpow_add₀ (by norm_num)]
      simp
    rw [e1, mul_assoc, e2]
  calc ENNReal.ofReal c₀⁻¹ * ENNReal.ofReal (yNorm s (G x))
      ≤ ENNReal.ofReal c₀⁻¹ * (ENNReal.ofReal (bernC2 * (2 / (2 * Real.conjExponent q - 1)) ^
          (1 / Real.conjExponent q) * L' ^ (-(1 / q))) *
        eLpNorm (fun z => yNorm s (G z)) (ENNReal.ofReal q) volume) := mul_le_mul' le_rfl hb
    _ ≤ ENNReal.ofReal c₀⁻¹ * (ENNReal.ofReal (bernC2 * (2 / (2 * Real.conjExponent q - 1)) ^
          (1 / Real.conjExponent q) * L' ^ (-(1 / q))) *
        (ENNReal.ofReal (((2 : ℝ) ^ W.1) ^ (1 / q)) * engTop 𝔭 s k F Cs q)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hE2)
    _ = ENNReal.ofReal (lowSupConst 𝔭 q) * engTop 𝔭 s k F Cs q := by
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.2 hc₀).le,
          ← ENNReal.ofReal_mul (mul_nonneg (inv_pos.2 hc₀).le hCq), mul_assoc (c₀⁻¹), hconst]
        rfl

/-! ## O-a -/

/-- The lower bound of `‖θ'_W(x)‖` for `x` within `3·2^σ` of the centre of `W` (`⟨·⟩ ≤ 4`). -/
def oaLower (𝔭 : Params) : ℝ := cutScale 𝔭 * (cutK 𝔭)⁻¹ * (4 : ℝ) ^ (-(𝔭.N : ℝ))

theorem oaLower_pos {𝔭 : Params} (hC : 0 < 𝔭.C) : 0 < oaLower 𝔭 := by
  have := cutScale_pos 𝔭
  have := cutK_pos hC
  unfold oaLower
  positivity

theorem le_norm_cutoffPsi {𝔭 : Params} {η : ℝ → ℝ} (hη : IsEtaCut 𝔭 η) (hC : 0 < 𝔭.C) {σ v : ℤ} {x : ℝ}
    (hx : |x - dyCentre σ v| ≤ 3 * (2 : ℝ) ^ σ) : oaLower 𝔭 ≤ ‖cutoffPsi 𝔭 η σ v x‖ := by
  have hp := zpow_two_pos σ
  unfold cutoffPsi
  rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (cutScale_pos 𝔭).le (tileCutoff_nonneg hη σ v x))]
  have h1 := le_tileCutoff hη hC σ v x
  have hjb : jb ((x - dyCentre σ v) / (2 : ℝ) ^ σ) ≤ 4 := by
    unfold jb
    have : |(x - dyCentre σ v) / (2 : ℝ) ^ σ| ≤ 3 := by
      rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]; exact hx
    linarith
  have h2 : (4 : ℝ) ^ (-(𝔭.N : ℝ)) ≤ jb ((x - dyCentre σ v) / (2 : ℝ) ^ σ) ^ (-(𝔭.N : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (jb_pos _) hjb (by simp)
  unfold oaLower
  calc cutScale 𝔭 * (cutK 𝔭)⁻¹ * (4 : ℝ) ^ (-(𝔭.N : ℝ))
      = cutScale 𝔭 * ((cutK 𝔭)⁻¹ * (4 : ℝ) ^ (-(𝔭.N : ℝ))) := by ring
    _ ≤ cutScale 𝔭 * ((cutK 𝔭)⁻¹ * jb ((x - dyCentre σ v) / (2 : ℝ) ^ σ) ^ (-(𝔭.N : ℝ))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (inv_pos.2 (cutK_pos hC)).le) (cutScale_pos 𝔭).le
    _ ≤ cutScale 𝔭 * tileCutoff η σ v x := mul_le_mul_of_nonneg_left h1 (cutScale_pos 𝔭).le

/-- The constant of O-a. -/
def oaConst (𝔭 : Params) (q : ℝ) : ℝ := (oaLower 𝔭)⁻¹ * lowSupConst 𝔭 q

/-- **O-a (MTT2 `gen-infty`, with the fat top term)**: for a `σ`-interval `I' ∋ x` with `3I' ∩ Ẽ_σ ≠ ∅` (`σ` on the lattice of the tile
scales, `J ≥ 2`, all slots of `TA` overlapping at the top `t`), `‖T_σ F(x)‖_{L^s(Y)} ≤ C · engTop 𝔭 s k F Cs q`,
`T_σ = tmult (lowSym (ξ_T f_k) σ)`.  The top operator used is at a lattice interval `W = (σ, v) ⊇ I_R` of the tile `R` of
G-3 (`σ = R.scale` allowed), with a FAT grid datum `ξ' ≈ ξ_T + 5·2^{-σ}/f_k` (`isTopDatum_of_nonlacunary`). -/
theorem overlap_Oa {𝔭 : Params} (h𝔭 : 𝔭.Admissible) (hJ2 : 2 ≤ 𝔭.J) {η' : ℝ → ℝ} (hη' : IsEtaCut 𝔭 η')
    {P : ℕ} [NeZero P] {s q : ℝ} (hs : 1 ≤ s) (hq : 1 < q) {k : Fin 3} {F : ℝ → ZMod P → ℂ} (hF : Measurable F)
    (hFb : ∃ B, ∀ x, yNorm 2 (F x) ≤ B) {TA Cs : Finset TriTile} (hsub : TA ⊆ Cs) {t : Top}
    (hov : ∀ R ∈ TA, IsOvSlot t k R.box) {σ u : ℤ} (hlat : ∀ R ∈ TA, (𝔭.J : ℤ) ∣ R.box.scale - σ)
    (h : (dilate 3 (dyadicInt σ u) ∩ eTil TA t.1 σ).Nonempty) {x : ℝ} (hx : x ∈ dyadicInt σ u) :
    ENNReal.ofReal (yNorm s (tmult (lowSym (t.2 * freqDir k) σ) F x)) ≤
      ENNReal.ofReal (oaConst 𝔭 q) * engTop 𝔭 s k F Cs q := by
  obtain ⟨hN, hD, hβ, hC⟩ := h𝔭.bounds
  have hCpos : 0 < 𝔭.C := by linarith
  obtain ⟨R, hR, hRs, v, hRv, hRJ, hv5⟩ := exists_lattice_key_near hJ2 hlat h
  have hp := zpow_two_pos σ
  -- the key `(σ, v)` is within `5 I'`, so `|x - c_W| ≤ 3 · 2^σ`
  have hdist : |x - dyCentre σ v| ≤ 3 * (2 : ℝ) ^ σ := by
    have hlt : (2 : ℝ) ^ σ * v < (2 : ℝ) ^ σ * ((v : ℝ) + 1) := by nlinarith
    have hsub5 := hv5
    rw [dilate_dyadicInt, dyadicInt_eq_Ico] at hsub5
    obtain ⟨h1, h2⟩ := (Set.Ico_subset_Ico_iff hlt).1 hsub5
    obtain ⟨hx1, hx2⟩ := hx
    unfold dyCentre
    rw [abs_le]
    constructor <;> nlinarith
  have hlow := le_norm_cutoffPsi hη' hCpos hdist
  have hmain := lowpass_sup_le h𝔭 hη' hs hq hF hFb (Cs := Cs) (R := R) (hsub hR) (hov R hR) (W := (σ, v)) hRv
    (by simpa using hRJ) x
  have hy0 : 0 ≤ yNorm s (tmult (lowSym (t.2 * freqDir k) σ) F x) := yNorm_nonneg' s _
  have hlp := oaLower_pos hCpos
  have hle : yNorm s (tmult (lowSym (t.2 * freqDir k) σ) F x) ≤
      (oaLower 𝔭)⁻¹ * (‖cutoffPsi 𝔭 η' σ v x‖ * yNorm s (tmult (lowSym (t.2 * freqDir k) σ) F x)) := by
    rw [← mul_assoc]
    have : 1 ≤ (oaLower 𝔭)⁻¹ * ‖cutoffPsi 𝔭 η' σ v x‖ := by
      rw [inv_mul_eq_div, le_div_iff₀ hlp]; linarith
    nlinarith
  calc ENNReal.ofReal (yNorm s (tmult (lowSym (t.2 * freqDir k) σ) F x))
      ≤ ENNReal.ofReal ((oaLower 𝔭)⁻¹ * (‖cutoffPsi 𝔭 η' σ v x‖ *
          yNorm s (tmult (lowSym (t.2 * freqDir k) σ) F x))) := ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal (oaLower 𝔭)⁻¹ * ENNReal.ofReal (‖cutoffPsi 𝔭 η' σ v x‖ *
          yNorm s (tmult (lowSym (t.2 * freqDir k) σ) F x)) := ENNReal.ofReal_mul (inv_pos.2 hlp).le
    _ ≤ ENNReal.ofReal (oaLower 𝔭)⁻¹ * (ENNReal.ofReal (lowSupConst 𝔭 q) * engTop 𝔭 s k F Cs q) :=
        mul_le_mul' le_rfl hmain
    _ = ENNReal.ofReal (oaConst 𝔭 q) * engTop 𝔭 s k F Cs q := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.2 hlp).le]; rfl

end PrimeBHT.TimeFrequency.X2
