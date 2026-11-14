module

public import PrimeBHT.TimeFrequency.X2.Disc.Select
public import PrimeBHT.TimeFrequency.X2.Disc.WhitneyCutoff
public import PrimeBHT.TimeFrequency.X2.Classes

/-!
# X2, node V05-5b (R3): the model multipliers `InMult`

* `wphi3`: the slot-3 bump, `= 1` on `[-1, 3]`, supported in `(-3/2, 7/2)`.
* `bumpPhase_deriv_bound`: for a smooth compactly supported `ψ` and `D` there is `M` with
  `(4b)^j ‖(ξ ↦ ψ(ξ/b - n) e^{2π i γ ξ})^{(j)}‖ ≤ M (4 (1 + 2π|γ| b))^D` for all `b > 0`, `n, γ`, `j ≤ D`.
* `inMult_bumpPhase`: `λ ψ(ξ/b - n) e^{2πiγξ} ∈ M_{ω}(𝔭)` when the support of the bump lies in the `β`-dilate
  (`β = 11/4`) and `‖λ‖ M (4(1+2π|γ|b))^D ≤ 𝔭.C`.
-/

@[expose] public noncomputable section

open Set Complex
open scoped ContDiff Real

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Disc

/-! ### The slot-3 bump -/

/-- `φ₃ = 1` on `[-1, 3]`, support in `(-3/2, 7/2)`. -/
def wphi3 (x : ℝ) : ℝ := stepG (2 * x + 5 / 2) * stepG (13 / 2 - 2 * x)

theorem contDiff_wphi3 : ContDiff ℝ ∞ wphi3 := by
  unfold wphi3 stepG
  have h := Real.smoothTransition.contDiff (n := ⊤)
  have h1 : ContDiff ℝ ∞ fun x : ℝ => Real.smoothTransition (2 * x + 5 / 2 + 1 / 2) :=
    h.comp (by fun_prop)
  have h2 : ContDiff ℝ ∞ fun x : ℝ => Real.smoothTransition (13 / 2 - 2 * x + 1 / 2) :=
    h.comp (by fun_prop)
  exact h1.mul h2

theorem wphi3_eq_one {x : ℝ} (h1 : -1 ≤ x) (h2 : x ≤ 3) : wphi3 x = 1 := by
  unfold wphi3
  rw [stepG_eq_one (by linarith), stepG_eq_one (by linarith)]; norm_num

theorem wphi3_ne_zero {x : ℝ} (h : wphi3 x ≠ 0) : -3 / 2 < x ∧ x < 7 / 2 := by
  by_contra hc
  apply h
  unfold wphi3
  by_cases h1 : x ≤ -3 / 2
  · rw [stepG_eq_zero (by linarith)]; ring
  · have h2 : 7 / 2 ≤ x := by by_contra h2; exact hc ⟨by linarith, by linarith⟩
    rw [stepG_eq_zero (by linarith : 13 / 2 - 2 * x ≤ -1 / 2)]; ring

theorem hasCompactSupport_wphi : HasCompactSupport wphi :=
  HasCompactSupport.intro (isCompact_Icc (a := (-1 / 2 : ℝ)) (b := 3 / 2)) fun x hx => by
    by_contra h
    exact hx ⟨(wphi_ne_zero h).1.le, (wphi_ne_zero h).2.le⟩

theorem hasCompactSupport_wphi3 : HasCompactSupport wphi3 :=
  HasCompactSupport.intro (isCompact_Icc (a := (-3 / 2 : ℝ)) (b := 7 / 2)) fun x hx => by
    by_contra h
    exact hx ⟨(wphi3_ne_zero h).1.le, (wphi3_ne_zero h).2.le⟩

/-! ### Derivative bounds -/

theorem iteratedDeriv_cexp_real (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun ξ : ℝ => Complex.exp (c * ξ)) = fun ξ : ℝ => c ^ n * Complex.exp (c * ξ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext ξ
    have h : HasDerivAt (fun ξ : ℝ => c ^ n * Complex.exp (c * ξ)) (c ^ n * (Complex.exp (c * ξ) * c)) ξ := by
      have h0 := (((hasDerivAt_id ξ).ofReal_comp.const_mul c).cexp).const_mul (c ^ n)
      simpa using h0
    rw [h.deriv]
    ring

theorem exists_bound_iteratedDeriv_ofReal {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (D : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ i ≤ D, ∀ x : ℝ, ‖iteratedDeriv i (fun x : ℝ => (ψ x : ℂ)) x‖ ≤ R := by
  have hc' : HasCompactSupport (fun x : ℝ => (ψ x : ℂ)) := hc.comp_left Complex.ofReal_zero
  have hs : ContDiff ℝ ∞ (fun x : ℝ => (ψ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hψ
  obtain ⟨C, hC0, hC⟩ := hc'.exists_bound_iteratedFDeriv hs D
  exact ⟨C, hC0, fun i hi x => by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact hC i hi x⟩

/-- Derivative bound for `ξ ↦ ψ(ξ/b - n) e^{2π i γ ξ}`. -/
theorem bumpPhase_deriv_bound {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (D : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (b : ℝ), 0 < b → ∀ (n γ : ℝ) (j : ℕ), j ≤ D → ∀ ξ : ℝ,
      (4 * b) ^ j * ‖iteratedDeriv j (fun ξ : ℝ => (ψ (ξ / b - n) : ℂ) *
          Complex.exp (((2 * π * γ : ℝ) : ℂ) * Complex.I * ξ)) ξ‖ ≤ M * (4 * (1 + 2 * π * |γ| * b)) ^ D := by
  obtain ⟨R, hR0, hR⟩ := exists_bound_iteratedDeriv_ofReal hψ hc D
  refine ⟨R, hR0, fun b hb n γ j hj ξ => ?_⟩
  set Ψ : ℝ → ℂ := fun x => (ψ x : ℂ) with hΨ
  have hΨs : ContDiff ℝ ∞ Ψ := Complex.ofRealCLM.contDiff.comp hψ
  set c : ℂ := ((2 * π * γ : ℝ) : ℂ) * Complex.I with hcdef
  have hu : ContDiff ℝ ∞ (fun ξ : ℝ => Ψ (ξ / b - n)) := by
    apply hΨs.comp
    exact (contDiff_id.div_const b).sub contDiff_const
  have hv : ContDiff ℝ ∞ (fun ξ : ℝ => Complex.exp (c * ξ)) := by
    apply Complex.contDiff_exp.comp
    exact contDiff_const.mul Complex.ofRealCLM.contDiff
  have hleib := iteratedDeriv_mul (n := j) (x := ξ) (f := fun ξ : ℝ => Ψ (ξ / b - n))
    (g := fun ξ : ℝ => Complex.exp (c * ξ))
    (hu.contDiffAt.of_le (by exact_mod_cast le_top)) (hv.contDiffAt.of_le (by exact_mod_cast le_top))
  have e : (fun ξ : ℝ => (ψ (ξ / b - n) : ℂ) * Complex.exp (((2 * π * γ : ℝ) : ℂ) * Complex.I * ξ)) =
      (fun ξ : ℝ => Ψ (ξ / b - n)) * (fun ξ : ℝ => Complex.exp (c * ξ)) := by
    funext ξ; simp only [Pi.mul_apply, hΨ, hcdef]
  rw [e, hleib]
  have hdu : ∀ i : ℕ, ∀ ξ : ℝ, iteratedDeriv i (fun ξ : ℝ => Ψ (ξ / b - n)) ξ =
      (b⁻¹) ^ i • iteratedDeriv i Ψ (ξ / b - n) := by
    intro i ξ
    have h1 : (fun ξ : ℝ => Ψ (ξ / b - n)) = fun ξ => (fun x => Ψ (x - n)) (b⁻¹ * ξ) := by
      funext ξ; simp [div_eq_inv_mul]
    have hf : ContDiff ℝ i (fun x : ℝ => Ψ (x - n)) :=
      (hΨs.comp (contDiff_id.sub contDiff_const)).of_le (by exact_mod_cast le_top)
    rw [h1, iteratedDeriv_comp_const_smul hf b⁻¹, iteratedDeriv_comp_sub_const]
    simp [div_eq_inv_mul]
  have hdv : ∀ i : ℕ, ∀ ξ : ℝ, ‖iteratedDeriv i (fun ξ : ℝ => Complex.exp (c * ξ)) ξ‖ ≤ (2 * π * |γ|) ^ i := by
    intro i ξ
    rw [iteratedDeriv_cexp_real]
    simp only [norm_mul, norm_pow]
    have : ‖Complex.exp (c * ξ)‖ = 1 := by
      rw [Complex.norm_exp]
      simp [hcdef, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [this, mul_one]
    have : ‖c‖ = 2 * π * |γ| := by
      rw [hcdef, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
        abs_mul, abs_mul, abs_of_pos Real.pi_pos]
      norm_num
    rw [this]
  set x : ℝ := 2 * π * |γ| * b with hx
  have hx0 : 0 ≤ x := by positivity
  have hterm : ∀ i ∈ Finset.range (j + 1),
      (4 * b) ^ j * ‖(j.choose i : ℂ) * iteratedDeriv i (fun ξ : ℝ => Ψ (ξ / b - n)) ξ *
          iteratedDeriv (j - i) (fun ξ : ℝ => Complex.exp (c * ξ)) ξ‖ ≤
        4 ^ j * R * ((j.choose i : ℝ) * x ^ (j - i)) := by
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [norm_mul, norm_mul, Complex.norm_natCast, hdu, norm_smul, norm_pow, norm_inv, Real.norm_eq_abs,
      abs_of_pos hb]
    have h1 := hR i (hij.trans hj) (ξ / b - n)
    have h2 := hdv (j - i) ξ
    have hb' : (b⁻¹) ^ i * b ^ j = b ^ (j - i) := by
      have : b ^ j = b ^ i * b ^ (j - i) := by rw [← pow_add]; congr 1; omega
      rw [this, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hb.ne', one_pow, one_mul]
    have hxe : x ^ (j - i) = (2 * π * |γ|) ^ (j - i) * b ^ (j - i) := by rw [hx, mul_pow]
    set A := ‖iteratedDeriv i Ψ (ξ / b - n)‖ with hA
    set B := ‖iteratedDeriv (j - i) (fun ξ : ℝ => Complex.exp (c * ξ)) ξ‖ with hB
    have hA0 : 0 ≤ A := norm_nonneg _
    have hB0 : 0 ≤ B := norm_nonneg _
    have e1 : (4 * b) ^ j * ((j.choose i : ℝ) * ((b⁻¹) ^ i * A) * B) =
        4 ^ j * b ^ (j - i) * ((j.choose i : ℝ) * A * B) := by
      rw [mul_pow, ← hb']; ring
    rw [e1]
    have hch : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
    have hg : 0 ≤ (2 * π * |γ|) ^ (j - i) := by positivity
    calc 4 ^ j * b ^ (j - i) * ((j.choose i : ℝ) * A * B)
        ≤ 4 ^ j * b ^ (j - i) * ((j.choose i : ℝ) * R * (2 * π * |γ|) ^ (j - i)) := by
          have : (j.choose i : ℝ) * A * B ≤ (j.choose i : ℝ) * R * (2 * π * |γ|) ^ (j - i) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 hch) h2 hB0 (mul_nonneg hch hR0)
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = 4 ^ j * R * ((j.choose i : ℝ) * x ^ (j - i)) := by rw [hxe]; ring
  calc (4 * b) ^ j * ‖∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * iteratedDeriv i (fun ξ : ℝ => Ψ (ξ / b - n)) ξ *
          iteratedDeriv (j - i) (fun ξ : ℝ => Complex.exp (c * ξ)) ξ‖
      ≤ (4 * b) ^ j * ∑ i ∈ Finset.range (j + 1), ‖(j.choose i : ℂ) * iteratedDeriv i (fun ξ : ℝ => Ψ (ξ / b - n)) ξ *
          iteratedDeriv (j - i) (fun ξ : ℝ => Complex.exp (c * ξ)) ξ‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ i ∈ Finset.range (j + 1), (4 * b) ^ j * ‖(j.choose i : ℂ) * iteratedDeriv i (fun ξ : ℝ => Ψ (ξ / b - n)) ξ *
          iteratedDeriv (j - i) (fun ξ : ℝ => Complex.exp (c * ξ)) ξ‖ := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (j + 1), 4 ^ j * R * ((j.choose i : ℝ) * x ^ (j - i)) := Finset.sum_le_sum hterm
    _ = 4 ^ j * R * (1 + x) ^ j := by
        rw [← Finset.mul_sum, add_pow]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [mul_comm]
    _ ≤ R * (4 * (1 + x)) ^ D := by
        have h1 : (1 : ℝ) ≤ 4 * (1 + x) := by linarith
        calc 4 ^ j * R * (1 + x) ^ j = R * (4 * (1 + x)) ^ j := by rw [mul_pow]; ring
          _ ≤ R * (4 * (1 + x)) ^ D := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hj) hR0

/-- **R3.** A bump times a phase, with amplitude `λ`, is in `M_ω(𝔭)` (for `β = 11/4`) when the support of the bump
lies within `(11/8) ℓ` of the centre `c` and `‖λ‖ M (4(1 + 2π|γ|b))^D ≤ 𝔭.C`
(`ℓ = 2^{-s}`, `b = ℓ/4`, `M = M(ψ, D)` from `bumpPhase_deriv_bound`). -/
theorem inMult_bumpPhase {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (lo hi : ℝ)
    (hsupp : ∀ x, ψ x ≠ 0 → lo < x ∧ x < hi) (𝔭 : Params) (hβ : 𝔭.β = 11 / 4) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (s : ℤ) (c n γ : ℝ) (lam : ℂ),
      c - 11 * ell s / 8 ≤ ell s / 4 * (n + lo) → ell s / 4 * (n + hi) ≤ c + 11 * ell s / 8 →
      ‖lam‖ * (M * (4 * (1 + 2 * π * |γ| * (ell s / 4))) ^ 𝔭.D) ≤ 𝔭.C →
      InMult 𝔭 s c (fun ξ : ℝ => lam * (ψ (ξ / (ell s / 4) - n) : ℂ) *
        Complex.exp (((2 * π * γ : ℝ) : ℂ) * Complex.I * ξ)) := by
  obtain ⟨M, hM0, hM⟩ := bumpPhase_deriv_bound hψ hc 𝔭.D
  refine ⟨M, hM0, fun s c n γ lam hlo hhi hC => ?_⟩
  have hℓ := ell_pos s
  set b : ℝ := ell s / 4 with hb
  have hb0 : 0 < b := by positivity
  set u : ℝ → ℂ := fun ξ => (ψ (ξ / b - n) : ℂ) with hu
  set v : ℝ → ℂ := fun ξ => Complex.exp (((2 * π * γ : ℝ) : ℂ) * Complex.I * ξ) with hv
  have hud : ContDiff ℝ ∞ u := by
    apply Complex.ofRealCLM.contDiff.comp
    exact hψ.comp ((contDiff_id.div_const b).sub contDiff_const)
  have hvd : ContDiff ℝ ∞ v := by
    apply Complex.contDiff_exp.comp
    exact contDiff_const.mul Complex.ofRealCLM.contDiff
  have hfun : (fun ξ : ℝ => lam * (ψ (ξ / (ell s / 4) - n) : ℂ) *
      Complex.exp (((2 * π * γ : ℝ) : ℂ) * Complex.I * ξ)) = fun ξ => lam * (u ξ * v ξ) := by
    funext ξ; simp only [hu, hv, mul_assoc, hb]
  rw [hfun]
  refine ⟨contDiff_const.mul (hud.mul hvd), ?_, ?_⟩
  · intro ξ hξ
    by_contra hne
    have hu0 : (ψ (ξ / b - n) : ℂ) ≠ 0 := by
      intro h0
      apply hne
      have : u ξ = 0 := h0
      simp [this]
    have hψ0 : ψ (ξ / b - n) ≠ 0 := by exact_mod_cast hu0
    obtain ⟨h1, h2⟩ := hsupp _ hψ0
    have h3 : b * (n + lo) < ξ := by
      have := mul_lt_mul_of_pos_left (show n + lo < ξ / b by linarith) hb0
      rwa [mul_div_cancel₀ _ hb0.ne'] at this
    have h4 : ξ < b * (n + hi) := by
      have := mul_lt_mul_of_pos_left (show ξ / b < n + hi by linarith) hb0
      rwa [mul_div_cancel₀ _ hb0.ne'] at this
    rw [hβ] at hξ
    have e : (2 : ℝ) ^ (-s) = ell s := rfl
    rw [e] at hξ
    rw [lt_abs] at hξ
    rcases hξ with h | h <;> linarith
  · intro a ha ξ
    have e : (2 : ℝ) ^ (-s) = 4 * b := by rw [hb]; unfold ell; ring
    rw [e]
    rw [iteratedDeriv_const_mul lam ((hud.mul hvd).contDiffAt.of_le (by exact_mod_cast le_top)), norm_mul]
    have h1 := hM b hb0 n γ a ha ξ
    have hprod : (fun ξ : ℝ => u ξ * v ξ) = fun ξ : ℝ => (ψ (ξ / b - n) : ℂ) *
        Complex.exp (((2 * π * γ : ℝ) : ℂ) * Complex.I * ξ) := rfl
    rw [hprod]
    calc (4 * b) ^ a * (‖lam‖ * ‖iteratedDeriv a (fun ξ : ℝ => (ψ (ξ / b - n) : ℂ) *
          Complex.exp (((2 * π * γ : ℝ) : ℂ) * Complex.I * ξ)) ξ‖)
        = ‖lam‖ * ((4 * b) ^ a * ‖iteratedDeriv a (fun ξ : ℝ => (ψ (ξ / b - n) : ℂ) *
          Complex.exp (((2 * π * γ : ℝ) : ℂ) * Complex.I * ξ)) ξ‖) := by ring
      _ ≤ ‖lam‖ * (M * (4 * (1 + 2 * π * |γ| * b)) ^ 𝔭.D) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ ≤ 𝔭.C := hC

end PrimeBHT.TimeFrequency.X2.Disc
