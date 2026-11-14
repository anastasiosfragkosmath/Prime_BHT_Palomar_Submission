module

public import PrimeBHT.TimeFrequency.X2.Psp.O2Kernel
public import PrimeBHT.TimeFrequency.X2.Psp.Geometry

/-!
# X2, V13 O2 (d): the commutator `[H_x, T_A]` of a Heaviside function with a multiplier (MTT2 `clij-est`, `mean`)

For a smooth compactly supported symbol `A` (kernel `k = 𝓕⁻ A`), `x ∈ ℝ`, `H_x = 1_{[x, ∞)}` (`heav (· - x)`) and a bounded
measurable `g`:
`commOp A x g z = H_x(z) (T_A g)(z) - T_A (H_x g)(z) = ∫ k(z - b) (H_x(z) - H_x(b)) g(b) db`.

* `comm_integrand_le`: pointwise domination (the kernel is evaluated at `z - b`, the difference `H_x(z) - H_x(b)` is non-zero only if
  `x` lies between `z` and `b`, so `|b - x| ≤ |z - b|`, `|z - x| ≤ |z - b|`): for a kernel decay `jb(w/ℓ)^{-q}` and a growth
  `‖g(b)‖ ≤ A jb((b - x)/L)^N` this gives `κ A (ℓ/L)^N jb((z-x)/ℓ)^{-p} jb((z-b)/ℓ)^{-p}`;
* `yNorm_commV_le`: the commutator of a `Y`-valued function is `≲ jb((z - x)/ℓ)^{-p}` (Minkowski);
* `integral_commOp_tilSym`: the MEAN of the commutator is the coefficient functional: `∫ commOp (tilSym J τ) x g = ∫ tilPhi(x - b) g(b) db`;
* `integral_commOp_eq`: the mean is the same for `tilSym` and `ovTilSym` (both reproduce `g`): the Leibniz rule
  `[H, T_{AB}] g = [H, T_A] T_B g + T_A [H, T_B] g` and `∫ T_A f = A(0) ∫ f = 0`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform ContDiff Real Convolution
open PrimeBHT.Statements PrimeBHT.TimeFrequency.Tile

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

/-! ## Basics -/

theorem measurable_heav : Measurable heav := by
  unfold heav
  exact Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const

theorem heav_nonneg (t : ℝ) : 0 ≤ heav t := by unfold heav; split_ifs <;> norm_num

theorem heav_le_one (t : ℝ) : heav t ≤ 1 := by unfold heav; split_ifs <;> norm_num

theorem abs_heav_sub_le_one (s t : ℝ) : |heav s - heav t| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [heav_nonneg s, heav_nonneg t, heav_le_one s, heav_le_one t]

theorem norm_heav (t : ℝ) : ‖((heav t : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (heav_nonneg t)]; exact heav_le_one t

/-- `H(z - x) ≠ H(b - x)` forces `x` to lie between `z` and `b`. -/
theorem heav_ne {x z b : ℝ} (h : heav (z - x) ≠ heav (b - x)) : |b - x| ≤ |z - b| ∧ |z - x| ≤ |z - b| := by
  unfold heav at h
  by_cases h1 : 0 ≤ z - x <;> by_cases h2 : 0 ≤ b - x
  · simp [h1, h2] at h
  · push Not at h2
    rw [abs_of_neg (by linarith : b - x < 0), abs_of_nonneg h1, abs_of_nonneg (by linarith : 0 ≤ z - b)]
    constructor <;> linarith
  · push Not at h1
    rw [abs_of_nonneg h2, abs_of_neg h1, abs_of_neg (by linarith : z - b < 0)]
    constructor <;> linarith
  · push Not at h1 h2
    simp [not_le.2 h1, not_le.2 h2] at h

theorem measurable_tm {A : ℝ → ℂ} (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A) {g : ℝ → ℂ}
    (hg : Measurable g) : Measurable (tm A g) := by
  obtain ⟨hkc, hki⟩ := kernel_facts hA hAc
  have h1 : StronglyMeasurable (Function.uncurry fun (x z : ℝ) => 𝓕⁻ A (x - z) * g z) :=
    ((hkc.comp (continuous_fst.sub continuous_snd)).stronglyMeasurable).mul
      (hg.comp measurable_snd).stronglyMeasurable
  exact (h1.integral_prod_right).measurable

theorem norm_tm_le_gen {A : ℝ → ℂ} (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A) {g : ℝ → ℂ}
    (_hg : Measurable g) {B : ℝ} (hB : ∀ z, ‖g z‖ ≤ B) (x : ℝ) : ‖tm A g x‖ ≤ B * ∫ w, ‖𝓕⁻ A w‖ := by
  obtain ⟨hkc, hki⟩ := kernel_facts hA hAc
  unfold tm
  refine (norm_integral_le_integral_norm _).trans ?_
  have h1 : ∫ z, ‖𝓕⁻ A (x - z) * g z‖ ≤ ∫ z, ‖𝓕⁻ A (x - z)‖ * B := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _) ?_
      (Filter.Eventually.of_forall fun z => ?_)
    · exact (hki.norm.comp_sub_left x).mul_const B
    · dsimp only; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB z) (norm_nonneg _)
  refine h1.trans (le_of_eq ?_)
  rw [integral_mul_const, integral_sub_left_eq_self (fun w => ‖𝓕⁻ A w‖) volume x, mul_comm]

/-! ## The commutator -/

/-- `[H_x, T_A] g (z) = H_x(z) T_A g (z) - T_A (H_x g) (z)`. -/
def commOp (A : ℝ → ℂ) (x : ℝ) (g : ℝ → ℂ) (z : ℝ) : ℂ :=
  ((heav (z - x) : ℝ) : ℂ) * tm A g z - tm A (fun b => ((heav (b - x) : ℝ) : ℂ) * g b) z

theorem measurable_Hg {x : ℝ} {g : ℝ → ℂ} (hg : Measurable g) :
    Measurable (fun b => ((heav (b - x) : ℝ) : ℂ) * g b) := by
  have := measurable_heav
  have h2 : Measurable (fun b : ℝ => ((heav (b - x) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (measurable_heav.comp (measurable_id.sub measurable_const))
  exact h2.mul hg

theorem norm_Hg_le {x : ℝ} {g : ℝ → ℂ} {B : ℝ} (hB : ∀ z, ‖g z‖ ≤ B) (b : ℝ) :
    ‖((heav (b - x) : ℝ) : ℂ) * g b‖ ≤ B := by
  rw [norm_mul]
  have h0 := norm_nonneg (g b)
  calc ‖((heav (b - x) : ℝ) : ℂ)‖ * ‖g b‖ ≤ 1 * B := mul_le_mul (norm_heav _) (hB b) h0 zero_le_one
    _ = B := one_mul B

theorem commOp_eq {A : ℝ → ℂ} (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A) {g : ℝ → ℂ}
    (hg : Measurable g) {B : ℝ} (hB : ∀ z, ‖g z‖ ≤ B) (x z : ℝ) :
    commOp A x g z = ∫ b, 𝓕⁻ A (z - b) * (((heav (z - x) - heav (b - x) : ℝ) : ℂ) * g b) := by
  obtain ⟨hkc, hki⟩ := kernel_facts hA hAc
  have i1 := integrable_kmul hki hg hB z hkc
  have i2 := integrable_kmul hki (measurable_Hg (x := x) hg) (norm_Hg_le (x := x) hB) z hkc
  unfold commOp tm
  rw [← integral_const_mul, ← integral_sub (i1.const_mul _) i2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  beta_reduce
  push_cast
  ring

/-! ## Weights -/

theorem jb_mono {a b : ℝ} (h : |a| ≤ |b|) : jb a ≤ jb b := by unfold jb; linarith

theorem jb_div_le_mul {t L ℓ : ℝ} (hL : 0 < L) (hLℓ : L ≤ ℓ) : jb (t / L) ≤ (ℓ / L) * jb (t / ℓ) := by
  have hℓ : 0 < ℓ := hL.trans_le hLℓ
  unfold jb
  rw [abs_div, abs_div, abs_of_pos hL, abs_of_pos hℓ]
  have h1 : 1 ≤ ℓ / L := by rw [le_div_iff₀ hL]; linarith
  have : ℓ / L * (1 + |t| / ℓ) = ℓ / L + |t| / L := by field_simp
  rw [this]
  linarith

theorem integral_jb_rpow (c : ℝ) {L : ℝ} (hL : 0 < L) {p : ℝ} (hp : 1 < p) :
    ∫ x, jb ((x - c) / L) ^ (-p) = 2 * L / (p - 1) := by
  have h := integral_one_add_abs_sub_div_rpow hp c hL
  have e : ∀ x : ℝ, jb ((x - c) / L) = 1 + |x - c| / L := fun x => by
    unfold jb; rw [abs_div, abs_of_pos hL]
  simp_rw [e]
  exact h

/-- **Pointwise domination of the commutator integrand.** -/
theorem comm_integrand_le {k : ℝ → ℂ} {κ ℓ L Ag N q p x : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hLℓ : L ≤ ℓ) (hκ : 0 ≤ κ)
    (hAg : 0 ≤ Ag) (hN : 0 ≤ N) (hp : 0 ≤ p) (hk : ∀ w, ‖k w‖ ≤ κ * jb (w / ℓ) ^ (-q)) (hq : N + 2 * p ≤ q)
    {z b Γ : ℝ} (hΓ0 : 0 ≤ Γ) (hΓ : Γ ≤ Ag * jb ((b - x) / L) ^ N) :
    ‖k (z - b)‖ * (|heav (z - x) - heav (b - x)| * Γ) ≤
      κ * Ag * (ℓ / L) ^ N * (jb ((z - x) / ℓ) ^ (-p) * jb ((z - b) / ℓ) ^ (-p)) := by
  have hs1 := one_le_jb ((z - x) / ℓ)
  have ht1 := one_le_jb ((z - b) / ℓ)
  have hs0 : 0 < jb ((z - x) / ℓ) := jb_pos _
  have ht0 : 0 < jb ((z - b) / ℓ) := jb_pos _
  have hℓL : 0 ≤ ℓ / L := by positivity
  have hRHS : 0 ≤ κ * Ag * (ℓ / L) ^ N * (jb ((z - x) / ℓ) ^ (-p) * jb ((z - b) / ℓ) ^ (-p)) := by positivity
  by_cases hd : heav (z - x) = heav (b - x)
  · rw [hd, sub_self, abs_zero, zero_mul, mul_zero]; exact hRHS
  obtain ⟨hbx, hzx⟩ := heav_ne hd
  have hΔ : |heav (z - x) - heav (b - x)| ≤ 1 := abs_heav_sub_le_one _ _
  -- growth
  have hj : jb ((b - x) / L) ≤ (ℓ / L) * jb ((z - b) / ℓ) :=
    calc jb ((b - x) / L) ≤ jb ((z - b) / L) := jb_mono (by
          rw [abs_div, abs_div, abs_of_pos hL]; exact div_le_div_of_nonneg_right hbx hL.le)
      _ ≤ (ℓ / L) * jb ((z - b) / ℓ) := jb_div_le_mul hL hLℓ
  have hG1 : Γ ≤ Ag * ((ℓ / L) * jb ((z - b) / ℓ)) ^ N :=
    hΓ.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (jb_pos _).le hj hN) hAg)
  rw [Real.mul_rpow hℓL ht0.le] at hG1
  have hk1 := hk (z - b)
  have e1 : jb ((z - b) / ℓ) ^ (-q) * jb ((z - b) / ℓ) ^ N = jb ((z - b) / ℓ) ^ (N - q) := by
    rw [← Real.rpow_add ht0]; congr 1; ring
  have h2 : jb ((z - b) / ℓ) ^ (N - q) ≤ jb ((z - b) / ℓ) ^ (-p) * jb ((z - x) / ℓ) ^ (-p) := by
    have a1 : jb ((z - b) / ℓ) ^ (N - q) ≤ jb ((z - b) / ℓ) ^ (-(2 * p)) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    have a2 : jb ((z - b) / ℓ) ^ (-(2 * p)) = jb ((z - b) / ℓ) ^ (-p) * jb ((z - b) / ℓ) ^ (-p) := by
      rw [← Real.rpow_add ht0]; congr 1; ring
    have a3 : jb ((z - b) / ℓ) ^ (-p) ≤ jb ((z - x) / ℓ) ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos hs0 (jb_mono (by
        rw [abs_div, abs_div, abs_of_pos hℓ]; exact div_le_div_of_nonneg_right hzx hℓ.le)) (by linarith)
    rw [a2] at a1
    refine a1.trans ?_
    gcongr
  have hpow0 : 0 ≤ jb ((z - b) / ℓ) ^ N := by positivity
  have hG2 : Γ ≤ Ag * ((ℓ / L) ^ N * jb ((z - b) / ℓ) ^ N) := hG1
  calc ‖k (z - b)‖ * (|heav (z - x) - heav (b - x)| * Γ)
      ≤ (κ * jb ((z - b) / ℓ) ^ (-q)) * (1 * (Ag * ((ℓ / L) ^ N * jb ((z - b) / ℓ) ^ N))) :=
        mul_le_mul hk1 (mul_le_mul hΔ hG2 hΓ0 zero_le_one) (by positivity) (by positivity)
    _ = κ * Ag * (ℓ / L) ^ N * jb ((z - b) / ℓ) ^ (N - q) := by rw [← e1]; ring
    _ ≤ κ * Ag * (ℓ / L) ^ N * (jb ((z - b) / ℓ) ^ (-p) * jb ((z - x) / ℓ) ^ (-p)) := by gcongr
    _ = _ := by ring

theorem jb_sub_comm (z b ℓ : ℝ) : jb ((z - b) / ℓ) = jb ((b - z) / ℓ) := by
  unfold jb
  rw [abs_div, abs_div, abs_sub_comm z b]

/-- the decay of the kernel of a symbol in the form `κ jb(w/ℓ)^{-q}` -/
theorem tilKer_decay (J : ℕ) (τ : ℤ) (q : ℕ) (w : ℝ) :
    ‖tilKer J τ w‖ ≤ (tilConst q * (2 : ℝ) ^ (-τ)) * jb (w / (2 : ℝ) ^ (τ + (J : ℤ) + 1)) ^ (-(q : ℝ)) := by
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-(τ + (J : ℤ) + 1)) := zpow_two_pos _
  refine (norm_tilKer_le q J τ w).trans (le_of_eq ?_)
  rw [inv_pow_eq_jb hl q w]
  congr 3
  rw [zpow_neg, inv_inv]

theorem ovTilKer_decay (J : ℕ) (τ : ℤ) (q : ℕ) (w : ℝ) :
    ‖ovTilKer J τ w‖ ≤ (tilConst q * (2 : ℝ) ^ (-τ)) * jb (w / (2 : ℝ) ^ (τ + (J : ℤ) + 1)) ^ (-(q : ℝ)) := by
  have hl : (0 : ℝ) < (2 : ℝ) ^ (-(τ + (J : ℤ) + 1)) := zpow_two_pos _
  refine (norm_ovTilKer_le q J τ w).trans (le_of_eq ?_)
  rw [inv_pow_eq_jb hl q w]
  congr 3
  rw [zpow_neg, inv_inv]

section Vec

variable {P : ℕ} [NeZero P]

/-- the commutator of a `Y`-valued function, coordinatewise -/
def commV (A : ℝ → ℂ) (x : ℝ) (G : ℝ → ZMod P → ℂ) (z : ℝ) : ZMod P → ℂ :=
  fun y => commOp A x (fun b => G b y) z

theorem yNorm_commV_le {A : ℝ → ℂ} (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A) {G : ℝ → ZMod P → ℂ}
    (hG : Measurable G) {B : ℝ} (hB : ∀ b y, ‖G b y‖ ≤ B) (x z : ℝ) :
    yNorm 2 (commV A x G z) ≤
      ∫ b, ‖𝓕⁻ A (z - b)‖ * (|heav (z - x) - heav (b - x)| * yNorm 2 (G b)) := by
  obtain ⟨hkc, hki⟩ := kernel_facts hA hAc
  have hcoord : ∀ y, commV A x G z y = ∫ b, 𝓕⁻ A (z - b) * (((heav (z - x) - heav (b - x) : ℝ) : ℂ) * G b y) :=
    fun y => commOp_eq hA hAc (measurable_pi_iff.1 hG y) (fun b => hB b y) x z
  have hint : ∀ y, Integrable (fun b => 𝓕⁻ A (z - b) * (((heav (z - x) - heav (b - x) : ℝ) : ℂ) * G b y)) := by
    intro y
    refine integrable_kmul hki (f := fun b => ((heav (z - x) - heav (b - x) : ℝ) : ℂ) * G b y) ?_ (B := B) ?_ z hkc
    · have h2 : Measurable (fun b : ℝ => (((heav (z - x) - heav (b - x) : ℝ)) : ℂ)) :=
        Complex.measurable_ofReal.comp ((measurable_const).sub (measurable_heav.comp (measurable_id.sub measurable_const)))
      exact h2.mul ((measurable_pi_apply y).comp hG)
    · intro b
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |heav (z - x) - heav (b - x)| * ‖G b y‖ ≤ 1 * B :=
            mul_le_mul (abs_heav_sub_le_one _ _) (hB b y) (norm_nonneg _) zero_le_one
        _ = B := one_mul B
  have h := yNorm_integral_le_of_one_le (s := 2) (by norm_num)
    (fun b y => 𝓕⁻ A (z - b) * (((heav (z - x) - heav (b - x) : ℝ) : ℂ) * G b y)) hint
  have e : commV A x G z = fun y => ∫ b, 𝓕⁻ A (z - b) * (((heav (z - x) - heav (b - x) : ℝ) : ℂ) * G b y) :=
    funext hcoord
  rw [e]
  refine h.trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  beta_reduce
  have : (fun y => 𝓕⁻ A (z - b) * (((heav (z - x) - heav (b - x) : ℝ) : ℂ) * G b y)) =
      fun y => (𝓕⁻ A (z - b) * (((heav (z - x) - heav (b - x) : ℝ) : ℂ))) * G b y := funext fun y => by ring
  rw [this, yNorm_fun_const_mul (by norm_num), norm_mul, Complex.norm_real, Real.norm_eq_abs]
  ring

/-- **The commutator of a `Y`-valued function decays away from `x`.** -/
theorem yNorm_commV_decay {A : ℝ → ℂ} (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A) {G : ℝ → ZMod P → ℂ}
    (hG : Measurable G) {B : ℝ} (hB : ∀ b y, ‖G b y‖ ≤ B) {κ ℓ L Ag N q p x : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L)
    (hLℓ : L ≤ ℓ) (hκ : 0 ≤ κ) (hAg : 0 ≤ Ag) (hN : 0 ≤ N) (hp1 : 1 < p)
    (hk : ∀ w, ‖𝓕⁻ A w‖ ≤ κ * jb (w / ℓ) ^ (-q)) (hq : N + 2 * p ≤ q)
    (hgrow : ∀ b, yNorm 2 (G b) ≤ Ag * jb ((b - x) / L) ^ N) (z : ℝ) :
    yNorm 2 (commV A x G z) ≤
      κ * Ag * (ℓ / L) ^ N * (2 * ℓ / (p - 1)) * jb ((z - x) / ℓ) ^ (-p) := by
  obtain ⟨hkc, hki⟩ := kernel_facts hA hAc
  refine (yNorm_commV_le hA hAc hG hB x z).trans ?_
  have hp0 : 0 ≤ p := by linarith
  have hdom : ∀ b, ‖𝓕⁻ A (z - b)‖ * (|heav (z - x) - heav (b - x)| * yNorm 2 (G b)) ≤
      κ * Ag * (ℓ / L) ^ N * (jb ((z - x) / ℓ) ^ (-p) * jb ((z - b) / ℓ) ^ (-p)) := fun b =>
    comm_integrand_le hℓ hL hLℓ hκ hAg hN hp0 hk hq (yNorm_nonneg' 2 _) (hgrow b)
  have hint : Integrable (fun b => κ * Ag * (ℓ / L) ^ N * (jb ((z - x) / ℓ) ^ (-p) * jb ((z - b) / ℓ) ^ (-p))) := by
    have := (integrable_jb_rpow (c := z) hℓ (r := p) hp1).const_mul (κ * Ag * (ℓ / L) ^ N * jb ((z - x) / ℓ) ^ (-p))
    refine this.congr (Filter.Eventually.of_forall fun b => ?_)
    beta_reduce
    rw [jb_sub_comm z b ℓ]; ring
  have hmeas : Measurable (fun b => ‖𝓕⁻ A (z - b)‖ * (|heav (z - x) - heav (b - x)| * yNorm 2 (G b))) := by
    have h1 : Measurable (fun b : ℝ => ‖𝓕⁻ A (z - b)‖) := (hkc.comp (continuous_const.sub continuous_id)).measurable.norm
    have h2 : Measurable (fun b : ℝ => |heav (z - x) - heav (b - x)|) :=
      continuous_abs.measurable.comp
        ((measurable_const (a := heav (z - x))).sub (measurable_heav.comp (measurable_id.sub measurable_const)))
    have h3 : Measurable (fun b => yNorm 2 (G b)) := (measurable_yNorm_fun 2).comp hG
    exact h1.mul (h2.mul h3)
  have hint2 : Integrable (fun b => ‖𝓕⁻ A (z - b)‖ * (|heav (z - x) - heav (b - x)| * yNorm 2 (G b))) := by
    refine hint.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun b => ?_)
    rw [Real.norm_of_nonneg (by have := yNorm_nonneg' 2 (G b); positivity)]
    exact hdom b
  refine (integral_mono hint2 hint hdom).trans (le_of_eq ?_)
  have e : ∫ b, κ * Ag * (ℓ / L) ^ N * (jb ((z - x) / ℓ) ^ (-p) * jb ((z - b) / ℓ) ^ (-p)) =
      κ * Ag * (ℓ / L) ^ N * jb ((z - x) / ℓ) ^ (-p) * ∫ b, jb ((b - z) / ℓ) ^ (-p) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    beta_reduce
    rw [jb_sub_comm z b ℓ]; ring
  rw [e, integral_jb_rpow z hℓ hp1]
  ring

end Vec

/-! ## The mean of the commutator -/

theorem integrable_prod_conv {φ ψ : ℝ → ℝ} (hφ : Integrable φ) (hψ : Integrable ψ) :
    Integrable (fun p : ℝ × ℝ => φ p.1 * ψ (p.1 - p.2)) (volume.prod volume) := by
  have h1 : Integrable (fun p : ℝ × ℝ => φ p.2 * ψ (-(p.1 - p.2))) (volume.prod volume) :=
    Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hφ hψ.comp_neg
  have h2 := h1.swap
  refine h2.congr (Filter.Eventually.of_forall fun p => ?_)
  obtain ⟨z, w⟩ := p
  simp only [Function.comp_apply, Prod.swap_prod_mk, neg_sub]

theorem integral_tilKer_heav (J : ℕ) (τ : ℤ) (x b : ℝ) :
    ∫ z, tilKer J τ (z - b) * (((heav (z - x) - heav (b - x) : ℝ) : ℂ)) = tilPhi J τ (x - b) := by
  set u : ℝ := x - b with hu
  have h1 := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun w => tilKer J τ w * (((heav (w - u) - heav (b - x) : ℝ) : ℂ))) b
  have e : ∀ z : ℝ, tilKer J τ (z - b) * (((heav (z - x) - heav (b - x) : ℝ) : ℂ)) =
      (fun w => tilKer J τ w * (((heav (w - u) - heav (b - x) : ℝ) : ℂ))) (z - b) := by
    intro z
    beta_reduce
    rw [show z - b - u = z - x by rw [hu]; ring]
  simp_rw [e]
  rw [h1]
  have hi1 : Integrable (fun w => tilKer J τ w * (((heav (w - u) : ℝ) : ℂ))) := by
    have : (fun w => tilKer J τ w * (((heav (w - u) : ℝ) : ℂ))) = (Set.Ici u).indicator (tilKer J τ) := by
      funext w
      unfold heav
      by_cases hw : 0 ≤ w - u
      · simp [hw, Set.indicator_of_mem (show w ∈ Set.Ici u from by simpa using (by linarith : u ≤ w))]
      · have : w ∉ Set.Ici u := by simpa using (by linarith [not_le.1 hw] : w < u)
        simp [hw, Set.indicator_of_notMem this]
    rw [this]
    exact (integrable_tilKer J τ).indicator measurableSet_Ici
  have hi2 : Integrable (fun w => (((heav (b - x) : ℝ) : ℂ)) * tilKer J τ w) :=
    (integrable_tilKer J τ).const_mul _
  have e2 : ∀ w : ℝ, tilKer J τ w * (((heav (w - u) - heav (b - x) : ℝ) : ℂ)) =
      tilKer J τ w * (((heav (w - u) : ℝ) : ℂ)) - (((heav (b - x) : ℝ) : ℂ)) * tilKer J τ w := by
    intro w; push_cast; ring
  simp_rw [e2]
  rw [integral_sub hi1 hi2, integral_const_mul, integral_tilKer, mul_zero, sub_zero]
  unfold tilPhi
  rw [← integral_indicator measurableSet_Ici]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  beta_reduce
  unfold heav
  by_cases hw : 0 ≤ w - u
  · simp [hw, Set.indicator_of_mem (show w ∈ Set.Ici u from by simpa using (by linarith : u ≤ w))]
  · have : w ∉ Set.Ici u := by simpa using (by linarith [not_le.1 hw] : w < u)
    simp [hw, Set.indicator_of_notMem this]

/-- **The mean of the commutator is the coefficient functional**: `∫ [H_x, T_{S̃}] g = ∫ tilPhi(x - b) g(b) db`. -/
theorem integral_commOp_tilSym (J : ℕ) (τ : ℤ) {g : ℝ → ℂ} (hg : Measurable g) {B : ℝ} (hB : ∀ z, ‖g z‖ ≤ B)
    {Ag N x : ℝ} (hAg : 0 ≤ Ag) (hN : 0 ≤ N) {q : ℕ} (hq : N + 4 ≤ q)
    (hgrow : ∀ b, ‖g b‖ ≤ Ag * jb ((b - x) / (2 : ℝ) ^ τ) ^ N) :
    ∫ z, commOp (tilSym J τ) x g z = ∫ b, tilPhi J τ (x - b) * g b := by
  have hA := contDiff_tilSym J τ
  have hAc := hasCompactSupport_tilSym J τ
  have hkc := continuous_tilKer J τ
  have hℓ : (0 : ℝ) < (2 : ℝ) ^ (τ + (J : ℤ) + 1) := zpow_two_pos _
  have hL : (0 : ℝ) < (2 : ℝ) ^ τ := zpow_two_pos _
  have hLℓ : (2 : ℝ) ^ τ ≤ (2 : ℝ) ^ (τ + (J : ℤ) + 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hκ : 0 ≤ tilConst q * (2 : ℝ) ^ (-τ) := by
    have := tilConst_pos q; have := zpow_two_pos (-τ); positivity
  have hdom : ∀ z b : ℝ, ‖tilKer J τ (z - b) * (((heav (z - x) - heav (b - x) : ℝ) : ℂ) * g b)‖ ≤
      (tilConst q * (2 : ℝ) ^ (-τ)) * Ag * ((2 : ℝ) ^ (τ + (J : ℤ) + 1) / (2 : ℝ) ^ τ) ^ N *
        (jb ((z - x) / (2 : ℝ) ^ (τ + (J : ℤ) + 1)) ^ (-(2 : ℝ)) *
          jb ((z - b) / (2 : ℝ) ^ (τ + (J : ℤ) + 1)) ^ (-(2 : ℝ))) := by
    intro z b
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact comm_integrand_le hℓ hL hLℓ hκ hAg hN (by norm_num) (fun w => tilKer_decay J τ q w) (by push_cast; linarith)
      (norm_nonneg _) (hgrow b)
  have hint : Integrable (fun p : ℝ × ℝ => tilKer J τ (p.1 - p.2) * (((heav (p.1 - x) - heav (p.2 - x) : ℝ) : ℂ) * g p.2))
      (volume.prod volume) := by
    have h1 : Integrable (fun z : ℝ => jb ((z - x) / (2 : ℝ) ^ (τ + (J : ℤ) + 1)) ^ (-(2 : ℝ))) :=
      integrable_jb_rpow (c := x) hℓ (r := 2) (by norm_num)
    have h2 : Integrable (fun w : ℝ => jb (w / (2 : ℝ) ^ (τ + (J : ℤ) + 1)) ^ (-(2 : ℝ))) := by
      simpa using integrable_jb_rpow (c := 0) hℓ (r := 2) (by norm_num)
    have h3 := (integrable_prod_conv h1 h2).const_mul
      ((tilConst q * (2 : ℝ) ^ (-τ)) * Ag * ((2 : ℝ) ^ (τ + (J : ℤ) + 1) / (2 : ℝ) ^ τ) ^ N)
    refine h3.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · have h4 : Measurable (fun p : ℝ × ℝ => tilKer J τ (p.1 - p.2) * (((heav (p.1 - x) - heav (p.2 - x) : ℝ) : ℂ) * g p.2)) := by
        have := hkc.measurable
        have := measurable_heav
        have := hg
        fun_prop
      exact h4.aestronglyMeasurable
    · simpa [mul_assoc] using hdom p.1 p.2
  have hswap := integral_integral_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (f := fun z b => tilKer J τ (z - b) * (((heav (z - x) - heav (b - x) : ℝ) : ℂ) * g b)) hint
  calc ∫ z, commOp (tilSym J τ) x g z
      = ∫ z, ∫ b, tilKer J τ (z - b) * (((heav (z - x) - heav (b - x) : ℝ) : ℂ) * g b) :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => commOp_eq hA hAc hg hB x z)
    _ = ∫ b, ∫ z, tilKer J τ (z - b) * (((heav (z - x) - heav (b - x) : ℝ) : ℂ) * g b) := hswap
    _ = ∫ b, tilPhi J τ (x - b) * g b := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
        beta_reduce
        have : ∀ z : ℝ, tilKer J τ (z - b) * (((heav (z - x) - heav (b - x) : ℝ) : ℂ) * g b) =
            (tilKer J τ (z - b) * (((heav (z - x) - heav (b - x) : ℝ) : ℂ))) * g b := fun z => by ring
        simp_rw [this]
        rw [integral_mul_const, integral_tilKer_heav J τ x b]

/-! ## `tilSym` and `ovTilSym` give the same mean (Leibniz rule) -/

theorem integral_kernel_eq {A : ℝ → ℂ} (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A) :
    ∫ w, 𝓕⁻ A w = A 0 := by
  have h := fourier_kerS hA hAc 0
  rw [kerS_apply hA hAc] at h
  rw [← h]
  simp [Real.fourier_real_eq_integral_exp_smul]

theorem tm_eq_convolution (A : ℝ → ℂ) (f : ℝ → ℂ) :
    tm A f = (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] 𝓕⁻ A) := by
  funext z
  rw [convolution_def]
  unfold tm
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [mul_comm]

theorem integrable_tm {A : ℝ → ℂ} (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A) {f : ℝ → ℂ}
    (hf : Integrable f) : Integrable (tm A f) := by
  obtain ⟨hkc, hki⟩ := kernel_facts hA hAc
  rw [tm_eq_convolution]
  exact hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hki

theorem integral_tm {A : ℝ → ℂ} (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A) (hA0 : A 0 = 0) {f : ℝ → ℂ}
    (hf : Integrable f) : ∫ z, tm A f z = 0 := by
  obtain ⟨hkc, hki⟩ := kernel_facts hA hAc
  rw [tm_eq_convolution, integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hf hki, integral_kernel_eq hA hAc, hA0]
  simp

/-- `T_A` of a bounded measurable function is bounded and measurable. -/
theorem commOp_bounds {A : ℝ → ℂ} (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A) {g : ℝ → ℂ}
    (hg : Measurable g) {B : ℝ} (hB : ∀ z, ‖g z‖ ≤ B) (x : ℝ) :
    Measurable (commOp A x g) ∧ ∀ z, ‖commOp A x g z‖ ≤ 2 * (B * ∫ w, ‖𝓕⁻ A w‖) := by
  refine ⟨?_, fun z => ?_⟩
  · unfold commOp
    have h1 : Measurable (fun z : ℝ => ((heav (z - x) : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (measurable_heav.comp (measurable_id.sub measurable_const))
    exact (h1.mul (measurable_tm hA hAc hg)).sub (measurable_tm hA hAc (measurable_Hg (x := x) hg))
  · unfold commOp
    refine (norm_sub_le _ _).trans ?_
    have e1 : ‖((heav (z - x) : ℝ) : ℂ) * tm A g z‖ ≤ B * ∫ w, ‖𝓕⁻ A w‖ := by
      rw [norm_mul]
      calc ‖((heav (z - x) : ℝ) : ℂ)‖ * ‖tm A g z‖ ≤ 1 * (B * ∫ w, ‖𝓕⁻ A w‖) :=
            mul_le_mul (norm_heav _) (norm_tm_le_gen hA hAc hg hB z) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    have e2 := norm_tm_le_gen hA hAc (measurable_Hg (x := x) hg) (norm_Hg_le (x := x) hB) z
    linarith

/-- **Leibniz rule** `[H, T_{AB}] g = [H, T_A] T_B g + T_A [H, T_B] g`. -/
theorem commOp_mul {A B : ℝ → ℂ} (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A) (hB : ContDiff ℝ ∞ B)
    (hBc : HasCompactSupport B) {g : ℝ → ℂ} (hg : Measurable g) {C : ℝ} (hC : ∀ z, ‖g z‖ ≤ C) (x z : ℝ) :
    commOp (fun ξ => A ξ * B ξ) x g z = commOp A x (tm B g) z + tm A (commOp B x g) z := by
  have hSg : Measurable (tm B g) := measurable_tm hB hBc hg
  have hSgb : ∀ w, ‖tm B g w‖ ≤ C * ∫ w, ‖𝓕⁻ B w‖ := fun w => norm_tm_le_gen hB hBc hg hC w
  have hHg := measurable_Hg (x := x) hg
  have hHgb := norm_Hg_le (x := x) hC
  have hTHg : Measurable (tm B (fun b => ((heav (b - x) : ℝ) : ℂ) * g b)) := measurable_tm hB hBc hHg
  have hTHgb : ∀ w, ‖tm B (fun b => ((heav (b - x) : ℝ) : ℂ) * g b) w‖ ≤ C * ∫ w, ‖𝓕⁻ B w‖ :=
    fun w => norm_tm_le_gen hB hBc hHg hHgb w
  have hHS : Measurable (fun b => ((heav (b - x) : ℝ) : ℂ) * tm B g b) := measurable_Hg (x := x) hSg
  have hHSb := norm_Hg_le (x := x) hSgb
  have e1 : tm (fun ξ => A ξ * B ξ) g z = tm A (tm B g) z := (tm_comp hA hAc hB hBc hg hC z).symm
  have e2 : tm (fun ξ => A ξ * B ξ) (fun b => ((heav (b - x) : ℝ) : ℂ) * g b) z =
      tm A (tm B (fun b => ((heav (b - x) : ℝ) : ℂ) * g b)) z :=
    (tm_comp hA hAc hB hBc hHg hHgb z).symm
  have e3 : tm A (commOp B x g) z =
      tm A (fun b => ((heav (b - x) : ℝ) : ℂ) * tm B g b) z -
        tm A (tm B (fun b => ((heav (b - x) : ℝ) : ℂ) * g b)) z := by
    have := tm_sub hA hAc hHS hTHg hHSb hTHgb z
    unfold commOp
    exact this
  rw [e3]
  unfold commOp
  rw [e1, e2]
  ring

/-- **The means of the two commutators agree** if `g` is reproduced by both `A` and `B` (and `A 0 = B 0 = 0`). -/
theorem integral_commOp_eq {A B : ℝ → ℂ} (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A) (hB : ContDiff ℝ ∞ B)
    (hBc : HasCompactSupport B) (hA0 : A 0 = 0) (hB0 : B 0 = 0) {g : ℝ → ℂ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ z, ‖g z‖ ≤ C) (hgA : ∀ z, tm A g z = g z) (hgB : ∀ z, tm B g z = g z) {x : ℝ}
    (hIA : Integrable (commOp A x g)) (hIB : Integrable (commOp B x g)) :
    ∫ z, commOp A x g z = ∫ z, commOp B x g z := by
  have hgA' : tm A g = g := funext hgA
  have hgB' : tm B g = g := funext hgB
  -- (A B): `∫ [H, T_{AB}] g = ∫ [H, T_A] g`
  have h1 : ∫ z, commOp (fun ξ => A ξ * B ξ) x g z = ∫ z, commOp A x g z := by
    have e : ∀ z, commOp (fun ξ => A ξ * B ξ) x g z = commOp A x g z + tm A (commOp B x g) z := by
      intro z
      rw [commOp_mul hA hAc hB hBc hg hC x z, hgB']
    simp_rw [e]
    rw [integral_add hIA (integrable_tm hA hAc hIB), integral_tm hA hAc hA0 hIB, add_zero]
  have h2 : ∫ z, commOp (fun ξ => B ξ * A ξ) x g z = ∫ z, commOp B x g z := by
    have e : ∀ z, commOp (fun ξ => B ξ * A ξ) x g z = commOp B x g z + tm B (commOp A x g) z := by
      intro z
      rw [commOp_mul hB hBc hA hAc hg hC x z, hgA']
    simp_rw [e]
    rw [integral_add hIB (integrable_tm hB hBc hIA), integral_tm hB hBc hB0 hIA, add_zero]
  have e3 : (fun ξ => B ξ * A ξ) = fun ξ => A ξ * B ξ := funext fun ξ => mul_comm _ _
  rw [e3] at h2
  rw [← h1, h2]

end PrimeBHT.TimeFrequency.X2
