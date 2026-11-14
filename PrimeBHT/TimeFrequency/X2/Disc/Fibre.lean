module

public import PrimeBHT.TimeFrequency.X2.Disc.PairSum
public import PrimeBHT.TimeFrequency.X2.Disc.Indexed
public import PrimeBHT.TimeFrequency.X2.Disc.Mult
import PrimeBHT.Interface.X2Checks

/-!
# X2, node V05 (R4-3, R4-4b): normalized multipliers and the bound of one fibre

For fixed `n` (V04 index), `d` and a coarse class `cl`, a finite set `J` of `(k, n₁)` whose boxes `pairBox (5-k) n₁ d t`
lie in the rank-1 set `cl.set` (injectively) satisfies
`‖Σ_{(k,n₁) ∈ J} c_{k,n} pairTerm k n n₁ d‖ₑ ≤ ofReal (B Q₁ Q₁ Q₃) · 2 · ofReal(C₀ CT) ‖F₁‖₂ ‖F₂‖₂ ‖F₃‖_u`
(`fibre_bound`), by the model bound (`class_form_bound_indexed`) applied to the normalized multipliers.
-/

@[expose] public noncomputable section

open MeasureTheory Complex Set
open scoped ENNReal FourierTransform SchwartzMap ComplexConjugate Real ContDiff
open PrimeBHT.Statements (yNorm tensorFun tensorFourier multiplierForm)

set_option autoImplicit false

namespace PrimeBHT.TimeFrequency.X2.Disc

/-- The statement of `inMult_bumpPhase` for a given constant `M`. -/
def IMStmt (𝔭 : Params) (ψ : ℝ → ℝ) (lo hi M : ℝ) : Prop :=
  ∀ (s : ℤ) (c n γ : ℝ) (lam : ℂ), c - 11 * ell s / 8 ≤ ell s / 4 * (n + lo) →
    ell s / 4 * (n + hi) ≤ c + 11 * ell s / 8 →
    ‖lam‖ * (M * (4 * (1 + 2 * π * |γ| * (ell s / 4))) ^ 𝔭.D) ≤ 𝔭.C →
    InMult 𝔭 s c (fun ξ : ℝ => lam * (ψ (ξ / (ell s / 4) - n) : ℂ) *
      Complex.exp (((2 * π * γ : ℝ) : ℂ) * Complex.I * ξ))

theorem exists_IMStmt {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (lo hi : ℝ)
    (hsupp : ∀ x, ψ x ≠ 0 → lo < x ∧ x < hi) (𝔭 : Params) (hβ : 𝔭.β = 11 / 4) :
    ∃ M : ℝ, 0 ≤ M ∧ IMStmt 𝔭 ψ lo hi M :=
  inMult_bumpPhase hψ hc lo hi hsupp 𝔭 hβ

/-- `X(n) = 4 (1 + π|n|/512)`. -/
def Xn (n : ℤ) : ℝ := 4 * (1 + π * |(n : ℝ)| / 512)

/-- Amplitude normalizations of slots 1, 2 and 3. -/
def Qa (𝔭 : Params) (M₁ : ℝ) (n : ℤ) : ℝ := (M₁ + 1) * Xn n ^ 𝔭.D / 𝔭.C
def Qc (𝔭 : Params) (M₃ : ℝ) : ℝ := (M₃ + 1) * 4 ^ 𝔭.D / 𝔭.C

theorem Xn_pos (n : ℤ) : 0 < Xn n := by unfold Xn; positivity

theorem Qa_pos {𝔭 : Params} (hC : 0 < 𝔭.C) {M₁ : ℝ} (hM : 0 ≤ M₁) (n : ℤ) : 0 < Qa 𝔭 M₁ n := by
  unfold Qa; have := Xn_pos n; positivity

theorem Qc_pos {𝔭 : Params} (hC : 0 < 𝔭.C) {M₃ : ℝ} (hM : 0 ≤ M₃) : 0 < Qc 𝔭 M₃ := by
  unfold Qc; positivity

theorem amp_ok {𝔭 : Params} (hC : 0 < 𝔭.C) {M X Q : ℝ} (hM : 0 ≤ M) (hX : 0 < X) (hQ : Q = (M + 1) * X ^ 𝔭.D / 𝔭.C)
    {κ : ℂ} (hκ : ‖κ‖ ≤ 1) : ‖κ / ((Q : ℝ) : ℂ)‖ * (M * X ^ 𝔭.D) ≤ 𝔭.C := by
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
  have h1 : ‖κ‖ / Q ≤ 1 / Q := div_le_div_of_nonneg_right hκ hQ0.le
  have hXD : 0 < X ^ 𝔭.D := by positivity
  calc ‖κ‖ / Q * (M * X ^ 𝔭.D) ≤ 1 / Q * (M * X ^ 𝔭.D) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 𝔭.C * (M / (M + 1)) := by rw [hQ]; field_simp
    _ ≤ 𝔭.C * 1 := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        rw [div_le_one (by linarith)]; linarith
    _ = 𝔭.C := mul_one _

theorem shift_bk (k n : ℤ) : 2 * π * |symbolShift (k, n)| * bk k = π * |(n : ℝ)| / 512 := by
  unfold symbolShift bk
  simp only
  rw [abs_div, abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) (-k)), abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  have : (2 : ℝ) ^ (-k) * (2 : ℝ) ^ (k - 7) = 1 / 128 := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), show -k + (k - 7) = (-7 : ℤ) by ring]
    norm_num
  calc 2 * π * (|(n : ℝ)| * (2 : ℝ) ^ (-k) / 8) * (2 : ℝ) ^ (k - 7)
      = 2 * π * |(n : ℝ)| / 8 * ((2 : ℝ) ^ (-k) * (2 : ℝ) ^ (k - 7)) := by ring
    _ = _ := by rw [this]; ring

theorem four_one_add_shift (k n : ℤ) : 4 * (1 + 2 * π * |-symbolShift (k, n)| * (ell (5 - k) / 4)) = Xn n := by
  rw [abs_neg, bk_eq_ell, shift_bk]; unfold Xn; ring

theorem four_one_add_shift' (k n : ℤ) : 4 * (1 + 2 * π * |symbolShift (k, n)| * (ell (5 - k) / 4)) = Xn n := by
  rw [bk_eq_ell, shift_bk]; unfold Xn; ring

/-- The normalized multipliers of the pair `(k, n₁, d)` with amplitude `κ` in slot 1. -/
def mmult (𝔭 : Params) (M₁ M₃ : ℝ) (k n n₁ d : ℤ) (κ : ℂ) : Fin 3 → ℝ → ℂ :=
  ![fun ξ => (κ / ((Qa 𝔭 M₁ n : ℝ) : ℂ)) * mu1 k n n₁ ξ,
    fun ξ => (1 / ((Qa 𝔭 M₁ n : ℝ) : ℂ)) * mu2 k n n₁ d ξ,
    fun ξ => (1 / ((Qc 𝔭 M₃ : ℝ) : ℂ)) * mu3 k n₁ d ξ]

theorem inMult_pair {𝔭 : Params} (hC : 0 < 𝔭.C) {M₁ M₃ : ℝ} (h₁ : 0 ≤ M₁) (h₃ : 0 ≤ M₃)
    (hI₁ : IMStmt 𝔭 wphi (-1 / 2) (3 / 2) M₁) (hI₃ : IMStmt 𝔭 wphi3 (-3 / 2) (7 / 2) M₃)
    (k n n₁ d t : ℤ) {κ : ℂ} (hκ : ‖κ‖ ≤ 1) (j : Fin 3) :
    InMult 𝔭 (pairBox (5 - k) n₁ d t).scale ((pairBox (5 - k) n₁ d t).centre j)
      (mmult 𝔭 M₁ M₃ k n n₁ d κ j) := by
  have hsup := pairBox_support (5 - k) n₁ d t
  dsimp only at hsup
  obtain ⟨⟨s1, s2⟩, ⟨s3, s4⟩, ⟨s5, s6⟩⟩ := hsup
  have hX := Xn_pos n
  have hQa := Qa_pos hC h₁ n
  have hQc := Qc_pos hC h₃
  fin_cases j
  · -- slot 0
    have hamp : ‖κ / ((Qa 𝔭 M₁ n : ℝ) : ℂ)‖ * (M₁ * (4 * (1 + 2 * π * |-symbolShift (k, n)| *
        (ell (5 - k) / 4))) ^ 𝔭.D) ≤ 𝔭.C := by
      rw [four_one_add_shift]; exact amp_ok hC h₁ hX rfl hκ
    have := hI₁ (5 - k) ((pairBox (5 - k) n₁ d t).centre 0) (n₁ : ℝ) (-symbolShift (k, n)) _
      (by linarith) (by linarith) hamp
    simp only [bk_eq_ell] at this
    show InMult 𝔭 (5 - k) ((pairBox (5 - k) n₁ d t).centre 0) (mmult 𝔭 M₁ M₃ k n n₁ d κ 0)
    convert this using 1
    funext ξ
    simp only [mmult, mu1, Matrix.cons_val_zero]
    push_cast
    ring_nf
  · -- slot 1
    have hamp : ‖(1 : ℂ) / ((Qa 𝔭 M₁ n : ℝ) : ℂ)‖ * (M₁ * (4 * (1 + 2 * π * |symbolShift (k, n)| *
        (ell (5 - k) / 4))) ^ 𝔭.D) ≤ 𝔭.C := by
      rw [four_one_add_shift']; exact amp_ok hC h₁ hX rfl (by simp)
    have := hI₁ (5 - k) ((pairBox (5 - k) n₁ d t).centre 1) (((n₁ + d : ℤ) : ℝ)) (symbolShift (k, n)) _
      (by linarith) (by linarith) hamp
    simp only [bk_eq_ell] at this
    show InMult 𝔭 (5 - k) ((pairBox (5 - k) n₁ d t).centre 1) (mmult 𝔭 M₁ M₃ k n n₁ d κ 1)
    convert this using 1
    funext ξ
    simp only [mmult, mu2, Matrix.cons_val_one, bk_eq_ell]
    push_cast
    ring_nf
  · -- slot 2
    have hamp : ‖(1 : ℂ) / ((Qc 𝔭 M₃ : ℝ) : ℂ)‖ * (M₃ * (4 * (1 + 2 * π * |(0 : ℝ)| *
        (ell (5 - k) / 4))) ^ 𝔭.D) ≤ 𝔭.C := by
      have := amp_ok hC h₃ (X := 4) (Q := Qc 𝔭 M₃) (by norm_num) rfl (κ := 1) (by simp)
      simpa using this
    have := hI₃ (5 - k) ((pairBox (5 - k) n₁ d t).centre 2) (((n₁ + (n₁ + d) : ℤ) : ℝ)) 0 _
      (by linarith) (by linarith) hamp
    simp only [bk_eq_ell] at this
    show InMult 𝔭 (5 - k) ((pairBox (5 - k) n₁ d t).centre 2) (mmult 𝔭 M₁ M₃ k n n₁ d κ 2)
    convert this using 1
    funext ξ
    simp only [mmult, mu3, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast
    simp

section Vector

variable {P : ℕ} [NeZero P]

theorem scaled_integral (T : Form P) (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ)) (k n n₁ d : ℤ) (α₁ α₂ α₃ : ℂ) :
    ∫ x, T (tmult (fun ξ => α₁ * mu1 k n n₁ ξ) (tensorFun f₁) x)
        (tmult (fun ξ => α₂ * mu2 k n n₁ d ξ) (tensorFun f₂) x)
        (tmult (fun ξ => α₃ * mu3 k n₁ d ξ) (tensorFun f₃) x) =
      α₁ * α₂ * (starRingEnd ℂ) α₃ * pairTerm T f₁ f₂ f₃ k n n₁ d := by
  rw [integral_form_tmult T (contDiff_const.mul (contDiff_mu1 k n n₁)) ((hasCompactSupport_mu1 k n n₁).mul_left)
    (contDiff_const.mul (contDiff_mu2 k n n₁ d)) ((hasCompactSupport_mu2 k n n₁ d).mul_left)
    (contDiff_const.mul (contDiff_mu3 k n₁ d)) ((hasCompactSupport_mu3 k n₁ d).mul_left),
    pairTerm_eq_integral, integral_form_tmult T (contDiff_mu1 k n n₁) (hasCompactSupport_mu1 k n n₁)
      (contDiff_mu2 k n n₁ d) (hasCompactSupport_mu2 k n n₁ d) (contDiff_mu3 k n₁ d) (hasCompactSupport_mu3 k n₁ d),
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [map_mul]
  ring

theorem tensorFun_hyps (f : ZMod P → 𝓢(ℝ, ℂ)) :
    Continuous (tensorFun f) ∧ IsBddV (tensorFun f) ∧
      eLpNorm (fun x : ℝ => yNorm 2 (tensorFun f x)) 2 volume < ⊤ := by
  have hc : Continuous (tensorFun f) := continuous_pi fun y => continuous_tensorFun_apply f y
  refine ⟨hc, ⟨hc.measurable, ?_⟩, PrimeBHT.Interface.X2.eLpNorm_two_tensorFun_lt_top f⟩
  choose c hc' using fun A => PrimeBHT.Interface.X2.schwartz_bounded (f A)
  exact ⟨∑ A, c A, fun x => PrimeBHT.Interface.X2.yNorm_le two_pos _ fun y =>
    (PrimeBHT.Interface.X2.norm_tensorFun_le f x y).trans (Finset.sum_le_sum fun A _ => hc' A x)⟩

/-- **R4-4b: the bound of one fibre.** -/
theorem fibre_bound {u : ℝ} {𝔭 : Params} {C₀ : ℝ} (hM : ModelBoundAt u 𝔭 C₀) (hJ𝔭 : 𝔭.J = 16)
    (hC : 0 < 𝔭.C) {M₁ M₃ : ℝ} (h₁ : 0 ≤ M₁) (h₃ : 0 ≤ M₃)
    (hI₁ : IMStmt 𝔭 wphi (-1 / 2) (3 / 2) M₁) (hI₃ : IMStmt 𝔭 wphi3 (-3 / 2) (7 / 2) M₃)
    {η : ℝ → ℝ} (hη : IsEtaCut 𝔭 η) (hX : ∀ s v : ℤ, InX 𝔭 s v (tileCutoff η s v))
    {T : Form P} {CT : ℝ} (hT : FormBound u T CT) (f₁ f₂ f₃ : ZMod P → 𝓢(ℝ, ℂ))
    (c : ℤ → ℤ → ℂ) {B : ℝ} (hB : 0 < B) (n : ℤ) (hcB : ∀ k, ‖c k n‖ ≤ B)
    (d : ℤ) (hd : 62 ≤ |d| ∧ |d| ≤ 258) (ρ : ℤ) (cl : WClass) (J : Finset (ℤ × ℤ))
    (hJ : ∀ q ∈ J, q.2 % 4 = ρ ∧ pairClass (5 - q.1) q.2 d (selT (5 - q.1) q.2 d) = cl) :
    ‖∑ q ∈ J, c q.1 n * pairTerm T f₁ f₂ f₃ q.1 n q.2 d‖ₑ ≤
      ENNReal.ofReal (B * Qa 𝔭 M₁ n * Qa 𝔭 M₁ n * Qc 𝔭 M₃) *
        (2 * (ENNReal.ofReal (C₀ * CT) * eLpNorm (fun x => yNorm 2 (tensorFun f₁ x)) 2 volume *
          eLpNorm (fun x => yNorm 2 (tensorFun f₂ x)) 2 volume *
          eLpNorm (fun x => yNorm u (tensorFun f₃ x)) ⊤ volume)) := by
  classical
  by_cases hJe : J = ∅
  · subst hJe; simp
  obtain ⟨q₀, hq₀⟩ := Finset.nonempty_iff_ne_empty.2 hJe
  have hvalid : cl.Valid := by
    have := pairClass_valid (5 - q₀.1) q₀.2 d hd
    rwa [(hJ q₀ hq₀).2] at this
  have hrank : IsRankOne 𝔭.J cl.set := by rw [hJ𝔭]; exact WClass.isRankOne_set cl hvalid
  set β : ℤ × ℤ → Box := fun q => pairBox (5 - q.1) q.2 d (selT (5 - q.1) q.2 d) with hβdef
  have hcl : ∀ q ∈ J, pairClass (5 - q.1) q.2 d (selT (5 - q.1) q.2 d) = cl := fun q hq => (hJ q hq).2
  have hβQ : ∀ q ∈ J, β q ∈ cl.set := by
    intro q hq
    have := pairBox_mem (5 - q.1) q.2 d (selT (5 - q.1) q.2 d)
    rwa [hcl q hq] at this
  have hβe : ∀ q ∈ J, β q = cl.box (5 - q.1) (i1 cl.t q.2) := by
    intro q hq
    have ht : selT (5 - q.1) q.2 d = cl.t := by
      have := congrArg WClass.t (hcl q hq)
      rwa [pairClass_t] at this
    simp only [hβdef, pairBox]
    rw [hcl q hq, ht]
  have hinj : Set.InjOn β ↑J := by
    intro q hq q' hq' h
    have hq := Finset.mem_coe.1 hq
    have hq' := Finset.mem_coe.1 hq'
    rw [hβe q hq, hβe q' hq'] at h
    obtain ⟨hs, hi⟩ := WClass.box_injective cl h
    have h1 : q.1 = q'.1 := by omega
    have h2 : q.2 = q'.2 := i1_injective cl.t q.2 q'.2 (by rw [(hJ q hq).1, (hJ q' hq').1]) hi
    exact Prod.ext h1 h2
  set κ : ℤ × ℤ → ℂ := fun q => c q.1 n / (B : ℂ) with hκdef
  have hκ : ∀ q, ‖κ q‖ ≤ 1 := by
    intro q
    simp only [hκdef]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB, div_le_one hB]
    exact hcB q.1
  set m : ℤ × ℤ → Fin 3 → ℝ → ℂ := fun q => mmult 𝔭 M₁ M₃ q.1 n q.2 d (κ q) with hmdef
  have hm : ∀ q ∈ J, ∀ k, InMult 𝔭 (β q).scale ((β q).centre k) (m q k) := fun q hq k =>
    inMult_pair hC h₁ h₃ hI₁ hI₃ q.1 n q.2 d _ (hκ q) k
  obtain ⟨hc₁, hb₁, hf₁⟩ := tensorFun_hyps f₁
  obtain ⟨hc₂, hb₂, hf₂⟩ := tensorFun_hyps f₂
  obtain ⟨hc₃, hb₃, -⟩ := tensorFun_hyps f₃
  have hm0 : ∀ q, m q 0 = fun ξ => (κ q / ((Qa 𝔭 M₁ n : ℝ) : ℂ)) * mu1 q.1 n q.2 ξ := fun q => rfl
  have hm1 : ∀ q, m q 1 = fun ξ => (1 / ((Qa 𝔭 M₁ n : ℝ) : ℂ)) * mu2 q.1 n q.2 d ξ := fun q => rfl
  have hm2 : ∀ q, m q 2 = fun ξ => (1 / ((Qc 𝔭 M₃ : ℝ) : ℂ)) * mu3 q.1 q.2 d ξ := fun q => rfl
  have hint : ∀ q ∈ J, Integrable (fun x => T (tmult (m q 0) (tensorFun f₁) x) (tmult (m q 1) (tensorFun f₂) x)
      (tmult (m q 2) (tensorFun f₃) x)) := by
    intro q hq
    rw [hm0, hm1, hm2]
    exact integrable_T_tmult T (contDiff_const.mul (contDiff_mu1 q.1 n q.2))
      ((hasCompactSupport_mu1 q.1 n q.2).mul_left) (contDiff_const.mul (contDiff_mu2 q.1 n q.2 d))
      ((hasCompactSupport_mu2 q.1 n q.2 d).mul_left) (contDiff_const.mul (contDiff_mu3 q.1 q.2 d))
      ((hasCompactSupport_mu3 q.1 q.2 d).mul_left) f₁ f₂ f₃
  have key := class_form_bound_indexed hM hT hrank J β hinj hβQ m hm hη hX hc₁ hc₂ hc₃ hb₁ hb₂ hb₃ hf₁ hf₂ hint
  -- identify the sum
  have hQa := Qa_pos hC h₁ n
  have hQc := Qc_pos hC h₃
  have hid : ∑ q ∈ J, c q.1 n * pairTerm T f₁ f₂ f₃ q.1 n q.2 d =
      (((B * Qa 𝔭 M₁ n * Qa 𝔭 M₁ n * Qc 𝔭 M₃ : ℝ)) : ℂ) * ∑ q ∈ J, ∫ x, T (tmult (m q 0) (tensorFun f₁) x)
        (tmult (m q 1) (tensorFun f₂) x) (tmult (m q 2) (tensorFun f₃) x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [hm0, hm1, hm2, scaled_integral]
    simp only [hκdef, Complex.conj_ofReal, map_div₀, map_one]
    have hB' : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
    have hQa' : ((Qa 𝔭 M₁ n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hQa.ne'
    have hQc' : ((Qc 𝔭 M₃ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hQc.ne'
    push_cast
    field_simp
  rw [hid, enorm_mul]
  have hr : ‖(((B * Qa 𝔭 M₁ n * Qa 𝔭 M₁ n * Qc 𝔭 M₃ : ℝ)) : ℂ)‖ₑ =
      ENNReal.ofReal (B * Qa 𝔭 M₁ n * Qa 𝔭 M₁ n * Qc 𝔭 M₃) := by
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ B * Qa 𝔭 M₁ n * Qa 𝔭 M₁ n * Qc 𝔭 M₃)]
  rw [hr]
  gcongr

end Vector

end PrimeBHT.TimeFrequency.X2.Disc
