module

public import PrimeBHT.TimeFrequency.X2.TopEnergy.Bessel
public import PrimeBHT.TimeFrequency.X2.Ortho.Level

/-!
# X2, TB-4a: the Hilbert `(1-α)` form for separated top families

`docs/audits/X2-V11-TB4-plan.md` §3 (TB-4a).  For a separated dual family (the hypotheses of `bessel_of_sep`) with ONLY the
upper size bound `ĉ_i ≤ μ`:

* `bessel_upper`: `S³ ≤ (16 C₀² μ)² Λ F2²` (`S = ∑ a_i²`, `Λ = ∑ ℓ_i`, `F2 = ‖F‖₂²`), i.e. the basic estimate
  `S ≤ (16C₀²)^{2/3} (μ² Λ)^{1/3} F2^{2/3}` (steps 1-2 of `bessel_of_sep`, `sum_Jw_le`, Cauchy-Schwarz, `tt_star'`);
* `level_top`: with `level_lemma`, for every `0 < α < 1`,
  `∑ a_i² ≤ C_α (F2 + (μ₀² Λ)^{1-α} F2^α)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PrimeBHT.Statements

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

variable {P : ℕ} [NeZero P] {ι : Type*}
variable {F : ℝ → ZMod P → ℂ} {𝒮 : Finset ι} {C₀ : ℝ} {ℓ c a : ι → ℝ} {z : ι → ℝ → ZMod P → ℂ}
  {Ov : ι → ι → Prop}

theorem DualFam.mono (h : DualFam F 𝒮 C₀ ℓ c a z Ov) {𝒬 : Finset ι} (h𝒬 : 𝒬 ⊆ 𝒮) :
    DualFam F 𝒬 C₀ ℓ c a z Ov :=
  ⟨fun i hi => h.pos i (h𝒬 hi), fun i hi => h.nonneg i (h𝒬 hi), fun i hi => h.meas i (h𝒬 hi),
    fun i hi => h.inner_F i (h𝒬 hi), fun i hi => h.bound i (h𝒬 hi),
    fun i hi j hj => h.orth i (h𝒬 hi) j (h𝒬 hj)⟩

theorem chatF_mul_ell {i : ι} (h : 0 < ℓ i) : chatF ℓ a i * ℓ i = a i * Real.sqrt (ℓ i) := by
  unfold chatF
  rw [Real.sqrt_eq_rpow, mul_comm (ℓ i ^ _) (a i), mul_assoc, ← Real.rpow_add_one h.ne']
  norm_num

/-- **Bessel with the upper size bound only**: `S³ ≤ (16 C₀² μ)² Λ F2²`. -/
theorem bessel_upper (h : DualFam F 𝒮 C₀ ℓ c a z Ov) (hC₀ : 0 ≤ C₀) (hF : Measurable F) {B : ℝ}
    (hFb : ∀ x, yNorm 2 (F x) ≤ B) (hFint : Integrable (fun x => yNorm 2 (F x) ^ 2))
    (hsym : ∀ i ∈ 𝒮, ∀ j ∈ 𝒮, Ov i j → Ov j i)
    (hsep : ∀ i ∈ 𝒮, ∀ j ∈ 𝒮, ∀ j' ∈ 𝒮, j ≠ j' → Ov i j → Ov i j' → ℓ j ≤ ℓ i → ℓ j' ≤ ℓ i →
      Disjoint (Ico (c j - ℓ j / 2) (c j + ℓ j / 2)) (Ico (c j' - ℓ j' / 2) (c j' + ℓ j' / 2)))
    {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : ∀ i ∈ 𝒮, chatF ℓ a i ≤ μ) :
    (∑ i ∈ 𝒮, a i ^ 2) ^ 3 ≤ (16 * C₀ ^ 2 * μ) ^ 2 * (∑ i ∈ 𝒮, ℓ i) * (∫ x, yNorm 2 (F x) ^ 2) ^ 2 := by
  set S := ∑ i ∈ 𝒮, a i ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  set T := ∫ x, yNorm 2 (∑ i ∈ 𝒮, z i x) ^ 2 with hT
  set F2 := ∫ x, yNorm 2 (F x) ^ 2 with hF2
  have hF0 : 0 ≤ F2 := integral_nonneg fun x => by positivity
  have hTT := tt_star' h hC₀ hF hFb hFint
  set M : ι → ι → ℝ := fun i j => C₀ ^ 2 * (chatF ℓ a i * chatF ℓ a j) * Jw ℓ c i j with hM
  have hMnn : ∀ i ∈ 𝒮, ∀ j ∈ 𝒮, 0 ≤ M i j := fun i hi j hj =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (chatF_nonneg h hi) (chatF_nonneg h hj)))
      (Jw_nonneg h hi hj)
  have hMsymm : ∀ i j, M i j = M j i := fun i j => by
    simp only [hM, Jw_comm ℓ c i j]; ring
  have hstep1 : T ≤ ∑ i ∈ 𝒮, ∑ j ∈ 𝒮, (if Ov i j then M i j else 0) := by
    refine (integral_sq_sum_le' h hC₀).trans ?_
    refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
    by_cases hc : Ov i j
    · simp only [ite_eq_left hc]; exact integral_yy_le' h hC₀ hi hj
    · simp [hc]
  set N : ι → Finset ι := fun i => 𝒮.filter (fun j => Ov i j ∧ ℓ j ≤ ℓ i) with hN
  have hstep2 : ∑ i ∈ 𝒮, ∑ j ∈ 𝒮, (if Ov i j then M i j else 0) ≤
      2 * ∑ i ∈ 𝒮, ∑ j ∈ N i, M i j := by
    set E1 : ι → ι → ℝ := fun i j => if Ov i j ∧ ℓ j ≤ ℓ i then M i j else 0 with hE1
    have hsum1 : ∀ i, ∑ j ∈ N i, M i j = ∑ j ∈ 𝒮, E1 i j := fun i => by
      simp only [hN, hE1, Finset.sum_filter]
    have hE1nn : ∀ i ∈ 𝒮, ∀ j ∈ 𝒮, 0 ≤ E1 i j := by
      intro i hi j hj
      simp only [hE1]
      split_ifs
      · exact hMnn i hi j hj
      · exact le_rfl
    have hle : ∀ i ∈ 𝒮, ∀ j ∈ 𝒮, (if Ov i j then M i j else 0) ≤ E1 i j + E1 j i := by
      intro i hi j hj
      by_cases hc : Ov i j
      · have hc' := hsym i hi j hj hc
        rcases le_total (ℓ j) (ℓ i) with hl | hl
        · have e1 : E1 i j = M i j := by simp only [hE1]; rw [ite_eq_left ⟨hc, hl⟩]
          have := hE1nn j hj i hi
          rw [ite_eq_left hc, e1]
          linarith
        · have e1 : E1 j i = M j i := by simp only [hE1]; rw [ite_eq_left ⟨hc', hl⟩]
          have := hE1nn i hi j hj
          rw [ite_eq_left hc, e1, hMsymm j i]
          linarith
      · rw [ite_eq_right hc]
        have := hE1nn i hi j hj
        have := hE1nn j hj i hi
        linarith
    calc ∑ i ∈ 𝒮, ∑ j ∈ 𝒮, (if Ov i j then M i j else 0) ≤ ∑ i ∈ 𝒮, ∑ j ∈ 𝒮, (E1 i j + E1 j i) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hle i hi j hj
      _ = ∑ i ∈ 𝒮, ∑ j ∈ 𝒮, E1 i j + ∑ i ∈ 𝒮, ∑ j ∈ 𝒮, E1 j i := by
          simp only [Finset.sum_add_distrib]
      _ = 2 * ∑ i ∈ 𝒮, ∑ j ∈ 𝒮, E1 i j := by
          rw [Finset.sum_comm (f := fun i j => E1 j i)]; ring
      _ = 2 * ∑ i ∈ 𝒮, ∑ j ∈ N i, M i j := by
          simp only [hsum1]
  have hstep3 : ∀ i ∈ 𝒮, ∑ j ∈ N i, M i j ≤ 8 * C₀ ^ 2 * μ * (chatF ℓ a i * ℓ i) := by
    intro i hi
    have hsJ := sum_Jw_le h hsep hi
    have hci := chatF_nonneg h hi
    calc ∑ j ∈ N i, M i j = ∑ j ∈ N i, (C₀ ^ 2 * chatF ℓ a i) * (chatF ℓ a j * Jw ℓ c i j) := by
          refine Finset.sum_congr rfl fun j _ => ?_; simp only [hM]; ring
      _ = (C₀ ^ 2 * chatF ℓ a i) * ∑ j ∈ N i, chatF ℓ a j * Jw ℓ c i j := by rw [Finset.mul_sum]
      _ ≤ (C₀ ^ 2 * chatF ℓ a i) * (μ * ∑ j ∈ N i, Jw ℓ c i j) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (sq_nonneg _) hci)
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun j hj => ?_
          have hj𝒮 := (Finset.mem_filter.1 hj).1
          exact mul_le_mul_of_nonneg_right (hμ j hj𝒮) (Jw_nonneg h hi hj𝒮)
      _ ≤ (C₀ ^ 2 * chatF ℓ a i) * (μ * (8 * ℓ i)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsJ hμ0) (mul_nonneg (sq_nonneg _) hci)
      _ = _ := by ring
  set X := ∑ i ∈ 𝒮, chatF ℓ a i * ℓ i with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun i hi => mul_nonneg (chatF_nonneg h hi) (h.pos i hi).le
  have hTX : T ≤ 16 * C₀ ^ 2 * μ * X := by
    calc T ≤ 2 * ∑ i ∈ 𝒮, ∑ j ∈ N i, M i j := hstep1.trans hstep2
      _ ≤ 2 * ∑ i ∈ 𝒮, 8 * C₀ ^ 2 * μ * (chatF ℓ a i * ℓ i) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep3) (by norm_num)
      _ = 16 * C₀ ^ 2 * μ * X := by rw [hX, ← Finset.mul_sum]; ring
  have hXsq : X ^ 2 ≤ S * ∑ i ∈ 𝒮, ℓ i := by
    have e : X = ∑ i ∈ 𝒮, a i * Real.sqrt (ℓ i) :=
      Finset.sum_congr rfl fun i hi => chatF_mul_ell (h.pos i hi)
    rw [e]
    refine (Finset.sum_mul_sq_le_sq_mul_sq 𝒮 a fun i => Real.sqrt (ℓ i)).trans (le_of_eq ?_)
    congr 1
    exact Finset.sum_congr rfl fun i hi => Real.sq_sqrt (h.pos i hi).le
  have hc0 : 0 ≤ 16 * C₀ ^ 2 * μ := by positivity
  have h1 : S ^ 2 ≤ 16 * C₀ ^ 2 * μ * X * F2 :=
    hTT.trans (mul_le_mul_of_nonneg_right hTX hF0)
  have h2 : S ^ 4 ≤ (16 * C₀ ^ 2 * μ) ^ 2 * (S * ∑ i ∈ 𝒮, ℓ i) * F2 ^ 2 := by
    have := pow_le_pow_left₀ (sq_nonneg S) h1 2
    calc S ^ 4 = (S ^ 2) ^ 2 := by ring
      _ ≤ (16 * C₀ ^ 2 * μ * X * F2) ^ 2 := this
      _ = (16 * C₀ ^ 2 * μ) ^ 2 * X ^ 2 * F2 ^ 2 := by ring
      _ ≤ (16 * C₀ ^ 2 * μ) ^ 2 * (S * ∑ i ∈ 𝒮, ℓ i) * F2 ^ 2 := by gcongr
  rcases eq_or_lt_of_le hS0 with hS00 | hSpos
  · rw [← hS00]
    have : 0 ≤ ∑ i ∈ 𝒮, ℓ i := Finset.sum_nonneg fun i hi => (h.pos i hi).le
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  · have h3 : S * S ^ 3 ≤ S * ((16 * C₀ ^ 2 * μ) ^ 2 * (∑ i ∈ 𝒮, ℓ i) * F2 ^ 2) := by
      calc S * S ^ 3 = S ^ 4 := by ring
        _ ≤ _ := h2
        _ = _ := by ring
    exact le_of_mul_le_mul_left h3 hSpos

theorem cube_root_bound {S x y w : ℝ} (hS : 0 ≤ S) (hx : 0 ≤ x) (hy : 0 ≤ y) (hw : 0 ≤ w)
    (h : S ^ 3 ≤ x ^ 2 * y * w ^ 2) :
    S ≤ x ^ ((2 : ℝ) / 3) * y ^ ((1 : ℝ) / 3) * w ^ ((2 : ℝ) / 3) := by
  have h1 := Real.rpow_le_rpow (pow_nonneg hS 3) h (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have e1 : (S ^ 3) ^ ((1 : ℝ) / 3) = S := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS]; norm_num
  have e2 : ∀ u : ℝ, 0 ≤ u → (u ^ 2) ^ ((1 : ℝ) / 3) = u ^ ((2 : ℝ) / 3) := fun u hu => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu]; norm_num
  rwa [e1, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hy, e2 x hx,
    e2 w hw] at h1

/-- The constant of the basic estimate. -/
def topBasicK (C₀ : ℝ) : ℝ := max 1 ((16 * C₀ ^ 2) ^ ((2 : ℝ) / 3))

/-- The constant of the `(1-α)` form. -/
def topLevelC (C₀ α : ℝ) : ℝ := 6 * topBasicK C₀ ^ 2 * (3 + 1 / ((1 - α) * Real.log 2))

theorem topLevelC_nonneg (C₀ : ℝ) {α : ℝ} (hα1 : α < 1) : 0 ≤ topLevelC C₀ α := by
  unfold topLevelC
  have : 0 < (1 - α) * Real.log 2 := mul_pos (by linarith) (Real.log_pos (by norm_num))
  positivity

/-- **TB-4a: the Hilbert `(1-α)` form for a separated dual family** (upper size bound `μ₀` only). -/
theorem level_top (h : DualFam F 𝒮 C₀ ℓ c a z Ov) (hC₀ : 0 ≤ C₀) (hF : Measurable F) {B : ℝ}
    (hFb : ∀ x, yNorm 2 (F x) ≤ B) (hFint : Integrable (fun x => yNorm 2 (F x) ^ 2))
    (hsym : ∀ i ∈ 𝒮, ∀ j ∈ 𝒮, Ov i j → Ov j i)
    (hsep : ∀ i ∈ 𝒮, ∀ j ∈ 𝒮, ∀ j' ∈ 𝒮, j ≠ j' → Ov i j → Ov i j' → ℓ j ≤ ℓ i → ℓ j' ≤ ℓ i →
      Disjoint (Ico (c j - ℓ j / 2) (c j + ℓ j / 2)) (Ico (c j' - ℓ j' / 2) (c j' + ℓ j' / 2)))
    {μ₀ : ℝ} (hμ₀ : 0 ≤ μ₀) (hμ : ∀ i ∈ 𝒮, chatF ℓ a i ≤ μ₀) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∑ i ∈ 𝒮, a i ^ 2 ≤ topLevelC C₀ α * ((∫ x, yNorm 2 (F x) ^ 2) +
      (μ₀ ^ 2 * ∑ i ∈ 𝒮, ℓ i) ^ (1 - α) * (∫ x, yNorm 2 (F x) ^ 2) ^ α) := by
  set F2 := ∫ x, yNorm 2 (F x) ^ 2 with hF2
  set L := ∑ i ∈ 𝒮, ℓ i with hL
  have hF0 : 0 ≤ F2 := integral_nonneg fun x => by positivity
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun i hi => (h.pos i hi).le
  have hS0 : 0 ≤ ∑ i ∈ 𝒮, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hR0 : 0 ≤ topLevelC C₀ α * (F2 + (μ₀ ^ 2 * L) ^ (1 - α) * F2 ^ α) :=
    mul_nonneg (topLevelC_nonneg C₀ hα1) (by positivity)
  have hbu := bessel_upper h hC₀ hF hFb hFint hsym hsep hμ₀ hμ
  by_cases hdeg : F2 = 0 ∨ L = 0
  · have h0 : (∑ i ∈ 𝒮, a i ^ 2) ^ 3 ≤ 0 := by
      rcases hdeg with h0 | h0
      · rw [← hF2, h0] at hbu; simpa using hbu
      · rw [← hL, h0] at hbu; simpa using hbu
    have : ∑ i ∈ 𝒮, a i ^ 2 = 0 := by
      by_contra hne
      have := pow_pos (lt_of_le_of_ne hS0 (Ne.symm hne)) 3
      linarith
    rw [this]; exact hR0
  push Not at hdeg
  have hK1 : 1 ≤ topBasicK C₀ := le_max_left _ _
  have hlev := level_lemma (𝒮 := 𝒮) (ℓ := ℓ) (c := chatF ℓ a) (K := topBasicK C₀) (F2 := F2) (L := L)
    (μ₀ := μ₀) hK1 (lt_of_le_of_ne hF0 (Ne.symm hdeg.1)) (lt_of_le_of_ne hL0 (Ne.symm hdeg.2)) hμ₀ hα0 hα1
    (fun i hi => h.pos i hi) hμ (by
      intro 𝒬 h𝒬 μ hμ0 hμ𝒬
      have hb := bessel_upper (h.mono h𝒬) hC₀ hF hFb hFint (fun i hi j hj => hsym i (h𝒬 hi) j (h𝒬 hj))
        (fun i hi j hj j' hj' => hsep i (h𝒬 hi) j (h𝒬 hj) j' (h𝒬 hj')) hμ0 hμ𝒬
      have hL𝒬 : ∑ i ∈ 𝒬, ℓ i ≤ L :=
        Finset.sum_le_sum_of_subset_of_nonneg h𝒬 fun i hi _ => (h.pos i hi).le
      have hL𝒬0 : 0 ≤ ∑ i ∈ 𝒬, ℓ i := Finset.sum_nonneg fun i hi => (h.pos i (h𝒬 hi)).le
      rw [min_eq_right hL𝒬]
      have e : ∑ i ∈ 𝒬, ℓ i * chatF ℓ a i ^ 2 = ∑ i ∈ 𝒬, a i ^ 2 :=
        Finset.sum_congr rfl fun i hi => ell_mul_chatF_sq (h.pos i (h𝒬 hi)) a
      rw [e]
      have hb' : (∑ i ∈ 𝒬, a i ^ 2) ^ 3 ≤ (16 * C₀ ^ 2) ^ 2 * (μ ^ 2 * ∑ i ∈ 𝒬, ℓ i) * F2 ^ 2 := by
        refine hb.trans (le_of_eq ?_); ring
      have hcr := cube_root_bound (Finset.sum_nonneg fun i _ => sq_nonneg _) (by positivity) (by positivity)
        hF0 hb'
      have hK : (16 * C₀ ^ 2) ^ ((2 : ℝ) / 3) ≤ topBasicK C₀ := le_max_right _ _
      calc ∑ i ∈ 𝒬, a i ^ 2 ≤ (16 * C₀ ^ 2) ^ ((2 : ℝ) / 3) * (μ ^ 2 * ∑ i ∈ 𝒬, ℓ i) ^ ((1 : ℝ) / 3) *
            F2 ^ ((2 : ℝ) / 3) := hcr
        _ ≤ topBasicK C₀ * ((μ ^ 2 * ∑ i ∈ 𝒬, ℓ i) ^ ((1 : ℝ) / 3) * F2 ^ ((2 : ℝ) / 3)) := by
            rw [mul_assoc]; gcongr
        _ ≤ topBasicK C₀ * (F2 + (μ ^ 2 * ∑ i ∈ 𝒬, ℓ i) ^ ((1 : ℝ) / 3) * F2 ^ ((2 : ℝ) / 3)) := by
            gcongr; linarith)
  have e : ∑ i ∈ 𝒮, ℓ i * chatF ℓ a i ^ 2 = ∑ i ∈ 𝒮, a i ^ 2 :=
    Finset.sum_congr rfl fun i hi => ell_mul_chatF_sq (h.pos i hi) a
  rw [e] at hlev
  exact hlev

end PrimeBHT.TimeFrequency.X2
