module

public import PrimeBHT.TimeFrequency.X2.TopEnergy.NHValue

/-!
# X2, TB-4c: the slot-3 `pint`-form for separated top families

`family_qX_bound`: for a shell-separated family of one-sided top data `(W_V, ξ_V, ψ_V, m_V)` (the separation produced by
the greedy selection, `ShellSep`), every measurable `F` with `yNorm s F ≤ 1`, `mixedPow qX s F < ⊤`, and every `ε > 0`:

  `∑_V ‖ψ_V T_{m_V} F‖^{qX}_{L^{qX}(L^s)} ≤ Cinf^{qX-2} · 2 C_α ((2/5 C₁)² ε Λ + (1 + ε^{-(1-α)/α}) M)`

(`Λ = ∑ |W_V|`, `M = ∫ yNorm s (F)^{qX}`).  Proof: `theoremI_meas` for the kernels `topKer ψ_V m_V`, with the Hilbert
hypothesis on step functions from `level_top` (TB-4a, applied to `topDualFam` of the step function) and Young's inequality
`x^{1-α} y^α ≤ ε x + ε^{-(1-α)/α} y`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal
open PrimeBHT.Statements

set_option autoImplicit false

open Classical

namespace PrimeBHT.TimeFrequency.X2

variable {P : ℕ} [NeZero P]

/-- Young's inequality in the form used for the HLC intersection form. -/
theorem young_split {x y ε α : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hε : 0 < ε) (hα0 : 0 < α) (hα1 : α < 1) :
    x ^ (1 - α) * y ^ α ≤ ε * x + ε ^ (-((1 - α) / α)) * y := by
  have hβ : 0 ≤ ε ^ (-((1 - α) / α)) := (Real.rpow_pos_of_pos hε _).le
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 - α) (w₂ := α) (p₁ := ε * x)
    (p₂ := ε ^ (-((1 - α) / α)) * y) (by linarith) hα0.le (by positivity) (by positivity) (by ring)
  have e : (ε * x) ^ (1 - α) * (ε ^ (-((1 - α) / α)) * y) ^ α = x ^ (1 - α) * y ^ α := by
    rw [Real.mul_rpow hε.le hx, Real.mul_rpow hβ hy, ← Real.rpow_mul hε.le]
    have : ε ^ (1 - α) * ε ^ (-((1 - α) / α) * α) = 1 := by
      rw [← Real.rpow_add hε, show 1 - α + -((1 - α) / α) * α = 0 by field_simp; ring, Real.rpow_zero]
    calc ε ^ (1 - α) * x ^ (1 - α) * (ε ^ (-((1 - α) / α) * α) * y ^ α) =
        (ε ^ (1 - α) * ε ^ (-((1 - α) / α) * α)) * (x ^ (1 - α) * y ^ α) := by ring
      _ = _ := by rw [this, one_mul]
  rw [e] at h
  have h1 : (1 - α) * (ε * x) ≤ ε * x := by nlinarith [mul_nonneg hε.le hx]
  have h2 : α * (ε ^ (-((1 - α) / α)) * y) ≤ ε ^ (-((1 - α) / α)) * y := by
    nlinarith [mul_nonneg hβ hy]
  linarith

/-! ## Step functions -/

omit [NeZero P] in
theorem measurable_stepFun {κ : Type*} [Fintype κ] {E : κ → Set ℝ} (hE : ∀ k, MeasurableSet (E k))
    (v : κ → ZMod P → ℂ) : Measurable (Pint.stepFun E v) :=
  measurable_pi_iff.2 fun _y => Finset.measurable_sum _ fun k _ =>
    (measurable_const.indicator (hE k)).mul measurable_const

theorem yNorm_stepFun_rpow {κ : Type*} [Fintype κ] {E : κ → Set ℝ}
    (hd : Pairwise fun k k' => Disjoint (E k) (E k')) (v : κ → ZMod P → ℂ) {p q : ℝ} (hp : 0 < p) (hq : q ≠ 0)
    (w : ℝ) : yNorm p (Pint.stepFun E v w) ^ q = ∑ k, (E k).indicator (fun _ => yNorm p (v k) ^ q) w := by
  by_cases h : ∃ k, w ∈ E k
  · obtain ⟨k, hk⟩ := h
    rw [Pint.stepFun_eq_of_mem hd _ hk, Finset.sum_eq_single k]
    · rw [Set.indicator_of_mem hk]
    · intro j _ hj
      exact Set.indicator_of_notMem (fun h => Set.disjoint_left.1 (hd hj) h hk) _
    · simp
  · push Not at h
    rw [Pint.stepFun_eq_zero _ h, yNorm_zero_of_pos hp, Real.zero_rpow hq]
    exact (Finset.sum_eq_zero fun k _ => Set.indicator_of_notMem (h k) _).symm

theorem integrable_yNorm_stepFun_rpow {κ : Type*} [Fintype κ] {E : κ → Set ℝ} (hE : Pint.IsStepData E)
    (v : κ → ZMod P → ℂ) {p q : ℝ} (hp : 0 < p) (hq : q ≠ 0) :
    Integrable fun w => yNorm p (Pint.stepFun E v w) ^ q := by
  simp_rw [yNorm_stepFun_rpow hE.2.2 v hp hq]
  exact integrable_finset_sum _ fun k _ =>
    (integrable_indicator_iff (hE.1 k)).2 (integrableOn_const (hE.2.1 k).ne)

/-! ## The family bound -/

/-- The separation of a selected family (the `hsep` of `round_selection`, produced by `top_separation_pair_H`). -/
def ShellSep (σ : ℝ) (k : Fin 3) (𝒮 : Finset TopSel) : Prop :=
  ∀ i ∈ 𝒮, ∀ j ∈ 𝒮, ∀ j' ∈ 𝒮, j ≠ j' →
    (Icc (shellLo σ k i.W (σ * i.ξ)) (shellUp σ k i.W (σ * i.ξ)) ∩
      Icc (shellLo σ k j.W (σ * j.ξ)) (shellUp σ k j.W (σ * j.ξ))).Nonempty →
    (Icc (shellLo σ k i.W (σ * i.ξ)) (shellUp σ k i.W (σ * i.ξ)) ∩
      Icc (shellLo σ k j'.W (σ * j'.ξ)) (shellUp σ k j'.W (σ * j'.ξ))).Nonempty →
    (2 : ℝ) ^ j.W.1 ≤ (2 : ℝ) ^ i.W.1 → (2 : ℝ) ^ j'.W.1 ≤ (2 : ℝ) ^ i.W.1 →
    Disjoint (Ico (dyCentre j.W.1 j.W.2 - (2 : ℝ) ^ j.W.1 / 2) (dyCentre j.W.1 j.W.2 + (2 : ℝ) ^ j.W.1 / 2))
      (Ico (dyCentre j'.W.1 j'.W.2 - (2 : ℝ) ^ j'.W.1 / 2) (dyCentre j'.W.1 j'.W.2 + (2 : ℝ) ^ j'.W.1 / 2))

/-- The Hilbert endpoint (HLC intersection form) for a separated family, for measurable `G` with
`yNorm 2 G ≤ B₀`, `∫ yNorm 2 G² < ∞`, and every `ε > 0`. -/
theorem family_hilbert (𝔭 : Params) (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) (hC : 0 ≤ 𝔭.C) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (k : Fin 3) {𝒮 : Finset TopSel} {ψ m : TopSel → ℝ → ℂ}
    (hψ : ∀ V ∈ 𝒮, InPsi 𝔭 V.W.1 V.W.2 (ψ V)) (hm : ∀ V ∈ 𝒮, InTopMultS 𝔭 σ V.W (σ * V.ξ) k (m V))
    (hsep : ShellSep σ k 𝒮) {α ε : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hε : 0 < ε)
    {G : ℝ → ZMod P → ℂ} (hG : Measurable G) {B₀ : ℝ} (hB₀ : ∀ x, yNorm 2 (G x) ≤ B₀)
    (hGint : Integrable (fun x => yNorm 2 (G x) ^ 2)) :
    ∑ V ∈ 𝒮, ∫ x, yNorm 2 (ψ V x • tmult (m V) G x) ^ 2 ≤
      (Real.sqrt (topLevelC (topC₁ 𝔭) α * ε * ∑ V ∈ 𝒮, (2 : ℝ) ^ V.W.1) * (2 / 5 * topC₁ 𝔭) * B₀ +
        Real.sqrt (topLevelC (topC₁ 𝔭) α * (1 + ε ^ (-((1 - α) / α)))) *
          (∫ x, yNorm 2 (G x) ^ 2) ^ ((1 : ℝ) / 2)) ^ 2 := by
  have hcls := fun V (hV : V ∈ 𝒮) => topData_classes hσ (hψ V hV) (hm V hV)
  have hfam := topDualFam (ι := TopSel) (F := G) 𝒮 (fun V => V.W) (fun V => shellC σ k V.W (σ * V.ξ))
    (fun V => shellLo σ k V.W (σ * V.ξ)) (fun V => shellUp σ k V.W (σ * V.ξ)) ψ m
    (𝔭 := 𝔭.shellCls) (by simpa using hN) (by simpa using hD) (by norm_num)
    (fun V hV => (hcls V hV).1) (fun V hV => (hcls V hV).2.1) (fun V hV => (hcls V hV).2.2) hG hB₀
  have e' : 2 ^ 13 * 𝔭.shellCls.β * 𝔭.shellCls.C * 𝔭.shellCls.C = topC₁ 𝔭 := by
    simp only [Params.shellCls_β, Params.shellCls_C, topC₁]
  rw [e'] at hfam
  have hC₁ := topC₁_nonneg hC
  have hB₀0 : 0 ≤ B₀ := (Pint.yNorm_nonneg 2 (G 0)).trans (hB₀ 0)
  have hsym : ∀ i ∈ 𝒮, ∀ j ∈ 𝒮, (Icc (shellLo σ k i.W (σ * i.ξ)) (shellUp σ k i.W (σ * i.ξ)) ∩
      Icc (shellLo σ k j.W (σ * j.ξ)) (shellUp σ k j.W (σ * j.ξ))).Nonempty →
      (Icc (shellLo σ k j.W (σ * j.ξ)) (shellUp σ k j.W (σ * j.ξ)) ∩
        Icc (shellLo σ k i.W (σ * i.ξ)) (shellUp σ k i.W (σ * i.ξ))).Nonempty :=
    fun i _ j _ ⟨x, hx1, hx2⟩ => ⟨x, hx2, hx1⟩
  set μ₀ := 2 / 5 * topC₁ 𝔭 * B₀ with hμ₀
  have hμ : ∀ V ∈ 𝒮, chatF (fun V : TopSel => (2 : ℝ) ^ V.W.1) (fun V => va (ψ V) (m V) G) V ≤ μ₀ :=
    fun V hV => chatTop_le hN hD hσ (hψ V hV) (hm V hV) hG hB₀ hC
  have hlev := level_top hfam hC₁ hG hB₀ hGint hsym hsep (by positivity) hμ hα0 hα1
  set Cα := topLevelC (topC₁ 𝔭) α with hCα
  have hCα0 : 0 ≤ Cα := topLevelC_nonneg _ hα1
  set L := ∑ V ∈ 𝒮, (2 : ℝ) ^ V.W.1 with hL
  set F2 := ∫ x, yNorm 2 (G x) ^ 2 with hF2
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun V _ => (zpow_pos (by norm_num) _).le
  have hF0 : 0 ≤ F2 := integral_nonneg fun x => by positivity
  have hva : ∀ V, va (ψ V) (m V) G ^ 2 = ∫ x, yNorm 2 (ψ V x • tmult (m V) G x) ^ 2 := fun V =>
    Real.sq_sqrt (integral_nonneg fun x => by positivity)
  simp only [hva] at hlev
  have hy := young_split (x := μ₀ ^ 2 * L) (y := F2) (by positivity) hF0 hε hα0 hα1
  set eβ := ε ^ (-((1 - α) / α)) with heβ
  have heβ0 : 0 ≤ eβ := (Real.rpow_pos_of_pos hε _).le
  refine hlev.trans ?_
  have hsq1 : Real.sqrt (Cα * ε * L) ^ 2 = Cα * ε * L := Real.sq_sqrt (by positivity)
  have hsq2 : Real.sqrt (Cα * (1 + eβ)) ^ 2 = Cα * (1 + eβ) := Real.sq_sqrt (by positivity)
  have hsq3 : (F2 ^ ((1 : ℝ) / 2)) ^ 2 = F2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hF0]; norm_num
  have hx0 : 0 ≤ Real.sqrt (Cα * ε * L) * (2 / 5 * topC₁ 𝔭) * B₀ := by positivity
  have hy0 : 0 ≤ Real.sqrt (Cα * (1 + eβ)) * F2 ^ ((1 : ℝ) / 2) := by positivity
  calc Cα * (F2 + (μ₀ ^ 2 * L) ^ (1 - α) * F2 ^ α) ≤ Cα * (F2 + (ε * (μ₀ ^ 2 * L) + eβ * F2)) := by gcongr
    _ = (Real.sqrt (Cα * ε * L) * (2 / 5 * topC₁ 𝔭) * B₀) ^ 2 +
          (Real.sqrt (Cα * (1 + eβ)) * F2 ^ ((1 : ℝ) / 2)) ^ 2 := by
        have e1 : (Real.sqrt (Cα * ε * L) * (2 / 5 * topC₁ 𝔭) * B₀) ^ 2 =
            Real.sqrt (Cα * ε * L) ^ 2 * (2 / 5 * topC₁ 𝔭) ^ 2 * B₀ ^ 2 := by ring
        have e2 : (Real.sqrt (Cα * (1 + eβ)) * F2 ^ ((1 : ℝ) / 2)) ^ 2 =
            Real.sqrt (Cα * (1 + eβ)) ^ 2 * (F2 ^ ((1 : ℝ) / 2)) ^ 2 := by ring
        rw [e1, e2, hsq1, hsq2, hsq3, hμ₀]; ring
    _ ≤ _ := by linarith only [mul_nonneg hx0 hy0]

/-- **TB-4c**: `theoremI_meas` for a separated top family at `(s, qX)`. -/
theorem family_qX_bound (𝔭 : Params) (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) (hC : 0 ≤ 𝔭.C) {s qX : ℝ}
    (hE : 1 < s ∧ s < qX ∧ s / (s - 1) < qX) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (k : Fin 3)
    {𝒮 : Finset TopSel} {ψ m : TopSel → ℝ → ℂ}
    (hψ : ∀ V ∈ 𝒮, InPsi 𝔭 V.W.1 V.W.2 (ψ V)) (hm : ∀ V ∈ 𝒮, InTopMultS 𝔭 σ V.W (σ * V.ξ) k (m V))
    (hsep : ShellSep σ k 𝒮) {α ε : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hε : 0 < ε)
    {F : ℝ → ZMod P → ℂ} (hF : Measurable F) (hB : ∀ x, yNorm s (F x) ≤ 1)
    (hM : mixedPow qX s F ≠ ⊤) :
    ∑ V ∈ 𝒮, ∫⁻ x, ENNReal.ofReal (yNorm s (ψ V x • tmult (m V) F x) ^ qX) ≤
      ENNReal.ofReal (topCinf 𝔭 ^ (qX - 2)) *
        ENNReal.ofReal ((Real.sqrt (topLevelC (topC₁ 𝔭) α * ε * ∑ V ∈ 𝒮, (2 : ℝ) ^ V.W.1) * (2 / 5 * topC₁ 𝔭) +
          Real.sqrt (topLevelC (topC₁ 𝔭) α * (1 + ε ^ (-((1 - α) / α)))) *
            (∫ x, yNorm s (F x) ^ qX) ^ ((1 : ℝ) / 2)) ^ 2) := by
  have h := Pint.theoremI_meas (ι := ↥𝒮) (K := fun V => topKer (ψ V) (m V)) (Cinf := topCinf 𝔭)
    (A := Real.sqrt (topLevelC (topC₁ 𝔭) α * ε * ∑ V ∈ 𝒮, (2 : ℝ) ^ V.W.1) * (2 / 5 * topC₁ 𝔭))
    (B₂ := Real.sqrt (topLevelC (topC₁ 𝔭) α * (1 + ε ^ (-((1 - α) / α))))) hE (topCinf_nonneg hC)
    (fun V => stronglyMeasurable_topKer (hψ V V.2).1 (continuous_fourierInv_inTopMult (hm V V.2).1))
    (fun V x => lintegral_topKer_le (by omega) hC (hψ V V.2) (hm V V.2).1 x) ?_ hF hB hM
  · simp only [kernelOp_topKer, Real.one_rpow, mul_one] at h
    rwa [Finset.sum_coe_sort 𝒮
      (fun V => ∫⁻ x, ENNReal.ofReal (yNorm s (ψ V x • tmult (m V) F x) ^ qX))] at h
  intro κ _ v E hEd B₀ hB₀
  simp only [kernelOp_topKer]
  rw [Finset.sum_coe_sort 𝒮
    (fun V => ∫⁻ x, ENNReal.ofReal (yNorm 2 (ψ V x • tmult (m V) (Pint.stepFun E v) x) ^ 2))]
  have hGm := measurable_stepFun hEd.1 v
  have hGint : Integrable fun x => yNorm 2 (Pint.stepFun E v x) ^ 2 :=
    (integrable_yNorm_stepFun_rpow hEd v two_pos two_ne_zero).congr
      (ae_of_all _ fun w => Real.rpow_two _)
  have hfh := family_hilbert 𝔭 hN hD hC hσ k hψ hm hsep hα0 hα1 hε hGm hB₀ hGint
  have hpiece : ∀ V ∈ 𝒮, ∫⁻ x, ENNReal.ofReal (yNorm 2 (ψ V x • tmult (m V) (Pint.stepFun E v) x) ^ 2) =
      ENNReal.ofReal (∫ x, yNorm 2 (ψ V x • tmult (m V) (Pint.stepFun E v) x) ^ 2) := by
    intro V hV
    obtain ⟨c1, c2, -⟩ := topData_classes hσ (hψ V hV) (hm V hV)
    exact (ofReal_integral_eq_lintegral_ofReal (integrable_piece_sq (𝔭 := 𝔭.shellCls)
      (by simpa using hN) (by simpa using hD) (by norm_num) c1 c2 hGm hB₀)
      (ae_of_all _ fun x => by positivity)).symm
  rw [Finset.sum_congr rfl hpiece, ← ENNReal.ofReal_sum_of_nonneg fun V _ =>
    integral_nonneg fun x => by positivity]
  exact ENNReal.ofReal_le_ofReal hfh

/-- The closing real algebra of the count (`ε = d/(2K)`). -/
theorem count_real_top {L d M K β dmax : ℝ} (_hL : 0 ≤ L) (hd : 0 < d) (hdm : d ≤ dmax) (hK : 0 < K)
    (hβ : 0 ≤ β) (hM : 0 ≤ M) (h : ∀ ε > 0, L * d ≤ K * ε * L + K * (1 + ε ^ (-β)) * M) :
    L * d ^ (1 + β) ≤ 2 * K * (dmax ^ β + (2 * K) ^ β) * M := by
  have h1 := h (d / (2 * K)) (by positivity)
  have e1 : K * (d / (2 * K)) * L = L * d / 2 := by field_simp
  rw [e1] at h1
  have h2 : L * d ≤ 2 * K * (1 + (d / (2 * K)) ^ (-β)) * M := by linarith
  have e2 : d ^ β * (d / (2 * K)) ^ (-β) = (2 * K) ^ β := by
    rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div,
      ← Real.mul_rpow hd.le (by positivity)]
    congr 1; field_simp
  have hdβ : 0 ≤ d ^ β := Real.rpow_nonneg hd.le _
  calc L * d ^ (1 + β) = (L * d) * d ^ β := by rw [Real.rpow_add hd, Real.rpow_one]; ring
    _ ≤ (2 * K * (1 + (d / (2 * K)) ^ (-β)) * M) * d ^ β := mul_le_mul_of_nonneg_right h2 hdβ
    _ = 2 * K * (d ^ β + d ^ β * (d / (2 * K)) ^ (-β)) * M := by ring
    _ = 2 * K * (d ^ β + (2 * K) ^ β) * M := by rw [e2]
    _ ≤ 2 * K * (dmax ^ β + (2 * K) ^ β) * M := by
        gcongr

/-- The constant `K₁` of the family count. -/
def topFamK (𝔭 : Params) (qX q : ℝ) : ℝ :=
  2 * topCinf 𝔭 ^ (qX - 2) * topLevelC (topC₁ 𝔭) (qX / q) * ((2 / 5 * topC₁ 𝔭) ^ 2 + 1)

/-- The constant of the family count. -/
def topFamC (𝔭 : Params) (qX q dmax : ℝ) : ℝ :=
  2 * topFamK 𝔭 qX q * (dmax ^ (q / qX - 1) + (2 * topFamK 𝔭 qX q) ^ (q / qX - 1))

/-- **The family count** (TB-4b/c): if every member of a separated family has
`|W_V| d ≤ ‖ψ_V T_{m_V} F‖^{qX}_{L^{qX}(L^s)}` then `(∑ |W_V|) d^{q/qX} ≤ topFamC · M`. -/
theorem family_count (𝔭 : Params) (hN : 12 ≤ 𝔭.N) (hD : 12 ≤ 𝔭.D) (hC1 : 1 ≤ 𝔭.C) {s qX q : ℝ}
    (hE : 1 < s ∧ s < qX ∧ s / (s - 1) < qX) (hq : qX < q) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (k : Fin 3)
    {𝒮 : Finset TopSel} {ψ m : TopSel → ℝ → ℂ}
    (hψ : ∀ V ∈ 𝒮, InPsi 𝔭 V.W.1 V.W.2 (ψ V)) (hm : ∀ V ∈ 𝒮, InTopMultS 𝔭 σ V.W (σ * V.ξ) k (m V))
    (hsep : ShellSep σ k 𝒮) {F : ℝ → ZMod P → ℂ} (hF : Measurable F) (hB : ∀ x, yNorm s (F x) ≤ 1)
    (hM : mixedPow qX s F ≠ ⊤) {d dmax : ℝ} (hd : 0 < d) (hdm : d ≤ dmax)
    (hcand : ∀ V ∈ 𝒮, ENNReal.ofReal ((2 : ℝ) ^ V.W.1 * d) ≤
      ∫⁻ x, ENNReal.ofReal (yNorm s (ψ V x • tmult (m V) F x) ^ qX)) :
    (∑ V ∈ 𝒮, (2 : ℝ) ^ V.W.1) * d ^ (q / qX) ≤ topFamC 𝔭 qX q dmax * ∫ x, yNorm s (F x) ^ qX := by
  have hC : 0 ≤ 𝔭.C := by linarith
  have hq2 := Pint.two_lt_qX hE
  have hq0 : 0 < qX := by linarith
  set α := qX / q with hα
  have hα0 : 0 < α := div_pos hq0 (by linarith)
  have hα1 : α < 1 := (div_lt_one (by linarith)).2 hq
  set L := ∑ V ∈ 𝒮, (2 : ℝ) ^ V.W.1 with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun V _ => (zpow_pos (by norm_num) _).le
  set M := ∫ x, yNorm s (F x) ^ qX with hMdef
  have hM0 : 0 ≤ M := integral_nonneg fun x => Real.rpow_nonneg (Pint.yNorm_nonneg _ _) _
  set Cα := topLevelC (topC₁ 𝔭) α with hCα
  have hCα0 : 0 ≤ Cα := topLevelC_nonneg _ hα1
  have hCi : 0 < topCinf 𝔭 := by unfold topCinf topRad; positivity
  have hCiq : 0 < topCinf 𝔭 ^ (qX - 2) := Real.rpow_pos_of_pos hCi _
  have hKpos : 0 < topFamK 𝔭 qX q := by
    unfold topFamK
    have : 0 < topLevelC (topC₁ 𝔭) (qX / q) := by
      unfold topLevelC topBasicK
      have : 0 < (1 - qX / q) * Real.log 2 := mul_pos (by linarith) (Real.log_pos (by norm_num))
      positivity
    positivity
  have hq0' : q ≠ 0 := by linarith
  have hβ : (1 - α) / α = q / qX - 1 := by rw [hα]; field_simp
  have key : ∀ ε > 0, L * d ≤ topFamK 𝔭 qX q * ε * L + topFamK 𝔭 qX q * (1 + ε ^ (-(q / qX - 1))) * M := by
    intro ε hε
    have hb := family_qX_bound 𝔭 hN hD hC hE hσ k hψ hm hsep hα0 hα1 hε hF hB hM
    rw [hβ] at hb
    have hlow : ENNReal.ofReal (L * d) ≤ ∑ V ∈ 𝒮, ∫⁻ x, ENNReal.ofReal (yNorm s (ψ V x • tmult (m V) F x) ^ qX) := by
      rw [hL, Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun V _ => by positivity]
      exact Finset.sum_le_sum hcand
    have h2 := hlow.trans hb
    rw [← ENNReal.ofReal_mul hCiq.le, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
    set A := Real.sqrt (Cα * ε * L) * (2 / 5 * topC₁ 𝔭) with hA
    set B₂ := Real.sqrt (Cα * (1 + ε ^ (-(q / qX - 1)))) with hB₂
    have hsqA : A ^ 2 = Cα * ε * L * (2 / 5 * topC₁ 𝔭) ^ 2 := by
      rw [hA, mul_pow, Real.sq_sqrt (by positivity)]
    have hsqB : (B₂ * M ^ ((1 : ℝ) / 2)) ^ 2 = Cα * (1 + ε ^ (-(q / qX - 1))) * M := by
      rw [hB₂, mul_pow, Real.sq_sqrt (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hM0]
      norm_num
    have hsq : (A + B₂ * M ^ ((1 : ℝ) / 2)) ^ 2 ≤ 2 * A ^ 2 + 2 * (B₂ * M ^ ((1 : ℝ) / 2)) ^ 2 := by
      linarith only [sq_nonneg (A - B₂ * M ^ ((1 : ℝ) / 2))]
    have hε0 : 0 ≤ ε ^ (-(q / qX - 1)) := (Real.rpow_pos_of_pos hε _).le
    calc L * d ≤ topCinf 𝔭 ^ (qX - 2) * (A + B₂ * M ^ ((1 : ℝ) / 2)) ^ 2 := h2
      _ ≤ topCinf 𝔭 ^ (qX - 2) * (2 * A ^ 2 + 2 * (B₂ * M ^ ((1 : ℝ) / 2)) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hCiq.le
      _ = topFamK 𝔭 qX q * ε * L * ((2 / 5 * topC₁ 𝔭) ^ 2 / ((2 / 5 * topC₁ 𝔭) ^ 2 + 1)) +
            topFamK 𝔭 qX q * (1 + ε ^ (-(q / qX - 1))) * M * (1 / ((2 / 5 * topC₁ 𝔭) ^ 2 + 1)) := by
          rw [hsqA, hsqB, topFamK, ← hα, ← hCα]; field_simp
      _ ≤ topFamK 𝔭 qX q * ε * L * 1 + topFamK 𝔭 qX q * (1 + ε ^ (-(q / qX - 1))) * M * 1 := by
          gcongr
          · rw [div_le_one (by positivity)]; linarith
          · rw [div_le_one (by positivity)]; linarith only [sq_nonneg (2 / 5 * topC₁ 𝔭)]
      _ = _ := by ring
  have hβ0 : 0 ≤ q / qX - 1 := by rw [sub_nonneg, le_div_iff₀ hq0]; linarith
  have hc := count_real_top hL0 hd hdm hKpos hβ0 hM0 key
  rwa [show 1 + (q / qX - 1) = q / qX by ring] at hc

end PrimeBHT.TimeFrequency.X2
