module

public import PrimeBHT.TransferenceAssembly.FinalBound
public import PrimeBHT.TransferenceAssembly.ChartCover
public import PrimeBHT.TransferenceAssembly.Duality
public import PrimeBHT.TransferenceAssembly.KernelData
public import PrimeBHT.BlockSum.Basic
public import PrimeBHT.PeriodicAssembly.Interp
public import PrimeBHT.PeriodicBlock.L2Norm

/-!
# N43(a): the per-block transference `BlockTransferBound`, conditional on X2 and the kernel data

`blockTransferBound_of_x2_of_kernelData` assembles the verified pieces
(`exists_norm_tsum_tsum_chartProj_le_lp_of_x2`, `ChartCover`, the alias facts, the `ℓ¹` duality
`summable_and_tsum_norm_le_of_chart_bounds_of_finite_support`) into the hypothesis
`PrimeBHT.BlockSum.BlockTransferBound φ c χ τ ε ps 24`.

The two arithmetic/analytic facts about the smoothed kernel `K^J_{Q;τ}` that are proved elsewhere
(`KernelData.lean`) enter as the hypotheses `KernelDataHyp` and `AliasArithHyp`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff ComplexConjugate ENNReal

namespace PrimeBHT.TransferenceAssembly

/-! ## The two hypotheses (verbatim from `KernelData.lean`) -/

/-- For every `Q, J` the smoothed kernel `K^J_{Q;τ}` is (the restriction to `ℝ` of) a Schwartz
function `K` whose Fourier transform is supported in `|t| ≤ c / N(Q)` and whose symbol
`t ↦ K̂(-t)` is smooth away from `0` with the all-order bounds `A`. -/
def KernelDataHyp (φ : 𝓢(ℝ, ℝ)) (c : ℝ) (χ : ℝ → ℝ) (τ ε : ℝ) (A : ℕ → ℝ) : Prop :=
  ∀ (Q J : ℕ), ∃ K : 𝓢(ℝ, ℂ),
    (∀ x : ℝ, K x = ((PrimeBHT.BlockSum.KQ φ χ Q τ ε J x : ℝ) : ℂ)) ∧
    (∀ t : ℝ, c / PrimeBHT.BlockSum.NQ Q τ ε < |t| → 𝓕 (K : ℝ → ℂ) t = 0) ∧
    ContDiffOn ℝ ∞ (fun t => 𝓕 (K : ℝ → ℂ) (-t)) {0}ᶜ ∧
    (∀ j : ℕ, ∀ t : ℝ, t ≠ 0 → |t| ^ j * ‖iteratedDeriv j (fun t => 𝓕 (K : ℝ → ℂ) (-t)) t‖ ≤ A j)

/-- The arithmetic input of N42: for large dyadic `Q`, `N = 𝒬_B` satisfies
`N · c / N(Q) ≤ 10⁻³` for every block `B`. -/
def AliasArithHyp (c τ ε : ℝ) : Prop :=
  ∃ Q₀ : ℕ, ∀ j : ℕ, Q₀ ≤ 2 ^ j → ∀ B : Finset ℕ, B ⊆ PrimeCarleson.Proof.Paper.sqfreeSet j → B.Nonempty →
    (B.card : ℝ) ≤ 24 * ((2 : ℝ) ^ j) ^ (τ - ε) → ∀ N : ℕ, PrimeCarleson.Proof.Paper.lcmQ B = N →
    (N : ℝ) * (c / PrimeBHT.BlockSum.NQ (2 ^ j) τ ε) ≤ 1 / 1000

/-! ## Norm conversions -/

section Norms

/-- `ℓ²` norm of a finitely supported function: `Lift.lpNorm 2` is `l2norm`. -/
theorem lpNorm_two_ofSupportFinite {f : ℤ → ℂ} (hf : (Function.support f).Finite) :
    Lift.lpNorm 2 (Finsupp.ofSupportFinite f hf) = PrimeBHT.Kernel.l2norm f := by
  unfold Lift.lpNorm PrimeBHT.Kernel.l2norm
  rw [Real.sqrt_eq_rpow, tsum_eq_sum (s := (Finsupp.ofSupportFinite f hf).support)]
  · simp only [Finsupp.ofSupportFinite_coe, Real.rpow_two, one_div]
  · intro b hb
    have h0 := Finsupp.notMem_support_iff.1 hb
    rw [Finsupp.ofSupportFinite_coe] at h0
    rw [h0]
    simp

theorem lpNorm_nonneg (p : ℝ) (h : ℤ →₀ ℂ) : 0 ≤ Lift.lpNorm p h :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _

theorem supNorm_nonneg (h : ℤ →₀ ℂ) : 0 ≤ Lift.supNorm h := NNReal.coe_nonneg _

theorem supNorm_le_one {h : ℤ →₀ ℂ} (hh : ∀ x, ‖h x‖ ≤ 1) : Lift.supNorm h ≤ 1 := by
  unfold Lift.supNorm
  rw [← NNReal.coe_one, NNReal.coe_le_coe]
  exact Finset.sup_le fun n _ => by
    rw [← NNReal.coe_le_coe]
    simpa using hh n

variable {N : ℕ} [NeZero N]

/-- The normalised `L^p` norm of `ZMod N` is `Lift.yNorm p`. -/
theorem lpNorm_eq_yNorm (p : ℝ) (F : ZMod N → ℂ) :
    PrimeBHT.PeriodicAssembly.lpNorm p F = Lift.yNorm p F := by
  unfold PrimeBHT.PeriodicAssembly.lpNorm Lift.yNorm
  rw [Fintype.expect_eq_sum_div_card, ZMod.card, div_eq_inv_mul]

theorem periodic_l2_eq_yNorm_two (F : ZMod N → ℂ) : PrimeBHT.Periodic.l2 F = Lift.yNorm 2 F :=
  (show PrimeBHT.Periodic.l2 F = PrimeBHT.PeriodicBlock.l2 F from rfl).trans (l2_eq_yNorm_two F)

theorem yNorm_two_one : Lift.yNorm 2 (fun _ : ZMod N => (1 : ℂ)) = 1 := by
  unfold Lift.yNorm
  simp [ZMod.card, NeZero.ne N]

/-- The constant in a periodic `L^p`-bound is nonnegative. -/
theorem nonneg_of_yNorm_le {p D : ℝ} {Λ : ZMod N → ℂ}
    (hD : ∀ F G : ZMod N → ℂ, Lift.yNorm p (PrimeBHT.PeriodicBlock.bilinAvg Λ F G) ≤
      D * Lift.yNorm 2 F * Lift.yNorm 2 G) : 0 ≤ D := by
  have h := hD (fun _ => 1) (fun _ => 1)
  rw [yNorm_two_one] at h
  linarith [Lift.yNorm_nonneg p (PrimeBHT.PeriodicBlock.bilinAvg Λ (fun _ => (1 : ℂ)) fun _ => 1)]

end Norms

/-! ## The block weight -/

theorem periodic_blockWeight {B : Finset ℕ} {N : ℕ} (hBN : ∀ q ∈ B, q ∣ N) :
    Function.Periodic (PrimeCarleson.blockWeight B) (N : ℤ) := fun n => by
  simpa using PrimeBHT.PeriodicBlock.blockWeight_add_mul_of_dvd hBN n 1

theorem exists_norm_blockWeight_le (B : Finset ℕ) :
    ∃ W : ℝ, ∀ n : ℤ, ‖PrimeCarleson.blockWeight B n‖ ≤ W := by
  refine ⟨∑ q ∈ B, ‖(((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ) : ℂ)‖ *
    (((Finset.Icc 1 q).filter (fun a => Nat.Coprime a q)).card : ℝ), fun n => ?_⟩
  unfold PrimeCarleson.blockWeight
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [norm_mul]
  gcongr
  unfold PrimeCarleson.ramanujanSum
  refine (norm_sum_le _ _).trans ?_
  simp [PrimeCarleson.Proof.Goal0.norm_e]


/-! ## Uniform chart constants -/

/-- One constant bounding the translate sums `sup_t ∑_j ‖χ̌_ι(t - j)‖` and the resulting lift
constants of all charts of a cover. -/
theorem exists_chart_constants (cc : ChartCover) :
    ∃ E : ℝ, 0 ≤ E ∧ ∃ M : ℝ, 0 ≤ M ∧
      (∀ (ι : Fin cc.n) (t : ℝ), ∑' j : ℤ, ‖chartKernel (cc.χ ι) (t - j)‖ ≤ M) ∧
      ∀ ι : Fin cc.n, M ^ (((2 : ℝ) - 1) / 2) * (∫ x : ℝ, ‖chartKernel (cc.χ ι) x‖) ^ (2 : ℝ)⁻¹ ≤ E := by
  choose C hC using fun ι : Fin cc.n =>
    exists_tsum_chartKernel_sub_le (cc.contDiff ι) (cc.hasCompactSupport ι)
  set M : ℝ := ∑ ι : Fin cc.n, |C ι| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hCM : ∀ ι : Fin cc.n, C ι ≤ M := fun ι =>
    (le_abs_self _).trans
      (Finset.single_le_sum (f := fun ι : Fin cc.n => |C ι|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ ι))
  have hterm : ∀ ι : Fin cc.n, 0 ≤ M ^ (((2 : ℝ) - 1) / 2) *
      (∫ x : ℝ, ‖chartKernel (cc.χ ι) x‖) ^ (2 : ℝ)⁻¹ := fun ι =>
    mul_nonneg (Real.rpow_nonneg hM0 _)
      (Real.rpow_nonneg (integral_nonneg fun _ => norm_nonneg _) _)
  refine ⟨∑ ι : Fin cc.n, M ^ (((2 : ℝ) - 1) / 2) *
      (∫ x : ℝ, ‖chartKernel (cc.χ ι) x‖) ^ (2 : ℝ)⁻¹,
    Finset.sum_nonneg fun ι _ => hterm ι, M, hM0, fun ι t => (hC ι t).trans (hCM ι), fun ι => ?_⟩
  exact Finset.single_le_sum (f := fun ι : Fin cc.n => M ^ (((2 : ℝ) - 1) / 2) *
      (∫ x : ℝ, ‖chartKernel (cc.χ ι) x‖) ^ (2 : ℝ)⁻¹) (fun ι _ => hterm ι) (Finset.mem_univ ι)

theorem ofReal_mul_ofReal_mul_ofReal_mul {a b c : ℝ} (d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c * ENNReal.ofReal d =
      ENNReal.ofReal (a * b * c * d) := by
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (mul_nonneg ha hb),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg ha hb) hc)]

/-! ## The bound for one chart triple, in real form -/

/-- **N42, one chart triple, real form** (conditional on X2). There is `K₀ ≥ 0`, depending only on
`(p, u, A)` and the chart cover, such that for every `N`, periodic `w`, kernel `K` as in N42 and
`D` dominating the periodic bound, `|T_{ι₁ι₂ι₃}| ≤ K₀ D ‖f‖_{ℓ²} ‖g‖_{ℓ²}` for `‖h‖_∞ ≤ 1`. -/
theorem exists_norm_chartTriple_le_of_x2 (hx2 : X2Statement) {p u : ℝ} (hpu : p.HolderConjugate u)
    (A : ℕ → ℝ) (cc : ChartCover) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ (N : ℕ) [NeZero N] {w : ℤ → ℂ} (_hw : Function.Periodic w (N : ℤ))
      (K : 𝓢(ℝ, ℂ)) {δ : ℝ} (_hK : ∀ t, δ < |t| → 𝓕 (K : ℝ → ℂ) t = 0)
      (_hNδ : N * δ ≤ 1 / 1000)
      (_hm : ContDiffOn ℝ ∞ (fun t => 𝓕 (K : ℝ → ℂ) (-t)) {0}ᶜ)
      (_hA : ∀ j : ℕ, ∀ t : ℝ, t ≠ 0 →
        |t| ^ j * ‖iteratedDeriv j (fun t => 𝓕 (K : ℝ → ℂ) (-t)) t‖ ≤ A j)
      {D : ℝ} (_hD : ∀ F G : ZMod N → ℂ, Lift.yNorm p
        (PrimeBHT.PeriodicBlock.bilinAvg (fun r : ZMod N => w (r.val : ℤ)) F G) ≤
          D * Lift.yNorm 2 F * Lift.yNorm 2 G)
      (f g h : ℤ →₀ ℂ), (∀ x, ‖h x‖ ≤ 1) → ∀ ι₁ ι₂ ι₃ : Fin cc.n,
      ‖∑' x : ℤ, ∑' n : ℤ, K n * w n * chartProj (cc.χ ι₁) N f (x - n) *
          chartProj (cc.χ ι₂) N g (x + n) * conj (chartProj (cc.χ ι₃) N h x)‖ ≤
        K₀ * D * (Lift.lpNorm 2 f * Lift.lpNorm 2 g) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_tsum_tsum_chartProj_le_lp_of_x2 hx2 hpu A
  obtain ⟨E, hE0, M, hM0, hM, hE⟩ := exists_chart_constants cc
  refine ⟨C * E * E * M, mul_nonneg (mul_nonneg (mul_nonneg hC0 hE0) hE0) hM0, ?_⟩
  intro N _ w hw K δ hK hNδ hm hA D hD f g h hh ι₁ ι₂ ι₃
  obtain ⟨d, hd⟩ := exists_alias_d cc ι₁ ι₂
  obtain ⟨v, hv⟩ := exists_alias_v cc ι₁ ι₂ ι₃
  have hD0 : 0 ≤ D := nonneg_of_yNorm_le hD
  have h1 := hC N (cc.contDiff ι₁) (cc.hasCompactSupport ι₁) (cc.contDiff ι₂)
    (cc.hasCompactSupport ι₂) (cc.contDiff ι₃) (cc.hasCompactSupport ι₃)
    (cc.mem_Icc_of_ne_zero ι₁) (cc.mem_Icc_of_ne_zero ι₂) (cc.mem_Icc_of_ne_zero ι₃) hw K hK hNδ
    hd hv hm hA hD (hM ι₁) (hM ι₂) (hM ι₃) f g h
  have e1 := hE ι₁
  have e2 := hE ι₂
  have hlf := lpNorm_nonneg 2 f
  have hlg := lpNorm_nonneg 2 g
  have hs0 := supNorm_nonneg h
  have hs1 := supNorm_le_one hh
  have hb1 : M ^ (((2 : ℝ) - 1) / 2) * (∫ x : ℝ, ‖chartKernel (cc.χ ι₁) x‖) ^ (2 : ℝ)⁻¹ *
      Lift.lpNorm 2 f ≤ E * Lift.lpNorm 2 f := mul_le_mul_of_nonneg_right e1 hlf
  have hb2 : M ^ (((2 : ℝ) - 1) / 2) * (∫ x : ℝ, ‖chartKernel (cc.χ ι₂) x‖) ^ (2 : ℝ)⁻¹ *
      Lift.lpNorm 2 g ≤ E * Lift.lpNorm 2 g := mul_le_mul_of_nonneg_right e2 hlg
  have hb3 : M * Lift.supNorm h ≤ M * 1 := mul_le_mul_of_nonneg_left hs1 hM0
  have hX0 : 0 ≤ C * D * (E * Lift.lpNorm 2 f) * (E * Lift.lpNorm 2 g) * (M * 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hD0) (mul_nonneg hE0 hlf))
      (mul_nonneg hE0 hlg)) (mul_nonneg hM0 zero_le_one)
  have h2 := h1.trans (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hb1))
    (ENNReal.ofReal_le_ofReal hb2)) (ENNReal.ofReal_le_ofReal hb3))
  rw [ofReal_mul_ofReal_mul_ofReal_mul _ (mul_nonneg hC0 hD0) (mul_nonneg hE0 hlf)
    (mul_nonneg hE0 hlg), ← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hX0] at h2
  refine h2.trans (le_of_eq ?_)
  ring


/-! ## The per-block transference bound -/

/-- `hOp` is the `tsum` form of the block operator, with the Schwartz kernel `K`. -/
theorem hOp_eq_tsum {φ : 𝓢(ℝ, ℝ)} {χ : ℝ → ℝ} {Q : ℕ} {τ ε : ℝ} {J : ℕ} (B : Finset ℕ)
    (f g : ℤ → ℂ) {K : 𝓢(ℝ, ℂ)}
    (hK : ∀ x : ℝ, K x = ((PrimeBHT.BlockSum.KQ φ χ Q τ ε J x : ℝ) : ℂ)) (x : ℤ) :
    PrimeBHT.BlockSum.hOp φ χ Q τ ε J B f g x =
      ∑' n : ℤ, K n * PrimeCarleson.blockWeight B n * f (x - n) * g (x + n) := by
  unfold PrimeBHT.BlockSum.hOp PrimeBHT.Kernel.bilin
  refine tsum_congr fun n => ?_
  rw [hK]

/-- **N43(a), conditional on X2 and the kernel data (`_of_kernelData`).** The per-block
transference bound `BlockTransferBound φ c χ τ ε ps 24`: `ℓ¹` duality, the chart expansion
(`n_ch³` chart triples), and the N42 bound for each triple. The constants `C, Q₀` depend only on
`ps`, the symbol bounds `A`, the chart cover and `Q₀` of the alias arithmetic. -/
theorem blockTransferBound_of_x2_of_kernelData (hx2 : X2Statement) {φ : 𝓢(ℝ, ℝ)} {c : ℝ}
    {χ : ℝ → ℝ} {τ ε ps : ℝ} (hps1 : 1 < ps) (_hps2 : ps ≤ 2) {A : ℕ → ℝ}
    (hKD : KernelDataHyp φ c χ τ ε A) (hAA : AliasArithHyp c τ ε) :
    PrimeBHT.BlockSum.BlockTransferBound φ c χ τ ε ps 24 := by
  intro _hφc
  obtain ⟨cc⟩ := exists_chartCover
  have hpu : ps.HolderConjugate (ps / (ps - 1)) := Real.HolderConjugate.conjExponent hps1
  obtain ⟨K₀, hK₀, hT⟩ := exists_norm_chartTriple_le_of_x2 hx2 hpu A cc
  obtain ⟨Q₀, hQ₀⟩ := hAA
  refine ⟨(cc.n : ℝ) ^ 3 * K₀, mul_nonneg (by positivity) hK₀, Q₀, ?_⟩
  intro j hj J B hB hBne hcard N _ hN D hD f g hf hg
  obtain ⟨K, hKeq, hKsupp, hKm, hKA⟩ := hKD (2 ^ j) J
  have hδ := hQ₀ j hj B hB hBne hcard N hN
  have hBN : ∀ q ∈ B, q ∣ N := fun q hq => hN ▸ PrimeCarleson.Proof.Paper.dvd_lcmQ hq
  have hw := periodic_blockWeight hBN
  obtain ⟨W, hW⟩ := exists_norm_blockWeight_le B
  have hD' : ∀ F G : ZMod N → ℂ, Lift.yNorm ps (PrimeBHT.PeriodicBlock.bilinAvg
      (fun r : ZMod N => PrimeCarleson.blockWeight B (r.val : ℤ)) F G) ≤
        D * Lift.yNorm 2 F * Lift.yNorm 2 G := by
    intro F G
    have h := hD F G
    rw [lpNorm_eq_yNorm, periodic_l2_eq_yNorm_two, periodic_l2_eq_yNorm_two] at h
    exact h
  have hD0 : 0 ≤ D := nonneg_of_yNorm_le hD'
  have hmain := summable_and_tsum_norm_le_of_chart_bounds_of_finite_support (χ := cc.χ)
    cc.contDiff cc.hasCompactSupport (fun N _ h m => sum_chartProj cc N h m) N K hW hf hg
    (C₀ := K₀ * D * (PrimeBHT.Kernel.l2norm f * PrimeBHT.Kernel.l2norm g)) ?_
  · simp only [hOp_eq_tsum B f g hKeq]
    refine ⟨hmain.1, hmain.2.trans (le_of_eq ?_)⟩
    ring
  · intro h hh ι₁ ι₂ ι₃
    have := hT N hw K hKsupp hδ hKm hKA hD' (Finsupp.ofSupportFinite f hf)
      (Finsupp.ofSupportFinite g hg) h hh ι₁ ι₂ ι₃
    rwa [lpNorm_two_ofSupportFinite, lpNorm_two_ofSupportFinite] at this

/-- **N43(a), conditional on X2 only.** The kernel data and the alias arithmetic are supplied by
`KernelData.lean` (`kernelData`, `exists_Q0_alias_arith`); the vanishing of `φ̂` outside `[-c, c]` is
the premise of `BlockTransferBound`. -/
theorem blockTransferBound_of_x2 (hx2 : X2Statement) {φ : 𝓢(ℝ, ℝ)} {c : ℝ} (hc : 0 ≤ c)
    {χ : ℝ → ℝ} (hχ : PrimeBHT.Kernel.IsCutoff χ) {τ ε ps : ℝ} (hε0 : 0 < ε) (hετ : ε < τ)
    (hps1 : 1 < ps) (hps2 : ps ≤ 2) :
    PrimeBHT.BlockSum.BlockTransferBound φ c χ τ ε ps 24 := fun hφc =>
  blockTransferBound_of_x2_of_kernelData hx2 hps1 hps2
    (A := PrimeBHT.KernelFourier.symbolConst hχ φ) (kernelData hχ hφc τ ε)
    (exists_Q0_alias_arith hc hε0 hετ) hφc

end PrimeBHT.TransferenceAssembly
