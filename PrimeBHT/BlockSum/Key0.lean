module

public import PrimeBHT.BlockSum.Sum

/-!
# Assembly of `p:key0` (blueprint N26), conditional on the per-block transference bound

* `exists_scale_le`: the elementary estimate `Q^{101} N(Q) ≤ 2^{a_Q}` for large `Q`;
* `key0_of_blockTransfer`: `‖U^J_{Q;τ}‖_{ℓ¹} ≤ C Q^{1-κ/2-1/p*+η'} ‖f‖₂ ‖g‖₂` for the unsmoothed
  operator (N25(a) + N43(c));
* `p_key0_of_blockTransfer`: the corrected `p:key0` (all `τ ∈ (0,1)`, all `η > 0`, every cutoff `χ`),
  in the `eLpNorm` shape of the draft `p_key0`.
-/

@[expose] public section

namespace PrimeBHT.BlockSum

open PrimeBHT.Kernel PrimeCarleson
open scoped FourierTransform ENNReal

/-! ## The elementary scale estimate -/

/-- For `τ, ε > 0` and `Q` large, `Q^{101} · N(Q) ≤ 2^{a_Q}`, hence `N(Q) ≤ 2^{a_Q}` and
`Q N(Q) 2^{-a_Q} ≤ Q^{-100}`. -/
theorem exists_scale_le {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ Q₀ : ℕ, ∀ Q : ℕ, Q₀ ≤ Q → 1 ≤ Q ∧ NQ Q τ ε ≤ 2 ^ aQ Q τ ∧
      (Q : ℝ) * (NQ Q τ ε / 2 ^ aQ Q τ) ≤ (Q : ℝ) ^ (-100 : ℝ) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδ : 0 < ε / 10 := by positivity
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, x ^ (-(ε / 10)) ≤ Real.log 2 / 3 :=
    (tendsto_rpow_neg_atTop hδ).eventually_le_const (by positivity)
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x‖ ≤ (Real.log 2 / 303) * ‖x ^ τ‖ :=
    (isLittleO_log_rpow_atTop hτ).def (by positivity)
  have h3 : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x := Filter.eventually_ge_atTop 1
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.1
    (tendsto_natCast_atTop_atTop.eventually (h1.and (h2.and h3)))
  refine ⟨Q₀, fun Q hQ => ?_⟩
  obtain ⟨hA, hB, hC⟩ := hQ₀ Q hQ
  have hQ1 : (1 : ℝ) ≤ Q := hC
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hQ1' : 1 ≤ Q := by exact_mod_cast hQ1
  have hXnn : 0 ≤ (Q : ℝ) ^ τ := Real.rpow_nonneg hQ0.le _
  have hlog : Real.log Q ≤ (Real.log 2 / 303) * (Q : ℝ) ^ τ := by
    rwa [Real.norm_of_nonneg (Real.log_nonneg hQ1), Real.norm_of_nonneg hXnn] at hB
  have hpow : (Q : ℝ) ^ (τ - ε / 10) ≤ (Real.log 2 / 3) * (Q : ℝ) ^ τ := by
    rw [sub_eq_add_neg, Real.rpow_add hQ0]
    calc (Q : ℝ) ^ τ * (Q : ℝ) ^ (-(ε / 10)) ≤ (Q : ℝ) ^ τ * (Real.log 2 / 3) := by gcongr
      _ = _ := by ring
  have hkey : 101 * Real.log Q + (Q : ℝ) ^ (τ - ε / 10) ≤ Real.log 2 * (Q : ℝ) ^ τ := by
    nlinarith [mul_nonneg hL.le hXnn]
  have e1 : (Q : ℝ) ^ 101 = Real.exp (101 * Real.log Q) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hQ0]
    congr 1
    push_cast
    ring
  have e2 : (2 : ℝ) ^ aQ Q τ = Real.exp ((aQ Q τ : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hle : Real.log 2 * (Q : ℝ) ^ τ ≤ (aQ Q τ : ℝ) * Real.log 2 := by
    have : (Q : ℝ) ^ τ ≤ (aQ Q τ : ℝ) := Nat.le_ceil _
    nlinarith
  have hmain : (Q : ℝ) ^ 101 * NQ Q τ ε ≤ 2 ^ aQ Q τ := by
    rw [e1, e2, NQ, ← Real.exp_add]
    exact Real.exp_le_exp.2 (hkey.trans hle)
  have hN0 : 0 < NQ Q τ ε := Real.exp_pos _
  have h2a : (0 : ℝ) < 2 ^ aQ Q τ := by positivity
  have hQ101 : (1 : ℝ) ≤ (Q : ℝ) ^ 101 := one_le_pow₀ hQ1
  refine ⟨hQ1', ?_, ?_⟩
  · calc NQ Q τ ε = 1 * NQ Q τ ε := (one_mul _).symm
      _ ≤ (Q : ℝ) ^ 101 * NQ Q τ ε := by gcongr
      _ ≤ _ := hmain
  · rw [mul_div_assoc', div_le_iff₀ h2a]
    have hexp : (Q : ℝ) ^ (-100 : ℝ) * (Q : ℝ) ^ 101 = Q := by
      have : (Q : ℝ) ^ (101 : ℕ) = (Q : ℝ) ^ ((101 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      rw [this, ← Real.rpow_add hQ0]
      norm_num
    calc (Q : ℝ) * NQ Q τ ε
        = (Q : ℝ) ^ (-100 : ℝ) * ((Q : ℝ) ^ 101 * NQ Q τ ε) := by rw [← mul_assoc, hexp]
      _ ≤ (Q : ℝ) ^ (-100 : ℝ) * 2 ^ aQ Q τ :=
          mul_le_mul_of_nonneg_left hmain (Real.rpow_nonneg hQ0.le _)

/-! ## `p:key0`, conditional on the per-block transference bound -/

/-- **N26 for the unsmoothed operator, conditional on `BlockTransferBound`.** For a cutoff `χ`,
`τ ∈ (0,1)`, `ε ∈ (0, τ/1000)`, `p* ∈ (1, 2]` and `η' > 0` there are `C, Q₀` with, for all dyadic
`Q = 2^j ≥ Q₀`, all `J` and all finitely supported `f, g`,
`‖U^J_{Q;τ}(f, g)‖_{ℓ¹} ≤ C Q^{1 - (τ-ε)/2 - 1/p* + η'} ‖f‖₂ ‖g‖₂`. -/
theorem key0_of_blockTransfer {φ : SchwartzMap ℝ ℝ} {c : ℝ} (hφ : ∫ u, φ u = 1)
    (hφc : ∀ ξ : ℝ, c < |ξ| → 𝓕 (fun x : ℝ => ((φ x : ℝ) : ℂ)) ξ = 0)
    {χ : ℝ → ℝ} (hχ : IsCutoff χ) {τ ε ps : ℝ} (hε0 : 0 < ε) (hετ : ε < τ / 1000)
    (hτ1 : τ < 1) (hps1 : 1 < ps) (hps2 : ps ≤ 2) (hBT : BlockTransferBound φ c χ τ ε ps 24)
    {η' : ℝ} (hη' : 0 < η') :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Q₀ : ℕ, ∀ j : ℕ, Q₀ ≤ 2 ^ j → ∀ J : ℕ, ∀ f g : ℤ → ℂ,
      (Function.support f).Finite → (Function.support g).Finite →
      Summable (fun x => ‖uOp χ (2 ^ j) τ J f g x‖) ∧
      ∑' x, ‖uOp χ (2 ^ j) τ J f g x‖ ≤
        C * ((2 : ℝ) ^ j) ^ (1 - (τ - ε) / 2 - 1 / ps + η') * (l2norm f * l2norm g) := by
  have hτ0 : 0 < τ := by linarith
  obtain ⟨CH, hCH0, QH, hQH⟩ := blockSum_bound_of_blockTransfer hφc hε0 hετ hτ1 hps1 hps2 hBT hη'
  obtain ⟨CS, hCS0, hCS⟩ := hχ.l1_smoothing_error_le φ hφ
  obtain ⟨QS, hQS⟩ := exists_scale_le hτ0 hε0
  refine ⟨CH + CS, by positivity, max QH QS, fun j hj J f g hf hg => ?_⟩
  have hjH : QH ≤ 2 ^ j := (le_max_left _ _).trans hj
  have hjS : QS ≤ 2 ^ j := (le_max_right _ _).trans hj
  obtain ⟨hQ1', hNle, hQN⟩ := hQS (2 ^ j) hjS
  have hcast : (((2 ^ j : ℕ)) : ℝ) = (2 : ℝ) ^ j := by push_cast; rfl
  have hQ1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hQ0 : (0 : ℝ) < (2 : ℝ) ^ j := by linarith
  obtain ⟨hsH, hH⟩ := hQH j hjH J f g hf hg
  -- the smoothing error
  have hNpos : 0 < NQ (2 ^ j) τ ε := Real.exp_pos _
  have hw : ∀ n : ℤ, ‖blockWeight (Finset.Ioc (2 ^ j / 2) (2 ^ j)) n‖ ≤ ((2 : ℝ) ^ j) := by
    intro n
    refine (PrimeCarleson.Proof.FplusProp21.norm_blockWeight_le_card _ n).trans ?_
    rw [Nat.card_Ioc, ← hcast]
    exact_mod_cast Nat.sub_le _ _
  obtain ⟨hsE, hE⟩ := hCS (NQ (2 ^ j) τ ε) (aQ (2 ^ j) τ) J
    (blockWeight (Finset.Ioc (2 ^ j / 2) (2 ^ j))) ((2 : ℝ) ^ j) f g hNpos hNle hw hf hg
  have hdiff : ∀ x, uOp χ (2 ^ j) τ J f g x - hOp φ χ (2 ^ j) τ ε J (Finset.Ioc (2 ^ j / 2) (2 ^ j)) f g x
      = bilin (fun n => blockWeight (Finset.Ioc (2 ^ j / 2) (2 ^ j)) n *
        ((kernelI χ (aQ (2 ^ j) τ) J (n : ℝ) -
          smooth φ (NQ (2 ^ j) τ ε) (kernelI χ (aQ (2 ^ j) τ) J) (n : ℝ) : ℝ) : ℂ)) f g x :=
    fun x => uOp_sub_hOp φ χ (2 ^ j) τ ε J hf g x
  have hpt : ∀ x, ‖uOp χ (2 ^ j) τ J f g x‖ ≤
      ‖hOp φ χ (2 ^ j) τ ε J (Finset.Ioc (2 ^ j / 2) (2 ^ j)) f g x‖ +
      ‖bilin (fun n => blockWeight (Finset.Ioc (2 ^ j / 2) (2 ^ j)) n *
        ((kernelI χ (aQ (2 ^ j) τ) J (n : ℝ) -
          smooth φ (NQ (2 ^ j) τ ε) (kernelI χ (aQ (2 ^ j) τ) J) (n : ℝ) : ℝ) : ℂ)) f g x‖ := by
    intro x
    rw [← hdiff x]
    calc ‖uOp χ (2 ^ j) τ J f g x‖
        = ‖hOp φ χ (2 ^ j) τ ε J (Finset.Ioc (2 ^ j / 2) (2 ^ j)) f g x +
            (uOp χ (2 ^ j) τ J f g x -
              hOp φ χ (2 ^ j) τ ε J (Finset.Ioc (2 ^ j / 2) (2 ^ j)) f g x)‖ := by
          congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have hsum := hsH.add hsE
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsum, ?_⟩
  have hps0 : 0 < ps := by linarith
  have hinv : 0 < 1 / ps := by positivity
  have hκ1 : τ - ε ≤ 1 := by linarith
  have hexp : (-100 : ℝ) ≤ 1 - (τ - ε) / 2 - 1 / ps + η' := by
    have : 1 / ps < 1 := by rw [div_lt_one hps0]; exact hps1
    linarith
  rw [hcast] at hQN
  have hQN' : (2 : ℝ) ^ j * (NQ (2 ^ j) τ ε / 2 ^ aQ (2 ^ j) τ) ≤
      ((2 : ℝ) ^ j) ^ (1 - (τ - ε) / 2 - 1 / ps + η') :=
    hQN.trans (Real.rpow_le_rpow_of_exponent_le hQ1 hexp)
  have hL : 0 ≤ l2norm f * l2norm g := mul_nonneg (l2norm_nonneg f) (l2norm_nonneg g)
  calc ∑' x, ‖uOp χ (2 ^ j) τ J f g x‖
      ≤ ∑' x, (‖hOp φ χ (2 ^ j) τ ε J (Finset.Ioc (2 ^ j / 2) (2 ^ j)) f g x‖ +
        ‖bilin (fun n => blockWeight (Finset.Ioc (2 ^ j / 2) (2 ^ j)) n *
          ((kernelI χ (aQ (2 ^ j) τ) J (n : ℝ) -
            smooth φ (NQ (2 ^ j) τ ε) (kernelI χ (aQ (2 ^ j) τ) J) (n : ℝ) : ℝ) : ℂ)) f g x‖) :=
        Summable.tsum_le_tsum hpt (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsum) hsum
    _ = _ := hsH.tsum_add hsE
    _ ≤ CH * ((2 : ℝ) ^ j) ^ (1 - (τ - ε) / 2 - 1 / ps + η') * (l2norm f * l2norm g) +
        CS * (2 : ℝ) ^ j * (NQ (2 ^ j) τ ε / 2 ^ aQ (2 ^ j) τ) * (l2norm f * l2norm g) :=
        add_le_add hH hE
    _ ≤ CH * ((2 : ℝ) ^ j) ^ (1 - (τ - ε) / 2 - 1 / ps + η') * (l2norm f * l2norm g) +
        CS * ((2 : ℝ) ^ j) ^ (1 - (τ - ε) / 2 - 1 / ps + η') * (l2norm f * l2norm g) := by
        have : CS * (2 : ℝ) ^ j * (NQ (2 ^ j) τ ε / 2 ^ aQ (2 ^ j) τ) * (l2norm f * l2norm g) =
            CS * ((2 : ℝ) ^ j * (NQ (2 ^ j) τ ε / 2 ^ aQ (2 ^ j) τ)) * (l2norm f * l2norm g) := by
          ring
        rw [this]
        gcongr
    _ = (CH + CS) * ((2 : ℝ) ^ j) ^ (1 - (τ - ε) / 2 - 1 / ps + η') * (l2norm f * l2norm g) := by
        ring

/-! ## The corrected `p:key0` -/

/-- **`p:key0` (blueprint N26, corrected quantifier order), conditional on `BlockTransferBound`.**
For the fixed smoothing function `φ` (`∫ φ = 1`, `φ̂` supported in `[-c, c]`), assume the per-block
transference bound for every cutoff `χ` and all parameters `τ`, `ε ∈ (0, τ/1000)`, `p* ∈ (1, 2]`
(blocks of size `≤ 24 Q^{τ-ε}`). Then for every cutoff `χ`, `τ ∈ (0,1)` and `η > 0` there are `Q₀`
and `C` such that for dyadic `Q ≥ Q₀`, all `J`, all finitely supported `f, g`,
`‖U^J_{Q;τ}(f,g)‖_{ℓ¹} ≤ C Q^{-τ/2 + η} ‖f‖_{ℓ²} ‖g‖_{ℓ²}` (the conclusion of the draft
`PrimeBHT.Statements.p_key0`, with the local `uOp`). The parameters are chosen as in blueprint N26
step 2: `ε = min (τ/2000) (η/4)`, `p* = 1 + min 1 (η/8)`, `η' = η/4`. -/
theorem p_key0_of_blockTransfer {φ : SchwartzMap ℝ ℝ} {c : ℝ} (hφ : ∫ u, φ u = 1)
    (hφc : ∀ ξ : ℝ, c < |ξ| → 𝓕 (fun x : ℝ => ((φ x : ℝ) : ℂ)) ξ = 0)
    (hBT : ∀ χ : ℝ → ℝ, IsCutoff χ → ∀ τ ε ps : ℝ, 0 < ε → ε < τ / 1000 → τ < 1 → 1 < ps →
      ps ≤ 2 → BlockTransferBound φ c χ τ ε ps 24) :
    ∀ χ : ℝ → ℝ, IsCutoff χ →
    ∀ τ : ℝ, 0 < τ → τ < 1 →
    ∀ η : ℝ, 0 < η →
      ∃ Q₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ Q : ℕ, (∃ j : ℕ, Q = 2 ^ j) → Q₀ ≤ Q →
        ∀ J : ℕ, ∀ f g : ℤ →₀ ℂ,
          MeasureTheory.eLpNorm (uOp χ Q τ J ⇑f ⇑g) 1 MeasureTheory.Measure.count ≤
            ENNReal.ofReal (C * (Q : ℝ) ^ (-τ / 2 + η)) *
              MeasureTheory.eLpNorm (⇑f) 2 MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm (⇑g) 2 MeasureTheory.Measure.count := by
  intro χ hχ τ hτ0 hτ1 η hη
  have hε0 : 0 < min (τ / 2000) (η / 4) := lt_min (by positivity) (by positivity)
  have hετ : min (τ / 2000) (η / 4) < τ / 1000 :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hm0 : 0 < min 1 (η / 8) := lt_min one_pos (by positivity)
  have hps1 : 1 < 1 + min 1 (η / 8) := by linarith
  have hps2 : 1 + min 1 (η / 8) ≤ 2 := by linarith [min_le_left 1 (η / 8)]
  obtain ⟨C, hC0, Q₀, hQ₀⟩ := key0_of_blockTransfer hφ hφc hχ hε0 hετ hτ1 hps1 hps2
    (hBT χ hχ τ _ _ hε0 hετ hτ1 hps1 hps2) (η' := η / 4) (by positivity)
  refine ⟨Q₀, C, hC0, ?_⟩
  rintro Q ⟨j, rfl⟩ hQ J f g
  have hf : (Function.support (⇑f)).Finite :=
    f.support.finite_toSet.subset fun x hx => by simpa using hx
  have hg : (Function.support (⇑g)).Finite :=
    g.support.finite_toSet.subset fun x hx => by simpa using hx
  obtain ⟨hs, hb⟩ := hQ₀ j hQ J f g hf hg
  have hcast : (((2 ^ j : ℕ)) : ℝ) = (2 : ℝ) ^ j := by push_cast; rfl
  have hQ1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  -- exponent comparison
  have hm1 : min 1 (η / 8) ≤ η / 8 := min_le_right _ _
  have hinv : 1 - min 1 (η / 8) ≤ 1 / (1 + min 1 (η / 8)) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [sq_nonneg (min 1 (η / 8))]
  have hε8 : min (τ / 2000) (η / 4) ≤ η / 4 := min_le_right _ _
  have hexp : 1 - (τ - min (τ / 2000) (η / 4)) / 2 - 1 / (1 + min 1 (η / 8)) + η / 4 ≤
      -τ / 2 + η := by linarith
  have hb' : ∑' x, ‖uOp χ (2 ^ j) τ J f g x‖ ≤
      C * ((2 ^ j : ℕ) : ℝ) ^ (-τ / 2 + η) * (l2norm f * l2norm g) := by
    rw [hcast]
    refine hb.trans ?_
    have := Real.rpow_le_rpow_of_exponent_le hQ1 hexp
    have hL : 0 ≤ l2norm f * l2norm g := mul_nonneg (l2norm_nonneg f) (l2norm_nonneg g)
    gcongr
  have hCQ : 0 ≤ C * ((2 ^ j : ℕ) : ℝ) ^ (-τ / 2 + η) :=
    mul_nonneg hC0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [eLpNorm_one_count_eq_ofReal hs, eLpNorm_two_count_eq_ofReal hf,
    eLpNorm_two_count_eq_ofReal hg, ← ENNReal.ofReal_mul hCQ,
    ← ENNReal.ofReal_mul (mul_nonneg hCQ (l2norm_nonneg f))]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ∑' x, ‖uOp χ (2 ^ j) τ J f g x‖
      ≤ C * ((2 ^ j : ℕ) : ℝ) ^ (-τ / 2 + η) * (l2norm f * l2norm g) := hb'
    _ = C * ((2 ^ j : ℕ) : ℝ) ^ (-τ / 2 + η) * l2norm f * l2norm g := by ring

end PrimeBHT.BlockSum
