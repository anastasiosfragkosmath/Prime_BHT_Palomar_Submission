module

public import PrimeBHT.BlockSum.Basic

/-!
# N43(c): from the per-block transference bound to the sum over blocks

`blockSum_bound_of_blockTransfer`: assuming `BlockTransferBound` (hypothesis) and using the
periodic bound `exists_lpNorm_bilinAvg_le` (N37) and the block partition N43(b),
`‖H^J_{Q;τ}(f, g)‖_{ℓ¹} ≤ C Q^{1 - κ/2 - 1/p* + η'} ‖f‖₂ ‖g‖₂` for dyadic `Q ≥ Q₀`, all `J`.
-/

@[expose] public section

namespace PrimeBHT.BlockSum

open PrimeBHT.Kernel PrimeCarleson
open PrimeCarleson.Proof.Paper (sqfreeSet mem_sqfreeSet lcmQ lcmQ_pos BlockPartition
  exists_blockPartition_24)
open scoped FourierTransform

/-- **N43(c), conditional on `BlockTransferBound`** (blocks of size `≤ 24 Q^κ`, the vendored
partition constant). For `τ ∈ (0,1)`, `ε ∈ (0, τ/1000)`, `κ = τ - ε`, `p* ∈ (1, 2]` and every
`η' > 0` there are `C` and `Q₀` with, for every dyadic `Q = 2^j ≥ Q₀`, every `J` and all finitely
supported `f, g`: `‖H^J_{Q;τ}(f,g)‖_{ℓ¹} ≤ C Q^{1 - κ/2 - 1/p* + η'} ‖f‖₂ ‖g‖₂`,
where `H^J_{Q;τ} = hOp … (Ioc (Q/2) Q)` has the full weight `w_Q`. -/
theorem blockSum_bound_of_blockTransfer {φ : SchwartzMap ℝ ℝ} {c : ℝ}
    (hφc : ∀ ξ : ℝ, c < |ξ| → 𝓕 (fun x : ℝ => ((φ x : ℝ) : ℂ)) ξ = 0)
    {χ : ℝ → ℝ} {τ ε ps : ℝ} (hε0 : 0 < ε) (hετ : ε < τ / 1000) (hτ1 : τ < 1)
    (hps1 : 1 < ps) (hps2 : ps ≤ 2) (hBT : BlockTransferBound φ c χ τ ε ps 24)
    {η' : ℝ} (hη' : 0 < η') :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Q₀ : ℕ, ∀ j : ℕ, Q₀ ≤ 2 ^ j → ∀ J : ℕ, ∀ f g : ℤ → ℂ,
      (Function.support f).Finite → (Function.support g).Finite →
      Summable (fun x => ‖hOp φ χ (2 ^ j) τ ε J (Finset.Ioc (2 ^ j / 2) (2 ^ j)) f g x‖) ∧
      ∑' x, ‖hOp φ χ (2 ^ j) τ ε J (Finset.Ioc (2 ^ j / 2) (2 ^ j)) f g x‖ ≤
        C * ((2 : ℝ) ^ j) ^ (1 - (τ - ε) / 2 - 1 / ps + η') * (l2norm f * l2norm g) := by
  have hτ0 : 0 < τ := by linarith
  have hκ0 : 0 ≤ τ - ε := by linarith
  have hκ1 : τ - ε ≤ 1 := by linarith
  have hη₁0 : 0 < min η' (1 / 2) := lt_min hη' (by norm_num)
  have hη₁1 : min η' (1 / 2) < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hη₁le : min η' (1 / 2) ≤ η' := min_le_left _ _
  obtain ⟨C₂, hC₂0, hC₂⟩ := PrimeBHT.PeriodicAssembly.exists_lpNorm_bilinAvg_le hη₁0 hη₁1
  obtain ⟨C₁, hC₁0, Q₀, hQ₀⟩ := hBT hφc
  refine ⟨48 * Real.sqrt 24 * C₁ * C₂, by positivity, Q₀, fun j hj J f g hf hg => ?_⟩
  obtain ⟨π⟩ := exists_blockPartition_24 j hκ0 hκ1
  have hQ1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hQ0 : (0 : ℝ) < (2 : ℝ) ^ j := by linarith
  have hl2 : 0 ≤ l2norm f * l2norm g := mul_nonneg (l2norm_nonneg f) (l2norm_nonneg g)
  -- the per-block bound
  have hblock : ∀ B ∈ π.blocks,
      Summable (fun x => ‖hOp φ χ (2 ^ j) τ ε J B f g x‖) ∧
      ∑' x, ‖hOp φ χ (2 ^ j) τ ε J B f g x‖ ≤
        (C₁ * C₂ * Real.sqrt 24) *
          ((2 : ℝ) ^ j) ^ ((τ - ε) / 2 + (-1 / ps + min η' (1 / 2))) * (l2norm f * l2norm g) := by
    intro B hB
    have hBsub := π.subset_sqfreeSet hB
    have hBne := π.nonempty_of_mem hB
    have hcard := π.card_le B hB
    have : NeZero (lcmQ B) :=
      ⟨(lcmQ_pos (fun q hq => Nat.pos_of_ne_zero (mem_sqfreeSet.1 (hBsub hq)).2.2.ne_zero)).ne'⟩
    have hD : ∀ F G : ZMod (lcmQ B) → ℂ,
        PrimeBHT.PeriodicAssembly.lpNorm ps
            (PrimeBHT.PeriodicBlock.bilinAvg (PrimeBHT.PeriodicBlock.lam B (lcmQ B)) F G) ≤
          (C₂ * √(B.card : ℝ) * ((2 : ℝ) ^ j) ^ (-1 / ps + min η' (1 / 2))) *
            PrimeBHT.Periodic.l2 F * PrimeBHT.Periodic.l2 G := fun F G =>
      hC₂ ps ((2 : ℝ) ^ j) B hps1.le hps2 hBne hQ1
        (fun q hq => real_bounds_of_mem_sqfreeSet (hBsub hq))
        (fun q hq => π.squarefree_of_mem hB hq) (lcmQ B) rfl F G
    obtain ⟨hs, hb⟩ := hQ₀ j hj J B hBsub hBne hcard (lcmQ B) rfl _ hD f g hf hg
    refine ⟨hs, hb.trans ?_⟩
    have hsq : √(B.card : ℝ) ≤ Real.sqrt 24 * ((2 : ℝ) ^ j) ^ ((τ - ε) / 2) := by
      calc √(B.card : ℝ) ≤ √(24 * ((2 : ℝ) ^ j) ^ (τ - ε)) := Real.sqrt_le_sqrt hcard
        _ = Real.sqrt 24 * ((2 : ℝ) ^ j) ^ ((τ - ε) / 2) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (((2 : ℝ) ^ j) ^ (τ - ε)),
            ← Real.rpow_mul hQ0.le]
          congr 2
          ring
    have hpow : 0 ≤ ((2 : ℝ) ^ j) ^ (-1 / ps + min η' (1 / 2)) :=
      Real.rpow_nonneg hQ0.le _
    have hmul : ((2 : ℝ) ^ j) ^ ((τ - ε) / 2) * ((2 : ℝ) ^ j) ^ (-1 / ps + min η' (1 / 2)) =
        ((2 : ℝ) ^ j) ^ ((τ - ε) / 2 + (-1 / ps + min η' (1 / 2))) := by
      rw [← Real.rpow_add hQ0]
    calc C₁ * (C₂ * √(B.card : ℝ) * ((2 : ℝ) ^ j) ^ (-1 / ps + min η' (1 / 2))) *
          (l2norm f * l2norm g)
        ≤ C₁ * (C₂ * (Real.sqrt 24 * ((2 : ℝ) ^ j) ^ ((τ - ε) / 2)) *
            ((2 : ℝ) ^ j) ^ (-1 / ps + min η' (1 / 2))) * (l2norm f * l2norm g) := by
          gcongr
      _ = (C₁ * C₂ * Real.sqrt 24) *
          (((2 : ℝ) ^ j) ^ ((τ - ε) / 2) * ((2 : ℝ) ^ j) ^ (-1 / ps + min η' (1 / 2))) *
            (l2norm f * l2norm g) := by ring
      _ = _ := by rw [hmul]
  -- sum over blocks
  have hsum : ∀ x, ‖hOp φ χ (2 ^ j) τ ε J (Finset.Ioc (2 ^ j / 2) (2 ^ j)) f g x‖ ≤
      ∑ B ∈ π.blocks, ‖hOp φ χ (2 ^ j) τ ε J B f g x‖ := fun x => by
    rw [hOp_eq_sum_blocks π φ χ τ ε J hf g x]
    exact norm_sum_le _ _
  have hsumm : Summable (fun x => ∑ B ∈ π.blocks, ‖hOp φ χ (2 ^ j) τ ε J B f g x‖) :=
    summable_sum fun B hB => (hblock B hB).1
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hsum hsumm, ?_⟩
  have hnc := π.blocks_card_le (by norm_num : (0 : ℝ) < 24)
  have hM : 0 ≤ (C₁ * C₂ * Real.sqrt 24) *
      ((2 : ℝ) ^ j) ^ ((τ - ε) / 2 + (-1 / ps + min η' (1 / 2))) * (l2norm f * l2norm g) := by
    have := hC₁0; have := hC₂0
    positivity
  calc ∑' x, ‖hOp φ χ (2 ^ j) τ ε J (Finset.Ioc (2 ^ j / 2) (2 ^ j)) f g x‖
      ≤ ∑' x, ∑ B ∈ π.blocks, ‖hOp φ χ (2 ^ j) τ ε J B f g x‖ :=
        Summable.tsum_le_tsum hsum (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hsum hsumm)
          hsumm
    _ = ∑ B ∈ π.blocks, ∑' x, ‖hOp φ χ (2 ^ j) τ ε J B f g x‖ :=
        Summable.tsum_finsetSum fun B hB => (hblock B hB).1
    _ ≤ ∑ B ∈ π.blocks, (C₁ * C₂ * Real.sqrt 24) *
          ((2 : ℝ) ^ j) ^ ((τ - ε) / 2 + (-1 / ps + min η' (1 / 2))) * (l2norm f * l2norm g) :=
        Finset.sum_le_sum fun B hB => (hblock B hB).2
    _ = (π.blocks.card : ℝ) * ((C₁ * C₂ * Real.sqrt 24) *
          ((2 : ℝ) ^ j) ^ ((τ - ε) / 2 + (-1 / ps + min η' (1 / 2))) * (l2norm f * l2norm g)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * 24 * ((2 : ℝ) ^ j) ^ (1 - (τ - ε))) * ((C₁ * C₂ * Real.sqrt 24) *
          ((2 : ℝ) ^ j) ^ ((τ - ε) / 2 + (-1 / ps + min η' (1 / 2))) * (l2norm f * l2norm g)) :=
        mul_le_mul_of_nonneg_right hnc hM
    _ = (48 * Real.sqrt 24 * C₁ * C₂) *
          (((2 : ℝ) ^ j) ^ (1 - (τ - ε)) *
            ((2 : ℝ) ^ j) ^ ((τ - ε) / 2 + (-1 / ps + min η' (1 / 2)))) *
            (l2norm f * l2norm g) := by ring
    _ = (48 * Real.sqrt 24 * C₁ * C₂) *
          ((2 : ℝ) ^ j) ^ (1 - (τ - ε) / 2 - 1 / ps + min η' (1 / 2)) *
            (l2norm f * l2norm g) := by
        rw [← Real.rpow_add hQ0]
        congr 3
        ring
    _ ≤ (48 * Real.sqrt 24 * C₁ * C₂) *
          ((2 : ℝ) ^ j) ^ (1 - (τ - ε) / 2 - 1 / ps + η') * (l2norm f * l2norm g) := by
        have h48 : 0 ≤ 48 * Real.sqrt 24 * C₁ * C₂ := by positivity
        gcongr

end PrimeBHT.BlockSum
